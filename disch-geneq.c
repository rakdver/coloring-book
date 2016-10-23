#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <math.h>
#include "gurobi_c.h"

typedef struct
{
  int a, b;
} rational;

static int
gcd (int a, int b)
{
  int ka = a < 0 ? -a : a;
  int kb = b < 0 ? -b : b;
  int t;

  if (ka == kb)
    return b;

  if (ka > kb)
    {
      t = ka;
      ka = kb;
      kb = t;
    }

  while (ka)
    {
      t = ka;
      ka = kb % ka;
      kb = t;
    }

  if (b > 0)
    return kb;
  else
    return -kb;
}

static rational
rat (int a, int b)
{
  int g = gcd (a, b);
  rational ret = {a / g, b / g};

  return ret;
}

static rational
r_add (rational x, rational y)
{
  int g = gcd (x.b, y.b);
  int mx = y.b / g;
  int my = x.b / g;

  return rat (mx * x.a + my * y.a, mx * x.b);
}

static int
r_cmp (rational x, rational y)
{
  y.a = -y.a;
  rational diff = r_add (x, y);
  return diff.a;
}


static rational
r_mult (rational x, rational y)
{
  return rat (x.a * y.a, x.b * y.b);
}

static double
r_double (rational x)
{
  return (double) x.a / x.b;
}

#define MX (1 << 30)

static rational
to_rational_rec (double x, int h2, int k2, int h1, int k1)
{
  int ipart = (int) x;
  int h0, k0;

  h0 = ipart * h1 + h2;
  k0 = ipart * k1 + k2;

  x -= ipart;
  if (x > 1e-8)
    {
      x = 1 / x;

      int nxtip = x;

      if ((MX - h1) / nxtip >= h0
	  && (MX - k1) / nxtip >= k0)
	return to_rational_rec (x, h1, k1, h0, k0);
    }
    
  return rat (h0, k0);
}

static rational
to_rational (double x)
{
  int neg = 0;

  if (x < 0)
    {
      neg = 1;
      x = -x;
    }

  rational ret = to_rational_rec (x, 0, 1, 1, 0);

  if (neg)
    ret.a = -ret.a;

  return ret;
}

struct coef
{
  int var;
  rational cf;
  struct coef *next;
};

static struct coef *lhs;

static void
free_cfl (struct coef *x)
{
  struct coef *nx;

  for (; x; x = nx)
    {
      nx = x->next;
      free (x);
    }
}

static void
clear_coefs (void)
{
  free_cfl (lhs);
  lhs = NULL;
}

static char *
var_name_va (char *class, int n, va_list ap)
{
  static char buf[10][1000];
  static int rot;
  char *p;
  int i, d;

  p = buf[rot];

  sprintf (p, "%s%n", class, &d);
  p += d;

  for (i = 0; i < n; i++)
    {
      sprintf (p, "x%d%n", va_arg(ap, int), &d);
      p += d;
    }

  p = buf[rot];
  rot = (rot + 1) % 10;
  return p;
}

static char *
var_name (char *class, int n, ...)
{
  va_list ap;
  char *ret;

  va_start(ap, n);
  ret = var_name_va (class, n, ap);
  va_end(ap);

  return ret;
}

static GRBmodel *model = NULL;

static int
name_to_id (char *name)
{
  int var;

  if (GRBgetvarbyname (model, name, &var) || var == -1)
    abort ();

  return var;
}

static int cons_id (char *name) __attribute__((used));

static int
cons_id (char *name)
{
  int cs;

  if (GRBgetconstrbyname (model, name, &cs) || cs == -1)
    abort ();

  return cs;
}

static int
var_id (char *class, int n, ...)
{
  char *name;
  va_list ap;

  va_start(ap, n);
  name = var_name_va (class, n, ap);
  va_end(ap);

  return name_to_id (name);
}

static void
gen_rel (char *a, char c, char *b)
{
  int id[2] = {name_to_id (a), name_to_id (b)};
  double cf[2] = {1,-1};
  char cn[100];

  sprintf (cn, "%s %c= %s", a, c, b);
  if (GRBaddconstr (model, 2, id, cf, c, 0, cn))
    abort ();
}

static void
add_coef (int var, rational val)
{
  struct coef **a, *nw;

  for (a = &lhs; *a; a = &(*a)->next)
    {
      if ((*a)->var == var)
	{
	  (*a)->cf = r_add ((*a)->cf, val);
	  return;
	}
      if ((*a)->var > var)
	break;
    }

  nw = malloc (sizeof (struct coef));
  nw->var = var;
  nw->cf = val;
  nw->next = *a;
  *a = nw;
}

struct hentry
{
  struct coef *lhs;
  char *descr;
  rational rhs;
  struct hentry *next;
};

#define HSIZE 5000000
#define Q 1009
static struct hentry *hash[HSIZE];

static unsigned
hash_fn (struct coef *a)
{
  if (!a)
    return 0;

  unsigned h = hash_fn (a->next);

  h = (Q * h + a->var) % HSIZE;
  h = (Q * h + a->cf.a) % HSIZE;
  h = (Q * h + a->cf.b) % HSIZE;

  return h;
}

static int rem_id;
static int total_eqs;

static int
same_cfl (struct coef *a, struct coef *b)
{
  while (a && b)
    {
      if (a->var != b->var)
	return 0;

      if (r_cmp (a->cf, b->cf) != 0)
	return 0;

      a = a->next;
      b = b->next;
    }

  if (a || b)
    return 0;

  return 1;
}

static void
clear_zero_coefs (void)
{
  struct coef **a = &lhs, *act;

  while (*a)
    {
      act = *a;
      if (act->cf.a != 0)
	{
	  a = &act->next;
	  continue;
	}

      *a = act->next;
      free (act);
    }
}

static void
write_eq (rational charge, char *cn)
{
  int hsh;
  struct hentry *h;

  clear_zero_coefs ();

  hsh = hash_fn (lhs);
  for (h = hash[hsh]; h; h = h->next)
    if (same_cfl (lhs, h->lhs))
      break;

  if (h)
    {
      if (r_cmp (charge, h->rhs) < 0)
	{
	  free (h->descr);
	  h->descr = strdup (cn);
	  h->rhs = charge;
	}

      return;
    }

  h = malloc (sizeof (struct hentry));
  h->lhs = lhs;
  lhs = NULL;
  h->rhs = charge;
  h->descr= strdup (cn);
  h->next = hash[hsh];
  hash[hsh] = h;
  total_eqs++;
}

static void
output_eq (struct hentry *h)
{
  int i, nc;
  struct coef *a;

  nc = 0;
  for (a = h->lhs; a; a = a->next)
    nc++;

  int inds[nc];
  double cfs[nc];

  for (a = h->lhs, i = 0; a; a = a->next, i++)
    {
      inds[i] = a->var;
      cfs[i] = -r_double (a->cf);
    }

  if (GRBaddconstr (model, nc, inds, cfs, GRB_LESS_EQUAL, r_double (h->rhs), h->descr))
    abort ();

  free_cfl (h->lhs);
  free (h->descr);
  free (h);
}

static void
output_eqs (void)
{
  int i;

  for (i = 0; i < HSIZE; i++)
    {
      struct hentry *h, *hn;

      for (h = hash[i]; h; h = hn)
	{
	  hn = h->next;
	  output_eq (h);
	}
      hash[i] = NULL;
    }
}

struct fld
{
  int len;
  int ge;
  char *descr;
};

static int
fl_le (struct fld *fl, int what)
{
  if (fl->ge)
    return 0;

  return fl->len <= what;
}

static void
lbound (int *x, int a)
{
  if (a > *x)
    *x = a;
}

static char
tohex (int x)
{
  if (x < 10)
    return '0' + x;

  return 'a' + x - 10;
}

static int
rotinv_idx (int len, int i, int inv, int r)
{
  if (inv)
    i = len - 1 - i;

  return (i + r) % len;
}

enum vtype
{
  deg4,
  deg5,
  deg6,
  degbig,
  LAST_VTYPE
};

static int
rotinv_smaller (int len, int act[], int inv, int r)
{
  int i, j;

  for (i = 0; i < len; i++)
    {
      j = rotinv_idx (len, i, inv, r);

      if (act[j] < act[i])
	return 1;
      if (act[j] > act[i])
	return 0;
    }

  return 0;
}

static int
rotinv_invariant (int len, int act[], int inv, int r)
{
  int i, j;

  for (i = 0; i < len; i++)
    {
      j = rotinv_idx (len, i, inv, r);

      if (act[j] != act[i])
	return 0;
    }

  return 1;
}

static int
rotinv_smaller_type (int len, enum vtype act[], int inv, int r)
{
  int i, j;

  for (i = 0; i < len; i++)
    {
      j = rotinv_idx (len, i, inv, r);

      if (act[j] < act[i])
	return 1;
      if (act[j] > act[i])
	return 0;
    }

  return 0;
}

static int
rotinv_minimal_type (int len, int intria[], enum vtype type[])
{
  int r, inv;

  for (inv = 0; inv <= 1; inv++)
    for (r = 0; r < len; r++)
      if (rotinv_invariant (len, intria, inv, r)
	  && rotinv_smaller_type (len, type, inv, r))
	return 0;

  return 1;
}

static int
rotinv_minimal (int len, int act[])
{
  int r, inv;

  for (inv = 0; inv <= 1; inv++)
    for (r = 0; r < len; r++)
      if (rotinv_smaller (len, act, inv, r))
	return 0;

  return 1;
}

static void
dump_rule (char *var_name)
{
  double val;
  rational rval;

  if (GRBgetdblattrelement (model, "X", name_to_id (var_name), &val))
    abort ();

  rval = to_rational (val);

  printf ("%s -> %d/%d (%.5f)\n", var_name, rval.a, rval.b, val);
}

static char *
varstring (char *var_name)
{
  static char buf[1000];
  double val;
  rational rval;

  if (GRBgetdblattrelement (model, "X", name_to_id (var_name), &val))
    abort ();

  rval = to_rational (val);

  sprintf (buf, "%d, %d", rval.a, rval.b);
  return buf;
}

static void
dump_constraint (int cs)
{
  int numcoef;
  int cb;
  int id[1000];
  double cf[1000];
  int i;
  char sen;
  double rhs;

  if (GRBgetconstrs (model, &numcoef, &cb, id, cf, cs, 1))
    abort ();
  for  (i = cb; i < numcoef; i++)
    {
      char *name;

      if (GRBgetstrattrelement (model, "VarName", id[i], &name))
	abort ();

      printf ("  %.5f %s", cf[i], name);
    }

  if (GRBgetcharattrelement (model, "Sense", cs, &sen))
    abort ();
  if (GRBgetdblattrelement (model, "RHS", cs, &rhs))
    abort ();

  printf ("  %c %.5f\n", sen, rhs);
}


static const char vtype_repr[LAST_VTYPE] = {'4', '5', '6', 'b'};

static char *
trirule (enum vtype v1, enum vtype v2, enum vtype v3)
{
  static char buf[10][1000];
  static int rot;
  char *p;

  if (v1 > v2)
    {
      enum vtype t = v1;
      v1 = v2;
      v2 = t;
    }

  p = buf[rot];
  sprintf (p, "tria_%c%c%c", vtype_repr[v1], vtype_repr[v2], vtype_repr[v3]);
  rot = (rot + 1) % 10;
  return p;
}

static rational
vtype_charge (enum vtype a)
{
  switch (a)
    {
    case deg4:
      return rat (0, 1);
    case deg5:
      return rat (1, 2);
    case deg6:
      return rat (2, 3);
    case degbig:
      return rat (1, 1);
    default:
      abort ();
    }
}

static void
gen_eq_triangle_kind (enum vtype a, enum vtype b, enum vtype c)
{
  char consname[1000];
  rational ch = rat (-1, 1);

  ch = r_add (ch, vtype_charge (a));
  ch = r_add (ch, vtype_charge (b));
  ch = r_add (ch, vtype_charge (c));

  clear_coefs ();
  add_coef (rem_id, rat (1, 1));
  add_coef (name_to_id (trirule (a, b, c)), rat (1, 1));
  add_coef (name_to_id (trirule (b, c, a)), rat (1, 1));
  add_coef (name_to_id (trirule (a, c, b)), rat (1, 1));
  sprintf (consname, "triangle %c%c%c", vtype_repr[a], vtype_repr[b], vtype_repr[c]);
  write_eq (ch, consname);
}

static void
gen_eq_triangle (void)
{
  int i, j, k;

  for (i = 0; i < LAST_VTYPE; i++)
    for (j = i; j < LAST_VTYPE; j++)
      for (k = j; k < LAST_VTYPE; k++)
	gen_eq_triangle_kind (i, j, k);
}

static void
sel (int x, int dir, int len, int i, int *a, int *pv, int *nv)
{
  *a = (x + len + (2 * dir - 1) * i) % len;
  if (dir)
    {
      *pv = *a;
      *nv = (*a + 1) % len;
    }
  else
    {
      *nv = *a;
      *pv = (*a + 1) % len;
    }
}

static void
gen_eq_face_type (int len, int intria[], enum vtype type[], enum vtype opptype[])
{
  char consname[1000];
  rational ch = rat (len - 4, 1);
  int i, ap; 
  enum vtype md = deg4;
  int nmd = 0, idx = -1;
  int light = 0;

  if (len != 5)
    abort ();

  for (i = 0; i < 5; i++)
    {
      if (type[i] > md)
	{
	  md = type[i];
	  nmd = 1;
	  idx = i;
	}
      else if (type[i] == md)
	nmd++;
    }

  if (md == deg4)
    {
      for (i = 0; i < 5; i++)
	if (intria[i] && opptype[i] == deg4)
	  return;
    }

  if (md == deg5 && nmd == 1)
    {
      if (intria[idx] && opptype[idx] == deg4)
	return;
      if (intria[(idx + len - 1) % len] && opptype[(idx + len - 1) % len] == deg4)
	return;
    }

  clear_coefs ();
  add_coef (rem_id, rat (1, 1));

  if (md == deg6 && nmd == 1
      && intria[idx] && opptype[idx] == deg4
      && intria[(idx + len - 1) % len] && opptype[(idx + len - 1) % len] == deg4)
    {
      add_coef (name_to_id ("six_to_light"), rat (1, 1));
      light = 1;
    }

  for (i = 0; i < len; i++)
    {
      if (intria[i])
	{
	  enum vtype v1, v2, v3;
	  v1 = type[i];
	  v2 = type[(i + 1) % len];
	  v3 = opptype[i];
	  add_coef (name_to_id (trirule (v1, v2, v3)), rat (-1, 1));
	}

      if (type[i] == deg6
	  && intria[(i + len - 1) % len] + intria[i] == 1)
	add_coef (name_to_id ("six_to_nonbitri"), rat (1, 1));

      if (type[i] == deg6
	  && intria[(i + len - 1) % len] && intria[i]
	  && !light)
	add_coef (name_to_id ("six_from_nonlight"), rat (-1, 1));
    }

  ap = 0;
  for (i = 0; i < len; i++)
    {
      consname[ap++] = vtype_repr[type[i]];
      if (intria[i])
	{
	  consname[ap++] = '(';
	  consname[ap++] = vtype_repr[opptype[i]];
	  consname[ap++] = ')';
	}
      else
	consname[ap++] = '-';
    }
  consname[ap] = 0;
  write_eq (ch, consname);
}

static void
gen_eq_face_type_1 (int len, int intria[], enum vtype type[])
{
  enum vtype opptype[len];
  int max_types = 1, i, at;

  for (i = 0; i < len; i++)
    if (intria[i])
      max_types *= LAST_VTYPE;

  for (at = 0; at < max_types; at++)
    {
      int x = at;
      for (i = 0; i < len; i++)
	{
	  int c;

	  if (!intria[i])
	    continue;

	  c = x % LAST_VTYPE;
	  x /= LAST_VTYPE;

	  opptype[i] = c;
	}

      gen_eq_face_type (len, intria, type, opptype);
    }
}

static void
gen_eq_face_tria (int len, int intria[])
{
  int max_types = 1, i, at;
  enum vtype type[len];

  for (i = 0; i < len; i++)
    max_types *= LAST_VTYPE;

  for (at = 0; at < max_types; at++)
    {
      int x = at;

      for (i = 0; i < len; i++)
	{
	  int c;

	  c = x % LAST_VTYPE;
	  x /= LAST_VTYPE;
	  type[i] = c;
	}

      if (rotinv_minimal_type (len, intria, type))
	gen_eq_face_type_1 (len, intria, type);
    }
}

static void
gen_eq_face (int len)
{
  int intria[len];
  unsigned bits;

  for (bits = 0; bits < (1 << len); bits++)
    {
      int i;
      for (i = 0; i < len; i++)
	intria[i] = (bits >> i) & 1;
      if (rotinv_minimal (len, intria))
	gen_eq_face_tria (len, intria);
    }
}

static void
gen_eq_six (void)
{
  clear_coefs ();
  add_coef (rem_id, rat (1, 1));
  add_coef (name_to_id ("six_to_nonbitri"), rat (-2, 1));
  write_eq (rat (4,3), "six-one triangle");

  clear_coefs ();
  add_coef (rem_id, rat (1, 1));
  add_coef (name_to_id ("six_to_nonbitri"), rat (-2, 1));
  add_coef (name_to_id ("six_to_light"), rat (-1, 1));
  write_eq (rat (2,3), "six-two triangles adj");

  clear_coefs ();
  add_coef (rem_id, rat (1, 1));
  add_coef (name_to_id ("six_to_nonbitri"), rat (-4, 1));
  write_eq (rat (2,3), "six-two triangles nonadj");

  clear_coefs ();
  add_coef (rem_id, rat (1, 1));
  add_coef (name_to_id ("six_to_light"), rat (-1, 1));
  add_coef (name_to_id ("six_from_nonlight"), rat (2, 1));
  write_eq (rat (0,1), "six-three triangles");

  /* Correction for (>=6)-faces.  */
  enum vtype b, c;
  for (b = 0; b < LAST_VTYPE; b++)
    for (c = 0; c < LAST_VTYPE; c++)
      {
	char consname[1000];
	clear_coefs ();
	add_coef (rem_id, rat (1, 1));
	add_coef (name_to_id ("six_from_nonlight"), rat (-1, 1));
	add_coef (name_to_id (trirule (deg6, b, c)), rat (-1, 1));
	sprintf (consname, "6-face correction at triangle 6%c%c", vtype_repr[b], vtype_repr[c]);
	write_eq (rat (1,3), consname);
      }
}

int main (void)
{
  int i, j, k, len;
  int cs, ncs;

  GRBenv *env = NULL;
  double obj[] = {1};
  double remmin[] = {0};
  double remmax[] = {GRB_INFINITY};
  char *name[] = {"rem"};
  int prev_eqs;

  if (GRBloadenv(&env, "geneq.log"))
    abort ();
  if (GRBnewmodel(env, &model, "discharging", 1, obj, remmin, remmax, NULL, name))
    abort ();
  rem_id = name_to_id ("rem");

  for (i = 0; i < LAST_VTYPE; i++)
    for (j = i; j < LAST_VTYPE; j++)
      for (k = 0; k < LAST_VTYPE; k++)
	if (GRBaddvar (model, 0, NULL, NULL, 0, -GRB_INFINITY, 1.0/3, GRB_CONTINUOUS, trirule (i, j, k)))
	  abort ();
  if (GRBaddvar (model, 0, NULL, NULL, 0, 0, GRB_INFINITY, GRB_CONTINUOUS, "six_to_nonbitri"))
    abort ();
  if (GRBaddvar (model, 0, NULL, NULL, 0, 0, GRB_INFINITY, GRB_CONTINUOUS, "six_to_light"))
    abort ();
  if (GRBaddvar (model, 0, NULL, NULL, 0, 0, GRB_INFINITY, GRB_CONTINUOUS, "six_from_nonlight"))
    abort ();

  if (GRBupdatemodel (model))
    abort ();

  prev_eqs = total_eqs;
  gen_eq_triangle ();
  printf ("%d equations for triangles.\n", total_eqs - prev_eqs);

  len = 5;
  prev_eqs = total_eqs;
  gen_eq_face (len);
  printf ("%d equations for %d-faces.\n", total_eqs - prev_eqs, len);

  prev_eqs = total_eqs;
  gen_eq_six ();
  printf ("%d equations for 6-vertices.\n", total_eqs - prev_eqs);

  output_eqs ();

  if (GRBoptimize(model))
    abort ();

  double remv;
  if (GRBgetdblattr(model, "ObjVal", &remv))
    abort ();

  printf ("Rules:\n");
  for (i = 0; i < LAST_VTYPE; i++)
    for (j = i; j < LAST_VTYPE; j++)
      for (k = 0; k < LAST_VTYPE; k++)
	dump_rule (trirule (i, j, k));
  dump_rule ("six_to_nonbitri");
  dump_rule ("six_to_light");
  dump_rule ("six_from_nonlight");

  rational rrem = to_rational (remv);
  printf ("Remains: %d/%d (%.5f)\n", rrem.a, rrem.b, remv);
  printf ("Tight constraints:\n");

  if (GRBgetintattr(model, "NumConstrs", &ncs))
    abort ();

  for (cs = 0; cs < ncs; cs++)
    {
      double dual;

      if (GRBgetdblattrelement(model, "Pi", cs, &dual))
	abort ();

      if (fabs (dual) > 1e-6)
	{
	  char *csnam;

	  if (GRBgetstrattrelement (model, "ConstrName", cs, &csnam))
	    abort ();
	  printf ("%.5f: %s\n", dual, csnam);
	  dump_constraint (cs);
	}
    }

  if (GRBfreemodel(model))
    abort ();
  GRBfreeenv(env);

  return 0;
}
