#include <cstdio>
#include <vector>
#include <list>
#include <set>
#include <map>
#include <sstream>
#include <cmath>
#include "gurobi_c++.h"
using namespace std;

static GRBEnv env;

typedef vector<int> precoloring;
typedef set<precoloring> potent;

static string
precoloring_name (const precoloring &col)
{
  string ret;

  for (precoloring::const_iterator i = col.begin (); i < col.end (); i++)
    ret.push_back ('1' + *i);

  return ret;
}

static void
dump_precoloring (const precoloring &col)
{
  printf ("%s", precoloring_name (col).c_str ());
}

static void
dump_potent (const potent &p)
{
  for (potent::const_iterator pc = p.begin (); pc != p.end (); pc++)
    {
      dump_precoloring (*pc);
      printf (";");
    }
  printf ("\n");
}

static bool
bad_parity (const precoloring &col)
{
  int nc[3] = {0, 0, 0};
  int parity = col.size () % 2;

  for (precoloring::const_iterator i = col.begin (); i < col.end (); i++)
    nc[*i]++;
  for (int i = 0; i < 3; i++)
    if (nc[i] % 2 != parity)
      return true;
  return false;
}

static void
gen_all_colorings (precoloring &col, size_t outer, int mx, potent &res)
{
  if (col.size () == outer)
    {
      if (!bad_parity (col))
	res.insert (col);	
      return;
    }

  for (int c = 0; c < mx; c++)
    {
      col.push_back (c);
      gen_all_colorings (col, outer, mx, res);
      col.pop_back ();
    }
  if (mx < 3)
    {
      col.push_back (mx);
      gen_all_colorings (col, outer, mx + 1, res);
      col.pop_back ();
    }
}

static void
gen_all_colorings (int outer, potent &res)
{
  precoloring col;
  gen_all_colorings (col, outer, 0, res);
}

struct matching
{
  vector<pair<int,int>> ps;

  matching (void)
    {
    }

  matching (int a, int b, const matching &l, const matching &r)
    {
      ps.push_back (pair<int,int>(a,b));
      ps.insert (ps.end (), l.ps.begin (), l.ps.end ());
      ps.insert (ps.end (), r.ps.begin (), r.ps.end ());
    }
};

static void
gen_matchings (const list<int> pos, list<matching> &ms)
{
  int n = pos.size ();
  if (n == 0)
    {
      ms.push_back (matching ());
      return;
    }

  list<int> left;
  list<int> right(pos);

  list<int>::const_iterator m0 = pos.begin ();
  m0++;
  for (int i = 0; i < n; i += 2, m0++, m0++)
    {
      list<matching> msl, msr;
      right.pop_front ();
      right.pop_front ();
      gen_matchings (left, msl);
      gen_matchings (right, msr);

      for (list<matching>::iterator l = msl.begin (); l != msl.end (); ++l)
	for (list<matching>::iterator r = msr.begin (); r != msr.end (); ++r)
	  ms.push_back (matching (pos.front (), *m0, *l, *r));

      left.push_back (*m0);
      left.push_back (right.front ());
    }
}

static void
swap_on_subset (const matching &m, int ss, precoloring &pc, int nonc)
{
  int n = m.ps.size ();

  for (int i = 0; i < n; i++)
    if ((ss >> i) & 1)
      {
	int a = m.ps[i].first;
	int b = m.ps[i].second;

	pc[a] = 3 - nonc - pc[a];
	pc[b] = 3 - nonc - pc[b];
      }
}

static void
canonicalize (precoloring &pc)
{
  int mapsto[3] = {-1, -1, -1};
  int m = 0;

  for (precoloring::iterator c = pc.begin (); c != pc.end (); c++)
    {
      if (mapsto[*c] != -1)
	{
	  *c = mapsto[*c];
	  continue;
	}
      mapsto[*c] = m;
      *c = m;
      m++;
    }
}

static bool
all_swaps_in_set (const potent &with, const precoloring &pc, const matching &m, int nonc)
{
  int n = m.ps.size ();
  for (int ss = 0; ss < (1 << n); ss++)
    {
      precoloring spc(pc);
      swap_on_subset (m, ss, spc, nonc);
      canonicalize (spc);
      if (with.count (spc) == 0)
	return false;
    }

  return true;
}

static bool
is_consistent_in_complcol (const potent &with, const precoloring &pc, int nonc)
{
  list<int> positions;
  int n = pc.size ();

  for (int i = 0; i < n; i++)
    if (pc[i] != nonc)
      positions.push_back (i);
  if (positions.size () <= 2)
    return true;

  list<matching> ms;
  gen_matchings (positions, ms);
  for (list<matching>::iterator m = ms.begin (); m != ms.end (); m++)
    if (all_swaps_in_set (with, pc, *m, nonc))
      return true;

  return false;
}

static bool
is_consistent (const potent &with, const precoloring &pc)
{
  return (is_consistent_in_complcol (with, pc, 0)
	  && is_consistent_in_complcol (with, pc, 1)
	  && is_consistent_in_complcol (with, pc, 2));
}

static void
prune_by_consistency (potent &what)
{
  bool any;
  do
    {
      any = false;

      for (potent::const_iterator pc = what.begin (); pc != what.end (); )
	{
	  if (is_consistent (what, *pc))
	    pc++;
	  else
	    {
	      pc = what.erase (pc);
	      any = true;
	    }
	}
    } while (any);
}

static string
chain_name (const precoloring &pc, const matching &m)
{
  stringstream rets;
  int n = m.ps.size ();
  for (int i = 0; i < n; i++)
    {
      int a = m.ps[i].first;
      int b = m.ps[i].second;
      rets << a;
      rets << (pc[a] == pc[b] ? 'o' : 'e');
      rets << b;
    }

  return rets.str ();
}

struct lpgm
{
  GRBModel *pgm;
  map<string,GRBVar> vars;

  lpgm (const potent &with)
    {
      pgm = new GRBModel (env);
      gen_equations (with);
      for (potent::const_iterator pc = with.begin (); pc != with.end (); pc++)
	get_var (precoloring_name (*pc)).set (GRB_DoubleAttr_LB, 1);
      pgm->optimize ();
    }

  bool is_bc_consistent (void)
    {
      return (pgm->get (GRB_IntAttr_Status) == GRB_OPTIMAL);
    }

  ~lpgm(void)
    {
      delete pgm;
    }

  GRBVar get_var (string name)
    {
      if (vars.count (name) == 0)
	vars[name] = pgm->addVar (0, GRB_INFINITY, 0, GRB_CONTINUOUS, name);

      return vars[name];
    }

  void gen_equations_complcol (const potent &with, const precoloring &pc, int nonc, bool create_vars)
    {
      list<int> positions;
      int n = pc.size ();

      for (int i = 0; i < n; i++)
	if (pc[i] != nonc)
	  positions.push_back (i);
      if (positions.size () <= 2)
	return;

      list<matching> ms;
      gen_matchings (positions, ms);
      GRBLinExpr cstr;

      stringstream consname;

      string col_name = precoloring_name (pc);
      GRBVar col_var = get_var (col_name);
      consname << col_name << " = ";
      if (!create_vars)
	cstr += GRBLinExpr (col_var, -1);
      const char *sep = "";
      for (list<matching>::iterator m = ms.begin (); m != ms.end (); m++)
	if (all_swaps_in_set (with, pc, *m, nonc))
	  {
	    string ch_name = chain_name (pc, *m);
	    GRBVar ch_var = get_var (ch_name);
	    consname << sep << ch_name;
	    if (!create_vars)
	      cstr += GRBLinExpr (ch_var, 1);
    	    sep = " + ";
	  }
      if (!create_vars)
	pgm->addConstr (cstr, GRB_EQUAL, 0, consname.str ());
    }

  void gen_equations (const potent &with, const precoloring &pc, bool create_vars)
    {
      gen_equations_complcol (with, pc, 0, create_vars);
      gen_equations_complcol (with, pc, 1, create_vars);
      gen_equations_complcol (with, pc, 2, create_vars);
    }

  void gen_equations (const potent &with)
    {
      for (potent::const_iterator pc = with.begin (); pc != with.end (); pc++)
	gen_equations (with, *pc, true);
      pgm->update ();
      for (potent::const_iterator pc = with.begin (); pc != with.end (); pc++)
	gen_equations (with, *pc, false);
    }

  void dump_dual (void)
    {
      GRBConstr *css = pgm->getConstrs ();
      int n = pgm->get (GRB_IntAttr_NumConstrs);

      for (int c = 0; c < n; c++)
	{
	  double val = css[c].get (GRB_DoubleAttr_Pi);
	  if (abs (val) < 1e-6)
	    continue;

	  printf ("%.3f\t%s\n", val, css[c].get (GRB_StringAttr_ConstrName).c_str ());
	}

      delete css;
    }

  void dump (void)
    {
      GRBConstr *css = pgm->getConstrs ();
      int n = pgm->get (GRB_IntAttr_NumConstrs);

      for (int c = 0; c < n; c++)
       	printf ("%s\n", css[c].get (GRB_StringAttr_ConstrName).c_str ());

      delete css;
    }
};

static void
test_consistent_sets (const potent &aset, const potent &fix)
{
  precoloring act;
  bool any = false;

  if (fix.size () > 14)
    return;

  for (potent::const_iterator pc = aset.begin (); pc != aset.end (); pc++)
    if (fix.count (*pc) == 0)
      {
	act = *pc;
	any = true;
	break;
      }

  if (!any)
    {
      static int cnt;

      cnt++;
      if (cnt % 1000 == 0)
	{
	  fprintf (stderr, "#");
	  fflush (stderr);
	}

      lpgm *tst = new lpgm (aset);
      if (!tst->is_bc_consistent ())
	dump_potent (aset);
      delete tst;
      return;
    }


  potent naset(aset);
  naset.erase (act);
  prune_by_consistency (naset);
  for (potent::const_iterator pc = fix.begin (); pc != fix.end (); pc++)
    if (naset.count (*pc) == 0)
      goto mustbein;
  test_consistent_sets (naset, fix);

mustbein:
  potent nfix(fix);
  nfix.insert (act);
  test_consistent_sets (aset, nfix);
}

int main (void)
{
  env.set(GRB_IntParam_OutputFlag, 0);
  potent all, none;

  gen_all_colorings (6, all);
  lpgm(all).dump ();
  test_consistent_sets (all, none);

  return 0;
}
