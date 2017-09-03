#include <cstdio>
#include <vector>
#include <list>
#include <set>
#include <map>
#include <sstream>
#include "gurobi_c++.h"
using namespace std;

static GRBEnv env;
static GRBModel *pgm;

struct edge
{
  int vs[2];

  edge(int v1, int v2) : vs{v1, v2}
    {
    }
};

struct configuration
{
  int outer, ne;
  vector<edge> es;
};

static const configuration birkhoffdiamond =
{
  6, 21,
  {
      edge(-1, 0),
      edge(-2, 1),
      edge(-3, 2),
      edge(-4, 3),
      edge(-5, 4),
      edge(-6, 5),
      edge(0, 7),
      edge(0, 6),
      edge(1, 7),
      edge(1, 2),
      edge(2, 8),
      edge(3, 8),
      edge(3, 9),
      edge(4, 9),
      edge(4, 5),
      edge(5, 6),
      edge(6, 10),
      edge(7, 11),
      edge(8, 11),
      edge(9, 10),
      edge(10, 11)
  }
};

static const configuration blockcntredu =
{
  10, 32,
  {
      edge(-1,0),
      edge(-2,1),
      edge(-3,3),
      edge(-4,4),
      edge(-5,6),
      edge(-6,7),
      edge(-7,9),
      edge(-8,10),
      edge(-9,12),
      edge(-10,13),
      edge(0,1),
      edge(0,14),
      edge(1,2),
      edge(2,3),
      edge(2,16),
      edge(3,4),
      edge(4,5),
      edge(5,6),
      edge(5,16),
      edge(6,7),
      edge(7,8),
      edge(8,9),
      edge(8,17),
      edge(9,10),
      edge(10,11),
      edge(11,12),
      edge(11,17),
      edge(12,13),
      edge(13,14),
      edge(14,15),
      edge(15,16),
      edge(15,17)
  }
};

static bool
at_same_vertex (const configuration &c, int e1, int e2)
{
  int i, j;
  for (i = 0; i < 2; i++)
    for (j = 0; j < 2; j++)
      if (c.es[e1].vs[i] == c.es[e2].vs[j])
	return true;
  return false;
}

typedef struct
{
  vector<list<int>> adj;
} graph;

static void
add_edge (graph &g, int v1, int v2)
{
  g.adj[v1].push_back (v2);
  g.adj[v2].push_back (v1);
}

static void
conf_to_graph (const configuration &c, graph &g)
{
  int e1, e2;

  g.adj.resize (c.ne);
  for (e1 = 0; e1 < c.ne; e1++)
    for (e2 = e1 + 1; e2 < c.ne; e2++)
      if (at_same_vertex (c, e1, e2))
	add_edge (g, e1, e2);
}

static vector<int> color;
static vector<vector<int>> avail;
static vector<int> navail;

struct ustel
{
  int *w;
  int val;

  ustel (int &wh)
    {
      w = &wh;
      val = wh;
    }
};
static vector<ustel> undo_stack;

static void
set_with_undo (int &w, int val)
{
  undo_stack.push_back (ustel (w));
  w = val;
}

static void
undo_till (size_t till)
{
  while (undo_stack.size () > till)
    {
      ustel &lst = undo_stack.back ();
      *lst.w = lst.val;
      undo_stack.pop_back ();
    }
}

static void
prune_color (int v, int c)
{
  if (color[v] >= 0 || !avail[v][c])
    return;

  set_with_undo (avail[v][c], 0);
  set_with_undo (navail[v], navail[v] - 1);
}

static void
set_color (const graph &g, int v, int c)
{
  set_with_undo (color[v], c);
  const list<int> &adj = g.adj[v];
  for (list<int>::const_iterator u = adj.begin (); u != adj.end (); u++)
    prune_color (*u, c);
}

static int
find_constrained_vertex (const graph &g)
{
  int bv = -1, cbv = 4, v;
  int n = g.adj.size ();

  for (v = 0; v < n; v++)
    if (color[v] == -1 && navail[v] < cbv)
      {
	bv = v;
	cbv = navail[v];
      }

  return bv;
}

static bool
try_extend (const graph &g)
{
  int bv = find_constrained_vertex (g);
  if (bv == -1)
    return true;

  int c;
  size_t till = undo_stack.size ();
  for (c = 0; c < 3; c++)
    if (avail[bv][c])
      {
	set_color (g, bv, c);
	if (try_extend (g))
	  return true;
	undo_till (till);
      }

  return false;
}

typedef vector<int> precoloring;

static bool
coloring_extends (const graph &g, const precoloring &col)
{
  int v, pc = col.size ();
  int n = g.adj.size ();

  color.clear ();
  color.resize (n, -1);
  navail.clear ();
  navail.resize (n, 3);
  avail.clear ();
  avail.resize (n, vector<int>{1,1,1});
  for (v = 0; v < pc; v++)
    {
      if (!avail[v][col[v]])
	return false;
      set_color (g, v, col[v]);
    }

  undo_stack.clear ();
  return try_extend (g);
}

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

static set<precoloring> nonext;

static void
test_colorings (const graph &g, precoloring &col, size_t outer, int mx)
{
  if (col.size () == outer)
    {
      if (bad_parity (col))
	return;
      if (coloring_extends (g, col))
	{
	  dump_precoloring (col);
	  printf ("\n");
	}
      else
	nonext.insert (col);
      return;
    }

  for (int c = 0; c < mx; c++)
    {
      col.push_back (c);
      test_colorings (g, col, outer, mx);
      col.pop_back ();
    }
  if (mx < 3)
    {
      col.push_back (mx);
      test_colorings (g, col, outer, mx + 1);
      col.pop_back ();
    }
}

static void
process_configuration (const configuration &c)
{
  graph g;
  conf_to_graph (c, g);

  precoloring col;
  test_colorings (g, col, c.outer, 0);
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
all_swaps_in_set (const set<precoloring> &with, const precoloring &pc, const matching &m, int nonc)
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
is_consistent_in_complcol (const set<precoloring> &with, const precoloring &pc, int nonc)
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
is_consistent (const set<precoloring> &with, const precoloring &pc)
{
  return (is_consistent_in_complcol (with, pc, 0)
	  && is_consistent_in_complcol (with, pc, 1)
	  && is_consistent_in_complcol (with, pc, 2));
}

static string
chain_name (const precoloring &pc, const matching &m)
{
  string ret;
  stringstream rets (ret);
  int n = m.ps.size ();
  for (int i = 0; i < n; i++)
    {
      int a = m.ps[i].first;
      int b = m.ps[i].second;
      rets << a;
      rets << (pc[a] == pc[b] ? 'o' : 'e');
      rets << b;
    }

  return ret;
}

static map<string,GRBVar> vars;

static GRBVar
get_var (string name, bool create)
{
  if (create)
    vars[name] = pgm->addVar (0, GRB_INFINITY, 1, GRB_CONTINUOUS, name);

  return vars[name];
}

static void
gen_equations_complcol (const set<precoloring> &with, const precoloring &pc, int nonc, bool create_vars)
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

  string col_name = precoloring_name (pc);
  GRBVar col_var = get_var (col_name, create_vars);
  if (create_vars)
    printf ("%s = ", col_name.c_str ());
  else
    cstr += GRBLinExpr (col_var, -1);
  const char *sep = "";
  for (list<matching>::iterator m = ms.begin (); m != ms.end (); m++)
    if (all_swaps_in_set (with, pc, *m, nonc))
      {
	string ch_name = chain_name (pc, *m);
	GRBVar ch_var = get_var (ch_name, create_vars);
	if (create_vars)
	  printf ("%s%s", sep, ch_name.c_str ());
	else
	  cstr += GRBLinExpr (ch_var, 1);
	sep = " + ";
      }
  if (!create_vars)
    pgm->addConstr (cstr, GRB_EQUAL, 0);
  printf ("\n");
}

static void
gen_equations (const set<precoloring> &with, const precoloring &pc, bool create_vars)
{
  gen_equations_complcol (with, pc, 0, create_vars);
  gen_equations_complcol (with, pc, 1, create_vars);
  gen_equations_complcol (with, pc, 2, create_vars);
}

static void
prune_by_consistency (const set<precoloring> &old, set<precoloring> &nw)
{
  for (set<precoloring>::const_iterator pc = old.begin (); pc != old.end (); pc++)
    if (is_consistent (old, *pc))
      nw.insert (*pc);
}

int main (void)
{
  printf ("Extends:\n");
//  process_configuration (birkhoffdiamond);
  process_configuration (blockcntredu);
  printf ("Initial non-ext: %d\n", (int) nonext.size ());
  set<precoloring> act_nonext (nonext);
  set<precoloring> prev_nonext;
  do
    {
      prev_nonext = act_nonext;
      act_nonext.clear ();
      prune_by_consistency (prev_nonext, act_nonext);
      printf ("Remaining non-ext: %d\n", (int) act_nonext.size ());
    } while (prev_nonext.size () > act_nonext.size ());

  pgm = new GRBModel (env);
  for (set<precoloring>::iterator pc = act_nonext.begin (); pc != act_nonext.end (); pc++)
    gen_equations (act_nonext, *pc, true);
  pgm->update ();
  for (set<precoloring>::iterator pc = act_nonext.begin (); pc != act_nonext.end (); pc++)
    gen_equations (act_nonext, *pc, false);
  pgm->set (GRB_IntAttr_ModelSense, GRB_MAXIMIZE);
  pgm->optimize ();

  delete pgm;
  return 0;
}
