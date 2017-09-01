#include <stdio.h>

#define MAXE 100
#define MUNDO 10000

typedef struct
{
  int outer, ne;
  int es[MAXE][2];
} configuration;

static configuration birkhoffdiamond =
{
  6, 21,
  {
      {-1, 0},
      {-2, 1},
      {-3, 2},
      {-4, 3},
      {-5, 4},
      {-6, 5},
      {0, 7},
      {0, 6},
      {1, 7},
      {1, 2},
      {2, 8},
      {3, 8},
      {3, 9},
      {4, 9},
      {4, 5},
      {5, 6},
      {6, 10},
      {7, 11},
      {8, 11},
      {9, 10},
      {10, 11}
  }
};

static int
at_same_vertex (configuration *c, int e1, int e2)
{
  int i, j;
  for (i = 0; i < 2; i++)
    for (j = 0; j < 2; j++)
      if (c->es[e1][i] == c->es[e2][j])
	return 1;
  return 0;
}

typedef struct
{
  int n;
  int deg[MAXE];
  int adj[MAXE][4];
} graph;

static void
add_edge (graph *g, int v1, int v2)
{
  g->adj[v1][g->deg[v1]++] = v2;
}

static void
conf_to_graph (configuration *c, graph *g)
{
  int e1, e2;

  g->n = c->ne;
  for (e1 = 0; e1 < c->ne; e1++)
    g->deg[e1] = 0;
  for (e1 = 0; e1 < c->ne; e1++)
    for (e2 = e1 + 1; e2 < c->ne; e2++)
      if (at_same_vertex (c, e1, e2))
	{
	  add_edge (g, e1, e2);
	  add_edge (g, e2, e1);
	}
}

static int color[MAXE];
static int avail[MAXE][3];
static int navail[MAXE];
static struct {int *w; int val;} undo_stack[MUNDO];
static int undo_top;

static void
set_with_undo (int *w, int val)
{
  undo_stack[undo_top].w = w;
  undo_stack[undo_top].val = *w;
  *w = val;
  undo_top++;
}

static void
undo_till (int till)
{
  while (undo_top > till)
    {
      undo_top--;
      *(undo_stack[undo_top].w) = undo_stack[undo_top].val;
    }
}

static void
prune_color (int v, int c)
{
  if (color[v] >= 0 || !avail[v][c])
    return;

  set_with_undo (&avail[v][c], 0);
  set_with_undo (&navail[v], navail[v] - 1);
}

static void
set_color (graph *g, int v, int c)
{
  int i;
  set_with_undo (&color[v], c);
  for (i = 0; i < g->deg[v]; i++)
    prune_color (g->adj[v][i], c);
}

static int
find_constrained_vertex (graph *g)
{
  int bv = -1, cbv = 4, v;

  for (v = 0; v < g->n; v++)
    if (color[v] == -1 && navail[v] < cbv)
      {
	bv = v;
	cbv = navail[v];
      }

  return bv;
}

static int
try_extend (graph *g)
{
  int bv = find_constrained_vertex (g);
  if (bv == -1)
    return 1;

  int c, till = undo_top;
  for (c = 0; c < 3; c++)
    if (avail[bv][c])
      {
	set_color (g, bv, c);
	if (try_extend (g))
	  return 1;
	undo_till (till);
      }

  return 0;
}

static int
coloring_extends (graph *g, int outer, int col[])
{
  int v, c;

  for (v = 0; v < g->n; v++)
    {
      color[v] = -1;
      for (c = 0; c < 3; c++)
	avail[v][c] = 1;
      navail[v] = 3;
    }
  for (v = 0; v < outer; v++)
    {
      if (!avail[v][col[v]])
	return 0;
      set_color (g, v, col[v]);
    }

  return try_extend (g);
}

static void
dump_coloring (int outer, int col[])
{
  int i;

  for (i = 0; i < outer; i++)
    printf ("%c", '1' + col[i]);
  printf ("\n");
}

static int
bad_parity (int outer, int col[])
{
  int nc[3] = {0, 0, 0};
  int i;

  for (i = 0; i < outer; i++)
    nc[col[i]]++;
  for (i = 0; i < 3; i++)
    if (nc[i] % 2 != outer % 2)
      return 1;
  return 0;
}

static void
test_colorings (graph *g, int col[], int a, int outer, int mx)
{
  int c;

  if (a == outer)
    {
      if (bad_parity (outer, col))
	return;
      if (coloring_extends (g, outer, col))
	printf ("ext ");
      dump_coloring (outer, col);
      return;
    }

  for (c = 0; c < mx; c++)
    {
      col[a] = c;
      test_colorings (g, col, a + 1, outer, mx);
    }
  if (mx < 3)
    {
      col[a] = mx;
      test_colorings (g, col, a + 1, outer, mx + 1);
    }
}

static void
process_configuration (configuration *c)
{
  graph g;
  conf_to_graph (c, &g);

  int outer = c->outer;
  int col[outer];
  test_colorings (&g, col, 0, outer, 0);
}

int main (void)
{
  process_configuration (&birkhoffdiamond);
  return 0;
}
