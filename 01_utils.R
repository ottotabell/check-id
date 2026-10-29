# Some useful helper functions. Some of them have been copied from the private 
# repository related to the article Clustering and Structural Robustness in 
# Causal Diagrams (Tikka et al., 2023)

library(igraph)
library(R.utils)

children <- function(x, g, v = igraph::V(g)) {
  ch_ind <- unlist(igraph::neighborhood(g, order = 1, nodes = x, mode = "out"))
  v[ch_ind]$name
}

children_lst <- function(x, g, v = igraph::V(g), self = TRUE) {
  ch <- igraph::neighborhood(g, order = 1, nodes = x, mindist = 1 - self, mode = "out")
  setNames(lapply(ch, function(i) v[i]$name), v[x]$name)
}

parents <- function(x, g, v = igraph::V(g)) {
  pa_ind <- unlist(igraph::neighborhood(g, order = 1, nodes = x, mode = "in"))
  v[pa_ind]$name
}

parents_lst <- function(x, g, v = igraph::V(g), self = TRUE) {
  pa <- igraph::neighborhood(g, order = 1, nodes = x, mindist = 1 - self, mode = "in")
  setNames(lapply(pa, function(i) v[i]$name), v[x]$name)
}

descendants <- function(x, g, v = igraph::V(g)) {
  de_ind <- unlist(igraph::neighborhood(g, order = length(v), nodes = x, mode = "out"))
  v[de_ind]$name
}

descendants_lst <- function(x, g, v = igraph::V(g), names = TRUE) {
  de <- igraph::neighborhood(g, order = length(v), nodes = x, mode = "out")
  if (!names) {
    return(de)
  }
  setNames(lapply(de, function(i) v[i]$name), v[x]$name)
}

ancestors <- function(x, g, v = igraph::V(g)) {
  an_ind <- unlist(igraph::neighborhood(g, order = length(v), nodes = x, mode = "in"))
  v[an_ind]$name
}

ancestors_lst <- function(x, g, v = igraph::V(g), names = TRUE) {
  an <- igraph::neighborhood(g, order = length(v), nodes = x, mode = "in")
  if (!names) {
    return(an)
  }
  setNames(lapply(an, function(i) v[i]$name), v[x]$name)
}

neighbors_ <- function(x, g, v = igraph::V(g)) {
  ne_ind <- unlist(igraph::neighborhood(g, order = 1, nodes = x, mode = "all"))
  v[ne_ind]$name
}

connected <- function(x, g, v = igraph::V(g)) {
  co_ind <- unlist(igraph::neighborhood(g, order = length(v), nodes = x, mode = "all"))
  v[co_ind]$name
}

uu <- function(x) {
  if (length(x)) unique(unlist(x))
  else character(0)
}

edge_subgraph <- function(g, e, incoming, outgoing) {
  # Setting from and to to NULL to satisfy CRAN if we end up making a package
  # R thinks these are global bindings, but they are igraph-operators for edges
  .to <- .from <- NULL
  e_inc <- e[.to(incoming)]
  e_out <- e[.from(outgoing)]
  igraph::subgraph_from_edges(g, e[setdiff(e, union(e_inc, e_out))], delete.vertices = FALSE)
}

# Convert an igraph graph using causaleffect syntax into a dag
# with explicit latent variables
to_dag <- function(g) {
  out <- g
  unobs_edges <- which(igraph::edge.attributes(g)$description == "U")
  if (length(unobs_edges)) {
    e <- igraph::get.edges(g, unobs_edges)
    e <- e[e[ ,1] > e[ ,2], , drop = FALSE]
    e_len <- nrow(e)
    new_nodes <- paste0("U[", 1:e_len, "]")
    g <- igraph::set.vertex.attribute(g, name = "description", value = "")
    g <- g + igraph::vertices(new_nodes, description = rep("U", e_len))
    v <- igraph::get.vertex.attribute(g, "name")
    g <- g + igraph::edges(c(rbind(new_nodes, v[e[ ,1]]), rbind(new_nodes, v[e[ ,2]])))
    obs_edges <- setdiff(igraph::E(g), igraph::E(g)[unobs_edges])
    out <- igraph::subgraph.edges(g, igraph::E(g)[obs_edges], delete.vertices = FALSE)
  }
  out
}

ancestors_unsrt <- function(node, G) {
  an.ind <- unique(unlist(igraph::neighborhood(G, order = igraph::vcount(G), nodes = node, mode = "in")))
  an <- igraph::V(G)[an.ind]$name
  return(an)
}

parents_unsrt <- function(node, G.obs) {
  pa.ind <- unique(unlist(igraph::neighborhood(G.obs, order = 1, nodes = node, mode = "in")))
  pa <- igraph::V(G.obs)[pa.ind]$name
  return(pa)
}

children_unsrt <- function(node, G) {
  ch.ind <- unique(unlist(igraph::neighborhood(G, order = 1, nodes = node, mode = "out")))
  ch <- igraph::V(G)[ch.ind]$name
  return(ch)
}

# Function to generate the subgraph G[A->B, B->C]

modify_clustered <- function(g, A, pa_X, ch_Y) {
  all_vars <- unique(c(A, pa_X, ch_Y))
  
  # Create subgraph with only these vertices
  sub_g <- induced_subgraph(g, all_vars)
  
  # Remove unwanted edges:
  # - For pa_X: remove edges that don't go TO A
  # - For ch_Y: remove edges that don't come FROM A
  e <- E(sub_g)
  tails <- tail_of(sub_g, e)$name
  heads <- head_of(sub_g, e)$name
  
  edges_to_remove <- e[
    (tails %in% pa_X & !heads %in% A) |
      (heads %in% ch_Y & !tails %in% A)
  ]
  
  sub_g <- delete_edges(sub_g, edges_to_remove)
  return(sub_g)
}

modify_clustered_alt <- function(g, edges, heads, tails, A, pa_X, ch_Y) {
  all_vars <- unique(c(A, pa_X, ch_Y))
  edges_to_keep <- edges[
    (tails %in% pa_X & heads %in% A) |
      (tails %in% A & heads %in% ch_Y) |
      (heads %in% A & tails %in% A)
  ]
  sub_g <- subgraph_from_edges(g, edges_to_keep, delete.vertices = TRUE)
  return(sub_g)
}