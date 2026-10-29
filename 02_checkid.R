source("01_utils.R")

# Function to check the universal identification invariance of a clustering operation.
# g = the graph as an igraph object
# clust = vector objects of the cluster vertices (unobserved excluded)
# unobs = vector of all unobserved variables in the graph
# coherent = truth value on whether the cluster can be already assumed to be coherent
# check_c_coherence = truth value on whether c-coherence is assessed. (Most likely an operation not running on polynomial time)
check_id <- function(g, clust, unobs = character(0), coherent = FALSE, 
                     check_c_coherence = FALSE) {
  unobs <- setdiff(unobs, "")
  if (any(clust %in% unobs)) stop("The cluster may not contain unobserved vertices.")
  unobs_children <- children_lst(unobs, g, self = FALSE)
  n_ch <- lengths(unobs_children)
  # Return error if there exists an unobserved vertex with more than two children.
  if (any(n_ch > 2)) {
    stop("Unobserved vertices with more than two children: ",
         paste(unobs[n_ch > 2], collapse = ", "))
  }
  # Unobserved vertices with exactly one child in the cluster and one outside it.
  n_in <- vapply(unobs_children, function(ch) sum(ch %in% clust), integer(1))
  unobs_interesting <- unobs[n_ch == 2 & n_in == 1]
  unobs_internal <- unobs[n_in == n_ch]
  
  if (!coherent) {
    
    # Check coherence
    
    edges <- igraph::E(g)
    heads <- head_of(g, edges)$name
    tails <- tail_of(g, edges)$name
    pa_interesting <- c(setdiff(parents(clust, g), c(clust, unobs)), unobs_interesting)
    ch_g <- setdiff(children(clust, g), clust)
    if (length(intersect(pa_interesting, ch_g)) > 0) return("undetermined")
    H <- modify_clustered_alt(g, edges, heads, tails, clust, pa_interesting, ch_g)
    an_ch_g <- ancestors_lst(ch_g, H)
    # Check whether each parent is among the ancestors of each child,
    # i.e. whether there exists a directed path from each parent to 
    # each child.
    if (length(pa_interesting) > 0 & length(ch_g) > 0) {
      for (p in pa_interesting) {
        for (j in seq_along(ch_g)) {
          if (!(p %in% unlist(an_ch_g[j]))) return("not coherent")
        }
      }
    }
    
  }
  # Check if the cluster is plain
  if (length(unobs_interesting) == 0) return("plain")
  
  pa_g <- lapply(parents_lst(clust, g), \(x) setdiff(x, c(clust, unobs_internal)))
  all_prnts <- uu(pa_g)
  t_stars <- clust[vapply(pa_g, \(x) all(all_prnts %in% x), logical(1))]
  if (length(t_stars) > 0) {
    # unobserved edges
    arcs <- matrix(unlist(unobs_children[n_ch == 2]), ncol = 2, byrow = TRUE)
    # graph whose vertices are bidirected arcs
    bd <- igraph::graph_from_data_frame(as.data.frame(arcs), directed = FALSE,
                                        vertices = setdiff(igraph::V(g)$name, unobs))
    # c-components of this graph
    memb <- igraph::components(bd)$membership
    # descendants of the cluster
    de_star <- setdiff(uu(lapply(igraph::ego(g, order = igraph::vcount(g), nodes = clust,
                                             mode = "out"), names)), clust)
    # check if there are members of c-components that are in the same c-component with
    # the descendants
    if (!any(memb[clust] %in% memb[de_star])) return("c-isolated")   # c-isolated
    if (check_c_coherence) {
      if (is_c_coherent(g, clust, unobs, t_stars)) return("c-coherent")
    }
  }
  return("undetermined")
}

# Vertices of S reachable from S[1] via bidirected arcs inside S
bd_reach <- function(S, bd) {
  # Vertices found so far 
  seen <- S[1]
  # the vertices found in the most recent round, whose neighbours haven't been examined yet.
  frontier <- S[1]
  # keep the loop going as long as something new is found
  while (length(frontier) > 0) {
    # every vertex of S with a bidirected arc to some frontier vertex
    nb <- S[colSums(bd[frontier, S, drop = FALSE]) > 0]
    # keep only the vertices not found before
    frontier <- setdiff(nb, seen)
    seen <- c(seen, frontier)
  }
  seen
}

# Checks if a path P is a c-component. Takes as inputs the path P (vertex set)
# and a matrix of bidirected arcs.
is_connected <- function(P, bd) length(bd_reach(P, bd)) == length(P)

dfs <- function(path, todo, bd, out_ch, succ, useful) {
  v <- path[length(path)]
  if (length(path) > 1 && is_connected(path, bd)) {
    todo <- setdiff(todo, out_ch[[v]])
  }
  for (w in intersect(succ[[v]], useful)) {
    if (length(todo) == 0) break
    res <- dfs(c(path, w), todo, bd, out_ch, succ, useful)
    todo <- res
  }
  todo
}

# c-coherence check
#
# Assumes the cluster has already passed the coherence check. `t_stars` are the
# candidate vertices t* with Pa*(t*) \ T+ = Pa*(T+), i.e. those found by the
# t* check in check_id().
#
# Returns TRUE if some t* certifies c-coherence, FALSE if no t* does

is_c_coherent <- function(g, clust, unobs, t_stars) {
  el <- igraph::as_edgelist(g)
  # Edges inside the cluster
  el_in <- el[el[, 1] %in% clust & el[, 2] %in% clust, , drop = FALSE]
  # Edges going out of the cluster
  el_out <- el[el[, 1] %in% clust & !(el[, 2] %in% clust), , drop = FALSE]
  ch_g <- unique(el_out[, 2])
  # if (length(ch_g) == 0) return(TRUE)
  
  # Children of each cluster variable inside the cluster
  succ <- split(el_in[, 2], factor(el_in[, 1], levels = clust))
  # Children of each cluster variable outside the cluster
  out_ch <- split(el_out[, 2], factor(el_out[, 1], levels = clust))
  
  # Bidirected arcs with both endpoints in the cluster
  bd <- matrix(FALSE, length(clust), length(clust), dimnames = list(clust, clust))
  for (u in unobs) {
    a <- names(igraph::neighbors(g, u, mode = "out"))
    if (length(a) == 2 && all(a %in% clust)) bd[a[1], a[2]] <- bd[a[2], a[1]] <- TRUE
  }
  
  for (ts in t_stars) {
    todo <- setdiff(ch_g, out_ch[[ts]])
    if (length(todo) == 0) return(TRUE)
    
    # Cluster vertices (including t*) connected to t* by bidirected paths that use
    # only arcs with both endpoints in the cluster
    allowed <- bd_reach(c(ts, setdiff(clust, ts)), bd)
    # Vertices in the allowed set that have at least one child outside the cluster
    useful <- allowed[lengths(out_ch[allowed]) > 0]
    while(TRUE) {
      # adds every allowed vertex that has a child already in useful, i.e. 
      # a vertex from which one step leads to a vertex that can already reach a child.
      grown <- union(useful, allowed[vapply(allowed, function(v) any(succ[[v]] %in% useful),
                                            logical(1))])
      if (length(grown) == length(useful)) break
      useful <- grown
    }
    
    res <- dfs(ts, todo, bd, out_ch, succ, useful)
    if (length(res) == 0) return(TRUE)
  }
  return(FALSE)
}

