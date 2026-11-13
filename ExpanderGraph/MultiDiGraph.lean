/-
Copyright (c) 2025-2026 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/

import Mathlib

import ExpanderGraph.CollisionProb
import ExpanderGraph.ProbabilityVector
import ExpanderGraph.StochasticMatrix

/-!
# MultiDiGraph

This file introduces the structure `MultiDiGraph` along with related definitions and
several API lemmas

## Main definitions

* `MultiDiGraph`
* `adjacencyMatrix`
* `randomWalkMatrix`
* `SpectralGap`
* `neighbourhood_as_multiset`

-/

open Finset Function BigOperators
open CollisionProb
open ProbabilityVector
open StochasticMatrixSpace
open Matrix
open Real
open Classical

namespace MultiDiGraphSpace

-- # MultiDiGraph


/-- A MultiDiGraph is a set of a vertices, a set of edges,
and a map of edges to an ordered pair of vertices -/
structure MultiDiGraph (V E : Type*) where
  /-- graph vertices -/
  vertices : Finset V
  /-- graph edges -/
  edges : Finset E
  /-- map from each edge to the vertices it connects -/
  edgeMap : E → V × V
  edgesValid : ∀ e ∈ edges, edgeMap e ∈ vertices ×ˢ vertices

variable {V E : Type*}

/-- The startpoint of an edge is a vertex -/
lemma fst_mem_vertices {G : MultiDiGraph V E} {e : E}
    (he : e ∈ G.edges) :
    (G.edgeMap e).fst ∈ G.vertices := by
  have h₁ := G.edgesValid e he
  aesop

/-- The endpoint of an edge is a vertex -/
lemma snd_mem_vertices {G : MultiDiGraph V E} {e : E}
    (he : e ∈ G.edges) :
    (G.edgeMap e).snd ∈ G.vertices := by
  have h₁ := G.edgesValid e he
  aesop

/-- The endpoint of an edge is a vertex, alternative statement -/
lemma snd_mem_vertices' {G : MultiDiGraph V E} :
    ∀ e ∈ G.edges, ∃ v ∈ G.vertices, (G.edgeMap e).2 = v := by
  intro e he
  have : (G.edgeMap e).2 ∈ G.vertices := by exact snd_mem_vertices he
  aesop

/-- Incident outedges of a vertex are edges whose first endpoint is that vertex -/
def MultiDiGraph.incidentOutEdges [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : Finset E :=
  {e ∈ G.edges | (G.edgeMap e).fst = v}

/-- An edge is an incident out edge of a vertex iff that edge has the vertex as its first vertex -/
lemma MultiDiGraph.mem_incidentOutEdges [DecidableEq V]
    {G : MultiDiGraph V E} {v : V} {e : E} :
    e ∈ G.incidentOutEdges v ↔ e ∈ G.edges ∧ (G.edgeMap e).fst = v := by
  unfold incidentOutEdges edges edgeMap
  aesop

/-- Incident edges are edges -/
lemma MultiDiGraph.incidentOutEdges_subset_edges [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) :
    G.incidentOutEdges v ⊆ G.edges := by
  unfold incidentOutEdges edges edgeMap
  aesop

/-- When the input is not a vertex there are no incident out edges -/
lemma MultiDiGraph.incidentOutEdges_eq_empty_of_notMem_vertices
    [DecidableEq V] {G : MultiDiGraph V E} {v : V} (hv : v ∉ G.vertices) :
    G.incidentOutEdges v = ∅ := by
  unfold incidentOutEdges
  apply Finset.filter_eq_empty_iff.mpr
  intro e he
  have h := G.edgesValid e he
  rw [Finset.mem_product] at h
  aesop

/-- The out degree of a vertex is the cardinality of the set of incident outedges -/
def MultiDiGraph.OutDegree [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : ℕ := #(G.incidentOutEdges v)

/-- If the input is not a vertex it has zero out degree -/
lemma MultiDiGraph.OutDegree_eq_zero_v_notin_vertices [DecidableEq V]
    (G : MultiDiGraph V E) : ∀ v ∉ G.vertices, G.OutDegree v = 0 := by
  intro v hv
  unfold OutDegree incidentOutEdges
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro e he
  have h₁ := G.edgesValid e he
  rw [Finset.mem_product] at h₁
  aesop

/-- All incident edges of a vertex are all edges that start or finish at that vertex -/
def MultiDiGraph.incidentAllEdges (G : MultiDiGraph V E)
    [DecidableEq V] (v : V) : Finset E :=
  {e ∈ G.edges | (G.edgeMap e).fst = v ∨ (G.edgeMap e).snd = v}

/-- The edges incident at some vertex is a subset of all the edges-/
lemma MultiDiGraph.incidentAllEdges_subset_edges [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) :
    G.incidentAllEdges v ⊆ G.edges := by
  unfold incidentAllEdges edges edgeMap
  aesop

/-- When the input is not a vertex there are no incident edges -/
lemma MultiDiGraph.incidentAllEdges_eq_empty_of_notMem_vertices
    [DecidableEq V] {G : MultiDiGraph V E} {v : V} (hv : v ∉ G.vertices) :
    G.incidentAllEdges v = ∅ := by
  unfold incidentAllEdges --edges edgeMap
  apply Finset.filter_eq_empty_iff.mpr
  intro e he
  have h₁ := G.edgesValid e he
  rw [Finset.mem_product] at h₁
  aesop

/-- The degree of a vertex is the cardinality of the set of incident edges -/
def MultiDiGraph.Degree [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : ℕ := #(G.incidentAllEdges v)

/-- If v is not a vertex it has zero degree -/
lemma MultiDiGraph.Degree_eq_zero_v_notin_vertices [DecidableEq V]
    (G : MultiDiGraph V E) : ∀ v ∉ G.vertices, G.Degree v = 0 := by
  intro v hv
  unfold Degree incidentAllEdges
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro e he
  have h₁ := G.edgesValid e he
  rw [Finset.mem_product] at h₁
  aesop

/-- The incident out edges are a subset of all incident edges -/
lemma MultiDiGraph.incidentOutEdges_subset_incidentAllEdges
    [DecidableEq V] (G : MultiDiGraph V E) (v : V) :
    G.incidentOutEdges v ⊆ G.incidentAllEdges v := by
  unfold incidentOutEdges incidentAllEdges
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨he.1, Or.inl he.2⟩

/-- A regular multidigraph is such that each vertex has the same in and out degree -/
def MultiDiGraph.isRegularOfDegree [DecidableEq V] (G : MultiDiGraph V E) (r : ℕ) :
    Prop :=
  ∀ v ∈ G.vertices, (#(G.edges.filter (fun e => (G.edgeMap e).fst = v)) = r) ∧
      (#(G.edges.filter (fun e => (G.edgeMap e).snd = v)) = r)

/-- If a multidigraph is regular of degree `r`, then the out degrees equals `r`
  for each vertex -/
lemma MultiDiGraph.isRegularOfDegree.outDegree_eq [DecidableEq V]
    (G : MultiDiGraph V E) (r : ℕ) (h : G.isRegularOfDegree r) (v : V) (hv : v ∈ G.vertices) :
    G.OutDegree v = r := (h v hv).1

-- The below definition is being deprecated in favour of `isRegularOfDegree` but
-- is being kept for now until it is certain that all dependencies have been
-- refactored accordingly

/-- A graph is regular if it is regular of some degree -/
def MultiDiGraph.regular [DecidableEq V]
    (G : MultiDiGraph V E) : Prop :=
  ∃ r : ℕ, G.isRegularOfDegree r

lemma MultiDiGraph.regular_lemma [DecidableEq V] (G : MultiDiGraph V E) :
    G.regular ↔ ∃ r : ℕ, G.isRegularOfDegree r := by
  aesop

/-- Neighbourhood: for this purposes of the present project defined as the set of
vertices connected by an out edge (nonstandard in some of the literature) -/
def MultiDiGraph.neighbourhood [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : Finset V :=
  (G.incidentOutEdges v).image fun e ↦ (G.edgeMap e).snd

lemma MultiDiGraph.mem_neighbourhood [DecidableEq V]
    {G : MultiDiGraph V E} {v u : V} :
    u ∈ G.neighbourhood v ↔ ∃ e ∈ G.edges, G.edgeMap e = (v, u) := by
  unfold neighbourhood edgeMap
  simp only [mem_image]
  unfold incidentOutEdges
  aesop

/-- The neighbourhood of any vertex is a subset of the vertices of the graph -/
lemma MultiDiGraph.neighbourhood_subset_vertices [DecidableEq V]
    {G : MultiDiGraph V E} {u : V} :
    G.neighbourhood u ⊆ G.vertices := by
  have h₀ : ∀ v ∈ G.neighbourhood u, ∃ e ∈ G.edges, (G.edgeMap e).snd = v := by
    intro v hv
    have h₀ : ∃ e₁ ∈ G.edges, (G.edgeMap e₁).fst = u ∧ (G.edgeMap e₁).snd = v := by
      unfold neighbourhood incidentOutEdges at hv
      aesop
    obtain ⟨e₁, he⟩ := h₀
    use e₁
    exact ⟨he.1, (he.2).2 ⟩
  have h₁ : ∀ e ∈ G.edges, (G.edgeMap e).snd ∈ G.vertices := by
    intro e he
    exact snd_mem_vertices he
  intro v hv
  obtain ⟨e, he, heq⟩ := h₀ v hv
  rw [←heq]
  exact h₁ e he

/-- Neighbourhood of a set of vertices -/
def MultiDiGraph.neighbourhoodOfSet [DecidableEq V]
    (G : MultiDiGraph V E) (vs : Finset V) : Finset V := vs.biUnion G.neighbourhood

/-- A cut is the set of edges from a set of vertices to its complemen -/
def MultiDiGraph.cut [DecidableEq V]
    (G : MultiDiGraph V E) (S : Finset V) : Finset E :=
  G.edges.filter (fun e =>
    let (u, v) := G.edgeMap e
    u ∈ S ∧ v ∈ G.vertices \ S)

/-- The set of edges from `S`, a subset of vertices to `T` another subset of vertices -/
def MultiDiGraph.eST [DecidableEq V]
    (G : MultiDiGraph V E) (S : Finset V) (T : Finset V) : ℕ :=
  #(G.edges.filter (fun e =>
    let (u, v) := G.edgeMap e
    u ∈ S ∧ v ∈ T))

/-- The size of the neighbourhood of a single vertex is at most its degree -/
lemma MultiDiGraph.neighbourhood_of_singleton_size_leq_degree [DecidableEq V]
    (G : MultiDiGraph V E) (S : Finset V) (hS : (#S : ℝ) = 1)
    (hS₀ : S ⊆ G.vertices) {r : ℕ} (hG : G.isRegularOfDegree r) :
    (#(G.neighbourhoodOfSet S) : ℝ) ≤ r := by
  unfold MultiDiGraph.neighbourhoodOfSet MultiDiGraph.neighbourhood
  unfold MultiDiGraph.isRegularOfDegree at hG
  have hSa : #S = 1 := by aesop
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hSa
  subst hv
  simp only [Finset.singleton_biUnion]
  unfold MultiDiGraph.incidentOutEdges
  have : v ∈ G.vertices := by exact singleton_subset_iff.mp hS₀
  specialize hG v this
  apply Nat.cast_le.mpr
  simp_all only [Nat.cast_one, singleton_subset_iff, card_singleton]
  obtain ⟨left, right⟩ := hG
  subst left
  apply Finset.card_image_le

/-- For each vertex in neighbourhood the neighbour of some `u`,
    it is the end-point of an edge whose start-point is `u` -/
lemma MultiDiGraph.exist_edge_vertex_in_neighbourhood [DecidableEq V]
    (G : MultiDiGraph V E) (u v : V) (hv : v ∈ G.neighbourhood u):
    ∃ e ∈ G.edges, (G.edgeMap e).1 = u ∧ (G.edgeMap e).2 = v := by
  unfold MultiDiGraph.neighbourhood MultiDiGraph.incidentOutEdges at hv
  aesop

/-- For regular graphs of non-zero degree, all non-empty subsets of
    vertices have non-empty neighbourhoods -/
lemma MultiDiGraph.regular_of_non_zero_deg_neighbour_nonempty [DecidableEq V]
    (G : MultiDiGraph V E) (r : ℕ) (hr : 0 < r) (hG: G.isRegularOfDegree r) :
    ∀ S ⊆ G.vertices, (0 < #S) → 0 < (#(G.neighbourhoodOfSet S) : ℝ) := by
  intro S hS1 hS2
  unfold MultiDiGraph.isRegularOfDegree at hG
  unfold neighbourhoodOfSet neighbourhood
  simp only [Nat.cast_pos, card_pos, biUnion_nonempty, image_nonempty]
  unfold incidentOutEdges
  have : ∀ v ∈ G.vertices, #({e ∈ G.edges | (G.edgeMap e).1 = v}) = r := by
    aesop
  have : ∀ v ∈ S, #({e ∈ G.edges | (G.edgeMap e).1 = v}) = r := by
    aesop
  have h₀ : ∀ v ∈ S, {e ∈ G.edges | (G.edgeMap e).1 = v}.Nonempty := by
    have : ∀ v ∈ S, 0 < #({e ∈ G.edges | (G.edgeMap e).1 = v}) := by
      aesop
    exact fun v a ↦ (fun {α} {s} ↦ card_pos.mp) (this v a)
  have h₁ : S.Nonempty := by exact card_pos.mp hS2
  have ⟨y, hy⟩ := h₁
  specialize h₀ y
  aesop

-- # Adjacency Matrix

/-- The adjacency matrix of a multidigraph -/
def MultiDiGraph.adjacencyMatrix [DecidableEq V]
    (G : MultiDiGraph V E) : Matrix V V ℕ :=
  Matrix.of (fun u v => #{e ∈ G.edges | (G.edgeMap e).fst = u ∧ (G.edgeMap e).snd = v})

/-- Elements of the adjacency matrix outside of the square corresponding to the vertices
equal zero. This lemma asserts this for certain such elements. -/
lemma MultiDiGraph.adjacencyMatrix_zero_if_not_vertices [DecidableEq V]
    (G : MultiDiGraph V E) (i : V) (j : V) (hj : j ∉ G.vertices) :
    G.adjacencyMatrix i j = 0 := by
  unfold MultiDiGraph.adjacencyMatrix Matrix.of
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro e he
  have h := G.edgesValid e he
  simp only [Finset.mem_product] at h
  intro ⟨hfst, hsnd⟩
  aesop

/-- The adjacency matrix has entries zero when the column and /
    or row index is not that of a vertex -/
lemma MultiDiGraph.adjacencyMatrix_zero_if_not_vertices' [DecidableEq V]
    (G : MultiDiGraph V E) (i : V) (j : V) (hi : i ∉ G.vertices) :
    G.adjacencyMatrix i j = 0 := by
  unfold MultiDiGraph.adjacencyMatrix
  simp
  have : ∀ e ∈ G.edges, (G.edgeMap e).1 ∈ G.vertices := by exact fun e a ↦ fst_mem_vertices a
  aesop

/-- The row sums of an adjacency matrix equal the out degree of the corresponding vertex -/
lemma MultiDiGraph.sum_adjacencyMatrix_eq_outDegree [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) (i : V) :
    ∑ j, G.adjacencyMatrix i j = G.OutDegree i := by
  simp_rw [adjacencyMatrix, of_apply, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp_rw [and_comm (a := (G.edgeMap _).1 = _), ite_and, sum_ite_eq]
  simp only [mem_univ, ↓reduceIte, sum_boole, Nat.cast_id, OutDegree, incidentOutEdges]

/-- If a multidigraph is regular each row sum is the same and equal to the degree -/
lemma MultiDiGraph.adjacencyMatrix_row_sum_const_if_regular
    [Fintype V] [DecidableEq V] (G : MultiDiGraph V E) (r : ℕ)
    (hr : G.isRegularOfDegree r) :
    ∀ i ∈ G.vertices, ∑ j, G.adjacencyMatrix i j = r := by
  intro i hi
  simp_rw [adjacencyMatrix, of_apply, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp_rw [and_comm (a := (G.edgeMap _).1 = _), ite_and, sum_ite_eq]
  simp only [mem_univ, ↓reduceIte, sum_boole, Nat.cast_id]
  exact (hr i hi).1

/-- If a multidigraph is regular each column sum is the same and equal to the degree -/
lemma MultiDiGraph.adjacencyMatrix_col_sum_const_if_regular
    [Fintype V] [DecidableEq V] (G : MultiDiGraph V E) (r : ℕ)
    (hr : G.isRegularOfDegree r) :
    ∀ i ∈ G.vertices, ∑ j, G.adjacencyMatrix.transpose i j = r := by
  intro i hi
  simp_rw [adjacencyMatrix, Matrix.transpose_apply, of_apply, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp_rw [ite_and, sum_ite_eq]
  simp only [mem_univ, ↓reduceIte, sum_boole, Nat.cast_id]
  exact (hr i hi).2

-- This fact is also proved for a slightly different statement thereof

/-- If a multidigraph is regular each column sum is the same and equal to the degree -/
lemma MultiDiGraph.adjacencyMatrix_col_sum_const_if_regular'
    [Fintype V] [DecidableEq V] (G : MultiDiGraph V E) (r : ℕ)
    (hr : G.isRegularOfDegree r) :
    ∀ i ∈ G.vertices, ∑ j, G.adjacencyMatrix j i = r := by
  have := G.adjacencyMatrix_col_sum_const_if_regular  r hr
  simpa using this

/-- A regular graph with non-zero degree has an adjacency
  matrix with a non-zero entry in each row -/
lemma MultiDiGraph.non_zero_degree_adjacency_has_nonzero_entry
    [DecidableEq V] (G : MultiDiGraph V E) {r : ℕ} (hr : 0 < r)
    (hr1 : G.isRegularOfDegree r) (u : V) (hu : u ∈ G.vertices) :
    ∃ v, 0 < G.adjacencyMatrix u v := by
  unfold MultiDiGraph.isRegularOfDegree at hr1
  unfold MultiDiGraph.adjacencyMatrix
  simp only [of_apply, card_pos]
  have hG1a : ∀ v ∈ G.vertices, #({e ∈ G.edges | (G.edgeMap e).1 = v}) = r := by aesop
  have h₀ : {e ∈ G.edges | (G.edgeMap e).1 = u}.Nonempty →
      ∃ v, {e ∈ G.edges | (G.edgeMap e).1 = u ∧ (G.edgeMap e).2 = v}.Nonempty := by
    intro hua
    have h₁ : ∀ e ∈ G.edges, ∃ v ∈ G.vertices, (G.edgeMap e).2 = v :=
      fun e a ↦ snd_mem_vertices' e a
    obtain ⟨e₁, he⟩ := hua
    have hea : e₁ ∈ G.edges := by exact mem_of_mem_filter e₁ he
    have heb : (G.3 e₁).1 = u := by aesop
    specialize h₁ e₁ hea
    obtain ⟨vv, hvv⟩ := h₁
    use vv
    have : e₁ ∈ {e ∈ G.edges | (G.edgeMap e).1 = u ∧ (G.edgeMap e).2 = vv} := by aesop
    exact ⟨e₁, this⟩
  have h₁ : {e ∈ G.edges | (G.edgeMap e).1 = u}.Nonempty := by
    specialize hG1a u hu
    aesop
  aesop

 -- # Random Walk Matrix

/-- The random walk matrix of an adjacency matrix is obtained by normalising the rows
by convention we place a one on the leading diagonal for all-zero rows, such that the
result is a stochastic matrix -/
noncomputable def MultiDiGraph.randomWalkMatrix [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) : Matrix V V ℝ :=
  Matrix.of fun u v => if (∑ v, G.adjacencyMatrix u v : ℝ) = 0 then (if u = v then (1: ℝ) else
    (0: ℝ)) else (G.adjacencyMatrix u v : ℝ) / (∑ v, G.adjacencyMatrix u v : ℝ)

lemma MultiDiGraph.randomWalkMatrix_apply_eq [Fintype V] [DecidableEq V] (G : MultiDiGraph V E)
    (u v : V) :
    G.randomWalkMatrix u v =
      if G.OutDegree u = 0
        then (if u = v then 1 else 0)
        else (G.adjacencyMatrix u v : ℝ) / G.OutDegree u := by
  simp [MultiDiGraph.randomWalkMatrix, MultiDiGraph.sum_adjacencyMatrix_eq_outDegree,
    ← Nat.cast_sum]

/-- By construction outside of the support the adjacency matrix is diagonal -/
lemma MultiDiGraph.diagonal_outside_support_randomWalkMatrix [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) :
    ∀ i ∉ G.vertices, G.randomWalkMatrix i i = 1 := by
  unfold randomWalkMatrix
  intro i hi
  simp [G.adjacencyMatrix_zero_if_not_vertices' _ _ hi]

/-- All elements of a randomWalkMatrix are non-negative -/
lemma MultiDiGraph.randomWalkMatrixNonNegative [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) : ∀ j, ∀ i, 0 ≤ G.randomWalkMatrix i j := by
  intros _ _
  unfold MultiDiGraph.randomWalkMatrix
  simp only [Matrix.of_apply]
  split_ifs
  all_goals
  positivity

/-- If an element of a random walk matrix is non-zero, the corresponding element of
the adjacency matrix is also non-zero (the leading diagonal is excluded) -/
lemma MultiDiGraph.non_zero_randomwalk_imp_nonzero_adjacency_in_vertices
    [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) (u v : V)
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    0 < G.randomWalkMatrix u v ∧ u ∈ G.vertices → 0 < G.adjacencyMatrix u v := by
  intro h₀
  have h₁ : 0 < G.randomWalkMatrix u v := h₀.1
  have h₂ : u ∈ G.vertices := h₀.2
  unfold MultiDiGraph.randomWalkMatrix at h₁
  simp only [of_apply] at h₁
  have h₃ : 0 < ∑ v, (G.adjacencyMatrix u v : ℝ) := by
    have h₃a' : ∀ (i j : V), 0 ≤ (G.adjacencyMatrix i j : ℝ) := fun i j ↦
      Nat.cast_nonneg' (G.adjacencyMatrix i j)
    have h₃b : ∃ v, 0 < G.adjacencyMatrix u v := by
      exact non_zero_degree_adjacency_has_nonzero_entry G hr hr1 u h₂
    obtain ⟨v₀, hv₀⟩ := h₃b
    have ha: ∑ v, (G.adjacencyMatrix u v : ℝ)
        = ∑ v ∈ {v₀}, (G.adjacencyMatrix u v : ℝ)
        + ∑ v ∉ {v₀}, (G.adjacencyMatrix u v : ℝ) := by
      rw [← Finset.sum_union]
      all_goals
      aesop
    rw [ha]
    have ha₁ : 0 < ∑ v ∈ {v₀}, (G.adjacencyMatrix u v : ℝ) := by
      have : ∑ v ∈ {v₀}, (G.adjacencyMatrix u v : ℝ) = (G.adjacencyMatrix u v₀ : ℝ) := by
        aesop
      rw [this]
      exact Nat.cast_pos'.mpr hv₀
    have ha₂ : 0 ≤ ∑ v ∈ {v₀}ᶜ, (G.adjacencyMatrix u v : ℝ) := by
      exact sum_nonneg fun i a ↦ h₃a' u i
    exact Right.add_pos_of_pos_of_nonneg ha₁ ha₂
  have h₃a :  ∑ v, (G.adjacencyMatrix u v : ℝ) ≠ 0 := by exact Ne.symm (ne_of_lt h₃)
  rw [ite_eq_right h₃a] at h₁
  refine Nat.zero_lt_of_ne_zero ?_
  aesop

/-- An element of a random walk matrix is strictly positive iff the element corresponds to a pair of
vertices such that one is in the neighbourhood of the other -/
lemma MultiDiGraph.randomWalkMatrix_pos_iff_mem_neighbourhood
    [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) (u v : V) (hu : u ∈ G.vertices)
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    0 < G.randomWalkMatrix u v ↔ v ∈ G.neighbourhood u := by
  constructor
  · intro huv
    have h₀ : 0 < G.randomWalkMatrix u v ∧ u ∈ G.vertices → 0 < G.adjacencyMatrix u v := by
      exact fun a ↦ non_zero_randomwalk_imp_nonzero_adjacency_in_vertices G u v r hr hr1 a
    have h₁ : 0 < G.adjacencyMatrix u v := by aesop
    unfold neighbourhood incidentOutEdges
    unfold adjacencyMatrix at h₁
    simp only [of_apply, card_pos] at h₁
    simp_all only [and_self, forall_const, mem_image, mem_filter]
    rcases h₁ with ⟨a, ha⟩
    aesop
  · intro hv
    have h₀ : ∃ e ∈ G.edges, (G.edgeMap e).1 = u ∧ (G.edgeMap e).2 = v := by
      exact exist_edge_vertex_in_neighbourhood G u v hv
    have h₁ : 0 < G.adjacencyMatrix u v := by
      unfold MultiDiGraph.adjacencyMatrix
      simp only [of_apply, card_pos]
      obtain ⟨e, heG, he₁, he₂⟩ := h₀
      use e
      aesop
    have h₁a: 0 < (G.adjacencyMatrix u v : ℝ) := by exact Nat.cast_pos'.mpr h₁
    have h₂ : 0 < ∑ x, (G.adjacencyMatrix u x : ℝ) := by
      have : ∑ x, (G.adjacencyMatrix u x : ℝ)
          = ∑ x ∈ {v}, (G.adjacencyMatrix u x : ℝ)
          + ∑ x ∉ {v}, (G.adjacencyMatrix u x : ℝ) := by
        rw [← Finset.sum_union]
        all_goals
        aesop
      rw [this]
      have : 0 < ∑ x ∈ {v}, (G.adjacencyMatrix u x : ℝ) := by
        have : ∑ x ∈ {v}, (G.adjacencyMatrix u x : ℝ) = (G.adjacencyMatrix u v : ℝ) := by aesop
        rw [this]
        exact h₁a
      have : 0 ≤ ∑ x ∉ {v}, (G.adjacencyMatrix u x : ℝ) := by
        apply Finset.sum_nonneg
        intro i hi
        exact Nat.cast_nonneg' (G.adjacencyMatrix u i)
      linarith
    unfold MultiDiGraph.randomWalkMatrix
    simp
    aesop


/-- All elements of a randomWalkMatrix are non-negative -/
lemma MultiDiGraph.randomWalkMatrixNonNegative1 [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) : ∀ i j, 0 ≤ G.randomWalkMatrix i j := by
  intros _ _
  unfold MultiDiGraph.randomWalkMatrix
  simp only [Matrix.of_apply]
  split_ifs
  all_goals
  positivity

/-- The rows of the randomwalkMatrix sum to one -/
lemma MultiDiGraph.randomWalkMatrixSumtoOne1 [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) :
    ∀ j , ∑ i , G.randomWalkMatrix j i = 1 := by
  intro j
  unfold randomWalkMatrix
  simp only [Matrix.of_apply, sum_ite_irrel, sum_ite_eq, mem_univ, ↓reduceIte, ite_eq_left_iff]
  intro hv
  let r := ∑ v, ↑(G.adjacencyMatrix j v)
  rw [← Finset.sum_div]
  field_simp


/-- Random walk matrices are row stochastic -/
lemma MultiDiGraph.randomWalkMatrixIsStochasticA [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E): G.randomWalkMatrix ∈  StochasticMatrixSpace.rowStochastic ℝ V :=
  StochasticMatrixSpace.mem_rowStochastic_iff_sum.2
    ⟨G.randomWalkMatrixNonNegative1, G.randomWalkMatrixSumtoOne1⟩


/-- If a graph is regular of non-zero degree the columns of its randomWalkMatrix sum to one -/
lemma MultiDiGraph.Regular_randomWalkMatrix_cols_SumtoOne [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E) {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r) :
    ∀ i, ∑ j, G.randomWalkMatrix j i = 1 := by
  intro i
  unfold randomWalkMatrix
  simp only [← Nat.cast_sum, sum_adjacencyMatrix_eq_outDegree]
  simp only [Matrix.of_apply]
  rw [sum_ite]
  rw [sum_ite_eq']
  simp only [Nat.cast_eq_zero, mem_filter, mem_univ, true_and]
  by_cases hi : i ∈ G.vertices
  -- this is true because the adjacency matrix columns and rows each sum to the degree
  -- when the graph is regular
  · rw [ite_eq_right, zero_add]
    -- cases where out degree is zero (cannot happen) and non-zero
    swap
    · unfold OutDegree incidentOutEdges
      unfold isRegularOfDegree at hG
      specialize hG i hi
      by_contra _
      aesop
    -- this block is now what informally one would go to directly: the degree is non-zero and
    -- we are addressing columns corresponding to vertices
    have : ∑ v with ¬ G.OutDegree v = 0, (G.adjacencyMatrix v i : ℝ) / G.OutDegree v =
          ∑ v with ¬ G.OutDegree v = 0, (G.adjacencyMatrix v i : ℝ) / r := by
      apply Finset.sum_congr rfl fun v hv ↦ ?_
      have : v ∈ G.vertices := by
        by_contra
        have := G.OutDegree_eq_zero_v_notin_vertices _ this
        aesop
      rw [hG.outDegree_eq]
      exact this
    rw [this]
    rw [← Finset.sum_div, ← Nat.cast_sum]
    have : ∑ v with ¬ G.OutDegree v = 0, G.adjacencyMatrix v i =
           ∑ v, G.adjacencyMatrix v i := by
      have : ∑ v, G.adjacencyMatrix v i = ∑ v with ¬G.OutDegree v = 0, G.adjacencyMatrix v i +
          ∑ v with G.OutDegree v = 0, G.adjacencyMatrix v i := by
        exact
          Eq.symm
            (sum_filter_not_add_sum_filter univ (fun x ↦ G.OutDegree x = 0) fun x ↦
              G.adjacencyMatrix x i)
      rw [this]
      have : ∑ v with G.OutDegree v = 0, G.adjacencyMatrix v i = 0 := by
        unfold adjacencyMatrix OutDegree incidentOutEdges
        simp only [card_eq_zero, of_apply, sum_eq_zero_iff, mem_filter, mem_univ, true_and]
        intro i1 hi1
        have : {e ∈ G.edges | (G.edgeMap e).1 = i1 ∧ (G.edgeMap e).2 = i} ⊆
            {e ∈ G.edges | (G.edgeMap e).1 = i1} := by
          intro e₁ he
          have h₁ : e₁ ∈ G.edges := by exact mem_of_mem_filter e₁ he
          have h₂ : (G.edgeMap e₁).1 = i1 := by
            aesop
          simp only [mem_filter]
          exact ⟨h₁, h₂⟩
        aesop
      rw [this]
      linarith
    rw [this]
    rw [adjacencyMatrix_col_sum_const_if_regular' G r hG]
    · by_cases hr : (r : ℝ) = 0
      all_goals
      aesop
    assumption
  -- the case where `i` is not a vertex; this is from the construction
  · have : (if G.OutDegree i = 0 then 1 else 0) = (1 : ℝ) := by
      have : ∀ v ∉ G.vertices, G.OutDegree v = 0 := fun v a ↦
        OutDegree_eq_zero_v_notin_vertices G v a
      specialize this i hi
      aesop
    rw [this]
    have : ∑ x with ¬G.OutDegree x = 0, (G.adjacencyMatrix x i : ℝ) / (G.OutDegree x : ℝ) = 0 := by
      have : ∀ i ∉ G.vertices, ∀ x, G.adjacencyMatrix x i = 0 := fun i a x ↦
        adjacencyMatrix_zero_if_not_vertices G x i a
      aesop
    rw [this]
    linarith

/--  By construction, outside of the square corresponding to the vertices the random walk matrix
is zero except for on the leading diagonal -/
lemma MultiDiGraph.random_walk_zero_off_diagonal_outside_vertices
    [Fintype V] [DecidableEq V] (G : MultiDiGraph V E)
    (v u : V) (huv : u ≠ v) (hv : v ∉ G.vertices) :
    G.randomWalkMatrix u v = 0 := by
  unfold randomWalkMatrix
  have : G.adjacencyMatrix u v = 0 := by
    exact adjacencyMatrix_zero_if_not_vertices G u v hv
  simp only [of_apply]
  aesop

/-- Regular graphs have random walk matrices that are doubly stochastic -/
lemma MultiDiGraph.RegularrandomWalkMatrixIsDoublyStochastic
    [Fintype V] [DecidableEq V] [DecidableEq E] (G : MultiDiGraph V E)
    {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r) : G.randomWalkMatrix ∈ doublyStochastic ℝ V :=
  mem_doublyStochastic_iff_sum.2 ⟨G.randomWalkMatrixNonNegative1,
    G.randomWalkMatrixSumtoOne1, (G.Regular_randomWalkMatrix_cols_SumtoOne hr hG)⟩

/--  Random walk matrices of regular graphs are doubly stochastic and leading diagonal
    elements equal one outside of the square corresponding to the vertices -/
lemma MultiDiGraph.Regular_is_DoublyStochastic [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E) {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r) :
    G.randomWalkMatrix ∈ doublyStochastic ℝ V ∧ ∀ l ∉ G.vertices, G.randomWalkMatrix l l = 1  := by
  constructor
  · exact MultiDiGraph.RegularrandomWalkMatrixIsDoublyStochastic G hr hG
  · intro l hl
    exact MultiDiGraph.diagonal_outside_support_randomWalkMatrix G l hl


/-- A probability vector multiplied by a random walk matrix has elements equal to zero
outside of the support -/
lemma if_not_vertex_prod_of_p_randomwalk_matrix_eq_zero [Fintype V]
    [DecidableEq V]
    (G : MultiDiGraph V E) (p : V → ℝ) (hχTperp0 : ∀ i ∉ G.vertices, p i = 0) :
    ∀ i ∉ G.vertices, (p ᵥ* G.randomWalkMatrix) i = 0 := by
  intro j hj
  simp only [vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : ∑ x, p x * G.randomWalkMatrix x j = ∑ x ∉ {j}, p x * G.randomWalkMatrix x j
      + ∑ x ∈ {j}, p x * G.randomWalkMatrix x j :=
        Eq.symm (sum_compl_add_sum {j} fun i ↦ p i * G.randomWalkMatrix i j)
  rw [this]
  have : ∑ x ∈ {j}, p x * G.randomWalkMatrix x j = p j * G.randomWalkMatrix j j :=
    sum_singleton (fun x ↦ p x * G.randomWalkMatrix x j) j
  rw [this]
  have : p j = 0 := by exact hχTperp0 j hj
  rw [this]
  have : ∑ x ∈ {j}ᶜ, p x * G.randomWalkMatrix x j = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    have : G.randomWalkMatrix x j = 0 := by
      have : x ≠ j := by aesop
      exact MultiDiGraph.random_walk_zero_off_diagonal_outside_vertices G j x this hj
    rw [this]
    linarith
  rw [this]
  linarith

/-- The random walk matrix of a regular graph is a constant factor multiplied by
the adjacency. In particular, this constant factor is the reciprocal of the degree -/
lemma MultiDiGraph.regular_adjacency_is_r_times_random_walk [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) (r: ℕ) (hr0 : 0 ≠ r)
    (hr : G.isRegularOfDegree r) :
    ∀i ∈ G.vertices, ∀j , (r : ℝ) * G.randomWalkMatrix i j
    = (G.adjacencyMatrix i j : ℝ) := by
  intro i hi j
  unfold randomWalkMatrix
  simp only [of_apply, mul_ite, mul_one, mul_zero]
  have : ∀ u ∈ G.vertices, ∑ v, (G.adjacencyMatrix u v : ℝ) = r := by
    intro u hu
    have : ∑ v, G.adjacencyMatrix u v = r :=
      adjacencyMatrix_row_sum_const_if_regular G r hr u hu
    aesop
  rw [this]
  · simp only [Nat.cast_eq_zero]
    have : (r : ℝ) * ((G.adjacencyMatrix i j : ℝ) / (r : ℝ)) = (G.adjacencyMatrix i j : ℝ) := by
      field_simp
    rw [this]
    simp_all only [ne_eq, CharP.cast_eq_zero, ite_self, ite_eq_right_iff]
    intro a
    subst a
    simp_all only [not_true_eq_false]
  · exact hi

-- # Spectral gap

/-- The spectral gap of the random walk matrix of a MultiDiGraph -/
noncomputable def MultiDiGraph.SpectralGap [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) : ℝ :=
  1 - sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G.vertices) ∧ (p ≠ UniformDist G.vertices) ∧
    (y = √ (L2normSQ ((p ᵥ* G.randomWalkMatrix) - UniformDist (G.vertices)) G.vertices)
    / √ (L2normSQ (p - UniformDist (G.vertices)) G.vertices))}


/-- Support of random walk matrix applied to a probability vector is the
neighbourhood of the set of vertices with non-zero probability -/
lemma SupportNeighbourhood [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) (p : V → ℝ) (hp: IsProbVector p G.vertices)
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    Support (Matrix.vecMul p G.randomWalkMatrix) G.vertices =
    G.neighbourhoodOfSet (Support p G.vertices) := by
  -- first establish that the matrix after the multiplication is non-zero everywhere
  have nonneg : ∀ u v, 0 ≤ p u * G.randomWalkMatrix u v := by
    intro u v
    apply mul_nonneg
    · exact hp.nonneg _
    · exact G.randomWalkMatrixNonNegative1 _ _
  -- this is now the main proof, which is decomposed as inclusions in each direction
  apply subset_antisymm
  · simp only [Support, ne_eq, MultiDiGraph.neighbourhoodOfSet, subset_iff, mem_filter,
    mem_biUnion, and_imp]
    intro v hv hv'
    simp only [vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hv'
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv'
    have hu' : 0 < p u * G.randomWalkMatrix u v := lt_of_le_of_ne (nonneg _ _) hu.symm
    have hpu : 0 < p u := by
      by_contra!
      have : p u = 0 := le_antisymm this (hp.nonneg _)
      simp [this] at hu'
    have : 0 < G.randomWalkMatrix u v := by
      by_contra!
      have : G.randomWalkMatrix u v = 0 := le_antisymm this (G.randomWalkMatrixNonNegative1 _ _)
      simp [this] at hu'
    have : u ∈ G.vertices := by
      by_contra
      simp [hp.2.2 _ this] at hpu
    use u
    refine ⟨by simp [*, hpu.ne'], ?_⟩
    rwa [← MultiDiGraph.randomWalkMatrix_pos_iff_mem_neighbourhood]
    --· exact this
    -- all_goals
    -- assumption
  · simp only [MultiDiGraph.neighbourhoodOfSet, Support, ne_eq, subset_iff, mem_biUnion,
      mem_filter, forall_exists_index, and_imp]
    intro u v hv hv' hu
    refine ⟨MultiDiGraph.neighbourhood_subset_vertices hu, ?_⟩
    have : 0 < p v := lt_of_le_of_ne (hp.nonneg _) (Ne.symm hv')
    have : 0 < G.randomWalkMatrix v u := by
      rwa [MultiDiGraph.randomWalkMatrix_pos_iff_mem_neighbourhood]
      -- all_goals
      -- assumption
    have : 0 < p v * G.randomWalkMatrix v u := by positivity
    simp only [vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply ne_of_gt
    apply sum_pos'
    · simpa using (nonneg · u)
    use v
    simpa using this
variable {n : Type*} [Fintype n] [DecidableEq n]
variable  {M : Matrix n n ℝ}
variable {v : n → ℝ}

-- Note the following lemma essentially follows from StochasticMatrix and is just being
-- restated here such that it is in exactly the form needed in the bigger results that follow

/-- doubly stochastic matrices are certainly row stochastic -/
lemma double_stochastic_imp_row_stochastic :
    M ∈ doublyStochastic ℝ n → M ∈ StochasticMatrixSpace.rowStochastic ℝ n := by
  unfold doublyStochastic StochasticMatrixSpace.rowStochastic
  aesop

-- The following is a result about doubly stochastic matrices, and in the Mathlib PR has been
-- included however as for this project it is only needed for results in this file, it is being
-- kept here for now


/-- Left multiplication of a row stochastic matrix by a vector that is a
probability distribution over a subset of the elements of the space such that
for those elements not included, the stochastic matrix is diagonal gives a
probability distribution over the same space-/
lemma pdist_subset_vecMul_of_mem_doublyStochastic (hMa : M ∈ doublyStochastic ℝ n)
    (m : Finset n) (hm : (0 < #m) ∧ ∀ i ∉ m, M i i = 1)
    (hv : (∀ i ∈ m, 0 ≤ v i) ∧ (∑ i ∈ m, v i = 1) ∧ ∀ i ∉ m, v i = 0) :
    (∀ j ∈ m, 0 ≤ (v ᵥ* M) j) ∧ (∑ j ∈ m, (v ᵥ* M) j =1) ∧  ∀ j ∉ m, (v ᵥ* M) j = 0 := by
  have hM : M ∈ StochasticMatrixSpace.rowStochastic ℝ n :=
      by exact double_stochastic_imp_row_stochastic hMa
  constructor
  -- break the goal into its two conjoined components, the first is easy
  · have : ∀ i , 0 ≤ v i := by
      intro i
      by_cases hi : i ∈ m
      all_goals
      aesop
    have : ∀ j, 0 ≤ (v ᵥ* M) j := StochasticMatrixSpace.nonneg_vecMul_of_mem_rowStochastic hM this
    aesop
  · have h₀ : ∀ j ∉ m, (v ᵥ* M) j = 0 := by
      -- establish that outside of the support the value is zero
      intro j hj
      have : (v ᵥ* M) j = ∑ i, v i * M i j := by
        exact rfl
      rw [this]
      have : ∑ i, v i * M i j = ∑ i ∈ m, v i * M i j + ∑ i ∉ m, v i * M i j := by
        exact Eq.symm (sum_add_sum_compl m fun i ↦ v i * M i j)
      rw [this]
      have : ∑ i ∉ m, v i * M i j = 0 := by
        rw [Finset.sum_eq_zero]
        intro x hx
        have : v x = 0 := by aesop
        rw [this]
        exact Lean.Grind.Semiring.zero_mul (M x j)
      rw [this]
      have : ∑ i ∈ m, v i * M i j = 0 := by
        rw [Finset.sum_eq_zero]
        intro x hx
        have : M x j = 0 := by
          have h₀a : M j j = 1 := by exact hm.2 j hj
          have h₀b : ∑ i, M i j = 1 := by exact sum_col_of_mem_doublyStochastic hMa j
          have h₀c : ∀ i, 0 ≤ M i j := by exact fun i ↦ nonneg_of_mem_doublyStochastic hMa
          have h₀d : ∑ i, M i j = ∑ i ∈ {j}ᶜ, M i j + ∑ i ∉ {j}ᶜ, M i j := by
            exact Eq.symm (sum_add_sum_compl {j}ᶜ fun i ↦ M i j)
          rw [h₀d] at h₀b
          have : ∑ i ∈ {j}ᶜᶜ, M i j = M j j := by aesop
          rw [this] at h₀b
          rw [h₀a] at h₀b
          have h₀e : ∑ i ∈ {j}ᶜ, M i j = 0 := by linarith
          have h₀f : ∀ i ≠ j, M i j = 0 := by
            intro j' _
            rw [Finset.sum_eq_zero_iff_of_nonneg (fun j' _ ↦ h₀c j')] at h₀e
            aesop
          have : x ≠ j := by aesop
          aesop
        rw [this]
        exact Lean.Grind.Semiring.mul_zero (v x)
      rw [this]
      linarith
    -- Having established `h₀` the remaining two parts of the claim can be closed in turn
    constructor
    · have h₁ : ∑ j, (v ᵥ* M) j = 1 := by
        have : (∀ i : n, 0 ≤ v i) ∧ ∑ i : n, v i = 1 := by
          constructor
          · intro i
            by_cases hm : i ∈ m
            · aesop
            · aesop
          · have : ∑ i, v i = ∑ i ∈ m, v i + ∑ i ∉ m, v i := by
              exact Eq.symm (sum_add_sum_compl m v)
            rw [this]
            have : ∑ i ∈ m, v i = 1 := by exact (hv.2).1
            rw [this]
            have :  ∑ i ∉ m, v i = 0 := by
              rw [Finset.sum_eq_zero]
              intro x hx
              exact (hv.2).2 x (mem_compl.mp hx)
            rw [this]
            simp
        exact (pdist_vecMul_of_mem_rowStochastic hM this).2
      have h₂ : ∑ j, (v ᵥ* M) j = ∑ j ∈ m, (v ᵥ* M) j + ∑ j ∉ m, (v ᵥ* M) j := by
        exact Eq.symm (sum_add_sum_compl m (v ᵥ* M))
      have h₃ : ∑ j ∉ m, (v ᵥ* M) j = 0 := by
        rw [Finset.sum_eq_zero]
        intro j hj
        exact h₀ j (mem_compl.mp hj)
      linarith
    · intro j hj
      aesop


set_option maxHeartbeats 600000 in
-- Unclear why this is so inefficient as it is not too long. Leaving the increased heartbeats
-- for now, but note that this value has been 'tuned' such that it is not _too_ much more
-- than is needed.

/-- Doubly stochastic matrices have uniform stationary distributions -/
lemma DoublyStochasticUniformStationaryDist
    {V : Type*} [Fintype V] [DecidableEq V] (L : Finset V)
    (M : Matrix V V ℝ) (hM : (M ∈ doublyStochastic ℝ V) ∧ ∀ l ∉ L, M l l = 1 ) :
    UniformDist L = (UniformDist L) ᵥ*  M := by
  let u := UniformDist L
  have h₀ : ∀ j, (u ᵥ* M) j = ∑ i, u i * M i j := by exact fun j ↦ rfl
  -- First, within the support the elements have the expected (non-zero) value
  have h₁ : ∀ j ∈ L, (u ᵥ* M) j = 1 / (#L : ℝ) := by
    intro j hj
    have : (u ᵥ* M) j = ∑ i, u i * M i j := by exact h₀ j
    rw [this]
    have : ∑ i, u i * M i j = ∑ i ∈ L, u i * M i j + ∑ i ∉ L, u i * M i j := by
      exact Eq.symm (sum_add_sum_compl L fun i ↦ u i * M i j)
    rw [this]
    have :  ∑ i ∉ L, u i * M i j = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      have : u x = 0 := by
        have hx2 : x ∉ L := by exact mem_compl.mp hx
        exact UniformDist_zero_outside_support L x hx2
      rw [this]
      exact Lean.Grind.Semiring.zero_mul (M x j)
    rw [this]
    have :  ∑ i ∈ L, u i * M i j = 1 / (#L : ℝ) := by
      have : ∀ i ∈ L, u i = 1 / (#L : ℝ) := fun i a ↦ UniformDist_element_value L i a
      have : ∑ i ∈ L, u i * M i j = ∑ i ∈ L, 1 / (#L : ℝ) * M i j := by
        aesop
      rw [this]
      have : ∑ i ∈ L, 1 / (#L : ℝ) * M i j = 1 / (#L : ℝ) * ∑ i ∈ L, M i j := by
        exact Eq.symm (mul_sum L (fun i ↦ M i j) (1 / ↑(#L)))
      rw [this]
      have : ∑ i ∈ L, M i j = 1 := by
        have : ∑ i ∈ L, M i j = ∑ i, M i j - ∑ i ∉ L, M i j := by
          have : ∑ i, M i j = ∑ i ∈ L, M i j + ∑ i ∉ L, M i j := by
            exact Eq.symm (sum_add_sum_compl L fun i ↦ M i j)
          linarith
        rw [this]
        have hMa : M ∈ doublyStochastic ℝ V := by exact hM.1
        have : ∑ i, M i j = 1 := by
          exact sum_col_of_mem_doublyStochastic hMa j
        rw [this]
        have : ∑ i ∈ Lᶜ, M i j = 0 := by
          rw [Finset.sum_eq_zero]
          intro x hx
          have hMa : M ∈ doublyStochastic ℝ V := hM.1
          have h₁a : M x x = 1 := by
            have hMb : ∀ l ∉ L, M l l = 1 := hM.2
            aesop
          have h₁b : ∑ j, M x j = 1 := by
            (expose_names; exact sum_row_of_mem_doublyStochastic hMa_1 x)
          have h₁c : ∀ j, 0 ≤ M x j := fun y ↦ nonneg_of_mem_doublyStochastic hMa
          have : ∑ j, M x j = ∑ j ∈ {x}ᶜ, M x j + M x x := by
            have : ∑ j, M x j = ∑ j ∈ {x}ᶜ, M x j + ∑ j ∉ {x}ᶜ, M x j := by
              exact Eq.symm (sum_add_sum_compl {x}ᶜ fun j ↦ M x j)
            rw [this]
            aesop
          rw [this, h₁a] at h₁b
          have h₁d : ∑ i ∈ {x}ᶜ, M x i = 0 := by aesop
          have h₁e : x ≠ j := by aesop
          have h₁f : ∀ k ≠ x, M x k = 0 := by
            intro j' _
            rw [Finset.sum_eq_zero_iff_of_nonneg (fun j' _ ↦ h₁c j')] at h₁d
            aesop
          aesop
        rw [this]
        exact sub_zero 1
      rw [this]
      linarith
    rw [this]
    linarith
  -- Second, outside of the support, the elements have value zero
  have h₂ : ∀ j ∉ L, (u ᵥ* M) j = 0 := by
    intro j hj
    have : (u ᵥ* M) j = ∑ i, u i * M i j := by exact h₀ j
    rw [this]
    have : ∑ i, u i * M i j = ∑ i ∈ L, u i * M i j + ∑ i ∉ L, u i * M i j := by
      exact Eq.symm (sum_add_sum_compl L fun i ↦ u i * M i j)
    rw [this]
    have : ∑ i ∈ L, u i * M i j = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      have : M x j = 0 := by
        have h₂a : M j j = 1 := by aesop
        have hMa : M ∈ doublyStochastic ℝ V := by exact hM.1
        have h₂b : ∑ y, M y j = 1 := by
          exact sum_col_of_mem_doublyStochastic hMa j
        have h₂ : ∀ y, 0 ≤ M y j := by
          exact fun y ↦ nonneg_of_mem_doublyStochastic hMa
        have : ∑ y, M y j = ∑ y ∈ {j}ᶜ, M y j + M j j := by
          have : ∑ y, M y j = ∑ y ∈ {j}ᶜ, M y j + ∑ y ∉ {j}ᶜ, M y j := by
            exact Eq.symm (sum_add_sum_compl {j}ᶜ fun i ↦ M i j)
          rw [this]
          aesop
        rw [this, h₂a] at h₂b
        have h₂c : ∑ y ∈ {j}ᶜ, M y j = 0 := by aesop
        have h₂d : x ≠ j := by aesop
        have h₂e : ∀ k ≠ j, M k j = 0 := by
          intro j' _
          rw [Finset.sum_eq_zero_iff_of_nonneg (fun j' _ ↦ h₂ j')] at h₂c
          aesop
        aesop
      rw [this]
      exact Lean.Grind.Semiring.mul_zero (u x)
    rw [this]
    have : ∑ i ∉ L, u i * M i j = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      have : u x = 0 := by
        have hx' : x ∉ L := by exact mem_compl.mp hx
        exact UniformDist_zero_outside_support L x hx'
      rw [this]
      exact Lean.Grind.Semiring.zero_mul (M x j)
    rw [this]
    linarith
  -- Together the two parts are enough
  have h₃ : (u ᵥ* M) = UniformDist L := IsUniformDist L (u ᵥ* M) h₁ h₂
  rw [h₃]

/-- Correspondence between two definitions of `ℓ₂ norm` -/
lemma norm_eq_sqrt_L2normSQ {s : Finset n} (h : ∀ i ∉ s, v i = 0) :
    ‖(EuclideanSpace.equiv _ _).symm v‖ = √(L2normSQ v s) := by
  rw [EuclideanSpace.norm_eq]
  simp only [PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply, norm_eq_abs, sq_abs, L2normSQ]
  congr! 1
  have : ∑ x, v x ^ 2 = ∑ x ∈ s, v x ^ 2 + ∑ x ∉ s, v x ^ 2 :=
    Eq.symm (sum_add_sum_compl s fun i ↦ v i ^ 2)
  rw [this]
  have : ∑ x ∉ s, v x ^ 2 = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    aesop
  rw [this]
  linarith

lemma norm_sq_eq_L2normSQ {s : Finset n} (h : ∀ i ∉ s, v i = 0) :
    ‖(EuclideanSpace.equiv _ _).symm v‖ ^ 2 = L2normSQ v s := by
  rw [norm_eq_sqrt_L2normSQ h]
  rw [Real.sq_sqrt]
  apply L2normSQ_nonneg _ _


open scoped Matrix.Norms.L2Operator

/-- Operator norm of a product is bounded -/
lemma Matrix.l2_opNorm_vecMul' {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℝ) (x : EuclideanSpace ℝ m) :
    ‖(EuclideanSpace.equiv _ _).symm (x ᵥ* A)‖ ≤ ‖A‖ * ‖x‖ := by
  have : ‖(EuclideanSpace.equiv _ _).symm (x ᵥ* A)‖ =
      ‖(EuclideanSpace.equiv _ _).symm (A.conjTranspose *ᵥ x)‖ := by
    rw [← Matrix.mulVec_transpose]
    have : Aᵀ = Aᴴ := rfl
    rw [this]
  rw [this]
  have h₀: ‖(EuclideanSpace.equiv n ℝ).symm (Aᴴ *ᵥ x)‖ ≤ ‖Aᴴ‖ * ‖x‖ :=
    l2_opNorm_mulVec Aᴴ x
  have : ‖Aᴴ‖  =  ‖A‖ := by exact l2_opNorm_conjTranspose A
  rw [←this]
  exact h₀


/-- A useful bound on the `ℓ₂` norm when the random walk matrix operates on a probability vector -/
lemma MultiDiGraph.bound_on_L2normSQ [Fintype V]
    [DecidableEq V] [DecidableEq E] (G : MultiDiGraph V E) (hV : 0 < #G.vertices)
    {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r) (p : V → ℝ) (hp : IsProbVector p G.vertices)
    (hpu : p ≠ UniformDist G.vertices) :
    √(L2normSQ (p ᵥ* G.randomWalkMatrix - UniformDist G.vertices) G.vertices)
    / √(L2normSQ (p - UniformDist G.vertices) G.vertices) ≤ 1 := by
  -- Establish a couple of basic facts that are used below
  have hM : (G.randomWalkMatrix ∈ doublyStochastic ℝ V)
      ∧ ∀ l ∉ G.vertices, G.randomWalkMatrix l l = 1  := by
    constructor
    · exact RegularrandomWalkMatrixIsDoublyStochastic G hr hG
    · exact fun l a ↦ diagonal_outside_support_randomWalkMatrix G l a
  have : UniformDist G.vertices = UniformDist G.vertices ᵥ* G.randomWalkMatrix := by
    exact DoublyStochasticUniformStationaryDist G.vertices G.randomWalkMatrix hM
  set U := UniformDist G.vertices
  rw [div_le_one₀]
  -- The upper-bound of one can be obtained by showing that the denominator is positive (taken
  -- as the first goal by the swap, below) which is easy, and that the numerator is smaller
  -- than the denominator
  swap
  · have : ∃ i ∈ G.vertices, (p-U) i ≠ 0 := by
      have hU :  IsProbVector U G.vertices := by exact
        UniformDist_is_ProbVector_on_superset_of_support G.vertices G.vertices hV fun ⦃a⦄ a ↦ a
      exact ProbVector_neq_then_elements_differ p U hpu G.vertices hp hU
    have : 0 < L2normSQ (p - U) G.vertices := L2normSQ_positive (p - U) G.vertices this
    exact sqrt_pos_of_pos this
  -- Now to show that the numerator is smaller than the denominator
  -- This essentially comes from the fact that the operator norm of a doubly stochastic
  -- matrix is upper-bounded by 1, as in `pNorm_le_one`, but there is a bit of work to get
  -- everything in the correct shape, as below
  have : p ᵥ* G.randomWalkMatrix - U = (p - U) ᵥ* G.randomWalkMatrix := by
    rw [sub_vecMul, ← this]
  rw [this]
  rw [← norm_eq_sqrt_L2normSQ, ← norm_eq_sqrt_L2normSQ]
  swap
  · intro i hi
    have : (p - U) i = p i - U i := rfl
    rw [this]
    have : p i = 0 := by exact ProbVector_zero_outside_range p G.vertices hp i hi
    rw [this]
    have : U i = 0 := by exact UniformDist_zero_outside_support G.vertices i hi
    rw [this]
    linarith
  swap
  · intro i hi
    have : ((p - U) ᵥ* G.randomWalkMatrix) i = ∑ j, (p - U) j *  G.randomWalkMatrix j i := rfl
    rw [this]
    have : ∑ j, (p - U) j * G.randomWalkMatrix j i = ∑ j ∈ {i}, (p - U) j * G.randomWalkMatrix j i
        + ∑ j ∉ {i}, (p - U) j * G.randomWalkMatrix j i :=
          Eq.symm (sum_add_sum_compl {i} fun i_1 ↦ (p - U) i_1 * G.randomWalkMatrix i_1 i)
    rw [this]
    have : ∑ j ∈ {i}, (p - U) j * G.randomWalkMatrix j i  = 0 := by
      have : ∑ j ∈ {i}, (p - U) j * G.randomWalkMatrix j i =
      (p - U) i * G.randomWalkMatrix i i := by
        exact sum_singleton (fun x ↦ (p - U) x * G.randomWalkMatrix x i) i
      rw [this]
      have : (p - U) i = 0 := by
        have : (p - U) i = p i - U i := rfl
        rw [this]
        have : p i = 0 := ProbVector_zero_outside_range p G.vertices hp i hi
        rw [this]
        have : U i = 0 := UniformDist_zero_outside_support G.vertices i hi
        rw [this]
        linarith
      rw [this]
      linarith
    rw [this]
    have : ∑ j ∈ {i}ᶜ, (p - U) j * G.randomWalkMatrix j i = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      have : x ≠ i := by
        simp only [mem_compl, mem_singleton] at hx
        exact hx
      have : G.randomWalkMatrix x i = 0 :=
        random_walk_zero_off_diagonal_outside_vertices G i x this hi
      rw [this]
      linarith
    rw [this]
    linarith
  apply (Matrix.l2_opNorm_vecMul' _ _).trans
  have : ‖G.randomWalkMatrix‖ ≤ 1 :=
    Matrix.l2_opNorm_le_one_of_mem_doublyStochastic
        (RegularrandomWalkMatrixIsDoublyStochastic G hr hG)
  apply mul_le_of_le_one_left _ this
  apply norm_nonneg

/-- An alternative statement closely related to `MultiDiGraph.bound_on_L2normSQ` -/
lemma MultiDiGraph.bound_on_L2normSQ' [Fintype V]
    [DecidableEq V] [DecidableEq E] (G : MultiDiGraph V E) (hV : 0 < #G.vertices)
    {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r) :
    ∀ x ∈ {y | ∃ p, IsProbVector p G.vertices ∧ p ≠ UniformDist G.vertices ∧ y =
    √(L2normSQ (p ᵥ* G.randomWalkMatrix - UniformDist G.vertices) G.vertices)
    / √(L2normSQ (p - UniformDist G.vertices) G.vertices)}, x ≤ 1 := by

  have (p : V → ℝ) (hp : IsProbVector p G.vertices) (hp' : p ≠ UniformDist G.vertices) :
      √(L2normSQ (p ᵥ* G.randomWalkMatrix - UniformDist G.vertices) G.vertices)
      / √(L2normSQ (p - UniformDist G.vertices) G.vertices) ≤ 1 := by
    exact G.bound_on_L2normSQ hV hr hG p hp hp'
  aesop

/-- The spectral gap is lower bounded by zero -/
lemma MultiDiGraph.SpectralGap_geq_zero [Fintype V]
    [DecidableEq V] [DecidableEq E] (G : MultiDiGraph V E) (hV: 0 < #G.vertices)
    {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r) :
    0 ≤ G.SpectralGap := by
  unfold SpectralGap
  have : ∀ x ∈ {y | ∃ p, IsProbVector p G.vertices ∧ p ≠ UniformDist G.vertices ∧ y =
            √(L2normSQ (p ᵥ* G.randomWalkMatrix - UniformDist G.vertices) G.vertices)
            / √(L2normSQ (p - UniformDist G.vertices) G.vertices)}, x ≤ 1 := by
    exact G.bound_on_L2normSQ' hV hr hG
  have : sSup {y | ∃ p, IsProbVector p G.vertices ∧ p ≠ UniformDist G.vertices ∧ y =
            √(L2normSQ (p ᵥ* G.randomWalkMatrix - UniformDist G.vertices) G.vertices)
            / √(L2normSQ (p - UniformDist G.vertices) G.vertices)} ≤ 1 := by
    refine Real.sSup_le this ?_
    linarith
  nlinarith

/-- The spectral gap is upper bounded by one -/
lemma MultiDiGraph.SpectralGap_leq_one [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) (hG: 0 < #G.vertices):
    G.SpectralGap ≤ 1 := by
  unfold SpectralGap
  let u := UniformDist G.vertices;
  let M := G.randomWalkMatrix;
  let L := G.vertices
  have : sSup {y | ∃ p, IsProbVector p G.vertices ∧ p ≠ UniformDist G.vertices ∧ y =
      √(L2normSQ (Matrix.vecMul p G.randomWalkMatrix - u) L) / √(L2normSQ (p - u) L)} ≥ 0 := by
    have h₁ : ∀ p : V → ℝ, (IsProbVector p G.vertices) ∧ p ≠ u → 0 < L2normSQ (p - u) L := by
      intro p hp
      have : ∃ i ∈ G.vertices, (p - u) i ≠ 0 := by
        have : IsProbVector u G.vertices :=
          UniformDist_is_ProbVector G.vertices hG
        exact ProbVector_neq_then_elements_differ p u hp.2 G.vertices hp.1 this
      exact L2normSQ_positive (p - u) L this
    have h1a : ∀ p : V → ℝ, (IsProbVector p G.vertices) ∧
        p ≠ u → 0 < √ (L2normSQ (p - u) L) := by aesop
    have h₃ : ∀ p : V → ℝ, (IsProbVector p G.vertices) ∧ p ≠ u  →
        0 ≤ √ (L2normSQ (Matrix.vecMul p G.randomWalkMatrix - u) L) / √ (L2normSQ (p - u) L) := by
      intros p hp
      have denom_pos := h1a p hp
      positivity
    apply Real.sSup_nonneg
    aesop
  aesop

/-- This lemma upper-bounds the set used in `MultiDiGraph.L2norm_eigenvalue_bound'` -/
lemma helper_lemma [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r):
    ∀ z ∈ {y | ∃ x, ¬x = 0 ∧ x ⬝ᵥ UniformDist G.vertices = 0 ∧
    (∀ i ∉ G.vertices, x i = 0) ∧
    y = √(L2normSQ (x ᵥ* G.randomWalkMatrix) G.vertices) / √(L2normSQ x G.vertices)}, z ≤ 1 := by
  intro z hz
  -- Informally, this have statement is enough, and is a little easier to get into
  -- conveniently, even in the formal proof `aesop` closes the goal from this in one step
  have : ∀ x, (x ≠ 0) → (∀ i ∉ G.vertices, x i = 0) →
      (√(L2normSQ (x ᵥ* G.randomWalkMatrix) G.vertices) / √(L2normSQ x G.vertices) ≤ 1) := by
    intro x _ _
    by_cases hx : L2normSQ x G.vertices = 0
    · aesop
    -- it is straightford when the `L2normSQ x G.vertices = 0` and so focus the main proof when
    -- this does not hold
    have h₀ : 0 < L2normSQ x G.vertices := by
      have : 0 ≤  L2normSQ x G.vertices := by exact L2normSQ_nonneg x G.vertices
      exact lt_of_le_of_ne this fun a ↦ hx (id (Eq.symm a))
    have h₁ : 0 < √(L2normSQ x G.vertices) := by
      exact sqrt_pos_of_pos h₀
    have h₂ : √(L2normSQ (x ᵥ* G.randomWalkMatrix) G.vertices) ≤ √(L2normSQ x G.vertices) := by
      rw [← norm_eq_sqrt_L2normSQ, ← norm_eq_sqrt_L2normSQ]
      swap
      · intro i hi
        aesop
      swap
      · intro i hi
        have : (x ᵥ* G.randomWalkMatrix) i = ∑ j, x j *  G.randomWalkMatrix j i := rfl
        rw [this]
        have : ∑ j, x j * G.randomWalkMatrix j i = ∑ j ∈ {i}, x j * G.randomWalkMatrix j i
            + ∑ j ∉ {i}, x j * G.randomWalkMatrix j i :=
              Eq.symm (sum_add_sum_compl {i} fun i_1 ↦ x i_1 * G.randomWalkMatrix i_1 i)
        rw [this]
        have : ∑ j ∈ {i}, x j * G.randomWalkMatrix j i  = 0 := by
          have : ∑ j ∈ {i}, x j * G.randomWalkMatrix j i =
              x i * G.randomWalkMatrix i i := by
            exact sum_singleton (fun y ↦ x y * G.randomWalkMatrix y i) i
          rw [this]
          have : x i = 0 := by
            aesop
          rw [this]
          linarith
        rw [this]
        have : ∑ j ∈ {i}ᶜ, x j * G.randomWalkMatrix j i = 0 := by
          rw [Finset.sum_eq_zero]
          intro y hy
          have : y ≠ i := by
            aesop
          have : G.randomWalkMatrix y i = 0 :=
            MultiDiGraph.random_walk_zero_off_diagonal_outside_vertices G i y this hi
          rw [this]
          linarith
        rw [this]
        linarith
      apply (Matrix.l2_opNorm_vecMul' _ _).trans
      have : ‖G.randomWalkMatrix‖ ≤ 1 :=
        Matrix.l2_opNorm_le_one_of_mem_doublyStochastic
            (G.RegularrandomWalkMatrixIsDoublyStochastic hr hG)
      apply mul_le_of_le_one_left _ this
      apply norm_nonneg
    exact (div_le_one₀ h₁).mpr h₂
  aesop

/-- Every non-zero vector can be decomposed as a sum of a vector in a certain direction
plus an orthogonal component-/
lemma existPerpVector {V : Type*} [Fintype V] (x : V → ℝ) (y : V → ℝ)
    (hy : ( y ⬝ᵥ y ) ≠ 0) : ∃ xperp : V → ℝ,
    (x = ((x ⬝ᵥ y) / (y ⬝ᵥ y )) • y + xperp ) ∧ y ⬝ᵥ xperp = 0 := by
  use x - ((x ⬝ᵥ y) / (y ⬝ᵥ y )) • y
  constructor
  · aesop
  · rw [dotProduct_sub, dotProduct_smul]
    field_simp [hy]
    ring_nf
    rw [dotProduct_comm]
    grind
    -- linarith

set_option maxHeartbeats 400000 in
-- This increase in heartbeats is not too bad, and as the following proof works and is easy to follow
-- it is deemed acceptable

/-- An equivalent condition for the spectral gap -/
lemma MultiDiGraph.alternative_spectral_gap [Fintype V]
    [DecidableEq V] [DecidableEq E] (G : MultiDiGraph V E) (hV : 0 < #G.vertices)
    {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r) :
    sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G.vertices) ∧ (p ≠ UniformDist G.vertices) ∧
    (y = Real.sqrt (L2normSQ ((p ᵥ* G.randomWalkMatrix) - UniformDist (G.vertices)) G.vertices)
    / Real.sqrt (L2normSQ (p - UniformDist G.vertices) G.vertices))}
    =
    sSup { y : ℝ  | ∃ x : V → ℝ , (x ≠ 0) ∧ (x ⬝ᵥ UniformDist G.vertices = 0) ∧
    (∀ i ∉ G.vertices, x i = 0) ∧
    (y = Real.sqrt (L2normSQ (x ᵥ* G.randomWalkMatrix) G.vertices)
    / Real.sqrt (L2normSQ x G.vertices))} := by
  -- start with a couple of standard definitions
  set u := UniformDist G.vertices
  set M := G.randomWalkMatrix
  -- establish the existence of an orthogonal vector
  have h₀ : ∀ p', ((IsProbVector p' G.vertices)
      → ∃ uperp, (p' = u + uperp) ∧ u ⬝ᵥ uperp = 0) := by
    -- note that this holds for single point probability distributions that can only be
    -- the uniform distribution; in the general case, it is a standard decomposition
    intro p' hp'
    have hu : u ⬝ᵥ u ≠ 0 := by
      rw [ne_eq, dotProduct_self_eq_zero]
      exact UniformDist_nonzero G.vertices hV
    have h₀a : ∃ uperp', (p' = ((p' ⬝ᵥ u) / (u ⬝ᵥ u )) • u + uperp' ) ∧ u ⬝ᵥ uperp' = 0 := by
      exact existPerpVector p' u  hu
    obtain ⟨uperp', h₀a_eq, h₀a_orth⟩ := h₀a
    use uperp'
    constructor
    · have : (p' ⬝ᵥ u / u ⬝ᵥ u) = 1 := by
        have : u ⬝ᵥ u = (1 / #G.vertices : ℝ) := by
          unfold dotProduct
          have hup : IsProbVector (UniformDist G.vertices) G.vertices :=
            UniformDist_is_ProbVector_on_superset_of_support G.vertices G.vertices hV fun ⦃a⦄ a ↦ a
          exact ProbVector_times_UniformDist' G.vertices u hup
        rw [this]
        have : p' ⬝ᵥ u = (1 / #G.vertices : ℝ) := by
          unfold dotProduct
          exact ProbVector_times_UniformDist' G.vertices p' hp'
        rw [this]
        have : (1 / #G.vertices : ℝ) ≠ 0 := by
          (expose_names; exact Ne.symm (ne_of_ne_of_eq (id (Ne.symm hu)) this_1))
        grind
      rw [this] at h₀a_eq
      aesop
    · exact h₀a_orth
  -- need now to rewrite using `h₀`
  -- also use `DoublyStochasticUniformStationaryDist` to write `πM = uperp' M + uM = uperp' M + u`
  apply csSup_eq_csSup_of_forall_exists_le
  -- the strategy is to show that each set contains an upper-bound of the other, hence
  -- that they have the same upper-bound
  · simp only [ne_eq, Set.mem_ofPred_eq, forall_exists_index, and_imp]
    rintro x p' hp' (hpu : p' ≠ u) hx
    obtain ⟨uperp, h₁, h₂⟩ := h₀ p' hp'
    refine ⟨_, ⟨uperp, ?_, ?_, ?_, rfl⟩, ?_⟩
    · rintro rfl
      apply hpu
      simp [h₁]
    · rwa [dotProduct_comm]
    · intro i hi
      have : uperp = p' - u := by
        rw [h₁]
        abel
      rw [this]
      have : (p' - u) i = p' i - u i := rfl
      rw [this]
      have : p' i = 0 := ProbVector_zero_outside_range p' G.vertices hp' i hi
      rw [this]
      have : u i = 0 := UniformDist_zero_outside_support G.vertices i hi
      rw [this]
      linarith
    · rw [hx, h₁, add_sub_cancel_left, Matrix.add_vecMul]
      rw [← DoublyStochasticUniformStationaryDist]
      · simp [u]
      exact Regular_is_DoublyStochastic G hr hG
  -- Now the upper-bound the other way around
  · simp only [ne_eq, Set.mem_ofPred_eq, forall_exists_index, and_imp]
    intro t x hx hxu hx_supp ht
    obtain ⟨i, hi⟩ := Finset.exists_maximalFor (fun i ↦ |x i|) G.vertices (by simpa using hV)
    -- these first steps turn it into an easier to work with existence problem, the next steps set
    -- up some notation and generally useful results
    let a := |x i|
    have ha_max : ∀ j, |x j| ≤ a := by
      intro j
      by_cases j ∈ G.vertices
      · have := hi.2
        simp only [← not_lt_iff_le_imp_ge, not_lt] at this
        exact this ‹_›
      simp [*, a]
    have ha_ne_zero : a ≠ 0 := by
      intro h
      rw [h] at ha_max
      simp only [abs_nonpos_iff] at ha_max
      apply hx
      ext
      simp [ha_max]
    refine ⟨_, ⟨u + (a * #G.vertices)⁻¹ • x, ?_, ?_, rfl⟩, ?_⟩
    -- Turn the conditions into their own goals.
    -- The first of these goals is hardest: to show that the constructed vector
    -- is a probability vector. This in turn requires the definition of probability vector
    -- and informally is true because `x` sums to zero, and (by construction) is scaled such that
    -- the elements that are never so large that when added to the uniform distribution, they
    -- remain between 0 and 1, hence this gives a probability distribution
    -- Though quite long, the remainder of this goal is easy enough to follow using the infoview
    · refine ⟨?_, ?_, ?_⟩
      · have : ∑ i ∈ G.vertices, (u + (a * ↑(#G.vertices))⁻¹ • x) i =
            ∑ i ∈ G.vertices, u i  + ∑ i ∈ G.vertices, ((a * ↑(#G.vertices))⁻¹ • x) i := by
          apply Finset.sum_add_distrib
        rw [this]
        have : ∑ i ∈ G.vertices, u i = 1 := by
          have : IsProbVector (UniformDist G.vertices) G.vertices :=
            UniformDist_is_ProbVector_on_superset_of_support G.vertices G.vertices hV fun ⦃a⦄ a ↦ a
          exact this.1
        rw [this]
        have : ∑ i ∈ G.vertices, ((a * (#G.vertices : ℝ))⁻¹ • x) i =
            (a * (#G.vertices : ℝ))⁻¹ • ∑ i ∈ G.vertices, x i := by
          rw [Finset.smul_sum]
          aesop
        rw [this]
        have : (a * (#G.vertices : ℝ))⁻¹ • ∑ i ∈ G.vertices, x i =
            (a * (#G.vertices : ℝ))⁻¹ * ∑ i ∈ G.vertices, x i := rfl
        rw [this]
        have : ∑ i ∈ G.vertices, x i = 0 := by
          have hxu' : x ⬝ᵥ u = 0 := hxu
          unfold dotProduct at hxu'
          have : ∑ i, x i * u i = ∑ i ∈ G.vertices, x i * u i + ∑ i ∉ G.vertices, x i * u i :=
            Eq.symm (sum_add_sum_compl G.vertices fun i ↦ x i * u i)
          rw [this] at hxu'
          have : ∑ i ∉ G.vertices, x i * u i  = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hi' : i ∉ G.vertices := by exact mem_compl.mp hi
            have : x i = 0 := by exact hx_supp i hi'
            rw [this]
            linarith
          rw [this] at hxu'
          have : ∑ i ∈ G.vertices, x i * u i
              = ∑ i ∈ G.vertices, x i * (1 / #G.vertices : ℝ) := by
            have : ∀ i ∈ G.vertices, (UniformDist G.vertices) i = (1 / #G.vertices : ℝ) :=
              fun i a ↦ UniformDist_element_value G.vertices i a
            aesop
          rw [this] at hxu'
          have :  ∑ i ∈ G.vertices, x i * (1 / ↑(#G.vertices)) =
              (1 / ↑(#G.vertices)) * ∑ i ∈ G.vertices, x i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x1 hx1
            linarith
          rw [this] at hxu'
          aesop
        rw [this]
        have : (a * (#G.vertices : ℝ)) ≠ 0 := by aesop
        linarith
      · intro i hi
        have : (u + (a * ↑(#G.vertices))⁻¹ • x) i = u i + (a * ↑(#G.vertices))⁻¹ * x i := rfl
        rw [this]
        have : u i = (#G.vertices : ℝ)⁻¹ := by
          have : ∀ j ∈ G.vertices, u j = (1 / #G.vertices : ℝ) :=
            fun j a ↦ UniformDist_element_value G.vertices j a
          aesop
        rw [this]
        have : (a * (#G.vertices : ℝ))⁻¹ = a⁻¹ * (#G.vertices : ℝ)⁻¹ :=
          mul_inv a ↑(#G.vertices)
        rw [this]
        have hpa : |x i| ≤ a := by exact ha_max i
        have : a = |a| := by (expose_names; exact Eq.symm (abs_abs (x i_1)))
        rw [this] at hpa
        have hpc : 0 < ((#G.vertices) : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hV)
        have hpd : ((#G.vertices) : ℝ)⁻¹ = |((#G.vertices) : ℝ)⁻¹| :=
          Eq.symm (abs_of_pos hpc)
        have hpb : |a⁻¹ * ((#G.vertices) : ℝ)⁻¹ * x i| ≤ ((#G.vertices) : ℝ)⁻¹ := by
          simp only [abs_mul]
          rw [← hpd]
          rw [abs_inv]
          rw [mul_comm]
          have : |x i| * (|a|⁻¹ * (↑(#G.vertices))⁻¹) = |x i| * |a|⁻¹ * (↑(#G.vertices))⁻¹ := by
            exact Eq.symm (mul_assoc |x i| |a|⁻¹ (↑(#G.vertices))⁻¹)
          rw [this]
          have : |x i| * |a|⁻¹ ≤ 1 := by
            refine mul_inv_le_one_of_le₀ hpa ?_
            exact abs_nonneg a
          nlinarith
        have hpe : -(a⁻¹ * (↑(#G.vertices))⁻¹ * x i) ≤ (↑(#G.vertices))⁻¹ :=
          le_of_max_le_right hpb
        nlinarith
      · intro i hi
        simp only [_root_.mul_inv_rev, Pi.add_apply, Pi.smul_apply, hx_supp i hi, smul_eq_mul,
          mul_zero, add_zero]
        exact UniformDist_zero_outside_support G.vertices i hi
    -- The remaining goals are straightforward
    · simpa [card_pos, ha_ne_zero, hx, nonempty_iff_ne_empty] using hV
    · rw [Matrix.add_vecMul]
      rw [← DoublyStochasticUniformStationaryDist]
      · simp only [add_sub_cancel_left, u, a]
        rw [smul_vecMul, L2normSQ_commute_out_constant, L2normSQ_commute_out_constant,
          sqrt_mul', sqrt_mul', mul_div_mul_left, ht]
        · positivity
        · exact L2normSQ_nonneg x G.vertices
        · exact L2normSQ_nonneg _ G.vertices
      exact Regular_is_DoublyStochastic G hr hG


/-- A bound on the ℓ₂ norm over the product of a vector and a doubly stochastic random walk matrix
    in terms of the spectral gap -/
lemma MultiDiGraph.L2norm_spectral_gap_bound
    [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices) {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r)
    (p : V → ℝ) (hpb : UniformDist G.vertices ⬝ᵥ p = 0)
    (hpa : ∀ i ∉ G.vertices, p i = 0):
    √(L2normSQ (p ᵥ* G.randomWalkMatrix) G.vertices) ≤
    (1 - G.SpectralGap) * √(L2normSQ p G.vertices) := by
  by_cases hpp : p = 0
  · have h₀ : L2normSQ (p ᵥ* G.randomWalkMatrix) G.vertices = 0 := by
      have : p ᵥ* G.randomWalkMatrix = 0 := by aesop
      rw [this]
      exact L2normSQ_zero_eq_zero 0 G.vertices rfl
    have h₁ : 0 ≤ (1 - G.SpectralGap) := by
      have : G.SpectralGap ≤ 1 := by exact SpectralGap_leq_one G hV
      linarith
    have h₂ : 0 ≤ √(L2normSQ p G.vertices) := by exact sqrt_nonneg (L2normSQ p G.vertices)
    rw [h₀]
    have : √ 0 = 0 := by exact sqrt_zero
    rw [this]
    nlinarith
  rw [SpectralGap]
  rw [alternative_spectral_gap G hV hr hG]
  · simp only [ne_eq, sub_sub_cancel]
    rw [← div_le_iff₀]
    · apply le_csSup
      · use 1
        exact helper_lemma G hr hG
      · have : p ⬝ᵥ UniformDist G.vertices = UniformDist G.vertices ⬝ᵥ p  :=
          dotProduct_comm p (UniformDist G.vertices)
        rw [← this] at hpb
        aesop
    · have : 0 < L2normSQ p G.vertices := L2normSQ_nonzero_geq_zero p G.vertices hpp hpa
      exact sqrt_pos_of_pos this

--#lint



-- # Neighbourhood as a multiset

open Multiset List

/-- Contains the incident vertices as a multiset, so duplications are included
with the corresponding multiplicity -/
def MultiDiGraph.neighbourhood_as_multiset [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : Multiset V :=
  (G.incidentOutEdges v).val.map fun e ↦ (G.edgeMap e).snd

  /-- Neighbourhood of a set of vertices taken as a multiset -/
def MultiDiGraph.neighbourhoodOfSet_as_multiset [DecidableEq V]
    (G : MultiDiGraph V E) (vs : Finset V) : Multiset V := vs.val.bind G.neighbourhood_as_multiset

/-- The multiset neighbourhood of a `r`-regular graph has size `r` -/
lemma neighbourhood_as_multiset_of_r_regular_has_card_r [DecidableEq V]
    (G : MultiDiGraph V E) (r : ℕ) (hr : G.isRegularOfDegree r) :
    ∀ v ∈ G.vertices, (G.neighbourhood_as_multiset v).card = r := by
  unfold MultiDiGraph.neighbourhood_as_multiset
  intro v hv
  simp only [Multiset.card_map, card_val]
  unfold MultiDiGraph.incidentOutEdges
  unfold MultiDiGraph.isRegularOfDegree at hr
  exact (hr v hv).left

/-- The multiset neighbourhood of a set of `r`-regular graph has size `r` times
the cardinality of the set  -/
lemma neighbourhood_of_set_card_s_as_multiset_of_r_regular_has_card_sr [DecidableEq V]
    (G : MultiDiGraph V E) (r : ℕ) (hr : G.isRegularOfDegree r) :
    ∀ s ⊆ G.vertices, (G.neighbourhoodOfSet_as_multiset s).card = (s.card) * r := by
  unfold MultiDiGraph.neighbourhoodOfSet_as_multiset
  intro s hs
  have h₀ : ∀ v ∈ s, (G.neighbourhood_as_multiset v).card = r := by
    exact fun v a ↦ neighbourhood_as_multiset_of_r_regular_has_card_r G r hr v (hs a)
  aesop

/-- The multiset neighbourhood of a set where each vertex has out-degree `r` has size
`r` times the cardinality of the set-/
lemma neighbourhood_of_set_card_s_as_multiset_of_r_regular_has_card_sr_a [DecidableEq V]
    (G : MultiDiGraph V E) (r : ℕ)  :
    ∀ S ⊆ G.vertices, (∀ v ∈ S, G.OutDegree v = r) →
    (G.neighbourhoodOfSet_as_multiset S).card = (S.card) * r := by
  unfold MultiDiGraph.neighbourhoodOfSet_as_multiset
  intro S hS hr
  have h₀ : ∀ v ∈ S, (G.neighbourhood_as_multiset v).card = r := by
    unfold MultiDiGraph.neighbourhood_as_multiset
    unfold MultiDiGraph.OutDegree at hr
    intro v' hv'
    simp_all only [Multiset.card_map, card_val]
  simp
  aesop

/-- If a multiset is turned into a finset, which is then treated as a multiset,
the result is a subset of the original set -/
lemma helper_lemma_1 {α : Type*} [DecidableEq α] (s : Multiset α) :
    s.toFinset.val ≤ s := by
  rw [Multiset.toFinset_val]
  exact Multiset.dedup_le s

/-- An element of a multiset is an element of the Finset of that multiset;
and in particular still when that Finset is treated as a multiset -/
lemma helper_lemma_2 {α : Type*} [DecidableEq α] (s : Multiset α)
    (v : α) (hv : v ∈ s):
    v ∈ s.toFinset.val := by
  aesop

lemma helper_lemma_3 {α : Type*} [DecidableEq α] (s t : Multiset α) (h₀ : s ≤ t):
    t - (t - s) = s := by
  have h₁ : s + (t - s) = t := by exact add_tsub_cancel_of_le h₀
  exact Eq.symm (Multiset.eq_sub_of_add_eq h₁)

lemma helper_lemma_4 {α : Type*} [DecidableEq α] (s t u : Multiset α)
    (h₀ : s ≤ t) :
    u - t ≤ u - s := by
  exact tsub_le_tsub_left h₀ u

/-- A multiset formed by taking some elements therein is a sub multiset -/
lemma multiset_construction_lemma {α : Type*} (s : Multiset α)
    (n' : ℕ) :
    s.toList.take n' ≤ s := by
  have : s.toList.take n' <+: s.toList := List.take_prefix _ _
  have : List.Subperm (s.toList.take n') s.toList := this.sublist.subperm
  rw [← Multiset.coe_le] at this
  apply this.trans_eq (by simp)

/-- One can always construct a sub multiset of a multiset -/
lemma helper_lemma_5 {α : Type*} (s : Multiset α)
    (n n' : ℕ) (hs : s.card = n) (hn : n' ≤ n) :
    ∃ t ≤ s, t.card = n' := by
  let slist := s.toList
  let tlist := slist.take n'
  use tlist
  constructor
  · exact multiset_construction_lemma s n'
  · simp [tlist, slist]
    omega


/-- A sub multiset of the neighbourhood set can be constructed such that it has size
  which is the difference between the neighbourhood multiset minus the neighbourhood (i.e., as a
  Finset) and contains just elements that are duplicated in the set formed by subtracting the new
  multiset from the neighbourhood multiset -/
lemma neighbour_of_set_as_multiset_duplicates [DecidableEq V]
    (G : MultiDiGraph V E) {s : Finset V}
    {a : ℕ} (ha : #(G.neighbourhoodOfSet s) = a)
    {b : ℕ} (hb : (G.neighbourhoodOfSet_as_multiset s).card = b) :

    ∃ t : Multiset V, t ≤ (G.neighbourhoodOfSet_as_multiset s)
        ∧ t.card = b - a
        ∧  ∀ v ∈ t, v ∈ (G.neighbourhoodOfSet_as_multiset s) - t := by

  have h₀ : (G.neighbourhoodOfSet_as_multiset s).toFinset = G.neighbourhoodOfSet s := by
    unfold MultiDiGraph.neighbourhoodOfSet MultiDiGraph.neighbourhood
    unfold MultiDiGraph.neighbourhoodOfSet_as_multiset MultiDiGraph.neighbourhood_as_multiset
    aesop
  have h₁ : ((G.neighbourhoodOfSet_as_multiset s).toFinset).val
      ≤ G.neighbourhoodOfSet_as_multiset s := by
    exact helper_lemma_1 (G.neighbourhoodOfSet_as_multiset s)
  use (G.neighbourhoodOfSet_as_multiset s) - ((G.neighbourhoodOfSet_as_multiset s).toFinset).val
  constructor
  · apply Multiset.sub_le_self
  · constructor
    · have h₂a : (G.neighbourhoodOfSet_as_multiset s).card = b := by exact hb
      have h₂b : ((G.neighbourhoodOfSet_as_multiset s).toFinset).val.card = a := by aesop
      rw [Multiset.card_sub h₁, h₂a, h₂b]
    · intro v hv
      have h₃ : v ∈ G.neighbourhoodOfSet_as_multiset s := by
        have : G.neighbourhoodOfSet_as_multiset s
            - (G.neighbourhoodOfSet_as_multiset s).toFinset.val
            ≤ G.neighbourhoodOfSet_as_multiset s :=
            Multiset.sub_le_self (G.neighbourhoodOfSet_as_multiset s)
              (G.neighbourhoodOfSet_as_multiset s).toFinset.val
        exact mem_of_le this hv
      have h₄ : v ∈ ((G.neighbourhoodOfSet_as_multiset s).toFinset).val :=
        helper_lemma_2 (G.neighbourhoodOfSet_as_multiset s) v h₃
      have h₅ : G.neighbourhoodOfSet_as_multiset s -
          (G.neighbourhoodOfSet_as_multiset s - (G.neighbourhoodOfSet_as_multiset s).toFinset.val) =
          (G.neighbourhoodOfSet_as_multiset s).toFinset.val :=
        helper_lemma_3 (G.neighbourhoodOfSet_as_multiset s).toFinset.val
            (G.neighbourhoodOfSet_as_multiset s) h₁
      rw [h₅]
      exact h₄




/-- A sub multiset of the neighbourhood set can be constructed such that it has size
  larger than the difference between the neighbourhood multiset minus the neighbourhood (i.e., as a
  Finset) and contains just elements that are duplicated in the set formed by subtracting the new
  multiset from the neighbourhood multiset -/
lemma neighbour_of_set_as_multiset_duplicates' [DecidableEq V]
    (G : MultiDiGraph V E)
    {s : Finset V}
    {a : ℕ} (ha : #(G.neighbourhoodOfSet s) < a)
    {b : ℕ} (hb : (G.neighbourhoodOfSet_as_multiset s).card = b)
    (hab : a < b):

    ∃ t : Multiset V, t ≤ (G.neighbourhoodOfSet_as_multiset s)
        ∧ t.card = b - a
        ∧  ∀ v ∈ t, v ∈ (G.neighbourhoodOfSet_as_multiset s) - t := by

  set a' := #(G.neighbourhoodOfSet s)
  have ha' : #(G.neighbourhoodOfSet s)  = a' := rfl
  have h₁ : ∃ t : Multiset V, t ≤ (G.neighbourhoodOfSet_as_multiset s)
        ∧ t.card = b - a'
        ∧  ∀ v ∈ t, v ∈ (G.neighbourhoodOfSet_as_multiset s) - t := by
    exact neighbour_of_set_as_multiset_duplicates G ha' hb
  obtain ⟨t', ht'⟩ := h₁
  have hab' : 0 < b - a := by aesop
  have h₂ : b - a < b - a' := by
    have : (b - a : ℤ) < (b - a' : ℤ) := by nlinarith
    grind
  have h₃ : ∃ t'' ≤ t', t''.card = b - a :=
    helper_lemma_5 t' (b - a') (b - a) (ht'.2).1 h₂.le
  obtain ⟨t'', ht''⟩ := h₃
  use t''
  constructor
  · exact Std.le_trans ht''.1 ht'.1
  · constructor
    · exact ht''.2
    · intro v hv
      have h₃ : G.neighbourhoodOfSet_as_multiset s - t' ≤
          G.neighbourhoodOfSet_as_multiset s - t'' :=
        tsub_le_tsub_left ht''.1 (G.neighbourhoodOfSet_as_multiset s)
      have h₄ : v ∈ t' := mem_of_le ht''.1 hv
      have h₅ : v ∈ G.neighbourhoodOfSet_as_multiset s - t' :=
        (ht'.2).2 v h₄
      exact mem_of_le h₃ h₅

--#lint
