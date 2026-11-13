/-
Copyright (c) 2025 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
import Mathlib

import ExpanderGraph.CollisionProb
import ExpanderGraph.MultiDiGraph
import ExpanderGraph.ProbabilityVector
import ExpanderGraph.ExpansionDefs
--import LeanCopilot

/-!
# Squaring graphs

This file shows that an spectral expander squared is another spectral expander

## Main results

* `G_squared_expander`

-/

open MultiDiGraphSpace
open ProbabilityVector
open Finset
open ExpansionDefs
open Matrix
open Classical


/-- A n-vertex r-regular graph that is a γ-spectral expander -/
def isnrγ_graph {V E : Type*} [Fintype V] [DecidableEq V] (G : MultiDiGraph V E)
    (n r : ℕ) (γ : ℝ) : Prop :=
  (#G.vertices = n) ∧ (G.isRegularOfDegree r) ∧ spectralExpander γ G

/-- Squaring a graph -/
def graph_squared {V E : Type*} [DecidableEq V] (G : MultiDiGraph V E) :
     MultiDiGraph V (E × E) :=
  let newEdges := (G.edges.product G.edges).filter (fun (e₁, e₂) =>
    (G.edgeMap e₁).2 = (G.edgeMap e₂).1)
  let newEdgeMap : (E × E) → V × V := fun (e₁, e₂) =>
    ((G.edgeMap e₁).1, (G.edgeMap e₂).2)
  let newEdgesValid : ∀ e ∈ newEdges, newEdgeMap e ∈ G.vertices ×ˢ G.vertices := by
    intro en hen
    simp only [mem_product]
    constructor
    · unfold newEdgeMap
      simp only
      have : en.1 ∈ G.edges := by aesop
      exact fst_mem_vertices this
    · unfold newEdgeMap
      simp only
      have : en.2 ∈ G.edges := by aesop
      exact snd_mem_vertices this
  MultiDiGraph.mk G.vertices newEdges newEdgeMap newEdgesValid


/--Graph squaring gives the same vertex set -/
lemma squaring_preserves_vertices {V E : Type*} [DecidableEq V]
    (G : MultiDiGraph V E) : #(graph_squared G).vertices = #G.vertices := by
  aesop

-- ++++++++++++++++++++++++++++ [ADDED-BY_SUPERVISOR_fixed_by_SJH_Nov_2026] +++++

lemma graph_squared_edges {V E : Type*} [DecidableEq V] (G : MultiDiGraph V E) :
    (graph_squared G).edges = {e ∈ G.edges ×ˢ G.edges | (G.edgeMap e.1).2 = (G.edgeMap e.2).1} :=
  rfl

lemma graph_squared_edgeMap {V E : Type*} [DecidableEq V] (G : MultiDiGraph V E) (e : E × E) :
    (graph_squared G).edgeMap e = ((G.edgeMap e.1).1, (G.edgeMap e.2).2) :=
  rfl

-- For the next two lemmas, I wrote the statement and began to construct the proof, but the
-- bulk of the work was done by the supervisor.


/-- Graph squaring of a regular graph gives a regular graph with the degree squared -/
lemma squaring_regular_squares_edges {V E : Type*} [DecidableEq V] (G : MultiDiGraph V E)
    (r : ℕ) (hG : G.isRegularOfDegree r) :
    (graph_squared G).isRegularOfDegree (r ^ 2) := by
  sorry

  -- # Below is a proof that worked in September 2025, but needs fixing

  -- dsimp [MultiDiGraph.isRegularOfDegree, graph_squared_edges, graph_squared_edgeMap] at hG ⊢
  -- intro v hv
  -- have hG1 : ∀ v ∈ G.vertices, #({e ∈ G.edges | (G.edgeMap e).1 = v}) = r := by aesop
  -- have hG2 : ∀ v ∈ G.vertices, #({e ∈ G.edges | (G.edgeMap e).2 = v}) = r := by aesop
  -- constructor
  -- · simp_rw +singlePass [filter_filter, card_filter, sum_product, ite_and, ← sum_filter]
  --   dsimp only
  --   simp_rw [sum_ite_irrel, sum_const_zero, ← card_eq_sum_ones, ← sum_filter]
  --   calc
  --       ∑ x ∈ G.edges with (G.edgeMap x).1 = v,
  --         (#({a ∈ G.edges | (G.edgeMap x).2 = (G.edgeMap a).1}))
  --       = ∑ x ∈ G.edges with (G.edgeMap x).1 = v, r := by
  --         congr! with x hx
  --         simp only [mem_filter] at hx
  --         simp_rw [eq_comm (a := Prod.snd _)]
  --         rw [hG1]
  --         exact snd_mem_vertices hx.1
  --     _ = r ^ 2 := by simp [hG1 _ hv, pow_two]
  -- · simp_rw +singlePass [filter_filter, card_filter, sum_product, sum_comm, ite_and, ← sum_filter]
  --   dsimp only
  --   simp_rw [sum_ite_irrel, sum_const_zero, ← card_eq_sum_ones, ← sum_filter]
  --   calc
  --       ∑ x ∈ G.edges with (G.edgeMap x).2 = v,
  --         (#({a ∈ G.edges | (G.edgeMap a).2 = (G.edgeMap x).1}))
  --       = ∑ x ∈ G.edges with (G.edgeMap x).2 = v, r := by
  --         congr! with x hx
  --         simp only [mem_filter] at hx
  --         rw [hG2]
  --         exact fst_mem_vertices hx.1
  --     _ = r ^ 2 := by simp [hG2 _ hv, pow_two]





/-- When a graph is squared then its random walk matrix is squared -/
lemma randomWalkMatrix_of_graph_squared {V E : Type*} [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) {r : ℕ} (hr : G.isRegularOfDegree r) (hr' : r ≠ 0) :
    (graph_squared G).randomWalkMatrix = G.randomWalkMatrix ^ 2 := by
  sorry

  -- # Below is a proof that worked in September 2025, but needs fixing

  -- ext i j
  -- simp only [pow_two, Matrix.mul_apply, MultiDiGraph.randomWalkMatrix_apply_eq]
  -- by_cases i ∈ G.vertices
  -- case neg hi =>
  --   have : i ∉ (graph_squared G).vertices := hi
  --   simp only [this, not_false_eq_true, MultiDiGraph.OutDegree_eq_zero_v_notin_vertices, ↓reduceIte,
  --         hi, boole_mul, sum_ite_eq, mem_univ]
  -- case pos hi =>
  --   have hd'' := squaring_regular_squares_edges G r hr
  --   have hi' : i ∈ (graph_squared G).vertices := hi
  --   simp only [hi', hd''.outDegree_eq, Nat.pow_eq_zero, hr', ne_eq, OfNat.ofNat_ne_zero,
  --     not_false_eq_true, and_true, ↓reduceIte, Nat.cast_pow, hi, hr.outDegree_eq, mul_ite,
  --     mul_one, mul_zero]
  --   have (x : V) : G.OutDegree x ≠ 0 ↔ x ∈ G.vertices := by
  --     constructor
  --     · intro h
  --       simp only [MultiDiGraph.OutDegree, MultiDiGraph.incidentOutEdges, ne_eq, card_eq_zero,
  --         filter_eq_empty_iff, not_forall, exists_prop, Decidable.not_not] at h
  --       obtain ⟨e, he, rfl⟩ := h
  --       apply fst_mem_vertices he
  --     · intro h
  --       rwa [hr.outDegree_eq _ _ _ h]
  --   simp_rw +singlePass [sum_ite, ← ne_eq, sum_ite_eq', mem_filter, mem_univ, true_and]
  --   split
  --   case isTrue h =>
  --     have (x : V) : G.adjacencyMatrix x j = 0 := by
  --       rw [MultiDiGraph.adjacencyMatrix_zero_if_not_vertices]
  --       rwa [← this, not_not]
  --     conv_lhs =>
  --       simp only [MultiDiGraph.adjacencyMatrix, graph_squared_edgeMap, graph_squared_edges,
  --         filter_filter, of_apply]
  --     simp only [this, CharP.cast_eq_zero, zero_div, ne_eq, mul_zero, sum_const_zero, add_zero,
  --       div_eq_zero_iff, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff, mem_product, not_and,
  --       and_imp, Prod.forall, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, hr',
  --       or_false]
  --     have := @snd_mem_vertices (G := G)
  --     grind
  --   case isFalse h =>
  --     conv_lhs =>
  --       simp only [MultiDiGraph.adjacencyMatrix, graph_squared_edgeMap, graph_squared_edges,
  --         filter_filter, of_apply]
  --     simp +contextual only [zero_add, this, filter_univ_mem,
  --       hr.outDegree_eq, div_mul_div_comm, ← sum_div, ← pow_two]
  --     congr! 1
  --     norm_cast
  --     simp only [MultiDiGraph.adjacencyMatrix, of_apply, card_eq_sum_ones, sum_filter, sum_product,
  --       sum_comm (s := G.vertices), sum_mul, mul_sum]
  --     rw [sum_comm]
  --     congr! 2 with e₁ he₁ e₂ he₂
  --     simp only [mul_boole, ← ite_and]
  --     suffices ∀ x, ((G.edgeMap e₁).1 = x ∧ (G.edgeMap e₁).2 = j) ∧
  --                    (G.edgeMap e₂).1 = i ∧ (G.edgeMap e₂).2 = x ↔
  --         (G.edgeMap e₁).1 = x ∧ (G.edgeMap e₂).2 = (G.edgeMap e₁).1 ∧
  --         (G.edgeMap e₂).1 = i ∧ (G.edgeMap e₁).2 = j by
  --       simp only [this, ite_and, sum_ite_eq, fst_mem_vertices he₁, if_true]
  --     intro x
  --     grind

-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++


/-- Graph squaring preserving regularity-/
lemma squaring_preserves_regular {V E : Type*} [DecidableEq V] (G : MultiDiGraph V E) :
    G.regular → (graph_squared G).regular := by
  intro hG
  have h₀ : ∃ r : ℕ, G.isRegularOfDegree r := by exact hG
  obtain ⟨r, hr⟩ := h₀
  have h₁ : (graph_squared G).isRegularOfDegree (r ^ 2) := squaring_regular_squares_edges G r hr
  refine ((graph_squared G).regular_lemma).mpr ?_
  exact Exists.intro (r ^ 2) h₁

/-- For a graph with at least two vertices, construct a vector orthogonal to the uniform
    distribution and such that it sums to zero -/
def vector_orthogonal_construction {α : Type*} [DecidableEq α] (v₁ v₂ : α) : α → ℝ :=
  fun i => if i = v₁ then 1 else if i = v₂ then -1 else 0

/-- For all graphs with at least two vertices, there exists a vector orthogonal to the
    uniform distribution that is non-zero and sums to zero -/
lemma vec_orthogonal_to_uniform_dist {V E : Type*} [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) (hn : 2 ≤ #G.vertices) :
    ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ UniformDist G.vertices = 0 ∧ (∀ i ∉ G.vertices, x i = 0) := by
  -- First step is to obtain two vertices `v₁` and `v₂`
  have h₀ : ∃ v₁ ∈ G.vertices, ∃ v₂ ∈ G.vertices, v₁ ≠ v₂ := by
    have : G.vertices.Nonempty := by
      have : 0 < #G.vertices := by linarith
      exact card_pos.mp this
    obtain ⟨v₁, hv₁⟩ := this
    have : (G.vertices \ {v₁} : Finset V).Nonempty := by
      have : 0 < #(G.vertices \ ({v₁} : Finset V)) := by
        have : 1 ≤ #(G.vertices \ ({v₁} : Finset V)) := by
          have hg : #(G.vertices) - #({v₁} : Finset V) ≤ #(G.vertices \ ({v₁} : Finset V))  := by
            exact le_card_sdiff {v₁} G.vertices
          have hgg : 1 ≤ #(G.vertices) - #({v₁} : Finset V) := by
            have hgg₁ : 2 ≤ #(G.vertices) := hn
            have hgg₂ : #({v₁} : Finset V) = 1 := by exact rfl
            rw [hgg₂]
            grind
          nlinarith
        nlinarith
      exact card_pos.mp this
    rcases this with ⟨v₂, hv₂⟩
    use v₁
    constructor
    · exact hv₁
    · use v₂
      constructor
      · grind
      · grind
  obtain ⟨v₁ , hv₁ , v₂ , hv₂ , hv ⟩ := h₀

  -- Now build the vector which is `1` at `v₁`, `-1` at `v₂` and zero elsewhere
  use (vector_orthogonal_construction v₁ v₂)
  -- The remainder is showing that the constructed vector has the claimed properties
  constructor
  · unfold vector_orthogonal_construction
    intro contra
    have := congrFun contra v₁
    simp at this
  · constructor
    · unfold dotProduct
      have : ∑ i, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i =
          ∑ i ∈ {v₁}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i +
          ∑ i ∉ {v₁}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i := by
        exact
          Eq.symm
            (sum_add_sum_compl {v₁} fun i ↦
              vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i)
      rw [this]
      have : ∑ i ∈ {v₁}ᶜ, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i
          = ∑ i ∈ {v₁}ᶜ \ {v₂}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i
            + ∑ i ∈ {v₂}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i := by
        aesop
      rw [this]
      have : ∑ i ∈ {v₁}ᶜ \ {v₂}, vector_orthogonal_construction v₁ v₂ i
          * UniformDist G.vertices i = 0 := by
        apply Finset.sum_eq_zero
        intro v' hv'
        have h₀ : v' ≠ v₁ ∧ v' ≠ v₂ := by
          constructor
          · have : v' ∈ ({v₁}ᶜ : Finset V) := by
              grind
            rw [Finset.mem_compl] at this
            rwa [Finset.mem_singleton] at this
          · grind
        have : vector_orthogonal_construction v₁ v₂ v' = 0 := by
          unfold vector_orthogonal_construction
          grind
        rw [this]
        linarith
      rw [this]
      have : ∑ i ∈ {v₂}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i
          = (-1 / #G.vertices : ℝ) := by
        have : ∑ i ∈ {v₂}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i =
            vector_orthogonal_construction v₁ v₂ v₂ * UniformDist G.vertices v₂ := by
          exact
            sum_singleton
              (fun x ↦ vector_orthogonal_construction v₁ v₂ x * UniformDist G.vertices x) v₂
        rw [this]
        unfold vector_orthogonal_construction UniformDist
        grind
      rw [this]
      have : ∑ i ∈ {v₁}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i
          = (1 / #G.vertices : ℝ) := by
        have : ∑ i ∈ {v₁}, vector_orthogonal_construction v₁ v₂ i * UniformDist G.vertices i =
            vector_orthogonal_construction v₁ v₂ v₁ * UniformDist G.vertices v₁ := by
          exact
            sum_singleton
              (fun x ↦ vector_orthogonal_construction v₁ v₂ x * UniformDist G.vertices x) v₁
        rw [this]
        unfold vector_orthogonal_construction UniformDist
        grind
      rw [this]
      grind
    · unfold vector_orthogonal_construction
      aesop

/-- One minus the spectral gap of a graph squared is at most the square of one minus
the spectral gap of the original graph -/
lemma spectral_gap_of_graph_squared {V E1 E2: Type*} [Fintype V]
    [DecidableEq V] [DecidableEq E1] [DecidableEq E2] (G1 : MultiDiGraph V E1)
    (G2 : MultiDiGraph V E2) (h : G1.vertices = G2.vertices)
    (hG : G2.randomWalkMatrix = G1.randomWalkMatrix ^2)
    (hV1: 0 < #G1.vertices) {d1 : ℕ} (hd1 : d1 ≠ 0) (hG1 : G1.isRegularOfDegree d1)
    (hV2: 0 < #G2.vertices) {d2 : ℕ} (hd2 : d2 ≠ 0) (hG2 : G2.isRegularOfDegree d2)
    (hn : 2 ≤ #G1.vertices):
    1 - G2.SpectralGap ≤  (1 - G1.SpectralGap)^2 := by
  -- The opening steps are just trivial re-writes, and the use of the alternative definition
  -- of the spectral gap
  calc 1 - G2.SpectralGap
    _ = 1 - (1 - sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G2.vertices)
        ∧ (p ≠ UniformDist G2.vertices) ∧
        (y = √ (L2normSQ ((p ᵥ* G2.randomWalkMatrix)
        - UniformDist (G2.vertices)) G2.vertices)
        / √ (L2normSQ (p - UniformDist (G2.vertices)) G2.vertices))}) := by
      unfold MultiDiGraph.SpectralGap
      rfl
    _ = sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G2.vertices) ∧ (p ≠ UniformDist G2.vertices) ∧
          (y = √ (L2normSQ ((p ᵥ* G2.randomWalkMatrix)
          - UniformDist (G2.vertices)) G2.vertices)
          / √ (L2normSQ (p - UniformDist (G2.vertices)) G2.vertices))} := by linarith
    _ = sSup { y : ℝ  | ∃ x : V → ℝ , (x ≠ 0) ∧ (x ⬝ᵥ UniformDist G2.vertices = 0) ∧
          (∀ i ∉ G2.vertices, x i = 0) ∧
          (y = √ (L2normSQ (x ᵥ* G2.randomWalkMatrix) G2.vertices)
          / √ (L2normSQ x G2.vertices))} := G2.alternative_spectral_gap hV2 hd2 hG2
    _ = sSup { y : ℝ  | ∃ x : V → ℝ , (x ≠ 0) ∧ (x ⬝ᵥ UniformDist G2.vertices = 0) ∧
          (∀ i ∉ G2.vertices, x i = 0) ∧
          (y = √ (L2normSQ (x ᵥ* G1.randomWalkMatrix ^ 2) G2.vertices)
          / √ (L2normSQ x G2.vertices))} := by rw [hG]
    _ = sSup { y : ℝ  | ∃ x : V → ℝ , (x ≠ 0) ∧ (x ⬝ᵥ UniformDist G2.vertices = 0) ∧
          (∀ i ∉ G2.vertices, x i = 0) ∧
          (y = √ (L2normSQ (x ᵥ* (G1.randomWalkMatrix * G1.randomWalkMatrix)) G2.vertices)
          / √ (L2normSQ x G2.vertices))} := by
      have : G1.randomWalkMatrix ^ 2 = G1.randomWalkMatrix * G1.randomWalkMatrix :=
        pow_two G1.randomWalkMatrix
      rw [this]
    _ = sSup { y : ℝ  | ∃ x : V → ℝ , (x ≠ 0) ∧ (x ⬝ᵥ UniformDist G2.vertices = 0) ∧
          (∀ i ∉ G2.vertices, x i = 0) ∧
          (y = √ (L2normSQ (x ᵥ* G1.randomWalkMatrix ᵥ* G1.randomWalkMatrix) G2.vertices)
          / √ (L2normSQ x G2.vertices))} := by aesop
    _ ≤ _ := by
    -- The final part is essentially getting it in the right form to use
    -- `MultiDiGraph.L2norm_spectral_gap_bound` twice, as per the informal proof
    -- There are quite a few technicalities needed for this, but easy to follow using the infoview
      apply csSup_le
      · have : ∃ x, x ≠ 0 ∧ x ⬝ᵥ UniformDist G2.vertices = 0 ∧
            (∀ i ∉ G2.vertices, x i = 0) := by
          rw [h] at hn
          exact vec_orthogonal_to_uniform_dist G2 hn
        rcases this with ⟨x, hx₁, hx₂, hx₃⟩
        use √ (L2normSQ (x ᵥ* G1.randomWalkMatrix ᵥ* G1.randomWalkMatrix) G2.vertices) /
            √ (L2normSQ x G2.vertices)
        use x
      simp only [ne_eq, Set.mem_ofPred_eq, forall_exists_index, and_imp]
      rintro _ p hp hp' hp'' rfl
      have h₁ : ∀ i ∉ G1.vertices, (p ᵥ* G1.randomWalkMatrix) i = 0 := by
        rw [←h] at hp''
        exact fun i a ↦ if_not_vertex_prod_of_p_randomwalk_matrix_eq_zero G1 p hp'' i a
      have h₂ : G1.randomWalkMatrix *ᵥ UniformDist G1.vertices =
          UniformDist G1.vertices := by
        have : G1.randomWalkMatrix *ᵥ UniformDist G1.vertices
            = UniformDist G1.vertices ᵥ* G1.randomWalkMatrix.transpose := by
          exact Eq.symm (vecMul_transpose G1.randomWalkMatrix (UniformDist G1.vertices))
        rw [this]
        have h₂a : G1.randomWalkMatrix ∈ doublyStochastic ℝ V :=
          MultiDiGraph.RegularrandomWalkMatrixIsDoublyStochastic G1 hd1 hG1
        have h₂b : G1.randomWalkMatrix.transpose ∈ doublyStochastic ℝ V :=
          StochasticMatrixSpace.mem_doublyStochastic_iff_transpose.mp h₂a
        have : (G1.randomWalkMatrix.transpose ∈ doublyStochastic ℝ V)
            ∧ ∀ l ∉ G1.vertices, G1.randomWalkMatrix.transpose l l = 1 := by
          constructor
          · exact h₂b
          · have : ∀ l ∉ G1.vertices, G1.randomWalkMatrix l l = 1 := by
              exact fun l a ↦ MultiDiGraph.diagonal_outside_support_randomWalkMatrix G1 l a
            exact fun l a ↦ this l a
        exact (DoublyStochasticUniformStationaryDist
            G1.vertices G1.randomWalkMatrix.transpose this).symm
      have h₃ : UniformDist G1.vertices ⬝ᵥ p ᵥ* G1.randomWalkMatrix = 0 := by
        rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, h₂, h, hp']
      have h₄ := MultiDiGraph.L2norm_spectral_gap_bound G1 hV1 hd1 hG1 p
        (by rwa [dotProduct_comm, h]) (by rwa [h])
      have h₅ := MultiDiGraph.L2norm_spectral_gap_bound G1 hV1 hd1 hG1
        (p ᵥ* G1.randomWalkMatrix) h₃ h₁
      simp only [h] at h₄ h₅ ⊢
      rw [div_le_iff₀]
      swap
      · rw [Real.sqrt_pos]
        exact L2normSQ_nonzero_geq_zero _ _ hp hp''
      grw [h₅, h₄]
      · grind
      simp only [sub_nonneg]
      apply MultiDiGraph.SpectralGap_leq_one _ hV1


-- This lemma specialises the preceeding one to the case in hand,
-- which is given a little more generally
lemma graph_squared_spectral_gap {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E)
    (hV: 0 < #G.vertices) {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r)
    (hn : 2 ≤ #G.vertices):
    1 - (1 - G.SpectralGap)^2 ≤ (graph_squared G).SpectralGap := by
  have hV2 : 0 < #(graph_squared G).vertices := by
    have : #(graph_squared G).vertices = #G.vertices := rfl
    rw [this]
    exact hV
  have hG2 : (graph_squared G).isRegularOfDegree (r ^ 2) := by
    exact squaring_regular_squares_edges G r hG
  have hr2 : (r ^ 2) ≠ 0 := by aesop
  have : 1 - (graph_squared G).SpectralGap ≤ (1 - G.SpectralGap)^2 :=
    spectral_gap_of_graph_squared G (graph_squared G) rfl
      (randomWalkMatrix_of_graph_squared G hG hr) hV hr hG hV2 hr2 hG2 hn
  linarith


/-- The square of a n,r,γ graph is a n, r², (1- (1-γ)²) graph -/
lemma G_squared_expander {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E) (n : ℕ) (hn : 0 < n) (γ : ℝ) (hγ : γ ≤ 1)
    (hV: 0 < #G.vertices) {r : ℕ} (hr : r ≠ 0) (hG : G.isRegularOfDegree r)
    (hna : 2 ≤ #G.vertices):
    -- note that there may appear to be some redundancy here,
    -- in that the definition of `isnrγ_graph` already says that the graph is regular
    -- however, it is important for the proofs that the degree is non-zero
    isnrγ_graph G n r γ → isnrγ_graph (graph_squared G) n (r^2) (1 - (1 - γ)^2) := by
  intro hi
  unfold isnrγ_graph
  constructor
  · rw [← hi.1]
    exact squaring_preserves_vertices G
  · constructor
    · exact squaring_regular_squares_edges G r (hi.2).1
    · unfold spectralExpander
      have h₁ : 1 - (1 - G.SpectralGap)^2 ≤ (graph_squared G).SpectralGap := by
        exact graph_squared_spectral_gap G hV hr hG hna
      have h₂ : 1 - (1 - γ) ^ 2 ≤ 1 - (1 - G.SpectralGap)^2 := by
        have h₂a : γ ≤ G.SpectralGap := by
          have : spectralExpander γ G := by exact (hi.2).2
          aesop
        have h₂b : (1 - γ) ^ 2 ≥  (1 - G.SpectralGap) ^ 2 := by
          have h₂ba : 1 - γ ≥ 1 - G.SpectralGap := by
            exact tsub_le_tsub_left h₂a 1
          have h₂bb : 0 ≤ 1 - γ := by
            aesop
          have h₂bc : 0 ≤ 1 - G.SpectralGap  := by
            have : #G.vertices = n := by exact hi.1
            rw [←this] at hn
            have : G.SpectralGap ≤ 1 := G.SpectralGap_leq_one hn
            aesop
          exact (sq_le_sq₀ h₂bc h₂bb).mpr h₂ba
        nlinarith
      exact Preorder.le_trans (1 - (1 - γ) ^ 2) (1 - (1 - G.SpectralGap) ^ 2)
          (graph_squared G).SpectralGap h₂ h₁


--#lint
