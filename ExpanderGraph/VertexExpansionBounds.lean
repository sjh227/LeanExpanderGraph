/-
Copyright (c) 2025-2026 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
import Mathlib

import ExpanderGraph.CollisionProb
import ExpanderGraph.MultiDiGraph
import ExpanderGraph.ProbabilityVector
import ExpanderGraph.ExpansionDefs

/-!
# VertexExpansionBounds

This file formalises an obvious upper-bound on graph expansion; and the less
obvious result that expanders of all sizes exist


## Main results

* `VertexExpansionUpperBound`
* `vertex_expanders_exist`

-/

open MultiDiGraphSpace
open ProbabilityVector
open Finset
open ExpansionDefs
open BigOperators
open Real


-- This is just a nice simple result to show that expansion is trivially upper-bounded
lemma VertexExpansionUpperBound {V E : Type*} [DecidableEq V] (G : MultiDiGraph V E)
    (r : ℕ) (hr : G.isRegularOfDegree r)
    (K : ℝ) (hK : 1 ≤ K ∧ K ≤ (#G.vertices : ℝ)) (A : ℝ):
    ((r : ℝ) < A) → ¬ vertexExpander K A G := by
  have hG₁ : 0 < (#G.vertices : ℝ) := by nlinarith
  have hG₂ : G.vertices.Nonempty := by simp_all only [Nat.cast_pos, card_pos]
  intro _
  unfold vertexExpander
  push Not
  have : ∀ s ⊆ G.vertices, (#s : ℝ) = 1 →
      (#(G.neighbourhoodOfSet s) : ℝ) < A * (#s : ℝ) ∧ (#s : ℝ) ≤ K := by
    intro s hs hss
    constructor
    · rw [hss]
      have : (#(G.neighbourhoodOfSet s) : ℝ) ≤ r :=
        G.neighbourhood_of_singleton_size_leq_degree s hss hs hr
      nlinarith
    · nlinarith
  obtain ⟨v, hv⟩ := hG₂
  have hs : {v} ⊆ G.vertices := by simp [hv]
  have h_card : (#{v} : ℝ) = 1 := by simp
  specialize this {v} hs h_card
  exact ⟨{v}, hs, this⟩


-- # Now the main bit on bipartite vertex expanders


--------------- [ADDED-BY-SUPERVISOR] ------------------------
section

open Nat

theorem factorial_bound_exp {n : ℕ} : (n / Real.exp 1) ^ n ≤ n ! := by
  rw [div_pow, ← rpow_natCast (exp 1), exp_one_rpow, div_le_iff₀ (by positivity),
    ← div_le_iff₀' (by positivity)]
  exact pow_div_factorial_le_exp _ (Nat.cast_nonneg _) _

theorem choose_upper_bound {n t : ℕ} : n.choose t ≤ (exp 1 * n / t) ^ t := by
  obtain h | h := Nat.eq_zero_or_pos t
  · simp [h]
  · grw [choose_le_pow_div, ← factorial_bound_exp, ← div_pow, div_div_eq_mul_div, mul_comm]

lemma combinatorial_fact (N : ℕ) (K : ℕ) :
    Nat.choose N K ≤ (N * Real.exp 1 / K )^K := by
  grw [choose_upper_bound, mul_comm]


end
-------------------------------------------------------------

-- This is version of the above established fact that is needed below
lemma combinatorial_fact' (N : ℕ) (K : ℕ) :
    (Nat.choose N K : ℝ) ≤ (N * Real.exp 1 / K )^K := by
  exact combinatorial_fact N K

-- easy result needed below
lemma lt_add_self (n : ℕ) (h : 0 < n) : n < n + n := by
  linarith

/-- Prop for when a graph is bipartite with specified left part -/
def isBipartite_vleft {V E : Type*} (G : MultiDiGraph V E) (vleft : Finset V) : Prop :=
  vleft ⊆ G.vertices -- basic requirement
  ∧ (∀ u ∈ vleft, ∀ v ∈ vleft,
  ¬ (∃ e ∈ G.edges, (G.edgeMap e).fst = u ∧ (G.edgeMap e).snd = v ))
  -- no edges between vertices in the left part
  ∧ (∀ u ∉ vleft, ∀ v ∉ vleft,
  ¬ (∃ e ∈ G.edges, (G.edgeMap e).fst = u ∧ (G.edgeMap e).snd = v ))
  -- no edges between vertices in the right part

/-- Prop for when a graph is in `Bip n r` with left part specified
for convenience -/
def isBipartite_n_r_vleft {V E : Type*}  [DecidableEq V] (G : MultiDiGraph V E)
    (n : ℕ) (r : ℕ) (vleft : Finset V) : Prop :=
  #vleft = n -- size of the left part
  ∧ #G.vertices = 2 * n -- equal sized parts
  ∧ isBipartite_vleft G vleft
  ∧ ∀ u ∈ vleft, G.OutDegree u = r -- left out regular

/-- Prop for when a graph is a bipartite vertex expander-/
def isBipartiteVertexExpander {V E : Type*} [DecidableEq V]
    (G : MultiDiGraph V E) (K : ℝ) (A : ℝ)
    (vleft : Finset V)
    : Prop :=
  ∃ n : ℕ, ∃ r : ℕ, (isBipartite_n_r_vleft G n r vleft) ∧
      ∀ s ⊆ vleft, (A * #s ≤ #(MultiDiGraph.neighbourhoodOfSet G s)) ∨ K < #s

/-- Map from an array of random numbers to the corresponding left out-regular
bipartite graph -/
def Ω (n r : ℕ) (M : Fin r → Fin n → Fin n) :
    MultiDiGraph (Fin (n + n)) (Fin r × Fin n) :=
  let edges : Finset (Fin r × Fin n) := Finset.univ
  let edgeMap : (Fin r × Fin n) → (Fin (n + n) × Fin (n + n)) :=
    fun (i, j) ↦ (Fin.castAdd n j, Fin.natAdd n (M i j))
  {
    vertices := Finset.univ,
    edges := edges,
    edgeMap := edgeMap,
    edgesValid := by
      intros e he
      simp only [mem_product]
      aesop
  }

/-- Ω makes left (out) regular graphs -/
lemma Ω_left_regular (n r : ℕ) (M : Fin r → Fin n → Fin n) :
    ∀ v : Fin (n + n), (v < n) →
      (Ω n r M).OutDegree v = r := by
  intro v hv
  simp only [MultiDiGraph.OutDegree, MultiDiGraph.incidentOutEdges, Ω]
  change Finset.card
    {e ∈ (Finset.univ : Finset (Fin r × Fin n)) |
      Fin.castAdd n e.2 = v} = r
  let w : Fin n := ⟨v.val, hv⟩
  have hw : Fin.castAdd n w = v := by
    apply Fin.ext
    rfl
  have h :
      {e ∈ (Finset.univ : Finset (Fin r × Fin n)) |
        Fin.castAdd n e.2 = v} =
      Finset.univ ×ˢ ({w} : Finset (Fin n)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · intro hj
      apply Fin.ext
      exact Fin.mk.inj_iff.mp hj
    · intro hj
      rw [hj, hw]
  rw [h]
  simp

/-- All functions from Fin n to Fin m -/
def allFns (n m : ℕ) : Finset (Fin n → Fin m) :=
  univ.image (fun f : Fin n → Fin m => f)

/-- All functions from Fin r to Fin n to Fin n -/
def allM (n r : ℕ) : Finset (Fin r → Fin n → Fin n) :=
  Finset.univ.image id

open Classical

/-- All graphs for all possible M, as defined in `def allM` -/
noncomputable def allGraphs (n r : ℕ) :
  Finset (MultiDiGraph (Fin (n + n)) (Fin r × Fin n)) :=
  (allM n r).image (Ω n r)

lemma vertices_of_mem_allGraphs {n r : ℕ} (G)
    (hG : G ∈ allGraphs n r) :
    G.vertices = Finset.univ := by
  grind [allGraphs, allM, Ω]

/-- All graphs constructed as in `allGraphs` are in Bip n r -/
theorem allGraphs_subset_bipartite (n r : ℕ) (hn : 0 < n)
    (G : MultiDiGraph (Fin (n + n)) (Fin r × Fin n)) (hG : G ∈ allGraphs n r) :
    isBipartite_n_r_vleft G n r {i | i < n} := by
  simp only [isBipartite_n_r_vleft, mem_filter, mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert Fin.card_Iio (⟨n, by omega⟩ : Fin (n + n))
    ext i
    simp [Fin.lt_def]
  · rw [vertices_of_mem_allGraphs _ hG]
    simp only [card_univ, Fintype.card_fin]
    grind
  · rw [isBipartite_vleft]
    refine ⟨?_, ?_, ?_⟩
    · rw [vertices_of_mem_allGraphs _ hG]
      simp
    · simp only [allGraphs, allM, image_id, mem_image, mem_univ, Ω, Fin.natAdd_eq_addNat,
        true_and] at hG
      obtain ⟨M, rfl⟩ := hG
      simp only [mem_filter, mem_univ, true_and, Prod.exists, not_exists, not_and]
      rintro u hu v hv i hi rfl
      simp only [Fin.ext_iff, Fin.val_addNat]
      grind
    · simp only [allGraphs, allM, image_id, mem_image, mem_univ, Ω, Fin.natAdd_eq_addNat,
      true_and] at hG
      obtain ⟨M, rfl⟩ := hG
      simp only [mem_filter, mem_univ, true_and, not_lt, Fin.ext_iff, Fin.val_castAdd,
        Fin.val_addNat, Prod.exists, not_exists, not_and]
      grind
  · intro v hv
    have := Ω_left_regular
    simp only [allGraphs, allM, image_id, mem_image, mem_univ, true_and] at hG
    grind

/-- If `n` is non-zero then the `allGraphs` is nonempty -/
lemma G_nonempty (n r : ℕ) (hn : 0 < n) : (allGraphs n r).Nonempty := by
  unfold allGraphs Ω
  simp only [image_nonempty]
  unfold allM
  simp_all only [image_id]
  rw [univ_nonempty_iff]
  have : Nonempty (Fin n) := by rwa [← Fin.pos_iff_nonempty]
  infer_instance

/-- The set of all graphs that satisfy the expansion condition -/
noncomputable def allGraphsH  (n r : ℕ) :
  Finset (MultiDiGraph (Fin (n + n)) (Fin r × Fin n)) :=
  {G ∈ allGraphs n r | isBipartiteVertexExpander G (n / ((Real.exp 1)^3 * r^4))
  (r-2) {i : Fin (n + n) | i < n} }

lemma H_subset_G  (n r : ℕ) : allGraphsH n r ⊆ allGraphs n r := by
  unfold allGraphsH
  apply Finset.filter_subset

/-- The graphs in `allGraphs` but not `allGraphsH` as a set of graphs conditioned on
    their definitive properties -/
lemma allGraphs_set_subtract (n r : ℕ) (hn : 0 < n) (hr : 2 ≤ r) :
    (allGraphs n r \ allGraphsH n r) = {G ∈ allGraphs n r |
          ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
          (#S ≤  (n : ℝ) / (rexp 1 ^ 3 * (r : ℝ) ^ 4))
          ∧ (#(G.neighbourhoodOfSet S) < #S*(r-2)) } := by
  -- This is essentially a case of massaging the definition into the correct form
  ext G
  set K := (n : ℝ) / (rexp 1 ^ 3 * (r : ℝ) ^ 4)
  -- The major step is to expression `allGraphsH` in a useful form
  have : allGraphsH n r =
      {G ∈ allGraphs n r | ∀ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
      ((r-2) * #S ≤ #(MultiDiGraph.neighbourhoodOfSet G S)) ∨ K < #S} := by
    unfold allGraphsH
    have h₀ : ∀ G ∈ allGraphs n r,
        isBipartiteVertexExpander G ((n : ℝ) / (rexp 1 ^ 3 * (r : ℝ) ^ 4))
        ((r : ℝ) - 2) {i | ↑i < n}
        ↔ ∀ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
        (r - 2) * #S ≤ #(G.neighbourhoodOfSet S) ∨ K < (#S : ℝ) := by
      intro G hG
      simp_all only [exp_one_pow, Nat.cast_ofNat, K]
      apply Iff.intro
      · intro a S _
        unfold isBipartiteVertexExpander at a
        have a' : ∀ S : Finset (Fin (n + n)),
            S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n) →
            ((r : ℝ) - 2) * (#S : ℝ) ≤ (#(G.neighbourhoodOfSet S) : ℝ)
            ∨ (n : ℝ) / (rexp 3 * (r : ℝ) ^ 4) < (#S : ℝ) := by
          aesop
        norm_cast at a ⊢
        grind
      · intro a
        unfold isBipartiteVertexExpander
        use n
        use r
        apply And.intro
        · refine allGraphs_subset_bipartite  n r hn _ hG
        · intro s a_1
          norm_cast at a ⊢
          grind
    -- Use the expression of `allGraphsH` established in `h₀`
    apply Finset.ext
    intro G
    simp only [exp_one_pow, Nat.cast_ofNat, mem_filter, and_congr_right_iff]
    intro hG
    have : rexp 1 ^ 3 = rexp 3 := by aesop
    rw [← this]
    exact h₀ G hG
  rw [this]
  have h₀ : ∀ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),  (¬(K < (#S : ℝ))
      = ((#S : ℝ) ≤ K)) := by
      grind
  have h₁ : ∀ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
      ¬((r - 2) * #S ≤ #(G.neighbourhoodOfSet S)) = (#(G.neighbourhoodOfSet S) < (r - 2) * #S) := by
    grind
  grind

-- This is the important counting argument
-- WiP -- as explained and justified in the dissertation
lemma counting_argument_lemma (n r k : ℕ) (hn : 0 < n) (hk : k ≤ n) (hr : 2 ≤ r) :
    ∑ G ∈ allGraphs n r,
    ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
    (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
    ∧ (G.neighbourhoodOfSet S).card < k * (r - 2)}
    (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) / (n.choose k : ℝ) ≤
    (#(allGraphs n r) : ℝ) * (Nat.choose (k * r) (2 * k) : ℝ) * (k * r / n) ^ (2 * k) := by
  sorry
  -- Note that for legacy reasons this claim appears with both sides divided through by the
  -- non-zero factor `(n.choose k : ℝ)`. This is an artefact of a previous informal proof
  -- strategy, and in the re-factoring may or may not be adjusted; but importantly the claim
  -- remains mathematically the same as in the detailed informal proof.
  -- Note also that whilst this proof is omitted, much of the scaffolding required to manipulate
  -- the neighbourhood multiset has been formalised, and is found at the bottom of `MultiDiGraph`



lemma calc_block_1
    (n r : ℕ)
    (K : ℝ)
    --(hKdef : K = (n :  ℝ) / (Real.exp 1 ^ 3 * ↑r ^ 4))
    (hK₀ : 0 ≤ K)
    --(hK : K < (n : ℝ))
    (K' : ℕ)
    (hKdef' : K' = ⌊K⌋₊) :
    --(hka : ∀ k ∈ Finset.Ioc 0 K', k ≤ n)
    --(hr' : 1 ≤ r)
    --(hG : (0 : ℝ) ≠ ↑(#(allGraphs n r)))
    --(hG' : (0 : ℝ) < ↑(#(allGraphs n r)))
    --(h₀ : allGraphsH n r ⊆ allGraphs n r) :

     (#({G ∈ allGraphs n r |
        ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
        (#S ≤ K) ∧ #(G.neighbourhoodOfSet S)
        < #S * (r - 2)}) : ℝ) ≤
        ∑ k ∈ Finset.Ioc 0 K',
          ∑ G ∈ allGraphs n r,
          ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
          (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n) ∧
          (G.neighbourhoodOfSet S).card < k * (r - 2)}
          (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) := by

  calc (#({G ∈ allGraphs n r |
          ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
          (#S ≤ K) ∧ #(G.neighbourhoodOfSet S)
          < #S * (r - 2)}) : ℝ)
    _ = (#( (Finset.Ioc 0 K').biUnion
            (fun k => {G ∈ allGraphs n r |
            ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
            (#S = k) ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2)})) : ℝ) := by
          have : {G ∈ allGraphs n r |
              ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
              (#S : ℝ)
              ≤ K ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2)} =
              ((Finset.Ioc 0 K').biUnion fun k ↦ {G ∈ allGraphs n r |
              ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
              #S = k ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2)}) := by
            ext G
            simp only [mem_filter, mem_biUnion, mem_Ioc]
            have : (G ∈ allGraphs n r ∧
                ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
                (#S : ℝ) ≤ K ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2))
                = (G ∈ allGraphs n r ∧
                ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
                #S ≤ K' ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2)) := by
              have : (∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
                  (#S : ℝ) ≤ K ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2))
                  ↔ (∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
                  #S ≤ ⌊K⌋₊ ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2)) := by
                refine exists_congr ?_
                intro a
                rwa [Nat.le_floor_iff]
                -- assumption
              rw [this, hKdef']
            rw [this]
            grind
          rw [this]
        _ ≤ ∑ k ∈ Finset.Ioc 0 K', (#({G ∈ allGraphs n r |
            ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
            (#S = k) ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2)}) : ℝ) := by
          -- union bound
          norm_cast
          apply Finset.card_biUnion_le

        _ = ∑ k ∈ Finset.Ioc 0 K', (#({G ∈ allGraphs n r |
            ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
            (#S = k) ∧ #(G.neighbourhoodOfSet S) < k * (r - 2)}) : ℝ) := by
          -- use the fact that `#S = k` already filtered for
          apply Finset.sum_congr rfl
          intro k hk
          congr
          refine Set.ofPred_inj.mp ?_
          grind
        _ = ∑ k ∈ Finset.Ioc 0 K',
            (#((Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))).biUnion (fun S =>
            {G ∈ allGraphs n r |
            S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
            ∧ (G.neighbourhoodOfSet S).card < k * (r - 2)})) : ℝ) := by
          -- decompose as a sum over the subsets of the correct size
          apply Finset.sum_congr rfl
          intro k hk
          congr
          ext G
          simp only [mem_filter, mem_biUnion, mem_powersetCard, subset_univ, true_and]
          grind

        _ ≤ ∑ k ∈ Finset.Ioc 0 K',
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            (#{G ∈ allGraphs n r |
            S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
            ∧ (G.neighbourhoodOfSet S).card < k * (r - 2)} : ℝ) := by
          -- union bound,
          gcongr with k hk
          norm_cast
          apply Finset.card_biUnion_le
        _ = ∑ k ∈ Finset.Ioc 0 K',
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            ∑ G ∈ allGraphs n r,
            (Set.indicator {G |
            S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n) ∧
            (G.neighbourhoodOfSet S).card < k * (r - 2)}
            (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) := by
          -- use indicator function
          simp [Set.indicator]
        _ = ∑ k ∈ Finset.Ioc 0 K',
            ∑ G ∈ allGraphs n r,
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            (Set.indicator {G |
            S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n) ∧
            (G.neighbourhoodOfSet S).card < k * (r - 2)}
            (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_comm


set_option maxHeartbeats 400000 in
-- This increase in hearbeats is pretty much necessary: the claim is already a mathematically
-- simple statement, and it would just confuse things to break it in half; a few extra heartbeats
-- is the lesser evil here

lemma calc_block_2a (n r : ℕ) (hn : 1 ≤ n)  --(K : ℝ)
    --(hKdef : K = ↑n / (Real.exp 1 ^ 3 * ↑r ^ 4)) (hK₀ : 0 ≤ K)
    --(hK : K < ↑n) (K' : ℕ) (hKdef' : K' = ⌊K⌋₊)
    --(hka : ∀ k ∈ Ioc 0 K', k ≤ n)
    --(hG : (0 : ℝ) ≠ (#(allGraphs n r) : ℝ)) (hG' : (0 : ℝ) < (#(allGraphs n r) : ℝ))
    --(h₀ : allGraphsH n r ⊆ allGraphs n r)
    --(h_choose : ∀ k ∈ Ioc 0 K', n.choose k ≠ 0)
    (k : ℕ) : --(hk : k ∈ Ioc 0 K') :

    (↑n * Real.exp 1 / ↑k) ^ k *
    ((↑k * (↑r * Real.exp 1) / (2 * ↑k)) ^ (2 * k) * (↑k * ↑r / ↑n) ^ (2 * k)) =
      (Real.exp 1 ^ 3 * (↑k * ↑r ^ 4) / (4 * ↑n)) ^ k := by

  -- This is an ''obvious'' statement mathematically that just takes several steps
  -- to formally work out. It is easy to follow in the infoview.
  have : (k : ℝ) * ((r : ℝ) * Real.exp 1)
       = (k : ℝ) * (r : ℝ) * Real.exp 1 := by
    exact Eq.symm (mul_assoc (↑k) (↑r) (Real.exp 1))
  rw [this]
  have : ((k : ℝ) * (r : ℝ) * Real.exp 1 / (2 * (k : ℝ))) ^ (2 * k)
      = ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 * Real.exp 1 ^ 2 / ((2 * (k : ℝ)) ^ 2 )) ^ k := by
    rw [pow_mul]
    congr
    field_simp
    -- ring_nf
    -- have : Real.exp 1 ^ 2 = Real.exp 2 := by norm_num
    -- rw [this]
    -- linarith
  rw [this]
  have : ((k : ℝ) * (r : ℝ) / (n : ℝ)) ^ (2 * k)
      = ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 / (n : ℝ) ^ 2) ^ k := by
    rw [pow_mul]
    congr
    field_simp
    -- ring_nf
  rw [this]
  have : ((n : ℝ) * Real.exp 1 / (k : ℝ)) ^ k
      * (((k : ℝ) ^ 2 * (r : ℝ) ^ 2 * Real.exp 1 ^ 2 / (2 * (k : ℝ)) ^ 2) ^ k
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 / (n : ℝ) ^ 2) ^ k)
      = ((n : ℝ) * Real.exp 1 / (k : ℝ)) ^ k
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 * Real.exp 1 ^ 2 / (2 * (k : ℝ)) ^ 2) ^ k
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 / (n : ℝ) ^ 2) ^ k := by
    exact
      Eq.symm
        (mul_assoc ((↑n * Real.exp 1 / ↑k) ^ k)
          ((↑k ^ 2 * ↑r ^ 2 * Real.exp 1 ^ 2 / (2 * ↑k) ^ 2) ^ k) ((↑k ^ 2 * ↑r ^ 2 / ↑n ^ 2) ^ k))
  rw [this]
  have : ((n : ℝ) * Real.exp 1 / (k : ℝ)) ^ k
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 * Real.exp 1 ^ 2 / (2 * (k : ℝ)) ^ 2) ^ k
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 / (n : ℝ) ^ 2) ^ k
      = (((n : ℝ) * Real.exp 1 / (k : ℝ))
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 * Real.exp 1 ^ 2 / (2 * (k : ℝ)) ^ 2)
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 / (n : ℝ) ^ 2)) ^ k := by
    rw [← mul_pow, ← mul_pow]
  rw [this]
  have : ((n : ℝ) * Real.exp 1 / (k : ℝ))
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 * Real.exp 1 ^ 2 / (2 * (k : ℝ)) ^ 2)
      * ((k : ℝ) ^ 2 * (r : ℝ) ^ 2 / (n : ℝ) ^ 2)
      = Real.exp 1 ^ 3 * ((k : ℝ) * (r : ℝ) ^ 4) / (4 * (n : ℝ)) := by
    field_simp
    ring_nf
    -- have : (n : ℝ) ^ 2 * rexp 1 * (k : ℝ) ^ 4 * (r : ℝ) ^ 4 * rexp 2
    --     * (n : ℝ)⁻¹ ^ 2 * (k : ℝ)⁻¹ ^ 3
    --     = (n : ℝ) ^ 2 * (n : ℝ)⁻¹ ^ 2 * (k : ℝ) ^ 4 * (k : ℝ)⁻¹ ^ 3
    --     * (r : ℝ) ^ 4 * rexp 1 * rexp 2 := by
    --   linarith
    -- rw [this]
    -- have : (n : ℝ) ^ 2 * (n : ℝ)⁻¹ ^ 2 = (1 : ℝ) := by
    --   have : n ≠ 0 := by aesop
    --   aesop
    -- rw [this]
    -- have : 1 * (k : ℝ) ^ 4 * (k : ℝ)⁻¹ ^ 3
    --     * (r : ℝ) ^ 4 * rexp 1 * rexp 2
    --     =  (k : ℝ) ^ 4 * (k : ℝ)⁻¹ ^ 3
    --     * (r : ℝ) ^ 4 * rexp 1 * rexp 2 := by linarith
    -- rw [this]
    -- have : (k : ℝ) ^ 4 * (k : ℝ)⁻¹ ^ 3 = (k : ℝ) := by
    --   have : k ≠ 0 := by
    --     have : 0 < k := by aesop
    --     exact Nat.ne_zero_of_lt this
    --   field_simp [this]
    --   linarith
    -- rw [this]
    -- have : (k : ℝ) * (r : ℝ) ^ 4 * rexp 1 * rexp 2 =
    --     (k : ℝ) * (r : ℝ) ^ 4 * (rexp 1 * rexp 2) := by linarith
    -- rw [this]
    -- have : rexp 1 * rexp 2 = rexp 3 := by
    --   rw [← Real.exp_add]
    --   norm_num
    -- rw [this]
  rw [this]


set_option maxHeartbeats 400000 in
-- This is already only part of a large calc block that has been extracted.
-- A small increase in hearbeats is acceptable to avoid further unhelpful fragmentation

lemma calc_block_2
    (n r : ℕ)
    (hn : 1 ≤ n)
    (hr : 2 ≤ r)
    (K : ℝ)
    (hKdef : K = (n :  ℝ) / (Real.exp 1 ^ 3 * ↑r ^ 4))
    (hK₀ : 0 ≤ K)
    (hK : K < (n : ℝ))
    (K' : ℕ)
    (hKdef' : K' = ⌊K⌋₊)
    (hka : ∀ k ∈ Finset.Ioc 0 K', k ≤ n)
    (hr' : 1 ≤ r)
    (hG : (0 : ℝ) ≠ ↑(#(allGraphs n r))) :
    --(hG' : (0 : ℝ) < ↑(#(allGraphs n r)))
    -- (h₀ : allGraphsH n r ⊆ allGraphs n r) :

    ∑ k ∈ Finset.Ioc 0 K',
            ∑ G ∈ allGraphs n r,
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n) ∧
            (G.neighbourhoodOfSet S).card < k * (r - 2)}
            (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) ≤
            (#(allGraphs n r) : ℝ) *  ∑ k ∈ Finset.Ioc 0 K',
            ( 1 / 4 : ℝ) ^ k := by

  have hKn : K' ≤ n := by
    have : (K' : ℝ) ≤ (n : ℝ) := by
      have : (K' : ℝ) ≤ K := by
        rw [hKdef']
        exact Nat.floor_le hK₀
      nlinarith
    aesop
  have h_choose : ∀ k ∈ Finset.Ioc 0 K', Nat.choose n k ≠ 0 := by
    intro k hk
    have hk₀ : 0 ≤ k := by exact Nat.zero_le k
    have hk₁ : k ≤ n := by exact hka k hk
    apply ne_of_gt
    exact Nat.choose_pos (hka k hk)
  calc  ∑ k ∈ Finset.Ioc 0 K',
            ∑ G ∈ allGraphs n r,
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
            ∧ (G.neighbourhoodOfSet S).card < k * (r - 2)}
            (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ)
        _ = ∑ k ∈ Finset.Ioc 0 K',
            (n.choose k : ℝ) *
            ∑ G ∈ allGraphs n r,
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
            ∧ (G.neighbourhoodOfSet S).card < k * (r - 2)}
            (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) / (n.choose k : ℝ) := by
          -- commute non-zero terms
          apply Finset.sum_congr rfl
          intro k hk
          simp_rw [mul_sum]
          apply Finset.sum_congr rfl
          intro G hG
          apply Finset.sum_congr rfl
          intro S hS
          rw [mul_div_cancel₀]
          apply Nat.cast_ne_zero.2
          exact h_choose k hk
        _ ≤ ∑ k ∈ Finset.Ioc 0 K',
            (n.choose k : ℝ) *
            (#(allGraphs n r) : ℝ) *
            (Nat.choose (k * r) (2 * k) : ℝ) * ( k * r / n ) ^ (2 * k) := by
          apply Finset.sum_le_sum
          intro i hi
          have hik : i ≤ n := by
            have hka₂ : K' < n := by
              have : (K' : ℝ) < (n : ℝ) := by
                have : (K' : ℝ) ≤ K := by
                  refine (Nat.le_floor_iff hK₀).mp ?_
                  exact Nat.le_of_eq hKdef'
                exact lt_of_le_of_lt this hK
              exact Nat.cast_lt.mp this
            have hka₃ : i ≤ K' := by
              aesop
            -- because K upper bounds k
            exact Nat.le_trans hka₃ hka₂.le
          have h₁ : ∑ G ∈ allGraphs n r,
              ∑ S ∈ (Finset.powersetCard i (Finset.univ : Finset (Fin (n + n)))),
              (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
              ∧ (G.neighbourhoodOfSet S).card < i * (r - 2)}
              (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) / (n.choose i : ℝ)  ≤
              (#(allGraphs n r) : ℝ) *
              (Nat.choose (i * r) (2 * i) : ℝ) * (i * r / n) ^ (2 * i) := by
            -- this is the important result that has been extraced as its own lemma, and is
            -- explained in great detail in the dissertation
            exact counting_argument_lemma n r i hn hik hr
          have h₁' :=
              mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg (n.choose i))
          linarith
        _ = ∑ k ∈ Finset.Ioc 0 K',
            (#(allGraphs n r) : ℝ) * (n.choose k : ℝ) *
            (Nat.choose (k * r) (2 * k) : ℝ) * (k * r / n) ^ (2 * k) := by
          -- easy re-order
          apply Finset.sum_congr rfl
          intro k hk
          rw [@Nat.cast_comm]
        _ ≤ ∑ k ∈ Finset.Ioc 0 K',
            (#(allGraphs n r) : ℝ) * (( n * Real.exp 1 / k) ^ k) *
            (Nat.choose (k * r) (2 * k) : ℝ) * (k * r / n) ^ (2 * k) := by
          have : ∀ k ∈ Finset.Ioc 0 K', (n.choose k : ℝ) ≤ (n * Real.exp 1 / k) ^ k := by
            intro k hk
            have hka' : k ≤ n := hka k hk
            have hka'' : 1 ≤ k := by
              rw [Finset.mem_Ioc] at hk
              omega
            exact combinatorial_fact' n k
          apply Finset.sum_le_sum
          intro k hk
          have hk₁ := this k hk
          apply mul_le_mul
          · gcongr
          · aesop
          · have : 0 < (k : ℝ) := by
              have : 0 ≤ k := Nat.zero_le k
              have : 0 ≠ k := by aesop
              positivity
            positivity
          · positivity
        _ ≤ ∑ k ∈ Finset.Ioc 0 K',
            (#(allGraphs n r) : ℝ) * ((n * Real.exp 1 / k) ^ k) *
            (( k * r * Real.exp 1 / (2 * k)) ^ (2 * k))  * (k * r / n) ^ (2 * k) := by
          have : ∀ k ∈ Finset.Ioc 0 K', (Nat.choose (k * r) (2 * k) : ℝ)
               ≤ ( ↑(k * r) * Real.exp 1 / ↑(2 * k)) ^ (2 * k) := by
            intro k hk
            have hka' : (2 * k) ≤ (k * r) := by nlinarith
            have hka'' : 1 ≤ (2 * k) := by
              rw [Finset.mem_Ioc] at hk
              omega
            exact combinatorial_fact' (k * r) (2 * k)
          apply Finset.sum_le_sum
          intro k hk
          have hk₁ := this k hk
          apply mul_le_mul
          · gcongr
            aesop
          · aesop
          · have : 0 < (k : ℝ) := by
              have : 0 ≤ k := Nat.zero_le k
              have : 0 ≠ k := by aesop
              positivity
            positivity
          · positivity
         _ ≤ ∑ k ∈ Finset.Ioc 0 K',
            (#(allGraphs n r) : ℝ) * (((Real.exp 1) ^ 3) * k * (r ^ 4) / (4 * n)) ^ k := by
          -- linear algebra
          apply Finset.sum_le_sum
          intro k hk
          simp only [mul_assoc]
          gcongr _ * ?_
          apply le_of_eq
          exact calc_block_2a n r hn k
              --n r hn K hKdef hK₀ hK K' hKdef' hka hG hG' h₀ h_choose k hk
        _ ≤ (#(allGraphs n r) : ℝ) *  ∑ k ∈ Finset.Ioc 0 K',
            (((Real.exp 1 ) ^ 3) * k * (r ^ 4) / (4 * n)) ^ k := by
          rw [mul_sum]
          -- commute term that is constant over the sum
        _ ≤ (#(allGraphs n r) : ℝ) *  ∑ k ∈ Finset.Ioc 0 K',
            (Real.exp 1 ^ 3 * K * (r : ℝ) ^ 4 / (4 * (n : ℝ))) ^ k := by
          -- monotonicity
          gcongr with k hk
          have h₁ : k ≤ K' := by aesop
          have h₁' : (k : ℝ) ≤ (K' : ℝ) := by exact Nat.cast_le.mpr h₁
          have h₂ : (K' : ℝ) ≤ K := by
            rw [hKdef']
            exact Nat.floor_le hK₀
          exact Std.le_trans h₁' h₂
        _ = (#(allGraphs n r) : ℝ) *  ∑ k ∈ Finset.Ioc 0 K',
            ( 1 / 4 : ℝ) ^ k := by
          -- linear algebra
          congr! 3 with k hk
          have : Real.exp 1 ^ 3 * K * (r : ℝ) ^ 4
              = K * Real.exp 1 ^ 3 * (r : ℝ) ^ 4 := by
            linarith
          rw [this]
          have : K * Real.exp 1 ^ 3 * (r : ℝ) ^ 4 / (4 * (n : ℝ))
              = K * (Real.exp 1 ^ 3 * (r : ℝ) ^ 4 / ((n : ℝ))) * (1 / 4) := by
            field_simp [mul_assoc, mul_comm (1 / 4)]
            -- exact Or.inl (mul_comm _ _)
          rw [this]
          have : (1 / K : ℝ) = Real.exp 1 ^ 3 * (r : ℝ) ^ 4 / ((n : ℝ)) := by
            rw [hKdef, one_div_div]
          rw [←this]
          have : K * (1 / K) = 1 := by
            have : 0 < K := by
              have h₂ : (0 : ℝ) < (n : ℝ) := by
                nlinarith
              have h₃ : (0 : ℝ) < Real.exp 1 ^ 3 * (r : ℝ) ^ 4 := by
                have : (0 : ℝ) < (r : ℝ) := by
                  aesop
                positivity
              rw [hKdef]
              positivity
            have : 0 ≠ K := by exact ne_of_lt this
            exact mul_one_div_cancel (id (Ne.symm this))
          rw [this]
          linarith


/-- At least two thirds of graphs constructed by `Ω` are
    (Θ(n), θ(r))- bipartite vertex expanders -/
theorem vertex_expanders_exist (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r):
    (2 / 3 : ℝ) ≤ #(allGraphsH n r) / #(allGraphs n r) := by
  -- First set up some standard notation and basic facts
  let K := n / ((Real.exp 1)^3 * r^4 : ℝ)
  have hK₀ : 0 ≤ K := by positivity
  have hK : K < (n : ℝ) := by
    have hK₁ : ((Real.exp 1)^3 * 2^4 : ℝ) ≤ (Real.exp 1)^3 * r^4 := by
      field_simp
      have : 2 ^ 4 ≤ r ^ 4 := by exact Nat.pow_le_pow_left hr 4
      rw [← Nat.cast_pow]
      refine EReal.coe_le_coe_iff.mp ?_
      simp only [EReal.coe_pow, Nat.cast_pow, EReal.coe_natCast]
      gcongr
      exact_mod_cast hr
      -- field_simp
      -- refine pow_le_pow_left₀ ?_ ?_ 4
      -- · aesop
      -- · exact Nat.ofNat_le_cast.mpr hr
    have hK₂ : 0 < (Real.exp 1 ^ 3 * (r : ℝ) ^ 4) := by
      positivity
    have hK₃ : 1 < (Real.exp 1 ^ 3 * (r : ℝ) ^ 4) := by
      have hK₃a : 16 ≤ (r : ℝ) ^ 4 := by
        have : (16 : ℝ) = 2 ^ 4 := by norm_num
        rw [this]
        have : 2 ^ 4 ≤ r ^ 4 := by exact Nat.pow_le_pow_left hr 4
        rw [← Nat.cast_pow]
        refine EReal.coe_le_coe_iff.mp ?_
        simp only [EReal.coe_pow, Nat.cast_pow, EReal.coe_natCast]
        gcongr
        exact_mod_cast hr
        -- field_simp
        -- refine pow_le_pow_left₀ ?_ ?_ 4
        -- · aesop
        -- · exact Nat.ofNat_le_cast.mpr hr
      have hK₃b : Real.exp 1 ^ 3 * 16 ≤ Real.exp 1 ^ 3 * (r : ℝ) ^ 4 := by
        linarith
      have hK₃c : 1 < Real.exp 1 ^ 3 * 16 := by
        simp only [Real.exp_one_pow, Nat.cast_ofNat]
        have ha : 1 < Real.exp 3 := by norm_num
        have hb : 1 < 16 := by norm_num
        nlinarith
      exact lt_of_le_of_lt' hK₃b hK₃c
    rw [show K = (↑n : ℝ) / (rexp 1 ^ 3 * ↑r ^ 4) by rfl]
    exact (div_lt_self (by exact_mod_cast hn) hK₃)
    -- field_simp [hK₂]
    -- unfold K
    -- apply div_lt_self
    -- · aesop
    -- · exact hK₃
  let K' := Nat.floor K
  have hka : ∀ k ∈ Finset.Ioc 0 K', k ≤ n := by
    have hka₂ : K' < n := (Nat.floor_lt hK₀).mpr hK
    intro k hk
    have hka₃ : k ≤ K' := by
      aesop
      -- because K upper bounds k
    exact Nat.le_trans hka₃ hka₂.le
  have hr' : 1 ≤ r := by nlinarith
  have hG : 0 ≠  (#(allGraphs n r) : ℝ) := by
    have : (allGraphs n r).Nonempty := G_nonempty n r hn
    have : 0 ≠ #(allGraphs n r) := Ne.symm ((fun {α} {s} ↦ card_ne_zero.mpr) this)
    have : #(allGraphs n r) ≠ 0 := by exact id (Ne.symm this)
    have : (#(allGraphs n r) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr this
    exact id (Ne.symm this)
  have hG' : 0 < (#(allGraphs n r) : ℝ) := by
    have : 0 ≤ (#(allGraphs n r) : ℝ) := by exact Nat.cast_nonneg' #(allGraphs n r)
    exact lt_of_le_of_ne this hG
  have h₀ : allGraphsH n r ⊆ allGraphs n r := by
    exact H_subset_G n r

  -- The result now essentially follows from the calc block that closely follows
  -- the informal proof. This is below and also in the two extracted lemmas
  have h₁ : (#(allGraphs n r \ allGraphsH n r) : ℝ) / #(allGraphs n r) ≤ 1 / 3 := by
    have h₂ : (#(allGraphs n r \ allGraphsH n r) : ℝ) ≤ #(allGraphs n r) / 3 := by
      have hKdef : K = (n :  ℝ) / (Real.exp 1 ^ 3 * ↑r ^ 4) := by exact rfl
      have h₂a : (allGraphs n r \ allGraphsH n r) = {G ∈ allGraphs n r |
          ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
          (#S ≤ K) ∧ (#(G.neighbourhoodOfSet S) < #S*(r-2)) } := by
        rw [hKdef]
        rw [allGraphs_set_subtract n r hn hr]
        aesop
      rw [h₂a]
      have hKdef' : K' = ⌊K⌋₊ := by exact rfl
      have hcalca : (#({G ∈ allGraphs n r |
          ∃ S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n),
          (#S ≤ K) ∧ #(G.neighbourhoodOfSet S) < #S * (r - 2)}) : ℝ) ≤
          ∑ k ∈ Finset.Ioc 0 K',
            ∑ G ∈ allGraphs n r,
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
            ∧ (G.neighbourhoodOfSet S).card < k * (r - 2)}
            (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) := by
          exact calc_block_1 n r K hK₀ K' hKdef'
          --exact calc_block_1 n r K hKdef hK₀ hK K' hKdef' hka hr' hG hG' h₀

      have hcalcb : ∑ k ∈ Finset.Ioc 0 K',
            ∑ G ∈ allGraphs n r,
            ∑ S ∈ (Finset.powersetCard k (Finset.univ : Finset (Fin (n + n)))),
            (Set.indicator {G | S ⊆ Finset.univ.filter (fun i : Fin (n + n) => i.val < n)
            ∧ (G.neighbourhoodOfSet S).card < k * (r - 2)}
            (fun _ => 1 : MultiDiGraph _ _ → ℝ) G : ℝ) ≤
            (#(allGraphs n r) : ℝ) *  ∑ k ∈ Finset.Ioc 0 K',
            ( 1 / 4 : ℝ) ^ k  := by
          exact calc_block_2 n r hn hr K hKdef hK₀ hK K' hKdef' hka hr' hG --hG' h₀


      have hcalcc : (#(allGraphs n r) : ℝ) *  ∑ k ∈ Finset.Ioc 0 K',
            ( 1 / 4 : ℝ) ^ k ≤ (#(allGraphs n r) : ℝ) / 3 := by

        calc (#(allGraphs n r) : ℝ) *  ∑ k ∈ Finset.Ioc 0 K', ( 1 / 4 : ℝ) ^ k
          _ = (#(allGraphs n r) : ℝ) *  ((∑ k ∈ (Finset.Icc 0 K'),
              ( 1 / 4 : ℝ) ^ k ) - ( 1 / 4 : ℝ) ^ 0) := by
            -- split the sum
            have ha₁ : (∑ k ∈ Finset.Icc 0 K', (1 / 4 : ℝ) ^ k) =
                (∑ k ∈ Finset.Ioc 0 K', (1 / 4 : ℝ) ^ k) + (1 / 4 : ℝ) ^ 0 := by
              rw [Finset.sum_Ioc_add_eq_sum_Icc]
              simp
            rw [ha₁]
            linarith
          _ = (#(allGraphs n r) : ℝ) *  (∑ k ∈ (Finset.Icc 0 K'),
              (( 1 / 4 : ℝ) ^ k ) - 1)  := by
            -- direct calculation
            have : (1 / 4 : ℝ) ^ 0 = 1 := by norm_num
            rw [this]
          _ = (#(allGraphs n r) : ℝ) *  (∑ k ∈ (Finset.Icc 0 K'),
              ( 1 / 4 : ℝ) ^ k ) -  (#(allGraphs n r) : ℝ)  := by
            -- direct calculation
            linarith
          _ ≤ (#(allGraphs n r) : ℝ) *  ∑' k : ℕ, ( 1 / 4 : ℝ) ^ k
              -  (#(allGraphs n r) : ℝ) := by
            -- upper bound the sum by infinite sum
            have : (∑ k ∈ (Finset.Icc 0 K'), ( 1 / 4 : ℝ) ^ k ) ≤
                (∑' k : ℕ, ( 1 / 4 : ℝ) ^ k  ) := by
              apply Summable.sum_le_tsum
              · intro i hi
                positivity
              · apply summable_geometric_of_lt_one
                all_goals
                norm_num
            nlinarith
          _ = (#(allGraphs n r) : ℝ) * (4 / 3 : ℝ) -  (#(allGraphs n r) : ℝ) := by
            -- direct evaluation of a convergent sum
            have : ∑' k : ℕ, ( 1 / 4 : ℝ) ^ k   = (1 - ( 1 / 4 : ℝ)) ^ (-1 : ℝ) := by
              have hs := tsum_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 4 : ℝ) < 1)
              rw [hs]
              linarith
            rw [this]
            linarith
          _ = (#(allGraphs n r) : ℝ) / 3 := by
            linarith
      grind
    refine (div_le_div_iff₀ hG' ?_).mpr ?_
    · linarith
    · simp_all only [ne_eq, Nat.cast_pos, card_pos, one_mul]
      linarith [h₂]
  -- Using some simple facts to get this exactly as claimed
  have h₃ : (#(allGraphs n r \ allGraphsH n r) : ℝ)
    = #(allGraphs n r) - #(allGraphsH n r) := cast_card_sdiff h₀
  rw [h₃] at h₁
  have h₄ : ((#(allGraphs n r) : ℝ) - #(allGraphsH n r)) / #(allGraphs n r) =
      (1 : ℝ) - #(allGraphsH n r) / #(allGraphs n r) := by
    field_simp
  rw [h₄] at h₁
  nlinarith

--#lint
