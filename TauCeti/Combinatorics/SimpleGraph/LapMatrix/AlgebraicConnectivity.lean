/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.LapMatrix.Eigenvalues
import Mathlib.Algebra.Order.Star.Real
import TauCeti.Analysis.InnerProductSpace.CourantFischer
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Combinatorics.SimpleGraph.AdjMatrix.Basic
import TauCeti.Combinatorics.SimpleGraph.LapMatrix.Complement

/-!
# The algebraic connectivity of a graph

The algebraic connectivity `a(G) = SimpleGraph.algebraicConnectivity G` of a finite simple graph
on `n ≥ 2` vertices is its second smallest Laplacian eigenvalue. Since the all-ones vector `𝟙`
spans part of the kernel of the Laplacian `L`, `a(G)` is the least value of the Rayleigh quotient
`xᵀLx / xᵀx` over the nonzero vectors `x` orthogonal to `𝟙`, that is with `∑ v, x v = 0`:

* `SimpleGraph.algebraicConnectivity_mul_dotProduct_self_le`: `a(G) · xᵀx ≤ xᵀLx` whenever
  `∑ v, x v = 0` (for every `n`, as `a(G) = 0` when `n ≤ 1`);
* `SimpleGraph.exists_dotProduct_mulVec_le_algebraicConnectivity_mul`: for `n ≥ 2` some nonzero
  `x` with `∑ v, x v = 0` has `xᵀLx ≤ a(G) · xᵀx`.

From this variational form follow two theorems of Fiedler.

* `SimpleGraph.algebraicConnectivity_add_le_sup`: for edge-disjoint graphs `G` and `H` on the same
  vertices, `a(G) + a(H) ≤ a(G ⊔ H)`.
* `SimpleGraph.algebraicConnectivity_le_card`: if the subgraph induced on the complement of a
  vertex set `D` is not connected (for instance empty), then `a(G) ≤ |D|`. The test vector is
  `|C₂|` on a component `C₁` of that subgraph, `-|C₁|` on the rest `C₂` of the complement, and
  `0` on `D`; only the edges at `D` contribute to its quadratic form.

## References

* M. Fiedler, *Algebraic connectivity of graphs*, Czechoslovak Math. J. 23 (1973), 298–305.
* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer Universitext (2012),
  Propositions 1.7.1 and 1.7.2.
-/

public section

open Finset Matrix
open scoped InnerProductSpace

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- On the vectors orthogonal to the eigenvector of the smallest eigenvalue in the sorted
eigenbasis of the Laplacian, the quadratic form is at least `a(G)` times the squared norm. -/
private theorem algebraicConnectivity_mul_dotProduct_self_le_of_inner_eq_zero
    (hn : 2 ≤ Fintype.card V) {y : V → ℝ}
    (hy : ⟪(isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis
      finrank_euclideanSpace ⟨Fintype.card V - 1, by omega⟩, WithLp.toLp 2 y⟫_ℝ = 0) :
    G.algebraicConnectivity * (y ⬝ᵥ y) ≤ y ⬝ᵥ (G.lapMatrix ℝ *ᵥ y) := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)
  set b := hT.eigenvectorBasis finrank_euclideanSpace
  let l : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hmem : WithLp.toLp 2 y ∈ b.spanIndices {l}ᶜ := by
    rw [OrthonormalBasis.mem_spanIndices_iff]
    intro i hi
    rw [Set.notMem_compl_iff, Set.mem_singleton_iff] at hi
    rw [b.repr_apply_apply, hi, hy]
  have h := hT.le_re_inner_apply_self_of_mem_spanIndices finrank_euclideanSpace
    (c := G.algebraicConnectivity) (fun i hi ↦ ?_) hmem
  · rwa [← EuclideanSpace.dotProduct_ofLp_self, WithLp.ofLp_toLp, RCLike.re_to_real,
      inner_toEuclideanLin_toLp_eq_dotProduct_mulVec] at h
  · -- Every index but the last is at most `n - 2`, where the eigenvalue is `a(G)`.
    rw [G.algebraicConnectivity_of_two_le hn, lapEigenvalues_def,
      IsHermitian.eigenvalues₀_eq_eigenvalues]
    refine hT.eigenvalues_antitone finrank_euclideanSpace ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Fin.ext_iff, l] at hi
    simp only [Fin.le_def]
    omega

/-- **The variational lower bound for the algebraic connectivity.** For every vector `x`
orthogonal to the all-ones vector, `a(G) · xᵀx ≤ xᵀLx`. -/
theorem algebraicConnectivity_mul_dotProduct_self_le {x : V → ℝ} (hx : ∑ v, x v = 0) :
    G.algebraicConnectivity * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) := by
  have hpsd (y : V → ℝ) : 0 ≤ y ⬝ᵥ (G.lapMatrix ℝ *ᵥ y) := by
    simpa using (posSemidef_lapMatrix ℝ G).dotProduct_mulVec_nonneg y
  by_cases hn : 2 ≤ Fintype.card V
  swap
  · rw [G.algebraicConnectivity_of_lt_two (by omega), zero_mul]
    exact hpsd x
  -- Facts about the all-ones vector `𝟙`: it is in the kernel of `L`, orthogonal to `x` and to
  -- the range of `L`, and its squared norm is `n`.
  have hL1 : G.lapMatrix ℝ *ᵥ 1 = 0 := G.lapMatrix_mulVec_one_eq_zero (R := ℝ)
  have h1L (y : V → ℝ) : 1 ⬝ᵥ (G.lapMatrix ℝ *ᵥ y) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, (isSymm_lapMatrix ℝ G).eq, hL1, zero_dotProduct]
  have hx1 : 1 ⬝ᵥ x = 0 := by rw [one_dotProduct, hx]
  have hx1' : x ⬝ᵥ 1 = 0 := by rw [dotProduct_one, hx]
  have h11 : (1 : V → ℝ) ⬝ᵥ 1 = Fintype.card V := by simp
  have ha := G.algebraicConnectivity_nonneg
  -- `b` is the eigenvector of the smallest eigenvalue in the sorted eigenbasis.
  set b := (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis
    finrank_euclideanSpace ⟨Fintype.card V - 1, by omega⟩
  set α := ⟪b, WithLp.toLp 2 (1 : V → ℝ)⟫_ℝ
  set β := ⟪b, WithLp.toLp 2 x⟫_ℝ
  by_cases hα : α = 0
  · -- `𝟙` itself is orthogonal to `b`, which forces `a(G) = 0`.
    have h := G.algebraicConnectivity_mul_dotProduct_self_le_of_inner_eq_zero hn hα
    rw [hL1, dotProduct_zero, h11] at h
    have hn' : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (by omega)
    have ha0 : G.algebraicConnectivity = 0 := le_antisymm (nonpos_of_mul_nonpos_left h hn') ha
    rw [ha0, zero_mul]
    exact hpsd x
  · -- Otherwise `y = α x - β 𝟙` is orthogonal to `b`, and `L y = α L x`.
    have h := G.algebraicConnectivity_mul_dotProduct_self_le_of_inner_eq_zero hn
      (y := α • x - β • 1) (by
        simp only [WithLp.toLp_sub, WithLp.toLp_smul, inner_sub_right, real_inner_smul_right,
          α, β]
        ring)
    simp only [mulVec_sub, mulVec_smul, hL1, smul_zero, sub_zero, dotProduct_smul,
      sub_dotProduct, smul_dotProduct, h1L, hx1, hx1', h11, dotProduct_sub, smul_eq_mul] at h
    have hβ : 0 ≤ G.algebraicConnectivity * (β ^ 2 * Fintype.card V) := by positivity
    have hα2 : 0 < α ^ 2 := by positivity
    nlinarith

/-- **The variational upper bound for the algebraic connectivity.** On at least two vertices,
some nonzero vector `x` orthogonal to the all-ones vector has `xᵀLx ≤ a(G) · xᵀx`. Together with
`SimpleGraph.algebraicConnectivity_mul_dotProduct_self_le`, `a(G)` is the least Rayleigh quotient
`xᵀLx / xᵀx` over these vectors. -/
theorem exists_dotProduct_mulVec_le_algebraicConnectivity_mul (h : 2 ≤ Fintype.card V) :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∑ v, x v = 0 ∧
      x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) ≤ G.algebraicConnectivity * (x ⬝ᵥ x) := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let one : EuclideanSpace ℝ V := WithLp.toLp 2 1
  have hone : one ≠ 0 := by
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    simp [one]
  have hdim : (k : ℕ) + 1 ≤ Module.finrank ℝ (ℝ ∙ one)ᗮ := by
    have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ one)
    rw [finrank_span_singleton hone, finrank_euclideanSpace] at this
    simp only [k]
    omega
  obtain ⟨y, hy, hy1, hle⟩ := hT.exists_unit_vector_re_inner_le_eigenvalue_of_le_finrank
    finrank_euclideanSpace k _ hdim
  obtain ⟨x, rfl⟩ : ∃ x, y = WithLp.toLp 2 x := ⟨_, (WithLp.toLp_ofLp 2 y).symm⟩
  have hxx : x ⬝ᵥ x = 1 := by
    rw [← WithLp.ofLp_toLp 2 x, EuclideanSpace.dotProduct_ofLp_self, hy1, one_pow]
  refine ⟨x, ?_, ?_, ?_⟩
  · rintro rfl
    simp at hxx
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy
    simpa [one, EuclideanSpace.inner_toLp_toLp, dotProduct] using hy
  · rw [hxx, mul_one, G.algebraicConnectivity_of_two_le h, lapEigenvalues_def,
      IsHermitian.eigenvalues₀_eq_eigenvalues]
    rwa [RCLike.re_to_real, inner_toEuclideanLin_toLp_eq_dotProduct_mulVec] at hle

/-- **Fiedler's superadditivity of the algebraic connectivity.** For edge-disjoint graphs `G` and
`H` on the same vertex type, `a(G) + a(H) ≤ a(G ⊔ H)` (Brouwer–Haemers, Proposition 1.7.1). -/
theorem algebraicConnectivity_add_le_sup {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] [DecidableRel (G ⊔ H).Adj] (hGH : Disjoint G H) :
    G.algebraicConnectivity + H.algebraicConnectivity ≤ (G ⊔ H).algebraicConnectivity := by
  by_cases hn : 2 ≤ Fintype.card V
  · obtain ⟨x, hx0, hx, hle⟩ := (G ⊔ H).exists_dotProduct_mulVec_le_algebraicConnectivity_mul hn
    have hpos : 0 < x ⬝ᵥ x := by simpa using dotProduct_star_self_pos_iff.mpr hx0
    have hG := G.algebraicConnectivity_mul_dotProduct_self_le hx
    have hH := H.algebraicConnectivity_mul_dotProduct_self_le hx
    rw [lapMatrix_sup_of_disjoint ℝ hGH, add_mulVec, dotProduct_add] at hle
    nlinarith
  · simp [algebraicConnectivity_of_lt_two, Nat.lt_of_not_le hn]

/-- If `x` vanishes on a vertex set `D` and is constant along the edges outside `D`, then
`xᵀLx ≤ |D| · xᵀx`: only the edges between `D` and its complement contribute to the quadratic
form, and each vertex has at most `|D|` neighbours in `D`. -/
private theorem dotProduct_mulVec_le_card_mul_dotProduct_self (D : Finset V) {x : V → ℝ}
    (hxD : ∀ v ∈ D, x v = 0) (hedge : ∀ i j, G.Adj i j → i ∉ D → j ∉ D → x i = x j) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) ≤ #D * (x ⬝ᵥ x) := by
  have hterm (i j : V) : (if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
      (if i ∈ D then 1 else 0) * x j ^ 2 + x i ^ 2 * (if j ∈ D then 1 else 0) := by
    by_cases hadj : G.Adj i j
    · by_cases hi : i ∈ D <;> by_cases hj : j ∈ D
      · simp [hadj, hi, hj, hxD]
      · simp [hadj, hi, hj, hxD]
      · simp [hadj, hi, hj, hxD]
      · simp [hadj, hi, hj, hedge i j hadj hi hj]
    · simp only [hadj, ↓reduceIte]
      positivity
  rw [← toLinearMap₂'_apply', lapMatrix_toLinearMap₂', div_le_iff₀ two_pos]
  refine (sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hterm i j).trans_eq ?_
  simp only [sum_add_distrib, ← sum_mul_sum, sum_boole, filter_mem_eq_inter, univ_inter,
    dotProduct, sq]
  ring

/-- **Fiedler's vertex-cut bound for the algebraic connectivity.** If deleting a vertex set `D`
leaves a subgraph that is not connected, then `a(G) ≤ |D|` (Brouwer–Haemers, Proposition 1.7.2).
The deleted set may be everything, as the graph on no vertices is not connected. -/
theorem algebraicConnectivity_le_card (D : Finset V)
    (h : ¬(G.induce (D : Set V)ᶜ).Connected) : G.algebraicConnectivity ≤ #D := by
  classical
  simp only [connected_iff_exists_forall_reachable, not_exists, not_forall] at h
  by_cases hD : ∃ u, u ∉ D
  swap
  · -- With nothing outside `D`, the bound is `a(G) ≤ ν₁ ≤ n`.
    simp only [not_exists, not_not] at hD
    rw [Finset.eq_univ_of_forall hD, card_univ]
    by_cases hn : 2 ≤ Fintype.card V
    · have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      rw [G.algebraicConnectivity_of_two_le hn]
      exact (G.lapEigenvalues_le_largestLapEigenvalue _).trans G.largestLapEigenvalue_le_card
    · rw [G.algebraicConnectivity_of_lt_two (by omega)]
      positivity
  obtain ⟨u, hu⟩ := hD
  obtain ⟨w, hw⟩ := h ⟨u, hu⟩
  -- `p v`: `v` lies outside `D`, in the component of `u` in the induced subgraph.
  let p : V → Prop := fun v ↦ ∃ hv : v ∉ D, (G.induce (D : Set V)ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩
  let c₁ : ℝ := #{v | v ∉ D ∧ p v}
  let c₂ : ℝ := #{v | v ∉ D ∧ ¬p v}
  let x : V → ℝ := fun v ↦ if v ∈ D then 0 else if p v then c₂ else -c₁
  have hxD (v : V) (hv : v ∈ D) : x v = 0 := by simp [x, hv]
  -- `x` is constant along the edges outside `D`.
  have hedge (i j : V) (hij : G.Adj i j) (hi : i ∉ D) (hj : j ∉ D) : x i = x j := by
    have hadj : (G.induce (D : Set V)ᶜ).Adj ⟨i, hi⟩ ⟨j, hj⟩ := induce_adj.mpr hij
    have hp : p i ↔ p j := ⟨fun ⟨_, hr⟩ ↦ ⟨hj, hr.trans hadj.reachable⟩,
      fun ⟨_, hr⟩ ↦ ⟨hi, hr.trans hadj.symm.reachable⟩⟩
    simp only [x, hi, hj, hp, ↓reduceIte]
  have hsum : ∑ v, x v = 0 := by
    have hx (v : V) : x v = c₂ * (if v ∉ D ∧ p v then 1 else 0) -
        c₁ * (if v ∉ D ∧ ¬p v then 1 else 0) := by
      by_cases hv : v ∈ D <;> by_cases hpv : p v <;> simp [x, hv, hpv]
    simp only [hx, sum_sub_distrib, ← mul_sum, sum_boole]
    ring
  have hx0 : x ≠ 0 := by
    have hc₂ : 0 < c₂ := by
      have : w.val ∈ ({v | v ∉ D ∧ ¬p v} : Finset V) :=
        mem_filter.mpr ⟨mem_univ _, w.property, fun ⟨_, hr⟩ ↦ hw hr⟩
      exact Nat.cast_pos.mpr (card_pos.mpr ⟨_, this⟩)
    intro h0
    have hpu : p u := ⟨hu, .rfl⟩
    have hxu : x u = c₂ := by simp [x, hu, hpu]
    rw [h0, Pi.zero_apply] at hxu
    exact hc₂.ne hxu
  have hquad := G.dotProduct_mulVec_le_card_mul_dotProduct_self D hxD hedge
  have hpos : 0 < x ⬝ᵥ x := by simpa using dotProduct_star_self_pos_iff.mpr hx0
  have hlow := G.algebraicConnectivity_mul_dotProduct_self_le hsum
  exact le_of_mul_le_mul_right (hlow.trans hquad) hpos

end SimpleGraph
