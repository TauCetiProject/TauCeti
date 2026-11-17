/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Topology.ConnectedComponents

/-!
# Runge's approximation theorem and finite-rank Runge operators

A compact subset `K` of an open plane set `Ω ⊆ ℂ` forms a *compact Runge pair*
(`TauCeti.IsRungeCompactPair Ω K`) when `K` is filled in `Ω` (`TauCeti.IsFilledIn K Ω`), meaning no
connected component of `Ω \ K` has compact closure contained in `Ω`.

This file establishes three forms of Runge's theorem for compact subsets of open plane sets:

* **Finite-rank linear Runge operator** (`TauCeti.exists_finite_rank_runge_operator`): for a
  compact Runge pair `(Ω, K)` and an open neighborhood `U ⊇ K`, there is a compact collar
  `L ⊆ U ∩ Ω` with `K ⊆ interior L` such that for every `ε > 0` one finite-rank evaluation formula
  `f ↦ fun z ↦ ∑ j, w j * f (ζ j) * g j z`, with nodes `ζ j ∈ interior L`, weights `w j : ℂ`, and
  functions `g j` holomorphic on `Ω` all chosen independently of `f`, satisfies
  `‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B` on `K` for every `U`-holomorphic `f` bounded by `B`
  on `L`.
* **Scalar Runge equivalence** (`IsOpen.isRungeCompactPair_iff_approximation`): for open `Ω` and
  compact `K ⊆ Ω`, `(Ω, K)` is a compact Runge pair if and only if every function holomorphic on
  an open neighborhood of `K` can be uniformly approximated on `K` by functions holomorphic on `Ω`.
* **Point separation off a Runge compactum**
  (`TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_lt_one_lt`): adjoining a point of `Ω`
  preserves compact Runge pairs (`TauCeti.IsRungeCompactPair.insert`), so every `a ∉ K` is
  separated from a Runge compactum `K` by an `Ω`-holomorphic function of modulus `< 1` on `K` and
  `> 1` at `a`.

## Implementation notes

To obtain the operator-norm bound `ε * B` uniformly across all `U`-holomorphic `f`, we pick a
compact collar `L ⊆ U ∩ Ω` with `K ⊆ interior L`, apply the discretized Cauchy–Pompeiu formula
`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le` on `interior L` to approximate every
`U`-holomorphic `f` uniformly on `K` by a fixed linear combination of simple fractions
`(z - ζ j)⁻¹` with poles `ζ j ∈ interior L \ K`, and replace each simple fraction on `K` by an
`Ω`-holomorphic function via `TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1, p. 25.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.9.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.1.
-/

public section

open Complex Metric Set Filter
open scoped Topology

namespace TauCeti

/-- A compact Runge pair: an open `Ω ⊆ ℂ`, a compact `K ⊆ Ω`, and `K` filled in `Ω` (no connected
component of `Ω \ K` has compact closure contained in `Ω`). -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

theorem isRungeCompactPair_def (Ω K : Set ℂ) :
    IsRungeCompactPair Ω K = (IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω) :=
  (rfl)

theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  Iff.rfl

namespace IsRungeCompactPair

variable {Ω K : Set ℂ}

/-- The ambient set `Ω` of a compact Runge pair `(Ω, K)` is open. -/
protected theorem isOpen (h : IsRungeCompactPair Ω K) : IsOpen Ω := h.1

/-- The subset `K` of a compact Runge pair `(Ω, K)` is compact. -/
protected theorem isCompact (h : IsRungeCompactPair Ω K) : IsCompact K := h.2.1

/-- The subset `K` of a compact Runge pair `(Ω, K)` is contained in `Ω`. -/
protected theorem subset (h : IsRungeCompactPair Ω K) : K ⊆ Ω := h.2.2.1

/-- The subset `K` of a compact Runge pair `(Ω, K)` is filled in `Ω`. -/
protected theorem isFilledIn (h : IsRungeCompactPair Ω K) : IsFilledIn K Ω := h.2.2.2

end IsRungeCompactPair

@[simp]
theorem isRungeCompactPair_empty {Ω : Set ℂ} : IsRungeCompactPair Ω ∅ ↔ IsOpen Ω :=
  ⟨IsRungeCompactPair.isOpen, fun hΩ ↦ ⟨hΩ, isCompact_empty, empty_subset _, hΩ.isFilledIn_empty⟩⟩

section FiniteRankOperator

/-- Bounding the pole-pushing step of `exists_finite_rank_runge_operator`: replacing each simple
fraction `(ξ - ζ j)⁻¹` in the discretized Cauchy–Pompeiu sum by an `Ω`-holomorphic approximant
`g j` within `(ε / 2) / (∑ j, ‖w j‖ + 1)` incurs error at most `(ε / 2) * B`. -/
private theorem norm_sum_inv_sub_le {N : ℕ} {ζ : Fin N → ℂ} {w : Fin N → ℂ} {g : Fin N → ℂ → ℂ}
    {f : ℂ → ℂ} {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) (hfζ : ∀ j, ‖f (ζ j)‖ ≤ B) {ξ : ℂ}
    (hgξ : ∀ j, ‖(ξ - ζ j)⁻¹ - g j ξ‖ ≤ (ε / 2) / ((∑ i : Fin N, ‖w i‖) + 1)) :
    ‖∑ j, w j * f (ζ j) * (ξ - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j ξ‖ ≤ ε / 2 * B := by
  set τ : ℝ := (ε / 2) / ((∑ i : Fin N, ‖w i‖) + 1)
  rw [← Finset.sum_sub_distrib]
  have hsum_le : (∑ j, ‖w j‖) / ((∑ j, ‖w j‖) + 1) ≤ 1 :=
    div_le_one_of_le₀ (by linarith) (by positivity)
  calc ‖∑ j, (w j * f (ζ j) * (ξ - ζ j)⁻¹ - w j * f (ζ j) * g j ξ)‖
      ≤ ∑ j, ‖w j * f (ζ j) * ((ξ - ζ j)⁻¹ - g j ξ)‖ :=
        (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ ↦ by rw [← mul_sub])
    _ ≤ ∑ j, ‖w j‖ * B * τ := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hfζ j) (norm_nonneg _))
          (hgξ j) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hB)
    _ = ((∑ j, ‖w j‖) / ((∑ j, ‖w j‖) + 1)) * (ε / 2 * B) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        simp only [τ]
        ring
    _ ≤ 1 * (ε / 2 * B) := mul_le_mul_of_nonneg_right hsum_le (by positivity)
    _ = ε / 2 * B := one_mul _

/-- **Finite-rank Runge operator.** Fix a compact collar `L` inside the holomorphy neighborhood and
the ambient domain. For every `ε > 0`, one finite evaluation formula, independent of `f`,
approximates every `U`-holomorphic `f` on `K` with an explicit operator bound `ε * B` in terms of
any upper bound `B` for `‖f‖` on `L`. This linear interface preserves smooth or holomorphic
dependence on external parameters. -/
theorem exists_finite_rank_runge_operator {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ ζ : Fin N → ℂ, ∃ w : Fin N → ℂ,
          ∃ g : Fin N → ℂ → ℂ,
            (∀ j, ζ j ∈ interior L) ∧
            (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
            ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
              ∀ B : ℝ, (∀ z ∈ L, ‖f z‖ ≤ B) →
                ∀ z ∈ K,
                  ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B := by
  obtain ⟨L, hL, hKL, hLUΩ⟩ := exists_compact_between hRunge.isCompact
    (hU.inter hRunge.isOpen) (subset_inter hKU hRunge.subset)
  have hLU : L ⊆ U := hLUΩ.trans inter_subset_left
  refine ⟨L, hL, hKL, hLUΩ, fun ε hε ↦ ?_⟩
  obtain ⟨N, ζ, w, hζ, hdisc⟩ :=
    hRunge.isCompact.exists_norm_sub_sum_mul_sub_inv_smul_le.{0} isOpen_interior hKL (half_pos hε)
  set τ : ℝ := (ε / 2) / ((∑ j : Fin N, ‖w j‖) + 1)
  have hτ : 0 < τ := div_pos (half_pos hε) (by positivity)
  choose g hgΩ hgK using fun j : Fin N ↦
    hRunge.isFilledIn.exists_differentiableOn_norm_inv_sub_lt hRunge.isOpen hRunge.isCompact
      hRunge.subset (hζ j).2 hτ
  refine ⟨N, ζ, w, g, fun j ↦ (hζ j).1, hgΩ, fun f hf B hfL ξ hξ ↦ ?_⟩
  have hB : 0 ≤ B := (norm_nonneg (f ξ)).trans (hfL ξ (interior_subset (hKL hξ)))
  have hq_err : ‖f ξ - ∑ j, w j * f (ζ j) * (ξ - ζ j)⁻¹‖ ≤ ε / 2 * B := by
    have h := hdisc f B (hf.mono (interior_subset.trans hLU))
      (fun z hz ↦ hfL z (interior_subset hz)) ξ hξ
    refine le_trans (le_of_eq ?_) h
    congr 2
    exact Finset.sum_congr rfl fun j _ ↦ by simp only [smul_eq_mul]; ring
  have hp_err : ‖∑ j, w j * f (ζ j) * (ξ - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j ξ‖ ≤ ε / 2 * B :=
    norm_sum_inv_sub_le hε hB (fun j ↦ hfL (ζ j) (interior_subset (hζ j).1))
      fun j ↦ (hgK j ξ hξ).le
  calc ‖f ξ - ∑ j, w j * f (ζ j) * g j ξ‖
      ≤ ‖f ξ - ∑ j, w j * f (ζ j) * (ξ - ζ j)⁻¹‖ +
          ‖∑ j, w j * f (ζ j) * (ξ - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j ξ‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (f ξ - ∑ j, w j * f (ζ j) * (ξ - ζ j)⁻¹)
            ((∑ j, w j * f (ζ j) * (ξ - ζ j)⁻¹) - ∑ j, w j * f (ζ j) * g j ξ)
    _ ≤ ε / 2 * B + ε / 2 * B := add_le_add hq_err hp_err
    _ = ε * B := by ring

end FiniteRankOperator

section Equivalence

/-- **Forward Runge approximation.** If `(Ω, K)` is a compact Runge pair and `f` is holomorphic on
a set `U` containing `K` in its interior, then `f` can be uniformly approximated on `K` within any
`ε > 0` by a function holomorphic on `Ω`. -/
theorem IsRungeCompactPair.exists_differentiableOn_norm_sub_lt {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hKU : K ⊆ interior U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, -, hLUΩ, hop⟩ := exists_finite_rank_runge_operator hRunge isOpen_interior hKU
  have hf_int : DifferentiableOn ℂ f (interior U) := hf.mono interior_subset
  obtain ⟨C, hC⟩ :=
    hL.exists_bound_of_continuousOn (hf_int.continuousOn.mono (hLUΩ.trans inter_subset_left))
  set B : ℝ := max 0 C + 1
  have hB : 0 < B := by positivity
  obtain ⟨N, ζ, w, g, -, hgΩ, happrox⟩ := hop (ε / (2 * B)) (by positivity)
  refine ⟨fun z ↦ ∑ j, w j * f (ζ j) * g j z,
    DifferentiableOn.fun_sum fun j _ ↦ (hgΩ j).const_mul _, fun z hz ↦ ?_⟩
  calc ‖f z - ∑ j, w j * f (ζ j) * g j z‖
      ≤ ε / (2 * B) * B :=
        happrox f hf_int B (fun y hy ↦ (hC y hy).trans ((le_max_right 0 C).trans (by linarith)))
          z hz
    _ = ε / 2 := by field_simp [hB.ne']
    _ < ε := half_lt_self hε

/-- **Converse of Runge's theorem.** If every function holomorphic near a closed subset `K` of an
open set `Ω` is uniformly approximable on `K` by functions holomorphic on `Ω`, then `K` is filled
in `Ω`: approximating `(z - x)⁻¹` for a point `x` in a relatively compact component `C` of `Ω \ K`
violates the maximum modulus principle for `1 - (z - x) * g z` on `C`. -/
private theorem isFilledIn_of_forall_exists_differentiableOn_norm_sub_lt {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsClosed K)
    (happrox : ∀ U : Set ℂ, IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε) :
    IsFilledIn K Ω := by
  rw [isFilledIn_iff]
  rintro x ⟨hxΩ, hxK⟩ ⟨hcpt, hclΩ⟩
  set C : Set ℂ := connectedComponentIn (Ω \ K) x
  have hfrK : frontier C ⊆ K := fun z hz ↦ by
    have hzΩ : z ∈ Ω := hclΩ (frontier_subset_closure hz)
    have hnot : z ∉ Ω \ K := frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK) x hz
    exact by_contra fun hzK ↦ hnot ⟨hzΩ, hzK⟩
  obtain ⟨M₀, hM₀⟩ :=
    hcpt.exists_bound_of_continuousOn (continuous_id.sub continuous_const).continuousOn
  set M : ℝ := max 0 M₀
  have hM_nonneg : 0 ≤ M := le_max_left 0 M₀
  have hfU : DifferentiableOn ℂ (fun z : ℂ ↦ (z - x)⁻¹) {x}ᶜ :=
    (differentiableOn_id.sub (differentiableOn_const x)).inv fun z hz ↦ sub_ne_zero.mpr hz
  obtain ⟨g, hgΩ, hgK⟩ := happrox {x}ᶜ isOpen_compl_singleton
    (fun z hz hzx ↦ hxK (hzx ▸ hz)) _ hfU (M + 1)⁻¹ (by positivity)
  set h : ℂ → ℂ := fun z ↦ 1 - (z - x) * g z
  have hhΩ : DifferentiableOn ℂ h Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub (differentiableOn_const x)).mul hgΩ)
  have hhC : DiffContOnCl ℂ h C :=
    ⟨hhΩ.mono ((connectedComponentIn_subset _ _).trans sdiff_subset), hhΩ.continuousOn.mono hclΩ⟩
  have hfr_le : ∀ z ∈ frontier C, ‖h z‖ ≤ M / (M + 1) := fun z hz ↦ by
    have hzK : z ∈ K := hfrK hz
    have hzx : z - x ≠ 0 := sub_ne_zero.mpr fun h0 ↦ hxK (h0 ▸ hzK)
    have hrew : h z = (z - x) * ((z - x)⁻¹ - g z) := by
      simp only [h, mul_sub, mul_inv_cancel₀ hzx]
    rw [hrew, norm_mul, div_eq_mul_inv]
    exact mul_le_mul ((hM₀ z (frontier_subset_closure hz)).trans (le_max_right 0 M₀))
      (hgK z hzK).le (norm_nonneg _) hM_nonneg
  have hx_le := norm_le_of_forall_mem_frontier_norm_le (hcpt.isBounded.subset subset_closure)
    hhC hfr_le (subset_closure (mem_connectedComponentIn ⟨hxΩ, hxK⟩))
  have hx_eq : ‖h x‖ = 1 := by simp [h]
  have hlt : M / (M + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-- **Runge's approximation theorem.** Every ambient-neighborhood holomorphic function is uniformly
approximable on `K` by functions holomorphic on `Ω` if and only if `(Ω, K)` is a compact Runge pair
(Rainer, Theorem 11.1). -/
theorem _root_.IsOpen.isRungeCompactPair_iff_approximation {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
          ∀ z ∈ K, ‖f z - g z‖ < ε :=
  ⟨fun hRunge _ hU hKU _ hf _ hε ↦
    hRunge.exists_differentiableOn_norm_sub_lt (hU.interior_eq.symm ▸ hKU) hf hε,
    fun happrox ↦ ⟨hΩ, hK, hKΩ,
      isFilledIn_of_forall_exists_differentiableOn_norm_sub_lt hΩ hK.isClosed happrox⟩⟩

end Equivalence

section PointSeparation

/-- Adjoining a point `a ∈ Ω` to a compact Runge pair `(Ω, K)` preserves `IsRungeCompactPair`. -/
theorem IsRungeCompactPair.insert {Ω K : Set ℂ} (hRunge : IsRungeCompactPair Ω K) {a : ℂ}
    (ha : a ∈ Ω) : IsRungeCompactPair Ω (Insert.insert a K) := by
  refine ⟨hRunge.isOpen, hRunge.isCompact.insert a, insert_subset ha hRunge.subset, ?_⟩
  rw [isFilledIn_iff]
  rintro x ⟨hxΩ, hxins⟩ ⟨hcpt, hclΩ⟩
  have hxa : x ≠ a := fun h ↦ hxins (h ▸ mem_insert a K)
  have hxK : x ∉ K := fun h ↦ hxins (mem_insert_of_mem a h)
  have hW : IsOpen (Ω \ K) := hRunge.isOpen.sdiff hRunge.isCompact.isClosed
  have hpunc : IsPreconnected (connectedComponentIn (Ω \ K) x \ {a}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank (E := ℂ)
      (by simp [Complex.rank_real_complex]) hW.connectedComponentIn
      isPreconnected_connectedComponentIn isClosed_singleton (finite_singleton a).isDiscrete
  have hcomp : connectedComponentIn (Ω \ Insert.insert a K) x =
      connectedComponentIn (Ω \ K) x \ {a} := by
    have heq : Ω \ Insert.insert a K = (Ω \ K) \ {a} := by
      ext z
      simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff]
      tauto
    rw [heq]
    exact Subset.antisymm
      (fun z hz ↦ ⟨connectedComponentIn_mono x sdiff_subset hz,
        (connectedComponentIn_subset _ _ hz).2⟩)
      (hpunc.subset_connectedComponentIn ⟨mem_connectedComponentIn ⟨hxΩ, hxK⟩, hxa⟩
        (sdiff_subset_sdiff (connectedComponentIn_subset _ _) subset_rfl))
  have hcl_sub : closure (connectedComponentIn (Ω \ K) x) ⊆
      closure (connectedComponentIn (Ω \ Insert.insert a K) x) ∪ {a} := by
    calc closure (connectedComponentIn (Ω \ K) x)
        ⊆ closure ((connectedComponentIn (Ω \ K) x \ {a}) ∪ {a}) :=
          closure_mono fun z hz ↦ (eq_or_ne z a).elim Or.inr fun hza ↦ Or.inl ⟨hz, hza⟩
      _ = closure (connectedComponentIn (Ω \ Insert.insert a K) x) ∪ {a} := by
          rw [closure_union, closure_singleton, hcomp]
  exact isFilledIn_iff.mp hRunge.isFilledIn x ⟨hxΩ, hxK⟩
    ⟨(hcpt.union isCompact_singleton).of_isClosed_subset isClosed_closure hcl_sub,
      hcl_sub.trans (union_subset hclΩ (singleton_subset_iff.mpr ha))⟩

/-- Any point `a` outside both `Ω` and `K` is separated from `K` by `({a}).indicator (fun _ ↦ 2)`,
which vanishes (hence is holomorphic) on `Ω` and has modulus `2 > 1` at `a`. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_of_notMem {Ω K : Set ℂ} {a : ℂ}
    (haΩ : a ∉ Ω) (haK : a ∉ K) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ K, ‖g z‖ < 1) ∧ 1 < ‖g a‖ :=
  ⟨({a} : Set ℂ).indicator fun _ ↦ (2 : ℂ),
    (differentiableOn_const 0).congr fun _ hz ↦
      indicator_of_notMem (s := {a}) (by rintro rfl; exact haΩ hz) _,
    fun _ hz ↦ by
      rw [indicator_of_notMem (s := {a}) (by rintro rfl; exact haK hz)]
      simp,
    by rw [indicator_of_mem (mem_singleton a)]; norm_num⟩

/-- **Point separation off a compact Runge pair.** If `(Ω, K)` is a compact Runge pair and
`a ∉ K`, there is a function `g` holomorphic on `Ω` with `‖g z‖ < 1` for all `z ∈ K` and
`1 < ‖g a‖`. -/
theorem IsRungeCompactPair.exists_differentiableOn_norm_lt_one_lt {Ω K : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) {a : ℂ} (ha : a ∉ K) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ K, ‖g z‖ < 1) ∧ 1 < ‖g a‖ := by
  by_cases haΩ : a ∈ Ω
  · obtain ⟨t, ht, hball⟩ :=
      Metric.isOpen_iff.mp hRunge.isCompact.isClosed.isOpen_compl a ha
    set r : ℝ := t / 2
    have hr : 0 < r := half_pos ht
    have hcbK : Disjoint (closedBall a r) K :=
      disjoint_left.mpr fun z hzb hzK ↦ hball (closedBall_subset_ball (half_lt_self ht) hzb) hzK
    set U : Set ℂ := ball a r ∪ (closedBall a r)ᶜ
    have hU : IsOpen U := isOpen_ball.union isClosed_closedBall.isOpen_compl
    have hinsU : Insert.insert a K ⊆ U :=
      insert_subset (Or.inl (mem_ball_self hr))
        fun z hz ↦ Or.inr (disjoint_right.mp hcbK hz)
    set f : ℂ → ℂ := (ball a r).indicator fun _ ↦ (2 : ℂ)
    have hfU : DifferentiableOn ℂ f U := fun z hz ↦ hz.elim
      (fun hzb ↦ ((differentiableAt_const (2 : ℂ)).congr_of_eventuallyEq
        (eventually_of_mem (isOpen_ball.mem_nhds hzb) fun _ hw ↦
          indicator_of_mem hw _)).differentiableWithinAt)
      fun hzc ↦ ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
        (eventually_of_mem (isClosed_closedBall.isOpen_compl.mem_nhds hzc) fun _ hw ↦
          indicator_of_notMem (fun hwb ↦ hw (ball_subset_closedBall hwb))
            _)).differentiableWithinAt
    obtain ⟨g, hgΩ, hg_approx⟩ :=
      (hRunge.insert haΩ).exists_differentiableOn_norm_sub_lt (hU.interior_eq.symm ▸ hinsU) hfU
        (half_pos one_pos)
    refine ⟨g, hgΩ, fun z hz ↦ ?_, ?_⟩
    · have hfz : f z = 0 :=
        indicator_of_notMem (fun hzb ↦ disjoint_left.mp hcbK (ball_subset_closedBall hzb) hz) _
      have hgz := hg_approx z (mem_insert_of_mem a hz)
      rw [hfz, zero_sub, norm_neg] at hgz
      linarith
    · have hfa : f a = 2 := indicator_of_mem (mem_ball_self hr) _
      have hga := hg_approx a (mem_insert a K)
      rw [hfa] at hga
      have htri : (2 : ℝ) - ‖g a‖ ≤ ‖(2 : ℂ) - g a‖ := by simpa using norm_sub_norm_le (2 : ℂ) (g a)
      linarith
  · exact exists_differentiableOn_norm_lt_one_lt_of_notMem_of_notMem haΩ ha

end PointSeparation

end TauCeti

end
