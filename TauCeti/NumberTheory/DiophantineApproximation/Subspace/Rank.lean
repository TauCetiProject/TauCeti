/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SuccessiveMinima

import TauCeti.Algebra.Order.BigOperators.Min

/-!
# The rank of an approximation domain

The rank of the span of an approximation domain is the number of its successive minima over
`K` that are at most one. Any family realizing those minima spans the domain with its first
`r` vectors, where `r` is this rank. These statements let arguments about the dimensions and
spans of domains use the geometry of their successive minima without choosing a new basis.

Equivalently, below the ambient dimension a successive minimum is at most one exactly when its
index is below the rank (`TauCeti.NumberField.successiveMinimum_approx_le_one_iff`); these minima
are positive (`TauCeti.NumberField.successiveMinimum_approx_pos`) and nondecreasing
(`TauCeti.NumberField.monotoneOn_successiveMinimum_approx`).

The threshold is non-strict: vectors on the boundary of the closed approximation body belong
to the domain. Only indices below the ambient dimension are counted, since later successive
minima have junk value zero. The rank and spanning statements allow rank zero and full rank.

When the domain spans a nonzero proper subspace, of rank `R`, the minima beyond the rank contain
a large jump: some `k` with `R ≤ k < #ι` has `(μ (k - 1) / μ k) ^ (#ι - R) ≤ (μ (#ι - 1))⁻¹`
(`TauCeti.NumberField.exists_div_pow_le_inv`). This chooses the splitting index `k` at which the
Plücker vectors of the first `k` minimal vectors are moved into an exterior power, where the jump
`μ k / μ (k - 1)` makes the last minimum of the new domain large.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), Definition 7.5.11,
  Lemma 7.5.12 and (7.41).
-/

public section

open Module NumberField NumberField.mixedEmbedding Set
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- For forms independent at every infinite place and a level `Q > 0`, the approximation body
`approxBody L c Q` is a convex body with `0` in its interior, and the span of the approximation
domain is spanned by the lattice vectors of `approxModule S₀ L c Q` in that body. This packages
the approximation body for the convex-body successive-minima API. -/
theorem exists_convexBody_approxSpan {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ∃ B : ConvexBody (ι → mixedSpace K),
      (B : Set (ι → mixedSpace K)) = approxBody L c Q ∧
      0 ∈ interior (B : Set (ι → mixedSpace K)) ∧
      approxSpan S₀ L c Q = Submodule.span K {x | x ∈ approxModule S₀ L c Q ∧
        (fun j ↦ mixedEmbedding K (x j)) ∈ (1 : ℝ) • (B : Set (ι → mixedSpace K))} := by
  let B : ConvexBody (ι → mixedSpace K) :=
    ⟨approxBody L c Q, convex_approxBody L c Q, isCompact_approxBody hLinf c Q,
      ⟨0, mem_of_mem_nhds (approxBody_mem_nhds_zero L c hQ)⟩⟩
  have hcoe : (B : Set (ι → mixedSpace K)) = approxBody L c Q :=
    ConvexBody.coe_mk _ _ _ _
  refine ⟨B, hcoe, ?_, ?_⟩
  · rw [hcoe]
    exact mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)
  · rw [hcoe, one_smul, approxSpan_eq_span, approxDomain_eq S₀ L c hQ.le]

open scoped Classical in
/-- The rank of an approximation domain of positive level is the number of its successive
minima over `K` at most one, including minima equal to one. -/
theorem finrank_approxSpan {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    finrank K (approxSpan S₀ L c Q) =
      (Finset.univ.filter fun l : Fin (Fintype.card ι) ↦
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤ 1).card := by
  classical
  let _ := discreteTopology_mixedImage_approxModule hLfin c Q
  let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
  obtain ⟨B, hcoe, hB, hspan⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLinf c hQ
  rw [hspan, ← hcoe]
  exact Submodule.finrank_span_setOf_mem (Λ := approxModule S₀ L c Q) hB
    (t := (1 : ℝ)) zero_lt_one

/-- Below `#ι`, the successive minima over `K` of an approximation domain of positive level are
positive. -/
theorem successiveMinimum_approx_pos {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) {l : ℕ} (hl : l < Fintype.card ι) :
    0 < (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l := by
  let _ := discreteTopology_mixedImage_approxModule hLfin c Q
  let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
  obtain ⟨B, hcoe, hB, -⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLinf c hQ
  rw [← hcoe]
  exact Submodule.successiveMinimum_pos hB hl

/-- Below `#ι`, the successive minima over `K` of an approximation domain of positive level are
nondecreasing. -/
theorem monotoneOn_successiveMinimum_approx {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    MonotoneOn ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q))
      (Iio (Fintype.card ι)) := by
  let _ := discreteTopology_mixedImage_approxModule hLfin c Q
  let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
  obtain ⟨B, hcoe, hB, -⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLinf c hQ
  rw [← hcoe]
  exact Submodule.monotoneOn_successiveMinimum hB

/-- Below `#ι`, a successive minimum over `K` of an approximation domain of positive level is at
most one exactly when its index is below the rank of the domain. -/
theorem successiveMinimum_approx_le_one_iff {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) {l : ℕ} (hl : l < Fintype.card ι) :
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤ 1 ↔
      l < finrank K (approxSpan S₀ L c Q) := by
  let _ := discreteTopology_mixedImage_approxModule hLfin c Q
  let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
  obtain ⟨B, hcoe, hB, hspan⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLinf c hQ
  rw [hspan, ← hcoe]
  exact Submodule.successiveMinimum_le_iff_lt_finrank_span hB hl one_pos

open scoped Classical in
/-- A family realizing the successive minima spans an approximation domain with its first
`r` vectors, where `r` is the rank of the domain. -/
theorem approxSpan_eq_span_image {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q)
    {x : Fin (Fintype.card ι) → ι → K} (hx : LinearIndependent K x)
    (hxΛ : ∀ l, x l ∈ approxModule S₀ L c Q)
    (hxB : ∀ l : Fin (Fintype.card ι), (fun j ↦ mixedEmbedding K (x l j)) ∈
      (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l • approxBody L c Q) :
    approxSpan S₀ L c Q =
      Submodule.span K (x '' {l | l.val < finrank K (approxSpan S₀ L c Q)}) := by
  classical
  let _ := discreteTopology_mixedImage_approxModule hLfin c Q
  let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
  obtain ⟨B, hcoe, hB, hspan⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLinf c hQ
  rw [← hcoe] at hxB
  rw [hspan]
  exact Submodule.span_setOf_mem_eq_span_image hB (t := (1 : ℝ)) zero_lt_one hx hxΛ hxB

/-- **A jump among the successive minima beyond the rank** (Bombieri–Gubler (7.41)). Let the
approximation domain at a positive level span a nonzero proper subspace, of rank `R`, and let
`μ` be its successive minima over `K`. Then some `k` with `R ≤ k < #ι` has
`(μ (k - 1) / μ k) ^ (#ι - R) ≤ (μ (#ι - 1))⁻¹`.

`R ≥ 1` is needed: it gives `μ (R - 1) ≤ 1`, which bounds the product of the ratios
`μ (k - 1) / μ k` over `R ≤ k < #ι` by `(μ (#ι - 1))⁻¹`. -/
theorem exists_div_pow_le_inv {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q)
    (hbot : approxSpan S₀ L c Q ≠ ⊥) (htop : approxSpan S₀ L c Q ≠ ⊤) :
    ∃ k ∈ Finset.Ico (finrank K (approxSpan S₀ L c Q)) (Fintype.card ι),
      ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^
          (Fintype.card ι - finrank K (approxSpan S₀ L c Q)) ≤
        ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
          (Fintype.card ι - 1))⁻¹ := by
  set R := finrank K (approxSpan S₀ L c Q)
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  have hR0 : 0 < R := Nat.pos_of_ne_zero fun h ↦ hbot (Submodule.finrank_eq_zero.1 h)
  have hRn : R < Fintype.card ι :=
    (Submodule.finrank_lt htop).trans_eq (Module.finrank_fintype_fun_eq_card K)
  have hpos (l : ℕ) (hl : l < Fintype.card ι) : 0 < μ l :=
    successiveMinimum_approx_pos hLinf hLfin c hQ hl
  -- The rank counts the minima at most `1`, so the `(R - 1)`-th minimum is at most `1`.
  have hle : μ (R - 1) ≤ 1 :=
    (successiveMinimum_approx_le_one_iff hLinf hLfin c hQ (by omega)).2 (by omega)
  -- Some ratio `μ j / μ (j + 1)` with `R - 1 ≤ j < #ι - 1` is at most the geometric mean.
  obtain ⟨j, hj, hjle⟩ := TauCeti.exists_mem_Ico_div_pow_le_div (f := μ) (m := R - 1)
    (n := Fintype.card ι - 1) (by omega) fun i hi ↦ hpos i (by grind)
  rw [Finset.mem_Ico] at hj
  have hexp : Fintype.card ι - 1 - (R - 1) = Fintype.card ι - R := by omega
  refine ⟨j + 1, Finset.mem_Ico.2 ⟨by omega, by omega⟩, ?_⟩
  rw [Nat.add_sub_cancel, ← hexp, ← one_div]
  exact hjle.trans (div_le_div_of_nonneg_right hle (hpos _ (by omega)).le)

end TauCeti.NumberField
