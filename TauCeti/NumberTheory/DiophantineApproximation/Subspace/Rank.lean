/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.SuccessiveMinima.Basic

import TauCeti.Algebra.Order.BigOperators.Min

/-!
# The rank of an approximation domain

In one direction no hypothesis is needed: for all forms and every real level, every successive
minimum over `K` of an approximation domain below the rank of its span is at most one. For a
positive level and forms linearly independent at the infinite places and at the places of `S₀`,
the converse holds as well: the rank of the span is exactly the number of minima at most one, and
any family realizing the minima (one exists by
`TauCeti.NumberField.exists_linearIndependent_mem_smul_successiveMinimum_approx`) spans the domain
with its first `r` vectors, where `r` is this rank. These statements let arguments about the
dimensions and spans of domains use the geometry of their successive minima without choosing a
new basis.

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
Plücker vectors of the `p`-subfamilies of the corrected family that meet the first `k` indices lie
in an exterior-power approximation domain, where the jump `μ k / μ (k - 1)` makes the last
minimum large.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), Definition 7.5.11,
  Lemma 7.5.12 and (7.41).
-/

public section

open Module NumberField NumberField.mixedEmbedding Set
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

private theorem approxSpan_eq_span_mixedEmbedding {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    approxSpan S₀ L c Q = Submodule.span K {x | x ∈ approxModule S₀ L c Q ∧
      (fun j ↦ mixedEmbedding K (x j)) ∈ (1 : ℝ) • approxBody L c Q} := by
  rw [one_smul, approxSpan_eq_span, approxDomain_eq S₀ L c hQ]

/-- **The minima below the rank of an approximation domain are at most one**: if `l` is less
than the rank of the span of `approxDomain S₀ L c Q`, then its `l`-th successive minimum over `K`
is at most `1`, since the domain holds `l + 1` linearly independent points. This holds for every
real level and all forms. -/
theorem successiveMinimum_le_one_of_lt_finrank_approxSpan {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {l : ℕ} (hl : l < finrank K (approxSpan S₀ L c Q)) :
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤ 1 := by
  rw [approxSpan_eq_span] at hl
  refine Submodule.successiveMinimum_le_of_lt_finrank_span one_pos
    approxDomain_subset_approxModule (fun x hx ↦ ?_) hl
  rw [one_smul, mixedEmbedding_mem_approxBody_iff]
  exact (mem_approxDomain.1 hx).1

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
  obtain ⟨B, hcoe, hB⟩ := exists_convexBody_eq_approxBody hLinf c hQ
  rw [approxSpan_eq_span_mixedEmbedding c hQ.le, ← hcoe]
  exact Submodule.finrank_span_setOf_mem (Λ := approxModule S₀ L c Q) hB
    (t := (1 : ℝ)) zero_lt_one

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
  obtain ⟨B, hcoe, hB⟩ := exists_convexBody_eq_approxBody hLinf c hQ
  simpa only [hcoe] using (approxModule S₀ L c Q).monotoneOn_successiveMinimum hB

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
  obtain ⟨B, hcoe, hB⟩ := exists_convexBody_eq_approxBody hLinf c hQ
  rw [approxSpan_eq_span_mixedEmbedding c hQ.le, ← hcoe]
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
  obtain ⟨B, hcoe, hB⟩ := exists_convexBody_eq_approxBody hLinf c hQ
  rw [← hcoe] at hxB
  rw [approxSpan_eq_span_mixedEmbedding c hQ.le, ← hcoe]
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
