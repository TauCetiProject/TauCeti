/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SuccessiveMinima

/-!
# The rank of an approximation domain

The rank of the span of an approximation domain is the number of its successive minima over
`K` that are at most one. Any family realizing those minima spans the domain with its first
`r` vectors, where `r` is this rank. These statements let arguments about the dimensions and
spans of domains use the geometry of their successive minima without choosing a new basis.

The threshold is non-strict: vectors on the boundary of the closed approximation body belong
to the domain. Only indices below the ambient dimension are counted, since later successive
minima have junk value zero. Both statements allow rank zero and full rank.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), Definition 7.5.11
  and Lemma 7.5.12.
-/

public section

open Module NumberField NumberField.mixedEmbedding Set
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- Bundle the approximation body and its span identity for the two applications of the
convex-body successive-minima API below. -/
private theorem exists_convexBody_approxSpan {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
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
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
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

open scoped Classical in
/-- A family realizing the successive minima spans an approximation domain with its first
`r` vectors, where `r` is the rank of the domain. -/
theorem approxSpan_eq_span_image {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
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

end TauCeti.NumberField
