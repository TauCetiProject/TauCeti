/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SuccessiveMinima

import TauCeti.LinearAlgebra.Dimension.Submodule

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
  obtain ⟨B, hcoe, hB⟩ := exists_convexBody_eq_approxBody hLinf c hQ
  refine ⟨B, hcoe, hB, ?_⟩
  rw [hcoe, one_smul, approxSpan_eq_span, approxDomain_eq S₀ L c hQ.le]

/-- **The minima below the rank of an approximation domain are at most one**: if `l` is less
than the rank of the span of `approxDomain S₀ L c Q`, then its `l`-th successive minimum over `K`
is at most `1`, since the domain holds `l + 1` linearly independent points. This holds for every
real level and all forms. -/
theorem successiveMinimum_le_one_of_lt_finrank_approxSpan {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {l : ℕ} (hl : l < finrank K (approxSpan S₀ L c Q)) :
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤ 1 := by
  rw [approxSpan_eq_span] at hl
  obtain ⟨x, hx, hxD⟩ := Submodule.le_finrank_span_iff_exists_linearIndependent.1 hl
  refine Submodule.successiveMinimum_le one_pos hx (fun i ↦ approxDomain_subset_approxModule
    (hxD i)) fun i ↦ ?_
  rw [one_smul, mixedEmbedding_mem_approxBody_iff]
  exact (mem_approxDomain.1 (hxD i)).1

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

end TauCeti.NumberField
