/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Fredholm.Shift
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# Range of the Fredholm index

This file determines the values taken by the Fredholm index on `{T : E →L[𝕜] F // T.IsFredholm}`
in finite and infinite dimensions (complementing the mixed-dimension emptiness results in
`TauCeti.Analysis.Fredholm.Basic`):

* **Finite-dimensional spaces** (`ContinuousLinearMap.range_index_isFredholm_of_finiteDimensional`):
  between finite-dimensional topological modules over a nontrivially normed field whenever the
  Fredholm locus is nonempty (for instance when `F` is `T₁`, by
  `ContinuousLinearMap.instNonemptyIsFredholmOfFiniteDimensional` in
  `TauCeti.Analysis.Fredholm.Zero`), the image of the index on the Fredholm locus is the singleton
  `{(finrank 𝕜 E : ℤ) - finrank 𝕜 F}`.
* **Infinite-dimensional Hilbert spaces**
  (`ContinuousLinearMap.exists_isFredholm_and_index_eq_self`,
  `ContinuousLinearMap.IsFredholm.exists_isFredholm_and_index_eq`,
  `ContinuousLinearMap.index_isFredholm_surjective`,
  `ContinuousLinearMap.range_index_isFredholm_of_not_finiteDimensional`,
  `ContinuousLinearEquiv.exists_isFredholm_and_index_eq`): if `E` is an infinite-dimensional real or
  complex Hilbert space (with no separability assumption), every integer `n : ℤ` is the index of a
  Fredholm endomorphism of `E`, and hence of a Fredholm map `E →L[𝕜] F` whenever `F` is a Hausdorff
  topological vector space with nonempty Fredholm locus `{T : E →L[𝕜] F // T.IsFredholm}` (or along
  any continuous linear equivalence `E ≃L[𝕜] F` without topological-group or separation hypotheses
  on `F`).

The infinite-dimensional construction orthonormalizes a countably infinite linearly independent
sequence in `E` via Gram–Schmidt, embeds `ℓ²(ℕ, 𝕜)` isometrically into `E`, and conjugates the
product of a unilateral shift power from `TauCeti.Analysis.Fredholm.Shift` with the identity on the
orthogonal complement across `LinearIsometry.prodOrthogonalRangeEquiv`.

## Main declarations

* `ContinuousLinearMap.range_index_isFredholm_of_finiteDimensional`: in finite dimensions, the
  range of the Fredholm index on a nonempty Fredholm locus is `{(finrank 𝕜 E : ℤ) - finrank 𝕜 F}`.
* `ContinuousLinearMap.exists_isFredholm_and_index_eq_self`: every integer is a Fredholm index on an
  infinite-dimensional Hilbert space.
* `ContinuousLinearMap.IsFredholm.exists_isFredholm_and_index_eq`,
  `ContinuousLinearMap.index_isFredholm_surjective`,
  `ContinuousLinearMap.range_index_isFredholm_of_not_finiteDimensional`: every integer is realized
  on any nonempty Fredholm locus out of an infinite-dimensional Hilbert space into a Hausdorff
  topological vector space.
* `ContinuousLinearEquiv.exists_isFredholm_and_index_eq`: every integer is a Fredholm index along a
  continuous linear equivalence out of an infinite-dimensional Hilbert space.

## References

* D. S. Freed, *The Atiyah–Singer index theorem*, Bull. Amer. Math. Soc. **58** (2021), 517–566,
  arXiv:2107.03557, display (3.13).
* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter III, §7, Example 7.5 and Theorem 7.8.
-/

public section

open Module
open scoped ENNReal InnerProductSpace lp

section FiniteDimensional

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [FiniteDimensional 𝕜 F]

/-- Between finite-dimensional spaces with nonempty Fredholm locus (in particular whenever `F` is
`T₁`), the range of the index on the Fredholm locus is the singleton
`{(finrank 𝕜 E : ℤ) - finrank 𝕜 F}`. -/
@[simp]
theorem range_index_isFredholm_of_finiteDimensional [Nonempty {T : E →L[𝕜] F // T.IsFredholm}] :
    Set.range (fun T : {T : E →L[𝕜] F // T.IsFredholm} ↦ T.val.index) =
      {(finrank 𝕜 E : ℤ) - finrank 𝕜 F} := by
  simp [index_eq_of_finiteDimensional]

end ContinuousLinearMap

end FiniteDimensional

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace ContinuousLinearMap

/-- On an infinite-dimensional real or complex Hilbert space `E`, every integer is the index of a
Fredholm endomorphism `E →L[𝕜] E`. No separability hypothesis is needed. -/
theorem exists_isFredholm_and_index_eq_self (hE : ¬ FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : E →L[𝕜] E, T.IsFredholm ∧ T.index = n := by
  -- Orthonormalize a countably infinite linearly independent sequence via Gram–Schmidt, embed
  -- `ℓ²(ℕ, 𝕜)` into `E`, and conjugate `S.prodMap id` across `φ.prodOrthogonalRangeEquiv`.
  have hinf : (Basis.ofVectorSpaceIndex 𝕜 E).Infinite :=
    fun hfin ↦ hE (FiniteDimensional.of_finite_basis (Basis.ofVectorSpace 𝕜 E) hfin)
  let e := hinf.natEmbedding (Basis.ofVectorSpaceIndex 𝕜 E)
  have hv : Orthonormal 𝕜
      (InnerProductSpace.gramSchmidtNormed 𝕜 fun k ↦ Basis.ofVectorSpace 𝕜 E (e k)) :=
    InnerProductSpace.gramSchmidtNormed_orthonormal
      ((Basis.ofVectorSpace 𝕜 E).linearIndependent.comp _ e.injective)
  let φ : ℓ²(ℕ, 𝕜) →ₗᵢ[𝕜] E := hv.orthogonalFamily.linearIsometry
  let eE := φ.prodOrthogonalRangeEquiv
  obtain ⟨S, hS, hind⟩ := lp.exists_isFredholm_and_index_eq 𝕜 2 n
  let T : E →L[𝕜] E :=
    (eE.toContinuousLinearMap.comp (S.prodMap (.id 𝕜 _))).comp eE.symm.toContinuousLinearMap
  refine ⟨T, ((hS.prodMap .id).equiv_comp eE).comp_equiv eE.symm, ?_⟩
  have := hS.finite_ker
  have := hS.finite_coker
  have := (IsFredholm.id (𝕜 := 𝕜) (E := (LinearMap.range φ.toLinearMap)ᗮ)).finite_ker
  have := (IsFredholm.id (𝕜 := 𝕜) (E := (LinearMap.range φ.toLinearMap)ᗮ)).finite_coker
  simp [T, hind]

section Nonempty

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F] [T2Space F]

/-- Given any Fredholm operator `T₀ : E →L[𝕜] F` out of an infinite-dimensional Hilbert space `E`
into a Hausdorff topological vector space `F`, every integer `n : ℤ` is the index of a Fredholm
operator `E →L[𝕜] F`. -/
theorem IsFredholm.exists_isFredholm_and_index_eq {T₀ : E →L[𝕜] F} (hT₀ : T₀.IsFredholm)
    (hE : ¬ FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : E →L[𝕜] F, T.IsFredholm ∧ T.index = n := by
  obtain ⟨S, hS, hind⟩ := exists_isFredholm_and_index_eq_self hE (n - T₀.index)
  refine ⟨T₀.comp S, hT₀.comp hS, ?_⟩
  have hcomp := hT₀.index_comp hS
  rw [← index_def, ← index_def, ← index_def, hind] at hcomp
  omega

/-- Out of an infinite-dimensional Hilbert space `E` into a Hausdorff topological vector space `F`
with nonempty Fredholm locus (in particular for `F = E`), the Fredholm index surjects onto `ℤ`. -/
theorem index_isFredholm_surjective [Nonempty {T : E →L[𝕜] F // T.IsFredholm}]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    Function.Surjective (fun T : {T : E →L[𝕜] F // T.IsFredholm} ↦ T.val.index) := fun n ↦ by
  obtain ⟨⟨T₀, hT₀⟩⟩ := ‹Nonempty {T : E →L[𝕜] F // T.IsFredholm}›
  obtain ⟨T, hT, hind⟩ := hT₀.exists_isFredholm_and_index_eq hE n
  exact ⟨⟨T, hT⟩, hind⟩

/-- Out of an infinite-dimensional Hilbert space `E` into a Hausdorff topological vector space `F`
with nonempty Fredholm locus (in particular for `F = E`), the range of the index on the Fredholm
locus is all of `ℤ`. -/
@[simp]
theorem range_index_isFredholm_of_not_finiteDimensional [Nonempty {T : E →L[𝕜] F // T.IsFredholm}]
    (hE : ¬ FiniteDimensional 𝕜 E) :
    Set.range (fun T : {T : E →L[𝕜] F // T.IsFredholm} ↦ T.val.index) = Set.univ :=
  Set.range_eq_univ.2 (index_isFredholm_surjective hE)

end Nonempty

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

/-- If `E` is an infinite-dimensional Hilbert space and `e : E ≃L[𝕜] F` is a continuous linear
equivalence, every integer is the index of a Fredholm operator `E →L[𝕜] F`. -/
theorem exists_isFredholm_and_index_eq (e : E ≃L[𝕜] F) (hE : ¬ FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : E →L[𝕜] F, T.IsFredholm ∧ T.index = n := by
  obtain ⟨T₀, hT₀, hind₀⟩ := ContinuousLinearMap.exists_isFredholm_and_index_eq_self hE n
  exact ⟨(e : E →L[𝕜] F).comp T₀, hT₀.equiv_comp e, (T₀.index_equiv_comp e).trans hind₀⟩

end ContinuousLinearEquiv

end Hilbert
