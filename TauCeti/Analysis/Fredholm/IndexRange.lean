/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Normed.Lp.Shift
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Range of the Fredholm index

This file determines the values taken by the Fredholm index on `{T : E →L[𝕜] F // T.IsFredholm}`
across finite, mixed, and infinite dimensions:

* **Dimension invariance** (`ContinuousLinearMap.IsFredholm.finiteDimensional_iff`): a Fredholm
  operator between topological modules over a nontrivially normed field has finite-dimensional
  domain if and only if it has finite-dimensional codomain. Consequently, when one space is
  finite-dimensional and the other is infinite-dimensional, the Fredholm locus is empty
  (`ContinuousLinearMap.isEmpty_fredholm_of_finiteDimensional_left`,
  `ContinuousLinearMap.isEmpty_fredholm_of_finiteDimensional_right`).
* **Finite-dimensional spaces** (`ContinuousLinearMap.range_index_fredholm_of_finiteDimensional`):
  over a complete nontrivially normed field with Hausdorff target, every continuous linear map is
  Fredholm and the image of the index on the Fredholm locus is the singleton
  `{(finrank 𝕜 E : ℤ) - finrank 𝕜 F}`.
* **Infinite-dimensional Hilbert spaces**
  (`ContinuousLinearMap.exists_isFredholm_and_index_eq_self`,
  `ContinuousLinearEquiv.exists_isFredholm_and_index_eq`,
  `LinearIsometryEquiv.exists_isFredholm_and_index_eq`): if `E` is an infinite-dimensional real or
  complex Hilbert space (with no separability assumption), every integer `n : ℤ` is the index of a
  Fredholm endomorphism of `E`, and hence of a Fredholm map `E →L[𝕜] F` along any continuous linear
  equivalence `E ≃L[𝕜] F` (in particular any unitary equivalence `E ≃ₗᵢ[𝕜] F`).

The infinite-dimensional construction orthonormalizes a countably infinite linearly independent
sequence in `E` via Gram–Schmidt, identifies its closed span `K` isometrically with `ℓ²(ℕ, 𝕜)`,
transports the powers of the unilateral left and right shifts from
`TauCeti.Analysis.Normed.Lp.Shift` to `K`, and extends them by the identity on `Kᗮ` across the
orthogonal decomposition `E ≃L[𝕜] K × Kᗮ`.

## Main declarations

* `ContinuousLinearMap.IsFredholm.finiteDimensional_iff`: Fredholm operators preserve and reflect
  finite dimensionality.
* `ContinuousLinearMap.range_index_fredholm_of_finiteDimensional`: in finite dimensions, the range
  of the Fredholm index is `{(finrank 𝕜 E : ℤ) - finrank 𝕜 F}`.
* `ContinuousLinearMap.exists_isFredholm_and_index_eq_self`: every integer is a Fredholm index on an
  infinite-dimensional Hilbert space.
* `ContinuousLinearEquiv.exists_isFredholm_and_index_eq`,
  `LinearIsometryEquiv.exists_isFredholm_and_index_eq`: every integer is a Fredholm index between
  continuously linearly (or unitarily) equivalent spaces when the source is an infinite-dimensional
  Hilbert space.

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
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A Fredholm operator has finite-dimensional domain if and only if it has finite-dimensional
codomain. -/
theorem IsFredholm.finiteDimensional_iff {T : E →L[𝕜] F} (hT : T.IsFredholm) :
    FiniteDimensional 𝕜 E ↔ FiniteDimensional 𝕜 F := by
  have := hT.finite_ker
  have := hT.finite_coker
  refine ⟨fun _ ↦ Module.Finite.of_submodule_quotient T.range, fun _ ↦ ?_⟩
  have : FiniteDimensional 𝕜 (E ⧸ T.ker) := T.quotKerEquivRange.symm.finiteDimensional
  exact Module.Finite.of_submodule_quotient T.ker

/-- No Fredholm operator exists from a finite-dimensional space to an infinite-dimensional space. -/
theorem not_exists_isFredholm_of_finiteDimensional_left [FiniteDimensional 𝕜 E]
    (hF : ¬ FiniteDimensional 𝕜 F) : ¬ ∃ T : E →L[𝕜] F, T.IsFredholm :=
  fun ⟨_, hT⟩ ↦ hF (hT.finiteDimensional_iff.1 inferInstance)

/-- No Fredholm operator exists from an infinite-dimensional space to a finite-dimensional space. -/
theorem not_exists_isFredholm_of_finiteDimensional_right (hE : ¬ FiniteDimensional 𝕜 E)
    [FiniteDimensional 𝕜 F] : ¬ ∃ T : E →L[𝕜] F, T.IsFredholm :=
  fun ⟨_, hT⟩ ↦ hE (hT.finiteDimensional_iff.2 inferInstance)

/-- The Fredholm locus is empty when the domain is finite-dimensional and the codomain is
infinite-dimensional. -/
theorem isEmpty_fredholm_of_finiteDimensional_left [FiniteDimensional 𝕜 E]
    (hF : ¬ FiniteDimensional 𝕜 F) : IsEmpty {T : E →L[𝕜] F // T.IsFredholm} :=
  ⟨fun T ↦ not_exists_isFredholm_of_finiteDimensional_left hF ⟨T.val, T.property⟩⟩

/-- The Fredholm locus is empty when the domain is infinite-dimensional and the codomain is
finite-dimensional. -/
theorem isEmpty_fredholm_of_finiteDimensional_right (hE : ¬ FiniteDimensional 𝕜 E)
    [FiniteDimensional 𝕜 F] : IsEmpty {T : E →L[𝕜] F // T.IsFredholm} :=
  ⟨fun T ↦ not_exists_isFredholm_of_finiteDimensional_right hE ⟨T.val, T.property⟩⟩

section BothFinite

variable [CompleteSpace 𝕜]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F] [FiniteDimensional 𝕜 F]

/-- Between finite-dimensional topological vector spaces over a complete nontrivially normed field
(with Hausdorff target), the Fredholm locus is nonempty since `0` is Fredholm. -/
instance instNonemptyFredholmOfFiniteDimensional :
    Nonempty {T : E →L[𝕜] F // T.IsFredholm} :=
  ⟨⟨0, isFredholm_of_finiteDimensional 0⟩⟩

/-- Between finite-dimensional spaces over a complete nontrivially normed field (with Hausdorff
target), the range of the index on the Fredholm locus is the singleton
`{(finrank 𝕜 E : ℤ) - finrank 𝕜 F}`. -/
@[simp]
theorem range_index_fredholm_of_finiteDimensional :
    Set.range (fun T : {T : E →L[𝕜] F // T.IsFredholm} ↦ T.val.index) =
      {(finrank 𝕜 E : ℤ) - finrank 𝕜 F} := by
  ext n
  simp only [Set.mem_range, Set.mem_singleton_iff]
  refine ⟨?_, fun hn ↦ ⟨⟨0, isFredholm_of_finiteDimensional 0⟩, by simp [hn]⟩⟩
  rintro ⟨T, rfl⟩
  exact T.val.index_eq_of_finiteDimensional

end BothFinite

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
  -- Extract a countably infinite orthonormal sequence `v` via Gram–Schmidt, identify its closed
  -- span `K` with `ℓ²(ℕ, 𝕜)`, transport a power of a shift to `K`, and extend by `id` on `Kᗮ`.
  have hinf : (Basis.ofVectorSpaceIndex 𝕜 E).Infinite :=
    fun hfin ↦ hE (FiniteDimensional.of_finite_basis (Basis.ofVectorSpace 𝕜 E) hfin)
  let e := hinf.natEmbedding (Basis.ofVectorSpaceIndex 𝕜 E)
  have hv : Orthonormal 𝕜
      (InnerProductSpace.gramSchmidtNormed 𝕜 fun k ↦ Basis.ofVectorSpace 𝕜 E (e k)) :=
    InnerProductSpace.gramSchmidtNormed_orthonormal
      ((Basis.ofVectorSpace 𝕜 E).linearIndependent.comp _ e.injective)
  let φ : ℓ²(ℕ, 𝕜) →ₗᵢ[𝕜] E := hv.orthogonalFamily.linearIsometry
  let K : Submodule 𝕜 E := LinearMap.range φ.toLinearMap
  let eK : ℓ²(ℕ, 𝕜) ≃L[𝕜] K := φ.equivRange.toContinuousLinearEquiv
  have : CompleteSpace K := φ.equivRange.symm.toIsometryEquiv.completeSpace
  let eE : (K × Kᗮ) ≃L[𝕜] E := K.prodEquivOfIsTopCompl Kᗮ K.isTopCompl_orthogonal
  obtain ⟨S, hS, hind⟩ := lp.exists_isFredholm_and_index_eq 𝕜 2 n
  let S' : K →L[𝕜] K := ((eK : ℓ²(ℕ, 𝕜) →L[𝕜] K).comp S).comp (eK.symm : K →L[𝕜] ℓ²(ℕ, 𝕜))
  have hS' : S'.IsFredholm := (hS.equiv_comp eK).comp_equiv eK.symm
  have hind' : S'.index = n := by simp [S', hind]
  let T : E →L[𝕜] E :=
    ((eE : K × Kᗮ →L[𝕜] E).comp (S'.prodMap (.id 𝕜 Kᗮ))).comp (eE.symm : E →L[𝕜] K × Kᗮ)
  refine ⟨T, ((hS'.prodMap .id).equiv_comp eE).comp_equiv eE.symm, ?_⟩
  have := hS'.finite_ker
  have := hS'.finite_coker
  have := (IsFredholm.id (𝕜 := 𝕜) (E := Kᗮ)).finite_ker
  have := (IsFredholm.id (𝕜 := 𝕜) (E := Kᗮ)).finite_coker
  simp [T, hind']

/-- On an infinite-dimensional Hilbert space `E`, the Fredholm index surjects onto `ℤ`. -/
theorem surjective_index_fredholm_self (hE : ¬ FiniteDimensional 𝕜 E) :
    Function.Surjective (fun T : {T : E →L[𝕜] E // T.IsFredholm} ↦ T.val.index) := fun n ↦ by
  obtain ⟨T, hT, hind⟩ := exists_isFredholm_and_index_eq_self hE n
  exact ⟨⟨T, hT⟩, hind⟩

/-- On an infinite-dimensional Hilbert space `E`, the range of the index on the Fredholm locus is
all of `ℤ`. -/
@[simp]
theorem range_index_fredholm_self_of_infiniteDimensional (hE : ¬ FiniteDimensional 𝕜 E) :
    Set.range (fun T : {T : E →L[𝕜] E // T.IsFredholm} ↦ T.val.index) = Set.univ :=
  Set.range_eq_univ.2 (surjective_index_fredholm_self hE)

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

/-- If `E` is an infinite-dimensional Hilbert space and `e : E ≃L[𝕜] F` is a continuous linear
equivalence, every integer is the index of a Fredholm operator `E →L[𝕜] F`. -/
theorem exists_isFredholm_and_index_eq (e : E ≃L[𝕜] F) (hE : ¬ FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : E →L[𝕜] F, T.IsFredholm ∧ T.index = n := by
  obtain ⟨T₀, hT₀, hind₀⟩ := ContinuousLinearMap.exists_isFredholm_and_index_eq_self hE n
  exact ⟨(e : E →L[𝕜] F).comp T₀, hT₀.equiv_comp e, (T₀.index_equiv_comp e).trans hind₀⟩

/-- Subtype form of `ContinuousLinearEquiv.exists_isFredholm_and_index_eq`: every integer is
realized on the Fredholm locus `{T : E →L[𝕜] F // T.IsFredholm}`. -/
theorem exists_index_eq (e : E ≃L[𝕜] F) (hE : ¬ FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : {T : E →L[𝕜] F // T.IsFredholm}, T.val.index = n := by
  obtain ⟨T, hT, hind⟩ := e.exists_isFredholm_and_index_eq hE n
  exact ⟨⟨T, hT⟩, hind⟩

/-- Under a continuous linear equivalence from an infinite-dimensional Hilbert space `E` to `F`,
the range of the Fredholm index is all of `ℤ`. -/
theorem range_index_fredholm (e : E ≃L[𝕜] F) (hE : ¬ FiniteDimensional 𝕜 E) :
    Set.range (fun T : {T : E →L[𝕜] F // T.IsFredholm} ↦ T.val.index) = Set.univ :=
  Set.range_eq_univ.2 (e.exists_index_eq hE)

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable {F : Type*} [SeminormedAddCommGroup F] [Module 𝕜 F]

/-- If `E` is an infinite-dimensional Hilbert space and `e : E ≃ₗᵢ[𝕜] F` is a linear isometric
equivalence (for instance a unitary equivalence of Hilbert spaces), every integer is the index of a
Fredholm operator `E →L[𝕜] F`. -/
theorem exists_isFredholm_and_index_eq (e : E ≃ₗᵢ[𝕜] F) (hE : ¬ FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : E →L[𝕜] F, T.IsFredholm ∧ T.index = n :=
  e.toContinuousLinearEquiv.exists_isFredholm_and_index_eq hE n

/-- Subtype form of `LinearIsometryEquiv.exists_isFredholm_and_index_eq`: every integer is the
index of an element of the Fredholm locus `{T : E →L[𝕜] F // T.IsFredholm}`. -/
theorem exists_index_eq (e : E ≃ₗᵢ[𝕜] F) (hE : ¬ FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : {T : E →L[𝕜] F // T.IsFredholm}, T.val.index = n :=
  e.toContinuousLinearEquiv.exists_index_eq hE n

end LinearIsometryEquiv

end Hilbert
