/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Isotypic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Simple
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Direct sums of coefficient spaces

For a family of right comodules `Mᵢ` over a coalgebra `C`, the coefficient maps
`Mᵢ* ⊗ Mᵢ → C`, `φ ⊗ m ↦ (φ ⊗ id) ρ(m)`, assemble into one linear map
`⨁ᵢ Mᵢ* ⊗ Mᵢ → C` (`TauCeti.Comodule.directSumMatrixCoefficientTensor`). For the coordinate
Hopf algebra of an affine group `G`, the image of `φ ⊗ m` in the summand of `Mᵢ` is the regular
function `g ↦ φ(g m)`. The range of the map is the sum of the coefficient spaces of the `Mᵢ`.

Over an algebraically closed field the map is injective for every family of simple comodules no
two of which are isomorphic: each summand embeds by Burnside's theorem
(`TauCeti.Comodule.matrixCoefficientTensor_injective`), and the coefficient spaces of
non-isomorphic simple comodules are independent
(`TauCeti.Comodule.iSupIndep_matrixCoefficientSubmodule`). Neither step uses linear reductivity,
so this holds in every characteristic and for every coalgebra; what can fail without linear
reductivity is surjectivity. For a linearly reductive coalgebra the map is bijective on a family
containing exactly one copy of each simple right coideal of `C` up to isomorphism (such a family
exists by `TauCeti.Comodule.exists_simple_family_pairwise_complete`); this algebraic Peter–Weyl
theorem is `TauCeti.Coalgebra.IsLinearlyReductive.peterWeylEquiv`.

## Main declarations

* `TauCeti.Comodule.directSumMatrixCoefficientTensor`: the map `⨁ᵢ Mᵢ* ⊗ Mᵢ → C`.
* `TauCeti.Comodule.range_directSumMatrixCoefficientTensor`: its range is `⨆ᵢ C(Mᵢ)`.
* `TauCeti.Comodule.directSumMatrixCoefficientTensor_injective`: injectivity over an
  algebraically closed field for pairwise non-isomorphic simple comodules.

## References

* M. Sweedler, *Hopf Algebras* (1969), Chapters II and XIV.
* J. S. Milne, *Algebraic Groups* (2017), §12, matrix coefficients.
-/

public noncomputable section

open scoped TensorProduct DirectSum

namespace TauCeti.Comodule

section CommSemiring

variable {R C ι : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, Comodule R C (M i)]

/-- The coefficient maps `Mᵢ* ⊗ Mᵢ → C` of a family of right comodules, assembled on the direct
sum `⨁ᵢ Mᵢ* ⊗ Mᵢ`. On the summand of `Mᵢ` it sends `φ ⊗ m` to the matrix coefficient
`(φ ⊗ id) ρ(m)`. -/
def directSumMatrixCoefficientTensor : (⨁ i, Module.Dual R (M i) ⊗[R] M i) →ₗ[R] C :=
  DirectSum.toModule R ι C fun i ↦ matrixCoefficientTensor (R := R) (C := C) (M := M i)

/-- On the summand of `Mᵢ`, `directSumMatrixCoefficientTensor` is the coefficient map of `Mᵢ`. -/
@[simp]
theorem directSumMatrixCoefficientTensor_lof (i : ι) (z : Module.Dual R (M i) ⊗[R] M i) :
    directSumMatrixCoefficientTensor (C := C) M (DirectSum.lof R ι _ i z) =
      matrixCoefficientTensor (R := R) (C := C) z := by
  rw [directSumMatrixCoefficientTensor, DirectSum.toModule_lof]

/-- The coefficient map of `Mᵢ`, with its codomain restricted to the coefficient space. -/
private def matrixCoefficientTensorCodRestrict (i : ι) :
    Module.Dual R (M i) ⊗[R] M i →ₗ[R] matrixCoefficientSubmodule (R := R) (C := C) (M := M i) :=
  (matrixCoefficientTensor (R := R) (C := C) (M := M i)).codRestrict _ fun z ↦ by
    rw [← range_matrixCoefficientTensor]
    exact LinearMap.mem_range_self _ z

omit [DecidableEq ι] in
private theorem matrixCoefficientTensorCodRestrict_surjective (i : ι) :
    Function.Surjective (matrixCoefficientTensorCodRestrict (R := R) (C := C) M i) := by
  rintro ⟨c, hc⟩
  rw [← range_matrixCoefficientTensor] at hc
  obtain ⟨z, rfl⟩ := hc
  exact ⟨z, Subtype.ext (by simp [matrixCoefficientTensorCodRestrict])⟩

/-- The assembled coefficient map factors through the direct sum of the coefficient spaces. -/
private theorem directSumMatrixCoefficientTensor_eq_comp :
    directSumMatrixCoefficientTensor (C := C) M =
      DirectSum.coeLinearMap (fun i ↦ matrixCoefficientSubmodule (R := R) (C := C) (M := M i)) ∘ₗ
        DirectSum.lmap (matrixCoefficientTensorCodRestrict (R := R) (C := C) M) := by
  ext i z
  simp [matrixCoefficientTensorCodRestrict]

/-- The range of the assembled coefficient map is the sum of the coefficient spaces. -/
theorem range_directSumMatrixCoefficientTensor :
    LinearMap.range (directSumMatrixCoefficientTensor (C := C) M) =
      ⨆ i, matrixCoefficientSubmodule (R := R) (C := C) (M := M i) := by
  rw [directSumMatrixCoefficientTensor_eq_comp, LinearMap.range_comp_of_range_eq_top,
    DirectSum.range_coeLinearMap]
  exact LinearMap.range_eq_top.mpr <|
    (DirectSum.lmap_surjective _).mpr (matrixCoefficientTensorCodRestrict_surjective M)

end CommSemiring

section Field

universe u v

variable {k : Type u} {C : Type v} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- **The coefficient maps of non-isomorphic simple comodules are jointly injective.** Over an
algebraically closed field, for a family of simple comodules with no nonzero morphism between
distinct members, the map `⨁ᵢ Mᵢ* ⊗ Mᵢ → C` is injective. -/
theorem directSumMatrixCoefficientTensor_injective [IsAlgClosed k] {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Comodule k C (M i)]
    [∀ i, IsSimpleOrder (Subcomodule k C (M i))]
    (hM : Pairwise fun i j ↦ ∀ f : Hom k C (M i) (M j), f = 0) :
    Function.Injective (directSumMatrixCoefficientTensor (R := k) (C := C) M) := by
  have (i : ι) : Module.Finite k (M i) := finite_of_isSimpleOrder (C := C)
  rw [directSumMatrixCoefficientTensor_eq_comp]
  refine (iSupIndep_matrixCoefficientSubmodule M hM).dfinsupp_lsum_injective.comp ?_
  refine (DirectSum.lmap_injective _).mpr fun i ↦ ?_
  intro x y h
  exact matrixCoefficientTensor_injective
    (by simpa [matrixCoefficientTensorCodRestrict] using congrArg Subtype.val h)

end Field

end TauCeti.Comodule
