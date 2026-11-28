/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.LinearAlgebra.Coevaluation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Category.FiniteIsocrystal.Monoidal

/-!
# The dual of a finite isocrystal

The dual of a finite isocrystal `D` over `(L, σ)` is the dual `L`-vector space `D^∨ = Dual L D`
with the Frobenius `ℓ ↦ σ ∘ ℓ ∘ Φ⁻¹`. It is characterized by `Φ^∨ ℓ (Φ x) = σ (ℓ x)`, and it is
again a bijective `σ`-semilinear map. The evaluation `D^∨ ⊗ D → L`, `ℓ ⊗ x ↦ ℓ x`, and the
coevaluation `L → D ⊗ D^∨`, `1 ↦ ∑ eᵢ ⊗ eᵢ^∨`, intertwine the Frobenii, so `D^∨` is a right dual
of `D` in the symmetric monoidal category of finite isocrystals. Hence the category of finite
isocrystals is rigid.

Over the completion of the maximal unramified extension of a local field, dualizing negates
slopes; that statement rests on the Dieudonné–Manin classification and is not proved here.
Together with the tensor product, duals are the tensor calculus of isocrystals that the functor to
vector bundles on the Fargues–Fontaine curve respects.

## Main definitions

* `TauCeti.FiniteIsocrystal.dualFrobenius`: the Frobenius `ℓ ↦ σ ∘ ℓ ∘ Φ⁻¹` of the dual.
* `TauCeti.FiniteIsocrystal.dual`: the dual finite isocrystal.
* The `ExactPairing D (dual D)` instance, whose evaluation and coevaluation are Mathlib's
  `contractLeft` and `coevaluation`, and the `RigidCategory` instance on finite isocrystals.

## Main results

* `TauCeti.FiniteIsocrystal.dualFrobenius_apply`: `Φ^∨ ℓ x = σ (ℓ (Φ⁻¹ x))`.
* `TauCeti.FiniteIsocrystal.dualFrobenius_apply_frobenius`: `Φ^∨ ℓ (Φ x) = σ (ℓ x)`.
* `TauCeti.FiniteIsocrystal.dualFrobenius_bijective`: the dual Frobenius is bijective.
* `TauCeti.FiniteIsocrystal.map_frobenius_dualFrobenius_coevaluation_one`: the Frobenius
  `Φ ⊗ Φ^∨` of `D ⊗ D^∨` fixes the canonical element `∑ eᵢ ⊗ eᵢ^∨`.
* `TauCeti.FiniteIsocrystal.hom_exactPairing_evaluation`,
  `TauCeti.FiniteIsocrystal.hom_exactPairing_coevaluation` and
  `TauCeti.FiniteIsocrystal.rightDual_eq_dual`: the underlying linear maps of `ε_` and `η_` are
  Mathlib's `contractLeft` and `coevaluation`, and `Dᘁ = D^∨`.
* `TauCeti.FiniteIsocrystal.finrank_dual`: the dual has the same rank.

## Implementation notes

The `ExactPairing` and rigid structure follow Mathlib's
`Mathlib/Algebra/Category/FGModuleCat/Basic.lean` (`FGModuleCat.exactPairing`): they reuse
Mathlib's `coevaluation` and `contractLeft`, and the triangle identities are
`contractLeft_assoc_coevaluation` and `contractLeft_assoc_coevaluation'`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3, Proposition 8.2.6.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), Definition 3.1.5.
-/

public section

open CategoryTheory TensorProduct
open scoped MonoidalCategory

universe u

namespace TauCeti

namespace FiniteIsocrystal

variable {E : Type*} {L : Type u} [CommRing E] [Field L] [Algebra E L] {σ : L ≃ₐ[E] L}

/-! ### The dual Frobenius -/

section DualFrobenius

variable (D : FiniteIsocrystal.{u} σ)

/-- The Frobenius of the dual of a finite isocrystal: the `σ`-semilinear map
`ℓ ↦ σ ∘ ℓ ∘ Φ⁻¹` on `Dual L D`, which is Mathlib's `LinearEquiv.arrowCongr` of `Φ` and `σ`. -/
noncomputable def dualFrobenius : Module.Dual L D →ₛₗ[(σ : L →+* L)] Module.Dual L D :=
  (LinearEquiv.arrowCongr D.frobeniusEquiv σ.toRingEquiv.toSemilinearEquiv :
    Module.Dual L D ≃ₛₗ[(σ : L →+* L)] Module.Dual L D).toLinearMap

/-- The dual Frobenius is `ℓ ↦ σ ∘ ℓ ∘ Φ⁻¹`. -/
theorem dualFrobenius_apply (ℓ : Module.Dual L D) (x : D) :
    D.dualFrobenius ℓ x = σ (ℓ (D.frobeniusEquiv.symm x)) := (rfl)

/-- The dual Frobenius is characterized by `Φ^∨ ℓ (Φ x) = σ (ℓ x)`. -/
@[simp]
theorem dualFrobenius_apply_frobenius (ℓ : Module.Dual L D) (x : D) :
    D.dualFrobenius ℓ (D.frobenius x) = σ (ℓ x) := by
  simp [dualFrobenius_apply]

/-- The dual Frobenius is the unique map with `Φ^∨ ℓ (Φ x) = σ (ℓ x)`. -/
theorem eq_dualFrobenius_iff (ℓ ℓ' : Module.Dual L D) :
    ℓ' = D.dualFrobenius ℓ ↔ ∀ x, ℓ' (D.frobenius x) = σ (ℓ x) := by
  refine ⟨fun h x => by simp [h], fun h => LinearMap.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := D.frobenius_surjective y
  rw [h, dualFrobenius_apply_frobenius]

/-- The dual Frobenius is bijective. -/
theorem dualFrobenius_bijective : Function.Bijective D.dualFrobenius :=
  (LinearEquiv.arrowCongr D.frobeniusEquiv σ.toRingEquiv.toSemilinearEquiv :
    Module.Dual L D ≃ₛₗ[(σ : L →+* L)] Module.Dual L D).bijective

/-- The dual of a finite isocrystal: `Dual L D` with Frobenius `ℓ ↦ σ ∘ ℓ ∘ Φ⁻¹`. -/
noncomputable abbrev dual : FiniteIsocrystal.{u} σ :=
  of σ (Module.Dual L D) D.dualFrobenius D.dualFrobenius_bijective

/-- The dual of a finite isocrystal has the same rank. -/
theorem finrank_dual : Module.finrank L D.dual = Module.finrank L D :=
  Subspace.dual_finrank_eq

/-- Over a basis `b`, the dual Frobenius and the Frobenius recover every vector:
`∑ᵢ Φ^∨ (bᵢ^∨) x • Φ bᵢ = x`. -/
theorem sum_dualFrobenius_coord_smul_frobenius {ι : Type*} [Fintype ι]
    (b : Module.Basis ι L D) (x : D) :
    ∑ i, D.dualFrobenius (b.coord i) x • D.frobenius (b i) = x := by
  obtain ⟨y, rfl⟩ := D.frobenius_surjective x
  have h (c : L) (z : D) : σ c • D.frobenius z = D.frobenius (c • z) := by simp
  simp_rw [dualFrobenius_apply_frobenius, h, ← map_sum, Module.Basis.coord_apply,
    Module.Basis.sum_repr]

/-- The Frobenius `Φ ⊗ Φ^∨` of `D ⊗ D^∨` fixes the canonical element `∑ eᵢ ⊗ eᵢ^∨`, the image of
`1` under the coevaluation. -/
theorem map_frobenius_dualFrobenius_coevaluation_one :
    TensorProduct.map D.frobenius D.dualFrobenius (coevaluation L D 1) =
      coevaluation L D 1 := by
  let b := Module.Basis.ofVectorSpace L D
  rw [coevaluation_apply_one]
  -- Expand each `Φ^∨ (bᵢ^∨)` in the dual basis and regroup by the dual basis vectors.
  calc TensorProduct.map D.frobenius D.dualFrobenius (∑ i, b i ⊗ₜ[L] b.coord i)
      = ∑ i, D.frobenius (b i) ⊗ₜ[L]
          ∑ j, D.dualFrobenius (b.coord i) (b j) • b.coord j := by
        simp only [map_sum, map_tmul]
        congr! with i
        exact (b.sum_dual_apply_smul_coord _).symm
    _ = ∑ j, (∑ i, D.dualFrobenius (b.coord i) (b j) • D.frobenius (b i)) ⊗ₜ[L] b.coord j := by
        simp_rw [tmul_sum, tmul_smul, smul_tmul', sum_tmul]
        exact Finset.sum_comm
    _ = ∑ j, b j ⊗ₜ[L] b.coord j :=
        Finset.sum_congr rfl fun j _ => by rw [sum_dualFrobenius_coord_smul_frobenius]

end DualFrobenius

/-! ### Evaluation and coevaluation -/

section Pairing

variable (D : FiniteIsocrystal.{u} σ)

/-- The dual `D^∨` is a right dual of `D`: the evaluation `D^∨ ⊗ D ⟶ 𝟙`, `ℓ ⊗ x ↦ ℓ x`, and the
coevaluation `𝟙 ⟶ D ⊗ D^∨`, `1 ↦ ∑ eᵢ ⊗ eᵢ^∨`, satisfy the triangle identities. -/
noncomputable instance exactPairing : ExactPairing D D.dual where
  coevaluation' := ofHom (coevaluation L D) fun c => by
    have hc (a : L) : coevaluation L D a = a • coevaluation L D 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [tensorObj_frobenius, hc, hc c, map_smulₛₗ, map_frobenius_dualFrobenius_coevaluation_one]
    simp
  evaluation' := ofHom (contractLeft L D) fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul ℓ x =>
      rw [tensorObj_frobenius, tensorUnit_frobenius_apply, map_tmul, contractLeft_apply,
        contractLeft_apply, dualFrobenius_apply_frobenius]
    | add t t' ht ht' => simp_all
  coevaluation_evaluation' := by
    ext1
    simp only [hom_comp, hom_whiskerLeft, hom_whiskerRight, hom_inv_associator,
      hom_hom_rightUnitor, hom_inv_leftUnitor, LinearMap.comp_assoc]
    exact contractLeft_assoc_coevaluation L D
  evaluation_coevaluation' := by
    ext1
    simp only [hom_comp, hom_whiskerLeft, hom_whiskerRight, hom_hom_associator,
      hom_hom_leftUnitor, hom_inv_rightUnitor, LinearMap.comp_assoc]
    exact contractLeft_assoc_coevaluation' L D

/-- The underlying linear map of the evaluation `ε_ D D^∨` is `ℓ ⊗ x ↦ ℓ x`. -/
@[simp]
theorem hom_exactPairing_evaluation : (ε_ D D.dual).hom = contractLeft L D := (rfl)

/-- The underlying linear map of the coevaluation `η_ D D^∨` is `1 ↦ ∑ eᵢ ⊗ eᵢ^∨`. -/
@[simp]
theorem hom_exactPairing_coevaluation : (η_ D D.dual).hom = coevaluation L D := (rfl)

noncomputable instance : HasRightDual D := ⟨D.dual⟩

/-- The right dual `Dᘁ` of a finite isocrystal is its dual `D^∨`. -/
@[simp]
theorem rightDual_eq_dual : Dᘁ = D.dual := (rfl)

noncomputable instance : RightRigidCategory (FiniteIsocrystal.{u} σ) where

/-- The category of finite isocrystals is rigid: since it is symmetric monoidal, the right dual
`D^∨` is also a left dual. -/
noncomputable instance : RigidCategory (FiniteIsocrystal.{u} σ) :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

end Pairing

end FiniteIsocrystal

end TauCeti
