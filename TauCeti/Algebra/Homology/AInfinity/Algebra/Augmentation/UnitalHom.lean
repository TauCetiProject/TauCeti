/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented

/-!
# The augmentation as a strict `A∞` morphism

For an augmented `A∞` algebra `(A, ε)` we package the augmentation itself as a strict `A∞`
morphism to the ground ring (`toAInfinityStrictHom`, `toAInfinityStrictUnitalHom`). We record the
linear part of the extension `(strictlyUnitalHomEquiv hB).symm g` of a nonunital `A∞` morphism
`g : A⁺ ⟶ B` on `A⁺` and on the strict unit, its naturality under strictly unital strict
morphisms (`strictlyUnitalHomEquiv_symm_comp_strict`), and the augmentation-preservation criterion
`comp_toAInfinityStrictHom_eq_iff`: a strictly unital morphism `f` satisfies `ε_B ∘ f = ε` if and
only if its restriction to `A⁺` vanishes under `ε_B`. For a DG algebra augmentation, the strict
morphism of `DGAlgAugmentation.toAInfinityAugmentation` is the strict morphism of the underlying
DG algebra morphism (`DGAlgAugmentation.toAInfinityAugmentation_toAInfinityStrictHom`).

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Chapter 3.
-/

public section

namespace TauCeti

open ReducedTensorWords (letter map_ofLetter)
open AInfinityHom (linearPart_apply)
open AInfinityStrictHom (taylor_toAInfinityHom taylor_toAInfinityHom_comp barMap_def)

universe uR uA uB uC

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}
  (ε : 𝒜.Augmentation)

/-- The bar differential commutes with the induced map on words of the inclusion `A⁺ ⟶ A`. -/
theorem barDifferential_comp_map_inclusion :
    𝒜.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
      ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype ∘ₗ
        ε.reducedAlgebra.barDifferential := by
  simpa [barMap_def] using ε.inclusion.barDifferential_comp_barMap

/-- The augmentation of an `A∞` algebra as a strict `A∞` morphism to the ground ring. -/
noncomputable def toAInfinityStrictHom : AInfinityStrictHom 𝒜
    (isDGAlgebra_trivialGrading R).toIsNonUnitalDGAlgebra.toAInfinityAlgebra where
  toLinearMap := ε.toLinearMap
  map_mem' {p a} ha := by
    rcases eq_or_ne p 0 with rfl | hp; exacts [by simp, by simp [ε.map_of_mem_ne_zero p a ha hp]]
  map_m'
    | 0 | _ + 3 => by ext; simp
    | 1 => by ext x; have hx : x = ![x 0] := funext <| Fin.forall_fin_one.2 rfl; rw [hx]; simp
    | 2 => by
      ext x; have hx : x = ![x 0, x 1] := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩; rw [hx]; simp

@[simp] theorem toAInfinityStrictHom_toLinearMap :
    ε.toAInfinityStrictHom.toLinearMap = ε.toLinearMap := (rfl)

@[simp] theorem coe_toAInfinityStrictHom : ⇑ε.toAInfinityStrictHom = ε := (rfl)

/-- The augmentation of an `A∞` algebra as a strictly unital strict `A∞` morphism to `R`. -/
noncomputable def toAInfinityStrictUnitalHom :
    AInfinityStrictUnitalHom ε.isStrictUnit (isDGAlgebra_trivialGrading R).strictUnit_one where
  toAInfinityStrictHom := ε.toAInfinityStrictHom
  map_unit' := ε.map_unit

@[simp] theorem toAInfinityStrictHom_toAInfinityStrictUnitalHom :
    ε.toAInfinityStrictUnitalHom.toAInfinityStrictHom = ε.toAInfinityStrictHom := (rfl)

theorem linearPart_strictlyUnitalHomEquiv_symm_coe {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) (x : ε.augmentationIdeal) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).val.linearPart x = g.linearPart x := by
  simp [ε.mem_augmentationIdeal.mp x.property]

theorem linearPart_strictlyUnitalHomEquiv_symm_unit {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).val.linearPart ε.unit = eB :=
  ((ε.strictlyUnitalHomEquiv hB).symm g).property.map_unit

/-- Extending a nonunital morphism `A⁺ ⟶ B` commutes with postcomposition by a strictly unital
strict morphism `B ⟶ C`. -/
theorem strictlyUnitalHomEquiv_symm_comp_strict {eB : B} {eC : C} (hB : ℬ.StrictUnit eB)
    (hC : 𝒞.StrictUnit eC) (φ : AInfinityStrictUnitalHom hB hC)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hC).symm (φ.toAInfinityStrictHom.toAInfinityHom.comp g)).val =
      φ.toAInfinityStrictHom.toAInfinityHom.comp ((ε.strictlyUnitalHomEquiv hB).symm g).val :=
  AInfinityHom.ext <| LinearMap.ext fun _ ↦ by
    rw [taylor_toAInfinityHom_comp, strictlyUnitalHomEquiv_symm_apply_val,
      strictlyUnitalHomEquiv_symm_apply_val, taylor_extendStrictlyUnitalHom,
      taylor_extendStrictlyUnitalHom, taylor_toAInfinityHom_comp]
    simp [AInfinityStrictHom.coe_toLinearMap, φ.map_unit']

/-- A strictly unital morphism preserves augmentations iff its restriction vanishes under `εB`. -/
theorem comp_toAInfinityStrictHom_eq_iff (εB : ℬ.Augmentation)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit εB.isStrictUnit}) :
    εB.toAInfinityStrictHom.toAInfinityHom.comp f.val = ε.toAInfinityStrictHom.toAInfinityHom ↔
      εB.toLinearMap ∘ₗ (ε.strictlyUnitalHomEquiv εB.isStrictUnit f).taylor = 0 := by
  have hcomp_red : (ε.toAInfinityStrictHom.toAInfinityHom.comp
      ε.inclusion.toAInfinityHom).taylor = 0 := by
    rw [taylor_toAInfinityHom_comp, taylor_toAInfinityHom]; simp [← LinearMap.comp_assoc]
  rw [strictlyUnitalHomEquiv_apply]
  refine ⟨fun h ↦ by
      have h' := congrArg (fun k ↦ (k.comp ε.inclusion.toAInfinityHom).taylor) h
      rwa [AInfinityHom.comp_assoc, taylor_toAInfinityHom_comp, toAInfinityStrictHom_toLinearMap,
        hcomp_red] at h',
    fun h ↦ congrArg Subtype.val <|
      (ε.strictlyUnitalHomEquiv (isDGAlgebra_trivialGrading R).strictUnit_one).injective
        (a₁ := ⟨εB.toAInfinityStrictHom.toAInfinityHom.comp f.val,
          εB.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom.comp f.property⟩)
        (a₂ := ⟨ε.toAInfinityStrictHom.toAInfinityHom,
          ε.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom⟩) <|
      AInfinityHom.ext <| by rwa [strictlyUnitalHomEquiv_apply, strictlyUnitalHomEquiv_apply,
        AInfinityHom.comp_assoc, taylor_toAInfinityHom_comp, toAInfinityStrictHom_toLinearMap,
        hcomp_red]⟩

end AInfinityAlgebra.Augmentation

namespace DGAlgAugmentation

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  (e : DGAlgAugmentation h)

@[simp] theorem toAInfinityAugmentation_toAInfinityStrictHom :
    e.toAInfinityAugmentation.toAInfinityStrictHom = e.toNonUnitalDGAlgHom.toAInfinityStrictHom :=
  by ext a; simp

end DGAlgAugmentation

end TauCeti
