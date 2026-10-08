/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Symmetric powers of free sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. If `I` is finite, the `n`-th symmetric
power of the free sheaf on `I` is free on `Sym I n`, the degree-`n` multisets of basis indices.
On sections this is the monomial basis of the degree-`n` homogeneous component of the symmetric
algebra induced by `TauCeti.SheafOfModules.freeBasis`. Restriction maps preserve these bases, so
the sectionwise comparison sheafifies to the claimed isomorphism.

## Main declarations

* `SheafOfModules.presheafSymmetricPowerFreeIso`: the sectionwise symmetric power of `free I` is
  the underlying presheaf of the free sheaf on degree-`n` multisets in `I`;
* `SheafOfModules.symmetricPowerFreeIso`: `Symⁿ (free I)` is free on those multisets.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory
open TauCeti.SheafOfModules (ringCatSheaf freeBasis freeBasis_map)

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

namespace SheafOfModules

variable (I : Type u) [Finite I]

/-- The sectionwise `n`-th symmetric power of the free sheaf on `I` is the underlying presheaf
of the free sheaf on degree-`n` multisets of basis indices. -/
def presheafSymmetricPowerFreeIso (n : ℕ) :
    (PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj
        (free (R := ringCatSheaf R) I).val ≅
      (free (R := ringCatSheaf R) (Sym I n)).val :=
  PresheafOfModulesOfCommRing.isoMk
    (fun W ↦ (((freeBasis (R := R) I W).symmetricAlgebraHomogeneous n).equiv
      (freeBasis (R := R) _ W) (Equiv.refl _)).toModuleIso)
    (fun W W' f ↦ by
      ext : 1
      refine ((freeBasis (R := R) I W).symmetricAlgebraHomogeneous n).ext fun d ↦ ?_
      have hP : ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj
          (free (R := ringCatSheaf R) I).val).map f
            ((freeBasis (R := R) I W).symmetricAlgebraHomogeneous n d) =
          (freeBasis (R := R) I W').symmetricAlgebraHomogeneous n d := by
        let g := (ModuleCat.semilinearMapAddEquiv (R.obj.map f).hom _ _).symm
          ((free (R := ringCatSheaf R) I).val.map f)
        have hg (i : I) : g (freeBasis (R := R) I W i) = freeBasis (R := R) I W' i :=
          freeBasis_map I f i
        apply Subtype.ext
        erw [PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply]
        simpa [g] using congrArg Subtype.val
          (TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ_symmetricAlgebraHomogeneous
            (R := R.obj.obj W)
            (M := ((free (R := ringCatSheaf R) I).val.obj W))
            (freeBasis (R := R) I W) (freeBasis (R := R) I W') g hg n d)
      exact ((congrArg (((freeBasis (R := R) I W').symmetricAlgebraHomogeneous n).equiv
          (freeBasis (R := R) _ W') (Equiv.refl _)) hP).trans
            (Module.Basis.equiv_apply _ _ _ _)).trans
        ((congrArg ((free (R := ringCatSheaf R) (Sym I n)).val.map f)
          (Module.Basis.equiv_apply _ _ _ _)).trans (freeBasis_map _ f d)).symm)

/-- The forward map of `presheafSymmetricPowerFreeIso` sends each homogeneous monomial basis
vector to the free basis section with the same exponent vector. -/
theorem presheafSymmetricPowerFreeIso_hom_app_basis (n : ℕ) (W : Cᵒᵖ)
    (d : Sym I n) :
    (presheafSymmetricPowerFreeIso (R := R) I n).hom.app W
        ((freeBasis (R := R) I W).symmetricAlgebraHomogeneous n d) =
      (freeSection (R := ringCatSheaf R) d).eval W := by
  exact (Module.Basis.equiv_apply _ _ _ _).trans
    (TauCeti.SheafOfModules.freeBasis_apply _ W d)

/-- The `n`-th symmetric power of the free sheaf on `I` is free on the degree-`n` multisets of
basis indices. -/
def symmetricPowerFreeIso (n : ℕ) :
    (symmetricPower R n).obj (free (R := ringCatSheaf R) I) ≅
      free (R := ringCatSheaf R) (Sym I n) :=
  symmetricPowerIso n (free I) ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
      (presheafSymmetricPowerFreeIso I n) ≪≫
    TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) (free _)

/-- The forward map of `symmetricPowerFreeIso` is the sheafification of the sectionwise free
comparison followed by the sheafification counit. -/
@[simp]
theorem symmetricPowerFreeIso_hom (n : ℕ) :
    (symmetricPowerFreeIso (R := R) I n).hom =
      (symmetricPowerIso n (free I)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          (presheafSymmetricPowerFreeIso I n).hom ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) (free _)).hom :=
  (rfl)

end SheafOfModules

end
