/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

/-!
# Exterior powers of finite locally free sheaves

Let `R` be a sheaf of commutative rings on a small site. If `I` is a finite linearly ordered type,
the `n`-th exterior power of the free sheaf of `R`-modules on `I` is free on the set
`Set.powersetCard I n` of `n`-element subsets of `I`: over each object `W`, the sections of
`free I` form a free `R(W)`-module with basis the sections `eᵢ = freeSection i`
(`TauCeti.SheafOfModules.freeBasis`), so their `n`-th exterior power is free with basis the
wedge products `e_{i₁} ∧ ⋯ ∧ e_{iₙ}` for `i₁ < ⋯ < iₙ` (Mathlib's `Module.Basis.exteriorPower`).
These bases are preserved by the restriction maps, so they identify the sectionwise exterior
power of `free I` with the underlying presheaf of `free (Set.powersetCard I n)`, and sheafifying
gives `⋀ⁿ (free I) ≅ free (Set.powersetCard I n)`.

Since exterior powers commute with restriction to a slice
(`SheafOfModules.overExteriorPowerIso`), a basis of a sheaf of modules `M` over an object `X`
indexed by a finite type `I` yields a basis of `⋀ⁿ M` over `X` indexed by the `n`-element subsets
of `I`. Consequently, exterior powers of finite locally free sheaves are finite locally free, and
a local basis with `r` elements gives a local basis of the `n`-th exterior power with
`r.choose n` elements. This is the input for the rank formula and the determinant of a vector
bundle.

## Main declarations

* `SheafOfModules.presheafExteriorPowerFreeIso`: the sectionwise exterior power of `free I` is
  the underlying presheaf of `free (Set.powersetCard I n)`, sending the wedge product of the
  basis sections indexed by `s` to the basis section indexed by `s`
  (`presheafExteriorPowerFreeIso_hom_app_ιMulti_family`);
* `SheafOfModules.exteriorPowerFreeIso`: `⋀ⁿ (free I) ≅ free (Set.powersetCard I n)`;
* `SheafOfModules.GeneratingSections.exteriorPower`: the basis of `⋀ⁿ M` over `X` induced by a
  finite basis of `M` over `X`;
* `SheafOfModules.isFiniteLocallyFree_exteriorPower`: exterior powers of finite locally free
  sheaves are finite locally free.

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

section Free

variable (I : Type u) [Finite I] [LinearOrder I]

/-- The sectionwise `n`-th exterior power of the free sheaf of modules on a finite linearly
ordered type `I` is the underlying presheaf of the free sheaf on the `n`-element subsets of `I`:
over each object `W` it maps the basis of `⋀[R(W)]^n` induced by `freeBasis I W` to
`freeBasis (Set.powersetCard I n) W`. -/
def presheafExteriorPowerFreeIso (n : ℕ) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj
        (free (R := ringCatSheaf R) I).val ≅
      (free (R := ringCatSheaf R) (Set.powersetCard I n)).val :=
  PresheafOfModulesOfCommRing.isoMk
    (fun W ↦ (((freeBasis (R := R) I W).exteriorPower n).equiv
      (freeBasis (R := R) _ W) (Equiv.refl _)).toModuleIso)
    (fun W W' f ↦ by
      ext : 1
      refine ((freeBasis (R := R) I W).exteriorPower n).ext fun s ↦ ?_
      -- Restriction sends the wedge product of basis sections indexed by `s` over `W` to the one
      -- over `W'`, since it preserves the basis sections of `free I`.
      have hP : ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj
          (free (R := ringCatSheaf R) I).val).map f
            ((freeBasis (R := R) I W).exteriorPower n s) =
          (freeBasis (R := R) I W').exteriorPower n s := by
        rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
        exact (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n _ f _).trans
          (congrArg _ (funext fun j ↦ freeBasis_map I f _))
      -- Both sides send this wedge product to the basis section indexed by `s` over `W'`.
      exact ((congrArg (((freeBasis (R := R) I W').exteriorPower n).equiv
          (freeBasis (R := R) _ W') (Equiv.refl _)) hP).trans
            (Module.Basis.equiv_apply _ _ _ _)).trans
        ((congrArg ((free (R := ringCatSheaf R) (Set.powersetCard I n)).val.map f)
          (Module.Basis.equiv_apply _ _ _ _)).trans (freeBasis_map _ f s)).symm)

/-- `presheafExteriorPowerFreeIso` sends the wedge product, in increasing order, of the basis
sections of `free I` indexed by an `n`-element subset `s` to the basis section indexed by `s`. -/
theorem presheafExteriorPowerFreeIso_hom_app_ιMulti_family (n : ℕ) (W : Cᵒᵖ)
    (s : Set.powersetCard I n) :
    (presheafExteriorPowerFreeIso (R := R) I n).hom.app W
        (exteriorPower.ιMulti_family (R.obj.obj W) n
          (fun i ↦ (freeSection (R := ringCatSheaf R) i).eval W) s) =
      (freeSection (R := ringCatSheaf R) s).eval W := by
  have h : (fun i ↦ (freeSection (R := ringCatSheaf R) i).eval W) = freeBasis (R := R) I W :=
    funext fun i ↦ (TauCeti.SheafOfModules.freeBasis_apply I W i).symm
  rw [h, ← exteriorPower.basis_apply]
  exact (Module.Basis.equiv_apply _ _ _ _).trans (TauCeti.SheafOfModules.freeBasis_apply _ W s)

/-- The inverse of `presheafExteriorPowerFreeIso` sends the basis section indexed by an
`n`-element subset `s` to the wedge product, in increasing order, of the basis sections of
`free I` indexed by `s`. -/
theorem presheafExteriorPowerFreeIso_inv_app_freeSection (n : ℕ) (W : Cᵒᵖ)
    (s : Set.powersetCard I n) :
    (presheafExteriorPowerFreeIso (R := R) I n).inv.app W
        ((freeSection (R := ringCatSheaf R) s).eval W) =
      exteriorPower.ιMulti_family (R.obj.obj W) n
        (fun i ↦ (freeSection (R := ringCatSheaf R) i).eval W) s := by
  rw [← presheafExteriorPowerFreeIso_hom_app_ιMulti_family]
  exact ((PresheafOfModules.evaluation _ W).mapIso
    (presheafExteriorPowerFreeIso (R := R) I n)).hom_inv_id_apply _

/-- The `n`-th exterior power of the free sheaf of modules on a finite linearly ordered type `I`
is the free sheaf on the `n`-element subsets of `I`. -/
def exteriorPowerFreeIso (n : ℕ) :
    (exteriorPower R n).obj (free (R := ringCatSheaf R) I) ≅
      free (R := ringCatSheaf R) (Set.powersetCard I n) :=
  exteriorPowerIso n (free I) ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
      (presheafExteriorPowerFreeIso I n) ≪≫
    TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) (free _)

/-- The forward map of `exteriorPowerFreeIso` is the sheafification of
`presheafExteriorPowerFreeIso`, followed by the identification of the sheafified underlying
presheaf of a free sheaf with that sheaf. -/
@[simp]
theorem exteriorPowerFreeIso_hom (n : ℕ) :
    (exteriorPowerFreeIso (R := R) I n).hom =
      (exteriorPowerIso n (free I)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          (presheafExteriorPowerFreeIso I n).hom ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) (free _)).hom :=
  (rfl)

end Free

section LocallyFree

variable [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} (ringCatSheaf R)} {X : C}

/-- A basis of `M` over `X` indexed by a finite linearly ordered type `σ.I` induces a basis of the
`n`-th exterior power of `M` over `X`, indexed by the `n`-element subsets of `σ.I`. -/
def GeneratingSections.exteriorPower (σ : (M.over X).GeneratingSections) [IsIso σ.π]
    [Finite σ.I] [LinearOrder σ.I] (n : ℕ) :
    (((SheafOfModules.exteriorPower R n).obj M).over X).GeneratingSections :=
  GeneratingSections.equivOfIso
    (overExteriorPowerIso n M X ≪≫ (SheafOfModules.exteriorPower (R.over X) n).mapIso
      (asIso σ.π).symm ≪≫ exteriorPowerFreeIso σ.I n).symm
    (free.generatingSections _)

variable (σ : (M.over X).GeneratingSections) [IsIso σ.π] [Finite σ.I] [LinearOrder σ.I] (n : ℕ)

/-- The basis `σ.exteriorPower n` is indexed by the `n`-element subsets of `σ.I`. -/
@[simp]
theorem GeneratingSections.exteriorPower_I :
    (σ.exteriorPower n).I = Set.powersetCard σ.I n :=
  (rfl)

/-- The characteristic equation of `σ.exteriorPower n`: it is the basis of the free sheaf on the
`n`-element subsets of `σ.I`, transported along the composite of `overExteriorPowerIso`, the
exterior power of the inverse of `σ.π`, and `exteriorPowerFreeIso`. -/
theorem GeneratingSections.exteriorPower_def :
    σ.exteriorPower n = GeneratingSections.equivOfIso
      (overExteriorPowerIso n M X ≪≫ (SheafOfModules.exteriorPower (R.over X) n).mapIso
        (asIso σ.π).symm ≪≫ exteriorPowerFreeIso σ.I n).symm
      (free.generatingSections _) :=
  (rfl)

instance GeneratingSections.isIso_exteriorPower_π : IsIso (σ.exteriorPower n).π :=
  GeneratingSections.isIso_equivOfIso_π _ _
    -- The free sheaf lives over `ringCatSheaf (R.over X)`, which instance search does not
    -- identify with `(ringCatSheaf R).over X`.
    (hσ := inferInstanceAs (IsIso (free.generatingSections (R := ringCatSheaf (R.over X)) _).π))

instance GeneratingSections.finite_exteriorPower_I : Finite (σ.exteriorPower n).I := by
  rw [GeneratingSections.exteriorPower_I]
  infer_instance

variable [Limits.HasPullbacks C]

variable (M) in
/-- The exterior powers of a finite locally free sheaf of modules are finite locally free. -/
theorem isFiniteLocallyFree_exteriorPower (hM : isFiniteLocallyFree (ringCatSheaf R) M) :
    isFiniteLocallyFree (ringCatSheaf R) ((SheafOfModules.exteriorPower R n).obj M) := by
  classical
  obtain ⟨q, hq, hq'⟩ := (isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType M).1 hM
  have (i : q.I) : Finite (q.generators i).I := (hq'.isFiniteType i).finite
  let _ (i : q.I) : LinearOrder (q.generators i).I := linearOrderOfSTO WellOrderingRel
  -- On each chart of `q`, the basis of `M` induces a finite basis of `⋀ⁿ M`.
  exact (isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType _).2
    ⟨{ I := q.I, X := q.X, coversTop := q.coversTop
       generators i := (q.generators i).exteriorPower n }, ⟨fun i ↦ inferInstance⟩,
      ⟨fun i ↦ ⟨inferInstance⟩⟩⟩

end LocallyFree

end SheafOfModules

end
