/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

/-!
# Exterior powers of finite locally free sheaves

Let `R` be a sheaf of commutative rings on a small site. Since exterior powers commute with
restriction to a slice (`SheafOfModules.overExteriorPowerIso`) and the `n`-th exterior power of
the free sheaf on a finite linearly ordered type `I` is free on the `n`-element subsets of `I`
(`SheafOfModules.exteriorPowerFreeIso`), a basis of a sheaf of modules `M` over an object `X`
indexed by a finite type `I` yields a basis of `⋀ⁿ M` over `X` indexed by the `n`-element subsets
of `I`. Consequently, exterior powers of finite locally free sheaves are finite locally free, and
a local basis with `r` elements gives a local basis of the `n`-th exterior power with
`r.choose n` elements. This is the input for the rank formula and the determinant of a vector
bundle.

## Main declarations

* `SheafOfModules.GeneratingSections.exteriorPower`: the basis of `⋀ⁿ M` over `X` induced by a
  finite basis of `M` over `X`;
* `SheafOfModules.isFiniteLocallyFree_exteriorPower`: exterior powers of finite locally free
  sheaves are finite locally free.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory
open TauCeti.SheafOfModules (ringCatSheaf)

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

namespace SheafOfModules

section LocallyFree

variable [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
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
variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]

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
