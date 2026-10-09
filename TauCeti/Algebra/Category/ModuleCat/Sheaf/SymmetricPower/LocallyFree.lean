/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Free

/-!
# Symmetric powers of finite locally free sheaves

Symmetric powers commute with restriction to a slice, and the `n`-th symmetric power of a free
sheaf on `I` is free on the degree-`n` multisets in `I`. Therefore a finite local basis of
a sheaf `M` induces a finite local basis of `Symⁿ M`. In particular, symmetric powers preserve
finite local freeness.

## Main declarations

* `SheafOfModules.GeneratingSections.symmetricPower`: the local basis of `Symⁿ M` induced by a
  finite local basis of `M`;
* `SheafOfModules.isFiniteLocallyFree_symmetricPower`: symmetric powers preserve finite local
  freeness.

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

/-- A finite basis of `M` over `X` induces a basis of its `n`-th symmetric power, indexed by
degree-`n` multisets in the original basis. -/
def GeneratingSections.symmetricPower (σ : (M.over X).GeneratingSections) [IsIso σ.π]
    [Finite σ.I] (n : ℕ) :
    (((SheafOfModules.symmetricPower R n).obj M).over X).GeneratingSections :=
  GeneratingSections.equivOfIso
    (overSymmetricPowerIso n M X ≪≫ (SheafOfModules.symmetricPower (R.over X) n).mapIso
      (asIso σ.π).symm ≪≫ symmetricPowerFreeIso σ.I n).symm
    (free.generatingSections _)

variable (σ : (M.over X).GeneratingSections) [IsIso σ.π] [Finite σ.I] (n : ℕ)

/-- The basis `σ.symmetricPower n` is indexed by degree-`n` multisets in `σ.I`. -/
@[simp]
theorem GeneratingSections.symmetricPower_I :
    (σ.symmetricPower n).I = Sym σ.I n :=
  (rfl)

/-- The characteristic equation of the local basis induced on a symmetric power. -/
theorem GeneratingSections.symmetricPower_def :
    σ.symmetricPower n = GeneratingSections.equivOfIso
      (overSymmetricPowerIso n M X ≪≫ (SheafOfModules.symmetricPower (R.over X) n).mapIso
        (asIso σ.π).symm ≪≫ symmetricPowerFreeIso σ.I n).symm
      (free.generatingSections _) :=
  (rfl)

instance GeneratingSections.isIso_symmetricPower_π : IsIso (σ.symmetricPower n).π :=
  GeneratingSections.isIso_equivOfIso_π _ _
    (hσ := inferInstanceAs (IsIso
      (free.generatingSections (R := ringCatSheaf (R.over X)) _).π))

instance GeneratingSections.finite_symmetricPower_I : Finite (σ.symmetricPower n).I := by
  rw [GeneratingSections.symmetricPower_I]
  infer_instance

variable [Limits.HasPullbacks C]
variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]

variable (M) in
/-- Symmetric powers of a finite locally free sheaf of modules are finite locally free. -/
theorem isFiniteLocallyFree_symmetricPower (hM : isFiniteLocallyFree (ringCatSheaf R) M) :
    isFiniteLocallyFree (ringCatSheaf R) ((SheafOfModules.symmetricPower R n).obj M) := by
  classical
  obtain ⟨q, hq, hq'⟩ := (isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType M).1 hM
  have (i : q.I) : Finite (q.generators i).I := (hq'.isFiniteType i).finite
  exact (isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType _).2
    ⟨{ I := q.I, X := q.X, coversTop := q.coversTop
       generators i := (q.generators i).symmetricPower n }, ⟨fun _ ↦ inferInstance⟩,
      ⟨fun _ ↦ ⟨inferInstance⟩⟩⟩

end LocallyFree

end SheafOfModules

end
