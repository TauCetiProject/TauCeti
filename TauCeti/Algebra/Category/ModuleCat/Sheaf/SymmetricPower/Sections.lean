/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Mul
-- Identify the sheafification unit through the named symmetric-power and adjunction comparisons.
import all TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Basic
import all TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal

/-!
# Sectionwise symmetric tensors in symmetric powers of sheaves

The sheafification unit sends a sectionwise symmetric tensor to a section of the symmetric
power sheaf. These maps are natural and preserve homogeneous multiplication. This provides
the multiplicative comparison needed to compute symmetric algebras on affine opens.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)

namespace SheafOfModules

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- The canonical map from sectionwise symmetric tensors to the underlying presheaf of the
symmetric power sheaf: the sheafification unit followed by `symmetricPowerIso.inv`. -/
def symmetricPowerUnit (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModulesOfCommRing.symmetricPower n).obj M.val ⟶
      ((symmetricPower R n).obj M).val :=
  (TauCeti.SheafOfModules.sheafificationForgetAdjunction R).unit.app _ ≫
    (SheafOfModules.forget (ringCatSheaf R)).map (symmetricPowerIso n M).inv

/-- On sections, `symmetricPowerUnit` is the defining sheafification map. -/
@[simp]
lemma symmetricPowerUnit_app (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) (U : Cᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj (R := R.obj) M.val U).symmetricPower n) :
    PresheafOfModules.Hom.app' (R := R.obj) (symmetricPowerUnit n M) U x =
      (symmetricPowerIso n M).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower n).obj M.val)).app U x) :=
  (rfl)

/-- The canonical map from sectionwise symmetric tensors is natural in the sheaf. -/
@[reassoc]
lemma symmetricPowerUnit_naturality (n : ℕ) {M N : SheafOfModules.{u} (ringCatSheaf R)}
    (φ : M ⟶ N) :
    (PresheafOfModulesOfCommRing.symmetricPower n).map φ.val ≫ symmetricPowerUnit n N =
      symmetricPowerUnit n M ≫ ((symmetricPower R n).map φ).val := by
  ext U x
  exact (symmetricPower_map_val_app_unit n φ U x).symm

/-- The sheafification maps on symmetric powers preserve homogeneous multiplication, through
the tensor comparison of the forgetful functor from sheaves to presheaves. -/
@[reassoc]
lemma symmetricPowerUnit_mul (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (symmetricPowerUnit i M ⊗ₘ symmetricPowerUnit j M) ≫
        Functor.LaxMonoidal.μ (SheafOfModules.forget (ringCatSheaf R)) _ _ ≫
          (symmetricPowerMul M i j).val =
      PresheafOfModulesOfCommRing.symmetricPowerMul M.val i j ≫
        symmetricPowerUnit (i + j) M := by
  let G := SheafOfModules.forget (ringCatSheaf R)
  let S := PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)
  let P := fun n ↦ (PresheafOfModulesOfCommRing.symmetricPower n).obj M.val
  let η := (TauCeti.SheafOfModules.sheafificationForgetAdjunction R).unit
  -- Work with the monoidal sheafification adjunction; its unit is a monoidal transformation.
  -- `forget.map` is the underlying presheaf morphism; spelling it this way exposes functoriality.
  change ((η.app (P i) ≫ G.map (symmetricPowerIso i M).inv) ⊗ₘ
      (η.app (P j) ≫ G.map (symmetricPowerIso j M).inv)) ≫
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (symmetricPowerMul M i j) = _
  rw [symmetricPowerMul_def, G.map_comp, G.map_comp, G.map_comp,
    ← Functor.LaxMonoidal.μ_natural_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id]
  have h : η.app (P i ⊗ P j) = (η.app (P i) ⊗ₘ η.app (P j)) ≫
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (Functor.LaxMonoidal.μ S (P i) (P j)) :=
    (Category.id_comp _).symm.trans
      (NatTrans.IsMonoidal.tensor (τ := η) (P i) (P j))
  -- The presheaf and commutative-ring presentations agree only after unfolding the coefficient
  -- sheaf, so these functorial identity rewrites require elaborator transparency.
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [CategoryTheory.Functor.map_comp]
  erw [← reassoc_of% h]
  exact (η.naturality_assoc (PresheafOfModulesOfCommRing.symmetricPowerMul M.val i j) _).symm

end

end SheafOfModules
