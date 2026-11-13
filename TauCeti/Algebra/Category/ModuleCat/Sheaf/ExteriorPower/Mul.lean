/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Mul
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal
public import TauCeti.CategoryTheory.GradedObject.MonObj

/-!
# Exterior multiplication of module sheaves

For a sheaf of modules `M` over a sheaf of commutative rings, exterior multiplication is
`⋀ⁱ M ⊗ ⋀ʲ M ⟶ ⋀ⁱ⁺ʲ M`. It is natural in `M`, associative and unital through `⋀⁰ M ≅ R`,
and graded commutative with sign `(-1)^(i*j)`. On a scheme these maps live in the canonical
monoidal category `X.Modules`, and supply the wedge multiplication used in determinants of
extensions of locally free sheaves.

Following `SheafOfModules.symmetricPowerMul`, the construction sheafifies the sectionwise
product and precomposes with the tensor comparison of monoidal sheafification. The laws
are transported from the sectionwise exterior products along this braided monoidal functor.

## References

* The Stacks Project, *Sheaves of Modules*, Tags 01CF and 01CG.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- Exterior multiplication of sheaves of modules, induced by sectionwise wedge multiplication. -/
def exteriorPowerMul (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (exteriorPower R i).obj M ⊗ (exteriorPower R j).obj M ⟶ (exteriorPower R (i + j)).obj M :=
  ((exteriorPowerIso i M).hom ⊗ₘ (exteriorPowerIso j M).hom) ≫
    Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) _ _ ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        (PresheafOfModulesOfCommRing.exteriorPowerMul M.val i j) ≫
      (exteriorPowerIso (i + j) M).inv

/-- Exterior multiplication is sheafified sectionwise multiplication, through `exteriorPowerIso`
and the tensor comparison of sheafification. -/
theorem exteriorPowerMul_def (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    exteriorPowerMul M i j =
      ((exteriorPowerIso i M).hom ⊗ₘ (exteriorPowerIso j M).hom) ≫
        Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) _ _ ≫
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
            (PresheafOfModulesOfCommRing.exteriorPowerMul M.val i j) ≫
          (exteriorPowerIso (i + j) M).inv :=
  (rfl)

/-- Exterior multiplication is natural in the sheaf of modules. -/
@[reassoc]
theorem exteriorPowerMul_naturality {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N)
    (i j : ℕ) :
    ((exteriorPower R i).map φ ⊗ₘ (exteriorPower R j).map φ) ≫ exteriorPowerMul N i j =
      exteriorPowerMul M i j ≫ (exteriorPower R (i + j)).map φ :=
  GradedObject.map_mul_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M)
    (Y' := fun n ↦ (exteriorPower R n).obj N) (e' := fun n ↦ exteriorPowerIso n N) _ _
    (exteriorPowerMul_def N) _ _ (fun n ↦ exteriorPower_map n φ)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_naturality φ.val) i j

/-- The unit is the sheafification of the sectionwise unit. -/
private theorem exteriorPowerZeroIso_inv_app_eq (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (exteriorPowerZeroIso R).inv.app M =
      Functor.LaxMonoidal.ε (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.exteriorPowerZeroIso R.obj).inv.app M.val) ≫
        (exteriorPowerIso 0 M).inv := by
  rw [exteriorPowerZeroIso_inv_app]
  congr 1
  exact TauCeti.SheafOfModules.sheafificationIso_unit_inv R

/-- Exterior multiplication is associative, with the canonical identification of degrees. -/
@[reassoc]
theorem exteriorPowerMul_assoc (M : SheafOfModules.{u} (ringCatSheaf R)) (i j k : ℕ) :
    (exteriorPowerMul M i j ▷ (exteriorPower R k).obj M) ≫ exteriorPowerMul M (i + j) k =
      (α_ _ _ _).hom ≫ ((exteriorPower R i).obj M ◁ exteriorPowerMul M j k) ≫
        exteriorPowerMul M i (j + k) ≫
          eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (add_assoc i j k).symm) :=
  GradedObject.mul_assoc_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_assoc M.val) i j k

/-- Swapping the exterior factors introduces the Koszul sign. -/
@[reassoc]
theorem exteriorPowerMul_comm (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (β_ ((exteriorPower R i).obj M) ((exteriorPower R j).obj M)).hom ≫
        exteriorPowerMul M j i =
      (-1 : ℤ) ^ (i * j) • (exteriorPowerMul M i j ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (add_comm i j))) := by
  let F := PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have := F.additive_of_preservesBinaryBiproducts
  exact GradedObject.mul_comm_zsmul_of_laxBraided
    (Y := fun n ↦ (exteriorPower R n).obj M) (e := fun n ↦ exteriorPowerIso n M)
    _ _ (exteriorPowerMul_def M) (fun i j ↦ (-1 : ℤ) ^ (i * j))
    (PresheafOfModulesOfCommRing.exteriorPowerMul_comm M.val) i j

/-- The zeroth exterior power is a left unit for exterior multiplication. -/
@[reassoc]
theorem exteriorPowerMul_one_mul (M : SheafOfModules.{u} (ringCatSheaf R)) (n : ℕ) :
    ((exteriorPowerZeroIso R).inv.app M ▷ (exteriorPower R n).obj M) ≫
        exteriorPowerMul M 0 n =
      (λ_ ((exteriorPower R n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (zero_add n).symm) :=
  GradedObject.one_mul_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M) _ _
    (exteriorPowerZeroIso_inv_app_eq M)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_one_mul M.val) n

/-- The zeroth exterior power is a right unit for exterior multiplication. -/
@[reassoc]
theorem exteriorPowerMul_mul_one (M : SheafOfModules.{u} (ringCatSheaf R)) (n : ℕ) :
    ((exteriorPower R n).obj M ◁ (exteriorPowerZeroIso R).inv.app M) ≫
        exteriorPowerMul M n 0 =
      (ρ_ ((exteriorPower R n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower R n).obj M) (add_zero n).symm) :=
  GradedObject.mul_one_of_laxMonoidal (Y := fun n ↦ (exteriorPower R n).obj M)
    (e := fun n ↦ exteriorPowerIso n M) _ _ (exteriorPowerMul_def M) _ _
    (exteriorPowerZeroIso_inv_app_eq M)
    (PresheafOfModulesOfCommRing.exteriorPowerMul_mul_one M.val) n

end SheafOfModules
