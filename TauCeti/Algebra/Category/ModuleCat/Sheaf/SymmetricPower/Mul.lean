/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal
public import TauCeti.CategoryTheory.GradedObject.MonObj

/-!
# Multiplication of symmetric powers of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. For a sheaf of `R`-modules `M`, the
symmetric powers `Symⁿ M` are the graded pieces of the symmetric algebra `Sym M = ⨁ₙ Symⁿ M`.
This file constructs its multiplication
`SheafOfModules.symmetricPowerMul M i j : Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M`
in the symmetric monoidal category of sheaves of `R`-modules: it is the sheafification of the
sectionwise multiplication `PresheafOfModulesOfCommRing.symmetricPowerMul`, composed with the
tensor comparison of the monoidal functor sheafification.

Together with the unit `R ≅ Sym⁰ M` of `SheafOfModules.symmetricPowerZeroIso`, the multiplication
is natural in `M` and satisfies the graded unit, associativity and commutativity laws. These are
the homogeneous laws taken by `CategoryTheory.GradedObject.monObjOfHomogeneous` and
`CategoryTheory.GradedObject.isCommMonObj_monObjOfHomogeneous`, which assemble such data into a
commutative algebra object in graded objects; on a scheme this is the input for the graded
symmetric algebra of an `𝒪_X`-module, whose relative spectrum is the associated linear scheme.
The laws are transported from the sectionwise ones along sheafification, which is a braided
monoidal functor.

## Main declarations

* `SheafOfModules.symmetricPowerMul`: the multiplication `Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M`, with
  defining equation `SheafOfModules.symmetricPowerMul_def`;
* `SheafOfModules.symmetricPowerMul_naturality`: naturality in `M`;
* `SheafOfModules.epi_symmetricPowerMul`: the multiplication is an epimorphism; in particular so
  is `Symⁿ M ⊗ Sym¹ M ⟶ Symⁿ⁺¹ M`, which is the sense in which the symmetric algebra is generated
  in degree one;
* `SheafOfModules.symmetricPowerMul_assoc`, `symmetricPowerMul_comm`,
  `symmetricPowerMul_one_mul` and `symmetricPowerMul_mul_one`: the graded associativity,
  commutativity and unit laws;
* `TauCeti.SheafOfModules.symmetricPowerLift_mul`: sheafifying sectionwise maps out of symmetric
  powers preserves compatibility with multiplications.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

namespace SheafOfModules

/-- The multiplication `Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M` of symmetric powers of a sheaf of modules:
the sheafification of the sectionwise multiplication of symmetric powers, preceded by the tensor
comparison of sheafification. -/
def symmetricPowerMul (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (symmetricPower R i).obj M ⊗ (symmetricPower R j).obj M ⟶ (symmetricPower R (i + j)).obj M :=
  ((symmetricPowerIso i M).hom ⊗ₘ (symmetricPowerIso j M).hom) ≫
    Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) _ _ ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        (PresheafOfModulesOfCommRing.symmetricPowerMul M.val i j) ≫
      (symmetricPowerIso (i + j) M).inv

/-- The defining equation of the multiplication of symmetric powers of a sheaf of modules, through
the identifications `symmetricPowerIso` of symmetric powers with sheafified sectionwise symmetric
powers. -/
theorem symmetricPowerMul_def (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    symmetricPowerMul M i j =
      ((symmetricPowerIso i M).hom ⊗ₘ (symmetricPowerIso j M).hom) ≫
        Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) _ _ ≫
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
            (PresheafOfModulesOfCommRing.symmetricPowerMul M.val i j) ≫
          (symmetricPowerIso (i + j) M).inv :=
  (rfl)

/-- The multiplication of symmetric powers is natural in the sheaf of modules. -/
@[reassoc]
theorem symmetricPowerMul_naturality {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N)
    (i j : ℕ) :
    ((symmetricPower R i).map φ ⊗ₘ (symmetricPower R j).map φ) ≫ symmetricPowerMul N i j =
      symmetricPowerMul M i j ≫ (symmetricPower R (i + j)).map φ :=
  GradedObject.map_mul_of_laxMonoidal (Y := fun n ↦ (symmetricPower R n).obj M)
    (e := fun n ↦ symmetricPowerIso n M) _ _ (symmetricPowerMul_def M)
    (Y' := fun n ↦ (symmetricPower R n).obj N) (e' := fun n ↦ symmetricPowerIso n N) _ _
    (symmetricPowerMul_def N) _ _ (fun n ↦ symmetricPower_map n φ)
    (PresheafOfModulesOfCommRing.symmetricPowerMul_naturality φ.val) i j

/-- The multiplication of symmetric powers of a sheaf of modules is an epimorphism: it is the
sheafification of the sectionwise multiplication, which is an epimorphism, up to isomorphisms. -/
instance epi_symmetricPowerMul (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    Epi (symmetricPowerMul M i j) := by
  rw [symmetricPowerMul_def]
  -- The sectionwise multiplication and the tensor comparison of sheafification are stated for
  -- presheaves of modules over `R.obj ⋙ forget₂ _ _` rather than `(ringCatSheaf R).obj`; the two
  -- agree only after unfolding `sheafCompose`, so their instances are supplied by hand.
  refine epi_comp' inferInstance (epi_comp' ?_ (epi_comp' ?_ inferInstance))
  · exact (Functor.Monoidal.μIso _ _ _).isIso_hom.epi_of_iso
  · exact @Functor.map_epi _ _ _ _ _ _ _ _ _
      (PresheafOfModulesOfCommRing.epi_symmetricPowerMul M.val i j)

/-- The unit `R ≅ Sym⁰ M` is the sheafification of the sectionwise unit, preceded by the unit
comparison of sheafification. -/
private theorem symmetricPowerZeroIso_inv_app_eq (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (symmetricPowerZeroIso R).inv.app M =
      Functor.LaxMonoidal.ε (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.symmetricPowerZeroIso R.obj).inv.app M.val) ≫
        (symmetricPowerIso 0 M).inv := by
  rw [symmetricPowerZeroIso_inv_app, TauCeti.SheafOfModules.sheafification_ε]
  congr 1
  -- Both isomorphisms are the counit of the sheafification adjunction at the structure sheaf; their
  -- sources agree only up to the definitional identification of the unit presheaf of modules.
  exact (Iso.inv_eq_inv _ _).2 ((TauCeti.SheafOfModules.sheafificationIso_hom _ _).trans
    (TauCeti.SheafOfModules.sheafificationUnitIso_hom R).symm)

/-- The multiplication of symmetric powers of a sheaf of modules is associative, up to the
identification of the degrees `i + (j + k)` and `i + j + k`. -/
@[reassoc]
theorem symmetricPowerMul_assoc (M : SheafOfModules.{u} (ringCatSheaf R)) (i j k : ℕ) :
    (symmetricPowerMul M i j ▷ (symmetricPower R k).obj M) ≫ symmetricPowerMul M (i + j) k =
      (α_ _ _ _).hom ≫ ((symmetricPower R i).obj M ◁ symmetricPowerMul M j k) ≫
        symmetricPowerMul M i (j + k) ≫
          eqToHom (congrArg (fun n ↦ (symmetricPower R n).obj M) (add_assoc i j k).symm) :=
  GradedObject.mul_assoc_of_laxMonoidal (Y := fun n ↦ (symmetricPower R n).obj M)
    (e := fun n ↦ symmetricPowerIso n M) _ _ (symmetricPowerMul_def M)
    (PresheafOfModulesOfCommRing.symmetricPowerMul_assoc M.val) i j k

/-- The multiplication of symmetric powers of a sheaf of modules is commutative, up to the
identification of the degrees `i + j` and `j + i`. -/
@[reassoc]
theorem symmetricPowerMul_comm (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (β_ ((symmetricPower R i).obj M) ((symmetricPower R j).obj M)).hom ≫
        symmetricPowerMul M j i =
      symmetricPowerMul M i j ≫
        eqToHom (congrArg (fun n ↦ (symmetricPower R n).obj M) (add_comm i j)) :=
  GradedObject.mul_comm_of_laxBraided (Y := fun n ↦ (symmetricPower R n).obj M)
    (e := fun n ↦ symmetricPowerIso n M) _ _ (symmetricPowerMul_def M)
    (PresheafOfModulesOfCommRing.symmetricPowerMul_comm M.val) i j

/-- The unit `R ≅ Sym⁰ M` is a left identity for the multiplication of symmetric powers, up to
the identification of the degrees `0 + n` and `n`. -/
@[reassoc]
theorem symmetricPowerMul_one_mul (M : SheafOfModules.{u} (ringCatSheaf R)) (n : ℕ) :
    ((symmetricPowerZeroIso R).inv.app M ▷ (symmetricPower R n).obj M) ≫
        symmetricPowerMul M 0 n =
      (λ_ ((symmetricPower R n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (symmetricPower R n).obj M) (zero_add n).symm) :=
  GradedObject.one_mul_of_laxMonoidal (Y := fun n ↦ (symmetricPower R n).obj M)
    (e := fun n ↦ symmetricPowerIso n M) _ _ (symmetricPowerMul_def M) _ _
    (symmetricPowerZeroIso_inv_app_eq M)
    (PresheafOfModulesOfCommRing.symmetricPowerMul_one_mul M.val) n

/-- The unit `R ≅ Sym⁰ M` is a right identity for the multiplication of symmetric powers, up to
the identification of the degrees `n + 0` and `n`. -/
@[reassoc]
theorem symmetricPowerMul_mul_one (M : SheafOfModules.{u} (ringCatSheaf R)) (n : ℕ) :
    ((symmetricPower R n).obj M ◁ (symmetricPowerZeroIso R).inv.app M) ≫
        symmetricPowerMul M n 0 =
      (ρ_ ((symmetricPower R n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (symmetricPower R n).obj M) (add_zero n).symm) :=
  GradedObject.mul_one_of_laxMonoidal (Y := fun n ↦ (symmetricPower R n).obj M)
    (e := fun n ↦ symmetricPowerIso n M) _ _ (symmetricPowerMul_def M) _ _
    (symmetricPowerZeroIso_inv_app_eq M)
    (PresheafOfModulesOfCommRing.symmetricPowerMul_mul_one M.val) n

end SheafOfModules

namespace TauCeti.SheafOfModules

open _root_.SheafOfModules

/-- Sectionwise maps out of symmetric powers compatible with the multiplications lift along
sheafification to maps compatible with the multiplications. -/
theorem symmetricPowerLift_mul {M : _root_.SheafOfModules.{u} (ringCatSheaf R)}
    {B : ℕ → _root_.SheafOfModules.{u} (ringCatSheaf R)}
    (ψ : ∀ n, (PresheafOfModulesOfCommRing.symmetricPower n).obj M.val ⟶ (B n).val)
    (mul : ∀ i j, B i ⊗ B j ⟶ B (i + j))
    (h : ∀ i j, (ψ i ⊗ₘ ψ j) ≫
      Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) (B i) (B j) ≫
        (mul i j).val = PresheafOfModulesOfCommRing.symmetricPowerMul M.val i j ≫ ψ (i + j))
    (i j : ℕ) :
    (symmetricPowerLift (ψ i) ⊗ₘ symmetricPowerLift (ψ j)) ≫ mul i j =
      symmetricPowerMul M i j ≫ symmetricPowerLift (ψ (i + j)) := by
  refine GradedObject.map_mul_of_laxMonoidal
    (F := PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))
    (e := fun n ↦ symmetricPowerIso n M) _ _ (symmetricPowerMul_def M)
    (e' := fun n ↦ (sheafificationIso _ (B n)).symm)
    (fun i j ↦ Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) (B i) (B j) ≫
      (mul i j).val) mul (fun i j ↦ ?_) ψ (fun n ↦ symmetricPowerLift (ψ n))
    (fun n ↦ symmetricPowerLift_def (ψ n)) h i j
  have h : ((sheafificationForgetAdjunction R).homEquiv _ _).symm
      (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) (B i) (B j) ≫
        (mul i j).val) = ((B i).tensorUnderlyingIso (B j)).inv ≫ mul i j :=
    (Equiv.symm_apply_eq _).2 (forget_μ_comp_map (mul i j))
  rw [Adjunction.homEquiv_counit, sheafificationForgetAdjunction_counit_app] at h
  rw [Iso.symm_hom, Iso.symm_hom, Iso.symm_inv]
  -- `h` displays the source of the sheafified map as `forget.obj (B i) ⊗ forget.obj (B j)`, the
  -- goal as `(B i).val ⊗ (B j).val`; these agree only up to unfolding `forget`.
  erw [h]
  rw [← Category.assoc, ← _root_.SheafOfModules.tensorUnderlyingIso_hom, Iso.hom_inv_id_assoc]

end TauCeti.SheafOfModules
