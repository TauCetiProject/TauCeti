/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
import TauCeti.CategoryTheory.Monoidal.Mod.Basic

/-!
# Scheme actions from comodule algebras

A right comodule algebra represents a right action. Composing its group coordinate with
inversion gives a left action on the same affine scheme, with Mathlib's native `ModObj` structure.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace TauCeti.ComoduleAlgebra

universe u

noncomputable section

section Bialgebra

variable (R H A : Type u) [CommRing R] [CommRing H] [Bialgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]

/-- The represented right action before conversion to a left action. -/
private def rightAction :
    op (CommAlgCat.of R A) ⊗ op (CommAlgCat.of R H) ⟶ op (CommAlgCat.of R A) :=
  (CommAlgCat.ofHom (coactAlgHom R H A)).op

private theorem rightAction_one :
    (op (CommAlgCat.of R A)) ◁ MonObj.one ≫ rightAction R H A =
      (ρ_ (op (CommAlgCat.of R A))).hom := by
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  ext a
  -- Opposite morphisms and their tensor unitors reduce to the coordinate algebra maps.
  change (Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.counitAlgHom R H))
    (coactAlgHom R H A a) = a ⊗ₜ[R] 1
  rw [coactAlgHom_apply]
  -- The underlying linear tensor map is precisely the comodule counit contraction.
  change TensorProduct.map LinearMap.id (Coalgebra.counit (R := R))
    (Comodule.coact (R := R) (C := H) a) = _
  exact Comodule.lTensor_counit_coact (R := R) (C := H) a

private theorem rightAction_mul :
    (rightAction R H A ▷ op (CommAlgCat.of R H)) ≫ rightAction R H A =
      (α_ (op (CommAlgCat.of R A)) (op (CommAlgCat.of R H))
        (op (CommAlgCat.of R H))).hom ≫
      (op (CommAlgCat.of R A)) ◁ MonObj.mul ≫ rightAction R H A := by
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  ext a
  -- The opposite associator becomes the inverse tensor associator on coordinates.
  change (Algebra.TensorProduct.map (coactAlgHom R H A) (AlgHom.id R H))
      (coactAlgHom R H A a) =
    (Algebra.TensorProduct.assoc R R R A H H).symm
      ((Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.comulAlgHom R H))
        (coactAlgHom R H A a))
  rw [coactAlgHom_apply]
  -- Expose only the linear tensor maps needed by the public coassociativity equation.
  change TensorProduct.map (coactAlgHom R H A).toLinearMap LinearMap.id
      (Comodule.coact (R := R) (C := H) a) =
    (TensorProduct.assoc R A H H).symm
      ((Coalgebra.comul (R := R)).lTensor A (Comodule.coact a))
  rw [toLinearMap_coactAlgHom]
  exact (Comodule.coassoc_symm_apply (R := R) (C := H) a).symm

private theorem lift_rightAction_one {Z : (CommAlgCat.{u} R)ᵒᵖ}
    (x : Z ⟶ op (CommAlgCat.of R A)) (e : Z ⟶ 𝟙_ _) :
    lift x (e ≫ MonObj.one) ≫ rightAction R H A = x := by
  have h := lift x e ≫= rightAction_one R H A
  simpa using h

private theorem lift_rightAction_mul {Z : (CommAlgCat.{u} R)ᵒᵖ}
    (x : Z ⟶ op (CommAlgCat.of R A))
    (g h : Z ⟶ op (CommAlgCat.of R H)) :
    lift (lift x g ≫ rightAction R H A) h ≫ rightAction R H A =
      lift x (g * h) ≫ rightAction R H A := by
  have h := lift (lift x g) h ≫= rightAction_mul R H A
  simpa only [Category.assoc, lift_whiskerRight_assoc,
    lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, Hom.mul_def] using h

end Bialgebra

variable (R H A : Type u) [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]

/-- Reuse Mathlib's braided spectrum functor with its bundled base fixed to `CommRingCat.of R`,
so instance search does not need to recover that bundled base from its carrier. -/
local instance algSpecBraided : (AlgebraicGeometry.algSpec (CommRingCat.of R)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

/-- The left action on the opposite coordinate algebra, obtained from the right action by
inverting the group coordinate. -/
@[instance_reducible]
private def coordinateModObj :
    ModObj (op (CommAlgCat.of R H)) (op (CommAlgCat.of R A)) where
  smul := lift (snd _ _) (fst _ _)⁻¹ ≫ rightAction R H A
  one_smul := by
    -- The self-action of the monoidal category is its tensor product.
    change (MonObj.one ▷ op (CommAlgCat.of R A)) ≫ _ = (λ_ _).hom
    simp only [comp_lift_assoc, GrpObj.comp_inv, whiskerRight_snd, whiskerRight_fst]
    rw [Hom.inv_def, Category.assoc, GrpObj.one_inv]
    simpa only [leftUnitor_hom] using
      lift_rightAction_one R H A (snd (𝟙_ _) _) (fst (𝟙_ _) _)
  mul_smul := by
    -- Expose the self-action associator before using cartesian projection laws.
    change (MonObj.mul ▷ op (CommAlgCat.of R A)) ≫ _ =
      (α_ _ _ _).hom ≫ (op (CommAlgCat.of R H)) ◁ _ ≫ _
    simp only [comp_lift_assoc, whiskerRight_snd, whiskerRight_fst,
      GrpObj.comp_inv, whiskerLeft_fst, whiskerLeft_snd,
      associator_hom_fst, associator_hom_snd_fst, associator_hom_snd_snd]
    have hmul : fst (op (CommAlgCat.of R H) ⊗ op (CommAlgCat.of R H))
        (op (CommAlgCat.of R A)) ≫ MonObj.mul =
        (fst _ _ ≫ fst _ _) * (fst _ _ ≫ snd _ _) := by
      rw [← MonObj.comp_mul, MonObj.mul_eq_mul]
    rw [hmul]
    rw [mul_inv_rev]
    exact (lift_rightAction_mul R H A (snd _ _)
      (fst _ _ ≫ snd _ _)⁻¹ (fst _ _ ≫ fst _ _)⁻¹).symm

/-- The native action on the relative spectrum of a commutative Hopf comodule algebra. -/
@[instance_reducible]
def specModObj :
    ModObj ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (op (CommHopfAlgCat.of R H))).X
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) := by
  let := coordinateModObj R H A
  exact (AlgebraicGeometry.algSpec (CommRingCat.of R)).modObjObj
    (op (CommAlgCat.of R H)) (op (CommAlgCat.of R A))

/-- The action is the spectrum of the coaction after flipping and inverting its group leg. -/
theorem specModObj_smul :
    letI : ModObj
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R H)))
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) :=
        specModObj R H A
    ModObj.smul
      (M := (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R H)))
      (X := (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) =
      Functor.LaxMonoidal.μ (AlgebraicGeometry.algSpec (CommRingCat.of R))
        (op (CommAlgCat.of R H)) (op (CommAlgCat.of R A)) ≫
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).map
        (lift (snd _ _) (fst _ _)⁻¹ ≫ (CommAlgCat.ofHom (coactAlgHom R H A)).op) := by
  let := coordinateModObj R H A
  exact (AlgebraicGeometry.algSpec (CommRingCat.of R)).modObjObj_smul
    (op (CommAlgCat.of R H)) (op (CommAlgCat.of R A))

/-- The action on algebra-valued points evaluates the original coaction against the inverse
group point. -/
theorem specModObj_smul_map (T : Type u) [CommRing T] [Algebra R T]
    (g : H →ₐ[R] T) (x : A →ₐ[R] T) :
    letI : ModObj
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R H)))
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) :=
        specModObj R H A
    (AlgebraicGeometry.algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op •
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom x).op =
    (AlgebraicGeometry.algSpec (CommRingCat.of R)).map
      (CommAlgCat.ofHom ((Algebra.TensorProduct.lift x
        (g.comp (HopfAlgebra.antipodeAlgHom R H)) (fun _ _ ↦ Commute.all _ _)).comp
          (coactAlgHom R H A))).op := by
  let : ModObj
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R H)))
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))) :=
        specModObj R H A
  rw [Hom.smul_def, specModObj_smul, ← Category.assoc, Functor.Monoidal.lift_μ,
    ← Functor.map_comp]
  congr 1
  simp only [comp_lift_assoc, GrpObj.comp_inv, lift_snd, lift_fst]
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  simp only [unop_comp, Quiver.Hom.unop_op, CommAlgCat.hom_comp, CommAlgCat.lift_unop_hom,
    Hom.inv_def, CommAlgCat.inv_op_of_unop_hom, CommAlgCat.hom_ofHom]

variable {R H A} {B : Type u} [CommRing B] [Algebra R B] [ComoduleAlgebra R H B]

private theorem coordinateModObj_isModHom (f : A →ₐ[R] B)
    (hf : (coactAlgHom R H B).comp f =
      (Algebra.TensorProduct.map f (AlgHom.id R H)).comp (coactAlgHom R H A)) :
    letI := coordinateModObj R H A
    letI := coordinateModObj R H B
    IsModHom (op (CommAlgCat.of R H)) (CommAlgCat.ofHom f).op := by
  let := coordinateModObj R H A
  let := coordinateModObj R H B
  have hright : rightAction R H B ≫ (CommAlgCat.ofHom f).op =
      ((CommAlgCat.ofHom f).op ▷ op (CommAlgCat.of R H)) ≫ rightAction R H A := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact hf
  constructor
  -- Express the two self-action maps using their cartesian product projections.
  change (lift (snd _ _) (fst _ _)⁻¹ ≫ rightAction R H B) ≫ _ =
    (op (CommAlgCat.of R H)) ◁ _ ≫ lift (snd _ _) (fst _ _)⁻¹ ≫ rightAction R H A
  simp only [Category.assoc, hright, lift_whiskerRight_assoc, comp_lift_assoc,
    GrpObj.comp_inv, whiskerLeft_snd, whiskerLeft_fst]

/-- A colinear algebra homomorphism induces an equivariant morphism of affine schemes. -/
theorem specModObj_isModHom (f : A →ₐ[R] B)
    (hf : (coactAlgHom R H B).comp f =
      (Algebra.TensorProduct.map f (AlgHom.id R H)).comp (coactAlgHom R H A)) :
    letI := specModObj R H A
    letI := specModObj R H B
    IsModHom ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (op (CommHopfAlgCat.of R H))).X
      ((AlgebraicGeometry.algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op) := by
  let := coordinateModObj R H A
  let := coordinateModObj R H B
  let := coordinateModObj_isModHom f hf
  exact (AlgebraicGeometry.algSpec (CommRingCat.of R)).modObjObj_isModHom
    (op (CommAlgCat.of R H)) (CommAlgCat.ofHom f).op

end

end TauCeti.ComoduleAlgebra
