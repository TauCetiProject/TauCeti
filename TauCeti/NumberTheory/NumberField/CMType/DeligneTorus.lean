/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Splitting
public import TauCeti.NumberTheory.NumberField.CMType.RealTensor
import Mathlib.Algebra.Module.Rat
import TauCeti.RingTheory.TensorProduct.LiftEquiv

/-!
# The Deligne homomorphism of a CM type on points

For a CM type `Φ` on `E`, its complex scalar map `ℂ → ℝ ⊗[ℚ] E` induces the homomorphism from
the Deligne torus to the real extension of `Res_{E/ℚ} 𝔾ₘ`. On points over a real algebra `R`
the target is `(R ⊗[ℚ] E)ˣ`. Over a complex algebra the `φ`-coordinate is the first Deligne
coordinate for `φ ∈ Φ` and the second for `φ ∉ Φ`. Thus the associated cocharacter has exponent
one at precisely the embeddings in the type and zero elsewhere.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Example 12.4(b).
-/

public section

open scoped TensorProduct
open Algebra.TensorProduct

namespace TauCeti.CMType

variable {E : Type*} [CommRing E] [Algebra ℚ E] [Module.Finite ℚ E] [IsReduced E]
variable (Φ : CMType E) (R : Type*) [CommRing R] [Algebra ℝ R] [Algebra ℚ R]

/-- Extension of the complex scalar map of `Φ` to a real algebra `R`, on the algebras whose
units give the two tori. -/
noncomputable def deligneScalarHom : ℂ ⊗[ℝ] R →ₐ[ℝ] R ⊗[ℚ] E :=
  productMap ((rTensor E (Algebra.ofId ℝ R)).comp Φ.complexScalarHom) includeLeft

@[simp]
theorem deligneScalarHom_tmul (z : ℂ) (r : R) :
    Φ.deligneScalarHom R (z ⊗ₜ[ℝ] r) =
      rTensor E (Algebra.ofId ℝ R) (Φ.complexScalarHom z) * (r ⊗ₜ[ℚ] 1) := by
  rw [deligneScalarHom, productMap_apply_tmul, AlgHom.comp_apply, includeLeft_apply]

/-- The CM homomorphism `h_Φ` on points with values in a real algebra. -/
noncomputable def delignePoints :
    WithConv (DeligneTorus.S →ₐ[ℝ] R) →* (R ⊗[ℚ] E)ˣ :=
  (Units.map (Φ.deligneScalarHom R).toMonoidHom).comp (DeligneTorus.pointsMulEquiv R).toMonoidHom

@[simp]
theorem coe_delignePoints (f : WithConv (DeligneTorus.S →ₐ[ℝ] R)) :
    (Φ.delignePoints R f : R ⊗[ℚ] E) =
      Φ.deligneScalarHom R (DeligneTorus.pointsMulEquiv R f) :=
  (rfl)

/-- Under the identification of real Deligne points with `ℂˣ`, the CM map is induced by the
complex scalar homomorphism. -/
@[simp]
theorem delignePoints_realPointsMulEquiv_symm (z : ℂˣ) :
    Φ.delignePoints ℝ (DeligneTorus.realPointsMulEquiv.symm z) =
      Units.map Φ.complexScalarHom.toMonoidHom z := by
  apply Units.ext
  simp only [coe_delignePoints, DeligneTorus.pointsMulEquiv_realPointsMulEquiv_symm,
    Units.coe_map, MonoidHom.coe_ofClass, rid_symm_apply,
    deligneScalarHom_tmul, Algebra.ofId_self, rTensor, map_id, AlgHom.id_apply,
    ← Algebra.TensorProduct.one_def, mul_one]
  rfl

variable {R} {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℚ R']

/-- The scalar homomorphism inducing the CM map commutes with maps of real algebras. -/
theorem deligneScalarHom_comp_lTensor (g : R →ₐ[ℝ] R') :
    (Φ.deligneScalarHom R').comp (lTensor ℂ g) =
      (rTensor E g).comp (Φ.deligneScalarHom R) := by
  have hcomp : (rTensor E g).comp (rTensor E (Algebra.ofId ℝ R)) =
      rTensor (R := ℚ) E (Algebra.ofId ℝ R') := by
    simp [← map_comp (R := ℚ)]
  simp only [deligneScalarHom, comp_productMap, ← AlgHom.comp_assoc, hcomp, map_comp_includeLeft]
  exact Algebra.TensorProduct.ext' fun z r ↦ by simp

/-- The CM homomorphism is natural in the real algebra of points. -/
theorem delignePoints_mapValue (g : R →ₐ[ℝ] R') (f : WithConv (DeligneTorus.S →ₐ[ℝ] R)) :
    Φ.delignePoints R' (AlgHom.mapValue g f) =
      Units.map (rTensor E g).toMonoidHom (Φ.delignePoints R f) := by
  apply Units.ext
  simp only [coe_delignePoints, DeligneTorus.pointsMulEquiv_mapValue, Units.coe_map,
    MonoidHom.coe_ofClass]
  exact DFunLike.congr_fun (Φ.deligneScalarHom_comp_lTensor g) _

variable [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- Evaluating the CM scalar homomorphism at an embedding selects the corresponding projection
of the complex tensor splitting. -/
theorem liftEquiv_comp_deligneScalarHom (φ : E →+* ℂ) [Decidable (φ ∈ Φ)] :
    (AlgHom.restrictScalars ℝ
      (AlgHom.liftEquiv ℚ R E R ((IsScalarTower.toAlgHom ℚ ℂ R).comp φ.toRatAlgHom))).comp
        (Φ.deligneScalarHom R) =
      (if φ ∈ Φ then AlgHom.fst ℝ R R else AlgHom.snd ℝ R R).comp
        (complexTensorProductEquivProd R).toAlgHom := by
  -- Use the given real and rational algebras to infer the scalar towers.
  let : Module ℝ R := Algebra.toModule
  let : Module ℚ R := Algebra.toModule
  have hbase (x : ℝ ⊗[ℚ] E) :
      AlgHom.liftEquiv ℚ R E R ((IsScalarTower.toAlgHom ℚ ℂ R).comp φ.toRatAlgHom)
          (rTensor E (Algebra.ofId ℝ R) x) =
        algebraMap ℂ R (AlgHom.liftEquiv ℚ ℝ E ℂ φ.toRatAlgHom x) :=
    φ.toRatAlgHom.liftEquiv_rTensor_apply ((Algebra.ofId ℝ R).restrictScalars ℚ)
      (IsScalarTower.toAlgHom ℚ ℂ R) (fun r ↦ (IsScalarTower.algebraMap_apply ℝ ℂ R r).symm) x
  split_ifs with hφ <;> apply Algebra.TensorProduct.ext' <;> intro z r <;>
    simp [Algebra.smul_def, hbase, hφ]

/-- In split coordinates `h_Φ(z₁,z₂)` has component `z₁` at a selected embedding and `z₂` at
an unselected one. -/
@[simp↓]
theorem liftEquiv_delignePoints (φ : E →+* ℂ) [Decidable (φ ∈ Φ)]
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] R)) :
    AlgHom.liftEquiv ℚ R E R ((IsScalarTower.toAlgHom ℚ ℂ R).comp φ.toRatAlgHom)
        (Φ.delignePoints R f : R ⊗[ℚ] E) =
      if φ ∈ Φ then ((DeligneTorus.complexSplitting R f).1 : R) else
        ((DeligneTorus.complexSplitting R f).2 : R) := by
  have h := DFunLike.congr_fun (Φ.liftEquiv_comp_deligneScalarHom (R := R) φ)
    (DeligneTorus.pointsMulEquiv R f).val
  simp only [coe_delignePoints, DeligneTorus.coe_complexSplitting_fst,
    DeligneTorus.coe_complexSplitting_snd]
  split_ifs at h ⊢ <;> exact h

/-- The CM cocharacter has exponent one on the type and zero on its complement. -/
theorem liftEquiv_delignePoints_mu (φ : E →+* ℂ) [Decidable (φ ∈ Φ)] (z : Rˣ) :
    AlgHom.liftEquiv ℚ R E R ((IsScalarTower.toAlgHom ℚ ℂ R).comp φ.toRatAlgHom)
        (Φ.delignePoints R (DeligneTorus.mu R z) : R ⊗[ℚ] E) =
      if φ ∈ Φ then (z : R) else 1 := by
  simp only [Φ.liftEquiv_delignePoints, DeligneTorus.complexSplitting_mu, Units.val_one]

end TauCeti.CMType
