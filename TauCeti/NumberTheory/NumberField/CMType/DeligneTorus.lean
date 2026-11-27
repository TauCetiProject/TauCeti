/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Splitting
public import TauCeti.NumberTheory.NumberField.CMType.RealTensor

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

variable {R} {R' : Type*} [CommRing R'] [Algebra ℝ R'] [Algebra ℚ R']

/-- The CM homomorphism is natural in the real algebra of points. -/
theorem delignePoints_mapValue (g : R →ₐ[ℝ] R') (f : WithConv (DeligneTorus.S →ₐ[ℝ] R)) :
    Φ.delignePoints R' (AlgHom.mapValue g f) =
      Units.map (rTensor E g).toMonoidHom (Φ.delignePoints R f) := by
  apply Units.ext
  simp only [coe_delignePoints, DeligneTorus.pointsMulEquiv_mapValue, Units.coe_map,
    MonoidHom.coe_ofClass]
  generalize (DeligneTorus.pointsMulEquiv R f).val = x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul z r =>
    have hcomp := map_comp g (Algebra.ofId ℝ R) (AlgHom.id ℚ E) (AlgHom.id ℚ E)
    simp only [map_tmul, AlgHom.id_apply, deligneScalarHom_tmul, map_mul]
    congr 1
    rw [Algebra.comp_ofId, AlgHom.id_comp] at hcomp
    exact DFunLike.congr_fun hcomp (Φ.complexScalarHom z)

variable [Algebra ℂ R] [IsScalarTower ℝ ℂ R]

/-- In split coordinates `h_Φ(z₁,z₂)` has component `z₁` at a selected embedding and `z₂` at
an unselected one. -/
@[simp↓]
theorem liftEquiv_delignePoints (φ : E →+* ℂ) [Decidable (φ ∈ Φ)]
    (f : WithConv (DeligneTorus.S →ₐ[ℝ] R)) :
    AlgHom.liftEquiv ℚ R E R ((IsScalarTower.toAlgHom ℚ ℂ R).comp φ.toRatAlgHom)
        (Φ.delignePoints R f : R ⊗[ℚ] E) =
      if φ ∈ Φ then ((DeligneTorus.complexSplitting R f).1 : R) else
        ((DeligneTorus.complexSplitting R f).2 : R) := by
  rw [coe_delignePoints]
  simp only [DeligneTorus.coe_complexSplitting_fst, DeligneTorus.coe_complexSplitting_snd]
  generalize (DeligneTorus.pointsMulEquiv R f).val = x
  have : IsScalarTower ℚ ℝ R := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  -- Evaluating a real tensor after extension to R gives its original complex value in R.
  have he (b : ℝ ⊗[ℚ] E) :
      AlgHom.liftEquiv ℚ R E R ((IsScalarTower.toAlgHom ℚ ℂ R).comp φ.toRatAlgHom)
          (rTensor E (Algebra.ofId ℝ R) b) =
      algebraMap ℂ R (AlgHom.liftEquiv ℚ ℝ E ℂ φ.toRatAlgHom b) := by
    induction b using TensorProduct.inductionOn with
    | add b c hb hc => simp [hb, hc]
    | tmul r a => simp [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ ℂ R]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => split_ifs at * <;> simp [hx, hy]
  | tmul z r =>
    simp only [deligneScalarHom_tmul, map_mul, he, liftEquiv_complexScalarHom,
      AlgHom.liftEquiv_tmul, complexTensorProductEquivProd_tmul]
    split_ifs <;> simp [Algebra.smul_def]

/-- The CM cocharacter has exponent one on the type and zero on its complement. -/
theorem liftEquiv_delignePoints_mu (φ : E →+* ℂ) [Decidable (φ ∈ Φ)] (z : Rˣ) :
    AlgHom.liftEquiv ℚ R E R ((IsScalarTower.toAlgHom ℚ ℂ R).comp φ.toRatAlgHom)
        (Φ.delignePoints R (DeligneTorus.mu R z) : R ⊗[ℚ] E) =
      if φ ∈ Φ then (z : R) else 1 := by
  simp only [Φ.liftEquiv_delignePoints, DeligneTorus.complexSplitting_mu, Units.val_one]

end TauCeti.CMType
