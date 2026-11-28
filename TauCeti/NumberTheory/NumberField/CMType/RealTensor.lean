/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Algebra.Hom.Rat
public import TauCeti.NumberTheory.NumberField.CMType.Basic
import TauCeti.RingTheory.Etale.Galois
import TauCeti.RingTheory.Etale.Reduced
import TauCeti.RingTheory.Etale.Splitting
import TauCeti.RingTheory.TensorProduct.LiftEquiv

/-!
# The real algebra of a CM type

Let `Φ` be a CM type on a finite reduced rational algebra `E`, for example a product of CM
fields. Evaluation at its selected embeddings identifies `ℝ ⊗[ℚ] E` with `Φ → ℂ`.
The diagonal copy of the complex scalars in these coordinates defines a real algebra map
`ℂ →ₐ[ℝ] ℝ ⊗[ℚ] E`. In this map a selected embedding sees `z` and its conjugate sees
`conj z`. It gives the complex structure on the real algebra used in the CM torus.

## References

* J. S. Milne, *Complex Multiplication*, §1, Definition 1.8 and the following paragraph.
-/

public section

open scoped TensorProduct ComplexConjugate

namespace TauCeti.CMType

variable {E : Type*} [CommRing E] [Algebra ℚ E]

private theorem liftEquiv_star_apply (φ : E →+* ℂ) (x : ℝ ⊗[ℚ] E) :
    AlgHom.liftEquiv ℚ ℝ E ℂ (star φ).toRatAlgHom x =
      conj (AlgHom.liftEquiv ℚ ℝ E ℂ φ.toRatAlgHom x) := by
  have h : (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp φ.toRatAlgHom =
      (star φ).toRatAlgHom := AlgHom.ext fun _ ↦ rfl
  simpa only [h, Algebra.TensorProduct.rTensor, Algebra.TensorProduct.map_id, AlgHom.id_apply,
    AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom, Complex.conjAe_coe] using
    φ.toRatAlgHom.liftEquiv_rTensor_apply (AlgHom.id ℚ ℝ)
      (Complex.conjAe.toAlgHom.restrictScalars ℚ) Complex.conjAe.toAlgHom.commutes x

variable [Module.Finite ℚ E] [IsReduced E]

/-- Evaluation at the embeddings selected by a CM type separates points of the real scalar
extension. -/
private theorem injective_pi_liftEquiv (Φ : CMType E) :
    Function.Injective (AlgHom.pi fun φ : Φ ↦ AlgHom.liftEquiv ℚ ℝ E ℂ φ.val.toRatAlgHom) := by
  classical
  let eval := AlgHom.liftEquiv ℚ ℝ E ℂ
  have : Algebra.Etale ℚ E :=
    algebraEtale_iff_finite_and_isReduced.mpr ⟨inferInstance, inferInstance⟩
  intro x y h
  apply _root_.Algebra.Etale.pi_id_injective ℝ ℂ (ℝ ⊗[ℚ] E)
  funext ψ
  obtain ⟨φ, rfl⟩ := ((RingHom.equivRatAlgHom E ℂ).trans eval).surjective ψ
  -- The missing coordinates are the conjugates of the selected ones.
  by_cases hφ : φ ∈ Φ
  · exact congrFun h ⟨φ, hφ⟩
  · have he := congrFun h (⟨star φ, (Φ.star_mem_iff φ).mpr hφ⟩ : Φ)
    simp only [AlgHom.pi_apply, liftEquiv_star_apply] at he
    exact Function.Involutive.injective Complex.conj_conj he

/-- The real scalar extension and the complex coordinates selected by a CM type have the same
real dimension. -/
private theorem finrank_realTensor_eq (Φ : CMType E) :
    Module.finrank ℝ (ℝ ⊗[ℚ] E) = Module.finrank ℝ (Φ → ℂ) := by
  have : Algebra.Etale ℚ E :=
    algebraEtale_iff_finite_and_isReduced.mpr ⟨inferInstance, inferInstance⟩
  let := Fintype.ofFinite Φ
  rw [Module.finrank_baseChange, ← Algebra.Etale.card_algHom_eq_finrank ℚ E ℂ,
    ← Nat.card_congr (RingHom.equivRatAlgHom E ℂ), Φ.card_ringHom_eq_two_mul]
  simp [Module.finrank_pi_fintype, Nat.card_eq_fintype_card, Nat.mul_comm]

private theorem bijective_pi_liftEquiv (Φ : CMType E) :
    Function.Bijective (AlgHom.pi fun φ : Φ ↦ AlgHom.liftEquiv ℚ ℝ E ℂ φ.val.toRatAlgHom) := by
  let := Fintype.ofFinite Φ
  let f := AlgHom.pi fun φ : Φ ↦ AlgHom.liftEquiv ℚ ℝ E ℂ φ.val.toRatAlgHom
  exact ⟨Φ.injective_pi_liftEquiv,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      Φ.finrank_realTensor_eq).mp Φ.injective_pi_liftEquiv⟩

/-- The decomposition of the real scalar extension into the complex coordinates selected by a
CM type. Its coordinate at `φ` sends `r ⊗ a` to `r * φ(a)`. -/
noncomputable def realTensorEquiv (Φ : CMType E) : ℝ ⊗[ℚ] E ≃ₐ[ℝ] (Φ → ℂ) :=
  AlgEquiv.ofBijective (AlgHom.pi fun φ : Φ ↦ AlgHom.liftEquiv ℚ ℝ E ℂ φ.val.toRatAlgHom)
    (bijective_pi_liftEquiv Φ)

/-- A coordinate of the decomposition is the real-linear extension of its embedding. -/
theorem realTensorEquiv_apply (Φ : CMType E) (x : ℝ ⊗[ℚ] E) (φ : Φ) :
    Φ.realTensorEquiv x φ = AlgHom.liftEquiv ℚ ℝ E ℂ φ.val.toRatAlgHom x := by
  rw [realTensorEquiv, AlgEquiv.ofBijective_apply, AlgHom.pi_apply]

@[simp]
theorem realTensorEquiv_tmul (Φ : CMType E) (r : ℝ) (a : E) (φ : Φ) :
    Φ.realTensorEquiv (r ⊗ₜ[ℚ] a) φ = r * φ.val a := by
  simp [realTensorEquiv_apply, Algebra.smul_def]

/-- The complex scalar action on the real CM algebra. Under the type coordinates it is the
diagonal map from `ℂ`. -/
noncomputable def complexScalarHom (Φ : CMType E) : ℂ →ₐ[ℝ] ℝ ⊗[ℚ] E :=
  Φ.realTensorEquiv.symm.toAlgHom.comp (Pi.constAlgHom ℝ Φ ℂ)

@[simp]
theorem realTensorEquiv_complexScalarHom (Φ : CMType E) (z : ℂ) :
    Φ.realTensorEquiv (Φ.complexScalarHom z) = fun _ ↦ z := by
  ext φ
  simp [complexScalarHom]

/-- At an arbitrary complex embedding the scalar acts by the identity if the embedding is in
the type and by conjugation otherwise. -/
@[simp]
theorem liftEquiv_complexScalarHom (Φ : CMType E) (φ : E →+* ℂ) (z : ℂ)
    [Decidable (φ ∈ Φ)] :
    AlgHom.liftEquiv ℚ ℝ E ℂ φ.toRatAlgHom (Φ.complexScalarHom z) =
      if φ ∈ Φ then z else conj z := by
  split_ifs with hφ
  · simpa only [realTensorEquiv_apply] using
      congrFun (Φ.realTensorEquiv_complexScalarHom z) (⟨φ, hφ⟩ : Φ)
  · have h := congrFun (Φ.realTensorEquiv_complexScalarHom z)
        ⟨star φ, (Φ.star_mem_iff φ).mpr hφ⟩
    rw [realTensorEquiv_apply, liftEquiv_star_apply] at h
    simpa only [Complex.conj_conj] using congrArg (conj : ℂ → ℂ) h

end TauCeti.CMType
