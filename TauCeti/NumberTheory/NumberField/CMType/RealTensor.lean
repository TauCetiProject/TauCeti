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

/-- Evaluating a real tensor at the conjugate embedding conjugates its value. -/
private theorem liftEquiv_star_apply {E : Type*} [Ring E] [Algebra ℚ E]
    (φ : E →+* ℂ) (x : ℝ ⊗[ℚ] E) :
    AlgHom.liftEquiv ℚ ℝ E ℂ (star φ).toRatAlgHom x =
      conj (AlgHom.liftEquiv ℚ ℝ E ℂ φ.toRatAlgHom x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r a =>
    simp only [AlgHom.liftEquiv_tmul, RingHom.toRatAlgHom_apply, RingHom.star_apply,
      ← starRingEnd_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]

variable {E : Type*} [CommRing E] [Algebra ℚ E] [Module.Finite ℚ E] [IsReduced E]

/-- The decomposition of the real scalar extension into the complex coordinates selected by a
CM type. Its coordinate at `φ` sends `r ⊗ a` to `r * φ(a)`. -/
noncomputable def realTensorEquiv (Φ : CMType E) : ℝ ⊗[ℚ] E ≃ₐ[ℝ] (Φ → ℂ) := by
  classical
  let eval := AlgHom.liftEquiv ℚ ℝ E ℂ
  let f := AlgHom.pi fun φ : Φ ↦ eval φ.val.toRatAlgHom
  have : Algebra.Etale ℚ E :=
    algebraEtale_iff_finite_and_isReduced.mpr ⟨inferInstance, inferInstance⟩
  -- The missing coordinates are the conjugates of the selected ones.
  have hinj : Function.Injective f := by
    intro x y h
    apply _root_.Algebra.Etale.pi_id_injective ℝ ℂ (ℝ ⊗[ℚ] E)
    funext ψ
    obtain ⟨φ, rfl⟩ := ((RingHom.equivRatAlgHom E ℂ).trans eval).surjective ψ
    by_cases hφ : φ ∈ Φ
    · exact congrFun h ⟨φ, hφ⟩
    · have he : eval (star φ).toRatAlgHom x = eval (star φ).toRatAlgHom y :=
        congrFun h ⟨star φ, (Φ.star_mem_iff φ).mpr hφ⟩
      rw [liftEquiv_star_apply, liftEquiv_star_apply] at he
      exact Function.Involutive.injective Complex.conj_conj he
  letI := Fintype.ofFinite Φ
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] E) = Module.finrank ℝ (Φ → ℂ) := by
    rw [Module.finrank_baseChange, ← Algebra.Etale.card_algHom_eq_finrank ℚ E ℂ,
      ← Nat.card_congr (RingHom.equivRatAlgHom E ℂ), Φ.card_ringHom_eq_two_mul]
    simp [Module.finrank_pi_fintype, Nat.card_eq_fintype_card, Nat.mul_comm]
  exact AlgEquiv.ofBijective f ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hdim).mp hinj⟩

/-- A coordinate of the decomposition is the real-linear extension of its embedding. -/
theorem realTensorEquiv_apply (Φ : CMType E) (x : ℝ ⊗[ℚ] E) (φ : Φ) :
    Φ.realTensorEquiv x φ = AlgHom.liftEquiv ℚ ℝ E ℂ φ.val.toRatAlgHom x :=
  (rfl)

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
  · exact congrFun (Φ.realTensorEquiv_complexScalarHom z) ⟨φ, hφ⟩
  · have h := congrFun (Φ.realTensorEquiv_complexScalarHom z)
        ⟨star φ, (Φ.star_mem_iff φ).mpr hφ⟩
    rw [realTensorEquiv_apply, liftEquiv_star_apply] at h
    simpa only [Complex.conj_conj] using congrArg (conj : ℂ → ℂ) h

end TauCeti.CMType
