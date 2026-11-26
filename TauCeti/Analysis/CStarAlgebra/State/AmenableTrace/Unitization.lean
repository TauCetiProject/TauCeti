/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.AmenableTrace.Basic
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Unitization

/-!
# Amenable traces and unitization

A norm-one positive functional has an amenable, quasidiagonal, or uniform amenable extension
to the unitization exactly when it has that property itself. No traciality hypothesis is
needed. Completely positive matrix contractions extend by `λ + a ↦ λ 1 + φ a`; their
multiplicativity defects and trace recovery errors are those of `φ` on the algebra component.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Proposition 3.5.10.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*,
  Ann. of Math. 185 (2017), Remark 1.5.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

/-- Extend a matrix contraction by its scalar component, using the canonical homomorphism
from the unitization of the target matrix algebra back to that algebra. -/
private noncomputable def matrixUnitization {k : ℕ}
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) :
    A⁺¹ →CP CStarMatrix (Fin k) (Fin k) ℂ :=
  (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (Unitization.starLift (NonUnitalStarAlgHom.id ℂ _))).comp (φ.unitization hφ)

private theorem matrixUnitization_apply {k : ℕ}
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (x : A⁺¹) :
    matrixUnitization φ hφ x = x.fst • 1 + φ x.snd := by
  simp [matrixUnitization, CompletelyPositiveMap.unitization_apply, Unitization.starLift,
    Unitization.lift, Algebra.algebraMap_eq_smul_one]

private theorem matrixUnitization_map_mul_sub {k : ℕ}
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (x y : A⁺¹) :
    matrixUnitization φ hφ (x * y) - matrixUnitization φ hφ x * matrixUnitization φ hφ y =
      φ (x.snd * y.snd) - φ x.snd * φ y.snd := by
  simp only [matrixUnitization_apply, Unitization.fst_mul, Unitization.snd_mul,
    map_add, map_smul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_add, smul_smul, mul_comm]
  abel

private theorem exists_matrixUnitization {k : ℕ}
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) :
    ∃ (l : ℕ) (ψ : A⁺¹ →CP CStarMatrix (Fin l) (Fin l) ℂ),
      (∀ x, ‖ψ x‖ ≤ ‖x‖) ∧
      (∀ x y, CStarMatrix.normalizedTwoNorm (ψ (x * y) - ψ x * ψ y) =
        CStarMatrix.normalizedTwoNorm (φ (x.snd * y.snd) - φ x.snd * φ y.snd)) ∧
      (∀ x y, ‖ψ (x * y) - ψ x * ψ y‖ = ‖φ (x.snd * y.snd) - φ x.snd * φ y.snd‖) ∧
      ∀ x, CStarMatrix.normalizedTrace (ψ x) - τ.unitization x =
        CStarMatrix.normalizedTrace (φ x.snd) - τ x.snd := by
  obtain ⟨l, ρ, hl, hρ, htr, htwo, hnorm⟩ :=
    CompletelyPositiveMap.exists_pos_matrix_approximant φ hφ
  let : NeZero l := ⟨hl.ne'⟩
  refine ⟨l, matrixUnitization ρ hρ, ?_, ?_, ?_, ?_⟩
  · apply (CompletelyPositiveMapClass.norm_map_one_le_one_iff _).mp
    simp [matrixUnitization_apply]
  · intro x y
    rw [matrixUnitization_map_mul_sub, htwo]
  · intro x y
    rw [matrixUnitization_map_mul_sub, hnorm]
  · intro x
    simp [matrixUnitization_apply, unitization_apply, hτ, htr]

/-- A norm-one positive functional is amenable exactly when its extension to the unitization
is amenable (Brown, Proposition 3.5.10). -/
theorem isAmenableTrace_unitization_iff (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) :
    τ.unitization.IsAmenableTrace ↔ τ.IsAmenableTrace := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  · classical
    rw [isAmenableTrace_iff] at h ⊢
    intro F ε hε
    obtain ⟨k, φ, hφ, hmul, htr⟩ := h (F.image (fun x : A⁺¹ => x.snd)) ε hε
    obtain ⟨l, ψ, hψ, htwo, -, hrec⟩ := exists_matrixUnitization φ hφ hτ
    refine ⟨l, ψ, hψ, fun x hx y hy => ?_, fun x hx => ?_⟩
    · rw [htwo]
      exact hmul _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)
    · rw [hrec]
      exact htr _ (Finset.mem_image_of_mem _ hx)

/-- A norm-one positive functional is quasidiagonal exactly when its extension to the
unitization is quasidiagonal (Tikuisis–White–Winter, Remark 1.5). -/
theorem isQuasidiagonalTrace_unitization_iff (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) :
    τ.unitization.IsQuasidiagonalTrace ↔ τ.IsQuasidiagonalTrace := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  · classical
    rw [isQuasidiagonalTrace_iff] at h ⊢
    intro F ε hε
    obtain ⟨k, φ, hφ, hmul, htr⟩ := h (F.image (fun x : A⁺¹ => x.snd)) ε hε
    obtain ⟨l, ψ, hψ, -, hnorm, hrec⟩ := exists_matrixUnitization φ hφ hτ
    refine ⟨l, ψ, hψ, fun x hx y hy => ?_, fun x hx => ?_⟩
    · rw [hnorm]
      exact hmul _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)
    · rw [hrec]
      exact htr _ (Finset.mem_image_of_mem _ hx)

/-- A norm-one positive functional is uniformly amenable exactly when its extension to the
unitization is uniformly amenable (Brown, Proposition 3.5.10). -/
theorem isUniformAmenableTrace_unitization_iff (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) :
    τ.unitization.IsUniformAmenableTrace ↔ τ.IsUniformAmenableTrace := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  · classical
    rw [isUniformAmenableTrace_iff] at h ⊢
    intro F ε hε
    obtain ⟨k, φ, hφ, hmul, htr⟩ := h (F.image (fun x : A⁺¹ => x.snd)) (ε / 2) (by positivity)
    obtain ⟨l, ψ, hψ, htwo, -, hrec⟩ := exists_matrixUnitization φ hφ hτ
    refine ⟨l, ψ, hψ, fun x hx y hy => ?_, fun x => ?_⟩
    · rw [htwo]
      exact (hmul _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)).trans
        (by linarith)
    · rw [hrec]
      have hsnd : ‖x.snd‖ ≤ 2 * ‖x‖ := by
        -- The Lipschitz theorem uses the auxiliary metric; its norm is the final C⋆-norm.
        let : NormedRing A⁺¹ := Unitization.normedRingAux
        have h := (Unitization.lipschitzWith_addEquiv (𝕜 := ℂ) (A := A)).dist_le_mul x 0
        simp only [dist_eq_norm, map_zero, sub_zero, NNReal.coe_ofNat] at h
        exact (le_max_right ‖x.fst‖ ‖x.snd‖).trans h
      exact (htr x.snd).trans (by nlinarith)

end PositiveContinuousLinearMap
