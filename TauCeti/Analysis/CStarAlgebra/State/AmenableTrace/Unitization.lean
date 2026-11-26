/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.AmenableTrace.Basic
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Unitization
import TauCeti.Analysis.CStarAlgebra.State.AmenableTrace.Approximation
import TauCeti.Analysis.CStarAlgebra.Unitization

/-!
# Amenable traces and unitization

A norm-one positive functional has an amenable, quasidiagonal, or uniform amenable extension
to the unitization exactly when it has that property itself. No traciality hypothesis is
needed. Completely positive matrix contractions extend by `λ + a ↦ λ 1 + φ a`; their
multiplicativity defects and trace recovery errors are those of `φ` on the algebra component
when the target has positive size. A witness into `M_0` is first replaced by the zero map
into `M_1`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Proposition 3.5.10.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*,
  Ann. of Math. 185 (2017), Remark 1.5.
-/

public section

open TauCeti (ApproxBy RecoverOn RecoverUniform)
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

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
  obtain ⟨l, ρ, hl, hnorm_apply, htr, htwo, hnorm⟩ := φ.exists_matrix_approximant_with_pos_size
  let : NeZero l := ⟨hl.ne'⟩
  have hρ : ∀ a, ‖ρ a‖ ≤ ‖a‖ := fun a => (hnorm_apply a).le.trans (hφ a)
  refine ⟨l, ρ.unitalExtension hρ, ρ.norm_unitalExtension_apply_le hρ, ?_, ?_, ?_⟩
  · intro x y
    rw [CompletelyPositiveMap.unitalExtension_map_mul_sub, htwo]
  · intro x y
    rw [CompletelyPositiveMap.unitalExtension_map_mul_sub, hnorm]
  · intro x
    simp [unitization_apply, hτ, htr]

/-- Transfer matrix witnesses to the unitization for either defect norm and any recovery condition
that transports along the algebra coordinate. -/
private theorem approxBy_unitization {measure : ℝ × ℝ → ℝ}
    [DecidableEq A] {F : Finset A⁺¹} {δ ε : ℝ}
    {R : (A → ℝ) → Prop} {S : (A⁺¹ → ℝ) → Prop}
    (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) (hδε : δ ≤ ε)
    (hR : ∀ e : A → ℝ, R e → S (fun x => e x.snd))
    (h : ApproxBy (fun _ m => measure (CStarMatrix.normalizedTwoNorm m, ‖m‖))
      (fun _ _ _ φ => R (fun a => ‖CStarMatrix.normalizedTrace (φ a) - τ a‖))
      (F.image (fun x : A⁺¹ => x.snd)) δ) :
    ApproxBy (fun _ m => measure (CStarMatrix.normalizedTwoNorm m, ‖m‖))
      (fun _ _ _ ψ => S (fun x => ‖CStarMatrix.normalizedTrace (ψ x) - τ.unitization x‖)) F ε := by
  refine h.transport (fun x : A⁺¹ => x.snd) hδε fun k φ hφ hrec => ?_
  obtain ⟨l, ψ, hψ, htwo, hnorm, htrace⟩ := exists_matrixUnitization φ hφ hτ
  refine ⟨l, ψ, hψ, fun x y => ?_, ?_⟩
  · rw [htwo, hnorm]
  · simpa only [htrace] using hR _ hrec

private theorem approxBy_unitization_recoverOn {measure : ℝ × ℝ → ℝ}
    [DecidableEq A] {F : Finset A⁺¹} {ε : ℝ} (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1)
    (h : ApproxBy (fun _ m => measure (CStarMatrix.normalizedTwoNorm m, ‖m‖))
      (RecoverOn τ) (F.image (fun x : A⁺¹ => x.snd)) ε) :
    ApproxBy (fun _ m => measure (CStarMatrix.normalizedTwoNorm m, ‖m‖))
      (RecoverOn τ.unitization) F ε :=
  approxBy_unitization (R := fun e => ∀ a ∈ F.image (fun x : A⁺¹ => x.snd), e a < ε)
    (S := fun e => ∀ x ∈ F, e x < ε) hτ le_rfl
    (fun _ he x hx => he x.snd (Finset.mem_image_of_mem _ hx)) h

/-- A norm-one positive functional is amenable exactly when its extension to the unitization
is amenable (Brown, Proposition 3.5.10). -/
@[simp]
theorem isAmenableTrace_unitization_iff (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) :
    τ.unitization.IsAmenableTrace ↔ τ.IsAmenableTrace := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  · classical
    rw [isAmenableTrace_iff] at h ⊢
    intro F ε hε
    exact approxBy_unitization_recoverOn (measure := Prod.fst) hτ
      (h (F.image (fun x : A⁺¹ => x.snd)) ε hε)

/-- A norm-one positive functional is quasidiagonal exactly when its extension to the
unitization is quasidiagonal (Tikuisis–White–Winter, Remark 1.5). -/
@[simp]
theorem isQuasidiagonalTrace_unitization_iff (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) :
    τ.unitization.IsQuasidiagonalTrace ↔ τ.IsQuasidiagonalTrace := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  · classical
    rw [isQuasidiagonalTrace_iff] at h ⊢
    intro F ε hε
    exact approxBy_unitization_recoverOn (measure := Prod.snd) hτ
      (h (F.image (fun x : A⁺¹ => x.snd)) ε hε)

/-- A norm-one positive functional is uniformly amenable exactly when its extension to the
unitization is uniformly amenable (Brown, Proposition 3.5.10). -/
@[simp]
theorem isUniformAmenableTrace_unitization_iff (hτ : ‖(τ : A →L[ℂ] ℂ)‖ = 1) :
    τ.unitization.IsUniformAmenableTrace ↔ τ.IsUniformAmenableTrace := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  · classical
    rw [isUniformAmenableTrace_iff] at h ⊢
    intro F ε hε
    refine approxBy_unitization (measure := Prod.fst)
      (R := fun e => ∀ a, e a ≤ ε / 2 * ‖a‖) (S := fun e => ∀ x, e x ≤ ε * ‖x‖)
      hτ (by linarith) (fun _ he x => (he x.snd).trans ?_)
      (h (F.image (fun x : A⁺¹ => x.snd)) (ε / 2) (by positivity))
    calc
      ε / 2 * ‖x.snd‖ ≤ ε / 2 * (2 * ‖x‖) := by
        gcongr
        exact x.norm_snd_le_two_mul_norm
      _ = ε * ‖x‖ := by ring

end PositiveContinuousLinearMap
