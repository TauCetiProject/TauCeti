/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.SchurComplement

/-!
# Quantitative bounds for block operators and their Schur complements

Let `M = ((A.coprod B).prod (C.coprod D)) : E₁ × E₂ → F₁ × F₂` be a `2 × 2` block operator
between normed spaces whose upper left block `A : E₁ ≃L[𝕜] F₁` is invertible, with Schur complement
`S = D - C A⁻¹ B` (`ContinuousLinearEquiv.schurComplement`). Bounds for `S` and bounds for `M` are
equivalent, with explicit constants depending only on `‖A⁻¹‖`, `‖B‖` and `‖C‖`. With
`a = ‖A⁻¹‖`, `b = ‖B‖`, `c = ‖C‖`, and the norm `‖(x₁, x₂)‖ = max ‖x₁‖ ‖x₂‖` on products:

* **A priori estimates.** If `‖z‖ ≤ s ‖S z‖` for all `z`, then
  `‖x‖ ≤ (a + s) (1 + a b) (1 + a c) ‖M x‖` for all `x`
  (`ContinuousLinearEquiv.antilipschitzWith_coprod_prod_coprod`). Conversely an estimate
  `‖x‖ ≤ k ‖M x‖` restricts to `‖z‖ ≤ k ‖S z‖`
  (`ContinuousLinearEquiv.antilipschitzWith_schurComplement`), by testing it on the graph
  `(-A⁻¹ B z, z)`, which `M` sends to `(0, S z)`.
* **Right inverses.** A right inverse `Q` of `S` yields the right inverse
  `y ↦ (A⁻¹ (y₁ - B Q z), Q z)`, `z = y₂ - C A⁻¹ y₁`, of `M`, of norm at most
  `(a + ‖Q‖) (1 + a b) (1 + a c)` (`ContinuousLinearEquiv.exists_rightInverse_coprod_prod_coprod`).
  Conversely a right inverse `R` of `M` yields the right inverse `z ↦ (R (0, z)).2` of `S`, of norm
  at most `‖R‖` (`ContinuousLinearEquiv.exists_rightInverse_schurComplement`).

In an adiabatic or Lyapunov–Schmidt reduction, where `A` is a uniformly invertible fast block and
`S` the slow operator, these transfer uniform estimates for the slow operator to the full
operator and back, with constants that stay bounded whenever `‖A⁻¹‖`, `‖B‖` and `‖C‖` do.
-/

public section

open ContinuousLinearMap
open scoped NNReal

namespace ContinuousLinearEquiv

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [SeminormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

variable (A : E₁ ≃L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (C : E₁ →L[𝕜] F₂) (D : E₂ →L[𝕜] F₂)

/-- The common estimate behind the a priori bound and the right inverse: if `x₁ = A⁻¹ (y₁ - B x₂)`
and `‖x₂‖ ≤ s ‖y₂ - C A⁻¹ y₁‖`, then `‖x‖ ≤ (a + s) (1 + a b) (1 + a c) ‖y‖`. -/
private theorem norm_le_of_eq_of_norm_snd_le {s : ℝ} (hs : 0 ≤ s) {x : E₁ × E₂} {y : F₁ × F₂}
    (h₁ : x.1 = A.symm (y.1 - B x.2)) (h₂ : ‖x.2‖ ≤ s * ‖y.2 - C (A.symm y.1)‖) :
    ‖x‖ ≤ (‖(A.symm : F₁ →L[𝕜] E₁)‖ + s) * (1 + ‖(A.symm : F₁ →L[𝕜] E₁)‖ * ‖B‖) *
      (1 + ‖(A.symm : F₁ →L[𝕜] E₁)‖ * ‖C‖) * ‖y‖ := by
  set a := ‖(A.symm : F₁ →L[𝕜] E₁)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ ‖B‖ := norm_nonneg _
  have hc : 0 ≤ ‖C‖ := norm_nonneg _
  have hA (v : F₁) : ‖A.symm v‖ ≤ a * ‖v‖ := (A.symm : F₁ →L[𝕜] E₁).le_opNorm v
  have hz : ‖y.2 - C (A.symm y.1)‖ ≤ (1 + a * ‖C‖) * ‖y‖ := by
    calc ‖y.2 - C (A.symm y.1)‖ ≤ ‖y‖ + ‖C‖ * (a * ‖y‖) :=
          norm_sub_le_of_le (norm_snd_le y) ((C.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left ((hA _).trans
              (mul_le_mul_of_nonneg_left (norm_fst_le y) ha)) hc))
      _ = (1 + a * ‖C‖) * ‖y‖ := by ring
  have hx₂ : ‖x.2‖ ≤ s * ((1 + a * ‖C‖) * ‖y‖) :=
    h₂.trans (mul_le_mul_of_nonneg_left hz hs)
  have hx₁ : ‖x.1‖ ≤ a * (‖y‖ + ‖B‖ * (s * ((1 + a * ‖C‖) * ‖y‖))) := by
    rw [h₁]
    refine (hA _).trans (mul_le_mul_of_nonneg_left ?_ ha)
    exact norm_sub_le_of_le (norm_fst_le y)
      ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx₂ hb))
  refine norm_prod_le_iff.2 ⟨hx₁.trans ?_, hx₂.trans ?_⟩
  · have : 0 ≤ a * (a * ‖B‖ + a * ‖C‖ + a * ‖B‖ * (a * ‖C‖)) * ‖y‖ +
        s * (1 + a * ‖C‖) * ‖y‖ := by positivity
    nlinarith
  · have : 0 ≤ (a * (1 + a * ‖B‖) + s * (a * ‖B‖)) * (1 + a * ‖C‖) * ‖y‖ := by positivity
    nlinarith

/-- **A priori estimate from the Schur complement.** If the Schur complement `S = D - C A⁻¹ B`
satisfies `‖z‖ ≤ s ‖S z‖`, then the block operator satisfies
`‖x‖ ≤ (‖A⁻¹‖ + s) (1 + ‖A⁻¹‖ ‖B‖) (1 + ‖A⁻¹‖ ‖C‖) ‖M x‖`. -/
theorem antilipschitzWith_coprod_prod_coprod {s : ℝ≥0}
    (hS : AntilipschitzWith s (A.schurComplement B C D)) :
    AntilipschitzWith ((‖(A.symm : F₁ →L[𝕜] E₁)‖₊ + s) *
        (1 + ‖(A.symm : F₁ →L[𝕜] E₁)‖₊ * ‖B‖₊) * (1 + ‖(A.symm : F₁ →L[𝕜] E₁)‖₊ * ‖C‖₊))
      (((A : E₁ →L[𝕜] F₁).coprod B).prod (C.coprod D)) := by
  refine ContinuousLinearMap.antilipschitz_of_bound _ fun x ↦ ?_
  obtain ⟨h₁, h₂⟩ := (coprod_prod_coprod_apply_eq_iff A B C D).1 rfl
  have h := hS.le_mul_norm (_root_.map_zero _) x.2
  rw [h₂] at h
  simpa using norm_le_of_eq_of_norm_snd_le A B C s.property h₁ h

/-- **A priori estimate for the Schur complement.** An estimate `‖x‖ ≤ k ‖M x‖` for the block
operator restricts to the estimate `‖z‖ ≤ k ‖S z‖` for its Schur complement `S = D - C A⁻¹ B`. -/
theorem antilipschitzWith_schurComplement {k : ℝ≥0}
    (hM : AntilipschitzWith k (((A : E₁ →L[𝕜] F₁).coprod B).prod (C.coprod D))) :
    AntilipschitzWith k (A.schurComplement B C D) := by
  refine ContinuousLinearMap.antilipschitz_of_bound _ fun z ↦ ?_
  have hx : ((A : E₁ →L[𝕜] F₁).coprod B).prod (C.coprod D) (-A.symm (B z), z) =
      (0, A.schurComplement B C D z) :=
    (coprod_prod_coprod_apply_eq_iff A B C D).2 ⟨by simp, by simp⟩
  calc ‖z‖ ≤ ‖((-A.symm (B z), z) : E₁ × E₂)‖ := norm_snd_le (-A.symm (B z), z)
    _ ≤ k * ‖((A : E₁ →L[𝕜] F₁).coprod B).prod (C.coprod D) (-A.symm (B z), z)‖ :=
      hM.le_mul_norm (_root_.map_zero _) _
    _ = k * ‖A.schurComplement B C D z‖ := by simp [hx]

/-- **Right inverse from the Schur complement.** A right inverse `Q` of the Schur complement
`S = D - C A⁻¹ B` yields a right inverse of the block operator, of norm at most
`(‖A⁻¹‖ + ‖Q‖) (1 + ‖A⁻¹‖ ‖B‖) (1 + ‖A⁻¹‖ ‖C‖)`. -/
theorem exists_rightInverse_coprod_prod_coprod {Q : F₂ →L[𝕜] E₂}
    (hQ : A.schurComplement B C D ∘L Q = .id 𝕜 F₂) :
    ∃ R : F₁ × F₂ →L[𝕜] E₁ × E₂,
      ((A : E₁ →L[𝕜] F₁).coprod B).prod (C.coprod D) ∘L R = .id 𝕜 (F₁ × F₂) ∧
        ‖R‖ ≤ (‖(A.symm : F₁ →L[𝕜] E₁)‖ + ‖Q‖) * (1 + ‖(A.symm : F₁ →L[𝕜] E₁)‖ * ‖B‖) *
          (1 + ‖(A.symm : F₁ →L[𝕜] E₁)‖ * ‖C‖) := by
  -- The remaining right-hand side `y₂ - C A⁻¹ y₁` of the Schur complement equation.
  let z : F₁ × F₂ →L[𝕜] F₂ := snd 𝕜 F₁ F₂ - C ∘L (A.symm : F₁ →L[𝕜] E₁) ∘L fst 𝕜 F₁ F₂
  have hz (y : F₁ × F₂) : z y = y.2 - C (A.symm y.1) := rfl
  have hSQ (v : F₂) : A.schurComplement B C D (Q v) = v := DFunLike.congr_fun hQ v
  refine ⟨((A.symm : F₁ →L[𝕜] E₁) ∘L (fst 𝕜 F₁ F₂ - B ∘L Q ∘L z)).prod (Q ∘L z),
    ContinuousLinearMap.ext fun y ↦ ?_, opNorm_le_bound _ (by positivity) fun y ↦ ?_⟩
  · rw [comp_apply, id_apply, coprod_prod_coprod_apply_eq_iff]
    exact ⟨by simp, by simp only [ContinuousLinearMap.prod_apply, comp_apply, hSQ, hz]⟩
  · refine norm_le_of_eq_of_norm_snd_le A B C (norm_nonneg Q) (by simp) ?_
    simpa [hz] using Q.le_opNorm (z y)

/-- **Right inverse of the Schur complement.** A right inverse `R` of the block operator yields
the right inverse `z ↦ (R (0, z)).2` of its Schur complement `S = D - C A⁻¹ B`, of norm at most
`‖R‖`. -/
theorem exists_rightInverse_schurComplement {R : F₁ × F₂ →L[𝕜] E₁ × E₂}
    (hR : ((A : E₁ →L[𝕜] F₁).coprod B).prod (C.coprod D) ∘L R = .id 𝕜 (F₁ × F₂)) :
    ∃ Q : F₂ →L[𝕜] E₂, A.schurComplement B C D ∘L Q = .id 𝕜 F₂ ∧ ‖Q‖ ≤ ‖R‖ := by
  refine ⟨snd 𝕜 E₁ E₂ ∘L R ∘L inr 𝕜 F₁ F₂, ContinuousLinearMap.ext fun v ↦ ?_,
    opNorm_le_bound _ (norm_nonneg R) fun v ↦ ?_⟩
  · have h := ((coprod_prod_coprod_apply_eq_iff A B C D).1 (DFunLike.congr_fun hR (0, v))).2
    simpa using h
  · calc ‖(R (0, v)).2‖ ≤ ‖R (0, v)‖ := norm_snd_le _
      _ ≤ ‖R‖ * ‖((0, v) : F₁ × F₂)‖ := R.le_opNorm _
      _ = ‖R‖ * ‖v‖ := by simp

end ContinuousLinearEquiv
