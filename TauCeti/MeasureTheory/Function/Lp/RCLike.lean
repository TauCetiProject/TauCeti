/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Real and imaginary parts in `Lp` over an `RCLike` field

Every `f : Lp 𝕜 p μ` over a real or complex field `𝕜` decomposes into its real and imaginary parts
in `Lp ℝ p μ` via `RCLike.reCLM.compLp`, `RCLike.imCLM.compLp`, and `RCLike.ofRealCLM.compLp`
(`MeasureTheory.Lp.ofRealCLM_compLp_reCLM_add_I_smul_ofRealCLM_compLp_imCLM`). Consequently, any
`𝕜`-linear map `T : Lp 𝕜 p μ → Lp 𝕜 q ν` (`1 ≤ q`) that intertwines an operator
`T₀ : Lp ℝ p μ → Lp ℝ q ν` of norm at most `C` along `RCLike.ofRealCLM.compLp` satisfies
`‖T f‖ ≤ 2 * C * ‖f‖` (`TauCeti.norm_apply_le_two_mul_of_compLp_ofRealCLM`).
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} {_ : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜] {p : ℝ≥0∞}

/-- Real and imaginary part decomposition in `Lp 𝕜 p μ`: casting the real and imaginary parts of
`f` back from `Lp ℝ p μ` recovers `f`. -/
theorem ofRealCLM_compLp_reCLM_add_I_smul_ofRealCLM_compLp_imCLM (f : Lp 𝕜 p μ) :
    (RCLike.ofRealCLM (K := 𝕜)).compLp ((RCLike.reCLM (K := 𝕜)).compLp f) +
      (RCLike.I : 𝕜) •
        (RCLike.ofRealCLM (K := 𝕜)).compLp ((RCLike.imCLM (K := 𝕜)).compLp f) = f := by
  let ofRealLp : Lp ℝ p μ → Lp 𝕜 p μ := (RCLike.ofRealCLM (K := 𝕜)).compLp
  let reLp := (RCLike.reCLM (K := 𝕜)).compLp f
  let imLp := (RCLike.imCLM (K := 𝕜)).compLp f
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (ofRealLp reLp) ((RCLike.I : 𝕜) • ofRealLp imLp),
    Lp.coeFn_smul (RCLike.I : 𝕜) (ofRealLp imLp),
    (RCLike.ofRealCLM (K := 𝕜)).coeFn_compLp reLp, (RCLike.reCLM (K := 𝕜)).coeFn_compLp f,
    (RCLike.ofRealCLM (K := 𝕜)).coeFn_compLp imLp, (RCLike.imCLM (K := 𝕜)).coeFn_compLp f]
    with x hadd hsmul hu hre hv him
  dsimp only [ofRealLp, reLp, imLp] at hadd hsmul hu hv ⊢
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hu, hre, hv, him]
  simp only [RCLike.ofRealCLM_apply, RCLike.reCLM_apply, RCLike.imCLM_apply]
  rw [mul_comm, RCLike.re_add_im]

/-- Taking the imaginary part in `Lp 𝕜 p μ` does not increase the norm. -/
theorem norm_imCLM_compLp_le (f : Lp 𝕜 p μ) : ‖(RCLike.imCLM (K := 𝕜)).compLp f‖ ≤ ‖f‖ := by
  have him : ‖(RCLike.imCLM : StrongDual ℝ 𝕜)‖ ≤ 1 :=
    (RCLike.imCLM (K := 𝕜)).opNorm_le_bound zero_le_one fun z ↦ by
      simpa using RCLike.abs_im_le_norm z
  have hf0 : 0 ≤ ‖f‖ := by rw [Lp.norm_def]; exact ENNReal.toReal_nonneg
  exact ((RCLike.imCLM (K := 𝕜)).norm_compLp_le f).trans (mul_le_of_le_one_left hf0 him)

end MeasureTheory.Lp

namespace TauCeti

open MeasureTheory

/-- If a `𝕜`-linear map `T : Lp 𝕜 p μ → Lp 𝕜 q ν` (`1 ≤ q`) intertwines `T₀ : Lp ℝ p μ → Lp ℝ q ν`
along `RCLike.ofRealCLM.compLp` and `‖T₀ g‖ ≤ C * ‖g‖` (`0 ≤ C`), then `‖T f‖ ≤ 2 * C * ‖f‖`. -/
theorem norm_apply_le_two_mul_of_compLp_ofRealCLM
    {α β 𝕜 : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {ν : Measure β} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    {M : Type*} [FunLike M (Lp 𝕜 p μ) (Lp 𝕜 q ν)] [LinearMapClass M 𝕜 (Lp 𝕜 p μ) (Lp 𝕜 q ν)]
    (T : M) (T₀ : Lp ℝ p μ → Lp ℝ q ν)
    (hcomm : ∀ g : Lp ℝ p μ,
      T ((RCLike.ofRealCLM (K := 𝕜)).compLp g) = (RCLike.ofRealCLM (K := 𝕜)).compLp (T₀ g))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ g : Lp ℝ p μ, ‖T₀ g‖ ≤ C * ‖g‖) (f : Lp 𝕜 p μ) :
    ‖T f‖ ≤ 2 * C * ‖f‖ := by
  let reLp := (RCLike.reCLM (K := 𝕜)).compLp f
  let imLp := (RCLike.imCLM (K := 𝕜)).compLp f
  have hnorm_ofReal (g : Lp ℝ q ν) : ‖(RCLike.ofRealCLM (K := 𝕜)).compLp g‖ ≤ ‖g‖ := by
    simpa using (RCLike.ofRealCLM (K := 𝕜)).norm_compLp_le g
  have hnorm_re : ‖reLp‖ ≤ ‖f‖ := by
    simpa [reLp] using (RCLike.reCLM (K := 𝕜)).norm_compLp_le f
  have hnorm_I : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rw [RCLike.norm_I]
    split_ifs <;> norm_num
  conv_lhs => rw [← Lp.ofRealCLM_compLp_reCLM_add_I_smul_ofRealCLM_compLp_imCLM f]
  rw [map_add, map_smul, hcomm, hcomm]
  calc ‖(RCLike.ofRealCLM (K := 𝕜)).compLp (T₀ reLp) +
          (RCLike.I : 𝕜) • (RCLike.ofRealCLM (K := 𝕜)).compLp (T₀ imLp)‖
      ≤ ‖(RCLike.ofRealCLM (K := 𝕜)).compLp (T₀ reLp)‖ +
          ‖(RCLike.I : 𝕜) • (RCLike.ofRealCLM (K := 𝕜)).compLp (T₀ imLp)‖ := norm_add_le _ _
    _ ≤ ‖T₀ reLp‖ + 1 * ‖T₀ imLp‖ := by
        gcongr
        · exact hnorm_ofReal (T₀ reLp)
        · rw [norm_smul]
          exact mul_le_mul hnorm_I (hnorm_ofReal (T₀ imLp)) (norm_nonneg _) zero_le_one
    _ ≤ C * ‖reLp‖ + 1 * (C * ‖imLp‖) := by gcongr <;> exact hC _
    _ ≤ C * ‖f‖ + 1 * (C * ‖f‖) := by
        gcongr
        exact Lp.norm_imCLM_compLp_le f
    _ = 2 * C * ‖f‖ := by ring

end TauCeti
