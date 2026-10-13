/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Extension
public import TauCeti.Analysis.Sobolev.W1p.Multiplication
import Mathlib.MeasureTheory.Function.Holder

/-!
# Localization of the flat Sobolev trace

The trace of a smooth cutoff times an `H¹` function is the boundary restriction of the
cutoff times the trace. This holds for both the whole-space hyperplane trace and the
one-sided half-space trace. In particular, equality of Sobolev values on the support of
a cutoff implies equality of their traces wherever that cutoff is nonzero on the boundary.

These identities allow local boundary traces to be patched with a partition of unity:
localizing before taking the trace agrees with localizing the boundary data. Bounds on
both the cutoff and its gradient are explicit. Compact support is not required.

The whole-space identity uses the dense test-function inclusion and Mathlib's
`ContinuousLinearMap.holderL` for multiplication of `L²` functions by `L∞` functions.
The half-space identity uses `TauCeti.W1p.halfSpaceTrace_restrictL`, so it does not require
the cutoff to commute with reflection.

## References

L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1
(localization of the trace theorem).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ}

/-- The whole-space `H¹` trace commutes with multiplication by a smooth function
whose value and gradient are bounded. The multiplier on the boundary is its classical
restriction to the hyperplane. -/
theorem W1p.hyperplaneTrace_contDiffSMul_ae (a : ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x, |ψ x| ≤ M) (hgradM : ∀ x, ‖∇ ψ x‖ ≤ M)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.hyperplaneTrace a
          (W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) u) y =
        ψ (WithLp.toLp 2 (a, y)) * W1p.hyperplaneTrace a u y := by
  let b : E → ℝ := fun y => ψ (WithLp.toLp 2 (a, y))
  have hb : MemLp b ∞ (volume : Measure E) :=
    memLp_top_of_bound (by fun_prop) M (.of_forall fun y => hψM _)
  let B := hb.toLp b
  let T : Lp ℝ 2 (volume : Measure E) →L[ℝ] Lp ℝ 2 volume :=
    (ContinuousLinearMap.lsmul ℝ ℝ).holderL volume ∞ 2 2 B
  have hT (f : Lp ℝ 2 (volume : Measure E)) :
      T f =ᵐ[volume] fun y => b y * f y := by
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder (r := 2) B f,
      hb.coeFn_toLp] with y hy hby
    simpa only [T, ContinuousLinearMap.holderL_apply_apply, B, hby,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hy
  have heq : W1p.hyperplaneTrace a
      (W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) u) =
      T (W1p.hyperplaneTrace a u) := by
    refine (W1p.denseRange_ofTestFunctionₗ_top
      (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 2) (by norm_num)).induction_on u
      (isClosed_eq ?_ ?_) ?_
    · simpa only [Function.comp_def, W1p.contDiffSMulL_apply] using
        (W1p.hyperplaneTrace a).continuous.comp
          (W1p.contDiffSMulL ψ hψ hM (fun x _ => hψM x)
            (fun x _ => hgradM x)).continuous
    · exact T.continuous.comp (W1p.hyperplaneTrace a).continuous
    · intro φ
      let Φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) :=
        ⟨ψ * (φ : WithLp 2 (ℝ × E) → ℝ), hψ.mul φ.contDiff,
          φ.hasCompactSupport.mul_left, by simp⟩
      rw [W1p.contDiffSMul_ofTestFunctionₗ hψ hM
        (fun x _ => hψM x) (fun x _ => hgradM x) φ Φ rfl]
      apply Lp.ext
      filter_upwards [W1p.hyperplaneTrace_ofTestFunction_apply_ae a Φ,
        W1p.hyperplaneTrace_ofTestFunction_apply_ae a φ,
        hT (W1p.hyperplaneTrace a (W1p.ofTestFunctionₗ volume ⊤ 2 φ))]
        with y hΦ hφ ht
      simp only [hΦ, ht, hφ, b]
      rfl
  rw [heq]
  exact hT _

/-- The one-sided `H¹` trace commutes with smooth bounded multiplication. No symmetry
of the multiplier across the boundary is assumed. -/
theorem W1p.halfSpaceTrace_contDiffSMul_ae (a : ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x, |ψ x| ≤ M) (hgradM : ∀ x, ‖∇ ψ x‖ ≤ M)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.halfSpaceTrace a
          (W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) u) y =
        ψ (WithLp.toLp 2 (a, y)) * W1p.halfSpaceTrace a u y := by
  let w := W1p.extendByReflectionL a u
  have heq : W1p.restrictL (le_top : normalHalfSpace (E := E) a ≤ ⊤)
      (W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) w) =
      W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) u := by
    apply W1p.ext_value
    apply Lp.ext
    have hw := (W1p.value_restrictL_ae
      (le_top : normalHalfSpace (E := E) a ≤ ⊤) w).symm
    rw [W1p.restrictL_extendByReflectionL] at hw
    have hmul := W1p.value_contDiffSMul_ae (mu := volume) (Omega := ⊤)
      hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) w
    simp only [Opens.coe_top, Measure.restrict_univ] at hmul
    filter_upwards [W1p.value_restrictL_ae le_top
        (W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) w),
      ae_restrict_of_ae hmul, hw,
      W1p.value_contDiffSMul_ae hψ hM
        (fun x _ => hψM x) (fun x _ => hgradM x) u] with x hx hm hwx hu
    simp only [hx, hm, hwx, hu]
  rw [← heq, W1p.halfSpaceTrace_restrictL, W1p.halfSpaceTrace_apply]
  exact W1p.hyperplaneTrace_contDiffSMul_ae a hψ hM hψM hgradM w

/-- Half-space Sobolev functions agreeing almost everywhere wherever a smooth cutoff
is nonzero have equal traces almost everywhere wherever its boundary restriction is nonzero.
This is the local agreement needed when gluing boundary charts. -/
theorem W1p.halfSpaceTrace_ae_eq_on_of_cutoff (a : ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x, |ψ x| ≤ M) (hgradM : ∀ x, ‖∇ ψ x‖ ≤ M)
    {u v : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2}
    (huv : ∀ᵐ x ∂volume.restrict (normalHalfSpace (E := E) a),
      ψ x ≠ 0 → W1p.value u x = W1p.value v x) :
    ∀ᵐ y ∂(volume : Measure E), ψ (WithLp.toLp 2 (a, y)) ≠ 0 →
      W1p.halfSpaceTrace a u y = W1p.halfSpaceTrace a v y := by
  have heq : W1p.contDiffSMul ψ hψ hM
      (fun x _ => hψM x) (fun x _ => hgradM x) u =
      W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) v := by
    apply W1p.ext_value
    apply Lp.ext
    filter_upwards [huv, W1p.value_contDiffSMul_ae hψ hM
      (fun x _ => hψM x) (fun x _ => hgradM x) u,
      W1p.value_contDiffSMul_ae hψ hM
        (fun x _ => hψM x) (fun x _ => hgradM x) v] with x hx hu hv
    rw [hu, hv]
    by_cases h : ψ x = 0
    · simp [h]
    · rw [hx h]
  have ht := congrArg (W1p.halfSpaceTrace a) heq
  filter_upwards [W1p.halfSpaceTrace_contDiffSMul_ae a hψ hM hψM hgradM u,
    W1p.halfSpaceTrace_contDiffSMul_ae a hψ hM hψM hgradM v] with y hu hv
  intro hy
  exact mul_left_cancel₀ hy
    (hu.symm.trans ((congrArg (fun f : Lp ℝ 2 (volume : Measure E) => f y) ht).trans hv))

end TauCeti
