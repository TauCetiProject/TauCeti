/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
import TauCeti.Analysis.SpecialFunctions.Exponential
import TauCeti.Topology.MetricSpace.Pseudo.Basic

/-!
# Comparing commuting bounded-generator semigroups

This file gives the perturbation estimate needed to compare the bounded semigroups in the
Yosida approximation. If bounded operators `A` and `B` commute and their exponentials are bounded
by `M` and `N` between zero and `t`, then

`‖exp (t A) x - exp (t B) x‖ ≤ M * N * t * ‖(A - B) x‖`.

The proof applies Duhamel's formula to the difference of the two exponentials. Commutativity
moves `A - B` through the second exponential, after which the two exponential factors contribute
their bounds. This pointwise estimate is sharper than the generic Banach-algebra bound involving
`exp (t ‖A‖)` and `exp (t ‖B‖)`; that generic bound is useless for Yosida approximations because
their operator norms grow with the approximation parameter.

The two constants are kept separate rather than fixed to one: the Yosida approximations of a
dissipative operator have contractive exponentials, but under the Hille--Yosida hypotheses for a
general growth constant `M` they only satisfy `‖exp (t A_lambda)‖ ≤ M`, and the resulting
comparison carries the factor `M ^ 2`.

## Main results

* `TauCeti.Semigroups.norm_exp_smul_sub_exp_smul_apply_le_of_commute`: the pointwise comparison
  estimate for commuting exponentials with bounds on the required time segment.
* `TauCeti.Semigroups.uniformCauchySeqOn_exp_smul_apply_of_tendsto`: strong convergence of
  eventually commuting generators gives uniform Cauchy convergence on bounded time sets.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

open NormedSpace Set

namespace TauCeti.Semigroups

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- If `A` and `B` commute and their bounded-generator semigroups obey the uniform bounds `M` and
`N` between zero and `t`, then their orbits differ by at most

`‖exp (t A) x - exp (t B) x‖ ≤ M * N * t * ‖(A - B) x‖` for `t ≥ 0`.

This is the bounded Duhamel estimate in the commuting case; the contraction case is `M = N = 1`. -/
theorem norm_exp_smul_sub_exp_smul_apply_le_of_commute {M N t : ℝ} (A B : X →L[𝕜] X)
    (hcomm : Commute A B)
    (hA : ∀ s ∈ Icc 0 t, ‖exp ((s : 𝕜) • A)‖ ≤ M)
    (hB : ∀ s ∈ Icc 0 t, ‖exp ((s : 𝕜) • B)‖ ≤ N)
    (ht : 0 ≤ t) (x : X) :
    ‖exp ((t : 𝕜) • A) x - exp ((t : 𝕜) • B) x‖ ≤ M * N * t * ‖(A - B) x‖ := by
  let : NormedSpace ℝ X := .restrictScalars ℝ 𝕜 X
  let : NormedAlgebra ℝ (X →L[𝕜] X) := .restrictScalars ℝ 𝕜 _
  let +nondep : NormedAlgebra ℚ (X →L[𝕜] X) := .restrictScalars ℚ 𝕜 _
  simp only [← RCLike.real_smul_eq_coe_smul] at hA hB ⊢
  have hN : 0 ≤ N := (norm_nonneg _).trans (hB 0 ⟨le_rfl, ht⟩)
  have hsum : t • A + t • (B - A) = t • B := by module
  have hint := TauCeti.intervalIntegrable_exp_smul_mul_mul_exp_smul
    (t • A + t • (B - A)) (t • (B - A)) (t • A)
  have hduhamel := TauCeti.exp_add_sub_exp_eq_integral (t • A) (t • (B - A))
  rw [hsum] at hint hduhamel
  have happly := congrArg (fun C : X →L[𝕜] X => C x) hduhamel
  rw [ContinuousLinearMap.intervalIntegral_apply (𝕜 := 𝕜) hint x] at happly
  simp only [sub_apply] at happly
  rw [norm_sub_rev, happly]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := M * N * t * ‖(A - B) x‖) ?_).trans_eq ?_
  · intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    have hs_nonneg : 0 ≤ s := hs.1.le
    have hone_sub_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
    have hmove :
        (t • (B - A)) * exp ((s * t) • A) = exp ((s * t) • A) * (t • (B - A)) :=
      (((hcomm.symm.sub_left (Commute.refl A)).smul_left t).smul_right (s * t)).exp_right.eq
    simp only [smul_smul]
    rw [mul_assoc, hmove]
    simp only [mul_apply_eq_comp]
    calc
      ‖exp (((1 - s) * t) • B) (exp ((s * t) • A) ((t • (B - A)) x))‖
          ≤ ‖exp (((1 - s) * t) • B)‖ *
              ‖exp ((s * t) • A) ((t • (B - A)) x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ N * ‖exp ((s * t) • A) ((t • (B - A)) x)‖ := by
        gcongr
        exact hB ((1 - s) * t) ⟨mul_nonneg hone_sub_nonneg ht, by nlinarith [hs_nonneg]⟩
      _ ≤ N * (M * ‖(t • (B - A)) x‖) :=
        mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right
              (hA (s * t) ⟨mul_nonneg hs_nonneg ht, mul_le_of_le_one_left ht hs.2⟩)
              (norm_nonneg _)))
          hN
      _ = M * N * t * ‖(A - B) x‖ := by
        rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
          ← neg_sub, neg_apply, norm_neg]
        ring
  · simp

/-- If bounded generators eventually commute pairwise and converge on a vector, their
exponential orbits on that vector are uniformly Cauchy on a bounded set of real times.
Only a uniform exponential bound along the segments from zero to those times is needed. -/
theorem uniformCauchySeqOn_exp_smul_apply_of_tendsto {ι : Type*} {l : Filter ι}
    {G : ι → X →L[𝕜] X} {x y : X} {S : Set ℝ} {M R : ℝ}
    (hcomm : ∀ᶠ p in l ×ˢ l, Commute (G p.1) (G p.2))
    (hconv : Filter.Tendsto (fun i => G i x) l (nhds y))
    (hbound : ∀ᶠ i in l, ∀ t ∈ S, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖exp (((s * t : ℝ) : 𝕜) • G i)‖ ≤ M)
    (htime : ∀ t ∈ S, |t| ≤ R) :
    UniformCauchySeqOn (fun i (t : ℝ) => exp ((t : 𝕜) • G i) x) l S := by
  apply TauCeti.uniformCauchySeqOn_of_dist_le_mul_dist hconv (M * M * R)
  filter_upwards [hcomm, hbound.prod_mk hbound] with p hc hb
  intro t ht
  have hcompare := norm_exp_smul_sub_exp_smul_apply_le_of_commute
    ((t : 𝕜) • G p.1) ((t : 𝕜) • G p.2)
    ((hc.smul_left (t : 𝕜)).smul_right (t : 𝕜))
    (fun s hs => by simpa only [smul_smul, RCLike.ofReal_mul] using! hb.1 t ht s hs)
    (fun s hs => by simpa only [smul_smul, RCLike.ofReal_mul] using! hb.2 t ht s hs)
    (by norm_num : (0 : ℝ) ≤ 1) x
  simp only [RCLike.ofReal_one, one_smul, mul_one, ← smul_sub, smul_apply,
    norm_smul, RCLike.norm_ofReal, sub_apply, ← dist_eq_norm] at hcompare
  rw [← mul_assoc] at hcompare
  exact hcompare.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (htime t ht) (mul_self_nonneg M)) dist_nonneg)

end TauCeti.Semigroups

end
