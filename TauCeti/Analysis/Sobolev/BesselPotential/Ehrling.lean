/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# Ehrling's inequality on the Bessel-potential scale

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space, and
write `H^s = H^s(E, F)` for Mathlib's `L²` Bessel-potential spaces. For orders `r ≤ t ≤ s` the
`H^t` norm is a geometric mean of the `H^r` and `H^s` norms: if `t = (1 - θ) r + θ s` with
`0 ≤ θ ≤ 1`, then

`‖u‖_{H^t} ≤ ‖u‖_{H^r} ^ (1 - θ) ‖u‖_{H^s} ^ θ`

(`BesselPotentialSpace.norm_inclusion_le_norm_inclusion_rpow_mul_norm_rpow`). On the Fourier side
`‖u‖_{H^t}` is the `L²` norm of `⟨ξ⟩ ^ t 𝓕 u`, where `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`, and
`⟨ξ⟩ ^ t |𝓕 u| = (⟨ξ⟩ ^ r |𝓕 u|) ^ (1 - θ) (⟨ξ⟩ ^ s |𝓕 u|) ^ θ` pointwise, so this is Hölder's
inequality.

Splitting the geometric mean gives **Ehrling's inequality** on all of `E`: for `r ≤ t < s` and every
`ε > 0` there is `C` with

`‖u‖_{H^t} ≤ ε ‖u‖_{H^s} + C ‖u‖_{H^r}` for all `u ∈ H^s`

(`BesselPotentialSpace.exists_norm_inclusion_le_mul_norm_add_mul_norm`). On a compact manifold, or
for elements with a common compact support, Ehrling's inequality is usually deduced from the
compactness of the inclusion `H^s ⊆ H^t` (`IsCompactOperator.exists_norm_le_mul_norm_add_mul_norm`
and the Rellich theorem `BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`). On the
`L²` Bessel-potential scale no support condition is needed, although the inclusion itself is never
compact for `E ≠ 0` and `F ≠ 0`: translates of a fixed Schwartz function `u` form a bounded
subset of `H^s` whose image in `H^r` has no convergent subsequence
(`BesselPotentialSpace.not_isCompactOperator_inclusion`, for every `1 ≤ p ≤ ∞`, in
`TauCeti.Analysis.Sobolev.BesselPotential.Rellich.Basic`).

## Main results

* `BesselPotentialSpace.norm_inclusion_le_norm_inclusion_rpow_mul_norm_rpow`: the logarithmic
  convexity of the Bessel-potential norms in the order.
* `BesselPotentialSpace.exists_norm_inclusion_le_mul_norm_add_mul_norm`: Ehrling's inequality.

## References

* G. Ehrling, *On a type of eigenvalue problem for certain elliptic differential operators*,
  Math. Scand. **2** (1954), 267–285.
* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution Filter Set
open scoped ENNReal SchwartzMap BesselPotentialSpace Topology Real RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

variable {r s t θ : ℝ}

/-- **Logarithmic convexity of the Bessel-potential norms.** For `r ≤ t ≤ s` with
`t = (1 - θ) r + θ s`, `0 ≤ θ ≤ 1`, the `H^t` norm of `u ∈ H^s` is at most
`‖u‖_{H^r} ^ (1 - θ) ‖u‖_{H^s} ^ θ`. -/
theorem norm_inclusion_le_norm_inclusion_rpow_mul_norm_rpow (hrt : r ≤ t) (hts : t ≤ s)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (ht : t = (1 - θ) * r + θ * s) (u : H^{s}(E, F)) :
    ‖inclusion hts u‖ ≤ ‖inclusion (hrt.trans hts) u‖ ^ (1 - θ) * ‖u‖ ^ θ := by
  rw [← norm_fourier_toLp_eq (inclusion hts u), ← norm_fourier_toLp_eq (inclusion _ u),
    ← norm_fourier_toLp_eq u]
  refine Lp.norm_le_norm_rpow_mul_norm_rpow_of_ae_le hθ ?_ ?_
  · rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.2 hθ.2) hθ.1, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  filter_upwards [coeFn_fourier_toLp_inclusion hts u,
    coeFn_fourier_toLp_inclusion (hrt.trans hts) u] with ξ h₁ h₂
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  simp only [h₁, h₂, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
  rw [Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.rpow_mul hpos.le, mul_assoc,
    ← Real.rpow_add' (norm_nonneg _) (by norm_num), sub_add_cancel, Real.rpow_one]
  refine le_of_eq ?_
  congr 2
  rw [ht]
  ring

/-- **Ehrling's inequality on the Bessel-potential scale.** For `r ≤ t < s` and `ε > 0` there is
`C` such that `‖u‖_{H^t} ≤ ε ‖u‖_{H^s} + C ‖u‖_{H^r}` for every `u ∈ H^s(E, F)`. No support
condition is needed, although, for nontrivial `E` and `F`, the inclusion `H^s ⊆ H^t` is not compact
(`BesselPotentialSpace.not_isCompactOperator_inclusion`). -/
theorem exists_norm_inclusion_le_mul_norm_add_mul_norm (hrt : r ≤ t) (hts : t < s) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C, ∀ u : H^{s}(E, F),
      ‖inclusion hts.le u‖ ≤ ε * ‖u‖ + C * ‖inclusion (hrt.trans hts.le) u‖ := by
  have hrs : 0 < s - r := by linarith
  set θ := (t - r) / (s - r)
  have hθ₀ : 0 ≤ θ := div_nonneg (by linarith) hrs.le
  have hθ₁ : θ < 1 := (div_lt_one hrs).2 (by linarith)
  -- Rescale the geometric mean `a ^ (1 - θ) b ^ θ` of `a = ‖u‖_{H^r}` and `b = ‖u‖_{H^s}` as
  -- that of `K a` and `ε b`, which is at most `max (K a) (ε b) ≤ ε b + K a`.
  set K := ε ^ (-θ / (1 - θ))
  refine ⟨K, fun u ↦ ?_⟩
  set a := ‖inclusion (hrt.trans hts.le) u‖
  set b := ‖u‖
  have hK : ε ^ (-θ / (1 - θ) * (1 - θ)) * ε ^ θ = 1 := by
    rw [div_mul_cancel₀ _ (sub_pos.2 hθ₁).ne', ← Real.rpow_add hε, neg_add_cancel, Real.rpow_zero]
  have hscale : a ^ (1 - θ) * b ^ θ = (K * a) ^ (1 - θ) * (ε * b) ^ θ := by
    rw [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow hε.le (norm_nonneg _),
      ← Real.rpow_mul hε.le]
    linear_combination (-(a ^ (1 - θ) * b ^ θ)) * hK
  calc ‖inclusion hts.le u‖ ≤ a ^ (1 - θ) * b ^ θ :=
        norm_inclusion_le_norm_inclusion_rpow_mul_norm_rpow hrt hts.le ⟨hθ₀, hθ₁.le⟩
          (by simp only [θ]; field_simp; ring) u
    _ = (K * a) ^ (1 - θ) * (ε * b) ^ θ := hscale
    _ ≤ max (K * a) (ε * b) :=
        TauCeti.rpow_mul_rpow_le_max (by positivity) (by positivity) ⟨hθ₀, hθ₁.le⟩
    _ ≤ ε * b + K * a := by
        rw [add_comm]
        exact max_le_add_of_nonneg (by positivity) (by positivity)

end BesselPotentialSpace
