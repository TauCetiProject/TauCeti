/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# Ehrling's inequality on the Bessel-potential scale, and the failure of Rellich on `ℝⁿ`

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
(`BesselPotentialSpace.not_isCompactOperator_inclusion`). Indeed the `H^r` inner product of two
translates `u(· - a)` and `u(· - b)` is the Fourier transform of the integrable function
`⟨ξ⟩ ^ (2 r) ‖𝓕 u ξ‖ ^ 2` at `b - a`, which tends to `0` as `‖b - a‖ → ∞` by the Riemann–Lebesgue
lemma, so far apart translates are at distance more than `‖u‖_{H^r}` from each other.

## Main results

* `BesselPotentialSpace.norm_inclusion_le_norm_inclusion_rpow_mul_norm_rpow`: the logarithmic
  convexity of the Bessel-potential norms in the order.
* `BesselPotentialSpace.exists_norm_inclusion_le_mul_norm_add_mul_norm`: Ehrling's inequality.
* `BesselPotentialSpace.not_isCompactOperator_inclusion`: the inclusion `H^s ⊆ H^r` is not compact.

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

/-! ### The inclusion is not compact -/

/-- The `H^r` inner product of the translates `u(· - a)` and `u(· - b)` of a Schwartz function is
the Fourier transform at `b - a` of `‖⟨ξ⟩ ^ r 𝓕 u ξ‖ ^ 2`. -/
private theorem inner_toBesselPotentialSpaceCLM_compSubConstCLM (r : ℝ) (u : 𝓢(E, F))
    (a b : E) :
    inner ℂ (SchwartzMap.toBesselPotentialSpaceCLM r 2 (u.compSubConstCLM ℂ a))
        (SchwartzMap.toBesselPotentialSpaceCLM r 2 (u.compSubConstCLM ℂ b)) =
      ∫ ξ, 𝐞 (-⟪ξ, b - a⟫) •
        ((‖(((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) • 𝓕 u ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hw : (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hphase (c₁ c₂ : Circle) (v : F) :
      inner ℂ (c₁ • v) (c₂ • v) = ((c₁⁻¹ * c₂ : Circle) : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Circle.smul_def, Circle.smul_def, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K, Circle.coe_mul, Circle.coe_inv_eq_conj, ← mul_assoc]
    norm_cast
  rw [← inner_toLp_toLp, ← Lp.inner_fourier_eq, SchwartzMap.fourier_toLp_toBesselPotentialSpaceCLM,
    SchwartzMap.fourier_toLp_toBesselPotentialSpaceCLM, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM F
      (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) (𝓕 (u.compSubConstCLM ℂ a))) 2 volume,
    SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM F
      (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) (𝓕 (u.compSubConstCLM ℂ b))) 2 volume]
    with ξ ha hb
  simp only [ha, hb, SchwartzMap.smulLeftCLM_apply_apply hw,
    SchwartzMap.fourier_compSubConstCLM_apply]
  rw [smul_comm _ (𝐞 _), smul_comm _ (𝐞 _), hphase,
    ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
    inner_sub_right, real_inner_comm a, real_inner_comm b]
  congr 4
  ring

/-- Far apart translates of a nonzero Schwartz function `u` are at `H^r` distance more than the
`H^r` norm of `u`. -/
private theorem exists_norm_lt_norm_sub_compSubConstCLM (r : ℝ) {u : 𝓢(E, F)} (hu : u ≠ 0) :
    ∃ R, ∀ a b : E, R ≤ ‖b - a‖ →
      ‖SchwartzMap.toBesselPotentialSpaceCLM r 2 u‖ <
        ‖SchwartzMap.toBesselPotentialSpaceCLM r 2 (u.compSubConstCLM ℂ a) -
          SchwartzMap.toBesselPotentialSpaceCLM r 2 (u.compSubConstCLM ℂ b)‖ := by
  set N := ‖SchwartzMap.toBesselPotentialSpaceCLM r 2 u‖
  have hN : 0 < N := SchwartzMap.norm_toBesselPotentialSpaceCLM_pos r hu
  -- By the Riemann–Lebesgue lemma, the inner products of far apart translates are small.
  have hRL := (tendsto_integral_exp_inner_smul_cocompact fun ξ ↦
    ((‖(((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) • 𝓕 u ξ‖ ^ 2 : ℝ) : ℂ)).eventually
      (Metric.ball_mem_nhds 0 (by positivity : (0 : ℝ) < N ^ 2 / 2))
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, eventually_comap,
    eventually_atTop] at hRL
  obtain ⟨R, hR⟩ := hRL
  refine ⟨R, fun a b hab ↦ ?_⟩
  have hinner := hR ‖b - a‖ hab (b - a) rfl
  rw [dist_zero_right, ← inner_toBesselPotentialSpaceCLM_compSubConstCLM] at hinner
  set x := SchwartzMap.toBesselPotentialSpaceCLM r 2 (u.compSubConstCLM ℂ a)
  set y := SchwartzMap.toBesselPotentialSpaceCLM r 2 (u.compSubConstCLM ℂ b)
  -- `‖x - y‖² = ‖x‖² - 2 re ⟪x, y⟫ + ‖y‖²` with `‖x‖ = ‖y‖ = N` and `|⟪x, y⟫| < N² / 2`.
  have hsq := norm_sub_sq (𝕜 := ℂ) x y
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_compSubConstCLM,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_compSubConstCLM] at hsq
  have hre := RCLike.re_le_norm (inner ℂ x y)
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [hsq]
  linarith

/-- **The inclusion `H^s ⊆ H^r` is not compact.** On a nonzero space `E`, for a nonzero complex
Hilbert space `F` and orders `r ≤ s`, the translates of a fixed nonzero Schwartz function form a
bounded subset of `H^s(E, F)` whose image in `H^r(E, F)` has no convergent subsequence. Compactness
needs a localization, as in the Rellich theorem
`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`. -/
theorem not_isCompactOperator_inclusion [Nontrivial E] [Nontrivial F] (h : r ≤ s) :
    ¬ IsCompactOperator (inclusion h : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) := by
  intro hc
  -- A nonzero Schwartz function `u`: a Gaussian times a nonzero vector.
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  set u : 𝓢(E, F) := (SchwartzMap.gaussian (V := E) (b := 1) (by simp)).postcompCLM
    (ContinuousLinearMap.toSpanSingleton ℂ v)
  have hu : u ≠ 0 := fun hu0 ↦ hv (by simpa [u] using congrArg (fun f : 𝓢(E, F) ↦ f 0) hu0)
  obtain ⟨R, hR⟩ := exists_norm_lt_norm_sub_compSubConstCLM r hu
  -- Its translates by the multiples `k R' e` of a unit vector `e` are pairwise far apart in `H^r`.
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  set R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set a : ℕ → E := fun k ↦ ((k : ℝ) * R') • e
  have hsep (j k : ℕ) (hjk : j ≠ k) : R ≤ ‖a k - a j‖ := by
    have h1 : (1 : ℝ) ≤ |(k : ℝ) - j| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.2 (by exact_mod_cast hjk.symm : (k : ℤ) ≠ j))
    rw [← sub_smul, norm_smul, he, mul_one, ← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_pos hR']
    calc R ≤ 1 * R' := by rw [one_mul]; exact le_max_left _ _
      _ ≤ |(k : ℝ) - j| * R' := by gcongr
  -- The translates are bounded in `H^s`, so a subsequence of their images in `H^r` converges.
  set S := Set.range fun k ↦ SchwartzMap.toBesselPotentialSpaceCLM s 2 (u.compSubConstCLM ℂ (a k))
  have hbdd : Bornology.IsBounded S := by
    refine isBounded_iff_forall_norm_le.2 ⟨‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (SchwartzMap.norm_toBesselPotentialSpaceCLM_compSubConstCLM s u (a k)).le
  have hmem (k : ℕ) : SchwartzMap.toBesselPotentialSpaceCLM r 2 (u.compSubConstCLM ℂ (a k)) ∈
      closure (inclusion h '' S) :=
    subset_closure ⟨_, ⟨k, rfl⟩, inclusion_toBesselPotentialSpaceCLM h _⟩
  obtain ⟨x, -, φ, hφ, hlim⟩ := (hc.isCompact_closure_image_of_bounded hbdd).tendsto_subseq hmem
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq _
    (SchwartzMap.norm_toBesselPotentialSpaceCLM_pos (p := 2) r hu)
  have hlt := hM (M + 1) (Nat.le_succ M)
  rw [dist_eq_norm] at hlt
  exact (hR _ _ (hsep _ _ (hφ.injective.ne (Nat.succ_ne_self M)))).not_gt hlt

end BesselPotentialSpace
