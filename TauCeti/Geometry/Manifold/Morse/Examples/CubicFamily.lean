/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPointContinuation
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Analysis.Calculus.Morse.OneDimensional

/-!
# The cubic family `x³ - t x`: a pair of critical points born at a degenerate one

The one-parameter family of functions `f_t(x) = x³ - t x` on the manifold `ℝ` is the simplest family
in which nondegenerate critical points appear and disappear. Its derivative is `3 x² - t` and its
second derivative `6 x`, so:

* for `t < 0` it has no critical point (`TauCeti.criticalPoints_pow_three_sub_mul_of_neg`,
  `TauCeti.totalCriticalCount_pow_three_sub_mul_of_neg`);
* for `t = 0` it has exactly one, the origin (`TauCeti.criticalPoints_pow_three_sub_mul_zero`,
  `TauCeti.totalCriticalCount_pow_three_sub_mul_zero`), and it is degenerate
  (`TauCeti.not_isManifoldNondegenerateCriticalPoint_pow_three_sub_mul_zero`);
* for `t > 0` it has exactly two, `±√(t / 3)` (`TauCeti.criticalPoints_pow_three_sub_mul_of_pos`,
  `TauCeti.totalCriticalCount_pow_three_sub_mul_of_pos`),
  a local maximum of Morse index `1` at `-√(t / 3)` and a local minimum of Morse index `0` at
  `√(t / 3)` (`TauCeti.manifoldMorseIndex_pow_three_sub_mul_neg_sqrt`,
  `TauCeti.manifoldMorseIndex_pow_three_sub_mul_sqrt`).

So `f_t` is a Morse function exactly when `t ≠ 0` (`TauCeti.isMorse_pow_three_sub_mul_iff`). Up
to the factor `3` and the reparametrization `s = t / 3` this is the birth–death potential
`TauCeti.birthDeathPotential`, `x³ - t x = 3 (x³ / 3 - (t / 3) x)`.

The family is jointly smooth, so at every critical point of `f_t` with `t ≠ 0` the continuation
theorem `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_contMDiffAt_criticalPoint_continuation`
gives a locally unique `C²` branch of nondegenerate critical points through it. Its hypothesis of
nondegeneracy cannot be dropped: at the degenerate critical point `(t, x) = (0, 0)` the existence,
the local uniqueness and the regularity of such a branch all fail.

* **No branch exists.** There is no function `ψ` with `ψ t` a critical point of `f_t` for all `t`
  near `0` (`TauCeti.not_exists_eventually_mem_criticalPoints_pow_three_sub_mul`), since there is no
  critical point at all for `t < 0`.
* **Critical points near `(0, 0)` are not locally unique.** No function `ψ` describes the critical
  points of the family near `(0, 0)` as its graph
  (`TauCeti.not_eventually_mem_criticalPoints_pow_three_sub_mul_iff_eq`): for small `t > 0` the two
  critical points `±√(t / 3)` are both close to `0`.
* **No branch is differentiable, even from one side.** A choice `ψ t` of critical points of `f_t`
  for all small `t > 0` satisfies `|ψ t| = √(t / 3)`, so no extension of `ψ` to `t = 0` is
  differentiable at `0` within `[0, ∞)`
  (`TauCeti.not_differentiableWithinAt_of_eventually_mem_criticalPoints_pow_three_sub_mul`), whereas
  the continuation theorem gives `C²` branches.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publications Mathématiques de l'IHÉS 39 (1970), 5–173.
-/

public section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {t x : ℝ}

/-! ### Derivatives -/

/-- The derivative of `y ↦ y³ - t y` is `3 x² - t`. -/
private theorem hasDerivAt_pow_three_sub_mul (t x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 3 - t * y) (3 * x ^ 2 - t) x := by
  refine ((hasDerivAt_pow 3 x).sub ((hasDerivAt_id' x).const_mul t)).congr_deriv ?_
  norm_num

/-- The second derivative of `y ↦ y³ - t y` is `6 x`. -/
private theorem iteratedDeriv_two_pow_three_sub_mul (t x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ ↦ y ^ 3 - t * y) x = 6 * x := by
  have hd : deriv (fun y : ℝ ↦ y ^ 3 - t * y) = fun y ↦ 3 * y ^ 2 - t :=
    funext fun y ↦ (hasDerivAt_pow_three_sub_mul t y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  refine (((hasDerivAt_pow 2 x).const_mul 3).sub_const t).deriv.trans ?_
  norm_num
  ring

/-! ### Critical points and their count -/

/-- **The critical points of `x³ - t x`** are the solutions of `3 x² = t`. -/
theorem mem_criticalPoints_pow_three_sub_mul_iff :
    x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) ↔ 3 * x ^ 2 = t := by
  rw [mem_criticalPoints_iff_deriv_eq_zero, (hasDerivAt_pow_three_sub_mul t x).deriv, sub_eq_zero]

/-- For `t < 0` the function `x³ - t x` has no critical point. -/
theorem criticalPoints_pow_three_sub_mul_of_neg (ht : t < 0) :
    criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ by
    have := mem_criticalPoints_pow_three_sub_mul_iff.1 hx
    nlinarith [sq_nonneg x]

/-- For `t = 0` the only critical point of `x³ - t x` is the origin. -/
theorem criticalPoints_pow_three_sub_mul_zero :
    criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - 0 * y) = {0} := by
  simpa using criticalPoints_pow (m := 3) (by norm_num)

/-- For `t > 0` the critical points of `x³ - t x` are `-√(t / 3)` and `√(t / 3)`. -/
theorem criticalPoints_pow_three_sub_mul_of_pos (ht : 0 < t) :
    criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = {-√(t / 3), √(t / 3)} := by
  ext x
  have h3 : √(t / 3) ^ 2 = t / 3 := Real.sq_sqrt (by positivity)
  rw [mem_criticalPoints_pow_three_sub_mul_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hx
    have hsq : x ^ 2 = √(t / 3) ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact .inr h
    · exact .inl h
  · rintro (rfl | rfl) <;> simp only [neg_sq, h3] <;> ring

/-- For `t < 0` the function `x³ - t x` has no critical point. -/
theorem totalCriticalCount_pow_three_sub_mul_of_neg (ht : t < 0) :
    totalCriticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = 0 := by
  rw [totalCriticalCount_def, criticalPoints_pow_three_sub_mul_of_neg ht, encard_empty]

/-- For `t = 0` the function `x³ - t x` has exactly one critical point. -/
theorem totalCriticalCount_pow_three_sub_mul_zero :
    totalCriticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - 0 * y) = 1 := by
  rw [totalCriticalCount_def, criticalPoints_pow_three_sub_mul_zero, encard_singleton]

/-- For `t > 0` the function `x³ - t x` has exactly two critical points. -/
theorem totalCriticalCount_pow_three_sub_mul_of_pos (ht : 0 < t) :
    totalCriticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = 2 := by
  have hne : -√(t / 3) ≠ √(t / 3) := by
    have := Real.sqrt_pos.2 (show 0 < t / 3 by positivity)
    linarith
  rw [totalCriticalCount_def, criticalPoints_pow_three_sub_mul_of_pos ht, encard_pair hne]

/-! ### Nondegeneracy and Morse indices -/

/-- **Nondegenerate critical points of `x³ - t x`.** A point is a nondegenerate critical point
exactly when it solves `3 x² = t` with `t ≠ 0`: all critical points are nondegenerate for `t ≠ 0`,
and the only critical point for `t = 0` is degenerate. -/
theorem isManifoldNondegenerateCriticalPoint_pow_three_sub_mul_iff :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) x ↔
      3 * x ^ 2 = t ∧ t ≠ 0 := by
  rw [isManifoldNondegenerateCriticalPoint_modelSpace_iff,
    isNondegenerateCriticalPoint_real_iff (by fun_prop), (hasDerivAt_pow_three_sub_mul t x).deriv,
    iteratedDeriv_two_pow_three_sub_mul, sub_eq_zero]
  refine and_congr_right fun hx ↦ ?_
  subst hx
  simp

/-- At `t = 0` the critical point `0` of `x³ - t x` is degenerate. -/
theorem not_isManifoldNondegenerateCriticalPoint_pow_three_sub_mul_zero :
    ¬IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - 0 * y) 0 := by
  rw [isManifoldNondegenerateCriticalPoint_pow_three_sub_mul_iff]
  simp

/-- **`x³ - t x` is a Morse function exactly when `t ≠ 0`.** -/
theorem isMorse_pow_three_sub_mul_iff :
    IsMorse 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) ↔ t ≠ 0 := by
  refine ⟨?_, fun ht ↦ isMorse_modelSpace_iff.2
    ⟨by fun_prop, hasNondegenerateCriticalPointsOn_iff.2 fun x _ hx ↦ ?_⟩⟩
  · rintro h rfl
    exact not_isManifoldNondegenerateCriticalPoint_pow_three_sub_mul_zero
      (h.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (criticalPoints_pow_three_sub_mul_zero ▸ mem_singleton 0))
  · rw [← isManifoldNondegenerateCriticalPoint_modelSpace_iff]
    exact isManifoldNondegenerateCriticalPoint_pow_three_sub_mul_iff.2
      ⟨mem_criticalPoints_pow_three_sub_mul_iff.1 (mem_criticalPoints_iff_fderiv_eq_zero.2 hx), ht⟩

/-- For `t > 0` the critical point `-√(t / 3)` of `x³ - t x` is a local maximum: its Morse index
is `1`. -/
theorem manifoldMorseIndex_pow_three_sub_mul_neg_sqrt (ht : 0 < t) :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) (-√(t / 3)) = 1 := by
  rw [manifoldMorseIndex_modelSpace]
  refine morseIndex_real_of_neg ?_
  rw [iteratedDeriv_two_pow_three_sub_mul]
  linarith [Real.sqrt_pos.2 (show 0 < t / 3 by positivity)]

/-- For `t > 0` the critical point `√(t / 3)` of `x³ - t x` is a local minimum: its Morse index
is `0`. -/
theorem manifoldMorseIndex_pow_three_sub_mul_sqrt (ht : 0 < t) :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) √(t / 3) = 0 := by
  rw [manifoldMorseIndex_modelSpace]
  refine morseIndex_real_of_pos ?_
  rw [iteratedDeriv_two_pow_three_sub_mul]
  linarith [Real.sqrt_pos.2 (show 0 < t / 3 by positivity)]

/-! ### Continuation fails at the degenerate critical point -/

/-- **No branch of critical points through `t = 0`.** No function `ψ` picks a critical point
`ψ t` of `x³ - t x` for every `t` near `0`: there is none for `t < 0`. -/
theorem not_exists_eventually_mem_criticalPoints_pow_three_sub_mul :
    ¬∃ ψ : ℝ → ℝ, ∀ᶠ t in 𝓝 0, ψ t ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨t, hψt, ht⟩ :=
    ((hψ.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Iio (0 : ℝ)))).exists
  rw [criticalPoints_pow_three_sub_mul_of_neg ht] at hψt
  exact hψt

/-- **The critical points near `(0, 0)` are not the graph of a function.** For no function `ψ`
are the critical points `x` of `x³ - t x`, for `(t, x)` near `(0, 0)`, exactly the points with
`x = ψ t`: for small `t > 0` the two critical points `±√(t / 3)` are both near `0`. -/
theorem not_eventually_mem_criticalPoints_pow_three_sub_mul_iff_eq (ψ : ℝ → ℝ) :
    ¬∀ᶠ q : ℝ × ℝ in 𝓝 (0, 0),
      (q.2 ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - q.1 * y) ↔ ψ q.1 = q.2) := by
  intro h
  have hcont : Continuous fun t : ℝ ↦ √(t / 3) := by fun_prop
  have hlim (σ : ℝ) : Tendsto (fun t : ℝ ↦ (t, σ * √(t / 3))) (𝓝[>] 0) (𝓝 (0, 0)) :=
    (((continuous_id.prodMk (continuous_const.mul hcont)).tendsto' 0 (0, 0)
      (by simp)).mono_left nhdsWithin_le_nhds)
  obtain ⟨t, ⟨hp, hm⟩, ht⟩ :=
    (((hlim 1).eventually h).and ((hlim (-1)).eventually h)).and self_mem_nhdsWithin |>.exists
  simp only [one_mul, neg_one_mul, criticalPoints_pow_three_sub_mul_of_pos ht, mem_insert_iff,
    mem_singleton_iff, true_or, or_true, true_iff] at hp hm
  have := Real.sqrt_pos.2 (show 0 < t / 3 by positivity)
  linarith

/-- **No branch of critical points is differentiable at the birth.** Let `ψ t` be a critical point
of `x³ - t x` for every small `t > 0`. Then `|ψ t| = √(t / 3)`, so `ψ`, whatever its value at `0`,
is not differentiable at `0` within `[0, ∞)`. -/
theorem not_differentiableWithinAt_of_eventually_mem_criticalPoints_pow_three_sub_mul {ψ : ℝ → ℝ}
    (hψ : ∀ᶠ t in 𝓝[>] 0, ψ t ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y)) :
    ¬DifferentiableWithinAt ℝ ψ (Ici 0) 0 := by
  intro hd
  have hsq : ∀ᶠ t in 𝓝[>] 0, 3 * ψ t ^ 2 = t :=
    hψ.mono fun t ht ↦ mem_criticalPoints_pow_three_sub_mul_iff.1 ht
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] 0 := nhdsWithin_mono _ Ioi_subset_Ici_self
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  -- The branch tends to `0`, since `ψ t ^ 2 = t / 3`, so its value at `0` must be `0`.
  have hψ0 : ψ 0 = 0 := by
    have hsq0 : Tendsto (fun t ↦ ψ t ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ ↦ t / 3) (𝓝[>] 0) (𝓝 0) := by
        simpa using hid.div_const 3
      exact this.congr' (hsq.mono fun t ht ↦ by linarith)
    have hlim := ((hd.continuousWithinAt.tendsto.mono_left hle).pow 2)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (tendsto_nhds_unique hlim hsq0)
  -- A derivative within `[0, ∞)` bounds `|ψ t|` by `C t`, against `ψ t ^ 2 = t / 3`.
  obtain ⟨C, hC⟩ := (hd.hasFDerivWithinAt.isBigO_sub.mono hle).bound
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 3 * C ^ 2 * t < 1 := by
    have : Tendsto (fun t : ℝ ↦ 3 * C ^ 2 * t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hid.const_mul (3 * C ^ 2)
    exact this.eventually (gt_mem_nhds one_pos)
  obtain ⟨t, ⟨⟨hCt, hst⟩, hsm⟩, ht⟩ := ((hC.and hsq).and hsmall).and self_mem_nhdsWithin |>.exists
  simp only [hψ0, sub_zero, Real.norm_eq_abs] at hCt
  have ht0 : (0 : ℝ) < t := ht
  have habs : |ψ t| ^ 2 ≤ (C * |t|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hCt 2
  rw [sq_abs, abs_of_pos ht0] at habs
  nlinarith

/-- For `t ≠ 0` the continuation theorem applies at every critical point of `x³ - t x`. -/
example {t₀ x₀ : ℝ} (ht₀ : t₀ ≠ 0)
    (hx₀ : x₀ ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t₀ * y)) :
    ∃ ψ : ℝ → ℝ, ψ t₀ = x₀ ∧ ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 ψ t₀ ∧
      ∀ᶠ q : ℝ × ℝ in 𝓝 (t₀, x₀),
        (q.2 ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - q.1 * y) ↔ ψ q.1 = q.2) := by
  have hnd : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, ℝ)
      (fun y : ℝ ↦ (fun q : ℝ × ℝ ↦ q.2 ^ 3 - q.1 * q.2) (t₀, y)) x₀ :=
    isManifoldNondegenerateCriticalPoint_pow_three_sub_mul_iff.2
      ⟨mem_criticalPoints_pow_three_sub_mul_iff.1 hx₀, ht₀⟩
  have hF : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) 3
      (fun q : ℝ × ℝ ↦ q.2 ^ 3 - q.1 * q.2) (t₀, x₀) := by
    have h₁ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) 3 (fun q : ℝ × ℝ ↦ q.1) (t₀, x₀) :=
      contMDiffAt_fst
    have h₂ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) 3 (fun q : ℝ × ℝ ↦ q.2) (t₀, x₀) :=
      contMDiffAt_snd
    exact (h₂.pow 3).sub (h₁.mul h₂)
  obtain ⟨ψ, hψ, hψd, -, -, huniq, -⟩ :=
    hnd.exists_contMDiffAt_criticalPoint_continuation hF
  exact ⟨ψ, hψ, hψd, huniq.mono fun q hq ↦ mem_criticalPoints_iff_mfderiv_eq_zero.trans hq⟩

end TauCeti
