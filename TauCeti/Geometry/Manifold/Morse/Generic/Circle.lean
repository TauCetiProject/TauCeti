/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
public import TauCeti.Geometry.Manifold.Morse.AddCircle
public import TauCeti.Geometry.Manifold.Morse.Persistence
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.ManifoldFamily

/-!
# Genericity of Morse functions on the circle: examples

On a compact manifold the `C^n` functions all of whose critical points are nondegenerate form an
open dense set for `2 ≤ n`
(`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint` and
`TauCeti.dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`). This
file tests both halves of that statement on the circle `S¹ = ℝ ⧸ 2πℤ`, and shows that the bound
`n ≥ 2` in the openness theorem cannot be lowered to `n = 1`.

* **Density, but not everything.** For `f_ε(θ) = cos³ θ + ε cos θ`, the derivative is
  `-sin θ (3 cos² θ + ε)`, so `f_ε` is a Morse function exactly when `ε ≠ 0` and `ε ≠ -3`. At
  `ε = 0` the critical points `θ = ±π/2`, where `cos θ = 0`, are degenerate. Since `ε ↦ f_ε` is
  continuous into `C^∞`, the non-Morse function `cos³` is a limit of Morse functions.
* **Openness needs `C²`.** The function `cos` is Morse, so every `C²`-small perturbation of it
  is still Morse. On the other hand the smooth functions
  `g_N(θ) = cos θ + (1 - cos (N θ)) / N²` tend to `cos` in `C¹`, since the perturbation and its
  derivative are bounded by `2 / N²` and `1 / N`, while `g_N'(0) = 0` and
  `g_N''(0) = -1 + 1 = 0`. So every `C¹` neighbourhood of `cos` contains a function with a
  degenerate critical point at `θ = 0`, and the `C¹` functions with only nondegenerate critical
  points do not form an open set.

## Main results

In the namespace `TauCeti`:

* `isMorse_iff_of_forall_coe_eq_cos_pow_three_add_mul_cos`: `cos³ θ + ε cos θ` is Morse exactly
  when `ε ≠ 0` and `ε ≠ -3`.
* `mem_criticalPoints_and_not_isManifoldNondegenerateCriticalPoint_of_cos_eq_zero`: the points
  where `cos θ = 0` are degenerate critical points of `cos³ θ`.
* `mem_closure_setOf_isMorse_and_not_isMorse_of_forall_coe_eq_cos_pow_three`: the non-Morse
  function `cos³ θ` is a limit of Morse functions in `C^∞`.
* `isMorse_of_forall_coe_eq_cos`: `cos θ` is a Morse function.
* `eventually_forall_isManifoldNondegenerateCriticalPoint_of_forall_coe_eq_cos`: `C^n`
  perturbations of `cos θ` with `n ≥ 2` keep all critical points nondegenerate.
* `frequently_mem_criticalPoints_and_not_isManifoldNondegenerateCriticalPoint_zero`: every `C¹`
  neighbourhood of `cos θ` contains a function with a degenerate critical point at `0`.
* `not_isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint_addCircle`:
  on the circle the `C¹` functions with only nondegenerate critical points do not form an open
  set.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Springer, 1976, Chapter 6, §1, where Morse functions
  are shown to form an open dense set in `C^r` for `r ≥ 2`.
-/

public section

open Filter Function Real Set
open scoped Manifold Topology ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

/-- The period of the circle `ℝ ⧸ 2πℤ` is positive. -/
local instance morseCircleTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-! ### The family `cos³ θ + ε cos θ` -/

section CubicCosine

variable {ε : ℝ} {f : AddCircle (2 * π) → ℝ}

private theorem hasDerivAt_cos_pow_three_add_mul_cos (ε t : ℝ) :
    HasDerivAt (fun t ↦ cos t ^ 3 + ε * cos t) (-sin t * (3 * cos t ^ 2 + ε)) t := by
  convert ((Real.hasDerivAt_cos t).fun_pow 3).fun_add ((Real.hasDerivAt_cos t).const_mul ε)
    using 1
  norm_num
  ring

private theorem deriv_cos_pow_three_add_mul_cos (ε : ℝ) :
    deriv (fun t ↦ cos t ^ 3 + ε * cos t) = fun t ↦ -sin t * (3 * cos t ^ 2 + ε) :=
  funext fun t ↦ (hasDerivAt_cos_pow_three_add_mul_cos ε t).deriv

private theorem iteratedDeriv_two_cos_pow_three_add_mul_cos (ε t : ℝ) :
    iteratedDeriv 2 (fun t ↦ cos t ^ 3 + ε * cos t) t =
      cos t * (6 * sin t ^ 2 - 3 * cos t ^ 2 - ε) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_cos_pow_three_add_mul_cos]
  refine HasDerivAt.deriv ?_
  convert (Real.hasDerivAt_sin t).fun_neg.fun_mul
    ((((Real.hasDerivAt_cos t).fun_pow 2).const_mul 3).add_const ε) using 1
  norm_num
  ring

/-- **`cos³ θ + ε cos θ` is Morse exactly when `ε ≠ 0` and `ε ≠ -3`.** Its derivative
`-sin θ (3 cos² θ + ε)` vanishes where `sin θ = 0` and where `3 cos² θ = -ε`. At the first kind
of point the second derivative is `-(3 + ε) cos θ`, and at the second it is `(6 + 2ε) cos θ`, with
`cos θ ≠ 0` unless `ε = 0`. -/
theorem isMorse_iff_of_forall_coe_eq_cos_pow_three_add_mul_cos
    (hf : ∀ t : ℝ, f t = cos t ^ 3 + ε * cos t) :
    IsMorse 𝓘(ℝ) f ↔ ε ≠ 0 ∧ ε ≠ -3 := by
  rw [isMorse_iff_of_forall_coe hf, deriv_cos_pow_three_add_mul_cos]
  simp only [iteratedDeriv_two_cos_pow_three_add_mul_cos]
  refine ⟨fun ⟨_, h⟩ ↦ ⟨?_, ?_⟩, fun ⟨h0, h3⟩ ↦ ⟨by fun_prop, fun t ht ↦ ?_⟩⟩
  · -- At `θ = π / 2` both derivatives of `cos³` vanish.
    rintro rfl
    exact h (π / 2) (by simp) (by simp)
  · -- At `θ = 0` both derivatives of `cos³ θ - 3 cos θ` vanish.
    rintro rfl
    exact h 0 (by simp) (by norm_num)
  rcases mul_eq_zero.1 ht with hs | hc
  · have hs : sin t = 0 := neg_eq_zero.1 hs
    have hc : cos t ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq t]
    refine mul_ne_zero (fun h ↦ by simp [h] at hc) ?_
    rw [hs, hc]
    intro h
    exact h3 (by linarith)
  · have hc0 : cos t ≠ 0 := fun h ↦ h0 (by simpa [h] using hc)
    have : 6 * sin t ^ 2 - 3 * cos t ^ 2 - ε = 6 + 2 * ε := by linarith [sin_sq_add_cos_sq t]
    refine mul_ne_zero hc0 ?_
    rw [this]
    intro h
    exact h3 (by linarith)

/-- **The degenerate critical points of `cos³ θ`.** Where `cos θ = 0`, that is at `θ = ±π/2`,
the function `cos³ θ` has a critical point at which its second derivative vanishes. -/
theorem mem_criticalPoints_and_not_isManifoldNondegenerateCriticalPoint_of_cos_eq_zero
    (hf : ∀ t : ℝ, f t = cos t ^ 3) {t : ℝ} (ht : cos t = 0) :
    (t : AddCircle (2 * π)) ∈ criticalPoints 𝓘(ℝ) f ∧
      ¬ IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) f t := by
  have hf' (t : ℝ) : f t = cos t ^ 3 + 0 * cos t := by rw [hf]; ring
  rw [coe_mem_criticalPoints_iff_of_forall_coe hf',
    isManifoldNondegenerateCriticalPoint_coe_iff_of_forall_coe hf' (by fun_prop),
    deriv_cos_pow_three_add_mul_cos, iteratedDeriv_two_cos_pow_three_add_mul_cos]
  simp [ht]

/-- **The non-Morse function `cos³ θ` is a limit of Morse functions.** The smooth functions
`cos³ θ + ε cos θ` are Morse for `ε > 0` and tend to `cos³ θ` in the weak Whitney topology on
`C^∞` as `ε` tends to `0`. -/
theorem mem_closure_setOf_isMorse_and_not_isMorse_of_forall_coe_eq_cos_pow_three
    (f : C^∞⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯) (hf : ∀ t : ℝ, f t = cos t ^ 3) :
    f ∈ closure {g : C^∞⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ | IsMorse 𝓘(ℝ) g} ∧
      ¬ IsMorse 𝓘(ℝ) f := by
  have hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (cos_periodic.lift : AddCircle (2 * π) → ℝ) :=
    (contMDiff_iff_contDiff_of_forall_coe fun t ↦ Periodic.lift_coe _ t).2 contDiff_cos
  let Φ (ε : ℝ) : C^∞⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ f x + ε * cos_periodic.lift x, f.contMDiff.add (contMDiff_const.mul hc)⟩
  have hΦ : Continuous Φ := ContMDiff.continuous_manifoldWeakWhitney (I' := 𝓘(ℝ))
    ((f.contMDiff.comp contMDiff_snd).add (contMDiff_fst.mul (hc.comp contMDiff_snd)))
  have hΦ0 : Φ 0 = f := by ext x; simp [Φ]
  have hΦt (ε t : ℝ) : Φ ε t = cos t ^ 3 + ε * cos t := by simp [Φ, hf]
  refine ⟨mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
    (hΦ0 ▸ (hΦ.tendsto 0).mono_left nhdsWithin_le_nhds) ?_, fun h ↦ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (isMorse_iff_of_forall_coe_eq_cos_pow_three_add_mul_cos (hΦt ε)).2
      ⟨hε.ne', by linarith⟩
  · exact (isMorse_iff_of_forall_coe_eq_cos_pow_three_add_mul_cos (ε := 0)
      fun t ↦ by rw [hf]; ring).1 h |>.1 rfl

end CubicCosine

/-! ### Perturbations of `cos θ` -/

section Cosine

variable {f : AddCircle (2 * π) → ℝ}

/-- **`cos θ` is a Morse function on the circle**, with critical points at `θ = 0` and `θ = π`. -/
theorem isMorse_of_forall_coe_eq_cos (hf : ∀ t : ℝ, f t = cos t) : IsMorse 𝓘(ℝ) f := by
  rw [isMorse_iff_of_forall_coe hf]
  refine ⟨contDiff_cos, fun t ht ↦ ?_⟩
  simp only [Real.deriv_cos', neg_eq_zero] at ht
  have h2 : iteratedDeriv 2 cos t = -cos t := by simp
  rw [h2, neg_ne_zero]
  intro h
  simpa [ht, h] using sin_sq_add_cos_sq t

/-- **`cos θ` stays Morse under `C²`-small perturbations.** For `n ≥ 2`, every `C^n` function
close enough to `cos θ` in the weak Whitney topology has only nondegenerate critical points. -/
theorem eventually_forall_isManifoldNondegenerateCriticalPoint_of_forall_coe_eq_cos
    {n : WithTop ℕ∞} (hn : 2 ≤ n) (c : C^n⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯)
    (hc : ∀ t : ℝ, c t = cos t) :
    ∀ᶠ g : C^n⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ in 𝓝 c,
      ∀ x ∈ criticalPoints 𝓘(ℝ) g, IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) g x :=
  (isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint hn).mem_nhds
    fun _ hx ↦
      (isMorse_of_forall_coe_eq_cos hc).isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        hx

/-- The perturbation `(1 - cos (N θ)) / N²` of `cos θ`, as a function on the circle. -/
private noncomputable def cosPerturbation (N : ℕ) : AddCircle (2 * π) → ℝ :=
  Periodic.lift (f := fun t ↦ (1 - cos (N * t)) / N ^ 2) fun t ↦ by
    simp only [mul_add, cos_add_nat_mul_two_pi]

private theorem cosPerturbation_coe (N : ℕ) (t : ℝ) :
    cosPerturbation N t = (1 - cos (N * t)) / N ^ 2 :=
  Periodic.lift_coe _ t

private theorem hasDerivAt_cosPerturbation (N : ℕ) (t : ℝ) :
    HasDerivAt (fun t ↦ (1 - cos (N * t)) / N ^ 2) (N * sin (N * t) / N ^ 2) t := by
  convert (((hasDerivAt_id' t).const_mul (N : ℝ)).cos.const_sub 1).div_const ((N : ℝ) ^ 2)
    using 1
  ring

/-- The perturbation `(1 - cos (N θ)) / N²` and its derivative `sin (N θ) / N` are bounded by
`2 / N`: read in any chart of the circle, so is its coordinate derivative of order at most one. -/
private theorem norm_chartIteratedFDeriv_cosPerturbation_le {N : ℕ} (hN : 1 ≤ N)
    (g : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯) (hg : ⇑g = cosPerturbation N)
    (x : AddCircle (2 * π)) {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ 1)
    (z : (extChartAt 𝓘(ℝ) x).target) :
    ‖ContMDiffMap.chartIteratedFDeriv g x m hm z‖ ≤ 2 / N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  rw [ContMDiffMap.chartIteratedFDeriv_self_target_apply,
    iteratedFDerivWithin_congr (f := fun t ↦ (1 - cos (N * t)) / N ^ 2)
      (fun u hu ↦ by
        rw [comp_apply, hg, AddCircle.extChartAt_symm_apply x hu, cosPerturbation_coe]) z.2,
    iteratedFDerivWithin_of_isOpen m (isOpen_extChartAt_target x) z.2,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hm1 : m ≤ 1 := by exact_mod_cast hm
  interval_cases m
  · -- The perturbation itself is at most `2 / N² ≤ 2 / N`.
    have h1 : 0 ≤ 1 - cos (N * (z : ℝ)) := by linarith [cos_le_one (N * (z : ℝ))]
    have h2 : 1 - cos (N * (z : ℝ)) ≤ 2 := by linarith [neg_one_le_cos (N * (z : ℝ))]
    rw [iteratedDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (div_nonneg h1 (sq_nonneg _)),
      div_le_div_iff₀ (pow_pos hNpos 2) hNpos]
    nlinarith
  · -- Its derivative is `sin (N θ) / N`.
    have hN2 : (N : ℝ) * sin (N * z) / N ^ 2 = sin (N * z) / N := by field_simp
    rw [iteratedDeriv_one, (hasDerivAt_cosPerturbation N z).deriv, hN2, norm_div,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNpos]
    gcongr
    exact (abs_sin_le_one _).trans one_le_two

/-- **`C¹`-small perturbations of `cos θ` can create a degenerate critical point.** Every
neighbourhood of `cos θ` in the weak Whitney topology on `C¹` contains a function having a
degenerate critical point at `θ = 0`. Indeed `cos θ + (1 - cos (N θ)) / N²` tends to `cos θ` in
`C¹`, and its first and second derivatives vanish at `θ = 0`. -/
theorem frequently_mem_criticalPoints_and_not_isManifoldNondegenerateCriticalPoint_zero
    (c : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯) (hc : ∀ t : ℝ, c t = cos t) :
    ∃ᶠ g : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ in 𝓝 c,
      (0 : AddCircle (2 * π)) ∈ criticalPoints 𝓘(ℝ) g ∧
        ¬ IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) g 0 := by
  have hcont (N : ℕ) : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (cosPerturbation N) :=
    (contMDiff_iff_contDiff_of_forall_coe (cosPerturbation_coe N)).2 (by fun_prop)
  let h (N : ℕ) : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ := ⟨cosPerturbation N, hcont N⟩
  -- The perturbations tend to `0` in `C¹`: each chart seminorm of order at most one is at most
  -- `2 / N`.
  have hlim : Tendsto h atTop (𝓝 0) := by
    rw [ContMDiffMap.withSeminorms_manifoldWeakWhitney.tendsto_nhds]
    rintro ⟨x, ⟨m, hm⟩, K⟩ ε hε
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually (gt_mem_nhds hε)] with N hN hNε
    rw [sub_zero, ContMDiffMap.chartSeminormFamily_apply]
    refine lt_of_le_of_lt ?_ hNε
    rw [ContMDiffMap.chartDerivativeSeminorm_le_iff _ _ _ _ _ (by positivity)]
    exact fun z _ ↦ norm_chartIteratedFDeriv_cosPerturbation_le hN (h N) rfl x hm z
  have hlim' : Tendsto (fun N ↦ c + h N) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add hlim
  refine hlim'.frequently (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  -- `G(θ) = cos θ + (1 - cos (N θ)) / N²` has `G'(0) = 0` and `G''(0) = -1 + 1 = 0`.
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hG (t : ℝ) : (c + h N) t = cos t + (1 - cos (N * t)) / N ^ 2 := by
    rw [ContMDiffMap.coe_add, Pi.add_apply, hc, ContMDiffMap.coeFn_mk, cosPerturbation_coe]
  have hG' : deriv (fun t ↦ cos t + (1 - cos (N * t)) / N ^ 2) =
      fun t ↦ -sin t + N * sin (N * t) / N ^ 2 :=
    funext fun t ↦ ((Real.hasDerivAt_cos t).add (hasDerivAt_cosPerturbation N t)).deriv
  have hG'' : iteratedDeriv 2 (fun t ↦ cos t + (1 - cos (N * t)) / N ^ 2) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hG', ((Real.hasDerivAt_sin 0).fun_neg.fun_add
      ((((hasDerivAt_id' (0 : ℝ)).const_mul (N : ℝ)).sin.const_mul (N : ℝ)).div_const
        ((N : ℝ) ^ 2))).deriv]
    simp only [mul_zero, cos_zero, mul_one]
    field_simp [hN0]
    ring
  have := (isManifoldNondegenerateCriticalPoint_coe_iff_of_forall_coe hG (by fun_prop) 0).not
  rw [QuotientAddGroup.mk_zero] at this
  refine ⟨?_, this.2 fun h ↦ h.2 hG''⟩
  rw [← QuotientAddGroup.mk_zero, coe_mem_criticalPoints_iff_of_forall_coe hG, hG']
  simp

/-- **Openness of Morse functions fails in `C¹`.** On the circle, the `C¹` functions all of whose
critical points are nondegenerate do not form an open set in the weak Whitney topology: `cos θ`
lies in this set, but every `C¹` neighbourhood of it contains functions with a degenerate
critical point. So the bound `n ≥ 2` of
`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint` is
sharp. -/
theorem not_isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint_addCircle :
    ¬ IsOpen {f : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ |
      ∀ x ∈ criticalPoints 𝓘(ℝ) f, IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) f x} := by
  intro hopen
  have hc : ∀ t : ℝ, cos_periodic.lift (t : AddCircle (2 * π)) = cos t :=
    fun t ↦ Periodic.lift_coe _ t
  let c : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ :=
    ⟨cos_periodic.lift, (contMDiff_iff_contDiff_of_forall_coe hc).2 (by fun_prop)⟩
  have hmem : c ∈ {f : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ |
      ∀ x ∈ criticalPoints 𝓘(ℝ) f, IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) f x} :=
    fun _ hx ↦
      (isMorse_of_forall_coe_eq_cos hc).isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        hx
  obtain ⟨g, ⟨hg0, hg⟩, hgS⟩ :=
    ((frequently_mem_criticalPoints_and_not_isManifoldNondegenerateCriticalPoint_zero c
      hc).and_eventually (hopen.mem_nhds hmem)).exists
  exact hg (hgS 0 hg0)

end Cosine

end TauCeti
