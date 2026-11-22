/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Cerf.Isolated
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import TauCeti.Analysis.Calculus.Bifurcation
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Birth–death points are folds of the critical locus

Let `f t : E → ℝ` be a one-parameter family of functions on a finite-dimensional real normed
space, jointly `C³`, and let `x₀` be a *birth–death point* of `f t₀`: a critical point at which
the family is transverse (the derivative of the parametrized differential `(t, x) ↦ d(f t)_x` is
onto) and whose Hessian has a nonzero kernel vector `v` with

`D³(f t₀)_{x₀} (v, v, v) · ∂ₜ (d(f t)_{x₀}) v ≠ 0`.

The sign of this product does not depend on `v`, which is determined up to a scalar factor `c`,
by which the product is multiplied by `c⁴`. This file proves that near a birth–death point a
pair of critical points is born or dies, as in Cerf's local model `x³ / 3 - s x` of
`TauCeti.Analysis.Calculus.Morse.BirthDeath`: there is a neighbourhood `U` of `x₀` such that

* `x₀` is the only critical point of `f t₀` in `U`;
* if the product is negative, `f t` has no critical point in `U` for `t < t₀` close to `t₀`, and
  exactly two, both nondegenerate, for `t > t₀` close to `t₀`
  (`TauCeti.exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_neg`);
* if the product is positive, the same holds with the two sides exchanged
  (`TauCeti.exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_pos`).

For the model `x³ / 3 - t x` at `(0, 0)` the third derivative is `2` and the parameter derivative
of the differential is `-1`, so the product is `-2`: the two critical points `±√t` exist for
`t > 0`.

The proof follows the critical locus. Choose a functional `ℓ` with `ℓ v = 1`. The map
`Φ (t, x) = (d(f t)_x, ℓ x)` from `ℝ × E` to `E* × ℝ` has an invertible derivative at
`(t₀, x₀)`, by transversality and because the kernel of the Hessian is the line through `v`. By
the inverse function theorem, the critical points of the family near `(t₀, x₀)` form the `C²`
curve `c(s) = Φ⁻¹ (0, ℓ x₀ + s)`, with `c(0) = (t₀, x₀)` and `c'(0) = (0, v)`, and the
critical points of `f t` near `x₀` are the points `c(s)` with `τ(s) = t`, where `τ(s)` is the
parameter component of `c(s)`. Differentiating `d(f τ(s))_{ξ(s)} = 0`, with `ξ(s)` the space
component, and pairing with `ξ'(s)` gives

`τ'(s) · ∂ₜ (d(f t)_{ξ(s)}) ξ'(s) + Hess(f τ(s))_{ξ(s)} (ξ'(s), ξ'(s)) = 0`.

The second term vanishes at `s = 0` and has derivative `D³(f t₀)_{x₀} (v, v, v)` there, by the
symmetry of the Hessian, while `τ'(0) = 0`. Dividing by `s` and letting `s → 0` gives

`τ''(0) = -D³(f t₀)_{x₀} (v, v, v) / ∂ₜ (d(f t)_{x₀}) v`,

which is positive when the product above is negative. So `τ` has a fold at `0`, and the fold
theorem `TauCeti.eventually_fold` for `τ(s) - t` shows that `τ` takes each value slightly above
`t₀` exactly twice near `0`, and no value below `t₀`. That the two critical points are
nondegenerate is `TauCeti.eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero`.

## Main results

* `TauCeti.exists_criticalCurve`: the critical points of the family near a transverse degenerate
  critical point form a `C²` curve through it, with velocity `(0, v)` for a kernel vector `v` of
  the Hessian.
* `TauCeti.exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_neg`: a birth at a
  birth–death point where the product is negative.
* `TauCeti.exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_pos`: a death at a
  birth–death point where the product is positive.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (generic one-parameter families and bifurcations).
-/

public section

open Function Module Set Filter Metric
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → ℝ} {t : ℝ} {x : E}

/-! ### The parameter along a curve of critical points -/

/-- **Differentiating the critical equation along a curve of critical points.** If `c` is a curve
of critical points of the family, `C²` at `0` and through a point where the family is jointly
`C²`, then near `0`, with `c' = (τ', ξ')` the velocity of `c`,

`τ' · ∂ₜ (d(f t)_{ξ}) ξ' + Hess(f τ)_{ξ} (ξ', ξ') = 0`,

where the parameter derivative of the differential is written as the derivative of
`(t, x) ↦ d(f t)_x` in the direction `(1, 0)`. -/
private theorem eventually_deriv_fst_mul_add_eq_zero {c : ℝ → ℝ × E}
    (hf : ContDiffAt ℝ 2 (uncurry f) (c 0)) (hcd : ContDiffAt ℝ 2 c 0)
    (hcrit : ∀ᶠ s in 𝓝 0, fderiv ℝ (f (c s).1) (c s).2 = 0) :
    ∀ᶠ s in 𝓝 0, (deriv c s).1 * fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (c s) (1, 0)
      (deriv c s).2 + fderiv ℝ (fderiv ℝ (f (c s).1)) (c s).2 (deriv c s).2 (deriv c s).2 = 0 := by
  set G : ℝ × E → StrongDual ℝ E := fun w ↦ fderiv ℝ (f w.1) w.2
  have hfc : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 2 (uncurry f) ((c s).1, (c s).2) :=
    hcd.continuousAt.tendsto.eventually (hf.eventually (by simp))
  filter_upwards [hcrit.eventually_nhds, hcd.eventually (by simp), hfc] with s hs hsd hsf
  have hGc : G ∘ c =ᶠ[𝓝 s] fun _ ↦ 0 := hs.mono fun _ h ↦ by simpa [G] using h
  have hGd : DifferentiableAt ℝ G (c s) :=
    (hsf.fderiv_slice (m := 1) (by norm_num)).differentiableAt one_ne_zero
  -- The derivative of `s ↦ d(f τ(s))_{ξ(s)}`, which vanishes identically near `s`, is zero.
  have h0 : fderiv ℝ G (c s) (deriv c s) = 0 := by
    rw [← (hGd.hasFDerivAt.comp_hasDerivAt s
      (hsd.differentiableAt two_ne_zero).hasDerivAt).deriv]
    exact hGc.deriv_eq.trans (deriv_const _ _)
  have hHw : fderiv ℝ G (c s) (0, (deriv c s).2) =
      fderiv ℝ (fderiv ℝ (f (c s).1)) (c s).2 (deriv c s).2 := by
    simpa using fderiv_fderiv_apply hsf (0, (deriv c s).2)
  have hsplit : deriv c s = (deriv c s).1 • ((1 : ℝ), (0 : E)) + ((0 : ℝ), (deriv c s).2) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, hHw] at h0
  simpa using congrArg (· (deriv c s).2) h0

/-- **The parameter has a fold along the critical curve.** Let `c` be a `C²` curve of critical
points of the family through `(t, x)`, with velocity `(0, v)` for a kernel vector `v` of the
Hessian of `f t` at `x`. If `D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v < 0`, then the second
derivative at `0` of the parameter component of `c` is positive. -/
private theorem deriv_deriv_fst_pos (hf : ContDiffAt ℝ 3 (uncurry f) (t, x)) {v : E}
    (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hsign : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v *
      deriv (fun s ↦ fderiv ℝ (f s) x) t v < 0)
    {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x)) (hcd : ContDiffAt ℝ 2 c 0)
    (hc' : HasDerivAt c (0, v) 0) (hcrit : ∀ᶠ s in 𝓝 0, fderiv ℝ (f (c s).1) (c s).2 = 0) :
    0 < deriv (fun s ↦ (deriv c s).1) 0 := by
  have hf2 : ContDiffAt ℝ 2 (uncurry f) (t, x) := hf.of_le (by norm_num)
  have hid := eventually_deriv_fst_mul_add_eq_zero (hc0 ▸ hf2) hcd hcrit
  set G : ℝ × E → StrongDual ℝ E := fun w ↦ fderiv ℝ (f w.1) w.2
  set H : ℝ × E → E →L[ℝ] StrongDual ℝ E := fun w ↦ fderiv ℝ (fderiv ℝ (f w.1)) w.2
  set κ := fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v
  set a := deriv (fun s ↦ fderiv ℝ (f s) x) t v
  have hG : ContDiffAt ℝ 2 G (t, x) := hf.fderiv_slice (m := 2) le_rfl
  have hH : ContDiffAt ℝ 1 H (t, x) := hG.fderiv_slice (m := 1) le_rfl
  -- The velocity `c' = (τ', w)` is differentiable at `0`, with `τ' 0 = 0` and `w 0 = v`.
  have hc'd : HasDerivAt (deriv c) (deriv (deriv c) 0) 0 :=
    (((hcd.fderiv_right (m := 1) le_rfl).clm_apply contDiffAt_const).differentiableAt
      one_ne_zero).hasDerivAt
  set w : ℝ → E := fun s ↦ (deriv c s).2
  have hw : HasDerivAt w (deriv (deriv c) 0).2 0 :=
    (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt _ hc'd
  have hw0 : w 0 = v := by simp [w, hc'.deriv]
  have hHv : H (t, x) v = 0 := hv
  -- `q s = Hess (w s, w s)` vanishes at `0` with derivative `κ` there, by the symmetry of the
  -- Hessian.
  have hq : HasDerivAt (fun s ↦ H (c s) (w s) (w s)) κ 0 := by
    have hH' : HasFDerivAt H (fderiv ℝ H (t, x)) (c 0) :=
      hc0 ▸ (hH.differentiableAt one_ne_zero).hasFDerivAt
    have hκ : fderiv ℝ H (t, x) (0, v) v v = κ := by
      rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right
        (hH.differentiableAt one_ne_zero)]
      simp [H, κ]
    have hHc : HasDerivAt (H ∘ c) (fderiv ℝ H (t, x) (0, v)) 0 := by
      simpa using (hH'.comp 0 hc'.hasFDerivAt).hasDerivAt
    have hsymm : H (t, x) (deriv (deriv c) 0).2 v = H (t, x) v (deriv (deriv c) 0).2 :=
      fderiv_fderiv_apply_comm_of_uncurry hf2 _ v
    simpa [hw0, hc0, hκ, hsymm, hHv] using (hHc.clm_apply hw).clm_apply hw
  -- `d s = ∂ₜ (d(f t)_{ξ(s)}) (w s)` tends to `a`.
  have hd : Tendsto (fun s ↦ fderiv ℝ G (c s) (1, 0) (w s)) (𝓝 0) (𝓝 a) := by
    have hd0 : fderiv ℝ G (c 0) (1, 0) (w 0) = a := by
      rw [hw0, hc0]
      simpa using congrArg (· v) (fderiv_fderiv_apply hf2 ((1 : ℝ), (0 : E)))
    rw [← hd0]
    have hGc : ContinuousAt (fun s ↦ fderiv ℝ G (c s)) 0 :=
      (hc0 ▸ (hG.fderiv_right (m := 1) (by norm_num)).continuousAt).comp hcd.continuousAt
    exact ((hGc.clm_apply continuousAt_const).clm_apply hw.continuousAt).tendsto
  have ha : a ≠ 0 := fun h ↦ by simp [h] at hsign
  rw [(hasDerivAt_neg_div_of_mul_add_eq_zero hid (by simp [hc'.deriv]) hq hd ha).deriv]
  have := div_pos (neg_pos.2 hsign) (by positivity : 0 < a ^ 2)
  rwa [show -(κ * a) / a ^ 2 = -κ / a by field_simp] at this

/-- **The critical curve folds back over the parameter.** Under the hypotheses of
`deriv_deriv_fst_pos`, for every small `δ > 0` and every `s` near `t`, the parameter component of
`c` on `(-δ, δ)` stays above `s` when `s < t`, takes the value `t` only at `0`, and takes the
value `s` exactly twice, once on each side of `0`, when `s > t`. This is `eventually_fold` for
`F (σ, u) = (c σ).1 - t - u`. -/
private theorem eventually_fold_criticalCurve (hf : ContDiffAt ℝ 3 (uncurry f) (t, x)) {v : E}
    (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hsign : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v *
      deriv (fun s ↦ fderiv ℝ (f s) x) t v < 0)
    {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x)) (hcd : ContDiffAt ℝ 2 c 0)
    (hc' : HasDerivAt c (0, v) 0) (hcrit : ∀ᶠ s in 𝓝 0, fderiv ℝ (f (c s).1) (c s).2 = 0) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ s in 𝓝 t, (s < t → ∀ σ ∈ Ioo (-δ) δ, s < (c σ).1) ∧
      (s = t → {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = {0}) ∧
      (t < s → ∃ x₁ ∈ Ioo (-δ) 0, ∃ x₂ ∈ Ioo 0 δ, {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = {x₁, x₂}) := by
  set F : ℝ × ℝ → ℝ := fun p ↦ (c p.1).1 - t - p.2
  have hF : ContDiffAt ℝ 2 F 0 :=
    ((hcd.comp (0 : ℝ × ℝ) contDiffAt_fst).fst.sub contDiffAt_const).sub contDiffAt_snd
  have hd : ∀ᶠ σ in 𝓝 0, HasDerivAt (fun σ ↦ F (σ, 0)) (deriv c σ).1 σ := by
    filter_upwards [hcd.eventually (by simp)] with σ hσ
    simpa [F] using ((ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt σ
      (hσ.differentiableAt two_ne_zero).hasDerivAt).sub_const t
  have hev : deriv (fun σ ↦ F (σ, 0)) =ᶠ[𝓝 0] fun σ ↦ (deriv c σ).1 :=
    hd.mono fun _ h ↦ h.deriv
  have hb : deriv (fun u ↦ F (0, u)) 0 = -1 := by
    simp [F]
  have hfold := eventually_fold hF (by simp [F, hc0]) (by simp [hev.self_of_nhds, hc'.deriv])
    (by rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
        exact deriv_deriv_fst_pos hf hv hsign hc0 hcd hc' hcrit) (by rw [hb]; norm_num)
  have hst : Tendsto (fun s ↦ s - t) (𝓝 t) (𝓝 0) := by
    simpa using (continuous_sub_right t).tendsto t
  filter_upwards [hfold] with δ hδ
  filter_upwards [hst.eventually hδ] with s ⟨hlt, heq, hgt⟩
  rw [hb] at hlt hgt
  have hFs : ∀ σ, F (σ, s - t) = (c σ).1 - s := fun σ ↦ by simp only [F]; ring
  have hset : {σ ∈ Ioo (-δ) δ | F (σ, s - t) = 0} = {σ ∈ Ioo (-δ) δ | (c σ).1 = s} := by
    ext σ
    simp [hFs, sub_eq_zero]
  refine ⟨fun h σ hσ ↦ ?_, fun h ↦ hset ▸ heq (by rw [h, sub_self]), fun h ↦ ?_⟩
  · have := hlt (by linarith) σ hσ
    rw [hFs] at this
    linarith
  · obtain ⟨x₁, hx₁, x₂, hx₂, hs, -⟩ := hgt (by linarith)
    exact ⟨x₁, hx₁, x₂, hx₂, hset ▸ hs⟩

/-! ### Critical points near a curve of critical points -/

/-- **Critical points near `(t, x)` lie on the critical curve.** If every critical point `z` of
the family in a neighbourhood `N` of `(t, x)` is the point `c (ℓ z.2 - ℓ x)` of a curve `c`, and
the critical points near `(t, x)` other than `(t, x)` are nondegenerate, then for some `r > 0`
every critical point `y` of `f s` with `|s - t| < r` and `y ∈ ball x r` is `c σ` for
`σ = ℓ y - ℓ x ∈ (-δ, δ)`, and is nondegenerate unless `(s, y) = (t, x)`. -/
private theorem exists_pos_forall_mem_ball {c : ℝ → ℝ × E} {ℓ : StrongDual ℝ E}
    {N : Set (ℝ × E)} (hN : N ∈ 𝓝 (t, x))
    (hcN : ∀ z ∈ N, fderiv ℝ (f z.1) z.2 = 0 → c (ℓ z.2 - ℓ x) = z)
    (hnd : ∀ᶠ z in 𝓝[≠] (t, x), fderiv ℝ (f z.1) z.2 = 0 →
      IsNondegenerateCriticalPoint (f z.1) z.2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ s y, dist s t < r → y ∈ ball x r → fderiv ℝ (f s) y = 0 →
      ℓ y - ℓ x ∈ Ioo (-δ) δ ∧ c (ℓ y - ℓ x) = (s, y) ∧
        ((s, y) ≠ (t, x) → IsNondegenerateCriticalPoint (f s) y) := by
  obtain ⟨r₁, hr₁, hr₁N⟩ := Metric.eventually_nhds_iff.1
    ((eventually_mem_set.2 hN).and (eventually_nhdsWithin_iff.1 hnd))
  obtain ⟨r₂, hr₂, hr₂ℓ⟩ := Metric.eventually_nhds_iff.1
    (Metric.tendsto_nhds.1 (ℓ.continuous.tendsto x) δ hδ)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun s y hs hy hy0 ↦ ?_⟩
  have hz : dist (s, y) (t, x) < r₁ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hs.trans_le (min_le_left _ _), (mem_ball.1 hy).trans_le (min_le_left _ _)⟩
  have hℓy := hr₂ℓ ((mem_ball.1 hy).trans_le (min_le_right _ _))
  rw [Real.dist_eq] at hℓy
  exact ⟨mem_Ioo.2 (abs_lt.1 hℓy), hcN _ (hr₁N hz).1 hy0,
    fun hne ↦ (hr₁N hz).2 hne hy0⟩

/-- **Two parameter values on the critical curve give two critical points.** Let `c` be a curve of
critical points on `(-δ, δ)`, along which `ℓ` restricted to the space component increases at unit
rate. Suppose that every critical point `y ∈ U` of `f s` is the point `c σ` for
`σ = ℓ y - ℓ x ∈ (-δ, δ)`, and that the parameter component of `c` takes the value `s` on
`(-δ, δ)` exactly at two points `x₁ ≠ x₂`, over `U`. Then `f s` has exactly two critical points
in `U`. -/
private theorem ncard_setOf_fderiv_eq_zero_eq_two {c : ℝ → ℝ × E} {ℓ : StrongDual ℝ E}
    {U : Set E} {δ s x₁ x₂ : ℝ}
    (hcrit : ∀ σ ∈ Ioo (-δ) δ, fderiv ℝ (f (c σ).1) (c σ).2 = 0 ∧ ℓ (c σ).2 = ℓ x + σ)
    (hcurve : ∀ y ∈ U, fderiv ℝ (f s) y = 0 → ℓ y - ℓ x ∈ Ioo (-δ) δ ∧ c (ℓ y - ℓ x) = (s, y))
    (hset : {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = {x₁, x₂}) (hne : x₁ ≠ x₂)
    (h₁ : (c x₁).2 ∈ U) (h₂ : (c x₂).2 ∈ U) :
    {y ∈ U | fderiv ℝ (f s) y = 0}.ncard = 2 := by
  have hmem : ∀ σ ∈ ({x₁, x₂} : Set ℝ), σ ∈ Ioo (-δ) δ ∧ (c σ).1 = s := fun σ hσ ↦ by
    rw [← hset] at hσ
    exact hσ
  have hpair : {y ∈ U | fderiv ℝ (f s) y = 0} = (fun σ ↦ (c σ).2) '' {x₁, x₂} := by
    ext y
    refine ⟨fun ⟨hy, hy0⟩ ↦ ?_, ?_⟩
    · obtain ⟨hσ, hcσ⟩ := hcurve y hy hy0
      exact ⟨ℓ y - ℓ x, hset ▸ ⟨hσ, by simp [hcσ]⟩, by simp [hcσ]⟩
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨hσI, hτσ⟩ := hmem σ hσ
      refine ⟨?_, hτσ ▸ (hcrit σ hσI).1⟩
      rcases hσ with rfl | rfl
      exacts [h₁, h₂]
  rw [hpair, Set.image_pair, Set.ncard_pair]
  intro h
  have h₁ := (hcrit x₁ (hmem x₁ (by simp)).1).2
  rw [h, (hcrit x₂ (hmem x₂ (by simp)).1).2] at h₁
  exact hne (by linarith)

/-- **Two critical points after the fold.** In the situation of
`ncard_setOf_fderiv_eq_zero_eq_two`, suppose that for `s > t` close to `t` the parameter
component of `c` takes the value `s` exactly twice on `(-δ₀, δ₀)` and exactly twice on
`(-δ₁, δ₁)`, once on each side of `0`, where `δ₁ ≤ δ₀` and the curve stays over `ball x r` on
`(-δ₁, δ₁)`. If the critical points in `ball x r` of `f s`, for `|s - t| < r`, are points `c σ`
with `σ ∈ (-δ₀, δ₀)`, nondegenerate away from `(t, x)`, then for `s > t` close to `t` the function
`f s` has exactly two critical points in `ball x r`, both nondegenerate. -/
private theorem eventually_ncard_setOf_fderiv_eq_zero_eq_two {c : ℝ → ℝ × E}
    {ℓ : StrongDual ℝ E} {δ₀ δ₁ r : ℝ} (hδ : δ₁ ≤ δ₀) (hr : 0 < r)
    (hcrit : ∀ σ ∈ Ioo (-δ₀) δ₀, fderiv ℝ (f (c σ).1) (c σ).2 = 0 ∧ ℓ (c σ).2 = ℓ x + σ)
    (hcurve : ∀ s y, dist s t < r → y ∈ ball x r → fderiv ℝ (f s) y = 0 →
      ℓ y - ℓ x ∈ Ioo (-δ₀) δ₀ ∧ c (ℓ y - ℓ x) = (s, y) ∧
        ((s, y) ≠ (t, x) → IsNondegenerateCriticalPoint (f s) y))
    (hU : ∀ σ ∈ Ioo (-δ₁) δ₁, (c σ).2 ∈ ball x r)
    (h₀ : ∀ᶠ s in 𝓝 t, t < s → ∃ x₁ ∈ Ioo (-δ₀) 0, ∃ x₂ ∈ Ioo 0 δ₀,
      {σ ∈ Ioo (-δ₀) δ₀ | (c σ).1 = s} = {x₁, x₂})
    (h₁ : ∀ᶠ s in 𝓝 t, t < s → ∃ x₁ ∈ Ioo (-δ₁) 0, ∃ x₂ ∈ Ioo 0 δ₁,
      {σ ∈ Ioo (-δ₁) δ₁ | (c σ).1 = s} = {x₁, x₂}) :
    ∀ᶠ s in 𝓝[>] t, {y ∈ ball x r | fderiv ℝ (f s) y = 0}.ncard = 2 ∧
      ∀ y ∈ ball x r, fderiv ℝ (f s) y = 0 → IsNondegenerateCriticalPoint (f s) y := by
  filter_upwards [nhdsWithin_le_nhds (h₀.and h₁), Ioo_mem_nhdsGT (show t < t + r by linarith)]
    with s ⟨h₀, h₁⟩ hs
  have hst : dist s t < r := by
    rw [← mem_ball, Real.ball_eq_Ioo]
    exact Ioo_subset_Ioo_left (by linarith) hs
  obtain ⟨x₁, hx₁, x₂, hx₂, hset₀⟩ := h₀ hs.1
  obtain ⟨y₁, hy₁, y₂, hy₂, hset₁⟩ := h₁ hs.1
  -- The two solutions in `(-δ₁, δ₁)` are the two solutions in `(-δ₀, δ₀)`.
  have hsub : ∀ σ ∈ ({y₁, y₂} : Set ℝ), σ ∈ ({x₁, x₂} : Set ℝ) := fun σ hσ ↦ by
    rw [← hset₁] at hσ
    rw [← hset₀]
    exact ⟨⟨by linarith [hσ.1.1], by linarith [hσ.1.2]⟩, hσ.2⟩
  have he₁ : y₁ = x₁ := (hsub y₁ (by simp)).resolve_right fun h ↦ by
    linarith [hy₁.2, hx₂.1, mem_singleton_iff.1 h]
  have he₂ : y₂ = x₂ := mem_singleton_iff.1 <| (hsub y₂ (by simp)).resolve_left fun h ↦ by
    linarith [hy₂.1, hx₁.2]
  subst he₁ he₂
  refine ⟨ncard_setOf_fderiv_eq_zero_eq_two hcrit
    (fun y hy hy0 ↦ (hcurve s y hst hy hy0).imp_right And.left) hset₀
    (by linarith [hy₁.2, hy₂.1]) (hU _ ⟨hy₁.1, by linarith [hy₁.1, hy₁.2]⟩)
    (hU _ ⟨by linarith [hy₂.1, hy₂.2], hy₂.2⟩), fun y hy hy0 ↦
      (hcurve s y hst hy hy0).2.2 fun h ↦ ?_⟩
  linarith [congrArg Prod.fst h, hs.1]

/-! ### The critical curve through a birth–death point -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **The derivative of the augmented differential is invertible at a birth–death point.** At a
transverse point where the Hessian of `f t` at `x` has a nonzero kernel vector `v` and `ℓ v = 1`,
the derivative of `(t, x) ↦ (d(f t)_x, ℓ x)`, which sends `(τ, ξ)` to
`(τ ∂ₜ (d(f t)_x) + Hess(f t)_x ξ, ℓ ξ)`, is a linear isomorphism carrying `(0, v)` to `(0, 1)`. -/
private theorem exists_continuousLinearEquiv_fderiv_prod (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x))) {v : E}
    (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0) (hv0 : v ≠ 0) {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    ∃ e : (ℝ × E) ≃L[ℝ] StrongDual ℝ E × ℝ, (e : ℝ × E →L[ℝ] StrongDual ℝ E × ℝ) =
      (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)).prod
        (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E)) ∧ e (0, v) = (0, ℓ v) := by
  set D : ℝ × E →L[ℝ] StrongDual ℝ E × ℝ :=
    (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)).prod
      (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E))
  have hD : ∀ w, D w = (w.1 • deriv (fun s ↦ fderiv ℝ (f s) x) t +
      fderiv ℝ (fderiv ℝ (f t)) x w.2, ℓ w.2) := fun w ↦ by
    simp [D, fderiv_fderiv_apply hf]
  have ha : deriv (fun s ↦ fderiv ℝ (f s) x) t v ≠ 0 :=
    fun h ↦ hv0 ((surjective_fderiv_fderiv_iff hf).1 hs v hv h)
  -- Pairing the first component with `v` kills the parameter component, and then the space
  -- component is a multiple of `v` on which `ℓ` vanishes.
  have hinj : Injective D := (injective_iff_map_eq_zero _).2 fun ⟨τ, ξ⟩ h ↦ by
    rw [hD, Prod.mk_eq_zero] at h
    have hτ : τ = 0 := by
      simpa [fderiv_fderiv_apply_comm_of_uncurry hf ξ v, hv, ha] using congrArg (· v) h.1
    subst hτ
    obtain ⟨c, rfl⟩ :=
      exists_eq_smul_of_fderiv_fderiv_apply_eq_zero hf hs hv0 hv (by simpa using h.1)
    simp_all
  have hdim : finrank ℝ (ℝ × E) = finrank ℝ (StrongDual ℝ E × ℝ) := by
    simp [ContinuousLinearMap.dual_finrank_eq, add_comm]
  exact ⟨(LinearMap.linearEquivOfInjective D.toLinearMap hinj hdim).toContinuousLinearEquiv, rfl,
    (hD (0, v)).trans (by simp [hv])⟩

/-- **The critical curve through a birth–death point.** At a critical point `x` of `f t` where
the family is transverse and the Hessian has a nonzero kernel vector `v`, with `ℓ v = 1`, there is
a `C²` curve `c` through `(t, x)` with velocity `(0, v)`, made of critical points of the family,
along which `ℓ` restricted to the space component increases at unit rate, and which passes
through every critical point of the family near `(t, x)`. It is the preimage of the line
`{0} × ℝ` under the local inverse of `(t, x) ↦ (d(f t)_x, ℓ x)`. -/
theorem exists_criticalCurve (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (hc : fderiv ℝ (f t) x = 0) {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0) (hv0 : v ≠ 0)
    {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    ∃ c : ℝ → ℝ × E, ∃ N ∈ 𝓝 (t, x), c 0 = (t, x) ∧ ContDiffAt ℝ 2 c 0 ∧
      HasDerivAt c (0, v) 0 ∧ (∀ᶠ s in 𝓝 0, fderiv ℝ (f (c s).1) (c s).2 = 0 ∧
        ℓ (c s).2 = ℓ x + s) ∧
      ∀ z ∈ N, fderiv ℝ (f z.1) z.2 = 0 → c (ℓ z.2 - ℓ x) = z := by
  set G : ℝ × E → StrongDual ℝ E := fun w ↦ fderiv ℝ (f w.1) w.2
  have hG : ContDiffAt ℝ 2 G (t, x) := hf.fderiv_slice (m := 2) le_rfl
  set Φ : ℝ × E → StrongDual ℝ E × ℝ := fun w ↦ (G w, ℓ w.2)
  have hΦ : ContDiffAt ℝ 2 Φ (t, x) :=
    hG.prodMk (ℓ.contDiff.contDiffAt.comp _ contDiffAt_snd)
  obtain ⟨e, he, hev⟩ := exists_continuousLinearEquiv_fderiv_prod (hf.of_le (by norm_num)) hs hv
    hv0 hℓ
  have hΦ' : HasFDerivAt Φ (e : ℝ × E →L[ℝ] StrongDual ℝ E × ℝ) (t, x) := by
    rw [he]
    exact ((hG.differentiableAt two_ne_zero).hasFDerivAt).prodMk
      (ℓ.hasFDerivAt.comp _ hasFDerivAt_snd)
  set P := hΦ.toOpenPartialHomeomorph Φ hΦ' two_ne_zero
  have hΦp : Φ (t, x) = (0, ℓ x) := by simp [Φ, G, hc]
  replace hev : (0, v) = e.symm (0, 1) := e.eq_symm_apply.2 (hev.trans (by rw [hℓ]))
  -- The curve `c s = Φ⁻¹ (0, ℓ x + s)`.
  set L : ℝ → StrongDual ℝ E × ℝ := fun s ↦ (0, ℓ x + s)
  have hL : HasDerivAt L (0, 1) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : StrongDual ℝ E)).prodMk ((hasDerivAt_id (0 : ℝ)).const_add _)
  have hL0 : L 0 = Φ (t, x) := by simp [L, hΦp]
  have hinv : ContDiffAt ℝ 2 P.symm (L 0) := hL0 ▸ hΦ.to_localInverse hΦ' two_ne_zero
  have hinv' : HasFDerivAt P.symm (e.symm : StrongDual ℝ E × ℝ →L[ℝ] ℝ × E) (L 0) :=
    hL0 ▸ ((hΦ.hasStrictFDerivAt hΦ' two_ne_zero).to_localInverse).hasFDerivAt
  have htarget : L 0 ∈ P.target := hL0 ▸ hΦ.image_mem_toOpenPartialHomeomorph_target hΦ' _
  refine ⟨P.symm ∘ L, P.source, P.open_source.mem_nhds
    (hΦ.mem_toOpenPartialHomeomorph_source hΦ' _), ?_, hinv.comp 0 (contDiff_const.prodMk
      (contDiff_const.add contDiff_id)).contDiffAt, ?_, ?_, fun z hz hz₀ ↦ ?_⟩
  · rw [comp_apply, hL0]
    exact P.left_inv (hΦ.mem_toOpenPartialHomeomorph_source hΦ' _)
  · simpa [hev] using hinv'.comp_hasDerivAt (0 : ℝ) hL
  · have hLc : ContinuousAt L 0 := hL.continuousAt
    filter_upwards [hLc.preimage_mem_nhds (P.open_target.mem_nhds htarget)] with s hs
    have h := P.right_inv hs
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · have hΦz : L (ℓ z.2 - ℓ x) = Φ z := by simp [L, Φ, G, hz₀]
    rw [comp_apply, hΦz]
    exact P.left_inv hz

/-! ### Births and deaths -/

/-- **A pair of critical points is born at a birth–death point.** Let `f t` be a family of
functions on a finite-dimensional real normed space, jointly `C³` at `(t, x)`, where `x` is a
critical point of `f t` at which the family is transverse: the derivative of the parametrized
differential `(t, x) ↦ d(f t)_x` is onto. Let `v` be a kernel vector of the Hessian of `f t` at
`x` with `D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v < 0`. Then `x` has a neighbourhood `U` in which
`x` is the only critical point of `f t`, `f s` has no critical point for `s < t` close to `t`,
and `f s` has exactly two critical points, both nondegenerate, for `s > t` close to `t`. -/
theorem exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_neg
    (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (hc : fderiv ℝ (f t) x = 0) {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hsign : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v *
      deriv (fun s ↦ fderiv ℝ (f s) x) t v < 0) :
    ∃ U ∈ 𝓝 x, {y ∈ U | fderiv ℝ (f t) y = 0} = {x} ∧
      (∀ᶠ s in 𝓝[<] t, ∀ y ∈ U, fderiv ℝ (f s) y ≠ 0) ∧
      ∀ᶠ s in 𝓝[>] t, {y ∈ U | fderiv ℝ (f s) y = 0}.ncard = 2 ∧
        ∀ y ∈ U, fderiv ℝ (f s) y = 0 → IsNondegenerateCriticalPoint (f s) y := by
  have hκ : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v ≠ 0 := fun h ↦ by simp [h] at hsign
  have hv0 : v ≠ 0 := by rintro rfl; simp at hκ
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv0
  obtain ⟨c, N, hN, hc0, hcd, hc', hcrit, hcN⟩ := exists_criticalCurve hf hs hc hv hv0 hℓ
  -- The parameter along the curve folds back at `0`.
  have hfold := eventually_fold_criticalCurve hf hv hsign hc0 hcd hc' (hcrit.mono fun _ h ↦ h.1)
  obtain ⟨ε, hε, hεc⟩ := Metric.eventually_nhds_iff.1 hcrit
  obtain ⟨δ₀, hfold₀, hδ₀⟩ := (hfold.and (Ioo_mem_nhdsGT hε)).exists
  have hcritI : ∀ σ ∈ Ioo (-δ₀) δ₀, fderiv ℝ (f (c σ).1) (c σ).2 = 0 ∧ ℓ (c σ).2 = ℓ x + σ :=
    fun σ hσ ↦ hεc (by
      rw [← mem_ball, Real.ball_zero_eq_Ioo]
      exact Ioo_subset_Ioo (neg_le_neg hδ₀.2.le) hδ₀.2.le hσ)
  -- The critical points in a small ball lie on the curve.
  obtain ⟨r, hr, hcurve⟩ := exists_pos_forall_mem_ball hN hcN
    (eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero hf hs
      fun u hu hu3 ↦ eq_zero_of_fderiv_fderiv_fderiv_apply_eq_zero (hf.of_le (by norm_num)) hs
        hv hκ hu hu3) hδ₀.1
  -- On `(-δ₁, δ₁)` the curve stays over the ball.
  have hξ : Tendsto (fun σ ↦ (c σ).2) (𝓝 0) (𝓝 x) := by
    simpa [hc0] using hcd.continuousAt.snd.tendsto
  obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.eventually_nhds_iff.1 (hξ.eventually (ball_mem_nhds x hr))
  obtain ⟨δ₁, hfold₁, hδ₁⟩ := (hfold.and (Ioo_mem_nhdsGT (lt_min hδ₀.1 hε₁))).exists
  refine ⟨ball x r, ball_mem_nhds x hr, Set.ext fun y ↦ ⟨fun ⟨hy, hy0⟩ ↦ ?_, ?_⟩, ?_, ?_⟩
  · -- At `t`, the only critical point in the ball is `x`, the point of the curve at `σ = 0`.
    obtain ⟨hσ, hcσ, -⟩ := hcurve t y (by simpa using hr) hy hy0
    have h0 : ℓ y - ℓ x ∈ ({0} : Set ℝ) := hfold₀.self_of_nhds.2.1 rfl ▸ ⟨hσ, by simp [hcσ]⟩
    rw [mem_singleton_iff] at h0
    rw [h0, hc0] at hcσ
    exact (congrArg Prod.snd hcσ).symm
  · rintro rfl
    exact ⟨mem_ball_self hr, hc⟩
  · -- Before `t`, there is none, since the parameter is at least `t` along the curve near `0`.
    filter_upwards [nhdsWithin_le_nhds hfold₀, Ioo_mem_nhdsLT (show t - r < t by linarith)]
      with s h₀ hs y hy hy0
    obtain ⟨hσ, hcσ, -⟩ := hcurve s y (by
      rw [← mem_ball, Real.ball_eq_Ioo]
      exact Ioo_subset_Ioo_right (by linarith) hs) hy hy0
    have := h₀.1 hs.2 _ hσ
    simp [hcσ] at this
  · -- After `t`, there are exactly two, both nondegenerate.
    exact eventually_ncard_setOf_fderiv_eq_zero_eq_two (hδ₁.2.le.trans (min_le_left _ _)) hr
      hcritI hcurve (fun σ hσ ↦ hε₁U (by
        have hδε : δ₁ ≤ ε₁ := hδ₁.2.le.trans (min_le_right _ _)
        rw [← mem_ball, Real.ball_zero_eq_Ioo]
        exact Ioo_subset_Ioo (neg_le_neg hδε) hδε hσ))
      (hfold₀.mono fun _ h ↦ h.2.2) (hfold₁.mono fun _ h ↦ h.2.2)

/-- **A pair of critical points dies at a birth–death point.** Let `f t` be a family of
functions on a finite-dimensional real normed space, jointly `C³` at `(t, x)`, where `x` is a
critical point of `f t` at which the family is transverse: the derivative of the parametrized
differential `(t, x) ↦ d(f t)_x` is onto. Let `v` be a kernel vector of the Hessian of `f t` at
`x` with `0 < D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v`. Then `x` has a neighbourhood `U` in which
`x` is the only critical point of `f t`, `f s` has no critical point for `s > t` close to `t`,
and `f s` has exactly two critical points, both nondegenerate, for `s < t` close to `t`. -/
theorem exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_pos
    (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (hc : fderiv ℝ (f t) x = 0) {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hsign : 0 < fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v *
      deriv (fun s ↦ fderiv ℝ (f s) x) t v) :
    ∃ U ∈ 𝓝 x, {y ∈ U | fderiv ℝ (f t) y = 0} = {x} ∧
      (∀ᶠ s in 𝓝[>] t, ∀ y ∈ U, fderiv ℝ (f s) y ≠ 0) ∧
      ∀ᶠ s in 𝓝[<] t, {y ∈ U | fderiv ℝ (f s) y = 0}.ncard = 2 ∧
        ∀ y ∈ U, fderiv ℝ (f s) y = 0 → IsNondegenerateCriticalPoint (f s) y := by
  -- Reverse the parameter: `g s = f (-s)` has a birth at `-t`.
  set g : ℝ → E → ℝ := fun s ↦ f (-s)
  have hgt : g (-t) = f t := by simp [g]
  have hg : ContDiffAt ℝ 3 (uncurry g) (-t, x) := by
    have hf' : ContDiffAt ℝ 3 (uncurry f) ((fun z : ℝ × E ↦ (-z.1, z.2)) (-t, x)) := by
      simpa using hf
    exact hf'.comp (-t, x) (contDiffAt_fst.neg.prodMk contDiffAt_snd)
  have hderiv : deriv (fun s ↦ fderiv ℝ (g s) x) (-t) = -deriv (fun s ↦ fderiv ℝ (f s) x) t := by
    simpa using deriv_comp_neg (f := fun s ↦ fderiv ℝ (f s) x) (x := -t)
  have hgs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (g w.1) w.2) (-t, x)) := by
    rw [surjective_fderiv_fderiv_iff (hg.of_le (by norm_num)), hgt, hderiv]
    have := (surjective_fderiv_fderiv_iff (hf.of_le (by norm_num))).1 hs
    simpa using this
  obtain ⟨U, hU, h₀, h₁, h₂⟩ := exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_neg hg hgs
    (by rwa [hgt]) (by rwa [hgt]) (by rw [hgt, hderiv]; simpa using hsign)
  refine ⟨U, hU, by rwa [hgt] at h₀, ?_, ?_⟩
  · filter_upwards [tendsto_neg_nhdsGT.eventually h₁] with s hs
    simpa [g] using hs
  · filter_upwards [tendsto_neg_nhdsLT.eventually h₂] with s hs
    simpa [g] using hs

end FiniteDimensional

end TauCeti
