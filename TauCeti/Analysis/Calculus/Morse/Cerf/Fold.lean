/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Cerf.Isolated
-- Private: used only inside proofs.
import TauCeti.Analysis.Calculus.Bifurcation
import TauCeti.Analysis.Calculus.Bifurcation.Fold
import TauCeti.Analysis.Calculus.Morse.Cerf.Index
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.MetricSpace.Pseudo.Prod

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
  (`TauCeti.exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_pos`);
* the two critical points have **adjacent Morse indices**: if `k` is the Morse index of `f t₀` at
  `x₀`, one of them has index `k + 1` and the other index `k`
  (`TauCeti.exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_neg` and
  `TauCeti.exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_pos`).

For the model `x³ / 3 - t x` at `(0, 0)` the third derivative is `2` and the parameter derivative
of the differential is `-1`, so the product is `-2`: the two critical points `±√t` exist for
`t > 0`, a local maximum `-√t` of index `1` and a local minimum `√t` of index `0`. Adjacent indices
are what the cancellation of the two born or dying critical points against each other in the Morse
complex requires.

The proof follows the critical locus, which is the zero locus of the family of differentials
`d(f s) : E → E*`. A birth–death point is a fold point of that family in the sense of
`TauCeti.Analysis.Calculus.Bifurcation.Fold`, with the functional `φ` on `E*` given by evaluation
at `v`, which vanishes on the range of the Hessian by its symmetry. Choose a functional `ℓ` with
`ℓ v = 1`. By `TauCeti.exists_curve_apply_eq_zero`, the critical points of the family near
`(t₀, x₀)` form a `C²` curve `c(s)` with `c(0) = (t₀, x₀)` and `c'(0) = (0, v)`, and the critical
points of `f t` near `x₀` are the points `c(s)` with `τ(s) = t`, where `τ(s)` is the parameter
component of `c(s)`. Since the fold coefficient is `D³(f t₀)_{x₀} (v, v, v) · ∂ₜ (d(f t)_{x₀}) v`,
`TauCeti.eventually_fold_curve_fst` shows that, when the product above is negative, `τ` takes
each value slightly above `t₀` exactly twice near `0`, once on each side, and no value below `t₀`.
That the two critical points are nondegenerate is
`TauCeti.eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero`.

Their Morse indices come from the Hessians along the curve. The path
`s ↦ Hess(f τ(s))_{ξ(s)}` of symmetric forms has derivative `D³(f t₀)_{x₀} (v, ·, ·)` at `0`,
since `τ'(0) = 0` and `ξ'(0) = v`, so `0` is a crossing whose kernel is the line through `v` and
whose crossing form is `D³(f t₀)_{x₀} (v, v, v) ≠ 0` there. Its negative index is therefore `k + 1`
on one side of `0` and `k` on the other (`TauCeti.eventually_nhdsGT_morseIndex_eq` and
`TauCeti.eventually_nhdsLT_morseIndex_eq` in `TauCeti.Analysis.Calculus.Morse.Cerf.Index`), and the
two critical points of `f t` lie on the curve on opposite sides of `0`.

## Main results

* `TauCeti.exists_curve_fderiv_eq_zero`: the critical points of the family near a transverse
  degenerate critical point form a `C²` curve through it, with velocity `(0, v)` for a kernel
  vector `v` of the Hessian.
* `TauCeti.exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_neg`: a birth at a birth–death
  point where the product is negative, of two critical points of Morse indices `k + 1` and `k`.
* `TauCeti.exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_pos`: a death at a birth–death
  point where the product is positive, of two critical points of Morse indices `k + 1` and `k`.
* `TauCeti.exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_neg` and
  `TauCeti.exists_mem_nhds_ncard_setOf_fderiv_eq_zero_eq_two_of_mul_pos`: the same births and
  deaths, counted.

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

/-! ### The family of differentials -/

/-- **Evaluation at a kernel vector of the Hessian vanishes on its range**, by the symmetry of the
Hessian: `Hess(f t)_x (y, v) = Hess(f t)_x (v, y) = 0`. -/
private theorem apply_fderiv_fderiv_apply_eq_zero (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0) (y : E) :
    ContinuousLinearMap.apply ℝ ℝ v (fderiv ℝ (fderiv ℝ (f t)) x y) = 0 := by
  rw [ContinuousLinearMap.apply_apply, fderiv_fderiv_apply_comm_of_uncurry hf, hv,
    zero_apply]

/-- **The critical curve folds back over the parameter.** Let `c` be a `C²` curve of critical
points of the family through `(t, x)`, with velocity `(0, v)` for a kernel vector `v` of the
Hessian of `f t` at `x`, and let `D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v < 0`. Then for every small
`δ > 0` and every `s` near `t`, the parameter component of `c` on `(-δ, δ)` avoids `s` when
`s < t`, takes the value `t` only at `0`, and takes the value `s` exactly twice, once on each side
of `0`, when `s > t`. This is `TauCeti.eventually_fold_curve_fst` for the family of differentials
`s ↦ d(f s)`, with `φ` the evaluation at `v`. -/
private theorem eventually_fold_curve_fst_of_mul_neg (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hsign : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v *
      deriv (fun s ↦ fderiv ℝ (f s) x) t v < 0)
    {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x)) (hcd : ContDiffAt ℝ 2 c 0)
    (hc' : HasDerivAt c (0, v) 0) (hcrit : ∀ᶠ s in 𝓝 0, fderiv ℝ (f (c s).1) (c s).2 = 0) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ s in 𝓝 t, (s < t → ∀ σ ∈ Ioo (-δ) δ, (c σ).1 ≠ s) ∧
      (s = t → {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = {0}) ∧
      (t < s → ∃ x₁ ∈ Ioo (-δ) 0, ∃ x₂ ∈ Ioo 0 δ, {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = {x₁, x₂}) := by
  have hfold := eventually_fold_curve_fst (f := fun s ↦ fderiv ℝ (f s))
    (φ := ContinuousLinearMap.apply ℝ ℝ v) (hf.fderiv_slice (m := 2) le_rfl)
    (apply_fderiv_fderiv_apply_eq_zero (hf.of_le (by norm_num)) hv) hsign.ne hc0 hcd hc' hcrit
  simp only [ContinuousLinearMap.apply_apply] at hfold
  filter_upwards [hfold] with δ hδ
  filter_upwards [hδ] with s ⟨hlt, heq, hgt⟩
  refine ⟨fun h ↦ hlt (mul_pos_of_neg_of_neg hsign (sub_neg.2 h)), heq, fun h ↦ ?_⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, hset, -⟩ := hgt (mul_neg_of_neg_of_pos hsign (sub_pos.2 h))
  exact ⟨x₁, hx₁, x₂, hx₂, hset⟩

/-! ### Critical points near a curve of critical points -/

/-- **Critical points near `(t, x)` lie on the critical curve.** If every critical point `z` of
the family in a neighbourhood `N` of `(t, x)` is the point `c (ℓ z.2 - ℓ x)` of a curve `c`, and
the critical points near `(t, x)` other than `(t, x)` are nondegenerate, then for some `r > 0`
every critical point `y` of `f s` with `|s - t| < r` and `y ∈ ball x r` is `c σ` for
`σ = ℓ y - ℓ x ∈ (-δ, δ)`, and is nondegenerate unless `(s, y) = (t, x)`. -/
private theorem exists_pos_forall_mem_ball_fderiv_eq_zero {c : ℝ → ℝ × E} {ℓ : StrongDual ℝ E}
    {N : Set (ℝ × E)} (hN : N ∈ 𝓝 (t, x))
    (hcN : ∀ z ∈ N, fderiv ℝ (f z.1) z.2 = 0 → c (ℓ z.2 - ℓ x) = z)
    (hnd : ∀ᶠ z in 𝓝[≠] (t, x), fderiv ℝ (f z.1) z.2 = 0 →
      IsNondegenerateCriticalPoint (f z.1) z.2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ s y, dist s t < r → y ∈ ball x r → fderiv ℝ (f s) y = 0 →
      ℓ y - ℓ x ∈ Ioo (-δ) δ ∧ c (ℓ y - ℓ x) = (s, y) ∧
        ((s, y) ≠ (t, x) → IsNondegenerateCriticalPoint (f s) y) := by
  obtain ⟨r, hr, hrN⟩ := exists_pos_forall_mem_of_mem_nhds
    (Filter.eventually_iff.1 ((eventually_mem_set.2 hN).and (eventually_nhdsWithin_iff.1 hnd)))
    ℓ.continuous.continuousAt hδ
  refine ⟨r, hr, fun s y hs hy hy0 ↦ ?_⟩
  obtain ⟨⟨hsN, hsnd⟩, hℓ⟩ := hrN s y hs hy
  exact ⟨hℓ, hcN _ hsN hy0, fun hne ↦ hsnd hne hy0⟩

/-- **Two critical points after the fold.** Let `c` be a curve of critical points on `(-δ₀, δ₀)`.
Suppose that for `s > t` close to `t` the parameter component of `c` takes the value `s` exactly
twice on `(-δ₀, δ₀)` and exactly twice on `(-δ₁, δ₁)`, once on each side of `0`, where
`δ₁ ≤ δ₀` and the curve stays over `ball x r` on `(-δ₁, δ₁)`. If the critical points in
`ball x r` of `f s`, for `|s - t| < r`, are points `c σ` with `σ ∈ (-δ₀, δ₀)`, nondegenerate away
from `(t, x)`, then for `s > t` close to `t` the critical points of `f s` in `ball x r` are the
space components of `c σ₁` and `c σ₂` for some `σ₁ ∈ (-δ₁, 0)` and `σ₂ ∈ (0, δ₁)` with parameter
components `s`, and they are nondegenerate. -/
private theorem eventually_setOf_fderiv_eq_zero_eq_pair {c : ℝ → ℝ × E}
    {ℓ : StrongDual ℝ E} {δ₀ δ₁ r : ℝ} (hδ : δ₁ ≤ δ₀) (hr : 0 < r)
    (hcrit : ∀ σ ∈ Ioo (-δ₀) δ₀, fderiv ℝ (f (c σ).1) (c σ).2 = 0)
    (hcurve : ∀ s y, dist s t < r → y ∈ ball x r → fderiv ℝ (f s) y = 0 →
      ℓ y - ℓ x ∈ Ioo (-δ₀) δ₀ ∧ c (ℓ y - ℓ x) = (s, y) ∧
        ((s, y) ≠ (t, x) → IsNondegenerateCriticalPoint (f s) y))
    (hU : ∀ σ ∈ Ioo (-δ₁) δ₁, (c σ).2 ∈ ball x r)
    (h₀ : ∀ᶠ s in 𝓝 t, t < s → ∃ x₁ ∈ Ioo (-δ₀) 0, ∃ x₂ ∈ Ioo 0 δ₀,
      {σ ∈ Ioo (-δ₀) δ₀ | (c σ).1 = s} = {x₁, x₂})
    (h₁ : ∀ᶠ s in 𝓝 t, t < s → ∃ x₁ ∈ Ioo (-δ₁) 0, ∃ x₂ ∈ Ioo 0 δ₁,
      {σ ∈ Ioo (-δ₁) δ₁ | (c σ).1 = s} = {x₁, x₂}) :
    ∀ᶠ s in 𝓝[>] t, ∃ σ₁ ∈ Ioo (-δ₁) 0, ∃ σ₂ ∈ Ioo 0 δ₁, (c σ₁).1 = s ∧ (c σ₂).1 = s ∧
      {y ∈ ball x r | fderiv ℝ (f s) y = 0} = {(c σ₁).2, (c σ₂).2} ∧
      ∀ y ∈ ball x r, fderiv ℝ (f s) y = 0 → IsNondegenerateCriticalPoint (f s) y := by
  filter_upwards [nhdsWithin_le_nhds (h₀.and h₁), Ioo_mem_nhdsGT (show t < t + r by linarith)]
    with s ⟨h₀, h₁⟩ hs
  have hst : dist s t < r := by
    rw [← mem_ball, Real.ball_eq_Ioo]
    exact Ioo_subset_Ioo_left (by linarith) hs
  obtain ⟨x₁, hx₁, x₂, hx₂, hset₀⟩ := h₀ hs.1
  obtain ⟨y₁, hy₁, y₂, hy₂, hset₁⟩ := h₁ hs.1
  have hval : ∀ σ ∈ ({y₁, y₂} : Set ℝ), (c σ).1 = s := fun σ hσ ↦ by
    rw [← hset₁] at hσ
    exact hσ.2
  refine ⟨y₁, hy₁, y₂, hy₂, hval y₁ (by simp), hval y₂ (by simp),
    setOf_eq_pair_of_forall_eq_curve (Z := fun s y ↦ fderiv ℝ (f s) y = 0) hδ hcrit
      (fun y hy hy0 ↦ (hcurve s y hst hy hy0).imp_right And.left) hU hx₁.2 hx₂.1 hset₀ hy₁ hy₂
      hset₁,
    fun y hy hy0 ↦ (hcurve s y hst hy hy0).2.2 fun h ↦ ?_⟩
  linarith [congrArg Prod.fst h, hs.1]

/-! ### The critical curve through a birth–death point -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **The critical curve through a birth–death point.** At a critical point `x` of `f t` where
the family is transverse and the Hessian has a nonzero kernel vector `v`, with `ℓ v = 1`, there is
a `C²` curve `c` through `(t, x)` with velocity `(0, v)`, made of critical points of the family,
along which `ℓ` restricted to the space component increases at unit rate, and which passes
through every critical point of the family near `(t, x)`. This is
`TauCeti.exists_curve_apply_eq_zero` for the family of differentials `s ↦ d(f s)`, with `φ` the
evaluation at `v`: the critical points of the family are the zeros of that family. -/
theorem exists_curve_fderiv_eq_zero (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (hc : fderiv ℝ (f t) x = 0) {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    ∃ c : ℝ → ℝ × E, ∃ N ∈ 𝓝 (t, x), c 0 = (t, x) ∧ ContDiffAt ℝ 2 c 0 ∧
      HasDerivAt c (0, v) 0 ∧ (∀ᶠ s in 𝓝 0, fderiv ℝ (f (c s).1) (c s).2 = 0 ∧
        ℓ (c s).2 = ℓ x + s) ∧
      ∀ z ∈ N, fderiv ℝ (f z.1) z.2 = 0 → c (ℓ z.2 - ℓ x) = z := by
  have hf2 : ContDiffAt ℝ 2 (uncurry f) (t, x) := hf.of_le (by norm_num)
  have hv0 : v ≠ 0 := by rintro rfl; simp at hℓ
  -- Transversality: `∂ₜ (d(f t)_x) v ≠ 0`.
  have ha : ContinuousLinearMap.apply ℝ ℝ v (deriv (fun s ↦ fderiv ℝ (f s) x) t) ≠ 0 :=
    fun h ↦ hv0 ((surjective_fderiv_fderiv_iff hf2).1 hs v hv h)
  exact exists_curve_apply_eq_zero (f := fun s ↦ fderiv ℝ (f s))
    (by simp [ContinuousLinearMap.dual_finrank_eq]) (hf.fderiv_slice (m := 2) le_rfl) hc
    (ker_fderiv_fderiv_eq_span_singleton hf2 hs hv0 hv)
    (apply_fderiv_fderiv_apply_eq_zero hf2 hv) ha hℓ


/-! ### The Morse index along the critical curve -/

/-- **The Morse index along the critical curve.** Let `c` be a curve through `(t, x)` with
velocity `(0, v)` at `0`, where `x` is a critical point of `f t` at which the family is jointly
`C³` and transverse, and `v` is a kernel vector of the Hessian of `f t` at `x` with
`κ = D³(f t)_x (v, v, v) ≠ 0`. The Hessians at the points of `c` form a path of symmetric forms
with derivative `D³(f t)_x (v, ·, ·)` at `0`, so `0` is a crossing whose kernel is the line through
`v` and whose crossing form is `κ` there. With `k` the Morse index of `f t` at `x`, the points of
`c` just after `0` therefore have Morse index `k + 1` if `κ < 0` and `k` if `κ > 0`, and the points
just before `0` the other one: this holds on `(0, ε)` and on `(-ε, 0)` for some `ε > 0`. -/
private theorem exists_pos_morseIndex_curve (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x))) {v : E}
    (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hκ : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v ≠ 0) {c : ℝ → ℝ × E}
    (hc0 : c 0 = (t, x)) (hc' : HasDerivAt c (0, v) 0) :
    ∃ ε > 0, (∀ σ ∈ Ioo 0 ε, morseIndex (f (c σ).1) (c σ).2 = morseIndex (f t) x +
      if fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v < 0 then 1 else 0) ∧
    ∀ σ ∈ Ioo (-ε) 0, morseIndex (f (c σ).1) (c σ).2 = morseIndex (f t) x +
      if fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v < 0 then 0 else 1 := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hκ
  have hker := ker_fderiv_fderiv_eq_span_singleton (hf.of_le (by norm_num)) hs hv0 hv
  obtain ⟨ε₁, hε₁, hR⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_nhdsGT_morseIndex_eq hf hker hκ hc0 hc')
  obtain ⟨ε₂, hε₂, hL⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1
    (eventually_nhdsLT_morseIndex_eq hf hker hκ hc0 hc')
  refine ⟨min ε₁ (-ε₂), lt_min hε₁ (neg_pos.2 hε₂),
    fun σ hσ ↦ hR ⟨hσ.1, hσ.2.trans_le (min_le_left _ _)⟩, fun σ hσ ↦ ?_⟩
  have hσL : morseIndex (f (c σ).1) (c σ).2 = morseIndex (f t) x +
      if 0 < fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v then 1 else 0 :=
    hL ⟨by linarith [hσ.1, min_le_right ε₁ (-ε₂)], hσ.2⟩
  rw [hσL]
  rcases hκ.lt_or_gt with h | h <;> simp [h, h.not_gt]

/-! ### Births and deaths -/

omit [FiniteDimensional ℝ E] in
/-- Two nondegenerate critical points which are all the critical points of `g` in `U`, one of
Morse index `k` and the other of index `k + 1` in one order or the other according to a
proposition `p`, are a critical point of index `k + 1` and one of index `k`. -/
private theorem exists_eq_pair_morseIndex {g : E → ℝ} {U : Set E} {y₁ y₂ : E} {k : ℕ}
    {p : Prop} [Decidable p] (hset : {y ∈ U | fderiv ℝ g y = 0} = {y₁, y₂})
    (hnd : ∀ y ∈ U, fderiv ℝ g y = 0 → IsNondegenerateCriticalPoint g y)
    (hi₁ : morseIndex g y₁ = k + if p then 0 else 1)
    (hi₂ : morseIndex g y₂ = k + if p then 1 else 0) :
    ∃ z₁ z₂, {y ∈ U | fderiv ℝ g y = 0} = {z₁, z₂} ∧ IsNondegenerateCriticalPoint g z₁ ∧
      IsNondegenerateCriticalPoint g z₂ ∧ morseIndex g z₁ = k + 1 ∧ morseIndex g z₂ = k := by
  have h₁ := hset.symm.subset (by simp : y₁ ∈ ({y₁, y₂} : Set E))
  have h₂ := hset.symm.subset (by simp : y₂ ∈ ({y₁, y₂} : Set E))
  by_cases hp : p
  · simp only [hp, ite_true, add_zero] at hi₁ hi₂
    exact ⟨y₂, y₁, hset.trans (Set.pair_comm _ _), hnd _ h₂.1 h₂.2, hnd _ h₁.1 h₁.2, hi₂, hi₁⟩
  · simp only [hp, ite_false, add_zero] at hi₁ hi₂
    exact ⟨y₁, y₂, hset, hnd _ h₁.1 h₁.2, hnd _ h₂.1 h₂.2, hi₁, hi₂⟩

/-- **A pair of critical points of adjacent indices is born at a birth–death point.** Let `f t` be
a family of functions on a finite-dimensional real normed space, jointly `C³` at `(t, x)`, where
`x` is a critical point of `f t` at which the family is transverse: the derivative of the
parametrized differential `(t, x) ↦ d(f t)_x` is onto. Let `v` be a kernel vector of the Hessian of
`f t` at `x` with `D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v < 0`, and let `k` be the Morse index of
`f t` at `x`. Then `x` has a neighbourhood `U` in which `x` is the only critical point of `f t`,
`f s` has no critical point for `s < t` close to `t`, and for `s > t` close to `t` the critical
points of `f s` in `U` are two nondegenerate critical points, of Morse indices `k + 1` and `k`. -/
theorem exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_neg
    (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (hc : fderiv ℝ (f t) x = 0) {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hsign : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v *
      deriv (fun s ↦ fderiv ℝ (f s) x) t v < 0) :
    ∃ U ∈ 𝓝 x, {y ∈ U | fderiv ℝ (f t) y = 0} = {x} ∧
      (∀ᶠ s in 𝓝[<] t, ∀ y ∈ U, fderiv ℝ (f s) y ≠ 0) ∧
      ∀ᶠ s in 𝓝[>] t, ∃ y₁ y₂, {y ∈ U | fderiv ℝ (f s) y = 0} = {y₁, y₂} ∧
        IsNondegenerateCriticalPoint (f s) y₁ ∧ IsNondegenerateCriticalPoint (f s) y₂ ∧
        morseIndex (f s) y₁ = morseIndex (f t) x + 1 ∧
          morseIndex (f s) y₂ = morseIndex (f t) x := by
  have hκ : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v ≠ 0 := fun h ↦ by simp [h] at hsign
  have hv0 : v ≠ 0 := by rintro rfl; simp at hκ
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv0
  obtain ⟨c, N, hN, hc0, hcd, hc', hcrit, hcN⟩ := exists_curve_fderiv_eq_zero hf hs hc hv hℓ
  -- The parameter along the curve folds back at `0`.
  have hfold := eventually_fold_curve_fst_of_mul_neg hf hv hsign hc0 hcd hc'
    (hcrit.mono fun _ h ↦ h.1)
  obtain ⟨ε, hε, hεc⟩ := Metric.eventually_nhds_iff.1 hcrit
  obtain ⟨δ₀, hfold₀, hδ₀⟩ := (hfold.and (Ioo_mem_nhdsGT hε)).exists
  have hcritI : ∀ σ ∈ Ioo (-δ₀) δ₀, fderiv ℝ (f (c σ).1) (c σ).2 = 0 := fun σ hσ ↦
    (hεc ((Real.dist_0_eq_abs σ).trans_lt ((abs_lt.2 hσ).trans hδ₀.2))).1
  -- The critical points in a small ball lie on the curve.
  obtain ⟨r, hr, hcurve⟩ := exists_pos_forall_mem_ball_fderiv_eq_zero hN hcN
    (eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero hf hs
      fun u hu hu3 ↦ eq_zero_of_fderiv_fderiv_fderiv_apply_eq_zero (hf.of_le (by norm_num)) hs
        hv hκ hu hu3) hδ₀.1
  -- On `(-δ₁, δ₁)` the curve stays over the ball, and its Morse index is constant on each side.
  have hξ : Tendsto (fun σ ↦ (c σ).2) (𝓝 0) (𝓝 x) := by
    simpa [hc0] using hcd.continuousAt.snd.tendsto
  obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.eventually_nhds_iff.1 (hξ.eventually (ball_mem_nhds x hr))
  obtain ⟨ε₂, hε₂, hR, hL⟩ := exists_pos_morseIndex_curve hf hs hv hκ hc0 hc'
  obtain ⟨δ₁, hfold₁, hδ₁⟩ :=
    (hfold.and (Ioo_mem_nhdsGT (lt_min (lt_min hδ₀.1 hε₁) hε₂))).exists
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
  · -- After `t`, there are exactly two, both nondegenerate, one on each side of `0` on the curve.
    filter_upwards [eventually_setOf_fderiv_eq_zero_eq_pair
      (hδ₁.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))) hr hcritI hcurve
      (fun σ hσ ↦ hε₁U ((Real.dist_0_eq_abs σ).trans_lt
        ((abs_lt.2 hσ).trans (hδ₁.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))))))
      (hfold₀.mono fun _ h ↦ h.2.2) (hfold₁.mono fun _ h ↦ h.2.2)]
      with s ⟨σ₁, hσ₁, σ₂, hσ₂, hs₁, hs₂, hset, hnd⟩
    have hδε₂ : δ₁ ≤ ε₂ := hδ₁.2.le.trans (min_le_right _ _)
    have hi₁ := hL σ₁ ⟨by linarith [hσ₁.1], hσ₁.2⟩
    have hi₂ := hR σ₂ ⟨hσ₂.1, by linarith [hσ₂.2]⟩
    rw [hs₁] at hi₁
    rw [hs₂] at hi₂
    exact exists_eq_pair_morseIndex hset hnd hi₁ hi₂

/-- **A pair of critical points of adjacent indices dies at a birth–death point.** Let `f t` be a
family of functions on a finite-dimensional real normed space, jointly `C³` at `(t, x)`, where `x`
is a critical point of `f t` at which the family is transverse: the derivative of the parametrized
differential `(t, x) ↦ d(f t)_x` is onto. Let `v` be a kernel vector of the Hessian of `f t` at `x`
with `0 < D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v`, and let `k` be the Morse index of `f t` at `x`.
Then `x` has a neighbourhood `U` in which `x` is the only critical point of `f t`, `f s` has no
critical point for `s > t` close to `t`, and for `s < t` close to `t` the critical points of `f s`
in `U` are two nondegenerate critical points, of Morse indices `k + 1` and `k`. -/
theorem exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_pos
    (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (hc : fderiv ℝ (f t) x = 0) {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hsign : 0 < fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v *
      deriv (fun s ↦ fderiv ℝ (f s) x) t v) :
    ∃ U ∈ 𝓝 x, {y ∈ U | fderiv ℝ (f t) y = 0} = {x} ∧
      (∀ᶠ s in 𝓝[>] t, ∀ y ∈ U, fderiv ℝ (f s) y ≠ 0) ∧
      ∀ᶠ s in 𝓝[<] t, ∃ y₁ y₂, {y ∈ U | fderiv ℝ (f s) y = 0} = {y₁, y₂} ∧
        IsNondegenerateCriticalPoint (f s) y₁ ∧ IsNondegenerateCriticalPoint (f s) y₂ ∧
        morseIndex (f s) y₁ = morseIndex (f t) x + 1 ∧
          morseIndex (f s) y₂ = morseIndex (f t) x := by
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
  obtain ⟨U, hU, h₀, h₁, h₂⟩ := exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_neg hg hgs
    (by rwa [hgt]) (by rwa [hgt]) (by rw [hgt, hderiv]; simpa using hsign)
  refine ⟨U, hU, by rwa [hgt] at h₀, ?_, ?_⟩
  · filter_upwards [tendsto_neg_nhdsGT.eventually h₁] with s hs
    simpa [g] using hs
  · filter_upwards [tendsto_neg_nhdsLT.eventually h₂] with s hs
    simpa [g, hgt] using hs

omit [FiniteDimensional ℝ E] in
/-- Two nondegenerate critical points of different Morse indices which are all the critical points
of `g` in `U` are exactly two critical points, all nondegenerate. -/
private theorem ncard_setOf_fderiv_eq_zero_eq_two {g : E → ℝ} {U : Set E} {y₁ y₂ : E} {k : ℕ}
    (hset : {y ∈ U | fderiv ℝ g y = 0} = {y₁, y₂}) (hnd₁ : IsNondegenerateCriticalPoint g y₁)
    (hnd₂ : IsNondegenerateCriticalPoint g y₂) (hi₁ : morseIndex g y₁ = k + 1)
    (hi₂ : morseIndex g y₂ = k) :
    {y ∈ U | fderiv ℝ g y = 0}.ncard = 2 ∧
      ∀ y ∈ U, fderiv ℝ g y = 0 → IsNondegenerateCriticalPoint g y := by
  refine ⟨hset ▸ Set.ncard_pair fun h ↦ by rw [h] at hi₁; omega, fun y hy hy0 ↦ ?_⟩
  rcases (hset ▸ ⟨hy, hy0⟩ : y ∈ ({y₁, y₂} : Set E)) with rfl | rfl
  exacts [hnd₁, hnd₂]

/-- **A pair of critical points is born at a birth–death point.** Let `f t` be a family of
functions on a finite-dimensional real normed space, jointly `C³` at `(t, x)`, where `x` is a
critical point of `f t` at which the family is transverse: the derivative of the parametrized
differential `(t, x) ↦ d(f t)_x` is onto. Let `v` be a kernel vector of the Hessian of `f t` at
`x` with `D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v < 0`. Then `x` has a neighbourhood `U` in which
`x` is the only critical point of `f t`, `f s` has no critical point for `s < t` close to `t`,
and `f s` has exactly two critical points, both nondegenerate, for `s > t` close to `t`. Their
Morse indices are computed in `exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_neg`. -/
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
  obtain ⟨U, hU, h₀, h₁, h₂⟩ :=
    exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_neg hf hs hc hv hsign
  exact ⟨U, hU, h₀, h₁, h₂.mono fun _ ⟨_, _, hset, hnd₁, hnd₂, hi₁, hi₂⟩ ↦
    ncard_setOf_fderiv_eq_zero_eq_two hset hnd₁ hnd₂ hi₁ hi₂⟩

/-- **A pair of critical points dies at a birth–death point.** Let `f t` be a family of
functions on a finite-dimensional real normed space, jointly `C³` at `(t, x)`, where `x` is a
critical point of `f t` at which the family is transverse: the derivative of the parametrized
differential `(t, x) ↦ d(f t)_x` is onto. Let `v` be a kernel vector of the Hessian of `f t` at `x`
with `0 < D³(f t)_x (v, v, v) · ∂ₜ (d(f t)_x) v`. Then `x` has a neighbourhood `U` in which `x` is
the only critical point of `f t`, `f s` has no critical point for `s > t` close to `t`, and `f s`
has exactly two critical points, both nondegenerate, for `s < t` close to `t`. Their Morse indices
are computed in `exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_pos`. -/
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
  obtain ⟨U, hU, h₀, h₁, h₂⟩ :=
    exists_mem_nhds_setOf_fderiv_eq_zero_eq_pair_of_mul_pos hf hs hc hv hsign
  exact ⟨U, hU, h₀, h₁, h₂.mono fun _ ⟨_, _, hset, hnd₁, hnd₂, hi₁, hi₂⟩ ↦
    ncard_setOf_fderiv_eq_zero_eq_two hset hnd₁ hnd₂ hi₁ hi₂⟩

end FiniteDimensional

end TauCeti
