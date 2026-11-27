/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Normed.Module.Basic

/-!
# Mean value estimates

## Exact increments along continuous real paths

`ContinuousOn.exists_deriv_comp_mul_sub_eq` realizes the mean value derivative at a time
on a continuous real path. This supplies the exact per-cell increments used in the
finite-variation chain rule, without requiring the path itself to be differentiable.

## A directional mean value inequality

The mean value inequality only needs control of the derivative in the direction of the
chord being estimated, not an operator norm bound. This is useful on lower-dimensional
simplices, where derivatives are determined only on tangent directions, and when estimating
a parametrized map in terms of the size of its geometric chord.

The argument follows Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`,
using its one-variable mean value inequality along the same line segment.

## Escaping a superlevel set at bounded speed

Let `w` be a differentiable real function on a real normed space whose derivative has norm at
most `L` on the band `{a ≤ w ≤ b}`. Starting from a point where `w ≥ b`, the function cannot reach
the level `a` within distance `(b - a) / L` (`TauCeti.lt_apply_add_of_norm_fderiv_le`).
Consequently the outer shell of the `r`-thickening of `{w ≥ 0}` lies in `{-(L r) < w < 0}` when
`‖Dw‖ ≤ L` on `{-(L r) ≤ w ≤ 0}`
(`Differentiable.thickening_sdiff_subset_preimage_Ioo_of_norm_fderiv_le`).

Mathlib's `Convex.norm_image_sub_le_of_norm_fderiv_le` needs the derivative bound along the
whole segment; here it is only assumed on the band, which is what is available near a level set
of a function whose gradient is controlled only there. The proof applies the one-variable mean
value theorem on the part of the segment where the function crosses the band.

The file also records the one-variable form of Mathlib's
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`, bounding the increment of a function
against a fixed derivative `φ` (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le'`).

For a map whose derivative is `α`-Hölder with constant `H` on the closed ball of radius `R` about
`x`, the linearization error at `x` of an increment between two points of that ball is at most
`H R^α` times the increment (`TauCeti.norm_sub_sub_le_of_holderOnWith`).

## Integrating a little-o derivative bound

If `f` is differentiable near `a` and `Df(x) = o(‖x - a‖ ^ r)` as `x → a`, where `r ≥ 0`, then
`f(x) - f(a) = o(‖x - a‖ ^ (r + 1))`, by the mean value inequality on balls about `a`
(`TauCeti.sub_isLittleO_norm_rpow_add_one_of_fderiv`). This is the little-o counterpart of
Mathlib's `sub_isBigO_norm_rpow_add_one_of_fderiv`.

## Along a polygonal path

On a set that is not convex, the mean value inequality still bounds the increment of a function
along any polygonal path inside the set by the derivative bound times the length of the path
(`TauCeti.norm_image_sub_le_of_norm_fderiv_le_of_segment_subset`, for three segments).

## Constancy on a relatively open part of a convex set

A function whose derivative within `Ω ∩ s` vanishes, for `Ω` open and `s` convex, is constant on
`Ω ∩ s` when that set is preconnected (`Convex.is_const_of_fderivWithin_inter_eq_zero`), since
near each of its points `Ω ∩ s` is the convex set `ball ∩ s`. For `s` a closed half-space this is
constancy up to the boundary of a half-disc.

## Space-time functions vanishing outside a time interval

A function of time and space with derivative bounded by `C` that vanishes outside the time
interval `(a, b)` is bounded by `C (b - a)`, by the mean value inequality from its value at the
time `a` (`TauCeti.norm_le_mul_sub_of_forall_notMem_Ioo_eq_zero`).

## A uniform first-order remainder estimate

If `G` is differentiable on `s` with a derivative `G'` uniformly continuous there, one radius
`η` serves at every centre: on each ball of radius at most `η` inside `s`, the first-order
remainder of `G` against its derivative at the centre is at most `c` times the increment
(`UniformContinuousOn.exists_pos_norm_image_sub_sub_le_of_hasFDerivAt`). This is the pointwise
estimate behind the differentiability of superposition operators.

## Comparing maps with nearby derivatives

If two maps on a convex set have derivatives within `ε` of a common linear map and agree at a
point `y`, then by the mean value inequality applied to their difference they stay within
`2 ε ‖x - y‖` of each other (`Convex.norm_sub_le_of_norm_hasFDerivWithin_sub_le`).
This compares a map to a model agreeing with it to first order before splicing them together
(`TauCeti.Analysis.Calculus.Splice`).

For a family of operators `Φ : E → Λ →L[𝕜] F` whose pointwise derivatives stay within `C` of a
fixed `L` in operator norm, the mean value inequality applied to each `w ↦ Φ w f` bounds the
operator norm of `Φ z - Φ y - L.flip (z - y)` by `C ‖z - y‖`
(`Convex.norm_sub_sub_flip_le_of_norm_hasFDerivWithin_sub_le`).

For an antilipschitz parametrization with bounded derivative, an image chord controls the
parametric chord and its intervening points. A scalar mean value estimate permits bounds on
individual coordinate derivatives. These estimates are adapted from
[KLS](https://github.com/human-ai-mathematics/kls-lean), commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/Disk.lean`.

## Invariance along a direction

Over `ℝ` or `ℂ`, a map whose derivative kills a vector `v` at every point `z + t • v` of the
segment from `z` to `z + v` (`t` real, `0 ≤ t ≤ 1`) takes the same value at `z` and `z + v`
(`TauCeti.apply_add_eq_of_fderiv_apply_eq_zero`). Unlike Mathlib's
`Convex.is_const_of_fderivWithin_eq_zero`, only the derivative in the direction `v` is assumed to
vanish, so the map need not be constant near the segment. Consequently, if `π` is a continuous
projection and the derivative of a map kills `ker π` on a ball about `0`, then near `0` the map
only depends on the `π` component (`TauCeti.apply_proj_eq_of_fderiv_apply_eq_zero`), and a
compactly supported differentiable map whose derivative kills a nonzero `v` everywhere is zero
(`HasCompactSupport.eq_zero_of_fderiv_apply_eq_zero`).

## Constancy from a vanishing derivative

A function on a preconnected subset of `ℝ` whose derivative within the set vanishes is constant
there (`IsPreconnected.eq_of_hasDerivWithinAt_zero`). A function `𝕜 → G`, `𝕜 = ℝ` or `𝕜 = ℂ`,
with zero derivative at every point is constant (`TauCeti.is_const_of_hasDerivAt_zero`).

## Signs from monotonicity on the real line

A real function continuous on `[x, ∞)`, with nonpositive (negative) derivative on `(x, ∞)` and
limit `L` at `+∞`, satisfies `L ≤ f x` (`L < f x`)
(`TauCeti.le_of_tendsto_atTop_of_hasDerivAt_nonpos`,
`TauCeti.lt_of_tendsto_atTop_of_hasDerivAt_neg`). A real function continuous on `[a, x]` with
positive (negative) derivative on `(a, x)` satisfies `f a < f x` (`f x < f a`)
(`TauCeti.lt_of_hasDerivAt_pos`, `TauCeti.lt_of_hasDerivAt_neg`). If a real function continuous on
`[a, ∞)` with limit `L` at `+∞` satisfies `L ≤ f a`, and its derivative, once nonpositive at a
point of `(a, ∞)`, stays nonpositive (negative) afterwards, then `L ≤ f x` on `[a, ∞)` (`L < f x`
on `(a, ∞)`) (`TauCeti.le_of_tendsto_atTop_of_hasDerivAt_nonpos_imp_nonpos`,
`TauCeti.lt_of_tendsto_atTop_of_hasDerivAt_nonpos_imp_neg`).
`TauCeti.pos_of_hasDerivAt_mul_secant` propagates the sign of a function whose derivative is a
positive weight times a function with the strict secant property `φ t < (t / s) φ s`.

The first two statements are adapted from `tail_nonneg` and `tail_pos` of the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean`; the sign-change and secant
lemmas are factored out of the proofs in that file.

## Second differences of maps with Lipschitz derivative

Let `f` be differentiable on a convex set `s`, with derivative of norm at most `C` and
`L`-Lipschitz on `s`. Then the second difference of `f` satisfies

`‖(f (a + b) - f a) - (f (a' + b') - f a')‖ ≤ C ‖b - b'‖ + L ‖b'‖ ‖a - a'‖`

whenever `a`, `a'`, `a + b`, `a + b'` and `a' + b'` lie in `s`
(`Convex.norm_image_sub_sub_sub_le_of_norm_fderiv_le`). The first term changes the increment `b`
into `b'` at the base point `a`; the second moves the base point of `y ↦ f (y + b') - f y`, whose
derivative `Df(y + b') - Df(y)` is at most `L ‖b'‖`, from `a'` to `a`. Both steps are Mathlib's
mean value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. This is the estimate
that makes a nonlinear coefficient `x ↦ J(u(x))` Lipschitz in the map `u` for Hölder norms.

## The descent lemma

Let `f` be a real function with derivative `D y` within the segment from `x` to `x + h` at each
point `y` of that segment, and suppose `‖D y - D x‖ ≤ L * ‖y - x‖` there. Then `f` lies below
its first-order expansion at `x` plus a quadratic term,

`f (x + h) ≤ f x + D x h + L / 2 * ‖h‖ ^ 2`

(`TauCeti.le_add_apply_add_of_norm_sub_le`, and `TauCeti.le_add_fderiv_add_of_lipschitz` for
`D = fderiv ℝ f`). The hypothesis compares the derivative only with its value at the base point,
and only along the segment, so no global Lipschitz bound and no continuity of the derivative are
assumed, and `L` is an arbitrary real number. Applied to `f` and to `-f`, the lemma bounds the
first-order Taylor remainder of a function with `L`-Lipschitz derivative by `L / 2 * ‖h‖ ^ 2`,
the inequality behind the convergence analysis of gradient methods (Y. Nesterov, *Lectures on
convex optimization*, 2nd ed., Springer, 2018, Lemma 1.2.3).

## A polynomial majorant for the derivative

If `f : ℝ → E` has derivative `f' r` within `[t, u]` and `‖f' r‖ ≤ C (r - t) ^ n` on `[t, u)`, then
`‖f u - f t‖ ≤ C (u - t) ^ (n + 1) / (n + 1)`
(`TauCeti.norm_image_sub_le_of_norm_deriv_le_mul_pow_sub_left`); the same holds with the bound
`C (u - r) ^ n` (`TauCeti.norm_image_sub_le_of_norm_deriv_le_mul_pow_sub_right`). Together they
give the two-sided form: if `‖f' r‖ ≤ C |r - s| ^ n` on `[a, b]`, then
`‖f u - f s‖ ≤ C |u - s| ^ (n + 1) / (n + 1)` for `s`, `u` in `[a, b]`
(`TauCeti.norm_image_sub_le_of_norm_deriv_le_mul_abs_sub_pow`). These integrate the bounds on the
derivatives of Taylor residuals.
-/

public section

/-- **Two maps with nearby derivatives that agree at a point stay close.** If the derivatives of
`k` and `l` on a convex set `S` are within `ε` of a fixed linear map `A`, and `k` and `l` agree at
`y ∈ S`, then `‖l x - k x‖ ≤ 2 ε ‖x - y‖` for every `x ∈ S`. -/
theorem Convex.norm_sub_le_of_norm_hasFDerivWithin_sub_le {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {S : Set X} (hS : Convex ℝ S)
    {k l : X → Y} {k' l' : X → X →L[ℝ] Y} {A : X →L[ℝ] Y} {ε : ℝ}
    (hk : ∀ x ∈ S, HasFDerivWithinAt k (k' x) S x) (hl : ∀ x ∈ S, HasFDerivWithinAt l (l' x) S x)
    (hk' : ∀ x ∈ S, ‖k' x - A‖ ≤ ε) (hl' : ∀ x ∈ S, ‖l' x - A‖ ≤ ε) {x y : X} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : k y = l y) : ‖l x - k x‖ ≤ 2 * ε * ‖x - y‖ := by
  have h := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun v => l v - k v)
    (f' := fun v => l' v - k' v) (C := 2 * ε) (fun v hv => (hl v hv).sub (hk v hv))
    (fun v hv => (norm_sub_le_norm_sub_add_norm_sub (l' v) A (k' v)).trans
      (by rw [norm_sub_rev A]; linarith [hl' v hv, hk' v hv])) hy hx
  rwa [hxy, sub_self, sub_zero] at h

/-- **The mean value inequality for the operator norm.** Let `Φ : E → Λ →L[𝕜] F` be a family of
operators on a convex set `s` such that each `w ↦ Φ w f` has derivative `D w f` within `s`, where
`D w` stays within `C` of `L` in operator norm. Then on `s`, `Φ` stays within `C ‖z - y‖` of its
first-order approximation `Φ y + L.flip (z - y)`, for the operator norm. -/
theorem Convex.norm_sub_sub_flip_le_of_norm_hasFDerivWithin_sub_le {𝕜 Λ E F : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup Λ]
    [NormedSpace 𝕜 Λ] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} (hs : Convex ℝ s)
    {Φ : E → Λ →L[𝕜] F} {D : E → Λ →L[𝕜] E →L[𝕜] F} {L : Λ →L[𝕜] E →L[𝕜] F} {C : ℝ}
    (hD : ∀ w ∈ s, ∀ f, HasFDerivWithinAt (fun w ↦ Φ w f) (D w f) s w)
    (hC : ∀ w ∈ s, ‖D w - L‖ ≤ C) {y z : E} (hy : y ∈ s) (hz : z ∈ s) :
    ‖Φ z - Φ y - L.flip (z - y)‖ ≤ C * ‖z - y‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg (D y - L)).trans (hC y hy)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦ ?_
  have key := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun w ↦ Φ w f)
    (f' := fun w ↦ D w f) (φ := L f) (C := C * ‖f‖) (fun w hw ↦ hD w hw f)
    (fun w hw ↦ ((D w - L).le_opNorm f).trans (mul_le_mul_of_nonneg_right (hC w hw)
      (norm_nonneg f))) hy hz
  calc ‖(Φ z - Φ y - L.flip (z - y)) f‖ = ‖Φ z f - Φ y f - L f (z - y)‖ := by simp
    _ ≤ C * ‖f‖ * ‖z - y‖ := key
    _ = C * ‖z - y‖ * ‖f‖ := by ring

open Set

/-- Along a continuous real path, some time realizes an exact mean value increment of `f`.
Continuity is required on the image and the specified derivative only in its interior;
no derivative of the path is needed. -/
theorem ContinuousOn.exists_deriv_comp_mul_sub_eq {g f f' : ℝ → ℝ} {l u : ℝ}
    (hgc : ContinuousOn g (Icc l u)) (hlu : l ≤ u)
    (hfc : ContinuousOn f (g '' Icc l u))
    (hf : ∀ x ∈ interior (g '' Icc l u), HasDerivAt f (f' x) x) :
    ∃ t ∈ Icc l u, f' (g t) * (g u - g l) = f (g u) - f (g l) := by
  have hmean {p q : ℝ} (hfc : ContinuousOn f (uIcc p q))
      (hf : ∀ x ∈ interior (uIcc p q), HasDerivAt f (f' x) x) :
      ∃ x ∈ uIcc p q, f' x * (q - p) = f q - f p := by
    wlog hpq : p ≤ q generalizing p q
    · obtain ⟨x, hx, he⟩ := this (by simpa only [uIcc_comm] using hfc)
        (by simpa only [uIcc_comm] using hf) (le_of_not_ge hpq)
      refine ⟨x, by simpa only [uIcc_comm] using hx, ?_⟩
      rw [← neg_sub p q, mul_neg, he, neg_sub]
    rcases hpq.eq_or_lt with rfl | hpq
    · exact ⟨p, by simp, by simp⟩
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f' hpq
      (by simpa only [uIcc_of_le hpq.le] using hfc)
      (by simpa only [uIcc_of_le hpq.le, interior_Icc] using hf)
    refine ⟨x, by simpa only [uIcc_of_le hpq.le] using Ioo_subset_Icc_self hx, ?_⟩
    rw [he, div_mul_cancel₀ _ (sub_ne_zero.mpr hpq.ne')]
  -- The intermediate value theorem turns the state-space mean value into a time tag.
  have himage : uIcc (g l) (g u) ⊆ g '' Icc l u := by
    simpa only [uIcc_of_le hlu] using
      (intermediate_value_uIcc (a := l) (b := u) (f := g)
        (by simpa only [uIcc_of_le hlu] using hgc))
  obtain ⟨x, hx, he⟩ := hmean (hfc.mono himage)
    (fun x hx ↦ hf x (interior_mono himage hx))
  obtain ⟨t, ht, rfl⟩ := himage hx
  exact ⟨t, ht, he⟩

namespace Convex

/-- The mean value inequality with a bound only in the direction of the chord. The bound
is needed only on the segment joining the endpoints. In particular, neither an operator norm
bound nor a full-dimensional domain is required. Derivatives may be taken over a real or
complex scalar field. -/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_apply_le
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} {f : E → F}
    {f' : E → E →L[𝕜] F} {x y : E} {C : ℝ} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hbound : ∀ z ∈ segment ℝ x y, ‖f' z (y - x)‖ ≤ C)
    (hx : x ∈ s) (hy : y ∈ s) : ‖f y - f x‖ ≤ C := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let γ : ℝ → E := AffineMap.lineMap x y
  have hγ : MapsTo γ (Icc 0 1) s := hs.mapsTo_lineMap hx hy
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ γ) (f' (γ t) (y - x)) (Icc 0 1) t := by
    intro t ht
    simpa only [ContinuousLinearMap.coe_restrictScalars'] using
      ((hf _ (hγ ht)).restrictScalars ℝ).comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hγ
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (γ t) (y - x)‖ ≤ C := by
    intro t ht
    exact hbound _ (lineMap_mem_segment ℝ _ _ (Ico_subset_Icc_self ht))
  simpa [γ] using norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb

end Convex

namespace UniformContinuousOn

open Metric

/-- **A uniform first-order remainder estimate.** Let `G` have derivative `G' x` at every point
`x` of `s`, with `G'` uniformly continuous on `s`. Then for every `c > 0` there is `η > 0` such
that on every ball of radius `r ≤ η` contained in `s`, with centre `x₀`, the first-order remainder
of `G` against `G' x₀` is at most `c` times the increment: `‖G x₁ - G x₂ - G' x₀ (x₁ - x₂)‖ ≤
c ‖x₁ - x₂‖`. The radius `η` does not depend on `x₀`. Derivatives may be taken over a real or
complex scalar field. -/
theorem exists_pos_norm_image_sub_sub_le_of_hasFDerivAt {𝕜 X Y : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y} {G' : X → X →L[𝕜] Y} {s : Set X}
    (hG' : UniformContinuousOn G' s) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x) {c : ℝ}
    (hc : 0 < c) :
    ∃ η > 0, ∀ x₀ r, r ≤ η → ball x₀ r ⊆ s → ∀ x₁ ∈ ball x₀ r, ∀ x₂ ∈ ball x₀ r,
      ‖G x₁ - G x₂ - G' x₀ (x₁ - x₂)‖ ≤ c * ‖x₁ - x₂‖ := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ X := .restrictScalars ℝ 𝕜 X
  obtain ⟨η, hη, hG'η⟩ := Metric.uniformContinuousOn_iff_le.1 hG' c hc
  refine ⟨η, hη, fun x₀ r hr hs x₁ h₁ x₂ h₂ ↦ ?_⟩
  have hx₀ : x₀ ∈ s := hs (mem_ball_self (dist_nonneg.trans_lt h₁))
  exact (convex_ball x₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx ↦ (hGs x (hs hx)).hasFDerivWithinAt)
    (fun x hx ↦ by
      rw [← dist_eq_norm]
      exact hG'η x (hs hx) x₀ hx₀ ((mem_ball.1 hx).le.trans hr))
    h₂ h₁

end UniformContinuousOn

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the derivative of `w` has norm at most `L` wherever `a ≤ w ≤ b`, then `w` stays above `a`
at distance less than `(b - a) / L` from every point where `w ≥ b`. -/
theorem lt_apply_add_of_norm_fderiv_le {w : E → ℝ} (hw : Differentiable ℝ w)
    {a b L : ℝ} (hL : 0 ≤ L) (hbound : ∀ x, a ≤ w x → w x ≤ b → ‖fderiv ℝ w x‖ ≤ L) {x z : E}
    (hx : b ≤ w x) (hz : L * ‖z‖ < b - a) : a < w (x + z) := by
  by_contra! h
  -- Along the segment from `x` to `x + z`, let `s₁` be the first time with `w ≤ a` and `s₀` the
  -- last earlier time with `w ≥ b`. Strictly between them `a < w < b`, so the derivative bound
  -- applies there, and the mean value theorem gives a contradiction.
  let f : ℝ → ℝ := fun s => w (x + s • z)
  have hfd (s : ℝ) : HasDerivAt f (fderiv ℝ w (x + s • z) z) s := by
    have hline : HasDerivAt (fun s : ℝ => x + s • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add x
    exact (hw (x + s • z)).hasFDerivAt.comp_hasDerivAt s hline
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun s => (hfd s).continuousAt
  have hab : a < b := by nlinarith [norm_nonneg z]
  obtain ⟨s₁, ⟨⟨hs₁I, hs₁a⟩, hs₁⟩⟩ :=
    (isCompact_Icc.inter_right (isClosed_Iic.preimage hfc)).exists_isLeast
      (⟨1, right_mem_Icc.2 zero_le_one, by simpa [f] using h⟩ :
        (Icc (0 : ℝ) 1 ∩ f ⁻¹' Iic a).Nonempty)
  obtain ⟨s₀, ⟨⟨hs₀I, hs₀b⟩, hs₀⟩⟩ :=
    (isCompact_Icc.inter_right (isClosed_Ici.preimage hfc)).exists_isGreatest
      (⟨0, left_mem_Icc.2 hs₁I.1, by simpa [f] using hx⟩ : (Icc 0 s₁ ∩ f ⁻¹' Ici b).Nonempty)
  simp only [mem_preimage, mem_Iic, mem_Ici] at hs₁a hs₀b
  have hlt : s₀ < s₁ :=
    lt_of_le_of_ne hs₀I.2 fun he => by rw [he] at hs₀b; linarith
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f (fun s => fderiv ℝ w (x + s • z) z) hlt
    hfc.continuousOn fun s _ => hfd s
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hs₀I.1.trans hc.1.le, hc.2.le.trans hs₁I.2⟩
  have hca : a < f c := by
    by_contra! hca
    exact (hs₁ ⟨hcI, hca⟩).not_gt hc.2
  have hcb : f c < b := by
    by_contra! hcb
    exact (hs₀ ⟨⟨hcI.1, hc.2.le⟩, hcb⟩).not_gt hc.1
  have hd : -(L * ‖z‖) ≤ fderiv ℝ w (x + c • z) z := by
    have := ((fderiv ℝ w (x + c • z)).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (hbound _ hca.le hcb.le) (norm_nonneg z))
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (fderiv ℝ w (x + c • z) z)]
  have hpos : 0 < s₁ - s₀ := sub_pos.2 hlt
  have hslope : f s₁ - f s₀ = fderiv ℝ w (x + c • z) z * (s₁ - s₀) := by
    rw [hcd, div_mul_cancel₀ _ hpos.ne']
  have : -(L * ‖z‖) ≤ f s₁ - f s₀ := by
    rw [hslope]
    nlinarith [mul_nonneg hL (norm_nonneg z), hs₀I.1, hs₁I.2]
  linarith

open Metric in
/-- The mean value inequality: if `h` fixes `c` and `h - id` has derivative of norm at most `δ` on
the closed ball of radius `2 r` about `c`, then `h - id` moves points of this ball by at most
`δ * (2 * r)`. -/
theorem norm_sub_le_of_norm_fderiv_sub_id_le {c : E} {h : E → E} {r δ : ℝ}
    (hhc : h c = c)
    (hhd : ∀ x ∈ closedBall c (2 * r),
      HasFDerivAt (fun y ↦ h y - y) (fderiv ℝ h x - ContinuousLinearMap.id ℝ E) x)
    (hδ : ∀ x ∈ closedBall c (2 * r), ‖fderiv ℝ h x - ContinuousLinearMap.id ℝ E‖ ≤ δ)
    {x : E} (hx : x ∈ closedBall c (2 * r)) : ‖h x - x‖ ≤ δ * (2 * r) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ x hx)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy ↦ (hhd y hy).differentiableAt)
    (fun y hy ↦ (hhd y hy).fderiv ▸ hδ y hy) (convex_closedBall c (2 * r))
    (mem_closedBall_self ((dist_nonneg).trans (mem_closedBall.1 hx))) hx
  rw [hhc, sub_self, sub_zero] at this
  exact this.trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hx) hδ0)

open Metric in
open scoped NNReal in
/-- **The linearization error of a map with a Hölder derivative.** If on the closed ball of radius
`R` about `x` the map `g` has derivative `g'` and `g'` is `α`-Hölder with constant `H`, then for
points `u, v` of that ball, `‖g u - g v - g' x (u - v)‖ ≤ H R^α ‖u - v‖`: on the segment from `v`
to `u` the derivative stays within `H R^α` of `g' x`. -/
theorem norm_sub_sub_le_of_holderOnWith {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {g' : E → E →L[ℝ] F} {x : E} {R : ℝ}
    (hg : ∀ z ∈ closedBall x R, HasFDerivWithinAt g (g' z) (closedBall x R) z) {H α : ℝ≥0}
    (hg' : HolderOnWith H α g' (closedBall x R)) {u v : E} (hu : ‖u - x‖ ≤ R)
    (hv : ‖v - x‖ ≤ R) :
    ‖g u - g v - g' x (u - v)‖ ≤ H * R ^ (α : ℝ) * ‖u - v‖ := by
  have hu' : u ∈ closedBall x R := by rwa [mem_closedBall, dist_eq_norm]
  have hv' : v ∈ closedBall x R := by rwa [mem_closedBall, dist_eq_norm]
  have hx : x ∈ closedBall x R := mem_closedBall_self ((norm_nonneg _).trans hu)
  refine (convex_closedBall x R).norm_image_sub_le_of_norm_hasFDerivWithin_le' hg
    (fun z hz ↦ ?_) hv' hu'
  rw [← dist_eq_norm]
  refine (hg'.dist_le hz hx).trans ?_
  gcongr
  exact mem_closedBall.1 hz

section Direction

variable {𝕂 : Type*} [RCLike 𝕂] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕂 G]

/-- If `g` is differentiable at every point `z + t • v` of the segment from `z` to `z + v`, for
real `0 ≤ t ≤ 1`, and its derivative kills `v` there, then `g` takes the same value at `z` and at
`z + v`. -/
theorem apply_add_eq_of_fderiv_apply_eq_zero {g : F → G} {z v : F}
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt 𝕂 g (z + (t : 𝕂) • v))
    (hv : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv 𝕂 g (z + (t : 𝕂) • v) v = 0) : g (z + v) = g z := by
  -- The points of the real segment from `0` to `1` in `𝕂` are the real numbers in `[0, 1]`.
  have hs : ∀ t ∈ segment ℝ (0 : 𝕂) 1, ∃ r ∈ Set.Icc (0 : ℝ) 1, (r : 𝕂) = t := by
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b, ⟨hb, ?_⟩, by simp [RCLike.real_smul_eq_coe_mul]⟩
    linarith
  -- The restriction of `g` to the line through `z` in direction `v` has zero derivative on this
  -- segment, which is convex and contains `0` and `1`.
  have hq : ∀ t ∈ segment ℝ (0 : 𝕂) 1, HasFDerivWithinAt (fun t : 𝕂 ↦ g (z + t • v))
      ((fderiv 𝕂 g (z + t • v)).comp ((ContinuousLinearMap.id 𝕂 𝕂).smulRight v))
      (segment ℝ (0 : 𝕂) 1) t := fun t ht ↦ by
    obtain ⟨r, hr, rfl⟩ := hs t ht
    exact ((hg r hr).hasFDerivAt.comp (r : 𝕂)
      ((hasFDerivAt_id _).smul_const v |>.const_add z)).hasFDerivWithinAt
  have h := (convex_segment (0 : 𝕂) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le hq
    (C := 0) (fun t ht ↦ by
      obtain ⟨r, hr, rfl⟩ := hs t ht
      rw [norm_le_zero_iff]
      ext
      simp [hv r hr])
    (left_mem_segment ℝ (0 : 𝕂) 1) (right_mem_segment ℝ (0 : 𝕂) 1)
  simpa [sub_eq_zero] using h

/-- Let `π` be a continuous projection of `F`. If `g` is differentiable on the ball of radius `r`
about `0` and its derivative there kills the kernel of `π`, then `g` only depends on the `π`
component on the part of that ball where `‖π z‖ + ‖z - π z‖ < r`. -/
theorem apply_proj_eq_of_fderiv_apply_eq_zero {g : F → G} {π : F →L[𝕂] F}
    (hπ : IsIdempotentElem π) {r : ℝ} (hg : DifferentiableOn 𝕂 g (Metric.ball 0 r))
    (hker : ∀ u ∈ Metric.ball (0 : F) r, ∀ v, π v = 0 → fderiv 𝕂 g u v = 0) {z : F}
    (hz : ‖π z‖ + ‖z - π z‖ < r) : g (π z) = g z := by
  have hπz : π (z - π z) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congr($hπ z).symm
  -- The segment from `π z` to `z` stays in the ball.
  have hball (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      π z + (t : 𝕂) • (z - π z) ∈ Metric.ball (0 : F) r := by
    rw [mem_ball_zero_iff]
    refine (norm_add_le _ _).trans_lt (lt_of_le_of_lt ?_ hz)
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg ht.1]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have h := apply_add_eq_of_fderiv_apply_eq_zero (z := π z) (v := z - π z)
    (fun t ht ↦ hg.differentiableAt (Metric.isOpen_ball.mem_nhds (hball t ht)))
    (fun t ht ↦ hker _ (hball t ht) _ hπz)
  rw [add_sub_cancel] at h
  exact h.symm

/-- A compactly supported differentiable map whose derivative in a fixed nonzero direction `v`
vanishes identically is zero: moving along `v` does not change its value, and far enough along `v`
the point leaves the support. -/
theorem _root_.HasCompactSupport.eq_zero_of_fderiv_apply_eq_zero {g : F → G}
    (hc : HasCompactSupport g) (hg : Differentiable 𝕂 g) {v : F} (hv : v ≠ 0)
    (h0 : ∀ w, fderiv 𝕂 g w v = 0) (z : F) : g z = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set c : ℝ := (|R| + ‖z‖ + 1) / ‖v‖
  have hconst := apply_add_eq_of_fderiv_apply_eq_zero (z := z) (v := (c : 𝕂) • v)
    (fun _ _ ↦ hg _) fun _ _ ↦ by rw [map_smul, h0, smul_zero]
  rw [← hconst]
  refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
  have hle := mem_closedBall_zero_iff.1 (hR hmem)
  have hcv : ‖(c : 𝕂) • v‖ = |R| + ‖z‖ + 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv)]
  have hlow := norm_sub_norm_le ((c : 𝕂) • v) (-z)
  rw [sub_neg_eq_add, norm_neg, hcv, add_comm ((c : 𝕂) • v)] at hlow
  linarith [le_abs_self R]

end Direction

/-- **The mean value inequality along three segments.** If the segments `[x, p]`, `[p, q]` and
`[q, y]` lie in a set `s` on which `g` is differentiable with derivative bounded by `L`, then
`‖g y - g x‖ ≤ L (‖x - p‖ + ‖p - q‖ + ‖q - y‖)`. Compare
`Convex.norm_image_sub_le_of_norm_fderiv_le` for a single segment. -/
theorem norm_image_sub_le_of_norm_fderiv_le_of_segment_subset {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {s : Set F} {g : F → G} {L : ℝ}
    (hg : ∀ z ∈ s, DifferentiableAt ℝ g z) (hL : ∀ z ∈ s, ‖fderiv ℝ g z‖ ≤ L) {x p q y : F}
    (hxp : segment ℝ x p ⊆ s) (hpq : segment ℝ p q ⊆ s) (hqy : segment ℝ q y ⊆ s) :
    ‖g y - g x‖ ≤ L * (dist x p + dist p q + dist q y) := by
  have hseg : ∀ {a b : F}, segment ℝ a b ⊆ s → ‖g b - g a‖ ≤ L * dist a b := fun {a b} hab ↦ by
    rw [dist_comm, dist_eq_norm]
    exact (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le (fun z hz ↦ hg z (hab hz))
      (fun z hz ↦ hL z (hab hz)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  calc ‖g y - g x‖ = ‖(g p - g x) + (g q - g p) + (g y - g q)‖ := by abel_nf
    _ ≤ ‖g p - g x‖ + ‖g q - g p‖ + ‖g y - g q‖ := norm_add₃_le
    _ ≤ L * dist x p + L * dist p q + L * dist q y := by
      gcongr <;> exact hseg ‹_›
    _ = _ := by ring

/-- A function with derivative bounded by `C` that vanishes outside the time interval `(a, b)` is
bounded by `C * (b - a)`, by the mean value inequality from its value at the time `a`. -/
theorem norm_le_mul_sub_of_forall_notMem_Ioo_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {φ : ℝ × E → ℝ} (hφd : Differentiable ℝ φ) {C : ℝ}
    (hC : ∀ q, ‖fderiv ℝ φ q‖ ≤ C) (hzero : ∀ q : ℝ × E, q.1 ∉ Ioo a b → φ q = 0) (hab : a ≤ b)
    (q : ℝ × E) : ‖φ q‖ ≤ C * (b - a) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  by_cases hq : q.1 ∈ Ioo a b
  · have hq' : q - (a, q.2) = (q.1 - a, 0) := by ext <;> simp
    have hn : ‖q - (a, q.2)‖ ≤ b - a := by
      rw [hq', Prod.norm_def, norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg _),
        abs_of_pos (sub_pos.2 hq.1)]
      linarith [hq.2]
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun p _ ↦ hφd p) (fun p _ ↦ hC p)
      (mem_univ (a, q.2)) (mem_univ q)
    rw [hzero (a, q.2) (by simp), sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hn hC0)
  · rw [hzero q hq, norm_zero]
    exact mul_nonneg hC0 (sub_nonneg.2 hab)

open Topology in
/-- Let `f : E → F` be differentiable in a neighbourhood of `a`. If `Df(x) = o(‖x - a‖ ^ r)` as
`x → a`, where `r ≥ 0`, then `f(x) - f(a) = o(‖x - a‖ ^ (r + 1))`. This is the little-o counterpart
of Mathlib's `sub_isBigO_norm_rpow_add_one_of_fderiv`. -/
theorem sub_isLittleO_norm_rpow_add_one_of_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {a : E} {r : ℝ}
    (hr : 0 ≤ r) (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hderiv : fderiv ℝ f =o[𝓝 a] (‖· - a‖ ^ r)) :
    (f · - f a) =o[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  -- the mean value inequality on balls about `a`, as for `sub_isBigO_norm_rpow_add_one_of_fderiv`
  refine Asymptotics.IsLittleO.of_bound fun C hC ↦ ?_
  obtain ⟨ε, hε₀, hε⟩ := Metric.eventually_nhds_iff_ball.mp (hdf.and (hderiv.bound hC))
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy ↦ ?_⟩
  have hsub : Metric.closedBall a ‖y - a‖ ⊆ Metric.ball a ε :=
    Metric.closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  have h := (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (C := C * ‖y - a‖ ^ r) (fun z hz ↦ (hε z (hsub hz)).1) (fun z hz ↦ ?_)
    (Metric.mem_closedBall_self (norm_nonneg _)) (mem_closedBall_iff_norm.mpr le_rfl)
  · rw [Real.norm_of_nonneg (by positivity), Real.rpow_add_one' (by positivity) (by positivity),
      ← mul_assoc]
    exact h
  · refine (hε z (hsub hz)).2.trans ?_
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    exact mem_closedBall_iff_norm.mp hz

end TauCeti

/-- **The outer shell of a thickening of a superlevel set lies in a level band.** Let `w` be
differentiable with `‖Dw‖ ≤ L` wherever `-(L r) ≤ w ≤ 0`. Then the part of the open
`r`-neighbourhood of `{w ≥ 0}` outside `{w ≥ 0}` lies in `{-(L r) < w < 0}`. -/
theorem Differentiable.thickening_sdiff_subset_preimage_Ioo_of_norm_fderiv_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {w : E → ℝ} (hw : Differentiable ℝ w) {L r : ℝ}
    (hL : 0 < L) (hgrad : ∀ x, -(L * r) ≤ w x → w x ≤ 0 → ‖fderiv ℝ w x‖ ≤ L) :
    Metric.thickening r {x | 0 ≤ w x} \ {x | 0 ≤ w x} ⊆ w ⁻¹' Ioo (-(L * r)) 0 := by
  rintro x ⟨hx, hxs⟩
  obtain ⟨p, hp, hpx⟩ := Metric.mem_thickening_iff.1 hx
  refine ⟨?_, lt_of_not_ge hxs⟩
  have := TauCeti.lt_apply_add_of_norm_fderiv_le hw (a := -(L * r)) (b := 0) hL.le hgrad
    (hp : 0 ≤ w p) (z := x - p) (by
      rw [← dist_eq_norm]
      linarith [mul_lt_mul_of_pos_left hpx hL])
  simpa using this

namespace Convex

variable {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}

/-- Variant of the mean value inequality on a convex set in dimension 1, using a bound on the
difference between the derivative and a fixed vector `φ`, rather than a bound on the derivative
itself. Version with `HasDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasDerivWithin_le' {φ : G} {C : ℝ}
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x - φ‖ ≤ C)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x - (y - x) • φ‖ ≤ C * ‖y - x‖ := by
  have key := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun z ↦ f z - z • φ)
    (fun z hz ↦ ((hf z hz).sub ((hasDerivWithinAt_id z s).smul_const φ)).congr_deriv
      (by rw [one_smul])) bound xs ys
  convert key using 2
  rw [sub_smul]
  abel

end Convex

/-- A chord in a closed unit ball remains uniformly close in the image to its initial point,
relative to the image distance to a prescribed intermediate point, if the parametrization
has bounded derivative and is antilipschitz on the ball. -/
theorem Differentiable.norm_sub_le_mul_of_segment {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {φ : P → Q} (hφd : Differentiable ℝ φ) {C κ : ℝ}
    (hbound : ∀ x ∈ Metric.closedBall (0 : P) 1, ‖fderiv ℝ φ x‖ ≤ C)
    (hanti : ∀ a ∈ Metric.closedBall (0 : P) 1, ∀ b ∈ Metric.closedBall (0 : P) 1,
      ‖a - b‖ ≤ κ * ‖φ a - φ b‖)
    {a b : P} (ha : a ∈ Metric.closedBall (0 : P) 1)
    (hb : b ∈ Metric.closedBall (0 : P) 1) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) s) :
    ‖φ a - φ (a + t • (b - a))‖ ≤ C * κ * ‖φ a - φ (a + s • (b - a))‖ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0 (by simp))
  have hsnorm : s * ‖b - a‖ ≤ κ * ‖φ a - φ (a + s • (b - a))‖ := by
    have h1 := hanti a ha _ ((convex_closedBall (0 : P) 1).add_smul_sub_mem ha hb hs)
    have heq : a - (a + s • (b - a)) = -(s • (b - a)) := by module
    simpa only [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] using h1
  have hconv := convex_closedBall (0 : P) 1
  have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ ↦ (hφd x).hasFDerivAt.hasFDerivWithinAt) hbound ha
      ((convex_closedBall (0 : P) 1).add_smul_sub_mem ha hb ⟨ht.1, ht.2.trans hs.2⟩)
  have heq : (a + t • (b - a)) - a = t • (b - a) := by module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hmv
  rw [norm_sub_rev]
  refine hmv.trans ?_
  have htnorm : t * ‖b - a‖ ≤ κ * ‖φ a - φ (a + s • (b - a))‖ :=
    (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans hsnorm
  calc C * (t * ‖b - a‖) ≤ C * (κ * ‖φ a - φ (a + s • (b - a))‖) :=
        mul_le_mul_of_nonneg_left htnorm hC
    _ = C * κ * ‖φ a - φ (a + s • (b - a))‖ := by ring

/-- The mean value estimate along a parametrized chord, with bounds on the coordinate
derivatives of a real-valued function and the derivative of the parametrization. -/
theorem Differentiable.abs_sub_le_of_basis_bound {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}
    {φ : P → (Fin n → ℝ)} (hφd : Differentiable ℝ φ)
    {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f) {C D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Metric.closedBall (0 : P) 1, ‖fderiv ℝ φ x‖ ≤ C)
    {a b : P} (ha : a ∈ Metric.closedBall (0 : P) 1)
    (hb : b ∈ Metric.closedBall (0 : P) 1) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hcoord : ∀ t ∈ Set.Ico (0 : ℝ) s, ∀ j : Fin n,
      |fderiv ℝ f (φ (a + t • (b - a))) (Pi.single j (1 : ℝ))| ≤ D) :
    |f (φ (a + s • (b - a))) - f (φ a)| ≤ n * (C * ‖b - a‖) * D * s := by
  let g : ℝ → ℝ := fun t ↦ f (φ (a + t • (b - a)))
  let g' : ℝ → ℝ := fun t ↦
    fderiv ℝ f (φ (a + t • (b - a))) (fderiv ℝ φ (a + t • (b - a)) (b - a))
  have hcurve (t : ℝ) : HasDerivAt (fun t : ℝ ↦ a + t • (b - a)) (b - a) t := by
    simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
  have hgd (t : ℝ) : HasDerivAt g (g' t) t :=
    (hf _).hasFDerivAt.comp_hasDerivAt t
      ((hφd _).hasFDerivAt.comp_hasDerivAt t (hcurve t))
  have hderiv : ∀ t ∈ Ico (0 : ℝ) s, ‖g' t‖ ≤ n * (C * ‖b - a‖) * D := by
    intro t ht
    have hball := (convex_closedBall (0 : P) 1).add_smul_sub_mem ha hb
      ⟨ht.1, ht.2.le.trans hs.2⟩
    have hvnorm : ‖fderiv ℝ φ (a + t • (b - a)) (b - a)‖ ≤ C * ‖b - a‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hbound _ hball) (norm_nonneg _))
    have hcoord_bound := ((LinearMap.norm_apply_le_sum_norm_mul
      (fderiv ℝ f (φ (a + t • (b - a)))).toLinearMap (fderiv ℝ φ (a + t • (b - a)) (b - a))).trans
      ((Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
        ((Real.norm_eq_abs _).trans_le (hcoord t ht j)) (norm_nonneg _)).trans_eq
        (Finset.sum_mul _ _ _).symm)).trans <|
      mul_le_mul_of_nonneg_right ((Pi.sum_norm_apply_le_norm
        (fderiv ℝ φ (a + t • (b - a)) (b - a))).trans_eq (nsmul_eq_mul _ _)) hD
    have hscalar : |g' t| ≤ n * ‖fderiv ℝ φ (a + t • (b - a)) (b - a)‖ * D := by
      simpa only [g', Fintype.card_fin, Real.norm_eq_abs, ContinuousLinearMap.coe_coe]
        using hcoord_bound
    exact hscalar.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvnorm (Nat.cast_nonneg n)) hD)
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t _ ↦ (hgd t).hasDerivWithinAt) hderiv s (right_mem_Icc.mpr hs.1)
  simpa only [g, zero_smul, add_zero, sub_zero, Real.norm_eq_abs] using hmain

namespace ContDiff

open Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lipschitz bound for a jointly `C¹` family on a box.** If `Γ t s` is `C¹` in `(t, s)`, there is
a constant `B` such that `‖Γ t₁ s₁ - Γ t₂ s₂‖ ≤ B * max |t₁ - t₂| |s₁ - s₂|` for all `t₁, t₂` in
`[t₀, t₁']` and all `s₁, s₂` in `[a, b]`. -/
theorem exists_norm_sub_le_mul_max_uncurry {Γ : ℝ → ℝ → E} (hΓ : ContDiff ℝ 1 (uncurry Γ))
    (t₀ t₀' a b : ℝ) :
    ∃ B : NNReal, ∀ ⦃x₁ y₁ x₂ y₂ : ℝ⦄, x₁ ∈ Icc t₀ t₀' → y₁ ∈ Icc a b → x₂ ∈ Icc t₀ t₀' →
      y₂ ∈ Icc a b → ‖Γ x₁ y₁ - Γ x₂ y₂‖ ≤ B * max |x₁ - x₂| |y₁ - y₂| := by
  have hQc : IsCompact (Icc t₀ t₀' ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hQv : Convex ℝ (Icc t₀ t₀' ×ˢ Icc a b) := (convex_Icc _ _).prod (convex_Icc _ _)
  obtain ⟨B, hB⟩ := hΓ.contDiffOn.exists_lipschitzOnWith one_ne_zero hQv hQc
  refine ⟨B, fun x₁ y₁ x₂ y₂ hx₁ hy₁ hx₂ hy₂ ↦ ?_⟩
  have := hB.dist_le_mul (x := (x₁, y₁)) (y := (x₂, y₂)) ⟨hx₁, hy₁⟩ ⟨hx₂, hy₂⟩
  simpa [dist_eq_norm, Prod.dist_eq, Real.dist_eq] using this

end ContDiff

namespace IsPreconnected

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ → G} {s : Set ℝ}

/-- A function on a preconnected subset of `ℝ` whose derivative within the set vanishes at every
point of the set takes the same value at any two points of the set. -/
theorem eq_of_hasDerivWithinAt_zero (hs : IsPreconnected s)
    (hf : ∀ t ∈ s, HasDerivWithinAt f 0 s t) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b := by
  have h := (Real.convex_iff_isPreconnected.2 hs).norm_image_sub_le_of_norm_hasDerivWithin_le
    hf (C := 0) (fun _ _ ↦ by simp) ha hb
  simpa [sub_eq_zero, eq_comm] using h

end IsPreconnected

namespace Convex

variable {𝕜 E G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f : E → G} {Ω s : Set E} {x y : E}

open Metric Set in
open scoped Topology in
/-- **Constancy on a preconnected relatively open part of a convex set.** Let `Ω` be open and `s`
convex, such as a closed half-space. A function on `Ω ∩ s` whose derivative within `Ω ∩ s`
vanishes at every point is constant on `Ω ∩ s` when that set is preconnected. The convex case
`Ω = univ` is Mathlib's `Convex.is_const_of_fderivWithin_eq_zero`. -/
theorem is_const_of_fderivWithin_inter_eq_zero (hs : Convex ℝ s) (hΩ : IsOpen Ω)
    (hc : IsPreconnected (Ω ∩ s)) (hf : DifferentiableOn 𝕜 f (Ω ∩ s))
    (hf' : ∀ z ∈ Ω ∩ s, fderivWithin 𝕜 f (Ω ∩ s) z = 0) (hx : x ∈ Ω ∩ s) (hy : y ∈ Ω ∩ s) :
    f x = f y := by
  classical
  -- `f` is locally constant on `Ω ∩ s`, which agrees near each of its points with a convex set
  have hloc : ∀ z ∈ Ω ∩ s, ∀ᶠ w in 𝓝[Ω ∩ s] z, f w = f z := by
    intro z hz
    obtain ⟨r, hr, hrΩ⟩ := isOpen_iff.1 hΩ z hz.1
    have hset : ball z r ∩ s = (Ω ∩ s) ∩ ball z r :=
      Set.ext fun w ↦ ⟨fun h ↦ ⟨⟨hrΩ h.1, h.2⟩, h.1⟩, fun h ↦ ⟨h.2, h.1.2⟩⟩
    have hd : ∀ w ∈ ball z r ∩ s, fderivWithin 𝕜 f (ball z r ∩ s) w = 0 := fun w hw ↦ by
      rw [hset, fderivWithin_inter (isOpen_ball.mem_nhds hw.1)]
      exact hf' w ⟨hrΩ hw.1, hw.2⟩
    have hconst : ∀ w ∈ ball z r ∩ s, f z = f w := fun w hw ↦
      ((convex_ball z r).inter hs).is_const_of_fderivWithin_eq_zero
        (hf.mono fun w hw ↦ ⟨hrΩ hw.1, hw.2⟩) hd ⟨mem_ball_self hr, hz.2⟩ hw
    exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (ball_mem_nhds z hr))
      fun w hw ↦ (hconst w ⟨hw.2, hw.1.2⟩).symm
  -- a locally constant map on a preconnected set is constant
  have hcont : ContinuousOn (fun w ↦ decide (f w = f x)) (Ω ∩ s) := fun z hz ↦
    continuousWithinAt_const.congr_of_eventuallyEq
      ((hloc z hz).mono fun w hw ↦ by simp only [hw]) rfl
  have h := hc.constant hcont hx hy
  simp only [decide_true, Bool.true_eq, decide_eq_true_eq] at h
  exact h.symm

end Convex

/-- A function `f : 𝕜 → G`, `𝕜 = ℝ` or `𝕜 = ℂ`, with zero derivative at every point is constant.
This is the `HasDerivAt` form of Mathlib's `is_const_of_deriv_eq_zero`. -/
theorem TauCeti.is_const_of_hasDerivAt_zero {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {f : 𝕜 → G} (hf : ∀ t, HasDerivAt f 0 t) (t s : 𝕜) : f t = f s :=
  is_const_of_deriv_eq_zero (fun t ↦ (hf t).differentiableAt) (fun t ↦ (hf t).deriv) t s

namespace TauCeti

open Filter Set
open scoped Topology

variable {f f' : ℝ → ℝ} {a x L : ℝ}

/-- A real function continuous on `[x, ∞)`, with a nonpositive derivative on `(x, ∞)` and limit
`L` at `+∞`, satisfies `L ≤ f x`. -/
theorem le_of_tendsto_atTop_of_hasDerivAt_nonpos (hfc : ContinuousOn f (Ici x))
    (hf : ∀ y, x < y → HasDerivAt f (f' y) y) (hlim : Tendsto f atTop (𝓝 L))
    (hf' : ∀ y, x < y → f' y ≤ 0) : L ≤ f x := by
  have hanti : AntitoneOn f (Ici x) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici x) hfc
      (fun y hy => (hf y (by simpa using hy)).hasDerivWithinAt)
      (fun y hy => hf' y (by simpa using hy))
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop x] with t ht
  exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-- A real function continuous on `[x, ∞)`, with a negative derivative on `(x, ∞)` and limit `L`
at `+∞`, satisfies `L < f x`. -/
theorem lt_of_tendsto_atTop_of_hasDerivAt_neg (hfc : ContinuousOn f (Ici x))
    (hf : ∀ y, x < y → HasDerivAt f (f' y) y) (hlim : Tendsto f atTop (𝓝 L))
    (hf' : ∀ y, x < y → f' y < 0) : L < f x := by
  have hanti : StrictAntiOn f (Ici x) :=
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici x) hfc
      (fun y hy => (hf y (by simpa using hy)).hasDerivWithinAt)
      (fun y hy => hf' y (by simpa using hy))
  have h1 : L ≤ f (x + 1) := le_of_tendsto_atTop_of_hasDerivAt_nonpos
    (hfc.mono (Ici_subset_Ici.mpr (by linarith))) (fun y hy => hf y (by linarith)) hlim
    (fun y hy => (hf' y (by linarith)).le)
  exact h1.trans_lt (hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith))

/-- A real function continuous on `[a, x]`, `a < x`, with a positive derivative on `(a, x)`
satisfies `f a < f x`. -/
theorem lt_of_hasDerivAt_pos (hax : a < x) (hfc : ContinuousOn f (Icc a x))
    (hf : ∀ y ∈ Ioo a x, HasDerivAt f (f' y) y) (hf' : ∀ y ∈ Ioo a x, 0 < f' y) : f a < f x :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a x) hfc
    (fun y hy => (hf y (by simpa using hy)).hasDerivWithinAt)
    (fun y hy => hf' y (by simpa using hy)) ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax

/-- A real function continuous on `[a, x]`, `a < x`, with a negative derivative on `(a, x)`
satisfies `f x < f a`. -/
theorem lt_of_hasDerivAt_neg (hax : a < x) (hfc : ContinuousOn f (Icc a x))
    (hf : ∀ y ∈ Ioo a x, HasDerivAt f (f' y) y) (hf' : ∀ y ∈ Ioo a x, f' y < 0) : f x < f a :=
  strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a x) hfc
    (fun y hy => (hf y (by simpa using hy)).hasDerivWithinAt)
    (fun y hy => hf' y (by simpa using hy)) ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax

/-- **Sign change of the derivative, nonstrict form.** Let `f` be continuous on `[a, ∞)` with
limit `L` at `+∞` and `L ≤ f a`, and let its derivative stay nonpositive beyond any point of
`(a, ∞)` where it is nonpositive (so `f` first increases, then decreases). Then `L ≤ f x` for
`x ≥ a`. -/
theorem le_of_tendsto_atTop_of_hasDerivAt_nonpos_imp_nonpos (hax : a ≤ x)
    (hfc : ContinuousOn f (Ici a)) (hf : ∀ y, a < y → HasDerivAt f (f' y) y) (ha : L ≤ f a)
    (hlim : Tendsto f atTop (𝓝 L)) (hf' : ∀ y z, a < y → y ≤ z → f' y ≤ 0 → f' z ≤ 0) :
    L ≤ f x := by
  rcases hax.eq_or_lt with rfl | hax
  · exact ha
  rcases le_or_gt (f' x) 0 with hx | hx
  · exact le_of_tendsto_atTop_of_hasDerivAt_nonpos (hfc.mono (Ici_subset_Ici.mpr hax.le))
      (fun y hy => hf y (hax.trans hy)) hlim fun y hy => hf' x y hax hy.le hx
  · have hmono : MonotoneOn f (Icc a x) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a x) (hfc.mono Icc_subset_Ici_self)
        (fun y hy => by
          rw [interior_Icc] at hy
          exact (hf y hy.1).hasDerivWithinAt)
        (fun y hy => by
          rw [interior_Icc] at hy
          by_contra! h
          exact (hf' y x hy.1 hy.2.le h.le).not_gt hx)
    exact ha.trans (hmono ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax.le)

/-- **Sign change of the derivative, strict form.** Let `f` be continuous on `[a, ∞)` with limit
`L` at `+∞` and `L ≤ f a`, and let its derivative be negative beyond any point of `(a, ∞)` where
it is nonpositive. Then `L < f x` for `x > a`. -/
theorem lt_of_tendsto_atTop_of_hasDerivAt_nonpos_imp_neg (hax : a < x)
    (hfc : ContinuousOn f (Ici a)) (hf : ∀ y, a < y → HasDerivAt f (f' y) y) (ha : L ≤ f a)
    (hlim : Tendsto f atTop (𝓝 L)) (hf' : ∀ y z, a < y → y < z → f' y ≤ 0 → f' z < 0) :
    L < f x := by
  rcases le_or_gt (f' x) 0 with hx | hx
  · exact lt_of_tendsto_atTop_of_hasDerivAt_neg (hfc.mono (Ici_subset_Ici.mpr hax.le))
      (fun y hy => hf y (hax.trans hy)) hlim fun y hy => hf' x y hax hy hx
  · refine ha.trans_lt (lt_of_hasDerivAt_pos hax (hfc.mono Icc_subset_Ici_self)
      (fun y hy => hf y hy.1) fun y hy => ?_)
    by_contra! h
    exact (hf' y x hy.1 hy.2 h).not_gt hx

/-- **Sign propagation for a secant-convex derivative.** Let `D(0) = 0` and
`D′(y) = w(y) φ(y²)` with `w > 0`, where `φ(t) < (t/s) φ(s)` for `0 < t < s`. If `D(y) ≥ 0` at
some `y > 0`, then `D > 0` on `(y, ∞)`. -/
theorem pos_of_hasDerivAt_mul_secant {D w φ : ℝ → ℝ} (hw : ∀ y, 0 < w y)
    (hD : ∀ y, HasDerivAt D (w y * φ (y ^ 2)) y) (hD0 : D 0 = 0)
    (hsec : ∀ t s, 0 < t → t < s → φ t < t / s * φ s) {y : ℝ} (hy : 0 < y) (hDy : 0 ≤ D y)
    {t : ℝ} (hyt : y < t) : 0 < D t := by
  have hcont : Continuous D := continuous_iff_continuousAt.mpr fun s => (hD s).continuousAt
  -- If `φ(y²) ≤ 0`, then `φ(s²) < 0` on `(0, y)` by the secant property, so `D y < D 0 = 0`.
  have hφy : 0 < φ (y ^ 2) := by
    by_contra! hcon
    have := lt_of_hasDerivAt_neg (f' := fun s => w s * φ (s ^ 2)) hy hcont.continuousOn
      (fun s _ => hD s) fun s hs => by
        have hs0 : 0 < s := hs.1
        have h1 := hsec _ _ (by positivity : 0 < s ^ 2) (by nlinarith [hs.2] : s ^ 2 < y ^ 2)
        have h2 : s ^ 2 / y ^ 2 * φ (y ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
        exact mul_neg_of_pos_of_neg (hw s) (by linarith)
    linarith
  -- Then `φ(s²) > 0` for `s > y`, so `D` increases strictly on `[y, t]`.
  have := lt_of_hasDerivAt_pos (f' := fun s => w s * φ (s ^ 2)) hyt hcont.continuousOn
    (fun s _ => hD s) fun s hs => by
      have h1 := hsec _ _ (by positivity : 0 < y ^ 2) (by nlinarith [hs.1] : y ^ 2 < s ^ 2)
      have h2 : 0 < φ (s ^ 2) := by
        by_contra! hcon
        have : y ^ 2 / s ^ 2 * φ (s ^ 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
        linarith
      exact mul_pos (hw s) h2
  linarith

end TauCeti

section SecondDifference

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {f : E → G} {s : Set E} {C L : ℝ}

/-- **Second-difference estimate.** If `f` is differentiable on the convex set `s`, with
`‖Df‖ ≤ C` and `Df` `L`-Lipschitz there, then
`‖(f (a + b) - f a) - (f (a' + b') - f a')‖ ≤ C ‖b - b'‖ + L ‖b'‖ ‖a - a'‖`
when `a`, `a'`, `a + b`, `a + b'` and `a' + b'` lie in `s`. -/
theorem Convex.norm_image_sub_sub_sub_le_of_norm_fderiv_le (hs : Convex ℝ s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C)
    (hL : ∀ x ∈ s, ∀ y ∈ s, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖)
    {a a' b b' : E} (ha : a ∈ s) (ha' : a' ∈ s) (hab : a + b ∈ s) (hab' : a + b' ∈ s)
    (ha'b' : a' + b' ∈ s) :
    ‖(f (a + b) - f a) - (f (a' + b') - f a')‖ ≤ C * ‖b - b'‖ + L * ‖b'‖ * ‖a - a'‖ := by
  -- The first step changes `b` into `b'` at the base point `a`.
  have hfirst : ‖f (a + b) - f (a + b')‖ ≤ C * ‖b - b'‖ := by
    simpa using hs.norm_image_sub_le_of_norm_fderiv_le hd hC hab' hab
  -- The second step moves the base point of `y ↦ f (y + b') - f y` from `a'` to `a`.
  have hseg : ∀ y ∈ segment ℝ a' a, y ∈ s ∧ y + b' ∈ s := fun y hy ↦ by
    refine ⟨hs.segment_subset ha' ha hy, hs.segment_subset ha'b' hab' ?_⟩
    have h : b' + y ∈ segment ℝ (b' + a') (b' + a) := by
      rw [← segment_translate_image]
      exact ⟨y, hy, rfl⟩
    simpa only [add_comm b'] using h
  have hsecond : ‖(f (a + b') - f a) - (f (a' + b') - f a')‖ ≤ L * ‖b'‖ * ‖a - a'‖ := by
    have hφd : ∀ y ∈ segment ℝ a' a, HasFDerivWithinAt (fun y ↦ f (y + b') - f y)
        (fderiv ℝ f (y + b') - fderiv ℝ f y) (segment ℝ a' a) y := fun y hy ↦ by
      have hshift := (hd _ (hseg y hy).2).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const b')
      rw [ContinuousLinearMap.comp_id] at hshift
      exact (hshift.sub (hd y (hseg y hy).1).hasFDerivAt).hasFDerivWithinAt
    refine (convex_segment a' a).norm_image_sub_le_of_norm_hasFDerivWithin_le hφd
      (fun y hy ↦ ?_) (left_mem_segment ℝ a' a) (right_mem_segment ℝ a' a)
    simpa using hL _ (hseg y hy).2 y (hseg y hy).1
  calc _ = ‖(f (a + b) - f (a + b')) + ((f (a + b') - f a) - (f (a' + b') - f a'))‖ := by
        congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hfirst hsecond)

end SecondDifference

namespace TauCeti

section Descent

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x h : E} {L : ℝ}

/-- **The descent lemma**, for a derivative within the segment. If `f` has derivative `D y`
within the segment from `x` to `x + h` at each point `y` of that segment, and
`‖D y - D x‖ ≤ L * ‖y - x‖` there, then `f (x + h) ≤ f x + D x h + L / 2 * ‖h‖ ^ 2`. -/
theorem le_add_apply_add_of_norm_sub_le {D : E → E →L[ℝ] ℝ}
    (hf : ∀ y ∈ segment ℝ x (x + h), HasFDerivWithinAt f (D y) (segment ℝ x (x + h)) y)
    (hL : ∀ y ∈ segment ℝ x (x + h), ‖D y - D x‖ ≤ L * ‖y - x‖) :
    f (x + h) ≤ f x + D x h + L / 2 * ‖h‖ ^ 2 := by
  have hmaps : MapsTo (AffineMap.lineMap x (x + h)) (Icc (0 : ℝ) 1) (segment ℝ x (x + h)) :=
    fun t ht ↦ lineMap_mem_segment ℝ x (x + h) ht
  -- The restriction of `f` to the segment has derivative `D (lineMap x (x + h) t) h` at `t`.
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (f ∘ AffineMap.lineMap x (x + h))
      (D (AffineMap.lineMap x (x + h) t) h) (Icc 0 1) t := fun t ht ↦ by
    simpa using (hf _ (hmaps ht)).comp_hasDerivWithinAt t
      (AffineMap.hasDerivWithinAt_lineMap (a := x) (b := x + h)) hmaps
  -- Compare it with the quadratic `t ↦ f x + t * D x h + L / 2 * ‖h‖ ^ 2 * t ^ 2` on `[0, 1]`.
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ f x + t * D x h + L / 2 * ‖h‖ ^ 2 * t ^ 2)
      (D x h + L / 2 * ‖h‖ ^ 2 * (2 * t)) t := fun t ↦ by
    have hlin : HasDerivAt (fun t : ℝ ↦ f x + t * D x h) (D x h) t := by
      simpa using ((hasDerivAt_id t).mul_const (D x h)).const_add (f x)
    have hquad : HasDerivAt (fun t : ℝ ↦ L / 2 * ‖h‖ ^ 2 * t ^ 2)
        (L / 2 * ‖h‖ ^ 2 * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖h‖ ^ 2)
    exact hlin.add hquad
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      D (AffineMap.lineMap x (x + h) t) h ≤ D x h + L / 2 * ‖h‖ ^ 2 * (2 * t) := fun t ht ↦ by
    have hnorm : ‖AffineMap.lineMap x (x + h) t - x‖ = t * ‖h‖ := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_sub_cancel_right, norm_smul,
        Real.norm_of_nonneg ht.1]
    have hop : (D (AffineMap.lineMap x (x + h) t) - D x) h ≤ L * (t * ‖h‖) * ‖h‖ :=
      (le_abs_self _).trans <| ((D (AffineMap.lineMap x (x + h) t) - D x).le_opNorm h).trans <|
        mul_le_mul_of_nonneg_right
          ((hL _ (hmaps (Ico_subset_Icc_self ht))).trans_eq (by rw [hnorm])) (norm_nonneg h)
    rw [sub_apply] at hop
    linarith
  have key := image_le_of_deriv_right_le_deriv_boundary
    (fun t ht ↦ (hg t ht).continuousWithinAt)
    (fun t ht ↦ (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (by simp) (fun t _ ↦ (hB t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hB t).hasDerivWithinAt) hbound (right_mem_Icc.2 zero_le_one)
  simpa using key

/-- **The descent lemma.** If `f` is differentiable at every point of the segment from `x` to
`x + h` and `‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖` for every `y` on that segment, then
`f (x + h) ≤ f x + fderiv ℝ f x h + L / 2 * ‖h‖ ^ 2`. -/
theorem le_add_fderiv_add_of_lipschitz
    (hf : ∀ y ∈ segment ℝ x (x + h), DifferentiableAt ℝ f y)
    (hL : ∀ y ∈ segment ℝ x (x + h), ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ L * ‖y - x‖) :
    f (x + h) ≤ f x + fderiv ℝ f x h + L / 2 * ‖h‖ ^ 2 :=
  le_add_apply_add_of_norm_sub_le (fun y hy ↦ (hf y hy).hasFDerivAt.hasFDerivWithinAt) hL

end Descent

section PolynomialMajorant

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mean value inequality with a derivative bound growing like a power of the distance to the
left endpoint: if `‖f' r‖ ≤ C (r - t) ^ n` on `[t, u)`, then
`‖f u - f t‖ ≤ C (u - t) ^ (n + 1) / (n + 1)`. -/
theorem norm_image_sub_le_of_norm_deriv_le_mul_pow_sub_left {f f' : ℝ → E} {t u C : ℝ} {n : ℕ}
    (htu : t ≤ u) (hf : ∀ r ∈ Icc t u, HasDerivWithinAt f (f' r) (Icc t u) r)
    (hbound : ∀ r ∈ Ico t u, ‖f' r‖ ≤ C * (r - t) ^ n) :
    ‖f u - f t‖ ≤ C * (u - t) ^ (n + 1) / (n + 1) := by
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun r ↦ f r - f t)
    (B := fun r ↦ C * (r - t) ^ (n + 1) / (n + 1))
    (fun r hr ↦ ((hf r hr).sub_const (f t)).continuousWithinAt)
    (fun r hr ↦ ((hf r (Ico_subset_Icc_self hr)).sub_const (f t)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hr)) (by simp) (fun r ↦ ?_) hbound (right_mem_Icc.2 htu)
  convert ((((hasDerivAt_id' r).sub_const t).fun_pow (n + 1)).const_mul C).div_const
    ((n : ℝ) + 1) using 1
  push_cast
  field_simp

/-- The mean value inequality with a derivative bound growing like a power of the distance to the
right endpoint: if `‖f' r‖ ≤ C (u - r) ^ n` on `[t, u)`, then
`‖f u - f t‖ ≤ C (u - t) ^ (n + 1) / (n + 1)`. -/
theorem norm_image_sub_le_of_norm_deriv_le_mul_pow_sub_right {f f' : ℝ → E} {t u C : ℝ} {n : ℕ}
    (htu : t ≤ u) (hf : ∀ r ∈ Icc t u, HasDerivWithinAt f (f' r) (Icc t u) r)
    (hbound : ∀ r ∈ Ico t u, ‖f' r‖ ≤ C * (u - r) ^ n) :
    ‖f u - f t‖ ≤ C * (u - t) ^ (n + 1) / (n + 1) := by
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun r ↦ f r - f t)
    (fun r hr ↦ ((hf r hr).sub_const (f t)).continuousWithinAt)
    (fun r hr ↦ ((hf r (Ico_subset_Icc_self hr)).sub_const (f t)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hr))
    (B := fun r ↦ C * ((u - t) ^ (n + 1) - (u - r) ^ (n + 1)) / (n + 1)) (by simp)
    (fun r ↦ ?_) hbound (right_mem_Icc.2 htu)
  · simpa using key
  · convert (((((hasDerivAt_id' r).const_sub u).fun_pow (n + 1)).const_sub
      ((u - t) ^ (n + 1))).const_mul C).div_const ((n : ℝ) + 1) using 1
    push_cast
    field_simp

/-- The mean value inequality with a derivative bound growing like a power of the distance to a
base point `s`: if `‖f' r‖ ≤ C |r - s| ^ n` on `[a, b]`, then for `s`, `u` in `[a, b]`, in either
order, `‖f u - f s‖ ≤ C |u - s| ^ (n + 1) / (n + 1)`. -/
theorem norm_image_sub_le_of_norm_deriv_le_mul_abs_sub_pow {f f' : ℝ → E} {a b s u C : ℝ}
    {n : ℕ}
    (hf : ∀ r ∈ Icc a b, HasDerivWithinAt f (f' r) (Icc a b) r)
    (hbound : ∀ r ∈ Icc a b, ‖f' r‖ ≤ C * |r - s| ^ n) (hs : s ∈ Icc a b) (hu : u ∈ Icc a b) :
    ‖f u - f s‖ ≤ C * |u - s| ^ (n + 1) / (n + 1) := by
  rcases le_total s u with hsu | hus
  · have hsub : Icc s u ⊆ Icc a b := Icc_subset_Icc hs.1 hu.2
    rw [abs_of_nonneg (sub_nonneg.2 hsu)]
    refine norm_image_sub_le_of_norm_deriv_le_mul_pow_sub_left hsu
      (fun r hr ↦ (hf r (hsub hr)).mono hsub) fun r hr ↦ ?_
    simpa [abs_of_nonneg (sub_nonneg.2 hr.1)] using hbound r (hsub (Ico_subset_Icc_self hr))
  · have hsub : Icc u s ⊆ Icc a b := Icc_subset_Icc hu.1 hs.2
    rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 hus), neg_sub]
    refine norm_image_sub_le_of_norm_deriv_le_mul_pow_sub_right hus
      (fun r hr ↦ (hf r (hsub hr)).mono hsub) fun r hr ↦ ?_
    simpa [abs_of_nonpos (sub_nonpos.2 hr.2.le)] using hbound r (hsub (Ico_subset_Icc_self hr))

end PolynomialMajorant

end TauCeti
