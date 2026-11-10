/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Path
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.Calculus.ContDiff.Approximation
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
import TauCeti.Analysis.Contour.NullHomologous
import TauCeti.Analysis.Contour.Winding.Proximity
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Homotopy invariance of the winding number

Two piecewise-`C¹` paths with the same endpoints, joined by an arbitrary continuous fixed-endpoint
homotopy through `ℂ \ {w}`, have the same winding number about `w`. The proof regularizes finitely
many horizontal slices of the homotopy by endpoint-preserving smooth approximations, then chains
the resulting smooth paths with proximity invariance of the winding number.

For closed curves the base point may move. A family of closed piecewise-`C¹` curves avoiding `w`,
depending jointly continuously on a parameter in a preconnected set, has a constant winding number
about `w`: nearby curves of the family are uniformly closer to each other than to `w`, so the
winding number is locally constant in the parameter. Shrinking concentric circles gives the
annulus and disc forms: if a `C¹` map `f` does not take the value `w` on a closed annulus, the
images of its two boundary circles wind equally often around `w`, and if `f` does not take the
value `w` on a closed disc, the image of the boundary circle does not wind around `w` at all.

## Main results

* `windingNumber_eq_of_pathHomotopy` proves homotopy invariance without any
  regularity hypothesis on the homotopy.
* `curveIntegral_inv_sub_smul_id_eq_of_pathHomotopy` is its curve-integral form: such a homotopy
  preserves the integral of the Cauchy-kernel `1`-form.
* `isNullHomologous_iff_of_pathHomotopy` transfers null-homology across a homotopy in the ambient
  set.
* `windingNumber_eq_of_continuousOn_uncurry` proves invariance along a continuous family of
  closed curves, with a moving base point.
* `windingNumber_comp_circleMap_eq_of_annulus` and `windingNumber_comp_circleMap_eq_zero` are the
  annulus and disc forms for the image of a circle under a `C¹` map.

## Provenance

The regularization step is `ContinuousMap.exists_contDiff_eq_endpoints_dist_lt`, which reuses
Mathlib's `bernsteinApproximation_uniform`. No formal source is vendored. Homotopy invariance of
the classical winding number is standard complex analysis; see L. Ahlfors, *Complex Analysis*,
Ch. 4.
-/

public section

noncomputable section

open scoped unitInterval Topology
open MeasureTheory Set

namespace TauCeti.Contour

/-- A continuous path homotopy avoiding `w` stays a uniformly positive distance from `w`, since
its domain is the compact unit square. -/
private theorem exists_pathHomotopy_dist_lower_bound {x y w : ℂ} {p q : Path x y}
    (φ : p.Homotopy q) (havoid : ∀ st : I × I, φ st ≠ w) :
    ∃ ρ > 0, ∀ st : I × I, ρ ≤ dist (φ st) w := by
  have hcompact : IsCompact (Set.range φ) := isCompact_range φ.toHomotopy.continuous
  have hnonempty : (Set.range φ).Nonempty := Set.range_nonempty φ
  have hw : w ∉ Set.range φ := by
    rintro ⟨st, hst⟩
    exact havoid st hst
  refine ⟨Metric.infDist w (Set.range φ),
    (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hw, fun st => ?_⟩
  simpa [dist_comm] using Metric.infDist_le_dist_of_mem (x := w) (Set.mem_range_self st)

/-- Uniform continuity lets a path homotopy be divided into finitely many nearby horizontal
slices. The stages are the equally spaced points `bernstein.z k` for a mesh size `N` supplied by
uniform continuity; the degree of the approximants regularizing each slice is chosen separately. -/
private theorem exists_nat_dist_pathHomotopy_stage_lt {x y : ℂ} {p q : Path x y}
    (φ : p.Homotopy q) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ k : Fin N, ∀ t : I,
      dist (φ (bernstein.z k.succ, t)) (φ (bernstein.z k.castSucc, t)) < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous φ.toHomotopy.continuous) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hmesh : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hN
  refine ⟨N, Nat.ne_of_gt (by exact_mod_cast hNpos), fun k t => hclose ?_⟩
  simp only [Prod.dist_eq, dist_self]
  have hsub : (((k : ℕ) + 1 : ℕ) : ℝ) / N - ((k : ℕ) : ℝ) / N = 1 / N := by
    push_cast
    ring
  simp only [bernstein.z, Subtype.dist_eq, Real.dist_eq, Fin.val_succ, Fin.val_castSucc]
  rw [hsub, abs_of_pos (by positivity), max_eq_left (by positivity)]
  exact hmesh

/-- The unit-interval form of the leash lemma used to chain the approximants below: two
piecewise-`C¹` curves with common endpoints that stay within `c` of one another, one of which
stays at distance at least `c` from `w`, have the same winding number about `w`. -/
private theorem windingNumber_eq_of_dist_lt_of_le_dist {γ δ : ℝ → ℂ} {w : ℂ} {c : ℝ}
    (hγ : IsPiecewiseC1On γ 0 1) (hδ : IsPiecewiseC1On δ 0 1) (h₀ : γ 0 = δ 0) (h₁ : γ 1 = δ 1)
    (hclose : ∀ t : I, dist (γ t) (δ t) < c) (hfar : ∀ t : I, c ≤ dist (δ t) w) :
    windingNumber γ 0 1 w = windingNumber δ 0 1 w := by
  refine hδ.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints hγ h₀.symm h₁.symm fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hcoe : ((⟨t, ht⟩ : I) : ℝ) = t := rfl
  have hc := hclose ⟨t, ht⟩
  have hf := hfar ⟨t, ht⟩
  rw [hcoe] at hc hf
  exact hc.trans_le hf

/-- Two piecewise-`C¹` curves with common endpoints that both stay within `ρ / 5` of curves
`f₁` and `f₂` which are `ρ / 5` apart, with `γ₂` at distance more than `4 * ρ / 5` from `w`,
have the same winding number about `w`: the adjacent step of the chain of approximants below. -/
private theorem windingNumber_eq_of_dist_lt_of_dist_lt {γ₁ γ₂ : ℝ → ℂ} {f₁ f₂ : I → ℂ} {w : ℂ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hγ₁ : IsPiecewiseC1On γ₁ 0 1) (hγ₂ : IsPiecewiseC1On γ₂ 0 1)
    (h₀ : γ₁ 0 = γ₂ 0) (h₁ : γ₁ 1 = γ₂ 1) (hclose₁ : ∀ t : I, dist (γ₁ t) (f₁ t) < ρ / 5)
    (hclose₂ : ∀ t : I, dist (γ₂ t) (f₂ t) < ρ / 5) (hf : ∀ t : I, dist (f₁ t) (f₂ t) < ρ / 5)
    (hfar : ∀ t : I, 4 * ρ / 5 < dist (γ₂ t) w) :
    windingNumber γ₁ 0 1 w = windingNumber γ₂ 0 1 w := by
  refine windingNumber_eq_of_dist_lt_of_le_dist (c := 3 * ρ / 5) hγ₁ hγ₂ h₀ h₁ (fun t => ?_)
    (fun t => ?_)
  · exact (dist_triangle4 (γ₁ t) (f₁ t) (f₂ t) (γ₂ t)).trans_lt
      (by linarith [hclose₁ t, hf t, hclose₂ t, dist_comm (f₂ t) (γ₂ t)])
  · linarith [hfar t, hρ]

/-- A piecewise-`C¹` curve `γ` with the endpoints of a path `r` that stays within `ρ / 5` of `r`,
where `r` stays at distance at least `ρ` from `w`, has the same winding number about `w` as
`r.extend`: the endpoint step of the chain of approximants below. -/
private theorem windingNumber_eq_extend_of_dist_lt {x y w : ℂ} {r : Path x y} {γ : ℝ → ℂ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hγ : IsPiecewiseC1On γ 0 1) (hr : IsPiecewiseC1On r.extend 0 1)
    (h₀ : γ 0 = x) (h₁ : γ 1 = y) (hclose : ∀ t : I, dist (γ t) (r t) < ρ / 5)
    (hfar : ∀ t : I, ρ ≤ dist (r t) w) :
    windingNumber γ 0 1 w = windingNumber r.extend 0 1 w := by
  refine windingNumber_eq_of_dist_lt_of_le_dist (c := ρ / 5) hγ hr
    (by rw [Path.extend_zero, h₀]) (by rw [Path.extend_one, h₁]) (fun t => ?_) (fun t => ?_)
  · rw [Path.extend_extends']
    exact hclose t
  · rw [Path.extend_extends']
    linarith [hfar t, hρ]

/-- **Homotopy invariance of the winding number off the curve.** Two piecewise-`C¹` paths with the
same endpoints, joined through `ℂ \ {w}` by an arbitrary continuous path homotopy, have the same
winding number about `w`. No differentiability of the homotopy is required. -/
theorem windingNumber_eq_of_pathHomotopy {x y w : ℂ} {p q : Path x y} (φ : p.Homotopy q)
    (hp : IsPiecewiseC1On p.extend 0 1) (hq : IsPiecewiseC1On q.extend 0 1)
    (havoid : ∀ st : I × I, φ st ≠ w) :
    windingNumber p.extend 0 1 w = windingNumber q.extend 0 1 w := by
  obtain ⟨ρ, hρ, hρle⟩ := exists_pathHomotopy_dist_lower_bound φ havoid
  obtain ⟨N, hN, hstage⟩ := exists_nat_dist_pathHomotopy_stage_lt φ (div_pos hρ (by norm_num :
    (0 : ℝ) < 5))
  let slice : Fin (N + 1) → C(I, ℂ) := fun k => (φ.eval (bernstein.z k)).toContinuousMap
  choose γ hγ using fun k : Fin (N + 1) =>
    (slice k).exists_contDiff_eq_endpoints_dist_lt (ε := ρ / 5) (div_pos hρ (by norm_num))
  have hγpw (k : Fin (N + 1)) : IsPiecewiseC1On (γ k) 0 1 :=
    IsPiecewiseC1On.of_contDiffOn ((hγ k).1.contDiffOn.of_le (by norm_num))
  have hγclose (k : Fin (N + 1)) (t : I) : dist (γ k t) (φ (bernstein.z k, t)) < ρ / 5 := by
    simpa only [slice, Path.coe_toContinuousMap, Path.Homotopy.eval_apply,
      ContinuousMap.Homotopy.curry_apply, ContinuousMap.HomotopyWith.coe_toHomotopy] using
      (hγ k).2.2.2 t
  have hγzero (k : Fin (N + 1)) : γ k 0 = x := by
    calc
      γ k 0 = slice k 0 := (hγ k).2.1
      _ = x := by simp [slice]
  have hγone (k : Fin (N + 1)) : γ k 1 = y := by
    calc
      γ k 1 = slice k 1 := (hγ k).2.2.1
      _ = y := by simp [slice]
  have hγdist (k : Fin (N + 1)) (t : I) : 4 * ρ / 5 < dist (γ k t) w := by
    have htriangle := dist_triangle (φ (bernstein.z k, t)) (γ k t) w
    have hlower := hρle (bernstein.z k, t)
    have hclose := hγclose k t
    rw [dist_comm (φ (bernstein.z k, t)) (γ k t)] at htriangle
    linarith
  -- Consecutive approximants are close enough for the leash lemma.
  have hadjacent (k : Fin N) : windingNumber (γ k.succ) 0 1 w =
      windingNumber (γ k.castSucc) 0 1 w :=
    windingNumber_eq_of_dist_lt_of_dist_lt hρ.le (hγpw k.succ) (hγpw k.castSucc)
      ((hγzero k.succ).trans (hγzero k.castSucc).symm)
      ((hγone k.succ).trans (hγone k.castSucc).symm) (hγclose k.succ) (hγclose k.castSucc)
      (hstage k) (hγdist k.castSucc)
  -- Chain the finitely many approximants from homotopy time `0` to time `1`.
  have hchain (k : Fin (N + 1)) : windingNumber (γ k) 0 1 w = windingNumber (γ 0) 0 1 w := by
    induction k using Fin.induction with
    | zero => rfl
    | succ k ih => exact (hadjacent k).trans ih
  -- The first and last approximants are close to the original endpoint paths.
  have hstart : windingNumber (γ 0) 0 1 w = windingNumber p.extend 0 1 w :=
    windingNumber_eq_extend_of_dist_lt hρ.le (hγpw 0) hp (hγzero 0) (hγone 0)
      (fun t => by simpa using hγclose 0 t) fun t => by simpa using hρle (0, t)
  have hend : windingNumber (γ (Fin.last N)) 0 1 w = windingNumber q.extend 0 1 w :=
    windingNumber_eq_extend_of_dist_lt hρ.le (hγpw (Fin.last N)) hq (hγzero _) (hγone _)
      (fun t => by simpa [bernstein.z_last hN] using hγclose (Fin.last N) t)
      fun t => by simpa using hρle (1, t)
  exact hstart.symm.trans ((hchain (Fin.last N)).symm.trans hend)

/-- **A path homotopy avoiding `w` preserves the curve integral of the Cauchy kernel.** Two
piecewise-`C¹` paths with the same endpoints, joined by an arbitrary continuous homotopy through
`ℂ \ {w}`, have equal integrals of the `1`-form `z ↦ (z - w)⁻¹ dz`. This is the curve-integral
restatement of `windingNumber_eq_of_pathHomotopy`. -/
theorem curveIntegral_inv_sub_smul_id_eq_of_pathHomotopy {x y w : ℂ} {p q : Path x y}
    (φ : p.Homotopy q) (hp : IsPiecewiseC1On p.extend 0 1) (hq : IsPiecewiseC1On q.extend 0 1)
    (haway : ∀ z ∈ Set.range φ, z ≠ w) :
    (∫ᶜ z in p, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ) =
      ∫ᶜ z in q, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hwind := windingNumber_eq_of_pathHomotopy φ hp hq fun st => haway _ ⟨st, rfl⟩
  rw [hp.absolutelyContinuousOnInterval.windingNumber_eq_two_pi_I_inv_mul_curveIntegral
      (fun t ↦ haway _ ⟨(0, t), by simp⟩),
    hq.absolutelyContinuousOnInterval.windingNumber_eq_two_pi_I_inv_mul_curveIntegral
      (fun t ↦ haway _ ⟨(1, t), by simp⟩)] at hwind
  exact mul_left_cancel₀ (inv_ne_zero hne) hwind

/-- Null-homology in `Ω` is invariant under an arbitrary continuous path homotopy whose image lies
in `Ω`. The endpoint paths themselves are piecewise `C¹`; no regularity is assumed of the
intermediate paths. -/
theorem isNullHomologous_iff_of_pathHomotopy {x y : ℂ} {p q : Path x y} {Ω : Set ℂ}
    (φ : p.Homotopy q)
    (hp : IsPiecewiseC1On p.extend 0 1) (hq : IsPiecewiseC1On q.extend 0 1)
    (hφΩ : ∀ st : I × I, φ st ∈ Ω) :
    IsNullHomologous p.extend 0 1 Ω ↔ IsNullHomologous q.extend 0 1 Ω := by
  constructor
  · intro h
    exact h.congr_windingNumber fun z hz ↦
      (windingNumber_eq_of_pathHomotopy φ hp hq
        (fun st (hst : φ st = z) ↦ hz (hst ▸ hφΩ st))).symm
  · intro h
    exact h.congr_windingNumber fun z hz ↦
      windingNumber_eq_of_pathHomotopy φ hp hq
        (fun st (hst : φ st = z) ↦ hz (hst ▸ hφΩ st))

/-- **Homotopy invariance of the winding number of closed curves.** Let `H p`, for `p` in a
preconnected set `S` of parameters, be closed piecewise-`C¹` curves on the parameter interval with
endpoints `a`, `b`, depending jointly continuously on the parameter and the time, and avoiding `w`.
Then all the curves `H p`, `p ∈ S`, have the same winding number about `w`. Unlike
`windingNumber_eq_of_pathHomotopy`, the base point `H p a` may move with `p`. -/
theorem windingNumber_eq_of_continuousOn_uncurry {P : Type*} [TopologicalSpace P] {S : Set P}
    (hS : IsPreconnected S) {H : P → ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hH : ContinuousOn (Function.uncurry H) (S ×ˢ uIcc a b))
    (hpw : ∀ p ∈ S, IsPiecewiseC1On (H p) a b) (hclosed : ∀ p ∈ S, H p a = H p b)
    (havoid : ∀ p ∈ S, ∀ t ∈ uIcc a b, H p t ≠ w) {p q : P} (hp : p ∈ S) (hq : q ∈ S) :
    windingNumber (H p) a b w = windingNumber (H q) a b w := by
  -- The curves near `H q` stay closer to it than `H q` stays to `w`, so the winding number is
  -- locally constant in the parameter.
  have hloc (q : P) (hq : q ∈ S) :
      ∀ᶠ p in 𝓝[S] q, windingNumber (H p) a b w = windingNumber (H q) a b w := by
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc
      ((continuous_id.dist continuous_const).comp_continuousOn (hpw q hq).continuousOn :
        ContinuousOn (fun t ↦ dist (H q t) w) _)
    obtain ⟨v, hv, hclose⟩ := isCompact_uIcc.mem_uniformity_of_prod hH hq
      (Metric.dist_mem_uniformity (dist_pos.2 (havoid q hq t₀ ht₀)))
    filter_upwards [hv, self_mem_nhdsWithin] with p hpv hpS
    exact (hpw q hq).windingNumber_eq_of_dist_lt_dist (hpw p hpS) (hclosed q hq) (hclosed p hpS)
      fun t ht ↦ (hclose p hpv t ht).trans_le (hmin ht)
  -- A locally constant function on a preconnected space is constant.
  have := isPreconnected_iff_preconnectedSpace.1 hS
  have hconst : IsLocallyConstant fun x : S ↦ windingNumber (H x) a b w :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦
      (eventually_nhds_subtype_iff S x _).2 (hloc x x.2)
  exact hconst.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨q, hq⟩

/-- **Concentric circles through an annulus avoiding `w` wind equally often.** If `f` is `C¹` on
the closed annulus `r₁ ≤ |z - z₀| ≤ r₂`, with `0 ≤ r₁ ≤ r₂`, and does not take the value `w`
there, then the images under `f` of the two boundary circles, each traversed once from the angle
`a`, have the same winding number about `w`. -/
theorem windingNumber_comp_circleMap_eq_of_annulus {f : ℂ → ℂ} {z₀ w : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁))
    (hw : ∀ z ∈ Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁, f z ≠ w) (a : ℝ) :
    windingNumber (f ∘ circleMap z₀ r₁) a (a + 2 * Real.pi) w =
      windingNumber (f ∘ circleMap z₀ r₂) a (a + 2 * Real.pi) w := by
  have hmaps {s : ℝ} (hs : s ∈ Icc r₁ r₂) (θ : ℝ) :
      circleMap z₀ s θ ∈ Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁ := by
    have hθ := Metric.mem_sphere.1 (circleMap_mem_sphere z₀ (hr₁.trans hs.1) θ)
    simp only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, hθ, not_lt]
    exact ⟨hs.2, hs.1⟩
  refine windingNumber_eq_of_continuousOn_uncurry (H := fun s θ ↦ f (circleMap z₀ s θ))
    isPreconnected_Icc ?_ (fun s hs ↦ ?_) (fun s _ ↦ ?_) (fun s hs θ _ ↦ hw _ (hmaps hs θ))
    (left_mem_Icc.2 hr) (right_mem_Icc.2 hr)
  · refine hf.continuousOn.comp (Continuous.continuousOn (by unfold circleMap; fun_prop))
      fun x hx ↦ hmaps hx.1 x.2
  · exact IsPiecewiseC1On.of_contDiffOn
      (hf.comp (contDiff_circleMap z₀ s).contDiffOn fun θ _ ↦ hmaps hs θ)
  · exact congrArg f (periodic_circleMap z₀ s a).symm

/-- **The image of the boundary of a disc missing `w` does not wind around `w`.** If `f` is `C¹`
on the closed disc of radius `r ≥ 0` about `z₀` and does not take the value `w` there, then the
image under `f` of the boundary circle, traversed once from the angle `a`, has winding number zero
about `w`. -/
theorem windingNumber_comp_circleMap_eq_zero {f : ℂ → ℂ} {z₀ w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall z₀ r))
    (hw : ∀ z ∈ Metric.closedBall z₀ r, f z ≠ w) (a : ℝ) :
    windingNumber (f ∘ circleMap z₀ r) a (a + 2 * Real.pi) w = 0 := by
  rw [← sdiff_empty (s := Metric.closedBall z₀ r), ← Metric.ball_zero (x := z₀)] at hf hw
  rw [← windingNumber_comp_circleMap_eq_of_annulus le_rfl hr hf hw, circleMap_zero_radius,
    Function.comp_const]
  exact windingNumber_const _ _ _ _

end TauCeti.Contour

end
