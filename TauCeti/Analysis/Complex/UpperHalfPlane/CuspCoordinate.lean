/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UnitDisc.PuncturedManifold
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# The local coordinate at a cusp

For a positive width `w`, the usual local coordinate
`z ↦ exp (2 π i z / w)` maps the upper half-plane onto the punctured unit disc. Its fibres
are exactly the orbits of the translation subgroup `w ℤ`. Consequently it identifies the orbit
quotient of the upper half-plane by these translations with the punctured unit disc.

A periodic function need only be holomorphic above some height for boundedness to make its
q-extension analytic at zero. This permits applying the same coordinate to functions with
interior poles. Likewise periodicity is only needed above that height, which permits applying it
to functions defined only on a horodisc, such as local sections near a cusp.

The construction reuses Mathlib's `Function.Periodic.qParam`; in particular, the normalization
of `2 π i / w` agrees with the local parameter used for modular-form q-expansions. The analytic
extension criterion uses `Function.Periodic.differentiableAt_cuspFunction_zero` and Mathlib's
removable singularity theorem.

## Main declarations

* `TauCeti.UpperHalfPlane.qParamPuncturedUnitDisc`: the width-`w` q-parameter with its range
  bundled.
* `TauCeti.UpperHalfPlane.invQParamUpperHalfPlane`: a chosen logarithmic lift/right inverse,
  valued in the upper half-plane.
* `TauCeti.UpperHalfPlane.qParamPuncturedUnitDisc_eq_iff`: two lifts have the same q-parameter
  exactly when they differ by an integral multiple of the width.
* `TauCeti.UpperHalfPlane.cuspTranslationQuotientHomeomorph`: the resulting homeomorphism from
  the translation-orbit quotient to the punctured unit disc.
* `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_zero_of_eventually_mdifferentiableAt`: bounded
  functions holomorphic sufficiently high have a removable q-singularity.
* `TauCeti.UpperHalfPlane.cuspFunction_qParam_of_lt_im`,
  `TauCeti.UpperHalfPlane.eqOn_cuspFunction_of_lt_im` and
  `TauCeti.UpperHalfPlane.differentiableOn_cuspFunction_of_lt_im`: a function periodic only above
  a height `A ≥ 0`, as on a horodisc, has a q-extension which recovers it there and depends only
  on its values there; if it is moreover holomorphic above that height and bounded at `i∞`, the
  q-extension is holomorphic on the disc of radius `exp (-2 * π * A / w)`, including at `q = 0`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Complex Filter Function MulAction UpperHalfPlane
open scoped Complex.UnitDisc Manifold Real Topology

namespace TauCeti.UpperHalfPlane

local notation "𝔢" => Function.Periodic.qParam

/-- A periodic function holomorphic at all sufficiently large heights and bounded at imaginary
infinity has an analytic q-extension at zero. Interior poles below that height are allowed. -/
theorem analyticAt_cuspFunction_zero_of_eventually_mdifferentiableAt {f : ℍ → ℂ} {w : ℝ}
    (hw : 0 < w) (hper : Periodic (f ∘ ofComplex) w)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z)
    (hbounded : IsBoundedAtImInfty f) :
    AnalyticAt ℂ (Function.Periodic.cuspFunction w (f ∘ ofComplex)) 0 := by
  have hdiff : ∀ᶠ z in Filter.comap Complex.im Filter.atTop,
      DifferentiableAt ℂ (f ∘ ofComplex) z := by
    filter_upwards [tendsto_comap_im_ofComplex.eventually hhol,
      preimage_mem_comap (Ioi_mem_atTop 0)] with z hz him
    simpa only [ofComplex_apply_of_im_pos him] using
      _root_.UpperHalfPlane.mdifferentiableAt_iff.mp hz
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hw hper hdiff)
    (Function.Periodic.differentiableAt_cuspFunction_zero hw hper hdiff
      (hbounded.comp_tendsto tendsto_comap_im_ofComplex)).continuousAt

/-- A function periodic above a height `A` is recovered from its q-extension at every point
above that height. -/
theorem cuspFunction_qParam_of_lt_im {f : ℍ → ℂ} {w A : ℝ} (hw : 0 < w)
    (hper : ∀ z : ℍ, A < z.im → f (w +ᵥ z) = f z) {z : ℍ} (hz : A < z.im) :
    Function.Periodic.cuspFunction w (f ∘ ofComplex) (𝔢 w z) = f z := by
  -- translates of `z` stay above height `A`, so periodicity applies along the whole orbit
  have hzpow (n : ℤ) : f (((n : ℝ) * w) +ᵥ z) = f z := by
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have h := hper ((((n : ℤ) : ℝ) * w) +ᵥ z) (by rwa [vadd_im])
      rw [vadd_vadd, ih] at h
      rw [← h]
      congr 2
      push_cast
      ring
    | pred n ih =>
      have h := hper ((((-(n : ℤ) - 1 : ℤ) : ℝ) * w) +ᵥ z) (by rwa [vadd_im])
      rw [vadd_vadd] at h
      rw [← ih, ← h]
      congr 2
      push_cast
      ring
  obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period hw.ne' (z : ℂ)
  have him : 0 < ((z : ℂ) + m * w).im := by simpa using z.im_pos
  rw [Function.Periodic.cuspFunction_eq_of_ne_zero _ _ (Function.Periodic.qParam_ne_zero _),
    comp_apply, hm, ofComplex_apply_of_im_pos him, ← hzpow m]
  congr 1
  ext
  simp [add_comm]

/-- Two functions which agree above a height `A` have q-extensions which agree on the disc of
the corresponding radius `exp (-2 * π * A / w)`, including at `q = 0`. -/
theorem eqOn_cuspFunction_of_lt_im {f g : ℍ → ℂ} {w A : ℝ} (hw : 0 < w)
    (hfg : ∀ z : ℍ, A < z.im → f z = g z) :
    Set.EqOn (Function.Periodic.cuspFunction w (f ∘ ofComplex))
      (Function.Periodic.cuspFunction w (g ∘ ofComplex))
      (Metric.ball 0 (Real.exp (-2 * Real.pi * A / w))) := by
  rcases lt_or_ge A 0 with hA | hA
  · -- every point of `ℍ` lies above height `A`, so `f = g`
    obtain rfl : f = g := funext fun z ↦ hfg z (hA.trans z.im_pos)
    exact fun _ _ ↦ rfl
  have hne {q : ℂ} (hq : q ≠ 0) (hqA : ‖q‖ < Real.exp (-2 * Real.pi * A / w)) :
      Function.Periodic.cuspFunction w (f ∘ ofComplex) q =
        Function.Periodic.cuspFunction w (g ∘ ofComplex) q := by
    have him : A < (Function.Periodic.invQParam w q).im := by
      rwa [← Function.Periodic.norm_qParam_lt_iff hw,
        Function.Periodic.qParam_right_inv hw.ne' hq]
    rw [Function.Periodic.cuspFunction_eq_of_ne_zero _ _ hq,
      Function.Periodic.cuspFunction_eq_of_ne_zero _ _ hq, comp_apply, comp_apply,
      ofComplex_apply_of_im_pos (hA.trans_lt him)]
    exact hfg _ him
  intro q hq
  rw [Metric.mem_ball, dist_zero_right] at hq
  rcases ne_or_eq q 0 with hq0 | rfl
  · exact hne hq0 hq
  -- at `q = 0` both values are limits along the punctured disc, where the functions agree
  have heq : Function.Periodic.cuspFunction w (f ∘ ofComplex) =ᶠ[𝓝[≠] 0]
      Function.Periodic.cuspFunction w (g ∘ ofComplex) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ)
      (Real.exp_pos (-2 * Real.pi * A / w)))] with q hq0 hqA
    exact hne hq0 (mem_ball_zero_iff.mp hqA)
  rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne,
    Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  exact congrArg lim (Filter.map_congr heq)

/-- **The q-extension of a function periodic and holomorphic above a height.** If `f` is periodic
of period `w > 0` and holomorphic above a height `A ≥ 0`, and bounded at `i∞`, then its q-extension
is holomorphic on the disc of radius `exp (-2 * π * A / w)`, including at `q = 0`. -/
theorem differentiableOn_cuspFunction_of_lt_im {f : ℍ → ℂ} {w A : ℝ} (hw : 0 < w) (hA : 0 ≤ A)
    (hper : ∀ z : ℍ, A < z.im → f (w +ᵥ z) = f z)
    (hhol : ∀ z : ℍ, A < z.im → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z)
    (hbounded : IsBoundedAtImInfty f) :
    DifferentiableOn ℂ (Function.Periodic.cuspFunction w (f ∘ ofComplex))
      (Metric.ball 0 (Real.exp (-2 * Real.pi * A / w))) := by
  -- cut `f` off below height `A`: the result is periodic everywhere and has the same q-extension
  set g : ℍ → ℂ := fun z ↦ if A < z.im then f z else 0 with hg
  have hfg (z : ℍ) (hz : A < z.im) : f z = g z := by simp [hg, hz]
  have hgper : Periodic (g ∘ ofComplex) w := UpperHalfPlane.periodic_comp_ofComplex fun z ↦ by
    by_cases hz : A < z.im
    · rw [← hfg _ (by rwa [vadd_im]), ← hfg _ hz, hper _ hz]
    · simp [hg, vadd_im, hz]
  have hgeq {z : ℍ} (hz : A < z.im) : g =ᶠ[𝓝 z] f := by
    filter_upwards [(isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hz]
      with z' hz'
    exact (hfg z' hz').symm
  have hghol {z : ℍ} (hz : A < z.im) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z :=
    (hhol z hz).congr_of_eventuallyEq (hgeq hz)
  refine DifferentiableOn.congr (fun q hq ↦ ?_) (eqOn_cuspFunction_of_lt_im hw hfg)
  rw [Metric.mem_ball, dist_zero_right] at hq
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases ne_or_eq q 0 with hq0 | rfl
  · have him : A < (Function.Periodic.invQParam w q).im := by
      rwa [← Function.Periodic.norm_qParam_lt_iff hw,
        Function.Periodic.qParam_right_inv hw.ne' hq0]
    have hpos : 0 < (Function.Periodic.invQParam w q).im := hA.trans_lt him
    rw [← Function.Periodic.qParam_right_inv hw.ne' hq0]
    refine Function.Periodic.differentiableAt_cuspFunction hw.ne' hgper ?_
    have h := _root_.UpperHalfPlane.mdifferentiableAt_iff.mp
      (hghol (z := ⟨_, hpos⟩) him)
    simpa using h
  · have hev : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z :=
      (atImInfty_mem _).mpr ⟨A + 1, fun z hz ↦ hghol (by linarith)⟩
    have hgbdd : IsBoundedAtImInfty g := by
      refine Asymptotics.IsBigO.congr' hbounded ?_ EventuallyEq.rfl
      exact (atImInfty_mem _).mpr ⟨A + 1, fun z hz ↦ hfg z (by linarith)⟩
    exact (analyticAt_cuspFunction_zero_of_eventually_mdifferentiableAt hw hgper hev
      hgbdd).differentiableAt

/-- The q-parameter of positive width, regarded as a map from the upper half-plane to the
punctured unit disc. -/
def qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) (z : ℍ) : {q : 𝔻 // q ≠ 0} :=
  ⟨Complex.UnitDisc.mk (𝔢 w z) (Function.Periodic.norm_qParam_lt_one hw z.im_pos),
    fun h ↦ Function.Periodic.qParam_ne_zero (h := w) z <| by
      simpa using congrArg ((↑) : 𝔻 → ℂ) h⟩

@[simp]
theorem coe_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) (z : ℍ) :
    (((qParamPuncturedUnitDisc w hw z : {q : 𝔻 // q ≠ 0}) : 𝔻) : ℂ) = 𝔢 w z :=
  (rfl)

/-- The logarithmic lift of a point of the punctured unit disc to the upper half-plane. -/
def invQParamUpperHalfPlane (w : ℝ) (hw : 0 < w) (q : {q : 𝔻 // q ≠ 0}) : ℍ :=
  ⟨Function.Periodic.invQParam w q,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one hw q.1.norm_lt_one <|
      fun h ↦ q.2 (Complex.UnitDisc.coe_injective h)⟩

@[simp]
theorem coe_invQParamUpperHalfPlane (w : ℝ) (hw : 0 < w) (q : {q : 𝔻 // q ≠ 0}) :
    (invQParamUpperHalfPlane w hw q : ℂ) = Function.Periodic.invQParam w q :=
  (rfl)

@[simp]
theorem qParamPuncturedUnitDisc_invQParamUpperHalfPlane (w : ℝ) (hw : 0 < w)
    (q : {q : 𝔻 // q ≠ 0}) :
    qParamPuncturedUnitDisc w hw (invQParamUpperHalfPlane w hw q) = q := by
  apply Subtype.ext
  apply Complex.UnitDisc.coe_injective
  rw [coe_qParamPuncturedUnitDisc, coe_invQParamUpperHalfPlane]
  exact Function.Periodic.qParam_right_inv hw.ne' fun h ↦
    q.2 (Complex.UnitDisc.coe_injective h)

/-- Every nonzero point of the unit disc has a logarithmic lift to the upper half-plane. -/
theorem qParamPuncturedUnitDisc_surjective (w : ℝ) (hw : 0 < w) :
    Function.Surjective (qParamPuncturedUnitDisc w hw) := fun q ↦
  ⟨invQParamUpperHalfPlane w hw q, qParamPuncturedUnitDisc_invQParamUpperHalfPlane w hw q⟩

private theorem continuous_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    Continuous (qParamPuncturedUnitDisc w hw) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact ((Function.Periodic.continuous_qParam (h := w)).comp continuous_coe).congr
    (fun z ↦ (coe_qParamPuncturedUnitDisc w hw z).symm)

/-- The q-parameter is holomorphic as a map into the punctured unit disc. -/
theorem mdifferentiable_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qParamPuncturedUnitDisc w hw) := by
  have h : MDiff (fun z : ℍ ↦ 𝔢 w z) :=
    Function.Periodic.differentiable_qParam.mdifferentiable.comp
    UpperHalfPlane.mdifferentiable_coe
  intro z
  apply mdifferentiableAt_iff_target.mpr
  constructor
  · exact (continuous_qParamPuncturedUnitDisc w hw).continuousAt
  · simpa only [TauCeti.Complex.UnitDisc.extChartAt_coe_punctured,
      Function.comp_def, coe_qParamPuncturedUnitDisc] using h z

/-- A horodisc is the inverse image of the punctured disc of the corresponding radius. -/
theorem norm_qParamPuncturedUnitDisc_lt_iff (w : ℝ) (hw : 0 < w) (A : ℝ) (z : ℍ) :
    ‖((qParamPuncturedUnitDisc w hw z : 𝔻) : ℂ)‖ < Real.exp (-2 * Real.pi * A / w) ↔
      A < z.im := by
  rw [coe_qParamPuncturedUnitDisc]
  exact Function.Periodic.norm_qParam_lt_iff hw A z

/-- The image of a horodisc is the punctured disc of the corresponding exponential radius. -/
theorem image_qParamPuncturedUnitDisc_setOf_lt_im (w : ℝ) (hw : 0 < w) (A : ℝ) :
    qParamPuncturedUnitDisc w hw '' {z : ℍ | A < z.im} =
      {q : {q : 𝔻 // q ≠ 0} | ‖((q : 𝔻) : ℂ)‖ < Real.exp (-2 * Real.pi * A / w)} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (norm_qParamPuncturedUnitDisc_lt_iff w hw A z).mpr hz
  · intro hq
    obtain ⟨z, rfl⟩ := qParamPuncturedUnitDisc_surjective w hw q
    exact ⟨z, (norm_qParamPuncturedUnitDisc_lt_iff w hw A z).mp hq, rfl⟩

/-- The q-parameter of positive width, as a function on `ℍ`, tends to zero through nonzero
values as the height tends to infinity. -/
theorem tendsto_qParam_atImInfty {w : ℝ} (hw : 0 < w) :
    Tendsto (fun z : ℍ ↦ 𝔢 w z) atImInfty (𝓝[≠] 0) :=
  (Function.Periodic.qParam_tendsto hw).comp tendsto_coe_atImInfty

/-- The q-parameter tends to zero through nonzero values as the height tends to infinity. -/
theorem tendsto_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    Tendsto (fun z : ℍ ↦ ((qParamPuncturedUnitDisc w hw z : 𝔻) : ℂ))
      atImInfty (𝓝[≠] 0) := by
  simpa only [coe_qParamPuncturedUnitDisc] using tendsto_qParam_atImInfty hw

/-- Multiplying by the `k`th integer power of the q-parameter is bounded at `i∞` exactly when
the original function satisfies the opposing exponential bound. For positive width,
nonnegative `k` controls growth, while negative `k` controls decay. -/
theorem isBoundedAtImInfty_qParam_zpow_mul_iff (w : ℝ) (k : ℤ) {f : ℍ → ℂ} :
    (IsBoundedAtImInfty fun z ↦ Function.Periodic.qParam w z ^ k * f z) ↔
      f =O[atImInfty] fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / w) := by
  have hq (z : ℍ) : ‖Function.Periodic.qParam w z ^ k‖ =
      (Real.exp (2 * Real.pi * (k : ℝ) * z.im / w))⁻¹ := by
    rw [norm_zpow, Function.Periodic.norm_qParam]
    rw [← Real.rpow_intCast, ← Real.exp_mul]
    rw [← Real.exp_neg]
    congr 1
    simp only [UpperHalfPlane.coe_im]
    ring
  simp only [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff, norm_mul, hq,
    Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos _)]

/-- Two points of the upper half-plane have the same width-`w` q-parameter exactly when one is
an integral-width translate of the other. -/
theorem qParamPuncturedUnitDisc_eq_iff (w : ℝ) (hw : 0 < w) (z z' : ℍ) :
    qParamPuncturedUnitDisc w hw z = qParamPuncturedUnitDisc w hw z' ↔
      ∃ n : ℤ, z = ((n : ℝ) * w) +ᵥ z' := by
  constructor
  · intro h
    have hq : 𝔢 w z = 𝔢 w z' := by
      simpa only [← coe_qParamPuncturedUnitDisc w hw] using
        congrArg (fun q : {q : 𝔻 // q ≠ 0} ↦ (((q : 𝔻) : ℂ))) h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp <| by
      simpa only [Function.Periodic.qParam] using hq
    refine ⟨n, UpperHalfPlane.coe_injective ?_⟩
    rw [UpperHalfPlane.coe_vadd]
    push_cast at hn ⊢
    field_simp [hw.ne'] at hn ⊢
    linear_combination hn
  · rintro ⟨n, rfl⟩
    apply Subtype.ext
    apply Complex.UnitDisc.coe_injective
    rw [coe_qParamPuncturedUnitDisc, coe_qParamPuncturedUnitDisc,
      Function.Periodic.qParam]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨n, ?_⟩
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    field_simp [hw.ne']
    ring_nf

/-- The orbit quotient of the upper half-plane by translations through integral multiples of a
positive width. -/
abbrev CuspTranslationQuotient (w : ℝ) :=
  AddAction.orbitRel.Quotient (AddSubgroup.zmultiples w) ℍ

/-- The orbit relation for integral-width translations is exactly equality of q-parameters. -/
theorem cuspTranslationOrbitRel_iff_qParam_eq (w : ℝ) (hw : 0 < w) (z z' : ℍ) :
    AddAction.orbitRel (AddSubgroup.zmultiples w) ℍ z z' ↔
      qParamPuncturedUnitDisc w hw z = qParamPuncturedUnitDisc w hw z' := by
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff,
    qParamPuncturedUnitDisc_eq_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
    exact ⟨n, by simp [zsmul_eq_mul]⟩
  · rintro ⟨n, rfl⟩
    refine ⟨⟨(n : ℝ) * w, AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [zsmul_eq_mul]⟩⟩, ?_⟩
    rfl

private theorem isOpenMap_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    IsOpenMap (qParamPuncturedUnitDisc w hw) := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I / w) ≠ 0 :=
    div_ne_zero Complex.two_pi_I_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne')
  have hlinear : IsOpenMap (fun z : ℂ ↦ (2 * (Real.pi : ℂ) * Complex.I / w) * z) :=
    (Homeomorph.mulLeft₀ _ hc).isOpenMap
  have hq : IsOpenMap (𝔢 w) := by
    convert Complex.isOpenMap_exp.comp hlinear using 1
    ext z
    simp only [Function.comp_apply, Function.Periodic.qParam]
    ring_nf
  have hqℍ : IsOpenMap (fun z : ℍ ↦ 𝔢 w z) :=
    hq.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  exact (hqℍ.subtype_mk _).subtype_mk _

/-- The q-parameter from the upper half-plane to the punctured unit disc is an open quotient
map. -/
theorem isOpenQuotientMap_qParamPuncturedUnitDisc (w : ℝ) (hw : 0 < w) :
    IsOpenQuotientMap (qParamPuncturedUnitDisc w hw) :=
  ⟨qParamPuncturedUnitDisc_surjective w hw, continuous_qParamPuncturedUnitDisc w hw,
    isOpenMap_qParamPuncturedUnitDisc w hw⟩

/-- The q-parameter descended to the width-translation quotient. -/
def cuspTranslationQuotientMap (w : ℝ) (hw : 0 < w) :
    CuspTranslationQuotient w → {q : 𝔻 // q ≠ 0} :=
  Quotient.lift (qParamPuncturedUnitDisc w hw) fun z z' h ↦
    (cuspTranslationOrbitRel_iff_qParam_eq w hw z z').mp h

@[simp]
theorem cuspTranslationQuotientMap_mk (w : ℝ) (hw : 0 < w) (z : ℍ) :
    cuspTranslationQuotientMap w hw (Quotient.mk'' z) = qParamPuncturedUnitDisc w hw z :=
  (rfl)

/-- The descended q-parameter is a homeomorphism. -/
theorem isHomeomorph_cuspTranslationQuotientMap (w : ℝ) (hw : 0 < w) :
    IsHomeomorph (cuspTranslationQuotientMap w hw) := by
  have hcomp : (cuspTranslationQuotientMap w hw) ∘
      (Quotient.mk (AddAction.orbitRel (AddSubgroup.zmultiples w) ℍ) :
        ℍ → CuspTranslationQuotient w) = qParamPuncturedUnitDisc w hw := by
    funext z
    exact cuspTranslationQuotientMap_mk w hw z
  have hquot : Topology.IsQuotientMap (cuspTranslationQuotientMap w hw) :=
    isQuotientMap_quotient_mk'.of_comp_isQuotientMap <| hcomp.symm ▸
      (isOpenQuotientMap_qParamPuncturedUnitDisc w hw).isQuotientMap
  apply isHomeomorph_iff_isQuotientMap_injective.mpr
  refine ⟨hquot, fun x y hxy ↦ ?_⟩
  induction x, y using Quotient.inductionOn₂ with
  | _ z z' =>
    apply Quotient.sound
    exact (cuspTranslationOrbitRel_iff_qParam_eq w hw z z').mpr hxy

/-- The q-parameter identifies the width-translation quotient of the upper half-plane
homeomorphically with the punctured unit disc. -/
noncomputable def cuspTranslationQuotientHomeomorph (w : ℝ) (hw : 0 < w) :
    CuspTranslationQuotient w ≃ₜ {q : 𝔻 // q ≠ 0} :=
  (isHomeomorph_cuspTranslationQuotientMap w hw).homeomorph _

@[simp]
theorem cuspTranslationQuotientHomeomorph_mk (w : ℝ) (hw : 0 < w) (z : ℍ) :
    cuspTranslationQuotientHomeomorph w hw (Quotient.mk'' z) =
      qParamPuncturedUnitDisc w hw z := by
  rw [cuspTranslationQuotientHomeomorph]
  rfl

@[simp]
theorem cuspTranslationQuotientHomeomorph_symm_apply (w : ℝ) (hw : 0 < w)
    (q : {q : 𝔻 // q ≠ 0}) :
    (cuspTranslationQuotientHomeomorph w hw).symm q =
      Quotient.mk'' (invQParamUpperHalfPlane w hw q) := by
  apply (cuspTranslationQuotientHomeomorph w hw).injective
  simp

end TauCeti.UpperHalfPlane
