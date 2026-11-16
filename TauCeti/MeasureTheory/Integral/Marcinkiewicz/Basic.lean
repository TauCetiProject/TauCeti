/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
-- `TauCeti.MeasureTheory.Integral.Prod` is imported privately: its Tonelli exchange
-- `TauCeti.lintegral_mul_setLIntegral_eq` appears only inside the proofs below.
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Marcinkiewicz interpolation between weak type `(1,1)` and `L^∞`

A **sublinear** operator `T` that is simultaneously of **weak type `(1,1)`** and bounded on `L^∞`
is bounded on `L^p` for every `1 < p < ∞`. This is the diagonal case `p₀ = 1`, `p₁ = ∞` of the
Marcinkiewicz interpolation theorem, and it is the mechanism that turns the Hardy–Littlewood
maximal inequality into the strong `(p,p)` bounds.

## The statements proved here

The analytic engine is stated in terms of the **distribution functions** of `T f` and of `f`.
The operator-level theorem then derives its hypothesis from subadditivity, weak type `(1,1)`, and
an `L^∞` bound. For each height `t`, these hypotheses produce the single inequality

`t * ν {T f > t} ≤ d⁻¹ * A * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ∂μ`,

which says that only the part of `f` above the height `c * t` can push `T f` above `t`. That
inequality is the hypothesis of `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le`, and its
conclusion is the `L^p` bound

`∫⁻ (T f) ^ p ∂ν ≤ (p * c ^ (1 - p) / (p - 1)) * d⁻¹ * A * ∫⁻ ‖f‖ ^ p ∂μ`.

Retaining this distributional lemma keeps the analytic engine usable even when `T` is not defined
on a whole function space. The operator theorem lets `μ` and `ν` live on different spaces and makes
the dependence on the endpoint and splitting constants explicit. Its constant blows up as
`p → 1`, exactly as it must — an operator of weak type `(1,1)` need not be bounded on `L¹`.

## The proof

The layer cake formula (`TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul`) converts both
sides into integrals in the height variable `t`. The hypothesis, multiplied by `t ^ (p - 2)`,
bounds the integrand by `A * t ^ (p - 2) * ∫⁻ x in {‖f‖ > c * t}, ‖f‖ ∂μ`; Tonelli's theorem then
exchanges the `t` and `x` integrations, and for each fixed `x` the inner integral is the
elementary `∫⁻ t in (0, ‖f x‖ / c), t ^ (p - 2) = (‖f x‖ / c) ^ (p - 1) / (p - 1)`, evaluated by
`TauCeti.lintegral_indicator_ofReal_rpow_Ioi`, which reassembles into
`c ^ (1 - p) / (p - 1) * ‖f x‖ ^ p`. Convergence of that inner integral at the origin is where
`1 < p` is used, and it is why the constant carries the factor `1 / (p - 1)`. The exchange and the
inner evaluation together are `TauCeti.lintegral_mul_setLIntegral_lt` with `s = p - 2`, `q = 1`.

Tonelli's theorem needs `μ` to be s-finite, but the statement does not: both sides ignore the
part of `μ` outside `{f > 0}`, and once `∫⁻ f ^ p ∂μ` is finite that part is σ-finite, being
exhausted by the level sets `{f ≥ 1 / (n + 1)}`, each of finite measure by Chebyshev.

## Main declarations

* `TauCeti.lintegral_mul_setLIntegral_lt`: the weighted mass of the part of `f` above the height
  `c * t`, the double integral that the interpolation estimate reduces to.
* `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le`: the interpolation estimate.
* `TauCeti.mul_meas_ofReal_lt_le_setLIntegral`: the reusable truncation argument from
  subadditivity and the two endpoint bounds.
* `TauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup`: operator-level
  Marcinkiewicz interpolation.

## References

* L. Grafakos, *Classical Fourier Analysis*, Theorem 1.3.1.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, §4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → ℝ≥0∞} {u : β → ℝ≥0∞} {p q s c : ℝ} {A : ℝ≥0∞}

/-- `TauCeti.lintegral_mul_setLIntegral_lt` for a measurable `f`. -/
private theorem lintegral_mul_setLIntegral_lt_of_measurable [SFinite μ] (hf : Measurable f)
    (hq : 0 ≤ q)
    (hs : -1 < s) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
      ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
  have hs1 : (0 : ℝ) ≤ s + 1 := by linarith
  have hR : MeasurableSet {z : ℝ × α | ENNReal.ofReal (c * z.1) < f z.2} :=
    measurableSet_lt ((measurable_fst.const_mul c).ennreal_ofReal) (hf.comp measurable_snd)
  rw [lintegral_mul_setLIntegral_eq (κ := volume.restrict (Ioi (0 : ℝ)))
      (w := fun t : ℝ => ENNReal.ofReal (t ^ s))
      (R := fun t x => ENNReal.ofReal (c * t) < f x) hR (hf.pow_const q).aemeasurable
      ((measurable_id.pow measurable_const).ennreal_ofReal.aemeasurable),
    ← lintegral_const_mul _ (hf.pow_const _)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_indicator_ofReal_rpow_Ioi hs hc (f x), ENNReal.rpow_add_of_nonneg q (s + 1) hq hs1]
  ring

/-- **The weighted mass of the part of `f` above the height `c * t`.** For `-1 < s` the weight
`t ^ s` is integrable at the origin, and the double integral of the upper truncations of `f ^ q`
against it is exactly a multiple of `∫⁻ f ^ (q + (s + 1))`. -/
theorem lintegral_mul_setLIntegral_lt [SFinite μ] (hf : AEMeasurable f μ) (hq : 0 ≤ q)
    (hs : -1 < s) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
      ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
  let g := hf.mk f
  have hfg : f =ᵐ[μ] g := hf.ae_eq_mk
  have hinner : ∀ t : ℝ,
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < g x}, g x ^ q ∂μ := by
    intro t
    have hset : {x | ENNReal.ofReal (c * t) < f x} =ᵐ[μ]
        {x | ENNReal.ofReal (c * t) < g x} :=
      hfg.mono fun _ hx => by simp only [Set.mem_ofPred_eq]; rw [hx]
    rw [Measure.restrict_congr_set hset]
    exact lintegral_congr_ae (ae_restrict_of_ae (hfg.fun_comp fun z => z ^ q))
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) *
          ∫⁻ x in {x | ENNReal.ofReal (c * t) < g x}, g x ^ q ∂μ := by
      exact lintegral_congr fun t => congrArg (ENNReal.ofReal (t ^ s) * ·) (hinner t)
    _ = ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) *
        ∫⁻ x, g x ^ (q + (s + 1)) ∂μ :=
      lintegral_mul_setLIntegral_lt_of_measurable hf.measurable_mk hq hs hc
    _ = ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) *
        ∫⁻ x, f x ^ (q + (s + 1)) ∂μ := by
      exact congrArg (ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * ·)
        (lintegral_congr_ae (hfg.fun_comp fun z => z ^ (q + (s + 1)))).symm

/-- The interpolation estimate for a measurable `f` and an s-finite `μ`, which is the generality
in which Tonelli's theorem is available; both hypotheses are removed below. -/
private theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable_of_sFinite [SFinite μ]
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp : 1 < p) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} ≤
      A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hR : MeasurableSet {z : ℝ × α | ENNReal.ofReal (c * z.1) < f z.2} :=
    measurableSet_lt ((measurable_fst.const_mul c).ennreal_ofReal) (hf.comp measurable_snd)
  -- Multiplying the hypothesis by `t ^ (p - 2)` bounds the layer cake integrand.
  have hkey : ∀ t ∈ Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1)) ≤
      A * (ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ (1 : ℝ) ∂μ) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hpow : t ^ (p - 1) = t * t ^ (p - 2) := by
      rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add ht', Real.rpow_one]
    simp only [ENNReal.rpow_one]
    calc ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1))
        = ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 2)) := by
          rw [hpow, ENNReal.ofReal_mul ht'.le]; ring
      _ ≤ (A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) *
            ENNReal.ofReal (t ^ (p - 2)) := mul_le_mul_left (h t ht') _
      _ = A * (ENNReal.ofReal (t ^ (p - 2)) *
            ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) := by ring
  -- Assemble: layer cake, the pointwise bound, and the weighted truncation identity.
  rw [lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul ν hu hp0]
  calc ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), A * (ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ (1 : ℝ) ∂μ) := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hkey t ht
    _ = ENNReal.ofReal p * (A * (ENNReal.ofReal (c ^ (-(p - 2 + 1)) / (p - 2 + 1)) *
          ∫⁻ x, f x ^ ((1 : ℝ) + (p - 2 + 1)) ∂μ)) := by
        have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - 2)) *
            ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ (1 : ℝ) ∂μ :=
          ((measurable_id.pow measurable_const).ennreal_ofReal).mul
            (measurable_setLIntegral_of_measurableSet
              (R := fun t x => ENNReal.ofReal (c * t) < f x) hR (hf.pow_const _).aemeasurable)
        rw [lintegral_const_mul _ hmeas,
          lintegral_mul_setLIntegral_lt_of_measurable (q := 1) (s := p - 2) hf zero_le_one
            (by linarith) hc]
    _ = ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
        rw [show -(p - 2 + 1) = 1 - p by ring, show p - 2 + 1 = p - 1 by ring,
          show (1 : ℝ) + (p - 1) = p by ring, mul_div_assoc, ENNReal.ofReal_mul hp0.le]
        ring

/-- The interpolation estimate for a measurable `f` and an arbitrary measure `μ`.

Only the part of `μ` carried by `{f > 0}` enters either side, and once `f` has finite `L^p` norm
that part is σ-finite by `TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`. So the
s-finite case applies to `μ` restricted to `{f > 0}`, after the two degenerate cases — a vanishing
weak-type constant and an infinite right-hand side — are disposed of. -/
private theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable
    (hf : Measurable f) (hu : AEMeasurable u ν) (hp : 1 < p) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} ≤
      A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hK : (0 : ℝ) < p * c ^ (1 - p) / (p - 1) := by positivity
  rcases eq_or_ne A 0 with hA | hA
  · -- With `A = 0` the hypothesis holds over the zero measure as well, and there it already
    -- yields the bound `∫⁻ u ^ p ∂ν ≤ 0`.
    have hzero := lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable_of_sFinite
      (μ := (0 : Measure α)) (A := A) hf hu hp hc fun t ht => by simpa [hA] using h t ht
    simpa [hA] using hzero
  rcases eq_or_ne (∫⁻ x, f x ^ p ∂μ) ∞ with htop | htop
  · -- The right-hand side is infinite.
    rw [htop, ENNReal.mul_top (mul_ne_zero (ENNReal.ofReal_pos.2 hK).ne' hA)]
    exact le_top
  -- `μ` restricted to `{f > 0}` is σ-finite, so in particular s-finite.
  have hσ : SigmaFinite (μ.restrict {x | 0 < f x}) :=
    sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top hf.aemeasurable hp0 htop
  -- The truncated integrals of the hypothesis do not see the complement of `{f > 0}`.
  have hsub : ∀ t : ℝ, 0 < t → {x | ENNReal.ofReal (c * t) < f x} ⊆ {x | 0 < f x} := by
    intro t _ x hx
    exact Set.mem_ofPred.2 (lt_of_le_of_lt zero_le (Set.mem_ofPred.1 hx))
  -- Neither does `∫⁻ f ^ p`, since `f ^ p` is supported in `{f > 0}`.
  have hpow : ∫⁻ x, f x ^ p ∂μ.restrict {x | 0 < f x} = ∫⁻ x, f x ^ p ∂μ := by
    refine setLIntegral_eq_of_support_subset fun x hx => ?_
    have hx' : f x ^ p ≠ 0 := hx
    refine Set.mem_ofPred.2 (pos_iff_ne_zero.2 fun h0 => hx' ?_)
    rw [h0, ENNReal.zero_rpow_of_pos hp0]
  have hmain := lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable_of_sFinite
    (μ := μ.restrict {x | 0 < f x}) hf hu hp hc fun t ht => by
      rw [Measure.restrict_restrict_of_subset (hsub t ht)]
      exact h t ht
  rwa [hpow] at hmain

/-- **Marcinkiewicz interpolation**, the diagonal case `p₀ = 1`, `p₁ = ∞`, in distributional form.

If for every height `t > 0` the superlevel set `{u > t}` obeys the weak-type bound

`t * ν {u > t} ≤ A * ∫⁻ x in {f > c * t}, f ∂μ`

against the part of `f` above `c * t`, then for every `1 < p < ∞`

`∫⁻ u ^ p ∂ν ≤ (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ f ^ p ∂μ`.

Applied with `u = T f` for a sublinear `T`, the hypothesis is what the weak `(1,1)` and `L^∞`
endpoint bounds for `T` give after splitting `f` at the height `c * t`, and the conclusion is the
strong type `(p,p)` bound. The constant degenerates as `p → 1`, as it must. -/
theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le
    (hf : AEMeasurable f μ) (hu : AEMeasurable u ν) (hp : 1 < p) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * ν {y | ENNReal.ofReal t < u y} ≤
      A * ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ∂μ) :
    ∫⁻ y, u y ^ p ∂ν ≤
      ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * A * ∫⁻ x, f x ^ p ∂μ := by
  have hae := hf.ae_eq_mk
  have hset : ∀ a : ℝ≥0∞,
      ∫⁻ x in {x | a < f x}, f x ∂μ = ∫⁻ x in {x | a < hf.mk f x}, hf.mk f x ∂μ := by
    intro a
    have hsets : {x | a < f x} =ᵐ[μ] {x | a < hf.mk f x} := by
      filter_upwards [hae] with x hx
      exact Iff.of_eq (congrArg (fun z : ℝ≥0∞ => a < z) hx)
    rw [Measure.restrict_congr_set hsets]
    exact lintegral_congr_ae (ae_restrict_of_ae hae)
  have hrpow : (fun x => f x ^ p) =ᵐ[μ] fun x => hf.mk f x ^ p :=
    hae.mono fun x hx => congrArg (fun z : ℝ≥0∞ => z ^ p) hx
  rw [lintegral_congr_ae hrpow]
  refine lintegral_rpow_le_of_mul_meas_ofReal_lt_le_of_measurable hf.measurable_mk hu hp hc
    fun t ht => ?_
  rw [← hset]
  exact h t ht

section Operator

variable {G : Type*} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G]
  [ESeminormedAddMonoid G] {T : (α → G) → β → ℝ≥0∞} {v : α → G} {b d t : ℝ}

/-- The reusable operator-level truncation argument for Marcinkiewicz interpolation.

Suppose `T` is subadditive, is of weak type `(1,1)` with constant `A`, and obeys the `L^∞`
bound `T g ≤ b · ‖g‖_∞`. Split `v` according to whether its
extended norm exceeds `c * t`. If `b * c + d ≤ 1`, then the low part contributes at most
`b * c * t`, so `T v > t` forces the image of the high part to exceed `d * t`. Applying the
weak-type bound to that high part gives

`t * ν {T v > t} ≤ d⁻¹ * A * ∫⁻ x in {‖v‖ₑ > c * t}, ‖v x‖ₑ ∂μ`.

The parameters `c` and `d` expose the choice of truncation rather than fixing the customary
`c = d = 1 / 2` for a normalized `L^∞` bound. -/
theorem mul_meas_ofReal_lt_le_setLIntegral
    (hv : AEMeasurable v μ) (ht : 0 < t) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (hbcd : b * c + d ≤ 1)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak : ∀ (g : α → G), AEMeasurable g μ → ∀ s : ℝ≥0∞,
      s * ν {y | s < T g y} ≤ A * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (hinfty : ∀ (g : α → G), AEMeasurable g μ → T g ≤ᵐ[ν]
      fun _ => ENNReal.ofReal b * eLpNormEssSup g μ) :
    ENNReal.ofReal t * ν {y | ENNReal.ofReal t < T v y} ≤
      ENNReal.ofReal d⁻¹ * A *
        ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
  have hct : 0 ≤ c * t := (mul_pos hc ht).le
  have hdt : 0 ≤ d * t := (mul_pos hd ht).le
  have hbct : 0 ≤ b * (c * t) := mul_nonneg hb hct
  have hdinv : 0 ≤ d⁻¹ := inv_nonneg.2 hd.le
  set g : α → G := hv.mk v
  have hvg : v =ᵐ[μ] g := hv.ae_eq_mk
  have hgmeas : Measurable g := hv.measurable_mk
  set S : Set α := {x | ENNReal.ofReal (c * t) < ‖g x‖ₑ} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hgmeas.eNorm
  set g₁ : α → G := S.indicator v with hg₁def
  set g₂ : α → G := Sᶜ.indicator v with hg₂def
  have hg₁meas : AEMeasurable g₁ μ := hv.indicator hSmeas
  have hg₂meas : AEMeasurable g₂ μ := hv.indicator hSmeas.compl
  have hsplit : g₁ + g₂ = v := by
    rw [hg₁def, hg₂def, Set.indicator_self_add_compl]
  have hTv : T v ≤ᵐ[ν] T g₁ + T g₂ := by
    rw [← hsplit]
    exact hadd g₁ g₂ hg₁meas hg₂meas
  have hg₂bound : ∀ᵐ x ∂μ, ‖g₂ x‖ₑ ≤ ENNReal.ofReal (c * t) := by
    filter_upwards [hvg] with x hx
    rw [hg₂def]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_notMem (by simp [hxS]), eNorm_zero]
      exact zero_le
    · rw [Set.indicator_of_mem (by simp [hxS]), hx]
      exact not_lt.1 (by simpa [hSdef] using hxS)
  have hTg₂ : ∀ᵐ y ∂ν, T g₂ y ≤ ENNReal.ofReal (b * (c * t)) := by
    filter_upwards [hinfty g₂ hg₂meas] with y hy
    exact hy.trans (calc
      ENNReal.ofReal b * eLpNormEssSup g₂ μ
          ≤ ENNReal.ofReal b * ENNReal.ofReal (c * t) := by
            gcongr
            exact essSup_le_of_ae_le _ hg₂bound
      _ = ENNReal.ofReal (b * (c * t)) := by rw [ENNReal.ofReal_mul hb])
  have hincl : {y | ENNReal.ofReal t < T v y} ≤ᵐ[ν]
      {y | ENNReal.ofReal (d * t) < T g₁ y} := by
    filter_upwards [hTv, hTg₂] with y hsum hlow
    intro hy
    have hconst : ENNReal.ofReal (d * t) + ENNReal.ofReal (b * (c * t)) ≤
        ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_add hdt hbct]
      gcongr
      nlinarith [mul_nonneg (sub_nonneg.2 hbcd) ht.le]
    have hlt : ENNReal.ofReal (d * t) + ENNReal.ofReal (b * (c * t)) <
        T g₁ y + ENNReal.ofReal (b * (c * t)) :=
      hconst.trans_lt (hy.trans_le (hsum.trans (add_le_add le_rfl hlow)))
    exact (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).1 hlt
  have hint : ∫⁻ x, ‖g₁ x‖ₑ ∂μ =
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
    have henorm : (fun x => ‖v x‖ₑ) =ᵐ[μ] fun x => ‖g x‖ₑ :=
      hvg.mono fun _ hx => congrArg eNorm hx
    have hsets : {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ} =ᵐ[μ] S := by
      filter_upwards [henorm] with x hx
      exact Iff.of_eq (congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (c * t) < z) hx)
    calc ∫⁻ x, ‖g₁ x‖ₑ ∂μ
        = ∫⁻ x in S, ‖v x‖ₑ ∂μ := by
          rw [hg₁def]
          simp_rw [eNorm_indicator_eq_indicator_eNorm]
          exact lintegral_indicator hSmeas _
      _ = ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
          rw [Measure.restrict_congr_set hsets]
  calc ENNReal.ofReal t * ν {y | ENNReal.ofReal t < T v y}
      = ENNReal.ofReal d⁻¹ *
          (ENNReal.ofReal (d * t) * ν {y | ENNReal.ofReal t < T v y}) := by
        have hscale : d⁻¹ * (d * t) = t := by field_simp
        rw [← mul_assoc, ← ENNReal.ofReal_mul hdinv, hscale]
    _ ≤ ENNReal.ofReal d⁻¹ *
          (ENNReal.ofReal (d * t) * ν {y | ENNReal.ofReal (d * t) < T g₁ y}) := by
        exact mul_le_mul_right
          (mul_le_mul_right (measure_mono_ae hincl) (ENNReal.ofReal (d * t)))
          (ENNReal.ofReal d⁻¹)
    _ ≤ ENNReal.ofReal d⁻¹ * (A * ∫⁻ x, ‖g₁ x‖ₑ ∂μ) := by
        exact mul_le_mul_right
          (hweak g₁ hg₁meas (ENNReal.ofReal (d * t)))
          (ENNReal.ofReal d⁻¹)
    _ = ENNReal.ofReal d⁻¹ * A *
          ∫⁻ x in {x | ENNReal.ofReal (c * t) < ‖v x‖ₑ}, ‖v x‖ₑ ∂μ := by
        rw [hint, mul_assoc]

/-- **Marcinkiewicz interpolation at operator level**, between weak type `(1,1)` and `L^∞`.

This packages the operator-specific truncation step: a subadditive operator with weak-type
constant `A` and `L^∞` constant `b` is strong type `(p,p)` for
`1 < p < ∞`. The positive splitting parameters `c, d` may be chosen arbitrarily subject to
`b * c + d ≤ 1`. -/
theorem lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup
    (hv : AEMeasurable v μ) (hTv : AEMeasurable (T v) ν) (hp : 1 < p)
    (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) (hbcd : b * c + d ≤ 1)
    (hadd : ∀ (g h : α → G), AEMeasurable g μ → AEMeasurable h μ →
      T (g + h) ≤ᵐ[ν] T g + T h)
    (hweak : ∀ (g : α → G), AEMeasurable g μ → ∀ s : ℝ≥0∞,
      s * ν {y | s < T g y} ≤ A * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (hinfty : ∀ (g : α → G), AEMeasurable g μ → T g ≤ᵐ[ν]
      fun _ => ENNReal.ofReal b * eLpNormEssSup g μ) :
    ∫⁻ y, T v y ^ p ∂ν ≤
      ENNReal.ofReal (p * c ^ (1 - p) / (p - 1)) * (ENNReal.ofReal d⁻¹ * A) *
        ∫⁻ x, ‖v x‖ₑ ^ p ∂μ := by
  apply lintegral_rpow_le_of_mul_meas_ofReal_lt_le hv.eNorm hTv hp hc
  intro t ht
  exact mul_meas_ofReal_lt_le_setLIntegral hv ht hb hc hd hbcd hadd hweak hinfty

end Operator

end TauCeti
