/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.UniformSpace.Equicontinuity
public import TauCeti.Analysis.Sobolev.Cylinder.W1p
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Equicontinuity
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Quasilinear first-order sections on `W^{1,p}` of the cylinder

A Floer cylinder, and more generally a solution of a perturbed Cauchy–Riemann equation on the
cylinder `ℝ × S¹`, is a zero of a first-order operator of the form

`F(u) = ∂s u + A(z, u) ∂t u + G(z, u)`,

with coefficients `A(z, y) ∈ L(V, V)` and `G(z, y) ∈ V` depending on the domain point `z = (s, t)`
and on the value `y` of the map. For the Floer equation
`∂s u - X_{K_s}(u) + J(u) (∂t u - X_{K_t}(u)) = 0` one takes `A = J` and
`G = -X_{K_s} - J X_{K_t}`. Transversality and gluing study the zeros of `F` near a reference map
`w` as the zeros of a map between Banach spaces, in a chart `ξ ↦ w + ξ` with `ξ` in the Sobolev
space `W^{1,p}(ℝ × S¹, V)` for `p > 2`, the dimension of the domain. This file constructs that
map and its derivative.

**The section.** For `x = (ξ, ξ_s, ξ_t)` in `W^{1,p}` (`TauCeti.CylinderSobolev.W1p`), with `ξ`
read through its continuous representative (`TauCeti.CylinderSobolev.continuousValue`), and for
a function `b` standing for `∂t w`, the **quasilinear section**
`TauCeti.CylinderSobolev.quasilinearSection A G w b p` sends `x` to the class in `Lᵖ` of

`ξ_s + A(z, w + ξ) (b + ξ_t) - A(z, w) b + G(z, w + ξ) - G(z, w)`.

When `b = ∂t w` and `ξ` is smooth, this is `F(w + ξ) - F(w)`: the operator in the chart, minus
its value at the reference map, which need not lie in `Lᵖ`. Its pointwise formula is
`TauCeti.CylinderSobolev.quasilinearSection_apply_ae`, under bounds making every term of it lie in
`Lᵖ`: `b` and `A` bounded, `A` and `G` Lipschitz in `y`, uniformly in `z`. On the jet of a test
section it is computed from classical derivatives
(`TauCeti.CylinderSobolev.quasilinearSection_toW1p_ae`).

**The linearization.** At `x₀ = (ξ₀, ξ₀_s, ξ₀_t)`, with `u₀ = w + ξ₀`, the derivative of the
section is the operator `TauCeti.CylinderSobolev.quasilinearLinearization A A' G' w b p x₀`,

`h ↦ h_s + A(z, u₀) h_t + (A'(z, u₀) h) (b + ξ₀_t) + G'(z, u₀) h`,

for the derivatives `A'`, `G'` of `A`, `G` in `y`
(`TauCeti.CylinderSobolev.quasilinearLinearization_apply_ae`). Its zeroth-order coefficient
contains the weak derivative `ξ₀_t`, which lies only in `Lᵖ`; the term `(A'(z, u₀) h) ξ₀_t` lies in
`Lᵖ` because `h` is bounded by its `W^{1,p}` norm. This is why the chart uses `p > 2`.

**Strict differentiability** (`TauCeti.CylinderSobolev.hasStrictFDerivAt_quasilinearSection`).
If `A'` and `G'` are bounded, and uniformly continuous in `y` uniformly in `z`
(`UniformEquicontinuous`), the section is strictly differentiable at every `x₀`, with derivative
the linearization. The first-order remainder of the section at `x₁`, `x₂` near `x₀` is the sum of
four terms: `(A(u₁) - A(u₀)) (ξ₁_t - ξ₂_t)`, which is small since the Sobolev embedding keeps
`u₁` uniformly close to `u₀`; the Taylor remainders of `A` and `G` between `u₂` and `u₁`, which the
mean value inequality bounds by the oscillation of `A'` and `G'` near `u₀`; and
`(A'(u₀) (ξ₁ - ξ₂)) (ξ₂_t - ξ₀_t)`, which is small since `ξ₂_t` is close to `ξ₀_t` in `Lᵖ`. Strict
differentiability is what the implicit function theorem and the Sard–Smale theorem ask of the map
whose zeros are the solutions.

The analogue for paths on the line, the trajectory section of a vector field, is
`TauCeti.WeakDerivStep.trajectorySection`.

## Main definitions

* `TauCeti.CylinderSobolev.quasilinearSection`: the section
  `x ↦ ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)` from `W^{1,p}` to `Lᵖ`.
* `TauCeti.CylinderSobolev.quasilinearLinearization`: its linearization at `x₀`.

## Main results

* `TauCeti.CylinderSobolev.quasilinearSection_apply_ae`: the pointwise formula of the section.
* `TauCeti.CylinderSobolev.quasilinearSection_zero`: it vanishes at the reference map.
* `TauCeti.CylinderSobolev.quasilinearSection_toW1p_ae`: its value on the jet of a test section.
* `TauCeti.CylinderSobolev.quasilinearLinearization_apply_ae`: the pointwise formula of the
  linearization.
* `TauCeti.CylinderSobolev.hasStrictFDerivAt_quasilinearSection`: the section is strictly
  differentiable, with derivative the linearization.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Proposition 3.5.3, on the nonlinear Cauchy–Riemann operator as a section in `W^{1,p}`
  charts and its linearization.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292, Section 3, on the Floer section on `W^{1,p}` of the
  cylinder.
-/

public section

noncomputable section

open MeasureTheory Filter Metric Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.CylinderSobolev

open StripSobolev (stripMeasure jet jet_apply coeFn_jetLp)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Preliminaries -/

/-- The first component of the jet of an element of `W1p V p` is its continuous representative,
almost everywhere on the strip. -/
private theorem fst_ae_eq_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((x : Lp (V × V × V) p stripMeasure) z).1 = continuousValue p x z := by
  filter_upwards [coeFn_valueL x, valueL_ae_eq_continuousValue hp hpt x] with z h₁ h₂
  rw [← h₁, h₂]

omit [CompleteSpace V] in
/-- The jet of a difference of elements of `W1p V p` is the difference of their jets, almost
everywhere. -/
private theorem coeFn_W1p_sub (x y : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((x - y : W1p V p) : Lp (V × V × V) p stripMeasure) z =
      (x : Lp (V × V × V) p stripMeasure) z - (y : Lp (V × V × V) p stripMeasure) z := by
  filter_upwards [Lp.coeFn_sub (x : Lp (V × V × V) p stripMeasure) y] with z hz
  rw [Submodule.coe_sub, hz, Pi.sub_apply]

/-- Applying a measurable family of continuous linear maps to a measurable family of vectors is
measurable. -/
private theorem aestronglyMeasurable_clm_apply {W X : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X] {f : ℝ × ℝ → W →L[ℝ] X}
    {g : ℝ × ℝ → W} (hf : AEStronglyMeasurable f stripMeasure)
    (hg : AEStronglyMeasurable g stripMeasure) :
    AEStronglyMeasurable (fun z ↦ f z (g z)) stripMeasure :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hf hg

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- A coefficient continuous jointly in the domain point and the value, evaluated along a
measurable map, is measurable. -/
private theorem aestronglyMeasurable_comp_uncurry {X : Type*} [TopologicalSpace X]
    {A : ℝ × ℝ → V → X} (hA : Continuous (Function.uncurry A)) {u : ℝ × ℝ → V}
    (hu : AEStronglyMeasurable u stripMeasure) :
    AEStronglyMeasurable (fun z ↦ A z (u z)) stripMeasure :=
  hA.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hu)

/-- An `Lᵖ` function dominated pointwise by a three-term combination of three other `Lᵖ`
functions obeys the same bound in norm. -/
private theorem norm_le_add_add_of_ae_norm_le {E F G H : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H] {f : Lp E p stripMeasure}
    {g : Lp F p stripMeasure} {k : Lp G p stripMeasure} {m : Lp H p stripMeasure} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hle : ∀ᵐ z ∂stripMeasure, ‖f z‖ ≤ a * ‖g z‖ + b * ‖k z‖ + c * ‖m z‖) :
    ‖f‖ ≤ a * ‖g‖ + b * ‖k‖ + c * ‖m‖ := by
  -- The last two terms are the pointwise norm of one `Lᵖ` function.
  have h := Lp.norm_le_add_of_ae_norm_le (f := f) (g := g)
    (h := b • Lp.normLp k + c • Lp.normLp m) ha zero_le_one (by
      filter_upwards [hle, Lp.coeFn_normLp k, Lp.coeFn_normLp m,
        Lp.coeFn_add (b • Lp.normLp k) (c • Lp.normLp m),
        Lp.coeFn_smul b (Lp.normLp k), Lp.coeFn_smul c (Lp.normLp m)]
        with z hz hk hm hadd hsk hsm
      rw [one_mul, hadd, Pi.add_apply, hsk, hsm, Pi.smul_apply, Pi.smul_apply, hk, hm,
        smul_eq_mul, smul_eq_mul, add_assoc] at *
      exact hz.trans (add_le_add_right (Real.le_norm_self _) _))
  calc ‖f‖ ≤ a * ‖g‖ + 1 * ‖b • Lp.normLp k + c • Lp.normLp m‖ := h
    _ ≤ a * ‖g‖ + (b * ‖k‖ + c * ‖m‖) := by
        rw [one_mul]
        gcongr
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hb, Real.norm_of_nonneg hc,
          Lp.norm_normLp, Lp.norm_normLp]
    _ = a * ‖g‖ + b * ‖k‖ + c * ‖m‖ := by ring

/-! ### The section -/

variable {A : ℝ × ℝ → V → V →L[ℝ] V} {G : ℝ × ℝ → V → V} {w b : ℝ × ℝ → V}

/-- The pointwise expression `ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)` of the
quasilinear section at an element `x = (ξ, ξ_s, ξ_t)` of `W1p V p`. -/
private def sectionFun (A : ℝ × ℝ → V → V →L[ℝ] V) (G : ℝ × ℝ → V → V) (w b : ℝ × ℝ → V)
    (x : W1p V p) (z : ℝ × ℝ) : V :=
  ((x : Lp (V × V × V) p stripMeasure) z).2.1 +
    (A z (w z + continuousValue p x z) (b z + ((x : Lp (V × V × V) p stripMeasure) z).2.2) -
      A z (w z) (b z)) +
    (G z (w z + continuousValue p x z) - G z (w z))

/-- Under bounds on `b` and `A` and Lipschitz bounds on `A` and `G` in the value, the pointwise
expression of the quasilinear section lies in `Lᵖ`. -/
private theorem memLp_sectionFun (hp : 2 < p) (hpt : p ≠ ∞) (hA : Continuous (Function.uncurry A))
    (hG : Continuous (Function.uncurry G)) (hw : AEStronglyMeasurable w stripMeasure)
    (hb : AEStronglyMeasurable b stripMeasure) {B C : ℝ} {K L : ℝ≥0} (hbB : ∀ z, ‖b z‖ ≤ B)
    (hAC : ∀ z y, ‖A z y‖ ≤ C) (hAL : ∀ z, LipschitzWith K (A z))
    (hGL : ∀ z, LipschitzWith L (G z)) (x : W1p V p) :
    MemLp (sectionFun A G w b x) p stripMeasure := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hAC 0 0)
  have hx := Lp.aestronglyMeasurable (x : Lp (V × V × V) p stripMeasure)
  have hu : AEStronglyMeasurable (fun z ↦ w z + continuousValue p x z) stripMeasure :=
    hw.add (continuousValue p x).continuous.aestronglyMeasurable
  have hAd := (aestronglyMeasurable_clm_apply (aestronglyMeasurable_comp_uncurry hA hu)
    (hb.add hx.snd.snd)).sub
    (aestronglyMeasurable_clm_apply (aestronglyMeasurable_comp_uncurry hA hw) hb)
  have hGd :=
    (aestronglyMeasurable_comp_uncurry hG hu).sub (aestronglyMeasurable_comp_uncurry hG hw)
  refine (Lp.memLp (x : Lp (V × V × V) p stripMeasure)).of_le_mul (c := 1 + C + K * B + L)
    ((hx.snd.fst.add hAd).add hGd) ?_
  filter_upwards [fst_ae_eq_continuousValue hp hpt x] with z hz
  set v := (x : Lp (V × V × V) p stripMeasure) z
  set ξ := continuousValue p x z
  have h0 : ‖ξ‖ ≤ ‖v‖ := hz ▸ norm_fst_le v
  have h1 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have h2 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  have hAd : ‖A z (w z + ξ) (b z + v.2.2) - A z (w z) (b z)‖ ≤ C * ‖v‖ + K * ‖v‖ * B := by
    have he : A z (w z + ξ) (b z + v.2.2) - A z (w z) (b z) =
        A z (w z + ξ) v.2.2 + (A z (w z + ξ) - A z (w z)) (b z) := by
      rw [map_add, sub_apply]
      abel
    have hL : ‖A z (w z + ξ) - A z (w z)‖ ≤ K * ‖v‖ :=
      ((hAL z).norm_sub_le _ _).trans (by rw [add_sub_cancel_left]; gcongr)
    rw [he]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ((A z _).le_of_opNorm_le (hAC z _) _).trans (by gcongr)
    · exact ((A z (w z + ξ) - A z (w z)).le_opNorm _).trans
        (mul_le_mul hL (hbB z) (norm_nonneg _) (by positivity))
  have hGd : ‖G z (w z + ξ) - G z (w z)‖ ≤ L * ‖v‖ :=
    ((hGL z).norm_sub_le _ _).trans (by rw [add_sub_cancel_left]; gcongr)
  calc ‖sectionFun A G w b x z‖
      ≤ ‖v.2.1‖ + ‖A z (w z + ξ) (b z + v.2.2) - A z (w z) (b z)‖ +
          ‖G z (w z + ξ) - G z (w z)‖ := norm_add₃_le
    _ ≤ ‖v‖ + (C * ‖v‖ + K * ‖v‖ * B) + L * ‖v‖ := by gcongr
    _ = (1 + C + K * B + L) * ‖v‖ := by ring

open scoped Classical in
/-- **The quasilinear section** of the operator `F(u) = ∂s u + A(z, u) ∂t u + G(z, u)` around a
reference map `w`, with `b` standing for `∂t w`: the map from `W^{1,p}(ℝ × S¹, V)` to `Lᵖ` sending
`x = (ξ, ξ_s, ξ_t)` to the class of `ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)`, with `ξ`
read through its continuous representative. When `b = ∂t w` and `ξ` is a test section, this is
`F(w + ξ) - F(w)`. The expression lies in `Lᵖ` under the bounds of
`TauCeti.CylinderSobolev.quasilinearSection_apply_ae`; when it does not, the section takes the
value `0`. -/
def quasilinearSection (A : ℝ × ℝ → V → V →L[ℝ] V) (G : ℝ × ℝ → V → V) (w b : ℝ × ℝ → V)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : W1p V p) : Lp V p stripMeasure :=
  if h : MemLp (sectionFun A G w b x) p stripMeasure then h.toLp _ else 0

/-- **The pointwise formula of the quasilinear section.** For `2 < p < ∞`, coefficients `A` and
`G` continuous in `(z, y)`, `A` bounded, `A` and `G` Lipschitz in `y` uniformly in `z`, and `b`
bounded, the section at `x = (ξ, ξ_s, ξ_t)` is almost everywhere
`ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)`. -/
theorem quasilinearSection_apply_ae (hp : 2 < p) (hpt : p ≠ ∞)
    (hA : Continuous (Function.uncurry A)) (hG : Continuous (Function.uncurry G))
    (hw : AEStronglyMeasurable w stripMeasure) (hb : AEStronglyMeasurable b stripMeasure)
    {B C : ℝ} {K L : ℝ≥0} (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hAL : ∀ z, LipschitzWith K (A z)) (hGL : ∀ z, LipschitzWith L (G z)) (x : W1p V p) :
    quasilinearSection A G w b p x =ᵐ[stripMeasure] fun z ↦
      ((x : Lp (V × V × V) p stripMeasure) z).2.1 +
        (A z (w z + continuousValue p x z) (b z + ((x : Lp (V × V × V) p stripMeasure) z).2.2) -
          A z (w z) (b z)) +
        (G z (w z + continuousValue p x z) - G z (w z)) := by
  have h := memLp_sectionFun hp hpt hA hG hw hb hbB hAC hAL hGL x
  have he : quasilinearSection A G w b p x = h.toLp _ := by simp [quasilinearSection, h]
  rw [he]
  exact h.coeFn_toLp

/-- The quasilinear section vanishes at the reference map. -/
@[simp]
theorem quasilinearSection_zero : quasilinearSection A G w b p 0 = 0 := by
  rw [quasilinearSection]
  split_ifs with h
  · refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [h.coeFn_toLp, Lp.coeFn_zero (V × V × V) p stripMeasure] with z hz h0
    rw [hz, Pi.zero_apply, sectionFun, map_zero, FunLike.coe_zero, Pi.zero_apply,
      Submodule.coe_zero, h0]
    simp
  · rfl

/-- **The section on test sections.** On the jet of a test section `ξ`, the quasilinear section is
computed from the classical derivatives of `ξ`: almost everywhere it is
`∂s ξ + A(w + ξ) (b + ∂t ξ) - A(w) b + G(w + ξ) - G(w)`. -/
theorem quasilinearSection_toW1p_ae (hp : 2 < p) (hpt : p ≠ ∞)
    (hA : Continuous (Function.uncurry A)) (hG : Continuous (Function.uncurry G))
    (hw : AEStronglyMeasurable w stripMeasure) (hb : AEStronglyMeasurable b stripMeasure)
    {B C : ℝ} {K L : ℝ≥0} (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hAL : ∀ z, LipschitzWith K (A z)) (hGL : ∀ z, LipschitzWith L (G z))
    (ξ : testSection V) :
    quasilinearSection A G w b p (toW1p p ξ) =ᵐ[stripMeasure] fun z ↦
      fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0) +
        (A z (w z + (ξ : ℝ × ℝ → V) z) (b z + fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)) -
          A z (w z) (b z)) +
        (G z (w z + (ξ : ℝ × ℝ → V) z) - G z (w z)) := by
  filter_upwards [quasilinearSection_apply_ae hp hpt hA hG hw hb hbB hAC hAL hGL (toW1p p ξ),
    coeFn_jetLp (S := testSection V) p ξ] with z hz hj
  rw [hz, coe_continuousValue_toW1p hp hpt, StripSobolev.coe_toJetClosure, hj, jet_apply]

/-! ### The linearization -/

variable {A' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V} {G' : ℝ × ℝ → V → V →L[ℝ] V}

/-- The pointwise expression `h_s + A(u₀) h_t + (A'(u₀) h) b + G'(u₀) h + (A'(u₀) h) ξ₀_t` of the
linearization at `x₀` of the quasilinear section, applied to `h`, with `u₀ = w + ξ₀`. The value
`h` enters the last term through its continuous representative and the others through its jet. -/
private def linFun (A : ℝ × ℝ → V → V →L[ℝ] V) (A' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V)
    (G' : ℝ × ℝ → V → V →L[ℝ] V)
    (w b : ℝ × ℝ → V) (x₀ h : W1p V p) (z : ℝ × ℝ) : V :=
  ((h : Lp (V × V × V) p stripMeasure) z).2.1 +
    A z (w z + continuousValue p x₀ z) ((h : Lp (V × V × V) p stripMeasure) z).2.2 +
    A' z (w z + continuousValue p x₀ z) ((h : Lp (V × V × V) p stripMeasure) z).1 (b z) +
    G' z (w z + continuousValue p x₀ z) ((h : Lp (V × V × V) p stripMeasure) z).1 +
    A' z (w z + continuousValue p x₀ z) (continuousValue p h z)
      ((x₀ : Lp (V × V × V) p stripMeasure) z).2.2


omit [CompleteSpace V] in
/-- The jet of a sum of elements of `W1p V p` is the sum of their jets, almost everywhere. -/
private theorem coeFn_W1p_add (x y : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((x + y : W1p V p) : Lp (V × V × V) p stripMeasure) z =
      (x : Lp (V × V × V) p stripMeasure) z + (y : Lp (V × V × V) p stripMeasure) z := by
  filter_upwards [Lp.coeFn_add (x : Lp (V × V × V) p stripMeasure) y] with z hz
  rw [Submodule.coe_add, hz, Pi.add_apply]

omit [CompleteSpace V] in
/-- The jet of a multiple of an element of `W1p V p` is the multiple of its jet, almost
everywhere. -/
private theorem coeFn_W1p_smul (c : ℝ) (x : W1p V p) :
    ∀ᵐ z ∂stripMeasure, ((c • x : W1p V p) : Lp (V × V × V) p stripMeasure) z =
      c • (x : Lp (V × V × V) p stripMeasure) z := by
  filter_upwards [Lp.coeFn_smul c (x : Lp (V × V × V) p stripMeasure)] with z hz
  rw [Submodule.coe_smul, hz, Pi.smul_apply]

/-- The pointwise bound on the expression of the linearization:
`‖h_s + A(u₀) h_t + (A'(u₀) h) b + G'(u₀) h + (A'(u₀) h) ξ₀_t‖` is at most
`(1 + C + K B + L) ‖h‖ + K ‖h‖_∞ ‖ξ₀_t‖`, the jets being measured pointwise. -/
private theorem norm_linFun_le {B C K L : ℝ} (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (x₀ h : W1p V p) (z : ℝ × ℝ) :
    ‖linFun A A' G' w b x₀ h z‖ ≤
      (1 + C + K * B + L) * ‖(h : Lp (V × V × V) p stripMeasure) z‖ +
        K * ‖continuousValue p h‖ * ‖(x₀ : Lp (V × V × V) p stripMeasure) z‖ := by
  have hK : 0 ≤ K := (norm_nonneg (A' 0 0)).trans (hA'K 0 0)
  set v := (h : Lp (V × V × V) p stripMeasure) z
  set v₀ := (x₀ : Lp (V × V × V) p stripMeasure) z
  set u₀ := w z + continuousValue p x₀ z
  have h1 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have h2 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  have h0 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h₀ : ‖v₀.2.2‖ ≤ ‖v₀‖ := (norm_snd_le v₀.2).trans (norm_snd_le v₀)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hAC z u₀)
  have hL : 0 ≤ L := (norm_nonneg _).trans (hG'K z u₀)
  have hA : ‖A z u₀ v.2.2‖ ≤ C * ‖v‖ :=
    ((A z u₀).le_of_opNorm_le (hAC z u₀) _).trans (by gcongr)
  have hA'b : ‖A' z u₀ v.1 (b z)‖ ≤ K * ‖v‖ * B :=
    ((A' z u₀ v.1).le_opNorm _).trans (mul_le_mul
      (((A' z u₀).le_of_opNorm_le (hA'K z u₀) _).trans (by gcongr)) (hbB z) (norm_nonneg _)
      (by positivity))
  have hG' : ‖G' z u₀ v.1‖ ≤ L * ‖v‖ :=
    ((G' z u₀).le_of_opNorm_le (hG'K z u₀) _).trans (by gcongr)
  have hA't : ‖A' z u₀ (continuousValue p h z) v₀.2.2‖ ≤ K * ‖continuousValue p h‖ * ‖v₀‖ :=
    ((A' z u₀ _).le_opNorm _).trans (mul_le_mul
      (((A' z u₀).le_of_opNorm_le (hA'K z u₀) _).trans
        (by gcongr; exact BoundedContinuousFunction.norm_coe_le_norm _ _)) h₀ (norm_nonneg _)
      (by positivity))
  have htri : ‖linFun A A' G' w b x₀ h z‖ ≤ ‖v.2.1‖ + ‖A z u₀ v.2.2‖ + ‖A' z u₀ v.1 (b z)‖ +
      ‖G' z u₀ v.1‖ + ‖A' z u₀ (continuousValue p h z) v₀.2.2‖ :=
    (norm_add_le _ _).trans (add_le_add_left norm_add₄_le _)
  linarith

variable {B C : ℝ} {K L : ℝ≥0}

/-- Under bounds on `b`, `A`, `A'` and `G'`, the pointwise expression of the linearization at `x₀`
is the pointwise expression of a continuous linear map from `W1p V p` to `Lᵖ`. -/
private theorem exists_linFun (hAc : Continuous (Function.uncurry A))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) (hb : AEStronglyMeasurable b stripMeasure)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C) (hA'K : ∀ z y, ‖A' z y‖ ≤ K)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (x₀ : W1p V p) :
    ∃ T : W1p V p →L[ℝ] Lp V p stripMeasure,
      ∀ h, T h =ᵐ[stripMeasure] linFun A A' G' w b x₀ h := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hAC 0 0)
  have hu₀ : AEStronglyMeasurable (fun z ↦ w z + continuousValue p x₀ z) stripMeasure :=
    hw.add (continuousValue p x₀).continuous.aestronglyMeasurable
  have hx₀ := Lp.aestronglyMeasurable (x₀ : Lp (V × V × V) p stripMeasure)
  have hmem (h : W1p V p) : MemLp (linFun A A' G' w b x₀ h) p stripMeasure := by
    have hj := Lp.aestronglyMeasurable (h : Lp (V × V × V) p stripMeasure)
    have hA'u := aestronglyMeasurable_comp_uncurry hA'c hu₀
    have hg : MemLp (fun z ↦ (1 + C + K * B + L) * ‖(h : Lp (V × V × V) p stripMeasure) z‖ +
        K * ‖continuousValue p h‖ * ‖(x₀ : Lp (V × V × V) p stripMeasure) z‖) p stripMeasure :=
      ((Lp.memLp _).norm.const_mul _).add ((Lp.memLp _).norm.const_mul _)
    refine hg.of_le ?_ (ae_of_all _ fun z ↦
      (norm_linFun_le hbB hAC hA'K hG'K x₀ h z).trans (Real.le_norm_self _))
    exact (((hj.snd.fst.add (aestronglyMeasurable_clm_apply
      (aestronglyMeasurable_comp_uncurry hAc hu₀) hj.snd.snd)).add
      (aestronglyMeasurable_clm_apply (aestronglyMeasurable_clm_apply hA'u hj.fst) hb)).add
      (aestronglyMeasurable_clm_apply (aestronglyMeasurable_comp_uncurry hG'c hu₀) hj.fst)).add
      (aestronglyMeasurable_clm_apply (aestronglyMeasurable_clm_apply hA'u
        (continuousValue p h).continuous.aestronglyMeasurable) hx₀.snd.snd)
  let T : W1p V p →ₗ[ℝ] Lp V p stripMeasure :=
    { toFun h := (hmem h).toLp _
      map_add' h₁ h₂ := by
        refine Lp.ext ?_
        filter_upwards [(hmem (h₁ + h₂)).coeFn_toLp,
          Lp.coeFn_add ((hmem h₁).toLp _) ((hmem h₂).toLp _), (hmem h₁).coeFn_toLp,
          (hmem h₂).coeFn_toLp, coeFn_W1p_add h₁ h₂] with z e₁ e₂ e₃ e₄ e₅
        rw [e₁, e₂, Pi.add_apply, e₃, e₄]
        simp only [linFun, e₅, map_add, Prod.fst_add, Prod.snd_add, add_apply]
        abel
      map_smul' c h := by
        refine Lp.ext ?_
        filter_upwards [(hmem (c • h)).coeFn_toLp, Lp.coeFn_smul c ((hmem h).toLp _),
          (hmem h).coeFn_toLp, coeFn_W1p_smul c h] with z e₁ e₂ e₃ e₄
        rw [e₁, RingHom.id_apply, e₂, Pi.smul_apply, e₃]
        simp only [linFun, e₄, map_smul, Prod.smul_fst, Prod.smul_snd, smul_apply,
          smul_add] }
  refine ⟨T.mkContinuous ((1 + C + K * B + L) + K * ‖continuousValue (V := V) p‖ * ‖x₀‖)
    fun h ↦ ?_, fun h ↦ (hmem h).coeFn_toLp⟩
  have hle := Lp.norm_le_add_of_ae_norm_le (f := (hmem h).toLp _)
    (g := (h : Lp (V × V × V) p stripMeasure)) (h := (x₀ : Lp (V × V × V) p stripMeasure))
    (a := 1 + C + K * B + L) (b := K * ‖continuousValue p h‖) (by positivity) (by positivity) (by
      filter_upwards [(hmem h).coeFn_toLp] with z hz
      rw [hz]
      exact norm_linFun_le hbB hAC hA'K hG'K x₀ h z)
  have hE := (continuousValue (V := V) p).le_opNorm h
  calc ‖T h‖ ≤ (1 + C + K * B + L) * ‖h‖ + K * ‖continuousValue p h‖ * ‖x₀‖ := hle
    _ ≤ (1 + C + K * B + L) * ‖h‖ + K * (‖continuousValue (V := V) p‖ * ‖h‖) * ‖x₀‖ := by
        gcongr
    _ = _ := by ring

open scoped Classical in
/-- **The linearization of the quasilinear section** at `x₀ = (ξ₀, ξ₀_s, ξ₀_t)`: the continuous
linear map from `W^{1,p}(ℝ × S¹, V)` to `Lᵖ` sending `h` to the class of
`h_s + A(u₀) h_t + (A'(u₀) h) (b + ξ₀_t) + G'(u₀) h`, with `u₀ = w + ξ₀` and `A'`, `G'` the
derivatives of `A`, `G` in the value. The value of `h` enters the term with `ξ₀_t`, which lies
only in `Lᵖ`, through its continuous representative. Under the bounds of
`TauCeti.CylinderSobolev.quasilinearLinearization_apply_ae` such an operator exists, and it is
unique; otherwise the linearization is `0`. It is the strict derivative of
`TauCeti.CylinderSobolev.quasilinearSection` at `x₀`
(`TauCeti.CylinderSobolev.hasStrictFDerivAt_quasilinearSection`). -/
def quasilinearLinearization (A : ℝ × ℝ → V → V →L[ℝ] V)
    (A' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V) (G' : ℝ × ℝ → V → V →L[ℝ] V) (w b : ℝ × ℝ → V)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x₀ : W1p V p) : W1p V p →L[ℝ] Lp V p stripMeasure :=
  if H : ∃ T : W1p V p →L[ℝ] Lp V p stripMeasure,
      ∀ h, T h =ᵐ[stripMeasure] linFun A A' G' w b x₀ h then H.choose else 0

/-- **The pointwise formula of the linearization.** For coefficients `A`, `A'`, `G'` continuous in
`(z, y)` and bounded, and `b` bounded, the linearization at
`x₀ = (ξ₀, ξ₀_s, ξ₀_t)` applied to `h = (η, η_s, η_t)` is almost everywhere
`η_s + A(u₀) η_t + (A'(u₀) η) b + G'(u₀) η + (A'(u₀) η) ξ₀_t`, with `u₀ = w + ξ₀`. -/
theorem quasilinearLinearization_apply_ae (hAc : Continuous (Function.uncurry A))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) (hb : AEStronglyMeasurable b stripMeasure)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (x₀ h : W1p V p) :
    quasilinearLinearization A A' G' w b p x₀ h =ᵐ[stripMeasure] fun z ↦
      ((h : Lp (V × V × V) p stripMeasure) z).2.1 +
        A z (w z + continuousValue p x₀ z) ((h : Lp (V × V × V) p stripMeasure) z).2.2 +
        A' z (w z + continuousValue p x₀ z) ((h : Lp (V × V × V) p stripMeasure) z).1 (b z) +
        G' z (w z + continuousValue p x₀ z) ((h : Lp (V × V × V) p stripMeasure) z).1 +
        A' z (w z + continuousValue p x₀ z) (continuousValue p h z)
          ((x₀ : Lp (V × V × V) p stripMeasure) z).2.2 := by
  have H := exists_linFun hAc hA'c hG'c hw hb hbB hAC hA'K hG'K x₀
  rw [quasilinearLinearization, dite_eq_left_of_eq_true (eq_true H)]
  exact H.choose_spec h

/-! ### Strict differentiability -/

/-- The continuous representatives of two elements of `W1p V p` are uniformly within the norm of
the Sobolev embedding times their distance. -/
private theorem norm_continuousValue_sub_le (x y : W1p V p) (z : ℝ × ℝ) :
    ‖continuousValue p x z - continuousValue p y z‖ ≤ ‖continuousValue (V := V) p‖ * ‖x - y‖ := by
  have h : continuousValue p x z - continuousValue p y z = continuousValue p (x - y) z := by
    rw [map_sub]
    rfl
  have hle := (continuousValue (V := V) p).le_opNorm (x - y)
  rw [h]
  exact (BoundedContinuousFunction.norm_coe_le_norm _ _).trans hle

omit [CompleteSpace V] in
/-- The pointwise algebra of the first-order remainder of the section. Let `vᵢ` be the jets of
`x₀`, `x₁`, `x₂` at a point, `ξᵢ` their values and `vh = v₁ - v₂`, `vm = v₂ - v₀`. The remainder
`S x₁ - S x₂ - D (x₁ - x₂)` at that point is the sum of `(A(u₁) - A(u₀)) (v₁ - v₂)_t`, the Taylor
remainder of `A` between `u₂` and `u₁` applied to `b + v₂_t`, `(A'(u₀) (ξ₁ - ξ₂)) (v₂ - v₀)_t`, and
the Taylor remainder of `G`, with `uᵢ = w + ξᵢ`. Bounding each term gives the stated estimate,
given bounds `a₁` on `‖ξ₁ - ξ₀‖` and `a₂` on `‖ξ₁ - ξ₂‖`. -/
private theorem norm_remainder_apply_le (hbB : ∀ z, ‖b z‖ ≤ B) (hAL : ∀ z, LipschitzWith K (A z))
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (z : ℝ × ℝ) {ξ₀ ξ₁ ξ₂ : V} {v₀ v₁ v₂ vh vm : V × V × V}
    (hvh : vh = v₁ - v₂) (hvm : vm = v₂ - v₀) (hξ : vh.1 = ξ₁ - ξ₂) {ε a₁ a₂ : ℝ} (hε : 0 ≤ ε)
    (ha₁ : ‖ξ₁ - ξ₀‖ ≤ a₁) (ha₂ : ‖ξ₁ - ξ₂‖ ≤ a₂)
    (hmA : ‖A z (w z + ξ₁) - A z (w z + ξ₂) - A' z (w z + ξ₀) (ξ₁ - ξ₂)‖ ≤ ε * ‖ξ₁ - ξ₂‖)
    (hmG : ‖G z (w z + ξ₁) - G z (w z + ξ₂) - G' z (w z + ξ₀) (ξ₁ - ξ₂)‖ ≤ ε * ‖ξ₁ - ξ₂‖) :
    ‖v₁.2.1 + (A z (w z + ξ₁) (b z + v₁.2.2) - A z (w z) (b z)) + (G z (w z + ξ₁) - G z (w z)) -
        (v₂.2.1 + (A z (w z + ξ₂) (b z + v₂.2.2) - A z (w z) (b z)) +
          (G z (w z + ξ₂) - G z (w z))) -
        (vh.2.1 + A z (w z + ξ₀) vh.2.2 + A' z (w z + ξ₀) vh.1 (b z) +
          G' z (w z + ξ₀) vh.1 + A' z (w z + ξ₀) (ξ₁ - ξ₂) v₀.2.2)‖ ≤
      (K * a₁ + ε * B + ε) * ‖vh‖ + ε * a₂ * ‖v₂‖ + K * a₂ * ‖vm‖ := by
  have hξh : ‖ξ₁ - ξ₂‖ ≤ ‖vh‖ := hξ ▸ norm_fst_le vh
  have ha₁0 : 0 ≤ a₁ := (norm_nonneg _).trans ha₁
  have ha₂0 : 0 ≤ a₂ := (norm_nonneg _).trans ha₂
  have hv : ‖v₁.2.2 - v₂.2.2‖ ≤ ‖vh‖ := by
    rw [hvh]
    exact (norm_snd_le (v₁ - v₂).2).trans (norm_snd_le (v₁ - v₂))
  have hv₂ : ‖v₂.2.2‖ ≤ ‖v₂‖ := (norm_snd_le v₂.2).trans (norm_snd_le v₂)
  have hv₀ : ‖v₂.2.2 - v₀.2.2‖ ≤ ‖vm‖ := by
    rw [hvm]
    exact (norm_snd_le (v₂ - v₀).2).trans (norm_snd_le (v₂ - v₀))
  -- The remainder is the sum of four terms.
  have hid : v₁.2.1 + (A z (w z + ξ₁) (b z + v₁.2.2) - A z (w z) (b z)) +
      (G z (w z + ξ₁) - G z (w z)) -
      (v₂.2.1 + (A z (w z + ξ₂) (b z + v₂.2.2) - A z (w z) (b z)) +
        (G z (w z + ξ₂) - G z (w z))) -
      (vh.2.1 + A z (w z + ξ₀) vh.2.2 + A' z (w z + ξ₀) vh.1 (b z) +
        G' z (w z + ξ₀) vh.1 + A' z (w z + ξ₀) (ξ₁ - ξ₂) v₀.2.2) =
      (A z (w z + ξ₁) - A z (w z + ξ₀)) (v₁.2.2 - v₂.2.2) +
        (A z (w z + ξ₁) - A z (w z + ξ₂) - A' z (w z + ξ₀) (ξ₁ - ξ₂)) (b z + v₂.2.2) +
        A' z (w z + ξ₀) (ξ₁ - ξ₂) (v₂.2.2 - v₀.2.2) +
        (G z (w z + ξ₁) - G z (w z + ξ₂) - G' z (w z + ξ₀) (ξ₁ - ξ₂)) := by
    rw [hξ, hvh]
    simp only [Prod.snd_sub, Prod.fst_sub, map_sub, map_add, sub_apply]
    abel
  have hTa : ‖(A z (w z + ξ₁) - A z (w z + ξ₀)) (v₁.2.2 - v₂.2.2)‖ ≤ K * a₁ * ‖vh‖ := by
    refine ((A z (w z + ξ₁) - A z (w z + ξ₀)).le_opNorm _).trans
      (mul_le_mul ?_ hv (norm_nonneg _) (by positivity))
    refine ((hAL z).norm_sub_le _ _).trans ?_
    rw [add_sub_add_left_eq_sub]
    gcongr
  have hTb : ‖(A z (w z + ξ₁) - A z (w z + ξ₂) - A' z (w z + ξ₀) (ξ₁ - ξ₂)) (b z + v₂.2.2)‖ ≤
      ε * B * ‖vh‖ + ε * a₂ * ‖v₂‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have hB : 0 ≤ B := (norm_nonneg _).trans (hbB z)
    have h₂ : ‖b z + v₂.2.2‖ ≤ B + ‖v₂‖ := (norm_add_le _ _).trans (add_le_add (hbB z) hv₂)
    calc _ ≤ ε * ‖ξ₁ - ξ₂‖ * (B + ‖v₂‖) := mul_le_mul hmA h₂ (norm_nonneg _) (by positivity)
      _ = ε * B * ‖ξ₁ - ξ₂‖ + ε * ‖ξ₁ - ξ₂‖ * ‖v₂‖ := by ring
      _ ≤ ε * B * ‖vh‖ + ε * a₂ * ‖v₂‖ := by gcongr
  have hTc : ‖A' z (w z + ξ₀) (ξ₁ - ξ₂) (v₂.2.2 - v₀.2.2)‖ ≤ K * a₂ * ‖vm‖ :=
    ((A' z (w z + ξ₀) (ξ₁ - ξ₂)).le_opNorm _).trans (mul_le_mul
      (((A' z (w z + ξ₀)).le_of_opNorm_le (hA'K z _) _).trans (by gcongr)) hv₀
      (norm_nonneg _) (by positivity))
  have hTd : ‖G z (w z + ξ₁) - G z (w z + ξ₂) - G' z (w z + ξ₀) (ξ₁ - ξ₂)‖ ≤ ε * ‖vh‖ :=
    hmG.trans (by gcongr)
  rw [hid]
  refine norm_add₄_le.trans ?_
  linarith

/-- **The first-order remainder of the section.** Let `ε ≥ 0` bound the Taylor remainders of `A`
and `G` between the values `w + ξ₂` and `w + ξ₁` of `x₂` and `x₁`, relative to the derivatives
at the value `w + ξ₀` of `x₀`. Then the remainder `S x₁ - S x₂ - D (x₁ - x₂)` of the section `S`
with respect to the linearization `D` at `x₀` has norm at most
`‖x₁ - x₂‖ (K E (‖x₁ - x₀‖ + ‖x₂ - x₀‖) + ε (B + 1 + E ‖x₂‖))`, with `E` the norm of the Sobolev
embedding. -/
private theorem norm_remainder_le (hp : 2 < p) (hpt : p ≠ ∞)
    (hAc : Continuous (Function.uncurry A)) (hGc : Continuous (Function.uncurry G))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) (hb : AEStronglyMeasurable b stripMeasure)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C) (hAL : ∀ z, LipschitzWith K (A z))
    (hGL : ∀ z, LipschitzWith L (G z)) (hA'K : ∀ z y, ‖A' z y‖ ≤ K)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) {x₀ x₁ x₂ : W1p V p} {ε : ℝ} (hε : 0 ≤ ε)
    (hmA : ∀ z, ‖A z (w z + continuousValue p x₁ z) - A z (w z + continuousValue p x₂ z) -
      A' z (w z + continuousValue p x₀ z) (continuousValue p x₁ z - continuousValue p x₂ z)‖ ≤
        ε * ‖continuousValue p x₁ z - continuousValue p x₂ z‖)
    (hmG : ∀ z, ‖G z (w z + continuousValue p x₁ z) - G z (w z + continuousValue p x₂ z) -
      G' z (w z + continuousValue p x₀ z) (continuousValue p x₁ z - continuousValue p x₂ z)‖ ≤
        ε * ‖continuousValue p x₁ z - continuousValue p x₂ z‖) :
    ‖quasilinearSection A G w b p x₁ - quasilinearSection A G w b p x₂ -
        quasilinearLinearization A A' G' w b p x₀ (x₁ - x₂)‖ ≤
      ‖x₁ - x₂‖ * (K * ‖continuousValue (V := V) p‖ * (‖x₁ - x₀‖ + ‖x₂ - x₀‖) +
        ε * (B + 1 + ‖continuousValue (V := V) p‖ * ‖x₂‖)) := by
  set E := ‖continuousValue (V := V) p‖
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  have key := norm_le_add_add_of_ae_norm_le
    (f := quasilinearSection A G w b p x₁ - quasilinearSection A G w b p x₂ -
      quasilinearLinearization A A' G' w b p x₀ (x₁ - x₂))
    (g := ((x₁ - x₂ : W1p V p) : Lp (V × V × V) p stripMeasure))
    (k := (x₂ : Lp (V × V × V) p stripMeasure))
    (m := ((x₂ - x₀ : W1p V p) : Lp (V × V × V) p stripMeasure))
    (a := K * (E * ‖x₁ - x₀‖) + ε * B + ε) (b := ε * (E * ‖x₁ - x₂‖))
    (c := K * (E * ‖x₁ - x₂‖)) (by positivity) (by positivity) (by positivity) (by
      filter_upwards [Lp.coeFn_sub (quasilinearSection A G w b p x₁ -
          quasilinearSection A G w b p x₂) (quasilinearLinearization A A' G' w b p x₀ (x₁ - x₂)),
        Lp.coeFn_sub (quasilinearSection A G w b p x₁) (quasilinearSection A G w b p x₂),
        quasilinearSection_apply_ae hp hpt hAc hGc hw hb hbB hAC hAL hGL x₁,
        quasilinearSection_apply_ae hp hpt hAc hGc hw hb hbB hAC hAL hGL x₂,
        quasilinearLinearization_apply_ae hAc hA'c hG'c hw hb hbB hAC hA'K hG'K x₀ (x₁ - x₂),
        coeFn_W1p_sub x₁ x₂, coeFn_W1p_sub x₂ x₀, fst_ae_eq_continuousValue hp hpt (x₁ - x₂)]
        with z e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      have hξ : continuousValue p (x₁ - x₂) z =
          continuousValue p x₁ z - continuousValue p x₂ z := by
        rw [map_sub]
        rfl
      rw [hξ] at e₅ e₈
      rw [e₁, Pi.sub_apply, e₂, Pi.sub_apply, e₃, e₄, e₅]
      exact norm_remainder_apply_le hbB hAL hA'K z e₆ e₇ e₈ hε
        (norm_continuousValue_sub_le x₁ x₀ z) (norm_continuousValue_sub_le x₁ x₂ z) (hmA z) (hmG z))
  refine key.trans_eq ?_
  simp only [Submodule.norm_coe]
  ring

omit [CompleteSpace V] in
/-- The mean value inequality on a ball: if the derivative `F'` of `F` stays within `ε` of
`F' y₀` on the ball of radius `δ` around `y₀`, then the Taylor remainder of `F` between two points
of that ball, relative to `F' y₀`, is at most `ε` times their distance. -/
private theorem norm_sub_sub_le_of_dist_lt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : V → X} {F' : V → V →L[ℝ] X} (hF : ∀ y, HasFDerivAt F (F' y) y) {y₀ y₁ y₂ : V}
    {δ ε : ℝ} (hosc : ∀ y, dist y y₀ < δ → dist (F' y) (F' y₀) < ε) (h₁ : dist y₁ y₀ < δ)
    (h₂ : dist y₂ y₀ < δ) : ‖F y₁ - F y₂ - F' y₀ (y₁ - y₂)‖ ≤ ε * ‖y₁ - y₂‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (s := ball y₀ δ)
    (fun y _ ↦ (hF y).hasFDerivWithinAt)
    (fun y hy ↦ by simpa only [dist_eq_norm] using (hosc y hy).le) (convex_ball _ _) h₂ h₁

/-- Elements of `W1p V p` within `r ≤ δ / (E + 1)` of `x₀`, with `E` the norm of the Sobolev
embedding, have continuous representatives uniformly within `δ` of that of `x₀`. -/
private theorem dist_add_continuousValue_lt {x x₀ : W1p V p} {δ r : ℝ} (hδ : 0 < δ)
    (hrδ : r ≤ δ / (‖continuousValue (V := V) p‖ + 1)) (hx : ‖x - x₀‖ < r) (y : V)
    (z : ℝ × ℝ) : dist (y + continuousValue p x z) (y + continuousValue p x₀ z) < δ := by
  rw [dist_add_left, dist_eq_norm]
  calc ‖continuousValue p x z - continuousValue p x₀ z‖
      ≤ ‖continuousValue (V := V) p‖ * ‖x - x₀‖ := norm_continuousValue_sub_le x x₀ z
    _ ≤ ‖continuousValue (V := V) p‖ * (δ / (‖continuousValue (V := V) p‖ + 1)) := by
        gcongr
        exact hx.le.trans hrδ
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

omit [CompleteSpace V] in
/-- A map whose derivative has norm at most `K` everywhere is `K`-Lipschitz. -/
private theorem lipschitzWith_of_hasFDerivAt {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {F : V → X} {F' : V → V →L[ℝ] X} (hF : ∀ y, HasFDerivAt F (F' y) y)
    (hF' : ∀ y, ‖F' y‖ ≤ K) : LipschitzWith K F :=
  lipschitzWith_of_nnNorm_fderiv_le (fun y ↦ (hF y).differentiableAt) fun y ↦ by
    rw [(hF y).fderiv, ← NNReal.coe_le_coe, coe_nnNorm]
    exact hF' y

/-- The constants of the strict differentiability estimate: if `a₁, a₂ < r` with `r` at most
`c / (4 (K E + 1))`, and `n₂ ≤ n₀ + 1`, then
`K E (a₁ + a₂) + ε (B + 1 + E n₂) ≤ c` for `ε = c / (2 (B + 1 + E (n₀ + 1)))`. -/
private theorem mul_add_div_mul_le {E c a₁ a₂ n₀ n₂ r : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (h₁ : a₁ < r) (h₂ : a₂ < r) (hrc : r ≤ c / (4 * (K * E + 1))) (hn₀ : 0 ≤ n₀)
    (hn₂ : n₂ ≤ n₀ + 1) :
    K * E * (a₁ + a₂) + c / (2 * (B + 1 + E * (n₀ + 1))) * (B + 1 + E * n₂) ≤ c := by
  have t₁ : K * E * (a₁ + a₂) ≤ c / 2 := by
    calc K * E * (a₁ + a₂) ≤ K * E * (2 * (c / (4 * (K * E + 1)))) := by
          gcongr
          linarith
      _ = c / 2 * (K * E / (K * E + 1)) := by field_simp; ring
      _ ≤ c / 2 := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (by linarith))
  have t₂ : c / (2 * (B + 1 + E * (n₀ + 1))) * (B + 1 + E * n₂) ≤ c / 2 := by
    calc c / (2 * (B + 1 + E * (n₀ + 1))) * (B + 1 + E * n₂)
        ≤ c / (2 * (B + 1 + E * (n₀ + 1))) * (B + 1 + E * (n₀ + 1)) := by gcongr
      _ = c / 2 := by field_simp
  linarith

/-- **The linearization of the quasilinear section.** Let `2 < p < ∞`, let `b` be bounded, and
let the coefficients `A` and `G` be differentiable in the value `y`, with derivatives `A'` and
`G'` that are bounded and uniformly continuous in `y` uniformly in the domain point `z`, and
with `A`, `A'`, `G`, `G'` continuous in `(z, y)` and `A` bounded. Then the quasilinear section is
strictly differentiable at every `x₀ ∈ W^{1,p}(ℝ × S¹, V)`, and its derivative is the
linearization `h ↦ h_s + A(u₀) h_t + (A'(u₀) h) (b + ξ₀_t) + G'(u₀) h` at `x₀`. -/
theorem hasStrictFDerivAt_quasilinearSection (hp : 2 < p) (hpt : p ≠ ∞)
    (hAc : Continuous (Function.uncurry A)) (hGc : Continuous (Function.uncurry G))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w stripMeasure) (hb : AEStronglyMeasurable b stripMeasure)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hA : ∀ z y, HasFDerivAt (A z) (A' z y) y) (hA'K : ∀ z y, ‖A' z y‖ ≤ K)
    (hA'u : UniformEquicontinuous A') (hG : ∀ z y, HasFDerivAt (G z) (G' z y) y)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (hG'u : UniformEquicontinuous G') (x₀ : W1p V p) :
    HasStrictFDerivAt (quasilinearSection A G w b p)
      (quasilinearLinearization A A' G' w b p x₀) x₀ := by
  have hAL (z : ℝ × ℝ) := lipschitzWith_of_hasFDerivAt (hA z) (hA'K z)
  have hGL (z : ℝ × ℝ) := lipschitzWith_of_hasFDerivAt (hG z) (hG'K z)
  set E := ‖continuousValue (V := V) p‖
  have hE : 0 ≤ E := ContinuousLinearMap.opNorm_nonneg _
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  -- The scale `ε` of the Taylor remainders, the radius `δ` of uniform continuity of `A'` and `G'`
  -- at that scale, and the radius `r` in `W^{1,p}` within which both estimates apply.
  set ε := c / (2 * (B + 1 + E * (‖x₀‖ + 1)))
  have hε : 0 < ε := by positivity
  obtain ⟨δA, hδA, hA'δ⟩ :=
    (uniformEquicontinuous_iff (α := V →L[ℝ] V →L[ℝ] V) (β := V) (F := A')).1 hA'u ε hε
  obtain ⟨δG, hδG, hG'δ⟩ :=
    (uniformEquicontinuous_iff (α := V →L[ℝ] V) (β := V) (F := G')).1 hG'u ε hε
  set δ := min δA δG
  have hδ : 0 < δ := lt_min hδA hδG
  set r := min 1 (min (δ / (E + 1)) (c / (4 * (K * E + 1))))
  have hr : 0 < r := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hrδ : r ≤ δ / (E + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r ≤ c / (4 * (K * E + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine Metric.eventually_nhds_iff.2 ⟨r, hr, ?_⟩
  rintro ⟨x₁, x₂⟩ hx
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hx
  obtain ⟨h₁, h₂⟩ := hx
  simp only at h₁ h₂
  have hmA (z : ℝ × ℝ) := norm_sub_sub_le_of_dist_lt (hA z)
    (fun y hy ↦ hA'δ y _ (hy.trans_le (min_le_left _ _)) z)
    (dist_add_continuousValue_lt hδ hrδ h₁ (w z) z)
    (dist_add_continuousValue_lt hδ hrδ h₂ (w z) z)
  have hmG (z : ℝ × ℝ) := norm_sub_sub_le_of_dist_lt (hG z)
    (fun y hy ↦ hG'δ y _ (hy.trans_le (min_le_right _ _)) z)
    (dist_add_continuousValue_lt hδ hrδ h₁ (w z) z)
    (dist_add_continuousValue_lt hδ hrδ h₂ (w z) z)
  simp only [add_sub_add_left_eq_sub] at hmA hmG
  refine (norm_remainder_le hp hpt hAc hGc hA'c hG'c hw hb hbB hAC hAL hGL hA'K hG'K hε.le
    hmA hmG).trans ?_
  have hx₂ : ‖x₂‖ ≤ ‖x₀‖ + 1 := by
    have := norm_le_insert' x₂ x₀
    linarith [min_le_left 1 (min (δ / (E + 1)) (c / (4 * (K * E + 1))))]
  change _ ≤ c * ‖x₁ - x₂‖
  rw [mul_comm c]
  exact mul_le_mul_of_nonneg_left
    (mul_add_div_mul_le hB hE hc h₁ h₂ hrc (norm_nonneg _) hx₂) (norm_nonneg _)

end TauCeti.CylinderSobolev
