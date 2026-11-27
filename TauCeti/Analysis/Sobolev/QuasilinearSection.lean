/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.Equicontinuity
public import TauCeti.Analysis.Sobolev.Strip.Jet
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Equicontinuity
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Quasilinear first-order sections on spaces of `Lᵖ` jets with continuous representatives

A Floer cylinder, a Floer strip, and more generally a solution of a perturbed Cauchy–Riemann
equation on a domain of the plane, is a zero of a first-order operator of the form

`F(u) = ∂s u + A(z, u) ∂t u + G(z, u)`,

with coefficients `A(z, y) ∈ L(V, V)` and `G(z, y) ∈ V` depending on the domain point `z = (s, t)`
and on the value `y` of the map. For the Floer equation
`∂s u - X_{K_s}(u) + J(u) (∂t u - X_{K_t}(u)) = 0` one takes `A = J` and
`G = -X_{K_s} - J X_{K_t}`. Transversality and gluing study the zeros of `F` near a reference map
`w` in a chart `ξ ↦ w + ξ`, with `ξ` in a Sobolev space `W^{1,p}` for `p > 2`, the dimension of the
domain. This file constructs the map `ξ ↦ F(w + ξ) - F(w)` between Banach spaces and its derivative.

**The setting.** Let `μ` be a measure on the plane `ℝ × ℝ` and `X` a space of `Lᵖ(μ)` jets
`x = (ξ, ξ_s, ξ_t)`, that is a submodule of `Lᵖ(μ, V × V × V)`, whose values have continuous
representatives: a continuous linear map `e : X →L[ℝ] (ℝ × ℝ →ᵇ V)` with `e x` almost everywhere
equal to the value `ξ` of `x`. The Sobolev spaces `W^{1,p}` of the cylinder
(`TauCeti.CylinderSobolev.continuousValue`) and of the strip with boundary conditions
(`TauCeti.StripSobolev.continuousValueIccExtend`) are of this form for `2 < p < ∞`, by the Sobolev
embedding. The value `e x` is what the nonlinear coefficients are evaluated at, and the norm of `e`
bounds it uniformly by the norm of `x`; this is where `p > 2` enters.

**The section.** For `x = (ξ, ξ_s, ξ_t)` in `X` and a function `b` standing for `∂t w`, the
**quasilinear section** `TauCeti.quasilinearSection e A G w b` sends `x` to the class in `Lᵖ(μ)` of

`ξ_s + A(z, w + ξ) (b + ξ_t) - A(z, w) b + G(z, w + ξ) - G(z, w)`,

with `ξ` read through its continuous representative `e x`. When `b = ∂t w` and `x` is the jet of a
differentiable section `ξ`, this expression is `F(w + ξ) - F(w)`
(`TauCeti.quasilinearSection_ae_eq_of_ae_eq_jet`): the operator in the chart, minus its value at the
reference map, which need not lie in `Lᵖ`. When the expression does not lie in `Lᵖ`, the section
takes the value `0`. Its pointwise formula is `TauCeti.quasilinearSection_apply_ae`, under bounds
making every term of it lie in `Lᵖ`: `b` and `A` bounded, `A` and `G` Lipschitz in `y`, uniformly
in `z`. Under these hypotheses its zeros are the `x` in `X` solving the weak equation
`ξ_s + A(z, w + ξ) (b + ξ_t) - A(z, w) b + G(z, w + ξ) - G(z, w) = 0` almost everywhere; that such a
zero is a classical solution is elliptic regularity, which is not proved here. For a reference map
with `F(w)` in `Lᵖ`, such as a pre-glued map, the section plus the constant `F(w)` agrees with
`ξ ↦ F(w + ξ)` on jets of differentiable sections, an affine shift with the same derivative.

**The linearization.** At `x₀ = (ξ₀, ξ₀_s, ξ₀_t)`, with `u₀ = w + ξ₀`, the derivative of the
section is the operator `TauCeti.quasilinearLinearization e A A' G' w b x₀`,

`h ↦ h_s + A(z, u₀) h_t + (A'(z, u₀) h) (b + ξ₀_t) + G'(z, u₀) h`,

for the derivatives `A'`, `G'` of `A`, `G` in `y` (`TauCeti.quasilinearLinearization_apply_ae`). Its
zeroth-order coefficient contains the weak derivative `ξ₀_t`, which lies only in `Lᵖ`; the term
`(A'(z, u₀) h) ξ₀_t` lies in `Lᵖ` because `h` is bounded by `‖e‖` times its norm in `X`.

**Strict differentiability** (`TauCeti.hasStrictFDerivAt_quasilinearSection`).
If `A'` and `G'` are bounded, and uniformly continuous in `y` uniformly in `z`
(`UniformEquicontinuous`), the section is strictly differentiable at every `x₀`, with derivative
the linearization. The first-order remainder of the section at `x₁`, `x₂` near `x₀` is the sum of
four terms: `(A(u₁) - A(u₀)) (ξ₁_t - ξ₂_t)`, which is small since `e` keeps `u₁` uniformly close
to `u₀`; the Taylor remainders of `A` and `G` between `u₂` and `u₁`, which the mean value
inequality bounds by the oscillation of `A'` and `G'` near `u₀`; and
`(A'(u₀) (ξ₁ - ξ₂)) (ξ₂_t - ξ₀_t)`, which is small since `ξ₂_t` is close to `ξ₀_t` in `Lᵖ`. Strict
differentiability is what the implicit function theorem and the Sard–Smale theorem ask of the
section.

The analogue for paths on the line, the trajectory section of a vector field, is
`TauCeti.WeakDerivStep.trajectorySection`.

## Main definitions

* `TauCeti.quasilinearSection`: the section
  `x ↦ ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)` from `X` to `Lᵖ(μ)`.
* `TauCeti.quasilinearLinearization`: its linearization at `x₀`.

## Main results

* `TauCeti.quasilinearSection_apply_ae`: the pointwise formula of the section.
* `TauCeti.quasilinearSection_zero`: it vanishes at the reference map.
* `TauCeti.quasilinearSection_ae_eq_of_ae_eq_jet`: its value on the jet of a section.
* `TauCeti.quasilinearLinearization_apply_ae`: the pointwise formula of the linearization.
* `TauCeti.hasStrictFDerivAt_quasilinearSection`: for coefficients differentiable in `y` with
  bounded, continuous, uniformly equicontinuous derivatives, the section is strictly
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

namespace TauCeti

open StripSobolev (jet jet_apply)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure (ℝ × ℝ)} {X : Submodule ℝ (Lp (V × V × V) p μ)}
  {e : X →L[ℝ] (ℝ × ℝ →ᵇ V)}

/-! ### Preliminaries -/

omit [NormedSpace ℝ V] in
/-- A coefficient continuous jointly in the domain point and the value, evaluated along a
measurable map, is measurable. -/
private theorem aestronglyMeasurable_comp_uncurry {Y : Type*} [TopologicalSpace Y]
    {A : ℝ × ℝ → V → Y} (hA : Continuous (Function.uncurry A)) {u : ℝ × ℝ → V}
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun z ↦ A z (u z)) μ :=
  hA.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hu)

/-! ### The section -/

variable {A : ℝ × ℝ → V → V →L[ℝ] V} {G : ℝ × ℝ → V → V} {w b : ℝ × ℝ → V}

/-- The pointwise expression `ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)` of the
quasilinear section at an element `x = (ξ, ξ_s, ξ_t)` of `X`. -/
private def sectionFun (e : X →L[ℝ] (ℝ × ℝ →ᵇ V)) (A : ℝ × ℝ → V → V →L[ℝ] V)
    (G : ℝ × ℝ → V → V) (w b : ℝ × ℝ → V) (x : X) (z : ℝ × ℝ) : V :=
  ((x : Lp (V × V × V) p μ) z).2.1 +
    (A z (w z + e x z) (b z + ((x : Lp (V × V × V) p μ) z).2.2) - A z (w z) (b z)) +
    (G z (w z + e x z) - G z (w z))

/-- Under bounds on `b` and `A` and Lipschitz bounds on `A` and `G` in the value, the pointwise
expression of the quasilinear section lies in `Lᵖ`. -/
private theorem memLp_sectionFun (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hA : Continuous (Function.uncurry A)) (hG : Continuous (Function.uncurry G))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ) {B C : ℝ} {K L : ℝ≥0}
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C) (hAL : ∀ z, LipschitzWith K (A z))
    (hGL : ∀ z, LipschitzWith L (G z)) (x : X) :
    MemLp (sectionFun e A G w b x) p μ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hAC 0 0)
  have hx := Lp.aestronglyMeasurable (x : Lp (V × V × V) p μ)
  have hu : AEStronglyMeasurable (fun z ↦ w z + e x z) μ :=
    hw.add (e x).continuous.aestronglyMeasurable
  have hAd := ((ContinuousLinearMap.apply ℝ V).aestronglyMeasurable_comp₂ (hb.add hx.snd.snd)
    (aestronglyMeasurable_comp_uncurry hA hu)).sub
    ((ContinuousLinearMap.apply ℝ V).aestronglyMeasurable_comp₂ hb
      (aestronglyMeasurable_comp_uncurry hA hw))
  have hGd :=
    (aestronglyMeasurable_comp_uncurry hG hu).sub (aestronglyMeasurable_comp_uncurry hG hw)
  refine (Lp.memLp (x : Lp (V × V × V) p μ)).of_le_mul (c := 1 + C + K * B + L)
    ((hx.snd.fst.add hAd).add hGd) ?_
  filter_upwards [he x] with z hz
  set v := (x : Lp (V × V × V) p μ) z
  set ξ := e x z
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
  calc ‖sectionFun e A G w b x z‖
      ≤ ‖v.2.1‖ + ‖A z (w z + ξ) (b z + v.2.2) - A z (w z) (b z)‖ +
          ‖G z (w z + ξ) - G z (w z)‖ := norm_add₃_le
    _ ≤ ‖v‖ + (C * ‖v‖ + K * ‖v‖ * B) + L * ‖v‖ := by gcongr
    _ = (1 + C + K * B + L) * ‖v‖ := by ring

open scoped Classical in
/-- **The quasilinear section** of the operator `F(u) = ∂s u + A(z, u) ∂t u + G(z, u)` around a
reference map `w`, with `b` standing for `∂t w`, on a space `X` of `Lᵖ(μ)` jets whose values have
the continuous representatives `e`: the map from `X` to `Lᵖ(μ)` sending `x = (ξ, ξ_s, ξ_t)` to the
class of `ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)`, with `ξ` read through `e x`. When
`b = ∂t w` and `x` is the jet of a differentiable section `ξ`, this is `F(w + ξ) - F(w)`
(`TauCeti.quasilinearSection_ae_eq_of_ae_eq_jet`). The expression lies in `Lᵖ` under the bounds of
`TauCeti.quasilinearSection_apply_ae`; when it does not, the section takes the value `0`. -/
def quasilinearSection (e : X →L[ℝ] (ℝ × ℝ →ᵇ V)) (A : ℝ × ℝ → V → V →L[ℝ] V)
    (G : ℝ × ℝ → V → V) (w b : ℝ × ℝ → V) (x : X) : Lp V p μ :=
  if h : MemLp (sectionFun e A G w b x) p μ then h.toLp _ else 0

/-- **The pointwise formula of the quasilinear section.** Let `e` give continuous representatives
of the values of the elements of `X`. For coefficients `A` and `G` continuous in `(z, y)`, `A`
bounded, `A` and `G` Lipschitz in `y` uniformly in `z`, and `b` bounded, the section at
`x = (ξ, ξ_s, ξ_t)` is almost everywhere `ξ_s + A(w + ξ) (b + ξ_t) - A(w) b + G(w + ξ) - G(w)`. -/
theorem quasilinearSection_apply_ae
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hA : Continuous (Function.uncurry A)) (hG : Continuous (Function.uncurry G))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ)
    {B C : ℝ} {K L : ℝ≥0} (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hAL : ∀ z, LipschitzWith K (A z)) (hGL : ∀ z, LipschitzWith L (G z)) (x : X) :
    quasilinearSection e A G w b x =ᵐ[μ] fun z ↦
      ((x : Lp (V × V × V) p μ) z).2.1 +
        (A z (w z + e x z) (b z + ((x : Lp (V × V × V) p μ) z).2.2) - A z (w z) (b z)) +
        (G z (w z + e x z) - G z (w z)) := by
  have h := memLp_sectionFun he hA hG hw hb hbB hAC hAL hGL x
  have he : quasilinearSection e A G w b x = h.toLp _ := by simp [quasilinearSection, h]
  rw [he]
  exact h.coeFn_toLp

/-- The quasilinear section vanishes at the reference map. -/
@[simp]
theorem quasilinearSection_zero : quasilinearSection e A G w b 0 = 0 := by
  rw [quasilinearSection]
  split_ifs with h
  · refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [h.coeFn_toLp, Lp.coeFn_zero (V × V × V) p μ] with z hz h0
    rw [hz, sectionFun, Submodule.coe_zero, h0]
    simp
  · rfl

/-- **The section on jets of sections.** If an element `x` of `X` is almost everywhere the jet of
a section `ξ`, the quasilinear section at `x` is computed from the classical derivatives of `ξ`:
almost everywhere it is `∂s ξ + A(w + ξ) (b + ∂t ξ) - A(w) b + G(w + ξ) - G(w)`. -/
theorem quasilinearSection_ae_eq_of_ae_eq_jet
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hA : Continuous (Function.uncurry A)) (hG : Continuous (Function.uncurry G))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ)
    {B C : ℝ} {K L : ℝ≥0} (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hAL : ∀ z, LipschitzWith K (A z)) (hGL : ∀ z, LipschitzWith L (G z)) {x : X}
    {ξ : ℝ × ℝ → V} (hx : (x : Lp (V × V × V) p μ) =ᵐ[μ] jet ξ) :
    quasilinearSection e A G w b x =ᵐ[μ] fun z ↦
      fderiv ℝ ξ z (1, 0) + (A z (w z + ξ z) (b z + fderiv ℝ ξ z (0, 1)) - A z (w z) (b z)) +
        (G z (w z + ξ z) - G z (w z)) := by
  filter_upwards [quasilinearSection_apply_ae he hA hG hw hb hbB hAC hAL hGL x, hx, he x]
    with z hz hj hv
  rw [hz, ← hv, hj, jet_apply]

/-! ### The linearization -/

variable {A' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V} {G' : ℝ × ℝ → V → V →L[ℝ] V}

/-- The pointwise expression `h_s + A(u₀) h_t + (A'(u₀) h) b + G'(u₀) h + (A'(u₀) h) ξ₀_t` of the
linearization at `x₀` of the quasilinear section, applied to `h`, with `u₀ = w + ξ₀`. The value
`h` enters the last term through its continuous representative and the others through its jet. -/
private def linFun (e : X →L[ℝ] (ℝ × ℝ →ᵇ V)) (A : ℝ × ℝ → V → V →L[ℝ] V)
    (A' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V) (G' : ℝ × ℝ → V → V →L[ℝ] V)
    (w b : ℝ × ℝ → V) (x₀ h : X) (z : ℝ × ℝ) : V :=
  ((h : Lp (V × V × V) p μ) z).2.1 +
    A z (w z + e x₀ z) ((h : Lp (V × V × V) p μ) z).2.2 +
    A' z (w z + e x₀ z) ((h : Lp (V × V × V) p μ) z).1 (b z) +
    G' z (w z + e x₀ z) ((h : Lp (V × V × V) p μ) z).1 +
    A' z (w z + e x₀ z) (e h z) ((x₀ : Lp (V × V × V) p μ) z).2.2

/-- The pointwise bound on the expression of the linearization:
`‖h_s + A(u₀) h_t + (A'(u₀) h) b + G'(u₀) h + (A'(u₀) h) ξ₀_t‖` is at most
`(1 + C + K B + L) ‖h‖ + K ‖h‖_∞ ‖ξ₀_t‖`, the jets being measured pointwise. -/
private theorem norm_linFun_le {B C K L : ℝ} (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (x₀ h : X) (z : ℝ × ℝ) :
    ‖linFun e A A' G' w b x₀ h z‖ ≤
      (1 + C + K * B + L) * ‖(h : Lp (V × V × V) p μ) z‖ +
        K * ‖e h‖ * ‖(x₀ : Lp (V × V × V) p μ) z‖ := by
  have hK : 0 ≤ K := (norm_nonneg (A' 0 0)).trans (hA'K 0 0)
  set v := (h : Lp (V × V × V) p μ) z
  set v₀ := (x₀ : Lp (V × V × V) p μ) z
  set u₀ := w z + e x₀ z
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
  have hA't : ‖A' z u₀ (e h z) v₀.2.2‖ ≤ K * ‖e h‖ * ‖v₀‖ :=
    ((A' z u₀ _).le_opNorm _).trans (mul_le_mul
      (((A' z u₀).le_of_opNorm_le (hA'K z u₀) _).trans
        (by gcongr; exact BoundedContinuousFunction.norm_coe_le_norm _ _)) h₀ (norm_nonneg _)
      (by positivity))
  have htri : ‖linFun e A A' G' w b x₀ h z‖ ≤ ‖v.2.1‖ + ‖A z u₀ v.2.2‖ + ‖A' z u₀ v.1 (b z)‖ +
      ‖G' z u₀ v.1‖ + ‖A' z u₀ (e h z) v₀.2.2‖ :=
    (norm_add_le _ _).trans (add_le_add_left norm_add₄_le _)
  linarith

/-- The pointwise expression of the linearization at `x₀`, applied to `h`, is a.e. strongly
measurable. -/
private theorem aestronglyMeasurable_linFun (hAc : Continuous (Function.uncurry A))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ)
    (x₀ h : X) : AEStronglyMeasurable (linFun e A A' G' w b x₀ h) μ := by
  have hu₀ : AEStronglyMeasurable (fun z ↦ w z + e x₀ z) μ :=
    hw.add (e x₀).continuous.aestronglyMeasurable
  have hx₀ := Lp.aestronglyMeasurable (x₀ : Lp (V × V × V) p μ)
  have hj := Lp.aestronglyMeasurable (h : Lp (V × V × V) p μ)
  have hA'u := aestronglyMeasurable_comp_uncurry hA'c hu₀
  -- Elaboration of `(ContinuousLinearMap.apply ℝ (V →L[ℝ] V)).aestronglyMeasurable_comp₂` cannot
  -- unify the normed and strong topologies on `V →L[ℝ] V →L[ℝ] V`; use `Continuous.clm_apply`.
  have hA'h := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hA'u hj.fst
  exact (((hj.snd.fst.add ((ContinuousLinearMap.apply ℝ V).aestronglyMeasurable_comp₂
    hj.snd.snd (aestronglyMeasurable_comp_uncurry hAc hu₀))).add
    ((ContinuousLinearMap.apply ℝ V).aestronglyMeasurable_comp₂ hb hA'h)).add
    ((ContinuousLinearMap.apply ℝ V).aestronglyMeasurable_comp₂ hj.fst
      (aestronglyMeasurable_comp_uncurry hG'c hu₀))).add
    ((ContinuousLinearMap.apply ℝ V).aestronglyMeasurable_comp₂ hx₀.snd.snd
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hA'u
        (e h).continuous.aestronglyMeasurable))

variable {B C : ℝ} {K L : ℝ≥0}

/-- Under bounds on `b`, `A`, `A'` and `G'`, the pointwise expression of the linearization at `x₀`
is the pointwise expression of a continuous linear map from `X` to `Lᵖ`. -/
private theorem exists_linFun (hAc : Continuous (Function.uncurry A))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C) (hA'K : ∀ z y, ‖A' z y‖ ≤ K)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (x₀ : X) :
    ∃ T : X →L[ℝ] Lp V p μ, ∀ h, T h =ᵐ[μ] linFun e A A' G' w b x₀ h := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hAC 0 0)
  have hmem (h : X) : MemLp (linFun e A A' G' w b x₀ h) p μ := by
    have hg : MemLp (fun z ↦ (1 + C + K * B + L) * ‖(h : Lp (V × V × V) p μ) z‖ +
        K * ‖e h‖ * ‖(x₀ : Lp (V × V × V) p μ) z‖) p μ :=
      ((Lp.memLp _).norm.const_mul _).add ((Lp.memLp _).norm.const_mul _)
    refine hg.of_le ?_ (ae_of_all _ fun z ↦
      (norm_linFun_le hbB hAC hA'K hG'K x₀ h z).trans (Real.le_norm_self _))
    exact aestronglyMeasurable_linFun hAc hA'c hG'c hw hb x₀ h
  let T : X →ₗ[ℝ] Lp V p μ :=
    { toFun h := (hmem h).toLp _
      map_add' h₁ h₂ := by
        refine Lp.ext ?_
        filter_upwards [(hmem (h₁ + h₂)).coeFn_toLp,
          Lp.coeFn_add ((hmem h₁).toLp _) ((hmem h₂).toLp _), (hmem h₁).coeFn_toLp,
          (hmem h₂).coeFn_toLp, Lp.coeFn_add (h₁ : Lp (V × V × V) p μ) h₂]
          with z e₁ e₂ e₃ e₄ e₅
        rw [e₁, e₂, Pi.add_apply, e₃, e₄]
        simp only [linFun, Submodule.coe_add, e₅, Pi.add_apply, map_add, Prod.fst_add,
          Prod.snd_add, add_apply]
        abel
      map_smul' c h := by
        refine Lp.ext ?_
        filter_upwards [(hmem (c • h)).coeFn_toLp, Lp.coeFn_smul c ((hmem h).toLp _),
          (hmem h).coeFn_toLp, Lp.coeFn_smul c (h : Lp (V × V × V) p μ)] with z e₁ e₂ e₃ e₄
        rw [e₁, RingHom.id_apply, e₂, Pi.smul_apply, e₃]
        simp only [linFun, Submodule.coe_smul, e₄, Pi.smul_apply, map_smul, Prod.smul_fst,
          Prod.smul_snd, smul_apply, smul_add] }
  refine ⟨T.mkContinuous ((1 + C + K * B + L) + K * ‖e‖ * ‖x₀‖)
    fun h ↦ ?_, fun h ↦ (hmem h).coeFn_toLp⟩
  have hle := Lp.norm_le_add_of_ae_norm_le (f := (hmem h).toLp _)
    (g := (h : Lp (V × V × V) p μ)) (h := (x₀ : Lp (V × V × V) p μ))
    (a := 1 + C + K * B + L) (b := K * ‖e h‖) (by positivity) (by positivity) (by
      filter_upwards [(hmem h).coeFn_toLp] with z hz
      rw [hz]
      exact norm_linFun_le hbB hAC hA'K hG'K x₀ h z)
  have hE := e.le_opNorm h
  calc ‖T h‖ ≤ (1 + C + K * B + L) * ‖h‖ + K * ‖e h‖ * ‖x₀‖ := hle
    _ ≤ (1 + C + K * B + L) * ‖h‖ + K * (‖e‖ * ‖h‖) * ‖x₀‖ := by gcongr
    _ = _ := by ring

open scoped Classical in
/-- **The linearization of the quasilinear section** at `x₀ = (ξ₀, ξ₀_s, ξ₀_t)`: the continuous
linear map from `X` to `Lᵖ(μ)` sending `h` to the class of
`h_s + A(u₀) h_t + (A'(u₀) h) (b + ξ₀_t) + G'(u₀) h`, with `u₀ = w + ξ₀` and `A'`, `G'` the
derivatives of `A`, `G` in the value. The value of `h` enters the term with `ξ₀_t`, which lies
only in `Lᵖ`, through its continuous representative `e h`. When no continuous linear map with this
pointwise expression exists, the linearization is `0`; under the bounds of
`TauCeti.quasilinearLinearization_apply_ae` one exists, and it is unique. When `A'`, `G'` are the
derivatives of `A`, `G` in the value and the continuity, bound and uniform equicontinuity
hypotheses of `TauCeti.hasStrictFDerivAt_quasilinearSection` hold, it is the strict derivative of
`TauCeti.quasilinearSection` at `x₀`. -/
def quasilinearLinearization (e : X →L[ℝ] (ℝ × ℝ →ᵇ V)) (A : ℝ × ℝ → V → V →L[ℝ] V)
    (A' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V) (G' : ℝ × ℝ → V → V →L[ℝ] V) (w b : ℝ × ℝ → V)
    (x₀ : X) : X →L[ℝ] Lp V p μ :=
  if H : ∃ T : X →L[ℝ] Lp V p μ, ∀ h, T h =ᵐ[μ] linFun e A A' G' w b x₀ h then H.choose else 0

/-- **The pointwise formula of the linearization.** For coefficients `A`, `A'`, `G'` continuous in
`(z, y)` and bounded, and `b` bounded, the linearization at `x₀ = (ξ₀, ξ₀_s, ξ₀_t)` applied to
`h = (η, η_s, η_t)` is almost everywhere
`η_s + A(u₀) η_t + (A'(u₀) η) b + G'(u₀) η + (A'(u₀) η) ξ₀_t`, with `u₀ = w + ξ₀`, and with `ξ₀`
and the `η` of the last term read through the continuous representatives `e x₀` and `e h`. -/
theorem quasilinearLinearization_apply_ae (hAc : Continuous (Function.uncurry A))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (x₀ h : X) :
    quasilinearLinearization e A A' G' w b x₀ h =ᵐ[μ] fun z ↦
      ((h : Lp (V × V × V) p μ) z).2.1 +
        A z (w z + e x₀ z) ((h : Lp (V × V × V) p μ) z).2.2 +
        A' z (w z + e x₀ z) ((h : Lp (V × V × V) p μ) z).1 (b z) +
        G' z (w z + e x₀ z) ((h : Lp (V × V × V) p μ) z).1 +
        A' z (w z + e x₀ z) (e h z) ((x₀ : Lp (V × V × V) p μ) z).2.2 := by
  have H := exists_linFun hAc hA'c hG'c hw hb hbB hAC hA'K hG'K x₀ (e := e)
  rw [quasilinearLinearization, dite_eq_left_of_eq_true (eq_true H)]
  exact H.choose_spec h

/-! ### Strict differentiability -/

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
`‖x₁ - x₂‖ (K E (‖x₁ - x₀‖ + ‖x₂ - x₀‖) + ε (B + 1 + E ‖x₂‖))`, with `E` the norm of `e`. -/
private theorem norm_remainder_le
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hAc : Continuous (Function.uncurry A)) (hGc : Continuous (Function.uncurry G))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C) (hAL : ∀ z, LipschitzWith K (A z))
    (hGL : ∀ z, LipschitzWith L (G z)) (hA'K : ∀ z y, ‖A' z y‖ ≤ K)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) {x₀ x₁ x₂ : X} {ε : ℝ} (hε : 0 ≤ ε)
    (hmA : ∀ z, ‖A z (w z + e x₁ z) - A z (w z + e x₂ z) -
      A' z (w z + e x₀ z) (e x₁ z - e x₂ z)‖ ≤ ε * ‖e x₁ z - e x₂ z‖)
    (hmG : ∀ z, ‖G z (w z + e x₁ z) - G z (w z + e x₂ z) -
      G' z (w z + e x₀ z) (e x₁ z - e x₂ z)‖ ≤ ε * ‖e x₁ z - e x₂ z‖) :
    ‖quasilinearSection e A G w b x₁ - quasilinearSection e A G w b x₂ -
        quasilinearLinearization e A A' G' w b x₀ (x₁ - x₂)‖ ≤
      ‖x₁ - x₂‖ * (K * ‖e‖ * (‖x₁ - x₀‖ + ‖x₂ - x₀‖) + ε * (B + 1 + ‖e‖ * ‖x₂‖)) := by
  set E := ‖e‖
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  have key := Lp.norm_le_add_add_of_ae_norm_le
    (f := quasilinearSection e A G w b x₁ - quasilinearSection e A G w b x₂ -
      quasilinearLinearization e A A' G' w b x₀ (x₁ - x₂))
    (g := ((x₁ - x₂ : X) : Lp (V × V × V) p μ))
    (h := (x₂ : Lp (V × V × V) p μ))
    (k := ((x₂ - x₀ : X) : Lp (V × V × V) p μ))
    (a := K * (E * ‖x₁ - x₀‖) + ε * B + ε) (b := ε * (E * ‖x₁ - x₂‖))
    (c := K * (E * ‖x₁ - x₂‖)) (by positivity) (by positivity) (by positivity) (by
      filter_upwards [Lp.coeFn_sub (quasilinearSection e A G w b x₁ -
          quasilinearSection e A G w b x₂) (quasilinearLinearization e A A' G' w b x₀ (x₁ - x₂)),
        Lp.coeFn_sub (quasilinearSection e A G w b x₁) (quasilinearSection e A G w b x₂),
        quasilinearSection_apply_ae he hAc hGc hw hb hbB hAC hAL hGL x₁,
        quasilinearSection_apply_ae he hAc hGc hw hb hbB hAC hAL hGL x₂,
        quasilinearLinearization_apply_ae hAc hA'c hG'c hw hb hbB hAC hA'K hG'K x₀ (x₁ - x₂),
        Lp.coeFn_sub (x₁ : Lp (V × V × V) p μ) x₂, Lp.coeFn_sub (x₂ : Lp (V × V × V) p μ) x₀,
        he (x₁ - x₂)] with z e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      rw [map_sub e, sub_apply] at e₅ e₈
      rw [e₁, Pi.sub_apply, e₂, Pi.sub_apply, e₃, e₄, e₅]
      exact norm_remainder_apply_le hbB hAL hA'K z (by rw [Submodule.coe_sub, e₆, Pi.sub_apply])
        (by rw [Submodule.coe_sub, e₇, Pi.sub_apply]) e₈ hε
        (e.norm_apply_sub_apply_le x₁ x₀ z) (e.norm_apply_sub_apply_le x₁ x₂ z) (hmA z) (hmG z))
  refine key.trans_eq ?_
  simp only [Submodule.norm_coe]
  ring

/-- Elements of `X` within `r ≤ δ / (E + 1)` of `x₀`, with `E` the norm of `e`, have continuous
representatives uniformly within `δ` of that of `x₀`. -/
private theorem dist_add_apply_lt {x x₀ : X} {δ r : ℝ} (hδ : 0 < δ)
    (hrδ : r ≤ δ / (‖e‖ + 1)) (hx : ‖x - x₀‖ < r) (y : V)
    (z : ℝ × ℝ) : dist (y + e x z) (y + e x₀ z) < δ := by
  rw [dist_add_left, dist_eq_norm]
  calc ‖e x z - e x₀ z‖
      ≤ ‖e‖ * ‖x - x₀‖ := e.norm_apply_sub_apply_le x x₀ z
    _ ≤ ‖e‖ * (δ / (‖e‖ + 1)) := by
        gcongr
        exact hx.le.trans hrδ
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg e]

/-- **The Taylor remainder along the continuous representatives.** If the derivatives `F' z` of
the maps `F z` oscillate by less than `ε` at distance less than `δ`, uniformly in `z`, then for
`x₁`, `x₂` within `r ≤ δ / (E + 1)` of `x₀`, the remainder of `F z` between `w + ξ₂` and `w + ξ₁`
relative to `F' z (w + ξ₀)` is at most `ε ‖ξ₁ - ξ₂‖`. This is the mean value inequality on the ball
of radius `δ` around `w + ξ₀`. -/
private theorem norm_sub_sub_apply_le {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {F : ℝ × ℝ → V → Y} {F' : ℝ × ℝ → V → V →L[ℝ] Y}
    (hF : ∀ z y, HasFDerivAt (F z) (F' z y) y) {δ ε r : ℝ} (hδ : 0 < δ)
    (hosc : ∀ y y', dist y y' < δ → ∀ z, dist (F' z y) (F' z y') < ε)
    (hrδ : r ≤ δ / (‖e‖ + 1)) {x₀ x₁ x₂ : X}
    (h₁ : ‖x₁ - x₀‖ < r) (h₂ : ‖x₂ - x₀‖ < r) (z : ℝ × ℝ) :
    ‖F z (w z + e x₁ z) - F z (w z + e x₂ z) - F' z (w z + e x₀ z) (e x₁ z - e x₂ z)‖ ≤
      ε * ‖e x₁ z - e x₂ z‖ := by
  have h := (convex_ball _ δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun y _ ↦ (hF z y).hasFDerivWithinAt)
    (fun y hy ↦ by
      rw [← dist_eq_norm]
      exact (hosc y _ (mem_ball.1 hy) z).le)
    (dist_add_apply_lt hδ hrδ h₂ (w z) z)
    (dist_add_apply_lt hδ hrδ h₁ (w z) z)
  simpa only [add_sub_add_left_eq_sub] using h

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

/-- **The linearization of the quasilinear section.** Let `e` give continuous representatives of
the values of the elements of `X`, and let `b` be bounded. Let the coefficients `A` and `G` be
differentiable in the value `y`, with derivatives `A'` and `G'` that are bounded and uniformly
continuous in `y` uniformly in the domain point `z`, and with `A`, `A'`, `G`, `G'` continuous in
`(z, y)` and `A` bounded. Then the quasilinear section is strictly differentiable at every
`x₀ ∈ X`, and its derivative is the linearization
`h ↦ h_s + A(u₀) h_t + (A'(u₀) h) (b + ξ₀_t) + G'(u₀) h` at `x₀`. -/
theorem hasStrictFDerivAt_quasilinearSection
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hAc : Continuous (Function.uncurry A)) (hGc : Continuous (Function.uncurry G))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ)
    (hbB : ∀ z, ‖b z‖ ≤ B) (hAC : ∀ z y, ‖A z y‖ ≤ C)
    (hA : ∀ z y, HasFDerivAt (A z) (A' z y) y) (hA'K : ∀ z y, ‖A' z y‖ ≤ K)
    (hA'u : UniformEquicontinuous A') (hG : ∀ z y, HasFDerivAt (G z) (G' z y) y)
    (hG'K : ∀ z y, ‖G' z y‖ ≤ L) (hG'u : UniformEquicontinuous G') (x₀ : X) :
    HasStrictFDerivAt (quasilinearSection e A G w b)
      (quasilinearLinearization e A A' G' w b x₀) x₀ := by
  have hAL (z : ℝ × ℝ) : LipschitzWith K (A z) := lipschitzOnWith_univ.1
    (convex_univ.lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
      (fun y _ ↦ (hA z y).hasFDerivWithinAt) fun y _ ↦ NNReal.coe_le_coe.1 (hA'K z y))
  have hGL (z : ℝ × ℝ) : LipschitzWith L (G z) := lipschitzOnWith_univ.1
    (convex_univ.lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
      (fun y _ ↦ (hG z y).hasFDerivWithinAt) fun y _ ↦ NNReal.coe_le_coe.1 (hG'K z y))
  set E := ‖e‖
  have hE : 0 ≤ E := norm_nonneg e
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  -- The scale `ε` of the Taylor remainders, the radius `δ` of uniform continuity of `A'` and `G'`
  -- at that scale, and the radius `r` in `X` within which both estimates apply.
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
  have hmA := norm_sub_sub_apply_le (w := w) hA hδ
    (fun y y' h ↦ hA'δ y y' (h.trans_le (min_le_left _ _))) hrδ h₁ h₂
  have hmG := norm_sub_sub_apply_le (w := w) hG hδ
    (fun y y' h ↦ hG'δ y y' (h.trans_le (min_le_right _ _))) hrδ h₁ h₂
  refine (norm_remainder_le he hAc hGc hA'c hG'c hw hb hbB hAC hAL hGL hA'K hG'K hε.le
    hmA hmG).trans ?_
  have hx₂ : ‖x₂‖ ≤ ‖x₀‖ + 1 := by
    have := norm_le_insert' x₂ x₀
    linarith [min_le_left 1 (min (δ / (E + 1)) (c / (4 * (K * E + 1))))]
  rw [mul_comm c]
  exact mul_le_mul_of_nonneg_left
    (mul_add_div_mul_le hB hE hc h₁ h₂ hrc (norm_nonneg _) hx₂) (norm_nonneg _)

end TauCeti
