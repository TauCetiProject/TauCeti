/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.Analysis.Complex.Conformal.Reflection.Line

/-!
# The pre-Schwarzian derivative along a straight boundary arc

A holomorphic function whose boundary values on a real interval run along an affine line continues
across that interval by Schwarz reflection, and the continuation `F` intertwines conjugation with
the reflection in the target line: `F (conj z) = τ (F z)`. Every reflection in a line of direction
`b` has the affine shape `τ w = c + u * conj w` with `u = b / conj b`, and this file draws out what
that shape forces on the derivatives of `F`.

Differentiating the identity once removes the additive constant, so `deriv F` satisfies the same
identity with `c = 0`; differentiating a second time leaves that identity unchanged. The factor `u`
therefore cancels from the quotient `deriv (deriv F) / deriv F`, the **pre-Schwarzian derivative**
`logDeriv (deriv F)`, which obeys the bare conjugation symmetry
`logDeriv (deriv F) (conj z) = conj (logDeriv (deriv F) z)` and is consequently *real on the real
axis*. Nothing about the target line survives into that conclusion; only the source line is
remembered. What the target line does control is `deriv F` itself, which on the real axis is a real
multiple of the direction `b`: the boundary arc runs along the target line.

Differentiability of `F` is not needed for any of this. The identity is an equality between
`deriv`s, and `deriv` of a function that is not differentiable at a point is `0` there, which
satisfies the identity as well.

These are the local statements the Schwarz--Christoffel formula needs in its converse direction. A
conformal map of the upper half-plane onto a polygon carries each boundary interval between two
consecutive prevertices into one side, hence has real pre-Schwarzian there; assembling those
intervals and reading off the poles left at the prevertices is what identifies the pre-Schwarzian
with `∑ i, e i / (z - a i)`, the pre-Schwarzian derivative of the Schwarz--Christoffel map
(`TauCeti.logDeriv_deriv_schwarzChristoffelPrimitive`).

The source line is the real axis throughout, as in
`TauCeti/Analysis/Complex/Conformal/Reflection/Basic.lean`: unlike holomorphy, the pre-Schwarzian
derivative is not invariant under an affine change of the source coordinate -- precomposing with
`w ↦ p + a * w` multiplies it by `a` -- so a general source line would only move that factor into
the statement, and the real axis is the coordinate the Schwarz--Christoffel prevertices live in.
The target line is arbitrary, since a polygon's sides are.

The abstract statements assume only the reflection identity, and so apply to any extension however
obtained. The concrete ones are about the explicit witness
`TauCeti.lineSchwarzReflection 0 1 q b f` of the reflection principle across the real axis with an
arbitrary target line; its holomorphy and its agreement with `f` on the closed upper half-plane are
`TauCeti.differentiableOn_lineSchwarzReflection_of_symmetric` and
`TauCeti.lineSchwarzReflection_of_coord_im_nonneg`.

## Main results

* `TauCeti.deriv_conj_eq_mul_conj_deriv` and
  `TauCeti.deriv_deriv_conj_eq_mul_conj_deriv_deriv` -- the first and second derivatives of a
  function intertwining conjugation with an affine reflection satisfy the same intertwining
  relation, with the additive constant gone.
* `TauCeti.logDeriv_deriv_conj_eq_conj_logDeriv_deriv` -- the pre-Schwarzian derivative
  intertwines conjugation with conjugation.
* `TauCeti.im_logDeriv_deriv_eq_zero` -- so it is real on the real axis.
* `TauCeti.im_div_deriv_lineSchwarzReflection_eq_zero` -- on the real axis the derivative of the
  reflected extension is a real multiple of the direction of the target line.
* `TauCeti.im_logDeriv_deriv_lineSchwarzReflection_eq_zero` -- the pre-Schwarzian derivative of
  the reflected extension is real on the real axis.
* `TauCeti.eqOn_logDeriv_deriv_lineSchwarzReflection` -- it extends the pre-Schwarzian derivative
  of the original branch.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

namespace TauCeti

open Complex Set Topology

variable {Ω : Set ℂ} {F f : ℂ → ℂ} {c u q b : ℂ}

/-- **The derivative inherits an affine reflection identity, without its constant.** If `F`
carries conjugation to the affine reflection `w ↦ c + u * conj w` on a conjugation-symmetric open
set, then `deriv F` carries conjugation to `w ↦ u * conj w`. No differentiability is assumed: the
identity also holds, with both sides `0`, wherever `F` fails to be differentiable. -/
theorem deriv_conj_eq_mul_conj_deriv (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    deriv F ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (deriv F z) := by
  -- Read the identity as `F = c + u * (conj ∘ F ∘ conj)` on `Ω`, an equality of *holomorphic*
  -- shapes which may be differentiated in the usual way.
  have hEq : EqOn F
      (fun w : ℂ => c + u * ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w) Ω := by
    intro w hw
    simpa [Function.comp_def] using hrefl ((starRingEnd ℂ) w) (hΩ hw)
  have hstep : ∀ w ∈ Ω, deriv F w = u * (starRingEnd ℂ) (deriv F ((starRingEnd ℂ) w)) := by
    intro w hw
    have hcc : deriv ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w
        = (starRingEnd ℂ) (deriv F ((starRingEnd ℂ) w)) := by
      simpa only [Function.comp_def] using congrFun deriv_conj_conj w
    calc deriv F w
        = deriv (fun w : ℂ => c + u * ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w) w :=
          (Filter.eventuallyEq_of_mem (hΩopen.mem_nhds hw) hEq).deriv_eq
      _ = deriv (fun w : ℂ => u * ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w) w :=
          deriv_const_add c
      _ = u * deriv ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w := deriv_const_mul_field u
      _ = u * (starRingEnd ℂ) (deriv F ((starRingEnd ℂ) w)) := by rw [hcc]
  simpa using hstep ((starRingEnd ℂ) z) (hΩ hz)

/-- **The second derivative inherits the same reflection identity.** If `F` intertwines
conjugation with an affine reflection on a conjugation-symmetric open set, then its second
derivative obeys the same multiplier relation as its first derivative. -/
theorem deriv_deriv_conj_eq_mul_conj_deriv_deriv (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    deriv (deriv F) ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (deriv (deriv F) z) :=
  deriv_conj_eq_mul_conj_deriv (c := 0) hΩopen hΩ
    (fun w hw => by simpa using deriv_conj_eq_mul_conj_deriv hΩopen hΩ hrefl hw) hz

/-- **The pre-Schwarzian derivative of a reflection-symmetric function is conjugation-symmetric.**
The factor `u` of the target reflection cancels between the second derivative and the first, so
`logDeriv (deriv F) = deriv (deriv F) / deriv F` intertwines conjugation with conjugation, whatever
the target line was. The degenerate factor `u = 0` is allowed: there `F` is constant on `Ω` and
both sides vanish. -/
theorem logDeriv_deriv_conj_eq_conj_logDeriv_deriv (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    logDeriv (deriv F) ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv (deriv F) z) := by
  rcases eq_or_ne u 0 with rfl | hu
  · -- `F` is the constant `c` on `Ω`, so every derivative of `F` vanishes there.
    have hconst : ∀ w ∈ Ω, F w = c := fun w hw => by
      simpa using hrefl ((starRingEnd ℂ) w) (hΩ hw)
    have hderiv : ∀ w ∈ Ω, deriv F w = 0 := fun w hw => by
      rw [(Filter.eventuallyEq_of_mem (hΩopen.mem_nhds hw) hconst).deriv_eq, deriv_const]
    have hderiv2 : ∀ w ∈ Ω, deriv (deriv F) w = 0 := fun w hw => by
      rw [(Filter.eventuallyEq_of_mem (hΩopen.mem_nhds hw) hderiv).deriv_eq, deriv_const]
    simp [logDeriv_apply, hderiv z hz, hderiv2 z hz, hderiv _ (hΩ hz), hderiv2 _ (hΩ hz)]
  · rw [logDeriv_apply, logDeriv_apply,
      deriv_deriv_conj_eq_mul_conj_deriv_deriv hΩopen hΩ hrefl hz,
      deriv_conj_eq_mul_conj_deriv hΩopen hΩ hrefl hz, mul_div_mul_left _ _ hu]
    exact (map_div₀ _ _ _).symm

/-- **The pre-Schwarzian derivative of a reflection-symmetric function is real on the real axis.**
-/
theorem im_logDeriv_deriv_eq_zero (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {x : ℂ} (hx : x ∈ Ω) (hx0 : x.im = 0) :
    (logDeriv (deriv F) x).im = 0 := by
  have h := logDeriv_deriv_conj_eq_conj_logDeriv_deriv hΩopen hΩ hrefl hx
  rw [Complex.conj_eq_iff_im.mpr hx0] at h
  exact Complex.conj_eq_iff_im.mp h.symm

section LineReflection

/-- The reflection identity of the Schwarz-reflection extension across the real axis, rewritten in
the affine form `w ↦ c + u * conj w` demanded by the lemmas above. The reflection in the line
through `q` with direction `b` has `u = b / conj b` and `c = q - u * conj q`. -/
private theorem lineSchwarzReflection_conj_eq (hb : b ≠ 0)
    (hline : ∀ z ∈ Ω, z.im = 0 → ((f z - q) / b).im = 0) {z : ℂ} (hz : z ∈ Ω) :
    lineSchwarzReflection 0 1 q b f ((starRingEnd ℂ) z) =
      (q - b / (starRingEnd ℂ) b * (starRingEnd ℂ) q) +
        b / (starRingEnd ℂ) b * (starRingEnd ℂ) (lineSchwarzReflection 0 1 q b f z) := by
  have hbc : (starRingEnd ℂ) b ≠ 0 := by simpa using hb
  have h := lineSchwarzReflection_sourceReflection (p := 0) (a := 1) (q := q) (b := b) (f := f)
    one_ne_zero hb (fun w hw hw0 => hline w hw (by simpa using hw0)) hz
  simp only [zero_add, one_mul, sub_zero, div_one] at h
  rw [h, map_div₀, map_sub]
  field_simp
  ring

/-- **On the real axis the reflected extension moves along the target line.** For boundary values
on the line through `q` with direction `b`, the derivative of the extension at a real point is a
real multiple of `b`. -/
theorem im_div_deriv_lineSchwarzReflection_eq_zero (hb : b ≠ 0) (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hline : ∀ z ∈ Ω, z.im = 0 → ((f z - q) / b).im = 0)
    {x : ℂ} (hx : x ∈ Ω) (hx0 : x.im = 0) :
    (deriv (lineSchwarzReflection 0 1 q b f) x / b).im = 0 := by
  have hA := deriv_conj_eq_mul_conj_deriv hΩopen hΩ
    (fun z hz => lineSchwarzReflection_conj_eq hb hline hz) hx
  rw [Complex.conj_eq_iff_im.mpr hx0] at hA
  refine Complex.conj_eq_iff_im.mp ?_
  rw [map_div₀]
  conv_rhs => rw [hA]
  field_simp

/-- **The pre-Schwarzian derivative of the reflected extension is real on the real axis.** The
hypotheses are those of the reflection principle across the real axis: the domain is symmetric, and
the boundary values of `f` lie on the line through `q` with direction `b`. -/
theorem im_logDeriv_deriv_lineSchwarzReflection_eq_zero (hb : b ≠ 0) (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hline : ∀ z ∈ Ω, z.im = 0 → ((f z - q) / b).im = 0)
    {x : ℂ} (hx : x ∈ Ω) (hx0 : x.im = 0) :
    (logDeriv (deriv (lineSchwarzReflection 0 1 q b f)) x).im = 0 :=
  im_logDeriv_deriv_eq_zero hΩopen hΩ
    (fun _ hz => lineSchwarzReflection_conj_eq hb hline hz) hx hx0

/-- **The reflected extension has the same pre-Schwarzian derivative as the original branch.**
On the open upper half-plane the extension agrees with `f`, hence so do all their derivatives. -/
theorem eqOn_logDeriv_deriv_lineSchwarzReflection (hb : b ≠ 0) :
    EqOn (logDeriv (deriv (lineSchwarzReflection 0 1 q b f))) (logDeriv (deriv f))
      {z : ℂ | 0 < z.im} := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  intro w hw
  have h0 : lineSchwarzReflection 0 1 q b f =ᶠ[𝓝 w] f :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hw) fun v hv =>
      lineSchwarzReflection_of_coord_im_nonneg f one_ne_zero hb (by simpa using hv.le)
  exact (logDeriv_congr_nhds h0.deriv).eq_of_nhds

end LineReflection

end TauCeti
