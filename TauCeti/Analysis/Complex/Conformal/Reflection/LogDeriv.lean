/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.Analysis.Complex.Conformal.Reflection.Line
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.RCLike.TangentCone
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.Reflection.Injective

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
consecutive prevertices into one side, hence has real pre-Schwarzian there. When the map is also
injective up to that interval and sends the upper half-plane to one side of the side's line, the
reflected extension is injective, so its derivative does not vanish on the interval and its
pre-Schwarzian is holomorphic across it. Assembling those intervals, the pre-Schwarzian continues to
a conjugation-symmetric function holomorphic on the plane minus the prevertices
(`TauCeti.exists_differentiableOn_eqOn_logDeriv_deriv`). Reading off its poles at the prevertices
is what identifies it with `∑ i, e i / (z - a i)`, the pre-Schwarzian derivative of the
Schwarz--Christoffel map (`TauCeti.logDeriv_deriv_schwarzChristoffelPrimitive`).

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
`TauCeti.lineSchwarzReflection_of_coord_im_nonneg`. The symmetry and real-axis statements about
its derivatives need no hypothesis on `f`: off the real axis the witness satisfies the reflection
identity whatever `f` is, and at a real point the identity passes to the derivatives from the upper
half-plane.

## Main results

* `TauCeti.deriv_conj_eq_mul_conj_deriv` and
  `TauCeti.deriv_deriv_conj_eq_mul_conj_deriv_deriv` -- the first and second derivatives of a
  function intertwining conjugation with an affine reflection satisfy the same intertwining
  relation, with the additive constant gone.
* `TauCeti.logDeriv_conj_eq_conj_logDeriv` -- the logarithmic derivative of a function
  intertwining conjugation with `w ↦ u * conj w` intertwines conjugation with conjugation.
* `TauCeti.logDeriv_deriv_conj_eq_conj_logDeriv_deriv` -- applied to the first derivative: the
  pre-Schwarzian derivative intertwines conjugation with conjugation.
* `TauCeti.im_logDeriv_deriv_eq_zero` -- so it is real on the real axis.
* `TauCeti.deriv_conj_eq_mul_conj_deriv_of_isOpen_of_forall_im_ne_zero` and
  `TauCeti.logDeriv_deriv_conj_eq_conj_logDeriv_deriv_of_isOpen_of_forall_im_ne_zero` -- a
  reflection identity holding at the non-real points of an open set `Ω` gives these identities at
  every point of `Ω` (for the second, every `z ∈ Ω` whose conjugate also lies in `Ω`), real points
  included; the `_of_forall_im_ne_zero` forms are the case of the whole plane.
* `TauCeti.im_div_deriv_lineSchwarzReflection_eq_zero` -- on the real axis the derivative of the
  reflected extension is a real multiple of the direction of the target line.
* `TauCeti.logDeriv_deriv_lineSchwarzReflection_conj` -- the pre-Schwarzian derivative of the
  reflected extension is conjugation-symmetric on the whole plane.
* `TauCeti.im_logDeriv_deriv_lineSchwarzReflection_eq_zero` -- so it is real on the real axis.
* `TauCeti.eqOn_logDeriv_deriv_lineSchwarzReflection` -- it extends the pre-Schwarzian derivative
  of the original branch.
* `TauCeti.differentiableOn_logDeriv_deriv_lineSchwarzReflection` -- for an injective branch
  mapping the upper half-plane to one side of the target line, it is holomorphic across the axis.
* `TauCeti.exists_differentiableOn_eqOn_logDeriv_deriv` -- the pre-Schwarzian derivative of a map
  of the upper half-plane with straight boundary arcs away from a set `S` continues to a
  conjugation-symmetric function holomorphic away from the real points of `S`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

namespace TauCeti

open Complex Set Topology

variable {Ω : Set ℂ} {F f : ℂ → ℂ} {c u q b : ℂ}

/-- **The derivative inherits an affine reflection identity, without its constant.** If `F`
carries conjugation to the affine reflection `w ↦ c + u * conj w` on an open set, then `deriv F`
carries conjugation to `w ↦ u * conj w`. No differentiability is assumed: the identity also holds,
with both sides `0`, wherever `F` fails to be differentiable. The set need not be
conjugation-symmetric: `hrefl` expresses `F` on the open neighbourhood `{w | conj w ∈ Ω}` of
`conj z` through the values of `F` on `Ω`. -/
theorem deriv_conj_eq_mul_conj_deriv (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    deriv F ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (deriv F z) := by
  -- Read the identity as `F = c + u * (conj ∘ F ∘ conj)` on the open set `{w | conj w ∈ Ω}`, an
  -- equality of *holomorphic* shapes which may be differentiated in the usual way.
  have hΩ' : IsOpen {w : ℂ | (starRingEnd ℂ) w ∈ Ω} := hΩopen.preimage Complex.continuous_conj
  have hEq : EqOn F
      (fun w : ℂ => c + u * ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w)
      {w : ℂ | (starRingEnd ℂ) w ∈ Ω} := by
    intro w hw
    simpa [Function.comp_def] using hrefl ((starRingEnd ℂ) w) hw
  have hstep : ∀ w, (starRingEnd ℂ) w ∈ Ω →
      deriv F w = u * (starRingEnd ℂ) (deriv F ((starRingEnd ℂ) w)) := by
    intro w hw
    have hcc : deriv ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w
        = (starRingEnd ℂ) (deriv F ((starRingEnd ℂ) w)) := by
      simpa only [Function.comp_def] using congrFun deriv_conj_conj w
    calc deriv F w
        = deriv (fun w : ℂ => c + u * ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w) w :=
          (Filter.eventuallyEq_of_mem (hΩ'.mem_nhds hw) hEq).deriv_eq
      _ = deriv (fun w : ℂ => u * ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w) w :=
          deriv_const_add c
      _ = u * deriv ((starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ)) w := deriv_const_mul_field u
      _ = u * (starRingEnd ℂ) (deriv F ((starRingEnd ℂ) w)) := by rw [hcc]
  simpa using hstep ((starRingEnd ℂ) z) (by simpa using hz)

/-- **The second derivative inherits the same reflection identity.** If `F` intertwines
conjugation with an affine reflection on an open set, then its second derivative obeys the same
multiplier relation as its first derivative. -/
theorem deriv_deriv_conj_eq_mul_conj_deriv_deriv (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    deriv (deriv F) ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (deriv (deriv F) z) :=
  deriv_conj_eq_mul_conj_deriv (c := 0) hΩopen
    (fun w hw => by simpa using deriv_conj_eq_mul_conj_deriv hΩopen hrefl hw) hz

/-- **The logarithmic derivative of a reflection-symmetric function is conjugation-symmetric, for a
nondegenerate multiplier.** If `F` carries conjugation to `w ↦ u * conj w` on an open set and
`u ≠ 0`, then `deriv F` carries conjugation to the same map, the factor `u` cancels between
`deriv F` and `F`, and `logDeriv F = deriv F / F` intertwines conjugation with conjugation. No
symmetry of `Ω` is needed. -/
theorem logDeriv_conj_eq_conj_logDeriv_of_ne_zero (hu : u ≠ 0) (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    logDeriv F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv F z) := by
  rw [logDeriv_apply, logDeriv_apply,
    deriv_conj_eq_mul_conj_deriv (c := 0) hΩopen (fun w hw => by simpa using hrefl w hw) hz,
    hrefl z hz, mul_div_mul_left _ _ hu]
  exact (map_div₀ _ _ _).symm

/-- **The logarithmic derivative of a reflection-symmetric function is conjugation-symmetric.** If
`F` carries conjugation to `w ↦ u * conj w` on an open set, then `logDeriv F` intertwines
conjugation with conjugation at every point `z` of the set whose conjugate also lies in it. The
degenerate factor `u = 0` is allowed: then `F` vanishes at `z` and at `conj z`, and both sides are
`0`; this is the only place where `conj z ∈ Ω` is used. -/
theorem logDeriv_conj_eq_conj_logDeriv (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) (hz' : (starRingEnd ℂ) z ∈ Ω) :
    logDeriv F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv F z) := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h1 : F ((starRingEnd ℂ) z) = 0 := by simpa using hrefl z hz
    have h2 : F z = 0 := by simpa using hrefl _ hz'
    simp [logDeriv_apply, h1, h2]
  · exact logDeriv_conj_eq_conj_logDeriv_of_ne_zero hu hΩopen hrefl hz

/-- **The pre-Schwarzian derivative of a reflection-symmetric function is conjugation-symmetric,
for a nondegenerate multiplier.** Differentiating the affine reflection identity of `F` removes its
constant, and `logDeriv_conj_eq_conj_logDeriv_of_ne_zero` applies to `deriv F`: the factor `u`
cancels, so `logDeriv (deriv F) = deriv (deriv F) / deriv F` intertwines conjugation with
conjugation, whatever the target line was. No symmetry of `Ω` is needed. -/
theorem logDeriv_deriv_conj_eq_conj_logDeriv_deriv_of_ne_zero (hu : u ≠ 0) (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    logDeriv (deriv F) ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv (deriv F) z) :=
  logDeriv_conj_eq_conj_logDeriv_of_ne_zero hu hΩopen
    (fun _ hw => deriv_conj_eq_mul_conj_deriv hΩopen hrefl hw) hz

/-- **The pre-Schwarzian derivative of a reflection-symmetric function is conjugation-symmetric.**
Differentiating the affine reflection identity of `F` removes its constant, and
`logDeriv_conj_eq_conj_logDeriv` applies to `deriv F`: `logDeriv (deriv F)` intertwines
conjugation with conjugation, whatever the target line was. The degenerate factor `u = 0` is
allowed: there `deriv F` vanishes at `z` and at `conj z`, and both sides are `0`; this is the only
place where `conj z ∈ Ω` is used. -/
theorem logDeriv_deriv_conj_eq_conj_logDeriv_deriv (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) (hz' : (starRingEnd ℂ) z ∈ Ω) :
    logDeriv (deriv F) ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv (deriv F) z) :=
  logDeriv_conj_eq_conj_logDeriv hΩopen
    (fun _ hw => deriv_conj_eq_mul_conj_deriv hΩopen hrefl hw) hz hz'

/-- **The pre-Schwarzian derivative of a reflection-symmetric function is real on the real axis.**
-/
theorem im_logDeriv_deriv_eq_zero (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {x : ℂ} (hx : x ∈ Ω) (hx0 : x.im = 0) :
    (logDeriv (deriv F) x).im = 0 := by
  have hxc : (starRingEnd ℂ) x = x := Complex.conj_eq_iff_im.mpr hx0
  have h := logDeriv_deriv_conj_eq_conj_logDeriv_deriv hΩopen hrefl hx (by rwa [hxc])
  rw [hxc] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **A reflection identity off the real axis passes to the derivative, real points included.** If
`F` carries conjugation to the affine reflection `w ↦ c + u * conj w` at every non-real point of an
open set `Ω`, then `deriv F` carries conjugation to `w ↦ u * conj w` at every point of `Ω`, the real
points included. Neither differentiability nor continuity of `F` is assumed: where `F` is not
differentiable both sides are `0`. At a real point the identity is read off from the upper
half-plane, which accumulates there. -/
theorem deriv_conj_eq_mul_conj_deriv_of_isOpen_of_forall_im_ne_zero (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, z.im ≠ 0 → F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) :
    deriv F ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (deriv F z) := by
  rcases ne_or_eq z.im 0 with hz0 | hz0
  · exact deriv_conj_eq_mul_conj_deriv
      (hΩopen.inter (isOpen_ne_fun Complex.continuous_im continuous_const))
      (fun w hw => hrefl w hw.1 hw.2) ⟨hz, hz0⟩
  have hzc : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr hz0
  rw [hzc]
  by_cases hd : DifferentiableAt ℂ F z
  swap
  · simp [deriv_zero_of_not_differentiableAt hd]
  -- Near `z` and off the axis `F` agrees with `H w = c + u * conj (F (conj w))`, which is
  -- differentiable at `z` with derivative `u * conj (deriv F z)`.
  set H : ℂ → ℂ := fun w => c + u * (starRingEnd ℂ) (F ((starRingEnd ℂ) w)) with hH
  have hHd : HasDerivAt H (u * (starRingEnd ℂ) (deriv F z)) z := by
    have h := hd.hasDerivAt.conj_conj
    rw [hzc] at h
    exact (h.const_mul u).const_add c
  -- The upper half-plane `U` accumulates at the real point `z`, so the two continuous functions
  -- agree at `z`, and `U` is a set of unique differentiability at `z`.
  set U : Set ℂ := {w : ℂ | 0 < w.im}
  have hzU : z ∈ closure U := by simp [U, hz0]
  have : (𝓝[U] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzU
  have hEq : H =ᶠ[𝓝[U] z] F := by
    have hΩ' : {w : ℂ | (starRingEnd ℂ) w ∈ Ω} ∈ 𝓝 z :=
      (hΩopen.preimage Complex.continuous_conj).mem_nhds (by simpa [hzc] using hz)
    filter_upwards [nhdsWithin_le_nhds hΩ', self_mem_nhdsWithin] with w hw hwU
    simpa [hH] using (hrefl ((starRingEnd ℂ) w) hw (by simpa using ne_of_gt hwU)).symm
  have hHz : H z = F z := tendsto_nhds_unique
    ((hHd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hEq)
    (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hU : UniqueDiffWithinAt ℂ U z :=
    uniqueDiffWithinAt_convex_of_isRCLikeNormedField (convex_halfSpace_im_gt 0)
      ⟨I, by rw [(isOpen_lt continuous_const Complex.continuous_im).interior_eq]; simp⟩ hzU
  exact hU.eq_deriv U hd.hasDerivAt.hasDerivWithinAt
    (hHd.hasDerivWithinAt.congr_of_eventuallyEq hEq.symm hHz.symm)

/-- **A reflection identity off the real axis passes to the derivative everywhere.** This is
`deriv_conj_eq_mul_conj_deriv_of_isOpen_of_forall_im_ne_zero` on the whole plane: if `F` carries
conjugation to `w ↦ c + u * conj w` at every non-real point, then `deriv F` carries conjugation to
`w ↦ u * conj w` at every point, the real axis included. -/
theorem deriv_conj_eq_mul_conj_deriv_of_forall_im_ne_zero
    (hrefl : ∀ z : ℂ, z.im ≠ 0 → F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z)) (z : ℂ) :
    deriv F ((starRingEnd ℂ) z) = u * (starRingEnd ℂ) (deriv F z) :=
  deriv_conj_eq_mul_conj_deriv_of_isOpen_of_forall_im_ne_zero isOpen_univ (fun w _ => hrefl w)
    (mem_univ z)

/-- **The pre-Schwarzian derivative is conjugation-symmetric when a reflection identity holds off
the real axis.** If `F` carries conjugation to the affine reflection `w ↦ c + u * conj w` at every
non-real point of an open set `Ω`, then `logDeriv (deriv F)` intertwines conjugation with
conjugation at every point `z` of `Ω` whose conjugate also lies in `Ω`, real points included. The
degenerate factor `u = 0` is allowed: then `deriv F` vanishes at `z` and at `conj z`, and both sides
are `0`. -/
theorem logDeriv_deriv_conj_eq_conj_logDeriv_deriv_of_isOpen_of_forall_im_ne_zero
    (hΩopen : IsOpen Ω)
    (hrefl : ∀ z ∈ Ω, z.im ≠ 0 → F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z))
    {z : ℂ} (hz : z ∈ Ω) (hz' : (starRingEnd ℂ) z ∈ Ω) :
    logDeriv (deriv F) ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv (deriv F) z) :=
  logDeriv_conj_eq_conj_logDeriv hΩopen
    (fun _ hw => deriv_conj_eq_mul_conj_deriv_of_isOpen_of_forall_im_ne_zero hΩopen hrefl hw) hz hz'

/-- **The pre-Schwarzian derivative is conjugation-symmetric everywhere when a reflection
identity holds off the real axis.** This is
`logDeriv_deriv_conj_eq_conj_logDeriv_deriv_of_isOpen_of_forall_im_ne_zero` on the whole plane: if
`F` carries conjugation to `w ↦ c + u * conj w` at every non-real point, then
`logDeriv (deriv F)` intertwines conjugation with conjugation at every point, the real axis
included. -/
theorem logDeriv_deriv_conj_eq_conj_logDeriv_deriv_of_forall_im_ne_zero
    (hrefl : ∀ z : ℂ, z.im ≠ 0 → F ((starRingEnd ℂ) z) = c + u * (starRingEnd ℂ) (F z)) (z : ℂ) :
    logDeriv (deriv F) ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv (deriv F) z) :=
  logDeriv_deriv_conj_eq_conj_logDeriv_deriv_of_isOpen_of_forall_im_ne_zero isOpen_univ
    (fun w _ => hrefl w) (mem_univ z) (mem_univ _)

section LineReflection

/-- The reflection identity of the Schwarz-reflection extension across the real axis at a non-real
point, rewritten in the affine form `w ↦ c + u * conj w` demanded by the lemmas above. Off the axis
it needs no hypothesis on `f`. For `b ≠ 0` the reflection in the line through `q` with direction
`b` has `u = b / conj b` and `c = q - u * conj q`. For `b = 0` the extension is the constant `q`,
and the identity holds trivially. -/
private theorem lineSchwarzReflection_conj_eq {z : ℂ} (hz : z.im ≠ 0) :
    lineSchwarzReflection 0 1 q b f ((starRingEnd ℂ) z) =
      (q - b / (starRingEnd ℂ) b * (starRingEnd ℂ) q) +
        b / (starRingEnd ℂ) b * (starRingEnd ℂ) (lineSchwarzReflection 0 1 q b f z) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hbc : (starRingEnd ℂ) b ≠ 0 := by simpa using hb
  have h := lineSchwarzReflection_sourceReflection (p := 0) (a := 1) (q := q) (b := b) (f := f)
    one_ne_zero (z := z) (fun hz0 => absurd (by simpa using hz0 : z.im = 0) hz)
  simp only [zero_add, one_mul, sub_zero, div_one] at h
  rw [h, map_div₀, map_sub]
  field_simp
  ring

/-- **On the real axis the reflected extension moves along the target line.** For `b ≠ 0` the
derivative of the extension at a real point is a real multiple of `b`, whatever `f` is. When the
boundary values of `f` lie on the line through `q` with direction `b`, this says that the boundary
arc runs along that line. For `b = 0` the quotient by `b` is `0`. -/
theorem im_div_deriv_lineSchwarzReflection_eq_zero {x : ℂ} (hx0 : x.im = 0) :
    (deriv (lineSchwarzReflection 0 1 q b f) x / b).im = 0 := by
  have hA := deriv_conj_eq_mul_conj_deriv_of_forall_im_ne_zero
    (F := lineSchwarzReflection 0 1 q b f) (fun _ hz => lineSchwarzReflection_conj_eq hz) x
  rw [Complex.conj_eq_iff_im.mpr hx0] at hA
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  refine Complex.conj_eq_iff_im.mp ?_
  rw [map_div₀]
  conv_rhs => rw [hA]
  field_simp

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

/-- **The pre-Schwarzian derivative of the reflected extension is conjugation-symmetric.** It
intertwines conjugation with conjugation at every point of the plane, whatever `f` is. For `b = 0`
the extension is the constant `q` and both sides are `0`. -/
theorem logDeriv_deriv_lineSchwarzReflection_conj (z : ℂ) :
    logDeriv (deriv (lineSchwarzReflection 0 1 q b f)) ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (logDeriv (deriv (lineSchwarzReflection 0 1 q b f)) z) :=
  logDeriv_deriv_conj_eq_conj_logDeriv_deriv_of_forall_im_ne_zero
    (fun _ hw => lineSchwarzReflection_conj_eq hw) z

/-- **The pre-Schwarzian derivative of the reflected extension is real on the real axis**,
whatever `f` is. -/
theorem im_logDeriv_deriv_lineSchwarzReflection_eq_zero {x : ℂ} (hx0 : x.im = 0) :
    (logDeriv (deriv (lineSchwarzReflection 0 1 q b f)) x).im = 0 := by
  have h := logDeriv_deriv_lineSchwarzReflection_conj (q := q) (b := b) (f := f) x
  rw [Complex.conj_eq_iff_im.mpr hx0] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **The pre-Schwarzian derivative of a reflected conformal map is holomorphic across the
axis.** Let `f` be continuous and injective on the closed upper part of a conjugation-symmetric
open set `Ω` and holomorphic on its open upper part, with boundary values on the line through `q`
with direction `b` and with the open upper part mapped strictly to the left of that line. Then the
pre-Schwarzian derivative of the reflected extension is holomorphic on all of `Ω`, the real points
included. For `b = 0` the hypotheses `hΩopen`, `hΩ` and `hside` force `Ω = ∅`, so that case
holds vacuously. -/
theorem differentiableOn_logDeriv_deriv_lineSchwarzReflection (hΩopen : IsOpen Ω)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hline : ∀ z ∈ Ω, z.im = 0 → ((f z - q) / b).im = 0)
    (hside : ∀ z ∈ Ω, 0 < z.im → 0 < ((f z - q) / b).im)
    (hinj : InjOn f (Ω ∩ {z : ℂ | 0 ≤ z.im})) :
    DifferentiableOn ℂ (logDeriv (deriv (lineSchwarzReflection 0 1 q b f))) Ω := by
  set F := lineSchwarzReflection 0 1 q b f with hFdef
  have hd : DifferentiableOn ℂ F Ω :=
    differentiableOn_lineSchwarzReflection_of_symmetric hΩopen
      (by simpa using hΩ) (by simpa using hcont) (by simpa using hholo) (by simpa using hline)
  -- In the target chart `w ↦ (w - q) / b` the extension is the real-axis Schwarz reflection of
  -- `g`, which is injective because `g` maps the open upper part into the upper half-plane.
  rcases eq_or_ne b 0 with rfl | hb
  · -- For `b = 0` the extension is the constant `q`, so `logDeriv (deriv _)` vanishes identically.
    simp [hFdef]
  set g : ℂ → ℂ := fun w => (f w - q) / b with hg
  have hFg : ∀ z, F z = q + b * schwarzReflection g z := fun z => by
    simp [hFdef, hg, lineSchwarzReflection_def]
  have hginj : InjOn (schwarzReflection g) Ω := by
    refine injOn_schwarzReflection_of_symmetric hΩ (fun z hz => hside z hz.1 hz.2)
      (fun z hz hz0 => (hline z hz hz0).ge) fun z hz w hw hzw => hinj hz hw ?_
    simpa [hg, div_left_inj' hb] using hzw
  have hFinj : InjOn F Ω := fun z hz w hw hzw => hginj hz hw <| by
    simpa [hFg, hb] using hzw
  have hd' : DifferentiableOn ℂ (deriv F) Ω := hd.deriv hΩopen
  refine ((hd'.deriv hΩopen).div hd' fun z hz => deriv_ne_zero_of_injOn hd hΩopen hFinj hz).congr
    fun z _ => logDeriv_apply _ _

end LineReflection

section Continuation

open Filter

/-- Near a real point where `f` is locally the restriction of a Schwarz reflection across a line,
the continuation of the pre-Schwarzian `logDeriv (deriv f)` (filled in on the axis by the real part
of its limit from above) is holomorphic. -/
private theorem differentiableAt_schwarzReflection_logDeriv_deriv {x : ℝ}
    (hholo : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hloc : ∃ r > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Metric.ball (x : ℂ) r, z.im = 0 → ((f z - q) / b).im = 0) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → 0 < ((f z - q) / b).im) :
    DifferentiableAt ℂ (schwarzReflection fun z : ℂ => if 0 < z.im then logDeriv (deriv f) z
      else ((limUnder (𝓝[{w : ℂ | 0 < w.im}] z) (logDeriv (deriv f))).re : ℂ)) x := by
  set ψ := logDeriv (deriv f)
  let ψu : ℂ → ℂ := fun z => if 0 < z.im then ψ z
    else ((limUnder (𝓝[{w : ℂ | 0 < w.im}] z) ψ).re : ℂ)
  let φ := schwarzReflection ψu
  obtain ⟨r, hr, q, b, hb, hcont, hinj, hline, hside⟩ := hloc
  have hball : MapsTo (starRingEnd ℂ) (Metric.ball (x : ℂ) r) (Metric.ball (x : ℂ) r) :=
    fun z hz => by
      rw [Metric.mem_ball, ← Complex.conj_ofReal, Complex.dist_conj_conj]
      exact hz
  set G := logDeriv (deriv (lineSchwarzReflection 0 1 q b f))
  have hG := differentiableOn_logDeriv_deriv_lineSchwarzReflection Metric.isOpen_ball hball
    hcont ((hholo.mono inter_subset_right)) hline hside hinj
  have hGψ : EqOn G ψ {z : ℂ | 0 < z.im} := eqOn_logDeriv_deriv_lineSchwarzReflection hb
  have hGconj : ∀ z, G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G z) :=
    logDeriv_deriv_lineSchwarzReflection_conj
  have hφG : φ =ᶠ[𝓝 (x : ℂ)] G := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · have hc : 0 < ((starRingEnd ℂ) z).im := by simpa using h
      simp only [φ, schwarzReflection_of_im_neg h, ψu, hc, ↓reduceIte]
      rw [← hGψ hc, hGconj z, Complex.conj_conj]
    · -- On the axis, `G` is continuous and agrees with `ψ` above, so it is the limit there.
      have hlim : Tendsto ψ (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 (G z)) :=
        ((hG.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)).tendsto.mono_left
          nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall fun w hw => hGψ hw)
      have : (𝓝[{w : ℂ | 0 < w.im}] z).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (by simp [h])
      have hGre : ((G z).re : ℂ) = G z := Complex.conj_eq_iff_re.mp <| by
        simpa [Complex.conj_eq_iff_im.mpr h] using (hGconj z).symm
      simp only [φ, schwarzReflection_of_im_zero h, ψu, h, lt_irrefl, ↓reduceIte]
      rw [hlim.limUnder_eq, hGre]
    · simp only [φ, schwarzReflection_of_im_nonneg h.le, ψu, h, ↓reduceIte]
      exact (hGψ h).symm
  exact ((hG x (Metric.mem_ball_self hr)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).congr_of_eventuallyEq hφG

/-- **The pre-Schwarzian derivative continues across straight boundary arcs.** Let `f` be
holomorphic with nonvanishing derivative on the open upper half-plane, and suppose that near every
real point outside `S` it extends continuously and injectively to the real axis, with boundary
values on a line and the nearby upper half-plane mapped strictly to one side of that line. Then
the pre-Schwarzian derivative `logDeriv (deriv f)` continues to a function holomorphic away from
the real points of `S` and symmetric under conjugation.

This is the situation of a conformal map of the upper half-plane onto a polygon, with `S` the set
of prevertices: each boundary interval between consecutive prevertices is carried into one side of
the polygon. The continuation is in fact holomorphic at every non-real point; the theorem permits
exceptions only at the real points of `S`. -/
theorem exists_differentiableOn_eqOn_logDeriv_deriv {S : Set ℂ}
    (hholo : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hderiv : ∀ z : ℂ, 0 < z.im → deriv f z ≠ 0)
    (hloc : ∀ x : ℝ, (x : ℂ) ∉ S → ∃ r > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ContinuousOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ Metric.ball (x : ℂ) r, z.im = 0 → ((f z - q) / b).im = 0) ∧
      ∀ z ∈ Metric.ball (x : ℂ) r, 0 < z.im → 0 < ((f z - q) / b).im) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (S ∩ {z : ℂ | z.im = 0})ᶜ ∧
      EqOn φ (logDeriv (deriv f)) {z : ℂ | 0 < z.im} ∧
      ∀ z, φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z) := by
  set ψ := logDeriv (deriv f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  -- Above the axis the pre-Schwarzian is holomorphic because `deriv f` does not vanish.
  have hψ : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ ψ z := fun z hz => by
    have h1 := hholo.deriv hopen
    have hz' := hopen.mem_nhds hz
    refine (((h1.deriv hopen) z hz).differentiableAt hz').div ((h1 z hz).differentiableAt hz')
      (hderiv z hz) |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    exact logDeriv_apply _ _
  -- The continuation is the Schwarz reflection of `ψ` filled in on the axis by the real part of
  -- its limit from above.
  let ψu : ℂ → ℂ := fun z => if 0 < z.im then ψ z
    else ((limUnder (𝓝[{w : ℂ | 0 < w.im}] z) ψ).re : ℂ)
  let φ := schwarzReflection ψu
  have hconj : ∀ z, φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z) := fun z =>
    schwarzReflection_conj z fun h => by simp [ψu, h]
  -- Near a real point outside `S`, the continuation is the pre-Schwarzian derivative of the
  -- local Schwarz reflection of `f`.
  have hreal : ∀ x : ℝ, (x : ℂ) ∉ S → DifferentiableAt ℂ φ x := fun x hx =>
    differentiableAt_schwarzReflection_logDeriv_deriv hholo (hloc x hx)
  refine ⟨φ, fun z hz => ?_, fun z (hz : 0 < z.im) => by simp [φ, ψu, hz, hz.le], hconj⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases lt_trichotomy z.im 0 with h | h | h
  · -- Below the axis the continuation is the mirror image of `ψ`.
    have hc : 0 < ((starRingEnd ℂ) z).im := by simpa using h
    have hmir := (hψ _ hc).conj_conj
    rw [Complex.conj_conj] at hmir
    refine hmir.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds h] with w hw
    simp [φ, ψu, hw]
  · have hzS : z ∉ S := fun hzS => hz ⟨hzS, h⟩
    have hzre : ((z.re : ℂ)) = z := Complex.ext (by simp) (by simp [h])
    rw [← hzre] at hzS ⊢
    exact hreal z.re hzS
  · refine (hψ z h).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds h] with w hw
    simp [φ, ψu, hw, hw.le]

end Continuation

end TauCeti
