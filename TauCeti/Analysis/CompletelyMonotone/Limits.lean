/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Laplace
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv

/-!
# Pointwise limits of completely monotone functions

Complete monotonicity on `(0, ∞)` is stable under pointwise convergence: no uniformity, no
equicontinuity, and no smoothness of the limit need be assumed.  This file proves that closure
property, completing the algebraic ones of
`TauCeti.Analysis.CompletelyMonotone.OpenClosure`.

The derivative form of the predicate is not visibly stable under pointwise limits — nothing says
that the derivatives converge — so the proof passes through the finite-difference form
`TauCeti.IsDifferenceCompletelyMonotone`, which is manifestly stable
(`TauCeti.isDifferenceCompletelyMonotone_of_tendsto`), and comes back through the representation
theorem of `TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Laplace`.  That return trip needs
the limit to be right-continuous at the left endpoint of the half-line it is stated on, and this
is where the convexity of a completely monotone function is used: a pointwise limit of convex
functions is convex, hence continuous on the *open* half-line, so every positive translate of the
limit is right-continuous at `0`.

The open half-line is not a defect of the proof.  Complete monotonicity on the closed half-line is
genuinely *not* closed under pointwise limits: the functions `t ↦ (1 + n t)⁻¹` are completely
monotone on `[0, ∞)` and converge pointwise to the indicator of `{0}`, which is not even
continuous.  What survives at the endpoint is exactly one extra hypothesis, right-continuity at
`0`, and with it `TauCeti.IsContinuousCompletelyMonotoneOnIoi` is closed under pointwise limits
too.

## Main declarations

* `TauCeti.IsCompletelyMonotoneOnIoi.convexOn`: a completely monotone function on `(0, ∞)` is
  convex there.
* `TauCeti.isCompletelyMonotoneOnIoi_of_forall_comp_add_const`: complete monotonicity on `(0, ∞)`
  can be checked on positive translates, the converse of
  `TauCeti.IsCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const`.
* `TauCeti.isCompletelyMonotoneOnIoi_of_tendsto`: **complete monotonicity on `(0, ∞)` is closed
  under pointwise limits.**
* `TauCeti.isContinuousCompletelyMonotoneOnIoi_of_tendsto`: the closed-half-line predicate is
  closed under pointwise limits of functions completely monotone on `(0, ∞)`, given
  right-continuity of the limit at `0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Corollary 1.7.
* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- A function completely monotone on `(0, ∞)` is convex there: its second derivative is the
alternating derivative of order `2`, hence nonnegative. -/
lemma IsCompletelyMonotoneOnIoi.convexOn (hf : IsCompletelyMonotoneOnIoi f) :
    ConvexOn ℝ (Ioi 0) f := by
  have hd : DifferentiableOn ℝ f (Ioi 0) := hf.contDiffOn.differentiableOn (by simp)
  have hderiv : ContDiffOn ℝ ∞ (deriv f) (Ioi 0) :=
    hf.contDiffOn.deriv_of_isOpen isOpen_Ioi (by simp)
  have hd' : DifferentiableOn ℝ (deriv f) (Ioi 0) := hderiv.differentiableOn (by simp)
  refine convexOn_of_deriv2_nonneg (convex_Ioi 0) hf.contDiffOn.continuousOn ?_ ?_ ?_
  · rwa [interior_Ioi]
  · rwa [interior_Ioi]
  · rw [interior_Ioi]
    intro x hx
    simpa [iteratedDeriv_eq_iterate] using hf.neg_one_pow_mul_iteratedDeriv_nonneg 2 hx

/-- Complete monotonicity on `(0, ∞)` is detected by the positive translates of a function: if
`t ↦ f (t + a)` is completely monotone on `(0, ∞)` for every `a > 0`, then so is `f`.  This is the
converse of `TauCeti.IsCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const`, and it is how
a statement proved after moving the boundary into the open half-line is transported back. -/
theorem isCompletelyMonotoneOnIoi_of_forall_comp_add_const
    (h : ∀ a : ℝ, 0 < a → IsCompletelyMonotoneOnIoi fun s => f (s + a)) :
    IsCompletelyMonotoneOnIoi f := by
  have hsmooth : ContDiffOn ℝ ∞ f (Ioi 0) := by
    intro u hu
    have ha : (0 : ℝ) < u / 2 := by linarith [mem_Ioi.mp hu]
    have hshift : ContDiffAt ℝ ∞ (fun s : ℝ => f (s + u / 2)) ((fun s : ℝ => s - u / 2) u) := by
      have := ((h (u / 2) ha).contDiffOn).contDiffAt (isOpen_Ioi.mem_nhds (mem_Ioi.mpr ha))
      simpa [show u - u / 2 = u / 2 by ring] using this
    have hcomp := hshift.comp u (by fun_prop : ContDiffAt ℝ ∞ (fun s : ℝ => s - u / 2) u)
    exact (by simpa [Function.comp_def] using hcomp : ContDiffAt ℝ ∞ f u).contDiffWithinAt
  refine ⟨hsmooth, fun n u hu => ?_⟩
  have ha : (0 : ℝ) < u / 2 := by linarith
  have hsign := (h (u / 2) ha).neg_one_pow_mul_iteratedDeriv_nonneg n ha
  rw [iteratedDeriv_comp_add_const] at hsign
  simpa [show u / 2 + u / 2 = u by ring] using hsign

/-- **Complete monotonicity on `(0, ∞)` is closed under pointwise limits.**  A pointwise limit of
functions completely monotone on `(0, ∞)` is completely monotone on `(0, ∞)`; in particular it is
automatically `C^∞` there.

Nothing is assumed about the limit, and no uniformity is assumed about the convergence.  The
closed half-line version is false, see the module docstring, and
`TauCeti.isContinuousCompletelyMonotoneOnIoi_of_tendsto` for what replaces it. -/
theorem isCompletelyMonotoneOnIoi_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} (hF : ∀ i, IsCompletelyMonotoneOnIoi (F i))
    (hlim : ∀ u : ℝ, 0 < u → Tendsto (fun i => F i u) L (𝓝 (f u))) :
    IsCompletelyMonotoneOnIoi f := by
  have hconv : ConvexOn ℝ (Ioi 0) f := by
    refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hmem : a • x + b • y ∈ Ioi (0 : ℝ) := convex_Ioi 0 hx hy ha hb hab
    refine le_of_tendsto_of_tendsto' (hlim _ hmem)
      (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)) fun i => ?_
    exact (hF i).convexOn.2 hx hy ha hb hab
  have hcont : ContinuousOn f (Ioi 0) := hconv.continuousOn isOpen_Ioi
  refine isCompletelyMonotoneOnIoi_of_forall_comp_add_const fun a ha => ?_
  have hdiff : IsDifferenceCompletelyMonotone fun s => f (s + a) :=
    isDifferenceCompletelyMonotone_of_tendsto
      (fun i => ((hF i).isCompletelyMonotone_comp_add_const ha).isDifferenceCompletelyMonotone)
      fun u hu => hlim (u + a) (by linarith)
  have hzero : ContinuousWithinAt (fun s => f (s + a)) (Ici 0) 0 := by
    have hfa : ContinuousAt f a := hcont.continuousAt (isOpen_Ioi.mem_nhds (mem_Ioi.mpr ha))
    have hcomp : ContinuousAt (f ∘ fun s : ℝ => s + a) 0 :=
      hfa.comp_of_eq (by fun_prop) (zero_add a)
    simpa [Function.comp_def] using hcomp.continuousWithinAt (s := Ici 0)
  exact (hdiff.isContinuousCompletelyMonotoneOnIoi hzero).isCompletelyMonotoneOnIoi

/-- Complete monotonicity in the closed-half-line sense of
`TauCeti.IsContinuousCompletelyMonotoneOnIoi` is closed under pointwise limits on `(0, ∞)`, once
the limit is known to be right-continuous at the endpoint.  That extra hypothesis cannot be
dropped: see the module docstring. -/
theorem isContinuousCompletelyMonotoneOnIoi_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} (hF : ∀ i, IsCompletelyMonotoneOnIoi (F i))
    (hlim : ∀ u : ℝ, 0 < u → Tendsto (fun i => F i u) L (𝓝 (f u)))
    (hzero : ContinuousWithinAt f (Ici 0) 0) :
    IsContinuousCompletelyMonotoneOnIoi f := by
  have hcm : IsCompletelyMonotoneOnIoi f := isCompletelyMonotoneOnIoi_of_tendsto hF hlim
  refine isContinuousCompletelyMonotoneOnIoi_iff.mpr ⟨fun u hu => ?_, hcm⟩
  rcases (mem_Ici.mp hu).lt_or_eq with h | h
  · exact (hcm.contDiffOn.continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds (mem_Ioi.mpr h))).continuousWithinAt
  · exact h ▸ hzero

end TauCeti
