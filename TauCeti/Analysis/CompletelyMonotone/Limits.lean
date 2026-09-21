/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Laplace
public import Mathlib.Analysis.Convex.Continuous

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
limit is right-continuous at `0`.  That convexity is
`TauCeti.IsCompletelyMonotoneOnIoi.convexOn`.

The open half-line is not a defect of the proof.  Complete monotonicity on the closed half-line is
genuinely *not* closed under pointwise limits: the functions `t ↦ (1 + n t)⁻¹` are completely
monotone on `[0, ∞)` and converge pointwise to the indicator of `{0}`, which is not even
continuous.  What survives at the endpoint is exactly one extra hypothesis, right-continuity at
`0`, and with it `TauCeti.IsContinuousCompletelyMonotoneOnIoi` is closed under pointwise limits
too.

## Main declarations

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

/-- **Complete monotonicity on `(0, ∞)` is closed under pointwise limits.**  A pointwise limit of
functions completely monotone on `(0, ∞)` is completely monotone on `(0, ∞)`; in particular it is
automatically `C^∞` there.

Nothing is assumed about the limit, and no uniformity is assumed about the convergence.  The
closed half-line version is false, see the module docstring, and
`TauCeti.isContinuousCompletelyMonotoneOnIoi_of_tendsto` for what replaces it. -/
theorem isCompletelyMonotoneOnIoi_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} (hF : ∀ᶠ i in L, IsCompletelyMonotoneOnIoi (F i))
    (hlim : ∀ u : ℝ, 0 < u → Tendsto (fun i => F i u) L (𝓝 (f u))) :
    IsCompletelyMonotoneOnIoi f := by
  have hconv : ConvexOn ℝ (Ioi 0) f := by
    refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hmem : a • x + b • y ∈ Ioi (0 : ℝ) := convex_Ioi 0 hx hy ha hb hab
    refine le_of_tendsto_of_tendsto (hlim _ hmem)
      (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)) (hF.mono fun i hi => ?_)
    exact hi.convexOn.2 hx hy ha hb hab
  have hcont : ContinuousOn f (Ioi 0) := hconv.continuousOn isOpen_Ioi
  refine isCompletelyMonotoneOnIoi_of_forall_comp_add_const fun a ha => ?_
  have hdiff : IsDifferenceCompletelyMonotone fun s => f (s + a) :=
    isDifferenceCompletelyMonotone_of_tendsto
      (hF.mono fun i hi =>
        (hi.isCompletelyMonotone_comp_add_const ha).isDifferenceCompletelyMonotone)
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
    {F : ι → ℝ → ℝ} (hF : ∀ᶠ i in L, IsCompletelyMonotoneOnIoi (F i))
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
