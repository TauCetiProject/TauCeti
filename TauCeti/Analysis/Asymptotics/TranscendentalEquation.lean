/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Inversion of `f(x) ∼ x` (DLMF 2.2.1–2.2.2)

Let `f` be continuous and strictly increasing on `[a, ∞)` with `f(x) ∼ x` as `x → +∞`. For every
`y > f(a)` the equation `f(x) = y` then has a unique root `x(y)` in `(a, ∞)`, and `x(y) ∼ y` as
`y → +∞`. This is the starting point of DLMF §2.2 on the asymptotic solution of transcendental
equations. The asymptotic statement needs only that `f` is monotone on `[a, ∞)`.

## Main results

* `ContinuousOn.existsUnique_root_of_isEquivalent`: existence and uniqueness of the root
  (DLMF 2.2.1).
* `MonotoneOn.root_isEquivalent`: any function that is eventually such a root is asymptotically
  equivalent to the identity (DLMF 2.2.2).

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.2, <https://dlmf.nist.gov/2.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/AsymptoticApproximations/Basics/Transcendental.lean`.
-/

@[expose] public section

open Asymptotics Filter Set

/-- DLMF 2.2.1: if `f` is continuous and strictly increasing on `[a, ∞)` and `f(x) ∼ x` as
`x → +∞`, then for every `y > f(a)` the equation `f(x) = y` has a unique root in `(a, ∞)`. -/
theorem ContinuousOn.existsUnique_root_of_isEquivalent {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f (Ici a)) (hmono : StrictMonoOn f (Ici a)) (hfx : f ~[atTop] id)
    {y : ℝ} (hy : f a < y) :
    ∃! x, a < x ∧ f x = y := by
  have htop : Tendsto f atTop atTop := hfx.symm.tendsto_atTop tendsto_id
  obtain ⟨x, hax, hfx'⟩ := intermediate_value_Ioi hf htop hy
  refine ⟨x, ⟨hax, hfx'⟩, fun x' hx' => ?_⟩
  exact hmono.injOn (mem_Ici.mpr hx'.1.le) (mem_Ici.mpr hax.le) (hx'.2.trans hfx'.symm)

/-- DLMF 2.2.2: if `f` is monotone on `[a, ∞)` with `f(x) ∼ x` as `x → +∞`, then any function `g`
such that `g y` is eventually a root of `f(x) = y` in `[a, ∞)` satisfies `g(y) ∼ y` as
`y → +∞`. -/
theorem MonotoneOn.root_isEquivalent {f : ℝ → ℝ} {a : ℝ} (hmono : MonotoneOn f (Ici a))
    (hfx : f ~[atTop] id) {g : ℝ → ℝ} (hg : ∀ᶠ y in atTop, a ≤ g y ∧ f (g y) = y) :
    g ~[atTop] id := by
  have hgt : Tendsto g atTop atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    set M' := max M a
    filter_upwards [hg, eventually_gt_atTop (f M')] with y hy hyM
    by_contra hlt
    push Not at hlt
    have h1 : f (g y) ≤ f M' := hmono (mem_Ici.mpr hy.1)
      (mem_Ici.mpr (le_max_right M a)) (hlt.le.trans (le_max_left M a))
    linarith [hy.2]
  have h := hfx.comp_tendsto hgt
  refine (IsEquivalent.congr_left h ?_).symm
  filter_upwards [hg] with y hy
  simpa using hy.2
