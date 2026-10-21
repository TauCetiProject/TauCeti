/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.UnitInterval

/-!
# Evaluating a homotopy fixing a set at a variable time

Let `h : T × Y → Y`, with `T` compact, fix every point of a set `A ⊆ Y` at all times. Evaluating
`h` at a time `φ z` and a point `q z` gives a continuous function of `z` as soon as `q` is
continuous and `φ` is continuous at the points with `q z ∉ A`; nothing is required of `φ` over
`A`. This is a tube-lemma argument over the compact parameter space `T`.

Such times typically have the form `min 1 (t / u y)` for a control function `u : Y → I` vanishing
exactly on `A`, which is discontinuous at `A` but continuous off it. The file records that
continuity, together with the fact that the real value of such a control function is nonzero off
`A`.

## Main declarations

* `ContinuousMap.continuous_apply_prodMk_of_fixed`: a homotopy fixing `A`, evaluated at a time
  that is continuous away from `A`, is continuous.
* `TauCeti.coe_ne_zero_iff_notMem`: a function to `I` vanishing exactly on `A` has nonzero real
  value exactly off `A`.
* `TauCeti.continuousAt_projIcc_div_of_notMem`: the time `min 1 (t / u y)`, as a point of `I`, is
  continuous off the zero set of `u`.
-/

public section

open Set unitInterval Filter Topology

namespace ContinuousMap

variable {T Y Z : Type*} [TopologicalSpace T] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Let `h : T × Y → Y`, with `T` compact, fix every point of `A` at all times. Then evaluating
`h` at a point `q z` and at a time `φ z` gives a continuous function of `z`, as soon as `q` is
continuous and `φ` is continuous at the points `z` with `q z ∉ A`. No condition on `φ` is needed
over `A`: by compactness of `T`, near a point of `A` all the values `h (t, y)` are close to it. -/
theorem continuous_apply_prodMk_of_fixed [CompactSpace T] (h : C(T × Y, Y)) {A : Set Y}
    (hA : ∀ t, ∀ y ∈ A, h (t, y) = y) {q : Z → Y} (hq : Continuous q) {φ : Z → T}
    (hφ : ∀ z, q z ∉ A → ContinuousAt φ z) :
    Continuous fun z ↦ h (φ z, q z) := by
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  by_cases hz : q z ∈ A
  · rw [ContinuousAt, hA _ _ hz, tendsto_def]
    intro W hW
    -- the tube lemma: near `q z`, the whole slice `h (T × {y})` lies in `W`
    have htube : ∀ᶠ y in 𝓝 (q z), ∀ t ∈ (univ : Set T), h (t, y) ∈ W :=
      isCompact_univ.eventually_forall_of_forall_eventually fun t _ ↦
        (h.continuous.comp continuous_swap).continuousAt.preimage_mem_nhds
          (by simpa [hA t _ hz] using hW)
    exact (hq.continuousAt.eventually htube).mono fun z' hz' ↦ hz' (φ z') trivial
  · exact h.continuous.continuousAt.comp ((hφ z hz).prodMk hq.continuousAt)

end ContinuousMap

namespace TauCeti

/-- A function `u : X → I` vanishing exactly on `A` has nonzero real value exactly off `A`. -/
theorem coe_ne_zero_iff_notMem {X : Type*} {A : Set X} {u : X → I}
    (hu : ∀ x, u x = 0 ↔ x ∈ A) (x : X) :
    (u x : ℝ) ≠ 0 ↔ x ∉ A :=
  coe_ne_zero.trans (hu x).not

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {A : Set X}

/-- Let `u : X → I` be continuous and vanish exactly on `A`. Then the time
`min 1 (t z / u (q z))`, as a point of `I`, is continuous at every `z` with `q z ∉ A`, for
continuous `t : Z → I` and `q : Z → X`. -/
theorem continuousAt_projIcc_div_of_notMem (u : C(X, I)) (hu : ∀ x, u x = 0 ↔ x ∈ A)
    {t : Z → I} {q : Z → X} (ht : Continuous t) (hq : Continuous q) {z : Z} (hz : q z ∉ A) :
    ContinuousAt (fun z ↦ projIcc 0 1 zero_le_one ((t z : ℝ) / u (q z))) z :=
  continuous_projIcc.continuousAt.comp (ContinuousAt.div (by fun_prop) (by fun_prop)
    ((coe_ne_zero_iff_notMem hu _).2 hz))

end TauCeti
