/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Topology.UnitInterval.Basic

/-!
# Concatenation of homotopies: range and retracing

The concatenation `F.trans G` of homotopies runs `F` on the first half of the interval and `G` on
the second half, so every value it takes is a value of `F` or of `G`
(`ContinuousMap.Homotopy.range_trans_subset`). In particular, if both homotopies take values in a
set `S`, so does their concatenation (`ContinuousMap.Homotopy.trans_apply_mem`); this is how
homotopies avoiding a compact set are chained in conditions such as simple connectivity at
infinity.

When `G` retraces `F` backwards at a point `x` — that is, `G (t, x) = F (σ t, x)` for all `t` —
the concatenation `F.trans G` at `x` is `F` reparametrised by the unit-interval tent map
`TauCeti.tent : I → I`, `t ↦ min (2 t) (2 - 2 t)`
(`ContinuousMap.Homotopy.trans_apply_of_retracing`).

## Main declarations

* `ContinuousMap.Homotopy.range_trans_subset` and `ContinuousMap.Homotopy.trans_apply_mem`: the
  range of `F.trans G` lies in the union of the ranges of `F` and `G`.
* `ContinuousMap.Homotopy.trans_apply_of_retracing`: at a point where `G` runs backwards along
  `F`, `F.trans G (t, x) = F (TauCeti.tent t, x)`.
-/

public section

open Set unitInterval

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ f₂ : C(X, Y)}

/-- Every value of a concatenated homotopy `F.trans G` is a value of `F` or of `G`. -/
theorem range_trans_subset (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    range (F.trans G) ⊆ range F ∪ range G := by
  rintro _ ⟨x, rfl⟩
  rw [trans_apply]
  split_ifs
  exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]

/-- If two homotopies take values in `S`, so does their concatenation. -/
theorem trans_apply_mem {S : Set Y} {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂}
    (hF : ∀ x, F x ∈ S) (hG : ∀ x, G x ∈ S) (x : I × X) : F.trans G x ∈ S := by
  obtain ⟨y, hy⟩ | ⟨y, hy⟩ := range_trans_subset F G ⟨x, rfl⟩
  exacts [hy ▸ hF y, hy ▸ hG y]

/-- At a point where the homotopy `G` runs backwards along `F`, the concatenation `F.trans G`
is `F` reparametrised by `TauCeti.tent`. -/
theorem trans_apply_of_retracing (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) {x : X}
    (hG : ∀ t, G (t, x) = F (σ t, x)) (t : I) :
    F.trans G (t, x) = F (TauCeti.tent t, x) := by
  rw [trans_apply]
  split_ifs with ht
  · congr 2
    ext
    simp [min_eq_left (by linarith : (2 : ℝ) * t ≤ 2 - 2 * t)]
  · rw [hG]
    congr 2
    ext
    simp only [TauCeti.coe_tent, coe_symm_eq]
    rw [min_eq_right (by linarith)]
    ring

end ContinuousMap.Homotopy
