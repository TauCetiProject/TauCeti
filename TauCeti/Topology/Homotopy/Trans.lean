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
(`ContinuousMap.Homotopy.range_trans_subset`). At time `u` it is `F` at time `2 u` or `G` at
time `2 u - 1` (`ContinuousMap.Homotopy.trans_apply_of_eq_two_mul` and
`ContinuousMap.Homotopy.trans_apply_of_eq_two_mul_sub_one`, both valid at the seam `u = 1/2`).
In particular, if both homotopies take values in a set `S x` depending on the point `x`, so does
their concatenation (`ContinuousMap.Homotopy.trans_apply_mem`). With `S` constant, this is how
homotopies avoiding a compact set are chained in conditions such as simple connectivity at
infinity. With `S x` the fibre of a map `π` over `q x`, it says that homotopies through maps over
a base concatenate to a homotopy through maps over the base.

When `G` retraces `F` backwards at a point `x` — that is, `G (t, x) = F (σ t, x)` for all `t` —
the concatenation `F.trans G` at `x` is `F` reparametrised by the unit-interval tent map
`TauCeti.tent : I → I`, `t ↦ min (2 t) (2 - 2 t)`
(`ContinuousMap.Homotopy.trans_apply_of_retracing`).

## Main declarations

* `ContinuousMap.Homotopy.range_trans_subset`: the range of `F.trans G` lies in the union of the
  ranges of `F` and `G`.
* `ContinuousMap.Homotopy.trans_apply_mem`: if `F` and `G` take values in `S x` at each point
  `x`, so does `F.trans G`.
* `ContinuousMap.Homotopy.trans_apply_of_eq_two_mul`,
  `ContinuousMap.Homotopy.trans_apply_of_eq_two_mul_sub_one`: `F.trans G` at time `u` is `F` at
  time `2 u` and `G` at time `2 u - 1`, whenever these lie in the interval.
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

/-- If two homotopies take values in `S x` at each point `x`, so does their concatenation. -/
theorem trans_apply_mem {S : X → Set Y} {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂}
    (hF : ∀ t x, F (t, x) ∈ S x) (hG : ∀ t x, G (t, x) ∈ S x) (t : I) (x : X) :
    F.trans G (t, x) ∈ S x := by
  rw [trans_apply]
  split_ifs
  exacts [hF _ x, hG _ x]

/-- The value of `F.trans G` at time `u` is the value of `F` at any time `v` with `v = 2 * u`. -/
theorem trans_apply_of_eq_two_mul (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) {u : I} (v : I)
    (hv : (v : ℝ) = 2 * u) (x : X) : F.trans G (u, x) = F (v, x) := by
  rw [trans_apply]
  split_ifs with h
  · exact congrArg (fun t ↦ F (t, x)) (Subtype.ext hv.symm)
  · exfalso
    linarith [v.property.2]

/-- The value of `F.trans G` at time `u` is the value of `G` at any time `v` with
`v = 2 * u - 1`. -/
theorem trans_apply_of_eq_two_mul_sub_one (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) {u : I}
    (v : I) (hv : (v : ℝ) = 2 * u - 1) (x : X) : F.trans G (u, x) = G (v, x) := by
  rw [trans_apply]
  split_ifs with h
  · have hu : (u : ℝ) = 1 / 2 := le_antisymm h (by linarith [v.property.1])
    have hv₀ : v = 0 := Subtype.ext (by rw [hv, hu]; norm_num)
    rw [hv₀, apply_zero, ← apply_one F x]
    exact congrArg (fun t ↦ F (t, x)) (Subtype.ext (by simp [hu]))
  · exact congrArg (fun t ↦ G (t, x)) (Subtype.ext hv.symm)

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
