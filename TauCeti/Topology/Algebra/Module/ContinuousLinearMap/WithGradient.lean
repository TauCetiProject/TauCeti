/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Prescribing the gradient of a covector

Let `g` be a symmetric positive definite continuous bilinear form on a real topological vector
space `V`, `α` a continuous linear functional and `v` a vector with `α v > 0`. Then `v` is the
`g'`-gradient of `α`, that is `g' v = α`, for the bilinear form

`g' (w, z) = g (P w, P z) + α w * α z / α v`, where `P w = w - (α w / α v) • v`

(`ContinuousLinearMap.withGradient`). Here `P` is the projection onto the kernel of `α` along `v`:
`g'` agrees with `g` on `ker α`, makes `v` orthogonal to `ker α`, and gives `v` the squared length
`α v`. It is again symmetric and positive definite, and it is `g` itself when `v` was already the
`g`-gradient of `α`.

Pointwise, this is how a vector field `V'` along which a function `f` strictly decreases is made
the negative gradient of `f`: take `α = -df` and `v = V'`. The construction is a continuous linear
combination of `g` and of products of the covectors `α` and `g v`, so a field of such forms is as
regular as the data `g`, `α`, `v` wherever `α v ≠ 0`.

## Main definitions

* `ContinuousLinearMap.withGradient g α v`: the bilinear form `g'` above.

## Main results

* `ContinuousLinearMap.withGradient_def`: `g'` as a combination of `g` and of products of the
  covectors `α` and `g v`.
* `ContinuousLinearMap.withGradient_apply_eq`: the formula `g (P w, P z) + α w * α z / α v`.
* `ContinuousLinearMap.withGradient_apply_left_self`: `g' (v, z) = α z`.
* `ContinuousLinearMap.withGradient_comm`, `ContinuousLinearMap.withGradient_apply_self_pos`: `g'`
  is symmetric and positive definite when `g` is and `α v > 0`.
* `ContinuousLinearMap.withGradient_eq_self`: `g' = g` when `g v = α`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.2, where pseudo-gradient fields are compared with gradient fields.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  (g : V →L[ℝ] V →L[ℝ] ℝ) (α : V →L[ℝ] ℝ) (v : V)

/-- The bilinear form obtained from `g` by making `v` the gradient of the covector `α`:
`g' (w, z) = g (P w, P z) + α w * α z / α v` with `P w = w - (α w / α v) • v`, for symmetric `g`
(`ContinuousLinearMap.withGradient_apply_eq`). It is written as a linear combination of `g` and of
products of the covectors `α` and `g v`, so that it depends regularly on its data. -/
def withGradient : V →L[ℝ] V →L[ℝ] ℝ :=
  g - (α v)⁻¹ • (α.smulRight (g v) + (g v).smulRight α) +
    ((α v)⁻¹ + g v v / α v ^ 2) • α.smulRight α

/-- `ContinuousLinearMap.withGradient` as a combination of `g` and of products of covectors. -/
theorem withGradient_def :
    g.withGradient α v = g - (α v)⁻¹ • (α.smulRight (g v) + (g v).smulRight α) +
      ((α v)⁻¹ + g v v / α v ^ 2) • α.smulRight α :=
  (rfl)

/-- The defining formula of `ContinuousLinearMap.withGradient`. -/
theorem withGradient_apply (w z : V) :
    g.withGradient α v w z =
      g w z - (α w * g v z + g v w * α z) / α v + (1 / α v + g v v / α v ^ 2) * (α w * α z) := by
  simp [withGradient, div_eq_inv_mul]
  ring

variable {g α v}

/-- **The vector `v` is the `g'`-gradient of `α`**: `g' (v, z) = α z`. -/
@[simp]
theorem withGradient_apply_left_self (hv : α v ≠ 0) (z : V) : g.withGradient α v v z = α z := by
  rw [withGradient_apply]
  field_simp
  ring

/-- For symmetric `g`, `g' (w, z) = g (P w, P z) + α w * α z / α v` with
`P w = w - (α w / α v) • v` the projection onto the kernel of `α` along `v`. -/
theorem withGradient_apply_eq (hg : ∀ w z, g w z = g z w) (hv : α v ≠ 0) (w z : V) :
    g.withGradient α v w z =
      g (w - (α w / α v) • v) (z - (α z / α v) • v) + α w * α z / α v := by
  simp only [withGradient_apply, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    hg w v]
  field_simp
  ring

/-- `g'` is symmetric when `g` is. -/
theorem withGradient_comm (hg : ∀ w z, g w z = g z w) (w z : V) :
    g.withGradient α v w z = g.withGradient α v z w := by
  rw [withGradient_apply, withGradient_apply, hg w z]
  ring

/-- `g'` is positive definite when `g` is and `α v > 0`. -/
theorem withGradient_apply_self_pos (hg : ∀ w z, g w z = g z w)
    (hpos : ∀ w, w ≠ 0 → 0 < g w w) (hv : 0 < α v) {w : V} (hw : w ≠ 0) :
    0 < g.withGradient α v w w := by
  rw [withGradient_apply_eq hg hv.ne']
  have hnonneg : ∀ u, 0 ≤ g u u := fun u ↦ by
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact (hpos u hu).le
  rcases eq_or_ne (α w) 0 with hαw | hαw
  · -- On the kernel of `α` the projection is the identity, so `g'` is `g` there.
    simpa [hαw] using hpos w hw
  · exact add_pos_of_nonneg_of_pos (hnonneg _) (div_pos (mul_self_pos.2 hαw) hv)

/-- `g'` is `g` itself when `v` is already the `g`-gradient of `α`. -/
theorem withGradient_eq_self (hgv : ∀ z, g v z = α z) (hv : α v ≠ 0) :
    g.withGradient α v = g := by
  ext w z
  simp only [withGradient_apply, hgv]
  field_simp
  ring

end ContinuousLinearMap
