/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Topology.Instances.AddCircle.Cover

/-!
# The translation flow of the circle `AddCircle p`

The real line acts on the circle `AddCircle p = ℝ ⧸ pℤ` by translation: time `t` moves `x` to
`x + [t]`. This is a flow of `ℝ` on the circle (`AddCircle.translationFlow p`), periodic with
period `p`: the time-`t` map fixes a point, equivalently is the identity, exactly when `t` is an
integer multiple of `p`. Multiplication by an integer `k` intertwines time `t` with time `k t`,
and the covering map `AddCircle p → AddCircle q`, for `p` a multiple of `q`, intertwines the two
flows at equal times.

These facts need no smooth structure and no positivity of `p`. For positive `p`, the smoothness
of the flow and its generator, the unit vector field `∂_t`, are developed in
`TauCeti.Geometry.Manifold.VectorField.AddCircle`.

## Main definitions

* `AddCircle.translationFlow p`: the flow `(t, x) ↦ x + [t]` of `ℝ` on `AddCircle p`.

## Main results

* `AddCircle.translationFlow_apply_eq_self_iff`, `AddCircle.translationFlow_eq_id_iff`,
  `AddCircle.translationFlow_add_period`: the time-`t` map fixes a point, equivalently is the
  identity, exactly when `t ∈ pℤ`; in particular the flow has period `p`.
* `AddCircle.zsmul_translationFlow`, `AddCircle.coverMap_translationFlow`: the integer
  multiplications and covering maps intertwine the translation flows, rescaling time by `k` and
  `1` respectively.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 9 (flows and their infinitesimal generators).
-/

public section

noncomputable section

namespace AddCircle

variable (p : ℝ)

/-- The translation flow of the circle `AddCircle p`: time `t` moves `x` to `x + [t]`. -/
def translationFlow : Flow ℝ (AddCircle p) where
  toFun t x := x + (t : AddCircle p)
  cont' := continuous_snd.add (continuous_quotient_mk'.comp continuous_fst)
  map_add' t s x := by
    rw [coe_add]
    abel
  map_zero' x := by simp

/-- The translation flow at time `t` adds the class of `t`. -/
@[simp]
theorem translationFlow_apply (t : ℝ) (x : AddCircle p) :
    translationFlow p t x = x + (t : AddCircle p) :=
  (rfl)

/-- The time-`t` map of the translation flow fixes the point `x` exactly when `t` is an integer
multiple of the period `p`. -/
theorem translationFlow_apply_eq_self_iff {t : ℝ} {x : AddCircle p} :
    translationFlow p t x = x ↔ t ∈ AddSubgroup.zmultiples p := by
  rw [translationFlow_apply, add_eq_left, coe_eq_zero_iff, AddSubgroup.mem_zmultiples_iff]

/-- The time-`t` map of the translation flow is the identity exactly when `t` is an integer
multiple of the period `p`. -/
theorem translationFlow_eq_id_iff {t : ℝ} :
    translationFlow p t = id ↔ t ∈ AddSubgroup.zmultiples p :=
  ⟨fun h ↦ (translationFlow_apply_eq_self_iff p).1 (congrFun h 0),
    fun h ↦ funext fun _ ↦ (translationFlow_apply_eq_self_iff p).2 h⟩

/-- The translation flow has period `p`. -/
@[simp]
theorem translationFlow_add_period (t : ℝ) :
    translationFlow p (t + p) = translationFlow p t := by
  funext x
  simp

/-- Multiplication by an integer `k` intertwines the time-`t` translation of `AddCircle p` with the
time-`k t` translation. -/
theorem zsmul_translationFlow (k : ℤ) (t : ℝ) (x : AddCircle p) :
    k • translationFlow p t x = translationFlow p (k * t) (k • x) := by
  rw [translationFlow_apply, translationFlow_apply, smul_add, ← coe_zsmul, zsmul_eq_mul]

/-- For `p` an integer multiple of `q`, the covering map `AddCircle p → AddCircle q` intertwines
the translation flows of the two circles at equal times. -/
theorem coverMap_translationFlow {q : ℝ} (h : p ∈ AddSubgroup.zmultiples q)
    (t : ℝ) (x : AddCircle p) :
    coverMap h (translationFlow p t x) = translationFlow q t (coverMap h x) := by
  rw [translationFlow_apply, map_add, coverMap_coe, translationFlow_apply]

end AddCircle
