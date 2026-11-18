/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Instances.AddCircle.Real

import TauCeti.Algebra.AddCircle

/-!
# The orbit of a rotation of the circle

For a point `a` of the circle `AddCircle p` of period `p > 0`, the rotation `(a + ·)` moves a
point `x` along the forward orbit `n ↦ x + n • a`, `n : ℕ`. This file records the elementary
dichotomy for these orbits:

* if `a` has infinite additive order, every forward orbit is dense, and the rotation is minimal:
  a nonempty closed set mapped into itself by `(a + ·)` is the whole circle;
* if `a` has finite additive order, the orbit of `0` is finite; when `a` is the class of a
  rational multiple `q * p` of the period, the orbit of `0` is exactly the `q.den`-torsion of the
  circle, so it has `q.den` points. These two counting statements hold for a positive period in
  any linearly ordered field, as does Mathlib's `AddCircle.addOrderOf_coe_rat`.

In the language of rhythm, a pulse of period `q * p` played against a cycle of length `p`
resolves after `q.den` beats, while a pulse of irrational ratio to the cycle comes arbitrarily
close to every point of the cycle.

The dense case reduces to Mathlib's `AddCircle.denseRange_zsmul_iff` through
`denseRange_zsmul_iff_nsmul`, which says that in a compact group the forward multiples of a
point are dense exactly when all of its integer multiples are.

## Main statements

* `AddCircle.denseRange_nsmul_iff`: the `ℕ`-orbit of `a` is dense iff `addOrderOf a = 0`.
* `AddCircle.denseRange_add_nsmul_iff`: the same for the forward orbit of any point.
* `AddCircle.eq_univ_of_isClosed_of_mapsTo_add`: minimality of a rotation of infinite order.
* `AddCircle.range_nsmul_coe_rat`: the orbit of the class of `q * p` is the `q.den`-torsion.
* `AddCircle.ncard_range_nsmul_coe_rat`: that orbit has exactly `q.den` points.
* `AddCircle.denseRange_nsmul_xor_finite_range`: every `ℕ`-orbit is dense or finite, and never
  both.

## References

* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, GTM 259,
  §1.1 (circle rotations and minimality of irrational rotations).
-/

public section

open Set
open scoped AddSubgroup

namespace AddCircle

section Real

variable {p : ℝ} [Fact (0 < p)] {a : AddCircle p}

/-- The `ℕ`-orbit of a point of the circle is dense exactly when the point has infinite additive
order. This is the forward-orbit form of `AddCircle.denseRange_zsmul_iff`. -/
theorem denseRange_nsmul_iff : DenseRange (· • a : ℕ → AddCircle p) ↔ addOrderOf a = 0 :=
  denseRange_zsmul_iff_nsmul.symm.trans denseRange_zsmul_iff

/-- The `ℕ`-orbit of the class of a real number `x` is dense in the circle of period `p` exactly
when `x / p` is irrational. This is the forward-orbit form of
`AddCircle.denseRange_zsmul_coe_iff`. -/
theorem denseRange_nsmul_coe_iff {x : ℝ} :
    DenseRange (· • (x : AddCircle p) : ℕ → AddCircle p) ↔ Irrational (x / p) :=
  denseRange_zsmul_iff_nsmul.symm.trans denseRange_zsmul_coe_iff

/-- The forward orbit `n ↦ x + n • a` of any point `x` under the rotation by `a` is dense exactly
when `a` has infinite additive order. -/
theorem denseRange_add_nsmul_iff (x : AddCircle p) :
    DenseRange (fun n : ℕ ↦ x + n • a) ↔ addOrderOf a = 0 := by
  have key (y : AddCircle p) {f : ℕ → AddCircle p} (hf : DenseRange f) :
      DenseRange (fun n ↦ y + f n) :=
    (Homeomorph.addLeft y).surjective.denseRange.comp hf (continuous_const.add continuous_id)
  rw [← denseRange_nsmul_iff]
  refine ⟨fun h ↦ ?_, key x⟩
  simpa using key (-x) h

/-- A rotation of the circle by a point of infinite order is minimal: a nonempty closed set which
the rotation maps into itself is the whole circle. -/
theorem eq_univ_of_isClosed_of_mapsTo_add (ha : addOrderOf a = 0) {s : Set (AddCircle p)}
    (hs : IsClosed s) (hne : s.Nonempty) (hmaps : MapsTo (a + ·) s s) : s = univ := by
  obtain ⟨x, hx⟩ := hne
  refine hs.dense_iff.mp (((denseRange_add_nsmul_iff x).mpr ha).mono ?_)
  rintro _ ⟨n, rfl⟩
  simpa [add_left_iterate, add_comm] using hmaps.iterate n hx

/-- The rhythmic dichotomy: the `ℕ`-orbit of a point of the circle is either dense or finite, and
never both. It is dense for a point of infinite additive order and finite otherwise. -/
theorem denseRange_nsmul_xor_finite_range (a : AddCircle p) :
    Xor (DenseRange (· • a : ℕ → AddCircle p)) (range (· • a : ℕ → AddCircle p)).Finite := by
  rw [denseRange_nsmul_iff, ← AddSubmonoid.coe_multiples, finite_multiples,
    addOrderOf_eq_zero_iff]
  exact xor_not_left.mpr Iff.rfl

end Real

section Rational

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {p : 𝕜} [Fact (0 < p)]

/-- The `ℕ`-orbit of the class of a rational multiple `q * p` of the period is the
`q.den`-torsion of the circle. -/
theorem range_nsmul_coe_rat (q : ℚ) :
    range (· • ((q * p : 𝕜) : AddCircle p) : ℕ → AddCircle p) =
      ((AddCircle p)[(q.den : ℤ)] : Set (AddCircle p)) := by
  have hfin : IsOfFinAddOrder ((q * p : 𝕜) : AddCircle p) := by
    rw [← addOrderOf_pos_iff, addOrderOf_coe_rat]
    exact q.pos
  rw [← AddSubmonoid.coe_multiples, hfin.multiples_eq_zmultiples,
    eq_torsionBy_of_natCard_eq p (Nat.cast_ne_zero.mpr q.den_nz)
      (H := AddSubgroup.zmultiples _) (by rw [Nat.card_zmultiples, addOrderOf_coe_rat])]

/-- The `ℕ`-orbit of the class of a rational multiple `q * p` of the period has exactly `q.den`
points: a pulse of period `q * p` against a cycle of length `p` resolves after `q.den` beats. -/
theorem ncard_range_nsmul_coe_rat (q : ℚ) :
    (range (· • ((q * p : 𝕜) : AddCircle p) : ℕ → AddCircle p)).ncard = q.den := by
  rw [← AddSubmonoid.coe_multiples, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
    Nat.card_addSubmonoidMultiples, addOrderOf_coe_rat]

end Rational

end AddCircle
