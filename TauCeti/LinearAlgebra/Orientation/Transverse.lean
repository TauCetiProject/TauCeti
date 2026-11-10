/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.Fin
public import TauCeti.LinearAlgebra.Orientation.Basis

/-!
# The orientation of a hyperplane transverse to a vector

Let `V` be a vector space of dimension `k + 1` over a linearly ordered field, oriented by `o`, and
let `W` be a subspace of dimension `k` with a vector `v ∉ W`. Then `o` and `v` orient `W`
(`Orientation.transverse`): a basis `b` of `W` is positive exactly when `v, b 0, …, b (k - 1)` is
a positive basis of `V` (`Orientation.transverse_eq_orientation_iff`). This is how an orientation
of a manifold together with a transverse vector field orients a codimension-one subbundle of the
tangent bundle, such as the tangent field of a transversely oriented codimension-one foliation.
Placing `v` first follows the outward-normal-first convention for boundaries; placing it last
instead multiplies the induced orientation by `(-1)ᵏ`.

The orientation can also be tested against an arbitrary basis `e` of `V`: `b` is positive exactly
when the sign of the determinant `e.det (v, b 0, …, b (k - 1))` matches whether `o` is the
orientation of `e` (`Orientation.transverse_eq_orientation_iff_det`). This is the form in which
continuity of induced orientations is checked in local trivializations.

## Main definitions

* `Orientation.transverse`: the orientation of `W` induced by an orientation of `V` and a vector
  `v ∉ W`.

## Main results

* `Orientation.transverse_eq_orientation_iff`: a basis `b` of `W` is positive exactly when the
  basis `v, b 0, …, b (k - 1)` of `V` is.
* `Orientation.transverse_eq_orientation_iff_det`: the same, read through the determinant with
  respect to any basis of `V`.
* `Orientation.transverse_neg`: reversing the orientation of `V` reverses the induced
  orientation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 15
  (orientations of hypersurfaces induced by a transverse vector field, Proposition 15.21).
-/

public section

noncomputable section

open Module

namespace Orientation

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V] {k : ℕ} {W : Submodule R V} {v : V}

/-- A basis of a subspace `W` of dimension `k` of a space `V` of dimension `k + 1`, the reference
basis against which `Orientation.transverse` is defined. -/
private def refBasis (hV : finrank R V = k + 1) (hW : finrank R W = k) : Basis (Fin k) R W :=
  haveI : FiniteDimensional R V := .of_finrank_eq_succ hV
  finBasisOfFinrankEq R W hW

variable [LinearOrder R] [IsStrictOrderedRing R] (o : Orientation R V (Fin (k + 1)))
  (hV : finrank R V = k + 1) (hW : finrank R W = k) (hv : v ∉ W)

open Classical in
/-- The orientation of a subspace `W` of dimension `k` of a space `V` of dimension `k + 1`
induced by an orientation `o` of `V` and a vector `v ∉ W`: a basis `b` of `W` is positive exactly
when `v, b 0, …, b (k - 1)` is a positive basis of `V`
(`Orientation.transverse_eq_orientation_iff`). -/
def transverse : Orientation R W (Fin k) :=
  if (Basis.mkFinConsOfNotMem v (refBasis hV hW) hv hV).orientation = o then
    (refBasis hV hW).orientation
  else -(refBasis hV hW).orientation

/-- **The transverse orientation is characterized by prepending the vector.** A basis `b` of `W`
is positive for the orientation induced by `o` and `v` exactly when the basis `c` of `V` with
`c = (v, b 0, …, b (k - 1))` is positive for `o`. -/
theorem transverse_eq_orientation_iff (b : Basis (Fin k) R W) (c : Basis (Fin (k + 1)) R V)
    (hc : ⇑c = Fin.cons v (W.subtype ∘ b)) :
    o.transverse hV hW hv = b.orientation ↔ c.orientation = o := by
  set b₀ := refBasis hV hW
  set c₀ := Basis.mkFinConsOfNotMem v b₀ hv hV
  -- `c` is positive for `c₀` exactly when `b` is positive for `b₀`.
  have hdet : c₀.det c = b₀.det b := by
    rw [hc]
    exact b₀.det_finCons_eq_det c₀ (Basis.coe_mkFinConsOfNotMem v b₀ hv hV) b
  have key : c₀.orientation = c.orientation ↔ b₀.orientation = b.orientation := by
    rw [c₀.orientation_eq_iff_det_pos, b₀.orientation_eq_iff_det_pos, hdet]
  rw [transverse]
  split_ifs with h
  · rw [← h, eq_comm (a := c.orientation), key]
  · obtain rfl : o = -c₀.orientation := (c₀.orientation_ne_iff_eq_neg o).1 (Ne.symm h)
    rw [eq_comm, ← b₀.orientation_ne_iff_eq_neg, ← c₀.orientation_ne_iff_eq_neg, ne_comm,
      ne_comm (a := c.orientation)]
    exact not_congr key.symm

/-- **The transverse orientation through determinants.** For any basis `e` of `V`, a basis `b` of
`W` is positive for the orientation induced by `o` and `v` exactly when the determinant
`e.det (v, b 0, …, b (k - 1))` is positive if `o` is the orientation of `e`, and negative
otherwise. -/
theorem transverse_eq_orientation_iff_det (b : Basis (Fin k) R W) (e : Basis (Fin (k + 1)) R V) :
    o.transverse hV hW hv = b.orientation ↔
      (o = e.orientation ↔ 0 < e.det (Fin.cons v (W.subtype ∘ b))) := by
  set c := Basis.mkFinConsOfNotMem v b hv hV
  have hc : ⇑c = Fin.cons v (W.subtype ∘ b) := Basis.coe_mkFinConsOfNotMem v b hv hV
  rw [transverse_eq_orientation_iff o hV hW hv b c hc, ← hc, ← e.orientation_eq_iff_det_pos]
  rcases e.orientation_eq_or_eq_neg o with rfl | rfl
  · simp only [true_iff]
    exact eq_comm
  · have hne : ¬(-e.orientation = e.orientation) := (Module.Ray.ne_neg_self _).symm
    simp only [hne, false_iff]
    rw [← e.orientation_ne_iff_eq_neg]
    exact ne_comm

/-- Reversing the orientation of `V` reverses the induced orientation of `W`. -/
@[simp]
theorem transverse_neg : (-o).transverse hV hW hv = -o.transverse hV hW hv := by
  set b := refBasis hV hW
  set c := Basis.mkFinConsOfNotMem v b hv hV
  have hc : ⇑c = Fin.cons v (W.subtype ∘ b) := Basis.coe_mkFinConsOfNotMem v b hv hV
  have hneg := transverse_eq_orientation_iff (-o) hV hW hv b c hc
  rcases b.orientation_eq_or_eq_neg (o.transverse hV hW hv) with h | h
  · -- `c` is positive for `o`, hence not for `-o`.
    have ho : c.orientation = o := (transverse_eq_orientation_iff o hV hW hv b c hc).1 h
    rw [h, ← b.orientation_ne_iff_eq_neg, ne_eq, hneg, ho]
    exact Module.Ray.ne_neg_self o
  · -- `c` is not positive for `o`, hence positive for `-o`.
    have ho : c.orientation ≠ o := fun ho ↦ Module.Ray.ne_neg_self b.orientation
      (((transverse_eq_orientation_iff o hV hW hv b c hc).2 ho).symm.trans h)
    have hc' : c.orientation = -o := by
      rcases c.orientation_eq_or_eq_neg o with h' | h'
      · exact absurd h'.symm ho
      · rw [h']
        exact (_root_.neg_neg c.orientation).symm
    rw [hneg.2 hc', h]
    exact (_root_.neg_neg b.orientation).symm

end Orientation
