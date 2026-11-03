/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Orientation

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
* `Module.Basis.det_finCons_ne_zero`: `v` followed by a basis of `W` is a basis of `V`.
* `Module.Basis.eq_iff_eq_orientation_iff`: two orientations are equal exactly when they agree on
  whether they are the orientation of a fixed basis.

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

/-- The basis `v, b 0, …, b (k - 1)` of `V`, for a basis `b` of a subspace `W` of dimension `k` of
a space `V` of dimension `k + 1` and `v ∉ W`. -/
private def consBasis (hV : finrank R V = k + 1) (hv : v ∉ W) (b : Basis (Fin k) R W) :
    Basis (Fin (k + 1)) R V :=
  basisOfLinearIndependentOfCardEqFinrank
    ((b.linearIndependent.map' W.subtype W.ker_subtype).finCons (by
      rwa [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]))
    (by rw [Fintype.card_fin, hV])

private theorem coe_consBasis (hV : finrank R V = k + 1) (hv : v ∉ W) (b : Basis (Fin k) R W) :
    ⇑(consBasis hV hv b) = Fin.cons v (W.subtype ∘ b) :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- For a basis `c` of `V` beginning with `v` and continuing with a basis `b` of `W`, and a second
basis `b'` of `W`, the determinant of `v, b' 0, …, b' (k - 1)` with respect to `c` is that of `b'`
with respect to `b`: `u ↦ c.det (v, u)` is an alternating form on `W` taking the value `1` on
`b`. -/
private theorem det_cons_eq_det (b b' : Basis (Fin k) R W) (c : Basis (Fin (k + 1)) R V)
    (hc : ⇑c = Fin.cons v (W.subtype ∘ b)) :
    c.det (Fin.cons v (W.subtype ∘ b')) = b.det b' := by
  let f : W [⋀^Fin k]→ₗ[R] R := (c.det.curryLeft v).compLinearMap W.subtype
  have hf (u : Fin k → W) : f u = c.det (Fin.cons v (W.subtype ∘ u)) := (rfl)
  have h1 : f b = 1 := by rw [hf, ← hc, c.det_self]
  rw [← hf, f.eq_smul_basis_det b, h1, one_smul]

/-- **The vectors `v, b 0, …, b (k - 1)` form a basis.** For a basis `b` of a subspace `W` of
codimension one and `v ∉ W`, their determinant with respect to any basis of `V` is nonzero. -/
theorem _root_.Module.Basis.det_finCons_ne_zero (e : Basis (Fin (k + 1)) R V)
    (b : Basis (Fin k) R W) (hv : v ∉ W) : e.det (Fin.cons v (W.subtype ∘ b)) ≠ 0 := by
  have hV : finrank R V = k + 1 := by rw [finrank_eq_card_basis e, Fintype.card_fin]
  rw [← coe_consBasis hV hv b]
  exact (e.isUnit_det _).ne_zero

/-- Two orientations are equal exactly when they agree on whether they are the orientation of a
fixed basis `e`, since every orientation is that of `e` or its opposite. -/
theorem _root_.Module.Basis.eq_iff_eq_orientation_iff [LinearOrder R] [IsStrictOrderedRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι R V) (x y : Orientation R V ι) :
    x = y ↔ (x = e.orientation ↔ y = e.orientation) := by
  refine ⟨fun h ↦ h ▸ Iff.rfl, fun h ↦ ?_⟩
  rcases e.orientation_eq_or_eq_neg x with hx | hx
  · rw [hx, h.1 hx]
  · rcases e.orientation_eq_or_eq_neg y with hy | hy
    · exact absurd (h.2 hy) (hx ▸ (Module.Ray.ne_neg_self _).symm)
    · rw [hx, hy]

variable [LinearOrder R] [IsStrictOrderedRing R] (o : Orientation R V (Fin (k + 1)))
  (hV : finrank R V = k + 1) (hW : finrank R W = k) (hv : v ∉ W)

open Classical in
/-- The orientation of a subspace `W` of dimension `k` of a space `V` of dimension `k + 1`
induced by an orientation `o` of `V` and a vector `v ∉ W`: a basis `b` of `W` is positive exactly
when `v, b 0, …, b (k - 1)` is a positive basis of `V`
(`Orientation.transverse_eq_orientation_iff`). -/
def transverse : Orientation R W (Fin k) :=
  if (consBasis hV hv (refBasis hV hW)).orientation = o then (refBasis hV hW).orientation
  else -(refBasis hV hW).orientation

/-- **The transverse orientation is characterized by prepending the vector.** A basis `b` of `W`
is positive for the orientation induced by `o` and `v` exactly when the basis `c` of `V` with
`c = (v, b 0, …, b (k - 1))` is positive for `o`. -/
theorem transverse_eq_orientation_iff (b : Basis (Fin k) R W) (c : Basis (Fin (k + 1)) R V)
    (hc : ⇑c = Fin.cons v (W.subtype ∘ b)) :
    o.transverse hV hW hv = b.orientation ↔ c.orientation = o := by
  set b₀ := refBasis hV hW
  set c₀ := consBasis hV hv b₀
  -- `c` is positive for `c₀` exactly when `b` is positive for `b₀`.
  have hdet : c₀.det c = b₀.det b := by
    rw [hc]
    exact det_cons_eq_det b₀ b c₀ (coe_consBasis hV hv b₀)
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
  set c := consBasis hV hv b
  have hc : ⇑c = Fin.cons v (W.subtype ∘ b) := coe_consBasis hV hv b
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
  set c := consBasis hV hv b
  have hc : ⇑c = Fin.cons v (W.subtype ∘ b) := coe_consBasis hV hv b
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
