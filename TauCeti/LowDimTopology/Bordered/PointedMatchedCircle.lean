/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Labelling

import TauCeti.Combinatorics.ChordDiagram
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# Pointed matched circles

A *pointed matched circle* `Z` of Lipshitz, Ozsváth and Thurston is an oriented circle with a
basepoint `z` and `4k` further points `a₁, …, a_{4k}`, together with a *matching* of these points,
a two-to-one map `M : {a₁, …, a_{4k}} → {1, …, 2k}`, such that surgery on the circle along the
`2k` matched pairs yields a single circle. It parametrizes the boundary of a bordered
three-manifold: thickening the circle to a disk and attaching a one-handle along each matched pair
gives a surface with one boundary circle, of genus `k`, and capping that circle gives the closed
surface `F(Z)`. The algebra `A(Z)` of bordered Floer homology is the subalgebra of the strands
algebra `A(4k)` cut out by the matching.

Cutting the circle at its basepoint orders the points, and we identify them with `Fin (4 * k)` in
the order given by the orientation. The matching itself is a labelled perfect matching
`TauCeti.PerfectMatching.Labelling`, whose partner is a perfect matching of the points. The circle
minus the points is a union of open arcs, one ending at each point `p` and running from the previous
point `p - 1` (the arc ending at the first point starts at the last point and passes through the
basepoint). Surgery along a matched pair `{p, q}` removes small neighbourhoods of `p` and `q` and
reconnects the ends compatibly with the orientation: an arc arriving at `p` continues out of `q`,
and an arc arriving at `q` continues out of `p`. So after the surgeries, the arc ending at `p` is
followed by the arc ending at `partner p + 1`, and the components of the surgered circle are the
cycles of the permutation `finRotate (4 * k) * partner`, `p ↦ partner p + 1`. The surgery condition
says that this permutation is a single cycle through all the points. This is the boundary
permutation `finRotate n * σ` of the one-vertex chord diagram whose chords are the matched pairs, as
in `TauCeti/Combinatorics/ChordDiagram.lean`: the surgered circle is the boundary of the disk with a
band attached along each matched pair. The general facts about such diagrams with a single boundary
cycle, such as `4 ∣ n`, are proved there.

## Main definitions

* `TauCeti.PointedMatchedCircle k`: a matching of `4k` points by `2k` labels on which surgery
  yields a single circle.
* `TauCeti.PointedMatchedCircle.reverse`: the orientation reversal `-Z`, which reverses the order
  of the points and keeps the matching.
* `TauCeti.PointedMatchedCircle.antipodal k`: the pointed matched circle of genus `k` matching each
  point with the antipodal point, `p ↦ p mod 2k`; for `k = 1` it is the matched circle of the
  torus algebra.

## Main results

* `TauCeti.PointedMatchedCircle.apply_finRotate_ne`: in a pointed matched circle, two consecutive
  points (in the cyclic order, through the basepoint) are never matched.
* `TauCeti.PointedMatchedCircle.finRotate_mul_partner_antipodal`: surgery on the antipodal
  pointed matched circle of genus `k` is the rotation by `2k + 1` points.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2
  (pointed matched circles and their orientation reversal) and §11.1 (the genus-one pointed
  matched circle and the torus algebra).
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

/-- A *pointed matched circle* of genus `k` (Lipshitz–Ozsváth–Thurston): a matching of `4k` points
on an oriented circle with a basepoint, labelled by `Fin (2 * k)`, such that surgery on the circle
along the `2k` matched pairs yields a single circle. The points are identified with
`Fin (4 * k)` in the order in which they are met when going around the circle from the basepoint.
There is no loss in assuming `4k` points: see
`TauCeti.IsPerfectMatching.four_dvd_of_isCycleOn_finRotate_mul`. -/
structure PointedMatchedCircle (k : ℕ) extends
    PerfectMatching.Labelling (Fin (4 * k)) (Fin (2 * k)) where
  /-- Surgery along the matched pairs yields a single circle: the permutation `p ↦ partner p + 1`
  recording how surgery reconnects the arcs between consecutive points is a single cycle. -/
  isCycleOn_finRotate_mul_partner :
    (finRotate (4 * k) * toLabelling.partner.val).IsCycleOn Set.univ

namespace PointedMatchedCircle

variable {k : ℕ}

theorem toLabelling_injective : Function.Injective
    (toLabelling : PointedMatchedCircle k → PerfectMatching.Labelling (Fin (4 * k)) (Fin (2 * k)))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[ext]
theorem ext {Z Z' : PointedMatchedCircle k} (h : ∀ p, Z.toLabelling p = Z'.toLabelling p) :
    Z = Z' :=
  toLabelling_injective (PerfectMatching.Labelling.ext h)

/-- In a pointed matched circle, two consecutive points are never matched; this includes the last
and the first point, which are consecutive through the basepoint. -/
theorem apply_finRotate_ne (Z : PointedMatchedCircle k) (p : Fin (4 * k)) :
    Z.toLabelling (finRotate (4 * k) p) ≠ Z.toLabelling p := by
  intro hp
  rcases Z.toLabelling.apply_eq_apply_iff.1 hp with hp | hp
  · exact mem_support.1 (by simp [support_finRotate_of_le (by simpa using Z.two_le_card p)]) hp
  · exact Z.partner.prop.apply_ne_finRotate_of_isCycleOn Z.isCycleOn_finRotate_mul_partner p hp.symm

/-- The orientation reversal `-Z` of a pointed matched circle `Z`: the same points and matching,
on the circle with the opposite orientation. Going around the reversed circle from the basepoint
meets the points in the opposite order, so the `p`-th point of `-Z` is the `(4k - 1 - p)`-th point
of `Z`. -/
def reverse (Z : PointedMatchedCircle k) : PointedMatchedCircle k where
  toLabelling := Z.toLabelling.comp Fin.revPerm
  isCycleOn_finRotate_mul_partner := by
    rw [PerfectMatching.Labelling.partner_comp, PerfectMatching.congr_val, Fin.revPerm_symm,
      Z.partner.prop.involutive.isCycleOn_finRotate_mul_permCongr_revPerm_iff]
    exact Z.isCycleOn_finRotate_mul_partner

@[simp]
theorem toLabelling_reverse (Z : PointedMatchedCircle k) :
    Z.reverse.toLabelling = Z.toLabelling.comp Fin.revPerm := (rfl)

@[simp]
theorem reverse_reverse (Z : PointedMatchedCircle k) : Z.reverse.reverse = Z := by
  ext p
  simp

theorem reverse_involutive : Function.Involutive (reverse : PointedMatchedCircle k → _) :=
  reverse_reverse

/-! ### The antipodal pointed matched circle -/

private theorem mod_two_mul_eq_ite {k a : ℕ} (ha : a < 4 * k) :
    a % (2 * k) = if a < 2 * k then a else a - 2 * k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem add_two_mul_mod_eq_ite {k a : ℕ} (ha : a < 4 * k) :
    (a + 2 * k) % (4 * k) = if a < 2 * k then a + 2 * k else a - 2 * k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The antipodal point of `p` among `4k` points on a circle, `p + 2k` modulo `4k`. -/
private def antipode (p : Fin (4 * k)) : Fin (4 * k) :=
  ⟨(p + 2 * k) % (4 * k), Nat.mod_lt _ (by have := p.isLt; omega)⟩

/-- The labelled perfect matching of `4k` points pairing each point with its antipode. -/
private def antipodalLabelling (k : ℕ) : PerfectMatching.Labelling (Fin (4 * k)) (Fin (2 * k)) :=
  PerfectMatching.Labelling.ofPartner
    (fun p => ⟨p % (2 * k), Nat.mod_lt _ (by have := p.isLt; omega)⟩) antipode
    (fun p h => by
      have hp := p.isLt
      have h' := congrArg Fin.val h
      simp only [antipode, add_two_mul_mod_eq_ite p.isLt] at h'
      split_ifs at h' <;> omega)
    (fun p q => by
      simp only [Fin.ext_iff, antipode, mod_two_mul_eq_ite p.isLt, mod_two_mul_eq_ite q.isLt,
        add_two_mul_mod_eq_ite p.isLt]
      have := p.isLt
      have := q.isLt
      split_ifs <;> omega)
    (fun i => ⟨⟨i, by omega⟩, Fin.ext (Nat.mod_eq_of_lt i.isLt)⟩)

private theorem antipodalLabelling_partner (p : Fin (4 * k)) :
    (antipodalLabelling k).partner.val p = antipode p :=
  PerfectMatching.Labelling.partner_ofPartner _ _ _ _ _ p

/-- Surgery on the antipodal matching of `4k` points sends the arc ending at `p` to the arc
ending at `p + 2k + 1`. -/
private theorem finRotate_mul_antipodalLabelling_partner :
    finRotate (4 * k) * (antipodalLabelling k).partner.val = finRotate (4 * k) ^ (2 * k + 1) := by
  refine Equiv.ext fun p => Fin.ext ?_
  have h1 (q : Fin (4 * k)) : (finRotate (4 * k) q : ℕ) = (q + 1) % (4 * k) := by
    simpa using Fin.coe_finRotate_pow 1 q
  rw [Perm.mul_apply, antipodalLabelling_partner, Fin.coe_finRotate_pow, h1]
  simp only [antipode, Nat.mod_add_mod]
  ring_nf

/-- The pointed matched circle of genus `k` in which each point is matched with the antipodal
point: the `p`-th and the `(p + 2k)`-th points carry the label `p` for `p < 2k`. For `k = 1` it
matches the first point with the third and the second with the fourth; this is the genus-one
pointed matched circle, whose algebra is the torus algebra. -/
def antipodal (k : ℕ) : PointedMatchedCircle k where
  toLabelling := antipodalLabelling k
  isCycleOn_finRotate_mul_partner := by
    rw [finRotate_mul_antipodalLabelling_partner]
    refine isCycleOn_univ_finRotate_pow <| Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 (even_two.mul_right k).add_one)
    · simp only [Nat.coprime_mul_right_add_left, Nat.coprime_one_left_eq_true]

/-- Surgery on the antipodal pointed matched circle of genus `k` is the rotation of the `4k` points
by `2k + 1` steps. -/
@[simp]
theorem finRotate_mul_partner_antipodal :
    finRotate (4 * k) * (antipodal k).toLabelling.partner.val = finRotate (4 * k) ^ (2 * k + 1) :=
  finRotate_mul_antipodalLabelling_partner

/-- In the antipodal pointed matched circle, the `p`-th point carries the label `p mod 2k`. -/
@[simp]
theorem coe_toLabelling_antipodal_apply (p : Fin (4 * k)) :
    ((antipodal k).toLabelling p : ℕ) = p % (2 * k) :=
  congrArg Fin.val (congrFun (PerfectMatching.Labelling.coe_ofPartner _ _ _ _ _) p)

/-- In the antipodal pointed matched circle, the partner of the `p`-th point is the
`(p + 2k mod 4k)`-th point. -/
@[simp]
theorem coe_partner_antipodal_apply (p : Fin (4 * k)) :
    ((antipodal k).toLabelling.partner.val p : ℕ) = (p + 2 * k) % (4 * k) := by
  rw [antipodal, antipodalLabelling_partner, antipode]

/-- The genus-one pointed matched circle: of the four points, the first and the third carry one
label and the second and the fourth the other. -/
theorem coe_toLabelling_antipodal_one : ⇑(antipodal 1).toLabelling = ![0, 1, 0, 1] := by
  ext p
  rw [coe_toLabelling_antipodal_apply]
  fin_cases p <;> rfl

end PointedMatchedCircle

end TauCeti
