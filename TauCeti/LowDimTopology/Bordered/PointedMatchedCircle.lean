/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin

import TauCeti.Data.Fin.Basic

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
the order given by the orientation. The circle minus the points is a union of open arcs, one
starting at each point `p` and running to the next point `p + 1` (the arc starting at the last
point passes through the basepoint and ends at the first point). Surgery along a matched pair
`{p, q}` removes small neighbourhoods of `p` and `q` and reconnects the ends compatibly with the
orientation: an arc arriving at `p` continues out of `q`, and an arc arriving at `q` continues out
of `p`. So after the surgeries, the arc starting at `p` is followed by the arc starting at the
partner of `p + 1`, and the components of the surgered circle are the cycles of the permutation
`p ↦ partner (p + 1)` (`TauCeti.Matching.surgeryPerm`). The surgery condition says that this
permutation is a single cycle through all the points.

## Main definitions

* `TauCeti.Matching α β`: a two-to-one map from a finite type `α` of points to a type `β` of
  labels.
* `TauCeti.Matching.partner`: the fixed-point-free involution exchanging the two points of each
  matched pair.
* `TauCeti.Matching.surgeryPerm`: for a matching of the points `Fin n` of a pointed circle, the
  permutation `p ↦ partner (p + 1)` of the arcs that records how surgery reconnects them.
* `TauCeti.PointedMatchedCircle k`: a matching of `4k` points by `2k` labels on which surgery
  yields a single circle.
* `TauCeti.PointedMatchedCircle.reverse`: the orientation reversal `-Z`, which reverses the order
  of the points and keeps the matching.
* `TauCeti.PointedMatchedCircle.antipodal k`: the pointed matched circle of genus `k` matching each
  point with the antipodal point, `p ↦ p mod 2k`; for `k = 1` it is the matched circle of the
  torus algebra.

## Main results

* `TauCeti.Matching.four_dvd_of_isCycleOn_surgeryPerm`: if surgery on a matching of `n` points
  yields a single circle then `4 ∣ n`, so pointed matched circles have `4k` points.
* `TauCeti.Matching.apply_finRotate_ne`: in a pointed matched circle, two consecutive points (in
  the cyclic order, through the basepoint) are never matched.
* `TauCeti.Matching.isCycleOn_surgeryPerm_comp_revPerm_iff`: reversing the orientation preserves
  the surgery condition.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2
  (pointed matched circles and their orientation reversal) and §11.1 (the genus-one pointed
  matched circle and the torus algebra).
-/

public section

open Finset Equiv Equiv.Perm

namespace TauCeti

/-- A *matching* of a finite type `α` of points by a type `β` of labels: a map `α → β` each of
whose fibres has exactly two elements, so that it pairs up the points, each pair carrying its own
label. This is the matching `M : a → [2k]` of a pointed matched circle. -/
structure Matching (α β : Type*) [Fintype α] [DecidableEq β] where
  /-- The label of each point. -/
  toFun : α → β
  /-- Each label is carried by exactly two points. -/
  card_filter_eq_two' : ∀ b, #{a | toFun a = b} = 2

namespace Matching

variable {α β γ : Type*} [Fintype α] [Fintype γ] [DecidableEq β]

instance : FunLike (Matching α β) α β where
  coe M := M.toFun
  coe_injective M N h := by cases M; cases N; congr

@[simp]
theorem toFun_eq_coe (M : Matching α β) : M.toFun = ⇑M := rfl

@[ext]
theorem ext {M N : Matching α β} (h : ∀ a, M a = N a) : M = N :=
  DFunLike.ext _ _ h

variable (M : Matching α β)

theorem card_filter_eq_two (b : β) : #{a | M a = b} = 2 :=
  M.card_filter_eq_two' b

private theorem existsUnique_ne_and_apply_eq (a : α) : ∃! b, b ≠ a ∧ M b = M a := by
  classical
  obtain ⟨c, hc⟩ := card_eq_one.1 <| show #(({b | M b = M a} : Finset α).erase a) = 1 by
    rw [card_erase_of_mem (by simp), M.card_filter_eq_two]
  have hmem (b : α) : b ≠ a ∧ M b = M a ↔ b = c := by
    simpa using Finset.ext_iff.1 hc b
  exact ⟨c, (hmem c).2 rfl, fun b hb => (hmem b).1 hb⟩

/-- The partner of a point: the other point with the same label. -/
private noncomputable def partnerFun (a : α) : α :=
  (M.existsUnique_ne_and_apply_eq a).exists.choose

private theorem ne_and_apply_eq_iff {a b : α} : b ≠ a ∧ M b = M a ↔ b = M.partnerFun a :=
  ⟨fun hb => (M.existsUnique_ne_and_apply_eq a).unique hb
    (M.existsUnique_ne_and_apply_eq a).exists.choose_spec,
    fun hb => hb ▸ (M.existsUnique_ne_and_apply_eq a).exists.choose_spec⟩

private theorem partnerFun_involutive : Function.Involutive M.partnerFun := fun a => by
  have h := M.ne_and_apply_eq_iff.2 (rfl : M.partnerFun a = M.partnerFun a)
  exact (M.ne_and_apply_eq_iff.1 ⟨h.1.symm, h.2.symm⟩).symm

/-- The *partner* involution of a matching, exchanging the two points of each matched pair. -/
noncomputable def partner : Perm α :=
  M.partnerFun_involutive.toPerm

theorem partner_eq_iff {a b : α} : M.partner a = b ↔ b ≠ a ∧ M b = M a := by
  rw [ne_and_apply_eq_iff, eq_comm]
  rfl

@[simp]
theorem apply_partner (a : α) : M (M.partner a) = M a :=
  (M.partner_eq_iff.1 rfl).2

theorem partner_ne (a : α) : M.partner a ≠ a :=
  (M.partner_eq_iff.1 rfl).1

@[simp]
theorem partner_partner (a : α) : M.partner (M.partner a) = a :=
  M.partnerFun_involutive a

@[simp]
theorem partner_mul_partner : M.partner * M.partner = 1 :=
  Perm.ext M.partner_partner

@[simp]
theorem partner_inv : M.partner⁻¹ = M.partner :=
  inv_eq_of_mul_eq_one_right M.partner_mul_partner

/-- Two points have the same label exactly when they are equal or partners. -/
theorem apply_eq_apply_iff {a b : α} : M b = M a ↔ b = a ∨ b = M.partner a := by
  rw [eq_comm (a := b) (b := M.partner a), partner_eq_iff]
  by_cases h : b = a <;> simp [h]

/-- The matching with labels `f`, given a fixed-point-free map `g` such that two points have the
same label exactly when they are equal or one is the image of the other under `g`. Every label
must be used. Its partner involution is `g` (`TauCeti.Matching.partner_ofPartner`). -/
def ofPartner (f : α → β) (g : α → α) (hg : ∀ a, g a ≠ a)
    (hfg : ∀ a b, f b = f a ↔ b = a ∨ b = g a) (hf : Function.Surjective f) : Matching α β where
  toFun := f
  card_filter_eq_two' b := by
    classical
    obtain ⟨a, rfl⟩ := hf b
    rw [show ({x | f x = f a} : Finset α) = {a, g a} by ext; simp [hfg]]
    exact card_pair (hg a).symm

@[simp]
theorem coe_ofPartner (f : α → β) (g : α → α) (hg : ∀ a, g a ≠ a)
    (hfg : ∀ a b, f b = f a ↔ b = a ∨ b = g a) (hf : Function.Surjective f) :
    ⇑(ofPartner f g hg hfg hf) = f := (rfl)

@[simp]
theorem partner_ofPartner (f : α → β) (g : α → α) (hg : ∀ a, g a ≠ a)
    (hfg : ∀ a b, f b = f a ↔ b = a ∨ b = g a) (hf : Function.Surjective f) (a : α) :
    (ofPartner f g hg hfg hf).partner a = g a := by
  rw [partner_eq_iff]
  exact ⟨hg a, ((hfg a (g a)).2 (Or.inr rfl))⟩

/-- The matching `M` pulled back along a bijection `e : γ ≃ α` of the points. -/
def comp (e : γ ≃ α) : Matching γ β where
  toFun := M ∘ e
  card_filter_eq_two' b := by
    rw [← M.card_filter_eq_two b, ← card_map e.toEmbedding]
    congr 1
    ext a
    simp

@[simp]
theorem comp_apply (e : γ ≃ α) (c : γ) : M.comp e c = M (e c) := (rfl)

@[simp]
theorem partner_comp_apply (e : γ ≃ α) (c : γ) :
    (M.comp e).partner c = e.symm (M.partner (e c)) := by
  rw [partner_eq_iff]
  exact ⟨fun h => M.partner_ne (e c) (e.symm_apply_eq.1 h), by simp⟩

/-- A type admitting a matching with a point has at least two points. -/
theorem two_le_card (M : Matching α β) (a : α) : 2 ≤ Fintype.card α := by
  rw [← M.card_filter_eq_two (M a)]
  exact card_le_univ _

/-! ### Surgery on a matching of the points of a pointed circle -/

variable {n : ℕ} (M : Matching (Fin n) β)

/-- For a matching `M` of the points `Fin n` of a pointed circle, ordered by its orientation, the
permutation `p ↦ partner (p + 1)` of the arcs between consecutive points, indexed by their
starting points. Surgery along the matched pairs joins the end of the arc starting at `p` to the
beginning of the arc starting at `partner (p + 1)`, so the circles obtained by surgery correspond
to the cycles of this permutation. -/
noncomputable def surgeryPerm : Perm (Fin n) :=
  M.partner * finRotate n

@[simp]
theorem surgeryPerm_apply (p : Fin n) : M.surgeryPerm p = M.partner (finRotate n p) := (rfl)

/-- If surgery on a matching of `n` points of a pointed circle yields a single circle, then `n` is
a multiple of four. Counting with signs: the partner involution is a product of `n / 2`
transpositions, `p ↦ p + 1` is an `n`-cycle, and their product is an `n`-cycle. -/
theorem four_dvd_of_isCycleOn_surgeryPerm (h : M.surgeryPerm.IsCycleOn Set.univ) : 4 ∣ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact dvd_zero 4
  have h2 : 2 ≤ n := by simpa using M.two_le_card ⟨0, hn⟩
  have := Fin.nontrivial_iff_two_le.2 h2
  have hσ : ∀ p, M.surgeryPerm p ≠ p := fun p => h.apply_ne Set.nontrivial_univ (Set.mem_univ p)
  have hsupp : M.surgeryPerm.support = univ := eq_univ_of_forall fun p => mem_support.2 (hσ p)
  have hcycle : M.surgeryPerm.IsCycle :=
    isCycle_iff_exists_isCycleOn.2 ⟨Set.univ, Set.nontrivial_univ, h, fun _ _ => trivial⟩
  have hpartner_supp : M.partner.support = univ :=
    eq_univ_of_forall fun p => mem_support.2 (M.partner_ne p)
  obtain ⟨m, hm⟩ : 2 ∣ n := by
    simpa [hpartner_supp] using two_dvd_card_support (σ := M.partner) (by simp [sq])
  have hfix : Fintype.card (Function.fixedPoints M.partner) = 0 :=
    Fintype.card_eq_zero_iff.2 ⟨fun ⟨p, hp⟩ => M.partner_ne p hp⟩
  have hsign := hcycle.sign
  rw [hsupp, card_univ, Fintype.card_fin, surgeryPerm, sign_mul,
    sign_of_pow_two_eq_one (by simp [sq]), sign_finRotate, Fintype.card_fin, hfix, Nat.sub_zero,
    hm, Nat.mul_div_cancel_left _ two_pos] at hsign
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hsign
  simp only [pow_succ, mul_neg, mul_one, pow_mul, pow_zero, neg_neg, one_pow] at hsign
  obtain ⟨t, rfl⟩ := (neg_one_pow_eq_neg_one_iff_odd (by decide)).1 hsign
  exact ⟨t + 1, by omega⟩

/-- In a matching of the points of a pointed circle on which surgery yields a single circle, no
arc closes up on its own after surgery. -/
theorem surgeryPerm_apply_ne (h : M.surgeryPerm.IsCycleOn Set.univ) (p : Fin n) :
    M.surgeryPerm p ≠ p :=
  have := Fin.nontrivial_iff_two_le.2 (by simpa using M.two_le_card p)
  h.apply_ne Set.nontrivial_univ (Set.mem_univ p)

/-- In a matching of the points of a pointed circle on which surgery yields a single circle, two
consecutive points are never matched; this includes the last and the first point, which are
consecutive through the basepoint. -/
theorem apply_finRotate_ne (h : M.surgeryPerm.IsCycleOn Set.univ) (p : Fin n) :
    M (finRotate n p) ≠ M p := by
  intro hp
  have h2 : 2 ≤ n := by simpa using M.two_le_card p
  rcases M.apply_eq_apply_iff.1 hp with hp | hp
  · exact mem_support.1 (by simp [support_finRotate_of_le h2]) hp
  · exact M.surgeryPerm_apply_ne h p (by rw [surgeryPerm_apply, hp, partner_partner])

/-- Reversing the order of the points conjugates the inverse of the surgery permutation. -/
theorem surgeryPerm_comp_revPerm :
    (M.comp Fin.revPerm).surgeryPerm =
      (Fin.revPerm * M.partner) * M.surgeryPerm⁻¹ * (Fin.revPerm * M.partner)⁻¹ := by
  refine Equiv.ext fun p => ?_
  have := p.neZero
  have hrev : (finRotate n p).rev = (finRotate n).symm p.rev := by
    simpa using Fin.rev_finRotate_rev p.rev
  simp only [surgeryPerm, mul_inv_rev, partner_inv]
  simp only [Perm.mul_apply, Perm.inv_def, partner_comp_apply, Fin.revPerm_symm, Fin.revPerm_apply,
    partner_partner, hrev]

/-- Reversing the orientation of a pointed circle, which reverses the order of its points,
preserves the condition that surgery on a matching yields a single circle. -/
theorem isCycleOn_surgeryPerm_comp_revPerm_iff :
    (M.comp Fin.revPerm).surgeryPerm.IsCycleOn Set.univ ↔ M.surgeryPerm.IsCycleOn Set.univ := by
  set g := Fin.revPerm * M.partner
  rw [surgeryPerm_comp_revPerm, ← isCycleOn_inv (f := M.surgeryPerm)]
  constructor
  · intro h
    have := h.conj (g := g⁻¹)
    rwa [show g⁻¹ * (g * M.surgeryPerm⁻¹ * g⁻¹) * g⁻¹⁻¹ = M.surgeryPerm⁻¹ by group,
      Set.image_univ_of_surjective (Equiv.surjective _)] at this
  · intro h
    have := h.conj (g := g)
    rwa [Set.image_univ_of_surjective (Equiv.surjective _)] at this

end Matching

/-- A *pointed matched circle* of genus `k` (Lipshitz–Ozsváth–Thurston): a matching of `4k` points
on an oriented circle with a basepoint, labelled by `Fin (2 * k)`, such that surgery on the circle
along the `2k` matched pairs yields a single circle. The points are identified with
`Fin (4 * k)` in the order in which they are met when going around the circle from the basepoint.
There is no loss in assuming `4k` points: see `TauCeti.Matching.four_dvd_of_isCycleOn_surgeryPerm`.
-/
structure PointedMatchedCircle (k : ℕ) extends Matching (Fin (4 * k)) (Fin (2 * k)) where
  /-- Surgery along the matched pairs yields a single circle. -/
  isCycleOn_surgeryPerm : toMatching.surgeryPerm.IsCycleOn Set.univ

namespace PointedMatchedCircle

variable {k : ℕ}

theorem toMatching_injective :
    Function.Injective (toMatching : PointedMatchedCircle k → Matching (Fin (4 * k)) (Fin (2 * k)))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[ext]
theorem ext {Z Z' : PointedMatchedCircle k} (h : ∀ p, Z.toMatching p = Z'.toMatching p) :
    Z = Z' :=
  toMatching_injective (Matching.ext h)

/-- The orientation reversal `-Z` of a pointed matched circle `Z`: the same points and matching,
on the circle with the opposite orientation. Going around the reversed circle from the basepoint
meets the points in the opposite order, so the `p`-th point of `-Z` is the `(4k - 1 - p)`-th point
of `Z`. -/
def reverse (Z : PointedMatchedCircle k) : PointedMatchedCircle k where
  toMatching := Z.toMatching.comp Fin.revPerm
  isCycleOn_surgeryPerm :=
    Z.toMatching.isCycleOn_surgeryPerm_comp_revPerm_iff.2 Z.isCycleOn_surgeryPerm

@[simp]
theorem toMatching_reverse (Z : PointedMatchedCircle k) :
    Z.reverse.toMatching = Z.toMatching.comp Fin.revPerm := (rfl)

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

/-- The matching of `4k` points pairing each point with its antipode. -/
private def antipodalMatching (k : ℕ) : Matching (Fin (4 * k)) (Fin (2 * k)) :=
  Matching.ofPartner (fun p => ⟨p % (2 * k), Nat.mod_lt _ (by have := p.isLt; omega)⟩) antipode
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

private theorem antipodalMatching_partner (p : Fin (4 * k)) :
    (antipodalMatching k).partner p = antipode p :=
  Matching.partner_ofPartner _ _ _ _ _ p

/-- The pointed matched circle of genus `k` in which each point is matched with the antipodal
point: the `p`-th and the `(p + 2k)`-th points carry the label `p` for `p < 2k`. For `k = 1` it
matches the first point with the third and the second with the fourth; this is the genus-one
pointed matched circle, whose algebra is the torus algebra. -/
def antipodal (k : ℕ) : PointedMatchedCircle k where
  toMatching := antipodalMatching k
  isCycleOn_surgeryPerm := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have := Fin.subsingleton_iff_le_one.2 (show 4 * 0 ≤ 1 by omega)
      exact isCycleOn_of_subsingleton _ _
    have hσ : (antipodalMatching k).surgeryPerm = finRotate (4 * k) ^ (2 * k + 1) := by
      refine Equiv.ext fun p => Fin.ext ?_
      have h1 : (finRotate (4 * k) p : ℕ) = (p + 1) % (4 * k) := by
        simpa using Fin.coe_finRotate_pow 1 p
      rw [Matching.surgeryPerm_apply, antipodalMatching_partner, Fin.coe_finRotate_pow]
      simp only [antipode, h1, Nat.mod_add_mod]
      ring_nf
    have hc : (finRotate (4 * k)).IsCycle := isCycle_finRotate_of_le (by omega)
    have hcop : Nat.Coprime (2 * k + 1) (orderOf (finRotate (4 * k))) := by
      rw [hc.orderOf, support_finRotate_of_le (by omega), card_univ, Fintype.card_fin]
      have h4 : Nat.Coprime (2 * k + 1) 4 :=
        Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 (even_two.mul_right k).add_one)
      exact h4.mul_right <| by
        simp only [Nat.coprime_mul_right_add_left, Nat.coprime_one_left_eq_true]
    rw [hσ]
    convert (hc.pow_iff.2 hcop).isCycleOn
    refine iff_of_true (Set.mem_univ _) (mem_support.1 ?_)
    rw [support_pow_coprime hcop, support_finRotate_of_le (by omega)]
    exact mem_univ _

/-- In the antipodal pointed matched circle, the `p`-th point carries the label `p mod 2k`. -/
@[simp]
theorem coe_toMatching_antipodal_apply (p : Fin (4 * k)) :
    ((antipodal k).toMatching p : ℕ) = p % (2 * k) := (rfl)

/-- In the antipodal pointed matched circle, the partner of the `p`-th point is the
`(p + 2k mod 4k)`-th point. -/
@[simp]
theorem coe_partner_antipodal_apply (p : Fin (4 * k)) :
    ((antipodal k).toMatching.partner p : ℕ) = (p + 2 * k) % (4 * k) := by
  rw [antipodal, antipodalMatching_partner, antipode]

/-- The genus-one pointed matched circle: of the four points, the first and the third carry one
label and the second and the fourth the other. -/
theorem toMatching_antipodal_one : ⇑(antipodal 1).toMatching = ![0, 1, 0, 1] := by
  ext p
  fin_cases p <;> rfl

end PointedMatchedCircle

end TauCeti
