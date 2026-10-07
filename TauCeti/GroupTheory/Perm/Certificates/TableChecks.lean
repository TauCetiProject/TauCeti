/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.TableActions
public import TauCeti.GroupTheory.Perm.Inversion
public import Mathlib.Data.List.Nodup
public import Mathlib.Algebra.Ring.Parity

/-!
# Uniform machines for cycles, support, and parity

The support test scans the point table. The single-cycle test uses bounded orbit
saturation. The parity test enumerates pairs and counts inversions.
-/

@[expose] public section

namespace TauCeti.PermutationTables

open Equiv Computability BitEncoding Turing

/-- Count points moved by the table. -/
def supportCount (n : ℕ) (t : Table) : ℕ :=
  (List.range n).countP fun x => !decide (lookup n t x = x)

/-- Check that the nonempty support is one orbit under the permutation. -/
def cycleCheck (n : ℕ) (t : Table) : Bool :=
  (List.range n).any fun a =>
    !decide (lookup n t a = a) &&
      (List.range n).all fun x =>
        decide (lookup n t x = x) || member (orbit n [t] a) x

/-- Enumerate all ordered pairs of points below `n`. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  ((List.range n).map fun x => (List.range n).map fun y => (x, y)).flatten

/-- Count inversions of the point-image table. -/
def inversions (n : ℕ) (t : Table) : ℕ :=
  (pairs n).countP fun p =>
    decide (p.1 < p.2) && decide (lookup n t p.2 < lookup n t p.1)

/-- Check even permutation parity using the inversion count. -/
def even (n : ℕ) (t : Table) : Bool := decide (inversions n t % 2 = 0)

@[fun_prop] theorem polyTime_supportCount :
    PolyTime (fun p : ℕ × Table => supportCount p.1 p.2) := by
  unfold supportCount
  fun_prop

@[fun_prop] theorem polyTime_singleOrbit :
    PolyTime (fun p : (ℕ × Table) × ℕ => orbit p.1.1 [p.1.2] p.2) :=
  PolyTime.comp (f := fun p : (ℕ × Table) × ℕ => ((p.1.1, [p.1.2]), p.2))
    polyTime_orbit (by fun_prop)

@[fun_prop] theorem polyTime_singleOrbitMember :
    PolyTime (fun p : ((ℕ × Table) × ℕ) × ℕ =>
      member (orbit p.1.1.1 [p.1.1.2] p.1.2) p.2) :=
  PolyTime.comp (f := fun p : ((ℕ × Table) × ℕ) × ℕ =>
    (orbit p.1.1.1 [p.1.1.2] p.1.2, p.2)) polyTime_member
    (PolyTime.pair
      (PolyTime.comp (f := fun p : ((ℕ × Table) × ℕ) × ℕ => p.1)
        polyTime_singleOrbit PolyTime.fst) PolyTime.snd)

@[fun_prop] theorem polyTime_cyclePoint :
    PolyTime (fun p : ((ℕ × Table) × ℕ) × ℕ =>
      decide (lookup p.1.1.1 p.1.1.2 p.2 = p.2) ||
        member (orbit p.1.1.1 [p.1.1.2] p.1.2) p.2) := by
  have he : PolyTime (fun p : ((ℕ × Table) × ℕ) × ℕ =>
      decide (lookup p.1.1.1 p.1.1.2 p.2 = p.2)) := by fun_prop
  exact PolyTime.comp (g := fun p : Bool × Bool => p.1 || p.2)
    (f := fun p : ((ℕ × Table) × ℕ) × ℕ =>
      (decide (lookup p.1.1.1 p.1.1.2 p.2 = p.2),
        member (orbit p.1.1.1 [p.1.1.2] p.1.2) p.2))
    PolyTime.or (PolyTime.pair he polyTime_singleOrbitMember)

@[fun_prop] theorem polyTime_cycleOrbit :
    PolyTime (fun p : (ℕ × Table) × ℕ =>
      (List.range p.1.1).all (fun x =>
        decide (lookup p.1.1 p.1.2 x = x) || member (orbit p.1.1 [p.1.2] p.2) x)) :=
  PolyTime.all (f := fun (p : (ℕ × Table) × ℕ) (x : ℕ) =>
    decide (lookup p.1.1 p.1.2 x = x) || member (orbit p.1.1 [p.1.2] p.2) x)
    polyTime_cyclePoint (by fun_prop)

@[fun_prop] theorem polyTime_cycleAt :
    PolyTime (fun p : (ℕ × Table) × ℕ =>
      !decide (lookup p.1.1 p.1.2 p.2 = p.2) &&
        (List.range p.1.1).all (fun x =>
          decide (lookup p.1.1 p.1.2 x = x) || member (orbit p.1.1 [p.1.2] p.2) x)) := by
  have he : PolyTime (fun p : (ℕ × Table) × ℕ =>
      !decide (lookup p.1.1 p.1.2 p.2 = p.2)) := by fun_prop
  exact PolyTime.comp (g := fun p : Bool × Bool => p.1 && p.2)
    (f := fun p : (ℕ × Table) × ℕ =>
      (!decide (lookup p.1.1 p.1.2 p.2 = p.2),
        (List.range p.1.1).all (fun x =>
          decide (lookup p.1.1 p.1.2 x = x) || member (orbit p.1.1 [p.1.2] p.2) x)))
    PolyTime.and (PolyTime.pair he polyTime_cycleOrbit)

@[fun_prop] theorem polyTime_cycleCheck :
    PolyTime (fun p : ℕ × Table => cycleCheck p.1 p.2) := by
  exact PolyTime.any (p := fun (p : ℕ × Table) (a : ℕ) =>
    !decide (lookup p.1 p.2 a = a) &&
      (List.range p.1).all (fun x =>
        decide (lookup p.1 p.2 x = x) || member (orbit p.1 [p.2] a) x)) polyTime_cycleAt
    (show PolyTime (fun p : ℕ × Table => List.range p.1) by fun_prop)

@[fun_prop] theorem polyTime_pairs : PolyTime pairs := by
  unfold pairs
  fun_prop

@[fun_prop] theorem polyTime_inversions :
    PolyTime (fun p : ℕ × Table => inversions p.1 p.2) := by
  unfold inversions
  fun_prop

@[fun_prop] theorem polyTime_even :
    PolyTime (fun p : ℕ × Table => even p.1 p.2) := by
  unfold even
  fun_prop

theorem supportCount_ofPerm {n : ℕ} (g : Perm (Fin n)) :
    supportCount n (ofPerm g) = g.support.card := by
  have h := (List.nodup_finRange n).card_eq_countP (P := fun x => g x ≠ x)
  have he : (Finset.univ.filter fun x => g x ≠ x) = g.support := by
    ext x
    simp
  rw [List.toFinset_finRange, he] at h
  rw [supportCount, range_eq_ofFn, List.ofFn_eq_map, List.countP_map]
  simpa [Function.comp_def, lookup_ofPerm, Fin.ext_iff] using h.symm

theorem cycleCheck_ofPerm {n : ℕ} (g : Perm (Fin n)) :
    cycleCheck n (ofPerm g) = FinitePermutation.cycleCheck g := by
  have ho (a : Fin n) : orbit n [ofPerm g] a.val = setBits (FiniteAction.orbit [g] a) :=
    orbit_ofPerm [g] a
  apply Bool.eq_iff_iff.mpr
  simp only [cycleCheck, any_range, Bool.and_eq_true, all_range, Bool.or_eq_true,
    decide_eq_true_eq, lookup_ofPerm, ho,
    member_setBits]
  simp [FinitePermutation.cycleCheck, Fin.ext_iff, or_iff_not_imp_left]

theorem product_map {α β γ δ : Type*} (f : α → γ) (g : β → δ)
    (l : List α) (u : List β) :
    (l.map f) ×ˢ (u.map g) = (l ×ˢ u).map (Prod.map f g) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.product_cons, ih, List.map_map, Function.comp_def]

theorem pairs_eq (n : ℕ) :
    pairs n = ((List.finRange n) ×ˢ (List.finRange n)).map
      (Prod.map Fin.val Fin.val) := by
  change (List.range n) ×ˢ (List.range n) = _
  rw [← List.map_coe_finRange_eq_range, product_map]

theorem inversions_ofPerm {n : ℕ} (g : Perm (Fin n)) :
    inversions n (ofPerm g) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ g p.2 < g p.1).card := by
  have hn := (List.nodup_finRange n).product (List.nodup_finRange n)
  have h := hn.card_eq_countP (P := fun p => p.1 < p.2 ∧ g p.2 < g p.1)
  have hu : ((List.finRange n) ×ˢ (List.finRange n)).toFinset =
      (Finset.univ : Finset (Fin n × Fin n)) := by
    ext p
    rcases p with ⟨x, y⟩
    simp
  rw [hu] at h
  rw [inversions, pairs_eq, List.countP_map]
  simpa [Function.comp_def, Prod.map, lookup_ofPerm] using h.symm

theorem units_neg_one_pow_eq_one (k : ℕ) :
    (-1 : ℤˣ) ^ k = 1 ↔ k % 2 = 0 := by
  rw [Units.ext_iff]
  change (-1 : ℤ) ^ k = 1 ↔ _
  rw [neg_one_pow_eq_one_iff_even (by decide), Nat.even_iff]

theorem units_neg_one_pow_eq_neg_one (k : ℕ) :
    (-1 : ℤˣ) ^ k = -1 ↔ k % 2 ≠ 0 := by
  rw [Units.ext_iff]
  change (-1 : ℤ) ^ k = -1 ↔ _
  rw [neg_one_pow_eq_neg_one_iff_odd (by decide), Nat.odd_iff]
  omega

theorem even_ofPerm {n : ℕ} (g : Perm (Fin n)) :
    even n (ofPerm g) = decide (Perm.sign g = 1) := by
  simp [even, inversions_ofPerm, TauCeti.sign_eq_neg_one_pow_card_inversion,
    units_neg_one_pow_eq_one]

theorem odd_ofPerm {n : ℕ} (g : Perm (Fin n)) :
    (!even n (ofPerm g)) = decide (Perm.sign g = -1) := by
  apply Bool.eq_iff_iff.mpr
  simp [even, inversions_ofPerm, TauCeti.sign_eq_neg_one_pow_card_inversion,
    units_neg_one_pow_eq_neg_one]

end TauCeti.PermutationTables
