/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Construction
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Explicit successful permutation-group families

The lists enumerate pairs or triples of points, never permutations. Ordered
pairs list each transposition twice; this harmless duplication keeps the
construction uniform and still gives at most `n²` ambient generators.
-/

open Equiv Equiv.Perm Subgroup MulAction
open TauCeti.FinitePermutation TauCeti.CertifiedPermutation TauCeti.CertificateWire
open TauCeti.CertificateConstruction

@[expose] public section

namespace TauCeti.SuccessfulFamilies

/-- List transpositions on all ordered distinct pairs of allowed points. -/
def swaps (degree : ℕ) (allowed : Fin degree → Bool) : List (Perm (Fin degree)) :=
  (List.finRange degree).flatMap fun a =>
    ((List.finRange degree).filter fun b => allowed a && allowed b && decide (a ≠ b)).map
      fun b => swap a b

/-- List three-cycles on all ordered distinct triples of allowed points. -/
def triples (degree : ℕ) (allowed : Fin degree → Bool) : List (Perm (Fin degree)) :=
  (List.finRange degree).flatMap fun a =>
    (List.finRange degree).flatMap fun b =>
      ((List.finRange degree).filter fun c =>
        allowed a && allowed b && allowed c && decide (a ≠ b) && decide (a ≠ c) &&
          decide (b ≠ c)).map fun c => swap a b * swap b c

theorem mem_swaps_iff {degree : ℕ} (allowed : Fin degree → Bool) (g : Perm (Fin degree)) :
    g ∈ swaps degree allowed ↔
      ∃ a b, allowed a = true ∧ allowed b = true ∧ a ≠ b ∧ swap a b = g := by
  simp [swaps, List.mem_flatMap, and_assoc]

theorem mem_triples_iff {degree : ℕ} (allowed : Fin degree → Bool) (g : Perm (Fin degree)) :
    g ∈ triples degree allowed ↔
      ∃ a b c, allowed a = true ∧ allowed b = true ∧ allowed c = true ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ swap a b * swap b c = g := by
  simp [triples, List.mem_flatMap, and_assoc]

theorem swaps_subset {degree : ℕ} (allowed : Fin degree → Bool) :
    ∀ g ∈ swaps degree allowed, g ∈ swaps degree (fun _ => true) := by
  intro g hg
  obtain ⟨a, b, _, _, hab, h⟩ := (mem_swaps_iff allowed g).mp hg
  exact (mem_swaps_iff _ g).mpr ⟨a, b, rfl, rfl, hab, h⟩

theorem triples_subset {degree : ℕ} (allowed : Fin degree → Bool) :
    ∀ g ∈ triples degree allowed, g ∈ triples degree (fun _ => true) := by
  intro g hg
  obtain ⟨a, b, c, _, _, _, hab, hac, hbc, h⟩ := (mem_triples_iff allowed g).mp hg
  exact (mem_triples_iff _ g).mpr ⟨a, b, c, rfl, rfl, rfl, hab, hac, hbc, h⟩

theorem ambient_swaps (degree : ℕ) :
    FiniteAction.ambientGroup (swaps degree (fun _ => true)) = ⊤ := by
  apply top_unique
  rw [← closure_isSwap]
  apply closure_mono
  intro g hg
  obtain ⟨a, b, hab, h⟩ := hg
  exact (mem_swaps_iff _ g).mpr ⟨a, b, rfl, rfl, hab, h.symm⟩

theorem triple_isThreeCycle {degree : ℕ} {a b c : Fin degree}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsThreeCycle (swap a b * swap b c) := by
  rw [swap_comm a b]
  exact isThreeCycle_swap_mul_swap_same hab.symm hbc hac

theorem ambient_triples (degree : ℕ) :
    FiniteAction.ambientGroup (triples degree (fun _ => true)) = alternatingGroup (Fin degree) := by
  rw [FiniteAction.ambientGroup, ← closure_three_cycles_eq_alternating]
  congr 1
  ext g
  constructor
  · intro hg
    obtain ⟨a, b, c, _, _, _, hab, hac, hbc, rfl⟩ := (mem_triples_iff _ g).mp hg
    exact triple_isThreeCycle hab hac hbc
  · intro hg
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hg.card_support]; decide)
    have hn := (hg.nodup_iff_mem_support).mpr ha
    have hne : a ≠ g a ∧ a ≠ g (g a) ∧ g a ≠ g (g a) := by
      simpa [and_assoc] using hn
    exact (mem_triples_iff _ g).mpr
      ⟨a, g a, g (g a), rfl, rfl, rfl, hne.1, hne.2.1, hne.2.2,
        ((hg.eq_swap_mul_swap_iff_mem_support).mpr ha).symm⟩

theorem primitive_top (degree : ℕ) :
    IsPreprimitive (⊤ : Subgroup (Perm (Fin degree))) (Fin degree) := by
  let φ : (⊤ : Subgroup (Perm (Fin degree))) → Perm (Fin degree) := Subgroup.topEquiv
  let f : Fin degree →ₑ[φ] Fin degree := { toFun := id, map_smul' _ _ := rfl }
  exact (isPreprimitive_congr Subgroup.topEquiv.surjective
    (show Function.Bijective f from Function.bijective_id)).mpr inferInstance

/-- The fixed-set mask selecting the point with index zero. -/
def fixedMask {degree : ℕ} (x : Fin degree) : Bool := decide (x.val = 0)

/-- The complement mask of the fixed point zero. -/
def allowed {degree : ℕ} (x : Fin degree) : Bool := !fixedMask x

theorem complement_ne_zero {degree : ℕ} (i : Fin (complement (@fixedMask degree)).length) :
    ((complement (@fixedMask degree)).get i).val ≠ 0 := by
  have h := (complement (@fixedMask degree)).get_mem i
  simpa [complement, fixedMask] using h

theorem fixedSet_eq_singleton {degree : ℕ} (hdegree : 0 < degree) :
    (Finset.univ.filter fun x => fixedMask x) = {⟨0, hdegree⟩} := by
  ext x
  simp [fixedMask, Fin.ext_iff]

/-- The point with index one, used as the orbit base. -/
def base {degree : ℕ} (hdegree : 4 ≤ degree) : Fin degree := ⟨1, by omega⟩

/-- The point with index two, used in explicit cycle witnesses. -/
def second {degree : ℕ} (hdegree : 4 ≤ degree) : Fin degree := ⟨2, by omega⟩

/-- The point with index three, used in explicit cycle witnesses. -/
def third {degree : ℕ} (hdegree : 4 ≤ degree) : Fin degree := ⟨3, by omega⟩

theorem swaps_fix_zero {degree : ℕ} :
    ∀ g ∈ swaps degree allowed, ∀ x, fixedMask x = true → g x = x := by
  intro g hg x hx
  obtain ⟨a, b, ha, hb, _, rfl⟩ := (mem_swaps_iff _ g).mp hg
  have ha' : a.val ≠ 0 := by simpa [allowed, fixedMask] using ha
  have hb' : b.val ≠ 0 := by simpa [allowed, fixedMask] using hb
  have hx' : x.val = 0 := by simpa [fixedMask] using hx
  apply swap_apply_of_ne_of_ne <;> intro h
  · exact ha' (h ▸ hx')
  · exact hb' (h ▸ hx')

theorem triples_fix_zero {degree : ℕ} :
    ∀ g ∈ triples degree allowed, ∀ x, fixedMask x = true → g x = x := by
  intro g hg x hx
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, rfl⟩ := (mem_triples_iff _ g).mp hg
  have hbc' : swap b c ∈ swaps degree allowed :=
    (mem_swaps_iff _ _).mpr ⟨b, c, hb, hc, hbc, rfl⟩
  have hab' : swap a b ∈ swaps degree allowed :=
    (mem_swaps_iff _ _).mpr ⟨a, b, ha, hb, hab, rfl⟩
  rw [mul_apply, swaps_fix_zero _ hbc' x hx, swaps_fix_zero _ hab' x hx]

theorem triples_even {degree : ℕ} : ∀ g ∈ triples degree allowed, g.sign = 1 := by
  intro g hg
  obtain ⟨a, b, c, _, _, _, hab, hac, hbc, rfl⟩ := (mem_triples_iff _ g).mp hg
  exact (triple_isThreeCycle hab hac hbc).sign

/-- An empty or one-letter transposition word taking the base to a complement point. -/
def symmetricOrbit {degree : ℕ} (hdegree : 5 ≤ degree)
    (i : Fin (complement (@fixedMask degree)).length) :
    Word (swaps degree allowed).length :=
  let x := (complement (@fixedMask degree)).get i
  let b := base (by omega : 4 ≤ degree)
  if hx : x = b then [] else
    [(indexOfMem (swaps degree allowed) (swap b x)
      ((mem_swaps_iff _ _).mpr ⟨b, x,
        by simp [b, base, allowed, fixedMask],
        by simpa [x, allowed, fixedMask] using complement_ne_zero i,
        Ne.symm hx, rfl⟩), false)]

theorem symmetricOrbit_reaches {degree : ℕ} (hdegree : 5 ≤ degree)
    (i : Fin (complement (@fixedMask degree)).length) :
    wordValue (swaps degree allowed) (symmetricOrbit hdegree i) (base (by omega)) =
      (complement (@fixedMask degree)).get i := by
  dsimp only [symmetricOrbit]
  split
  · rename_i h
    simpa only [wordValue, List.map_nil, List.prod_nil, one_apply] using h.symm
  · simp only [wordValue, letterValue, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Bool.false_eq_true, ite_false, mul_one]
    rw [indexOfMem_spec]
    exact swap_apply_left _ _

/-- The index of the symmetric family’s transposition prime-cycle witness. -/
def symmetricIndex {degree : ℕ} (hdegree : 5 ≤ degree) :
    Fin (swaps degree allowed).length :=
  indexOfMem (swaps degree allowed) (swap (base (by omega)) (second (by omega)))
    ((mem_swaps_iff _ _).mpr ⟨base (by omega), second (by omega),
      by simp [base, allowed, fixedMask],
      by simp [second, allowed, fixedMask],
      by simp [base, second, Fin.ext_iff], rfl⟩)

theorem symmetricIndex_spec {degree : ℕ} (hdegree : 5 ≤ degree) :
    (swaps degree allowed).get (symmetricIndex hdegree) =
      swap (base (by omega)) (second (by omega)) :=
  indexOfMem_spec _ _ _

/-- An explicit symmetric normal-closure certificate for every degree at least five. -/
def symmetricCertificate {degree : ℕ} (hdegree : 5 ≤ degree) :
    RawCertificate degree (swaps degree (fun _ => true)).length :=
  make (swaps degree (fun _ => true)) (swaps degree allowed) (swaps_subset allowed)
    .symmetric fixedMask (base (by omega)) (symmetricOrbit hdegree) (symmetricIndex hdegree)

theorem symmetricCertificate_valid {degree : ℕ} (hdegree : 5 ≤ degree) :
    Valid (decode (swaps degree (fun _ => true)) (symmetricCertificate hdegree)) := by
  have hne : base (by omega : 4 ≤ degree) ≠ second (by omega : 4 ≤ degree) := by
    simp [base, second, Fin.ext_iff]
  apply make_valid_symmetric
  · apply make_baseValid
    · rw [ambient_swaps]
      exact primitive_top degree
    · rw [fixedSet_eq_singleton (by omega)]
      exact Finset.singleton_nonempty _
    · rw [fixedSet_eq_singleton (by omega), Finset.card_singleton]
      omega
    · simp [fixedMask, base]
    · exact swaps_fix_zero
    · exact symmetricOrbit_reaches hdegree
  · rw [symmetricIndex_spec]
    refine ⟨isCycle_swap hne, ?_, ?_⟩
    · rw [card_support_swap hne]
      decide
    · rw [card_support_swap hne]
      omega
  · exact ⟨_, (swaps degree allowed).get_mem (symmetricIndex hdegree), by
      rw [symmetricIndex_spec, sign_swap hne]⟩

theorem symmetricCertificate_accepted {degree : ℕ} (hdegree : 5 ≤ degree) :
    (verifyRaw (swaps degree (fun _ => true))
      (writeCertificate (symmetricCertificate hdegree))).isSome = true :=
  (verifyRaw_encoded_iff _ _).mpr (symmetricCertificate_valid hdegree)

/-- A second point distinct from both the base point and the orbit target. -/
def auxiliary {degree : ℕ} (hdegree : 6 ≤ degree) (x : Fin degree) : Fin degree :=
  if x.val = 2 then third (by omega) else second (by omega)

theorem auxiliary_spec {degree : ℕ} (hdegree : 6 ≤ degree) (x : Fin degree) :
    allowed (auxiliary hdegree x) = true ∧
      base (by omega) ≠ auxiliary hdegree x ∧ x ≠ auxiliary hdegree x := by
  by_cases hx : x.val = 2
  · simp [auxiliary, hx, third, base, allowed, fixedMask, Fin.ext_iff]
  · simp [auxiliary, hx, second, base, allowed, fixedMask, Fin.ext_iff]

/-- An empty or one-letter three-cycle word taking the base to a complement point. -/
def alternatingOrbit {degree : ℕ} (hdegree : 6 ≤ degree)
    (i : Fin (complement (@fixedMask degree)).length) :
    Word (triples degree allowed).length :=
  let x := (complement (@fixedMask degree)).get i
  let b := base (by omega : 4 ≤ degree)
  let z := auxiliary hdegree x
  if hx : x = b then [] else
    [(indexOfMem (triples degree allowed) (swap b x * swap x z)
      ((mem_triples_iff _ _).mpr ⟨b, x, z,
        by simp [b, base, allowed, fixedMask],
        by simpa [x, allowed, fixedMask] using complement_ne_zero i,
        (auxiliary_spec hdegree x).1, Ne.symm hx,
        (auxiliary_spec hdegree x).2.1, (auxiliary_spec hdegree x).2.2, rfl⟩), false)]

theorem alternatingOrbit_reaches {degree : ℕ} (hdegree : 6 ≤ degree)
    (i : Fin (complement (@fixedMask degree)).length) :
    wordValue (triples degree allowed) (alternatingOrbit hdegree i) (base (by omega)) =
      (complement (@fixedMask degree)).get i := by
  dsimp only [alternatingOrbit]
  split
  · rename_i h
    simpa only [wordValue, List.map_nil, List.prod_nil, one_apply] using h.symm
  · rename_i h
    simp only [wordValue, letterValue, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Bool.false_eq_true, ite_false, mul_one]
    rw [indexOfMem_spec, mul_apply,
      swap_apply_of_ne_of_ne (Ne.symm h) (auxiliary_spec hdegree _).2.1,
      swap_apply_left]

/-- The index of the alternating family’s three-cycle prime-cycle witness. -/
def alternatingIndex {degree : ℕ} (hdegree : 6 ≤ degree) :
    Fin (triples degree allowed).length :=
  indexOfMem (triples degree allowed)
    (swap (base (by omega)) (second (by omega)) *
      swap (second (by omega)) (third (by omega)))
    ((mem_triples_iff _ _).mpr ⟨base (by omega), second (by omega), third (by omega),
      by simp [base, allowed, fixedMask],
      by simp [second, allowed, fixedMask],
      by simp [third, allowed, fixedMask],
      by simp [base, second, Fin.ext_iff],
      by simp [base, third, Fin.ext_iff],
      by simp [second, third, Fin.ext_iff], rfl⟩)

theorem alternatingIndex_spec {degree : ℕ} (hdegree : 6 ≤ degree) :
    (triples degree allowed).get (alternatingIndex hdegree) =
      swap (base (by omega)) (second (by omega)) *
        swap (second (by omega)) (third (by omega)) :=
  indexOfMem_spec _ _ _

/-- An explicit alternating normal-closure certificate for every degree at least six. -/
def alternatingCertificate {degree : ℕ} (hdegree : 6 ≤ degree) :
    RawCertificate degree (triples degree (fun _ => true)).length :=
  make (triples degree (fun _ => true)) (triples degree allowed) (triples_subset allowed)
    .alternating fixedMask (base (by omega)) (alternatingOrbit hdegree)
    (alternatingIndex hdegree)

theorem alternatingCertificate_valid {degree : ℕ} (hdegree : 6 ≤ degree) :
    Valid (decode (triples degree (fun _ => true)) (alternatingCertificate hdegree)) := by
  have hcycle : IsThreeCycle
      (swap (base (by omega : 4 ≤ degree)) (second (by omega : 4 ≤ degree)) *
        swap (second (by omega : 4 ≤ degree)) (third (by omega : 4 ≤ degree))) :=
    triple_isThreeCycle (by simp [base, second, Fin.ext_iff])
      (by simp [base, third, Fin.ext_iff]) (by simp [second, third, Fin.ext_iff])
  apply make_valid_alternating
  · apply make_baseValid
    · rw [ambient_triples]
      exact alternatingGroup.isPreprimitive_of_three_le_card (Fin degree)
        (by simpa only [Nat.card_fin] using (show 3 ≤ degree by omega))
    · rw [fixedSet_eq_singleton (by omega)]
      exact Finset.singleton_nonempty _
    · rw [fixedSet_eq_singleton (by omega), Finset.card_singleton]
      omega
    · simp [fixedMask, base]
    · exact triples_fix_zero
    · exact alternatingOrbit_reaches hdegree
  · rw [alternatingIndex_spec]
    refine ⟨hcycle.isCycle, ?_, ?_⟩
    · rw [hcycle.card_support]
      decide
    · rw [hcycle.card_support]
      omega
  · exact triples_even

theorem alternatingCertificate_accepted {degree : ℕ} (hdegree : 6 ≤ degree) :
    (verifyRaw (triples degree (fun _ => true))
      (writeCertificate (alternatingCertificate hdegree))).isSome = true :=
  (verifyRaw_encoded_iff _ _).mpr (alternatingCertificate_valid hdegree)


end TauCeti.SuccessfulFamilies
