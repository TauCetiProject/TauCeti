/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Encoding.Basic

/-!
# Constructing certificates from explicitly listed permutations

All indices are found by finite list scans. The proof of membership is erased
at execution; no choice of a permutation or a group element is performed.
-/

open Equiv
open TauCeti.FinitePermutation TauCeti.CertifiedPermutation TauCeti.CertificateWire

@[expose] public section

namespace TauCeti.CertificateConstruction

variable {G H : Type*} [Group G] [Group H]

/-- Transport generator indices of a signed word along an equality of list lengths. -/
def castWord {a b : ℕ} (h : a = b) (word : Word a) : Word b :=
  word.map fun letter => (Fin.cast h letter.1, letter.2)

theorem castWord_trans {a b c : ℕ} (hab : a = b) (hbc : b = c) (word : Word a) :
    castWord hbc (castWord hab word) = castWord (hab.trans hbc) word := by
  subst b
  subst c
  simp [castWord]

theorem wordValue_congr (gs hs : List G) (h : gs = hs) (word : Word gs.length) :
    wordValue gs word = wordValue hs (castWord (congrArg List.length h) word) := by
  subst hs
  simp [castWord]

theorem wordValue_map (f : G →* H) (gs : List G) (word : Word gs.length) :
    wordValue (gs.map f) (castWord (List.length_map ..).symm word) =
      f (wordValue gs word) := by
  induction word with
  | nil => simp [wordValue, castWord]
  | cons letter word ih =>
      rcases letter with ⟨i, inverted⟩
      cases inverted <;>
        simpa [wordValue, castWord, letterValue] using
          congrArg (fun value => f (gs.get i) * value) ih

variable {degree : ℕ}

/-- Find the first index of a permutation in a list containing it. -/
def indexOfMem (gs : List (Perm (Fin degree))) (g : Perm (Fin degree)) (hg : g ∈ gs) :
    Fin gs.length :=
  Fin.find (fun i => gs.get i = g) (List.mem_iff_get.mp hg)

theorem indexOfMem_spec (gs : List (Perm (Fin degree))) (g : Perm (Fin degree)) (hg : g ∈ gs) :
    gs.get (indexOfMem gs g hg) = g :=
  Fin.find_spec (p := fun i => gs.get i = g) _

/-- Represent listed subgroup generators as one-letter ambient-generator words. -/
def wordsFor (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs) :
    List (Word gs.length) :=
  List.ofFn fun i : Fin hs.length => [(indexOfMem gs (hs.get i) (hmem _ (hs.get_mem i)), false)]

@[simp]
theorem wordsFor_length (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs) :
    (wordsFor gs hs hmem).length = hs.length :=
  List.length_ofFn

theorem wordsFor_values (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs) :
    (wordsFor gs hs hmem).map (wordValue gs) = hs := by
  rw [wordsFor, List.map_ofFn]
  calc
    _ = List.ofFn hs.get := by
      congr 1
      funext i
      simpa [wordValue, letterValue] using
        indexOfMem_spec gs (hs.get i) (hmem _ (hs.get_mem i))
    _ = hs := List.ofFn_get hs

/-- A claim-dependent factor list using one indicated subgroup generator. -/
def oneFactor {ambientSize subgroupSize : ℕ} (claim : Claim)
    (index : Fin subgroupSize) : FactorsFor claim ambientSize subgroupSize :=
  match claim with
  | .doublyTransitive => ()
  | .alternating => [⟨[], index, false⟩]
  | .symmetric => [⟨[], index, false⟩]

/-- Build a raw certificate from listed subgroup generators and orbit words. -/
def make (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs)
    (claim : Claim) (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (cycleIndex : Fin hs.length) :
    RawCertificate degree gs.length where
  claim := claim
  generatorWords := wordsFor gs hs hmem
  mask := mask
  base := base
  orbitWords i := castWord (wordsFor_length gs hs hmem).symm (orbitWords i)
  cycleFactors := oneFactor claim (Fin.cast (wordsFor_length gs hs hmem).symm cycleIndex)

theorem make_generators (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs)
    (claim : Claim) (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (cycleIndex : Fin hs.length) :
    ((decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)).generators.map
      (FiniteAction.ambientGroup gs).subtype) = hs := by
  simpa [decode, decodedGenerators, make, List.map_map, Function.comp_def, wordToAmbient]
    using wordsFor_values gs hs hmem

theorem make_orbit_value (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs)
    (claim : Claim) (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (cycleIndex : Fin hs.length)
    (x : Fin degree) (hx : mask x = false) :
    let c := decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)
    (signedWordEval c.generators (c.orbitWords x) : Perm (Fin degree)) =
      wordValue hs (orbitWords (complementIndex mask x hx)) := by
  dsimp only
  have h := wordValue_map (FiniteAction.ambientGroup gs).subtype
    (decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)).generators
    ((decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)).orbitWords x)
  have hc := wordValue_congr _ _
    (make_generators gs hs hmem claim mask base orbitWords cycleIndex)
    (castWord (List.length_map ..).symm
      ((decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)).orbitWords x))
  rw [h] at hc
  have hw :
      castWord
        (congrArg List.length
          (make_generators gs hs hmem claim mask base orbitWords cycleIndex))
        (castWord (List.length_map ..).symm
          ((decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)).orbitWords x)) =
      orbitWords (complementIndex mask x hx) := by
    simp only [decode, make, hx, dite_eq_left, castWord, List.map_map, Function.comp_def]
    apply List.map_id''
    intro letter
    exact Prod.ext (Fin.ext rfl) rfl
  rw [hw] at hc
  exact hc

theorem make_cycle_value (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs)
    (claim : Claim) (hclaim : claim ≠ .doublyTransitive)
    (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (cycleIndex : Fin hs.length) :
    cycleValue (decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)) =
      hs.get cycleIndex := by
  have hg := congrArg (fun l => l[cycleIndex.val]?)
    (make_generators gs hs hmem claim mask base orbitWords cycleIndex)
  have hget :
      ((decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)).generators.get
        (Fin.cast ((List.length_map ..).trans (wordsFor_length gs hs hmem)).symm cycleIndex) :
          Perm (Fin degree)) = hs.get cycleIndex := by
    apply Option.some.inj
    simpa [decode, make, decodedGenerators, List.get_eq_getElem, wordsFor_length] using hg
  cases claim with
  | doublyTransitive => exact (hclaim rfl).elim
  | alternating =>
      simpa [cycleValue, conjugateProduct, factorEval, decode, decodedGenerators, make,
        oneFactor, factorList, wordToAmbient, wordValue, castWord] using hget
  | symmetric =>
      simpa [cycleValue, conjugateProduct, factorEval, decode, decodedGenerators, make,
        oneFactor, factorList, wordToAmbient, wordValue, castWord] using hget

theorem make_baseValid (gs hs : List (Perm (Fin degree))) (hmem : ∀ h ∈ hs, h ∈ gs)
    (claim : Claim) (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (cycleIndex : Fin hs.length)
    (hprimitive : MulAction.IsPreprimitive (FiniteAction.ambientGroup gs) (Fin degree))
    (hnonempty : (Finset.univ.filter fun x => mask x).Nonempty)
    (hcard : (Finset.univ.filter fun x => mask x).card + 1 < degree)
    (hbase : mask base = false)
    (hfix : ∀ h ∈ hs, ∀ x, mask x = true → h x = x)
    (hreach : ∀ i, wordValue hs (orbitWords i) base = (complement mask).get i) :
    BaseValid (decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)) := by
  have hfixed :
      (decode gs (make gs hs hmem claim mask base orbitWords cycleIndex)).fixedSet =
        Finset.univ.filter (fun x => mask x) := rfl
  refine ⟨hprimitive, hnonempty, ?_, ?_, ?_, ?_⟩
  · rw [hfixed]
    simpa only [Nat.card_fin] using hcard
  · rw [hfixed]
    change base ∉ Finset.univ.filter (fun x => mask x)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbase,
      Bool.false_eq_true, not_false_eq_true]
  · intro h hh x hx
    have hh' : (h : Perm (Fin degree)) ∈ hs := by
      rw [← make_generators gs hs hmem claim mask base orbitWords cycleIndex]
      exact List.mem_map.mpr ⟨h, hh, rfl⟩
    rw [hfixed] at hx
    exact hfix _ hh' x (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx)
  · intro x hx
    rw [hfixed] at hx
    have hx' : mask x = false := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] using hx
    rw [make_orbit_value gs hs hmem claim mask base orbitWords cycleIndex x hx']
    exact (hreach _).trans (complementIndex_spec mask x hx')

theorem make_valid_alternating (gs hs : List (Perm (Fin degree)))
    (hmem : ∀ h ∈ hs, h ∈ gs) (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (cycleIndex : Fin hs.length)
    (hbase : BaseValid (decode gs (make gs hs hmem .alternating mask base orbitWords cycleIndex)))
    (hcycle : (hs.get cycleIndex).IsCycle ∧ (hs.get cycleIndex).support.card.Prime ∧
      (hs.get cycleIndex).support.card + 3 ≤ degree) (heven : ∀ h ∈ hs, h.sign = 1) :
    Valid (decode gs (make gs hs hmem .alternating mask base orbitWords cycleIndex)) := by
  refine ⟨hbase, ?_⟩
  change CycleValid (decode gs (make gs hs hmem .alternating mask base orbitWords
    cycleIndex)) ∧ _
  refine ⟨?_, ?_⟩
  · simpa [CycleValid, make_cycle_value gs hs hmem .alternating (by decide)] using hcycle
  · intro h hh
    apply heven
    rw [← make_generators gs hs hmem .alternating mask base orbitWords cycleIndex]
    exact List.mem_map.mpr ⟨h, hh, rfl⟩

theorem make_valid_symmetric (gs hs : List (Perm (Fin degree)))
    (hmem : ∀ h ∈ hs, h ∈ gs) (mask : Fin degree → Bool) (base : Fin degree)
    (orbitWords : Fin (complement mask).length → Word hs.length) (cycleIndex : Fin hs.length)
    (hbase : BaseValid (decode gs (make gs hs hmem .symmetric mask base orbitWords cycleIndex)))
    (hcycle : (hs.get cycleIndex).IsCycle ∧ (hs.get cycleIndex).support.card.Prime ∧
      (hs.get cycleIndex).support.card + 3 ≤ degree) (hodd : ∃ h ∈ hs, h.sign = -1) :
    Valid (decode gs (make gs hs hmem .symmetric mask base orbitWords cycleIndex)) := by
  refine ⟨hbase, ?_⟩
  change CycleValid (decode gs (make gs hs hmem .symmetric mask base orbitWords
    cycleIndex)) ∧ _
  refine ⟨?_, ?_⟩
  · simpa [CycleValid, make_cycle_value gs hs hmem .symmetric (by decide)] using hcycle
  · obtain ⟨h, hh, hodd⟩ := hodd
    rw [← make_generators gs hs hmem .symmetric mask base orbitWords cycleIndex] at hh
    obtain ⟨g, hg, hgh⟩ := List.mem_map.mp hh
    refine ⟨g, hg, ?_⟩
    change Equiv.Perm.sign ((FiniteAction.ambientGroup gs).subtype g) = -1
    rw [hgh]
    exact hodd


end TauCeti.CertificateConstruction
