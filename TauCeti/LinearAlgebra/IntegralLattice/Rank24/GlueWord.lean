/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Labels
import Mathlib.Data.List.OfFn

/-!
# Checked decoding of glue words

A glue word has one Conway--Sloane label per component of an ordered ADE family. The
function `decodeGlueWord` accepts a list of natural-number labels precisely when its
length and every label range are correct. It returns an element of the dependent product
of the existing component glue alphabets, so mixed cyclic and Klein four components use
their actual addition laws. Out-of-range labels are rejected rather than reduced modulo
the alphabet size.

The decidable predicate `IsValidGlueWord` records the length and label-range checks;
`decodeGlueWord_isSome_iff` characterizes acceptance using this predicate. The encoder and
decoder are inverse on accepted words. `decodeGlueWord_eq_some_iff`
characterizes successful decoding without unfolding either function, while
`decodeGlueWord_eq_none_iff` characterizes both ways a word can fail validation. An ordered
list of components is represented by its `List.get` family on `Fin length`.

Reference: Conway and Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16 §1.
-/

public section

namespace TauCeti

variable {n : ℕ} (t : Fin n → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)

/-- A glue word has one label per component, each within its component's alphabet. -/
def IsValidGlueWord (l : List ℕ) : Prop :=
  ∃ hlen : l.length = n, ∀ i : Fin n, l[i.val]'(by omega) < (t i).glueLabelCount

/-- Validity is exactly the length and coordinate-range condition. -/
theorem isValidGlueWord_iff (l : List ℕ) :
    IsValidGlueWord t l ↔
      ∃ hlen : l.length = n,
        ∀ i : Fin n, l[i.val]'(by omega) < (t i).glueLabelCount := (Iff.rfl)

/-- Glue-word validity is decidable by checking length and label ranges. -/
instance (l : List ℕ) : Decidable (IsValidGlueWord t l) :=
  decidable_of_iff _ (isValidGlueWord_iff t l).symm

/-- Encode a word in the component glue alphabets by its Conway--Sloane digit labels. -/
def encodeGlueWord (w : ∀ i, (t i).glueAlphabet (ht i)) : List ℕ :=
  List.ofFn fun i ↦ ((t i).glueLabelEquiv (ht i)).symm (w i) |>.val

/-- Decode a glue word, checking its length and the range of each label before mapping
it to the component's existing finite quadratic module. -/
def decodeGlueWord (l : List ℕ) : Option (∀ i, (t i).glueAlphabet (ht i)) :=
  if h : IsValidGlueWord t l then
    some fun i ↦ (t i).glueLabelEquiv (ht i)
      ⟨l[i.val]'(by have := ((isValidGlueWord_iff t l).mp h).choose; omega),
        ((isValidGlueWord_iff t l).mp h).choose_spec i⟩
  else none

/-- Encoding preserves the number of components. -/
@[simp] theorem length_encodeGlueWord (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (encodeGlueWord t ht w).length = n := by
  simp [encodeGlueWord]

/-- Each encoded coordinate is the corresponding component label. -/
@[simp] theorem getElem_encodeGlueWord (w : ∀ i, (t i).glueAlphabet (ht i)) (i : Fin n) :
    (encodeGlueWord t ht w)[i.val]'(by simp) =
      (((t i).glueLabelEquiv (ht i)).symm (w i)).val := by
  simp [encodeGlueWord]

/-- The labels of an encoded word satisfy the length and range checks. -/
@[simp] theorem isValidGlueWord_encodeGlueWord (w : ∀ i, (t i).glueAlphabet (ht i)) :
    IsValidGlueWord t (encodeGlueWord t ht w) := by
  refine (isValidGlueWord_iff t _).2 ⟨length_encodeGlueWord t ht w, ?_⟩
  intro i
  rw [getElem_encodeGlueWord]
  exact Fin.isLt _

/-- A valid word decodes to the component classes specified by its labels. -/
theorem decodeGlueWord_of_valid (l : List ℕ) (h : IsValidGlueWord t l) :
    decodeGlueWord t ht l =
      some fun i ↦ (t i).glueLabelEquiv (ht i)
        ⟨l[i.val]'(by have := ((isValidGlueWord_iff t l).mp h).choose; omega),
          ((isValidGlueWord_iff t l).mp h).choose_spec i⟩ := by
  simp only [decodeGlueWord, dite_eq_left h]

/-- Decoding the labels of a word recovers that word. -/
@[simp] theorem decodeGlueWord_encodeGlueWord (w : ∀ i, (t i).glueAlphabet (ht i)) :
    decodeGlueWord t ht (encodeGlueWord t ht w) = some w := by
  rw [decodeGlueWord_of_valid t ht _ (isValidGlueWord_encodeGlueWord t ht w)]
  simp only [Option.some.injEq]
  funext i
  simp only [getElem_encodeGlueWord, Fin.eta, Equiv.apply_symm_apply]

/-- Digit lists distinguish words in the component glue alphabets. -/
theorem encodeGlueWord_injective : Function.Injective (encodeGlueWord t ht) := by
  intro w v h
  have h := congrArg (decodeGlueWord t ht) h
  simpa only [decodeGlueWord_encodeGlueWord, Option.some.injEq] using h

/-- Successful decoding determines exactly the digit list of the resulting word. -/
@[simp] theorem decodeGlueWord_eq_some_iff (l : List ℕ)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    decodeGlueWord t ht l = some w ↔ l = encodeGlueWord t ht w := by
  constructor
  · intro h
    unfold decodeGlueWord at h
    split_ifs at h with hvalid
    · have hlen := ((isValidGlueWord_iff t l).mp hvalid).choose
      have hw := Option.some.inj h
      subst w
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi hj
        simp [encodeGlueWord]
  · rintro rfl
    exact decodeGlueWord_encodeGlueWord t ht w

/-- Decoding succeeds exactly for valid glue words. -/
@[simp] theorem decodeGlueWord_isSome_iff (l : List ℕ) :
    (decodeGlueWord t ht l).isSome ↔ IsValidGlueWord t l := by
  simp only [decodeGlueWord]
  split_ifs <;> simp_all

/-- A glue word is rejected exactly when it is invalid. -/
@[simp] theorem decodeGlueWord_eq_none_iff (l : List ℕ) :
    decodeGlueWord t ht l = none ↔ ¬ IsValidGlueWord t l := by
  simp only [decodeGlueWord]
  split_ifs <;> simp_all

end TauCeti
