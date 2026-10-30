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

For a word given by its labels `List.ofFn d`, validity is the range condition on each label
(`isValidGlueWord_ofFn_iff`), and decoding is natural under permutations of the components
(`decodeGlueWord_ofFn_comp`): permuting the labels and the components together reindexes the
decoded word through `Equiv.piCongrLeft`, the reindexing along which the glue-word isometry is
natural.

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
instance (l : List ℕ) : Decidable (IsValidGlueWord t l) := by
  rw [isValidGlueWord_iff]
  infer_instance

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

/-- An encoded word lists the labels of its coordinates. -/
theorem encodeGlueWord_def (w : ∀ i, (t i).glueAlphabet (ht i)) :
    encodeGlueWord t ht w =
      List.ofFn fun i ↦ (((t i).glueLabelEquiv (ht i)).symm (w i)).val :=
  (rfl)

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

/-! ### Words given by their labels, and permutations of the components -/

/-- A word given by its labels is valid exactly when each label lies in the alphabet of its
component. -/
@[simp] theorem isValidGlueWord_ofFn_iff (d : Fin n → ℕ) :
    IsValidGlueWord t (List.ofFn d) ↔ ∀ i, d i < (t i).glueLabelCount := by
  simp [isValidGlueWord_iff]

/-- A word given by in-range labels decodes to the classes of those labels. -/
theorem decodeGlueWord_ofFn (d : Fin n → ℕ) (hd : ∀ i, d i < (t i).glueLabelCount) :
    decodeGlueWord t ht (List.ofFn d) =
      some fun i ↦ (t i).glueLabelEquiv (ht i) ⟨d i, hd i⟩ := by
  rw [decodeGlueWord_eq_some_iff]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have h := getElem_encodeGlueWord t ht (fun i ↦ (t i).glueLabelEquiv (ht i) ⟨d i, hd i⟩)
      ⟨i, by simpa using hi⟩
    simp only [Equiv.symm_apply_apply] at h
    simpa using h.symm

/-- **Decoding is natural under permutations of the components.** Reindexing the labels of a
word along `σ : Fin m ≃ Fin n` and decoding against the reindexed components `k ↦ t (σ k)`
reindexes the decoded word; in particular the reindexed word is valid exactly when the original
one is. -/
theorem decodeGlueWord_ofFn_comp {m : ℕ} (σ : Fin m ≃ Fin n) (d : Fin n → ℕ) :
    decodeGlueWord (fun k ↦ t (σ k)) (fun k ↦ ht (σ k)) (List.ofFn (d ∘ σ)) =
      (decodeGlueWord t ht (List.ofFn d)).map
        (Equiv.piCongrLeft (fun i ↦ (t i).glueAlphabet (ht i)) σ).symm := by
  by_cases hd : ∀ i, d i < (t i).glueLabelCount
  · rw [decodeGlueWord_ofFn (fun k ↦ t (σ k)) (fun k ↦ ht (σ k)) (d ∘ σ) fun k ↦ hd (σ k),
      decodeGlueWord_ofFn t ht d hd, Option.map_some]
    simp only [Option.some.injEq]
    funext k
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  · have hdσ : ¬ ∀ k, (d ∘ σ) k < (t (σ k)).glueLabelCount := fun h ↦
      hd (σ.forall_congr_right.mp h)
    rw [(decodeGlueWord_eq_none_iff _ _ _).mpr (by simpa using hdσ),
      (decodeGlueWord_eq_none_iff _ _ _).mpr (by simpa using hd), Option.map_none]

end TauCeti
