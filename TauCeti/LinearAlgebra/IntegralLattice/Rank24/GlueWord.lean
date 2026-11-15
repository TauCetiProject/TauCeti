/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Representatives
public import Mathlib.Data.List.GetD
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
natural.  Replacing the components by an equal family reindexed along `σ` reindexes the digit
list along `σ` (`encodeGlueWord_piGlueAlphabetCongr_eq_ofFn`); in particular, reading the
positions of a list of components as an explicitly given family does not change digit lists
(`encodeGlueWord_piGlueAlphabetCongr`).

Sums, shortest norms, and canonical rational dual-lattice representatives of glue words can be
computed directly on their digit words: `glueWordAdd` adds two digit words label by label
(`encodeGlueWord_add`), `glueWordMinimum` sums the shortest norms of the printed labels, giving the
shortest norm `μ(w)` of the coset named by the word (`glueWordMinimum_encodeGlueWord`), and
`glueWordVector` evaluates `TauCeti.DynkinType.glueLabelVector` on each coordinate, giving the
shortest dual-lattice vector of any valid digit word (`glueWordVector_encodeGlueWord`,
`form_glueWordVector_self`). Finite checks on printed glue words therefore evaluate by `decide`.
Like digit lists, shortest norms are unchanged by passing to an equal family of components
(`TauCeti.DynkinType.sum_glueMinimum_piGlueAlphabetCongr`).

For a constant type-`A` family, `typeAGlueWordOfDigits` reads digits modulo the alphabet size.
`encodeGlueWord_typeA_eq` gives the encoder's residue formula, and
`decoded_typeA_eq_image_ofDigits` identifies a set of checked decoded words with the image of
this reader when the lists have the correct length and canonical digits.

Reference: Conway and Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16 §1.
-/

public section

namespace TauCeti

section

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

/-- The glue word with prescribed labels encodes to the list of those labels. -/
@[simp] theorem encodeGlueWord_glueLabelEquiv (d : ∀ i, Fin (t i).glueLabelCount) :
    encodeGlueWord t ht (fun i ↦ (t i).glueLabelEquiv (ht i) (d i)) =
      List.ofFn fun i ↦ (d i : ℕ) := by
  simp [encodeGlueWord]

/-- The zero glue word has every label zero. -/
@[simp] theorem encodeGlueWord_zero : encodeGlueWord t ht 0 = List.replicate n 0 := by
  simp [encodeGlueWord, List.ofFn_const]

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

/-- **Digits of a reindexed glue word**: if the components `s k` over `Fin m` are the components
`t (σ k)` for `σ : Fin m ≃ Fin n`, the image of a glue word `w` under
`TauCeti.DynkinType.piGlueAlphabetCongr` has in position `k` the digit of `w` in position
`σ k`. -/
theorem encodeGlueWord_piGlueAlphabetCongr_eq_ofFn {m : ℕ} {s : Fin m → DynkinType}
    (hs : ∀ k, (s k).IsSimplyLaced) (σ : Fin m ≃ Fin n) (h : ∀ k, t (σ k) = s k)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    encodeGlueWord s hs (DynkinType.piGlueAlphabetCongr t ht σ h w) =
      List.ofFn fun k ↦ (((t (σ k)).glueLabelEquiv (ht (σ k))).symm (w (σ k))).val := by
  rw [encodeGlueWord_def]
  exact congrArg List.ofFn (funext fun k ↦ by
    rw [DynkinType.piGlueAlphabetCongr_apply]
    exact DynkinType.val_glueLabelEquiv_symm_ofEq (h k) _ _ _)

/-- **Digits are unchanged by passing to an equal family of components**: if the components
`s k` over `Fin m` are the components `t k` over `Fin n` read along `m = n`, then a glue word and
its image under `TauCeti.DynkinType.piGlueAlphabetCongr` have the same digit list. -/
theorem encodeGlueWord_piGlueAlphabetCongr {m : ℕ} {s : Fin m → DynkinType}
    (hs : ∀ k, (s k).IsSimplyLaced) (hmn : m = n) (h : ∀ k, t (finCongr hmn k) = s k)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    encodeGlueWord s hs (DynkinType.piGlueAlphabetCongr t ht (finCongr hmn) h w) =
      encodeGlueWord t ht w := by
  subst hmn
  exact encodeGlueWord_piGlueAlphabetCongr_eq_ofFn t ht hs _ h w

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
  rw [decodeGlueWord_eq_some_iff, encodeGlueWord_glueLabelEquiv]

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

/-! ### Digit arithmetic of glue words -/

/-- The digit word of the sum of two glue words, computed label by label from their digit words
with `TauCeti.DynkinType.glueLabelAdd` (`encodeGlueWord_add`); a missing label reads as `0`. -/
@[expose] def glueWordAdd (l l' : List ℕ) : List ℕ :=
  List.ofFn fun i : Fin n ↦ (t i).glueLabelAdd (l.getD i 0) (l'.getD i 0)

/-- The shortest norm `μ(w)` of a glue word, computed from its digit word as the sum of the
shortest norms `TauCeti.DynkinType.glueLabelMinimum` of its labels
(`glueWordMinimum_encodeGlueWord`); a missing label reads as `0`. -/
@[expose] def glueWordMinimum (l : List ℕ) : ℚ :=
  ∑ i : Fin n, (t i).glueLabelMinimum (l.getD i 0)

/-- A label-wise sum lists the sums of the corresponding labels. -/
theorem glueWordAdd_def (l l' : List ℕ) :
    glueWordAdd t l l' =
      List.ofFn fun i : Fin n ↦ (t i).glueLabelAdd (l.getD i 0) (l'.getD i 0) :=
  (rfl)

/-- A label-wise sum has one label for each component. -/
@[simp] theorem length_glueWordAdd (l l' : List ℕ) : (glueWordAdd t l l').length = n := by
  simp [glueWordAdd]

/-- Each label of a label-wise sum is the sum of the corresponding labels. -/
@[simp] theorem getElem_glueWordAdd (l l' : List ℕ) (i : Fin n) :
    (glueWordAdd t l l')[i.val]'(by simp) = (t i).glueLabelAdd (l.getD i 0) (l'.getD i 0) := by
  simp [glueWordAdd]

/-- The shortest norm of a digit word is the sum of the shortest norms of its labels. -/
theorem glueWordMinimum_def (l : List ℕ) :
    glueWordMinimum t l = ∑ i : Fin n, (t i).glueLabelMinimum (l.getD i 0) :=
  (rfl)

private theorem getD_encodeGlueWord (w : ∀ i, (t i).glueAlphabet (ht i)) (i : Fin n) :
    (encodeGlueWord t ht w).getD i 0 = (((t i).glueLabelEquiv (ht i)).symm (w i)).val := by
  rw [List.getD_eq_getElem _ _ (by simp), getElem_encodeGlueWord]

/-- **The digit word of a sum of glue words is the label-wise sum of their digit words.** -/
@[simp]
theorem encodeGlueWord_add (w w' : ∀ i, (t i).glueAlphabet (ht i)) :
    encodeGlueWord t ht (w + w') =
      glueWordAdd t (encodeGlueWord t ht w) (encodeGlueWord t ht w') := by
  rw [encodeGlueWord_def, glueWordAdd]
  congr 1
  funext i
  rw [getD_encodeGlueWord, getD_encodeGlueWord, Pi.add_apply,
    DynkinType.val_glueLabelEquiv_symm_add]

/-- **The shortest norm of a glue word is read off its digit word**:
`glueWordMinimum` of the digits of `w` is `μ(w) = ∑ i, μ_(t i)(w_i)`. -/
@[simp]
theorem glueWordMinimum_encodeGlueWord (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordMinimum t (encodeGlueWord t ht w) = ∑ i, (t i).glueMinimum (ht i) (w i) := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [getD_encodeGlueWord, ← DynkinType.glueMinimum_glueLabelEquiv, Equiv.apply_symm_apply]

end

section GlueWordVector

open IntegralLattice

/-- **Computable dual-lattice vector of a digit glue word** `l : List ℕ` for an ordered family
`t : Fin n → DynkinType`, in componentwise Bourbaki simple-root coordinates
`∀ i, Fin (t i).rank → ℚ`.  When every component of `t` is valid and simply laced and
`IsValidGlueWord t l` holds, this is the canonical shortest representative of the discriminant
coset named by `l` (`mk_glueWordVector_of_decodeGlueWord_eq_some`, `form_glueWordVector_self`).
Missing entries default to digit `0` (hence `0`), while out-of-range digits follow
`TauCeti.DynkinType.glueLabelVector` (`0`, except on `Aₘ` where digit `d` gives a dual-carrier
representative of `d • ω₁`, shortest only for `d ≤ m + 1`). -/
def glueWordVector {n : ℕ} (t : Fin n → DynkinType) (l : List ℕ) :
    ∀ i, Fin (t i).rank → ℚ :=
  fun i ↦ (t i).glueLabelVector (l.getD i 0)

/-- `glueWordVector` applies `glueLabelVector` coordinatewise with default digit `0`. -/
theorem glueWordVector_def {n : ℕ} (t : Fin n → DynkinType) (l : List ℕ) :
    glueWordVector t l = fun i ↦ (t i).glueLabelVector (l.getD i 0) :=
  (rfl)

/-- Evaluating `glueWordVector` at component `i` gives `(t i).glueLabelVector (l.getD i 0)`. -/
@[simp]
theorem glueWordVector_apply {n : ℕ} (t : Fin n → DynkinType) (l : List ℕ) (i : Fin n) :
    glueWordVector t l i = (t i).glueLabelVector (l.getD i 0) :=
  (rfl)

/-- The empty digit list maps to the zero vector. -/
@[simp]
theorem glueWordVector_nil {n : ℕ} (t : Fin n → DynkinType) :
    glueWordVector t [] = 0 := by
  funext i
  rw [glueWordVector_apply, List.getD_nil, DynkinType.glueLabelVector_zero, Pi.zero_apply]

/-- An all-zero digit list of any length maps to the zero vector. -/
@[simp]
theorem glueWordVector_replicate_zero {n : ℕ} (t : Fin n → DynkinType) (m : ℕ) :
    glueWordVector t (List.replicate m 0) = 0 := by
  funext i
  simp [List.getD_eq_getElem?_getD]

/-- On `List.ofFn d`, the `i`-th component of `glueWordVector` is `(t i).glueLabelVector (d i)`. -/
@[simp]
theorem glueWordVector_ofFn {n : ℕ} (t : Fin n → DynkinType) (d : Fin n → ℕ) :
    glueWordVector t (List.ofFn d) = fun i ↦ (t i).glueLabelVector (d i) := by
  funext i
  rw [glueWordVector_apply, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **Compatibility with `encodeGlueWord`**: evaluating `glueWordVector` on the digit list of a
glue word `w` recovers `DynkinType.glueWordRepresentativeVector t ht w`. -/
@[simp]
theorem glueWordVector_encodeGlueWord {n : ℕ} (t : Fin n → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordVector t (encodeGlueWord t ht w) =
      DynkinType.glueWordRepresentativeVector t ht w := by
  funext i
  rw [glueWordVector_apply, List.getD_eq_getElem _ _ (by simp), getElem_encodeGlueWord,
    DynkinType.glueWordRepresentativeVector_apply, DynkinType.glueRepresentativeVector_def]

/-- If `l` decodes to `w`, then `glueWordVector t l` equals
`glueWordRepresentativeVector t ht w`. -/
theorem glueWordVector_eq_of_decodeGlueWord_eq_some {n : ℕ} (t : Fin n → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) {l : List ℕ} {w : ∀ i, (t i).glueAlphabet (ht i)}
    (hw : decodeGlueWord t ht l = some w) :
    glueWordVector t l = DynkinType.glueWordRepresentativeVector t ht w := by
  rw [(decodeGlueWord_eq_some_iff t ht l w).mp hw, glueWordVector_encodeGlueWord]

/-- Every `glueWordVector` lies in the dual carrier of the orthogonal sum of component root
lattices when all components are valid and simply laced. -/
theorem glueWordVector_mem_dualCarrier {n : ℕ} (t : Fin n → DynkinType)
    (hv : ∀ i, (t i).Valid) (ht : ∀ i, (t i).IsSimplyLaced) (l : List ℕ) :
    glueWordVector t l ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  (mem_dualCarrier_pi_iff _ _).mpr fun i ↦
    (t i).glueLabelVector_mem_dualCarrier (hv i) (ht i) (l.getD i 0)

/-- If `l` decodes to `w`, then `glueWordVector t l` represents the discriminant coset
`glueWordIsometry t ht hv w`. -/
theorem mk_glueWordVector_of_decodeGlueWord_eq_some {n : ℕ} (t : Fin n → DynkinType)
    (hv : ∀ i, (t i).Valid) (ht : ∀ i, (t i).IsSimplyLaced) {l : List ℕ}
    {w : ∀ i, (t i).glueAlphabet (ht i)} (hw : decodeGlueWord t ht l = some w) :
    (Submodule.Quotient.mk ⟨glueWordVector t l, glueWordVector_mem_dualCarrier t hv ht l⟩ :
        (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
      DynkinType.glueWordIsometry t ht hv w := by
  have heq : (⟨glueWordVector t l, glueWordVector_mem_dualCarrier t hv ht l⟩ :
        (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier) =
      DynkinType.glueWordRepresentative t ht hv w :=
    Subtype.ext ((glueWordVector_eq_of_decodeGlueWord_eq_some t ht hw).trans
      (DynkinType.coe_glueWordRepresentative t ht hv w).symm)
  rw [heq, DynkinType.mk_glueWordRepresentative]

/-- **Squared norm of `glueWordVector`**: for every valid digit word `l`, the squared norm of
`glueWordVector t l` equals `glueWordMinimum t l`, the shortest norm of the coset named by `l`. -/
theorem form_glueWordVector_self {n : ℕ} (t : Fin n → DynkinType)
    (hv : ∀ i, (t i).Valid) (ht : ∀ i, (t i).IsSimplyLaced) {l : List ℕ}
    (hl : IsValidGlueWord t l) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordVector t l) (glueWordVector t l) =
      glueWordMinimum t l := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((decodeGlueWord_isSome_iff t ht l).mpr hl)
  rw [glueWordVector_eq_of_decodeGlueWord_eq_some t ht hw,
    DynkinType.form_glueWordRepresentativeVector_self t ht hv w,
    (decodeGlueWord_eq_some_iff t ht l w).mp hw, glueWordMinimum_encodeGlueWord]

end GlueWordVector

/-! ### Constant type-`A` families -/

/-- Read a digit list as a word in `m` copies of the type-`Aₙ` glue alphabet, reducing its
entries modulo `n + 1` and using zero for any missing entries. Unlike `decodeGlueWord`, this
construction does not check the digit ranges or the length. -/
def typeAGlueWordOfDigits (n m : ℕ) (l : List ℕ) :
    Fin m → (DynkinType.A n).glueAlphabet (DynkinType.isSimplyLaced_A n) :=
  fun i ↦ ((l.getD i 0 : ℕ) : ZMod (n + 1))

/-- Each coordinate of a type-`A` digit word is the corresponding digit reduced modulo the
alphabet size. -/
@[simp] theorem typeAGlueWordOfDigits_apply (n m : ℕ) (l : List ℕ) (i : Fin m) :
    typeAGlueWordOfDigits n m l i = ((l.getD i 0 : ℕ) : ZMod (n + 1)) :=
  (rfl)

/-- Encoding a word in a constant type-`A` family lists its least nonnegative residues. -/
theorem encodeGlueWord_typeA_eq (n m : ℕ)
    (w : Fin m → (DynkinType.A n).glueAlphabet (DynkinType.isSimplyLaced_A n)) :
    encodeGlueWord (fun _ : Fin m ↦ DynkinType.A n)
      (fun _ ↦ DynkinType.isSimplyLaced_A n) w =
      List.ofFn fun i ↦ ZMod.val (n := n + 1) (w i) := by
  rw [encodeGlueWord_def (fun _ : Fin m ↦ DynkinType.A n)
    (fun _ ↦ DynkinType.isSimplyLaced_A n) w]
  congr 1
  funext i
  exact congrArg Fin.val (DynkinType.glueLabelEquiv_A_symm_apply n
    (DynkinType.isSimplyLaced_A n) (w i))

/-- Reading the encoded digits of a type-`A` word recovers the word. -/
@[simp] theorem typeAGlueWordOfDigits_encodeGlueWord (n m : ℕ)
    (w : Fin m → (DynkinType.A n).glueAlphabet (DynkinType.isSimplyLaced_A n)) :
    typeAGlueWordOfDigits n m (encodeGlueWord (fun _ : Fin m ↦ DynkinType.A n)
      (fun _ ↦ DynkinType.isSimplyLaced_A n) w) = w := by
  funext i
  rw [encodeGlueWord_typeA_eq n m w, typeAGlueWordOfDigits_apply,
    List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  exact ZMod.natCast_zmod_val (n := n + 1) (w i)

/-- On a set of correctly sized lists of canonical type-`A` digits, checked decoding gives
exactly the image of the digit-word construction. The hypothesis can be verified by finite
computation for an explicit table of glue generators. -/
theorem decoded_typeA_eq_image_ofDigits (n m : ℕ) (s : Set (List ℕ))
    (hs : ∀ l ∈ s,
      List.ofFn (fun i : Fin m ↦ (((l.getD i 0 : ℕ) : ZMod (n + 1))).val) = l) :
    {w | ∃ l ∈ s, decodeGlueWord (fun _ : Fin m ↦ DynkinType.A n)
        (fun _ ↦ DynkinType.isSimplyLaced_A n) l = some w} =
      typeAGlueWordOfDigits n m '' s := by
  ext w
  simp only [Set.mem_ofPred_eq, decodeGlueWord_eq_some_iff, Set.mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨_, hl, typeAGlueWordOfDigits_encodeGlueWord n m w⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, hl, ?_⟩
    rw [encodeGlueWord_typeA_eq n m (typeAGlueWordOfDigits n m l)]
    simpa only [typeAGlueWordOfDigits_apply] using (hs l hl).symm

end TauCeti
