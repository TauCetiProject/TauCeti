/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Stream.Init
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Word cylinders and coordinate flips in Cantor space

Cantor space `ℕ → Bool` and Baire space `ℕ → ℕ` have the cylinders `N_w`, the sets of sequences
beginning with a finite word `w`, as a basis of clopen sets. This file develops these cylinders
for sequences `ℕ → α` over an arbitrary alphabet, with words `List α` read left to right, and the
coordinate flips of Cantor space, which permute its cylinders.

A word `w` is prepended to a sequence `x` by `w.prependWord x`, and the cylinder
`w.wordCylinder` is the range of `w.prependWord`. A longer word gives a smaller cylinder. Over an
alphabet with at least two letters, one cylinder is contained in another exactly when the second
word is a prefix of the first; over a nonempty alphabet, two cylinders are disjoint exactly when
neither word is a prefix of the other. For a discrete alphabet
`w.prependWord` is an open embedding onto the clopen set `w.wordCylinder`.

Mathlib's cylinders `PiNat.cylinder x n` are indexed instead by a sequence `x` and a length `n`,
and its restrictions `PiNat.res x n` list the first `n` values newest-first. The two conventions
agree through `PiNat.wordCylinder_reverse_res`:
`(PiNat.res x n).reverse.wordCylinder = PiNat.cylinder x n`.

The flip `Homeomorph.flipAt i` of `ι → Bool` negates the `i`-th coordinate. At a position `n`
inside a word it exchanges the cylinders of the two words that differ only there; at a position
past the end of the word it preserves the cylinder. Flips are what move category information
between the two halves `N_{s ++ [false]}` and `N_{s ++ [true]}` of a cylinder `N_s`.

## Main definitions

* `List.prependWord w x`: the sequence beginning with the word `w` and continuing with `x`.
* `List.wordCylinder w`: the sequences beginning with `w`.
* `Homeomorph.flipAt i`: the homeomorphism of `ι → Bool` negating the `i`-th coordinate.

## Main results

* `List.mem_wordCylinder_iff`: `y ∈ w.wordCylinder` exactly when `y i = w[i]` for `i < w.length`.
* `List.wordCylinder_subset_wordCylinder_iff`, `List.disjoint_wordCylinder_iff`: inclusion and
  disjointness of cylinders in terms of the prefix order on words.
* `List.isOpenEmbedding_prependWord`, `List.isClopen_wordCylinder`.
* `PiNat.wordCylinder_reverse_res`: word cylinders agree with Mathlib's `PiNat.cylinder`.
* `Homeomorph.image_flipAt_wordCylinder_of_lt`,
  `Homeomorph.image_flipAt_wordCylinder_append_singleton` and
  `Homeomorph.image_flipAt_wordCylinder_of_length_le`: the action of flips on cylinders.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, for the basic open sets `N_s` of Cantor and Baire space.
-/

public section

open Set Function Topology

namespace List

variable {α : Type*}

/-- `w.prependWord x` is the sequence that begins with the word `w`, read left to right, and
continues with the sequence `x`. It is `Stream'.appendStream'` stated on the function type
`ℕ → α`, which carries the product topology, rather than on the type synonym `Stream' α`. -/
def prependWord (w : List α) (x : ℕ → α) : ℕ → α :=
  w ++ₛ x

/-- The cylinder of a word `w`: the sequences beginning with `w`, that is, the range of
`w.prependWord`. -/
def wordCylinder (w : List α) : Set (ℕ → α) :=
  Set.range w.prependWord

variable {v w : List α} {x y : ℕ → α} {n : ℕ}

@[simp]
theorem range_prependWord (w : List α) : Set.range w.prependWord = w.wordCylinder :=
  (rfl)

/-! ### Prepending a word -/

@[simp]
theorem prependWord_apply_of_lt (x : ℕ → α) (h : n < w.length) : w.prependWord x n = w[n] :=
  Stream'.get_append_left _ _ _ h

@[simp]
theorem prependWord_length_add (w : List α) (x : ℕ → α) (n : ℕ) :
    w.prependWord x (w.length + n) = x n :=
  Stream'.get_append_right _ _ _

theorem prependWord_apply_of_length_le (x : ℕ → α) (h : w.length ≤ n) :
    w.prependWord x n = x (n - w.length) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [prependWord_length_add, Nat.add_sub_cancel_left]

@[simp]
theorem prependWord_cons_succ (a : α) (w : List α) (x : ℕ → α) (n : ℕ) :
    (a :: w).prependWord x (n + 1) = w.prependWord x n :=
  Stream'.get_succ_cons n _ a

@[simp]
theorem prependWord_nil (x : ℕ → α) : ([] : List α).prependWord x = x :=
  Stream'.nil_append_stream x

/-- Prepending `v ++ w` is prepending `w` and then `v`. -/
@[simp]
theorem prependWord_append (v w : List α) (x : ℕ → α) :
    (v ++ w).prependWord x = v.prependWord (w.prependWord x) :=
  Stream'.append_append_stream v w x

/-- Dropping the first `w.length` terms of `w.prependWord x` recovers `x`. -/
theorem leftInverse_prependWord (w : List α) :
    LeftInverse (fun y : ℕ → α => fun n => y (w.length + n)) w.prependWord :=
  fun x => funext fun n => prependWord_length_add w x n

theorem prependWord_injective (w : List α) : Injective w.prependWord :=
  w.leftInverse_prependWord.injective

/-! ### Word cylinders -/

@[simp]
theorem prependWord_mem_wordCylinder (w : List α) (x : ℕ → α) : w.prependWord x ∈ w.wordCylinder :=
  mem_range_self x

/-- A sequence lies in the cylinder of `w` exactly when it begins with the letters of `w`. -/
theorem mem_wordCylinder_iff : y ∈ w.wordCylinder ↔ ∀ i (h : i < w.length), y i = w[i] := by
  refine ⟨?_, fun hy => ⟨fun n => y (w.length + n), funext fun n => ?_⟩⟩
  · rintro ⟨x, rfl⟩ i h
    exact prependWord_apply_of_lt x h
  · rcases Nat.lt_or_ge n w.length with h | h
    · rw [prependWord_apply_of_lt _ h, hy n h]
    · rw [prependWord_apply_of_length_le _ h, Nat.add_sub_cancel' h]

/-- The cylinder of `w` is Mathlib's cylinder of length `w.length` around any sequence beginning
with `w`. -/
theorem wordCylinder_eq_cylinder (w : List α) (x : ℕ → α) :
    w.wordCylinder = PiNat.cylinder (w.prependWord x) w.length := by
  ext y
  simp +contextual [mem_wordCylinder_iff, PiNat.mem_cylinder_iff]

@[simp]
theorem wordCylinder_nil : ([] : List α).wordCylinder = univ :=
  eq_univ_of_forall fun y => ⟨y, prependWord_nil y⟩

theorem wordCylinder_nonempty [Nonempty α] (w : List α) : w.wordCylinder.Nonempty :=
  range_nonempty _

/-- A sequence in the cylinders of two words, the first no longer than the second, shows that the
first word is a prefix of the second. -/
private theorem isPrefix_of_mem_wordCylinder (hv : y ∈ v.wordCylinder) (hw : y ∈ w.wordCylinder)
    (hvw : v.length ≤ w.length) : v <+: w := by
  rw [mem_wordCylinder_iff] at hv hw
  rw [prefix_iff_eq_take]
  refine ext_getElem (by simp [hvw]) fun i h _ => ?_
  rw [getElem_take, ← hv i h, hw i (Nat.lt_of_lt_of_le h hvw)]

/-- The cylinder of an extension of `w` lies in the cylinder of `w`. -/
theorem IsPrefix.wordCylinder_subset (h : w <+: v) : v.wordCylinder ⊆ w.wordCylinder := by
  intro y hy
  rw [mem_wordCylinder_iff] at hy ⊢
  intro i hi
  rw [hy i (Nat.lt_of_lt_of_le hi h.length_le), h.getElem hi]

/-- Over an alphabet with at least two letters, the cylinder of `v` lies in the cylinder of `w`
exactly when `w` is a prefix of `v`. -/
theorem wordCylinder_subset_wordCylinder_iff [Nontrivial α] :
    v.wordCylinder ⊆ w.wordCylinder ↔ w <+: v := by
  refine ⟨fun h => ?_, IsPrefix.wordCylinder_subset⟩
  have hlen : w.length ≤ v.length := by
    by_contra! hlt
    -- continue `v` by a letter different from the letter of `w` at position `v.length`
    obtain ⟨b, hb⟩ := exists_ne w[v.length]
    have := mem_wordCylinder_iff.1 (h (v.prependWord_mem_wordCylinder fun _ => b)) v.length hlt
    rw [prependWord_apply_of_length_le _ le_rfl] at this
    exact hb this
  obtain ⟨a⟩ : Nonempty α := inferInstance
  exact isPrefix_of_mem_wordCylinder (h (v.prependWord_mem_wordCylinder fun _ => a))
    (v.prependWord_mem_wordCylinder fun _ => a) hlen

/-- Over a nonempty alphabet, two cylinders are disjoint exactly when neither word is a prefix of
the other. -/
theorem disjoint_wordCylinder_iff [Nonempty α] :
    _root_.Disjoint v.wordCylinder w.wordCylinder ↔ ¬(v <+: w ∨ w <+: v) := by
  refine ⟨?_, fun h => Set.disjoint_left.2 fun y hv hw => h ?_⟩
  · rintro hd (h | h)
    · obtain ⟨y, hy⟩ := w.wordCylinder_nonempty
      exact Set.disjoint_left.1 hd (h.wordCylinder_subset hy) hy
    · obtain ⟨y, hy⟩ := v.wordCylinder_nonempty
      exact Set.disjoint_left.1 hd hy (h.wordCylinder_subset hy)
  rcases Nat.le_total v.length w.length with hvw | hwv
  · exact .inl (isPrefix_of_mem_wordCylinder hv hw hvw)
  · exact .inr (isPrefix_of_mem_wordCylinder hw hv hwv)

/-- The cylinders of the one-letter extensions of `w` cover the cylinder of `w`. -/
theorem iUnion_wordCylinder_append_singleton (w : List α) :
    ⋃ a, (w ++ [a]).wordCylinder = w.wordCylinder := by
  refine Subset.antisymm (iUnion_subset fun a => (w.prefix_append [a]).wordCylinder_subset)
    fun y hy => mem_iUnion.2 ⟨y w.length, mem_wordCylinder_iff.2 fun i hi => ?_⟩
  rw [mem_wordCylinder_iff] at hy
  rcases Nat.lt_or_ge i w.length with h | h
  · rw [getElem_append_left h, hy i h]
  · obtain rfl : i = w.length := by simp at hi; omega
    simp

/-- The cylinders of two different one-letter extensions of `w` are disjoint. -/
theorem disjoint_wordCylinder_append_singleton {a b : α} (hab : a ≠ b) (w : List α) :
    _root_.Disjoint (w ++ [a]).wordCylinder (w ++ [b]).wordCylinder :=
  Set.disjoint_left.2 fun y ha hb => hab <| by
    simpa using (mem_wordCylinder_iff.1 ha w.length (by simp)).symm.trans
      (mem_wordCylinder_iff.1 hb w.length (by simp))

/-! ### Topology -/

section Topology

variable [TopologicalSpace α]

@[fun_prop]
theorem continuous_prependWord (w : List α) : Continuous w.prependWord := by
  refine continuous_pi fun n => ?_
  rcases Nat.lt_or_ge n w.length with h | h
  · simp only [prependWord_apply_of_lt _ h]
    exact continuous_const
  · simp only [prependWord_apply_of_length_le _ h]
    exact continuous_apply _

theorem isEmbedding_prependWord (w : List α) : IsEmbedding w.prependWord :=
  w.leftInverse_prependWord.isEmbedding (by fun_prop) w.continuous_prependWord

/-- Over a discrete alphabet, word cylinders are open. -/
theorem isOpen_wordCylinder [DiscreteTopology α] (w : List α) : IsOpen w.wordCylinder := by
  obtain _ | ⟨a, -⟩ := w
  · simp
  · rw [wordCylinder_eq_cylinder _ fun _ => a]
    exact PiNat.isOpen_cylinder _ _ _

/-- Over a `T₁` alphabet, word cylinders are closed. -/
theorem isClosed_wordCylinder [T1Space α] (w : List α) : IsClosed w.wordCylinder := by
  obtain _ | ⟨a, -⟩ := w
  · simp
  · rw [wordCylinder_eq_cylinder _ fun _ => a, PiNat.cylinder_eq_pi]
    exact isClosed_set_pi fun _ _ => isClosed_singleton

/-- Over a discrete alphabet, word cylinders are clopen. -/
theorem isClopen_wordCylinder [DiscreteTopology α] (w : List α) : IsClopen w.wordCylinder :=
  ⟨w.isClosed_wordCylinder, w.isOpen_wordCylinder⟩

/-- Over a discrete alphabet, prepending a word is an open embedding, onto its cylinder. -/
theorem isOpenEmbedding_prependWord [DiscreteTopology α] (w : List α) :
    IsOpenEmbedding w.prependWord :=
  ⟨w.isEmbedding_prependWord, w.isOpen_wordCylinder⟩

end Topology

end List

/-! ### Mathlib's cylinders -/

namespace PiNat

variable {α : Type*}

/-- Reversing the restriction `res x n`, which lists the first `n` values of `x` newest-first,
lists them in order. -/
theorem reverse_res (x : ℕ → α) (n : ℕ) : (res x n).reverse = List.ofFn fun i : Fin n => x i := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.ofFn_succ', -List.ofFn_succ]

/-- **Word cylinders are Mathlib's cylinders.** The cylinder of the first `n` values of `x`,
listed in order, is `PiNat.cylinder x n`. -/
theorem wordCylinder_reverse_res (x : ℕ → α) (n : ℕ) :
    (res x n).reverse.wordCylinder = cylinder x n := by
  ext y
  simp [reverse_res, List.mem_wordCylinder_iff, mem_cylinder_iff]

end PiNat

/-! ### Coordinate flips -/

namespace Homeomorph

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate flip at `i`: the homeomorphism of `ι → Bool` that negates the `i`-th
coordinate and fixes the others. -/
def flipAt (i : ι) : (ι → Bool) ≃ₜ (ι → Bool) where
  toFun x := update x i (!x i)
  invFun x := update x i (!x i)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun :=
    continuous_id.update i (continuous_of_discreteTopology.comp (continuous_apply i))
  continuous_invFun :=
    continuous_id.update i (continuous_of_discreteTopology.comp (continuous_apply i))

theorem flipAt_apply (i : ι) (x : ι → Bool) : flipAt i x = update x i (!x i) :=
  (rfl)

@[simp]
theorem flipAt_apply_self (i : ι) (x : ι → Bool) : flipAt i x i = !x i := by
  simp [flipAt_apply]

@[simp]
theorem flipAt_apply_of_ne {i j : ι} (h : j ≠ i) (x : ι → Bool) : flipAt i x j = x j := by
  simp [flipAt_apply, h]

@[simp]
theorem flipAt_symm (i : ι) : (flipAt i).symm = flipAt i :=
  (rfl)

@[simp]
theorem flipAt_flipAt (i : ι) (x : ι → Bool) : flipAt i (flipAt i x) = x :=
  (flipAt i).symm_apply_apply x

variable {w : List Bool} {n : ℕ}

/-- Flipping a position inside the word `w` flips the corresponding letter of `w`. -/
theorem flipAt_prependWord_of_lt (h : n < w.length) (x : ℕ → Bool) :
    flipAt n (w.prependWord x) = (w.set n (!w[n])).prependWord x := by
  funext m
  rcases Nat.lt_or_ge m w.length with hm | hm
  · rcases eq_or_ne m n with rfl | hmn
    · simp [h]
    · simp [hm, hmn, Ne.symm hmn]
  · have hmn : m ≠ n := by omega
    rw [flipAt_apply_of_ne hmn, List.prependWord_apply_of_length_le _ hm,
      List.prependWord_apply_of_length_le _ (by simpa using hm), List.length_set]

/-- Flipping a position past the end of the word `w` flips the continuation. -/
theorem flipAt_length_add_prependWord (w : List Bool) (x : ℕ → Bool) (n : ℕ) :
    flipAt (w.length + n) (w.prependWord x) = w.prependWord (flipAt n x) := by
  funext m
  rcases Nat.lt_or_ge m w.length with hm | hm
  · rw [flipAt_apply_of_ne (by omega), List.prependWord_apply_of_lt _ hm,
      List.prependWord_apply_of_lt _ hm]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rcases eq_or_ne k n with rfl | hkn
    · simp
    · rw [flipAt_apply_of_ne (by omega), List.prependWord_length_add,
        List.prependWord_length_add, flipAt_apply_of_ne hkn]

/-- The flip at a position inside the word `w` maps the cylinder of `w` onto the cylinder of the
word obtained by flipping that letter. -/
theorem image_flipAt_wordCylinder_of_lt (h : n < w.length) :
    flipAt n '' w.wordCylinder = (w.set n (!w[n])).wordCylinder := by
  rw [← List.range_prependWord, ← List.range_prependWord, ← range_comp]
  exact congrArg range (funext (flipAt_prependWord_of_lt h))

/-- The flip at position `s.length` exchanges the cylinders of `s ++ [b]` and `s ++ [!b]`, the
two halves of the cylinder of `s`. -/
theorem image_flipAt_wordCylinder_append_singleton (s : List Bool) (b : Bool) :
    flipAt s.length '' (s ++ [b]).wordCylinder = (s ++ [!b]).wordCylinder := by
  rw [image_flipAt_wordCylinder_of_lt (by simp)]
  simp

/-- The flip at a position past the end of the word `w` maps the cylinder of `w` onto itself. -/
theorem image_flipAt_wordCylinder_of_length_le (h : w.length ≤ n) :
    flipAt n '' w.wordCylinder = w.wordCylinder := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← List.range_prependWord, ← range_comp]
  have : flipAt (w.length + k) ∘ w.prependWord = w.prependWord ∘ flipAt k :=
    funext (flipAt_length_add_prependWord w · k)
  rw [this, (flipAt k).surjective.range_comp]

end Homeomorph
