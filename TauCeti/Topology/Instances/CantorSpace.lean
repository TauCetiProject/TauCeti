/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Stream.Init
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Word cylinders and coordinate flips in Cantor space

A *word* is a finite list `w : List α`, read left to right. The point `prependWord w x` of
`ℕ → α` starts with the letters of `w` and continues with `x`, and the *word cylinder*
`wordCylinder w` is the set of points that start with `w`, the range of `prependWord w`.
These are the basic open sets of Cantor space `ℕ → Bool` and of Baire space `ℕ → ℕ` indexed by
the word they begin with. Constructions on Cantor space indexed by words, such as the graphs
`G_S` of Kechris, Solecki and Todorcevic, whose edges join `prependWord (s ++ [false]) x` and
`prependWord (s ++ [true]) x`, are phrased in this language.

Mathlib's cylinders `PiNat.cylinder x n` are indexed instead by a point and a length, and
`PiNat.res x n` lists the first `n` values of `x` newest first. The two conventions are related
by `PiNat.wordCylinder_reverse_res`, which says that `wordCylinder (res x n).reverse` is
`cylinder x n`. The point `prependWord w x` is Mathlib's `Stream'.appendStream' w x`, and its
basic API is derived from Mathlib's lemmas about `Stream'.appendStream'`. It is typed as a point
of `ℕ → α` because the type synonym `Stream' α` carries no topology or measurable structure, and
Mathlib's lemmas, phrased through `Stream'.get`, do not apply to evaluation `y n` by `simp` or
`rw`.

The coordinate flip `PiNat.flipAt n` negates the `n`-th coordinate of a point of Cantor space.
It is an involutive homeomorphism, and it maps the cylinder of a word `w` onto the cylinder of
the word obtained by negating the `n`-th letter of `w` (`PiNat.image_flipAt_wordCylinder`). In
particular it exchanges the two halves `wordCylinder (s ++ [false])` and
`wordCylinder (s ++ [true])` of `wordCylinder s` when `s` has length `n`: this is the symmetry
used in Miller's proof that the graphs `G_S` have no countable Baire-measurable coloring, and in
the proof that eventual equality `E₀` is generically ergodic.

## Main definitions

* `PiNat.prependWord w x`: the point that starts with the word `w` and continues with `x`.
* `PiNat.wordCylinder w`: the set of points that start with `w`.
* `PiNat.flipAt n`: the homeomorphism of `ℕ → Bool` negating the `n`-th coordinate.

## Main results

* `PiNat.mem_wordCylinder_iff`: a point lies in `wordCylinder w` iff it agrees with `w` on the
  first `w.length` coordinates.
* `PiNat.wordCylinder_subset_wordCylinder_iff`: over a nontrivial alphabet, inclusion of word
  cylinders is the reverse of the prefix order on words.
* `PiNat.disjoint_wordCylinder_iff`: two word cylinders are disjoint iff neither word is a prefix
  of the other.
* `PiNat.isOpenEmbedding_prependWord`: over a discrete alphabet, `prependWord w` is an open
  embedding onto the clopen set `wordCylinder w`.
* `PiNat.wordCylinder_reverse_res`: `wordCylinder (res x n).reverse = cylinder x n`.
* `PiNat.image_flipAt_wordCylinder`: `flipAt n` maps `wordCylinder w` onto the cylinder of `w`
  with its `n`-th letter negated.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer-Verlag, 1995, Section 2.D, for
  cylinders indexed by finite sequences in `ℕ → α`.
* B. D. Miller, "The graph-theoretic approach to descriptive set theory", *Bulletin of Symbolic
  Logic* 18 (2012), 554–575, for the graphs `G_S` and the coordinate flip.
-/

public section

open Set Function Topology

namespace PiNat

variable {α : Type*}

/-! ### Prepending a word -/

/-- `prependWord w x` is the point of `ℕ → α` that starts with the letters of the word `w`, read
left to right, and continues with the point `x`: Mathlib's `Stream'.appendStream' w x`, typed as a
point of `ℕ → α`. -/
def prependWord (w : List α) (x : ℕ → α) : ℕ → α :=
  w ++ₛ x

variable {w v : List α} {x y : ℕ → α} {n : ℕ}

/-- Below `w.length`, the coordinates of `prependWord w x` are the letters of `w`. -/
theorem prependWord_apply_of_lt (h : n < w.length) : prependWord w x n = w[n] :=
  Stream'.get_append_left n w x h

@[simp]
theorem prependWord_apply_length_add (w : List α) (x : ℕ → α) (n : ℕ) :
    prependWord w x (w.length + n) = x n :=
  Stream'.get_append_right n w x

/-- From `w.length` on, the coordinates of `prependWord w x` are those of `x`, shifted by
`w.length`. -/
theorem prependWord_apply_of_le (h : w.length ≤ n) : prependWord w x n = x (n - w.length) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp

@[simp]
theorem prependWord_apply_length (w : List α) (x : ℕ → α) : prependWord w x w.length = x 0 :=
  Stream'.get_append_length w x

@[simp]
theorem prependWord_nil (x : ℕ → α) : prependWord [] x = x :=
  Stream'.nil_append_stream x

/-- Prepending `v ++ w` is prepending `w` and then `v`. -/
@[simp]
theorem prependWord_append (v w : List α) (x : ℕ → α) :
    prependWord (v ++ w) x = prependWord v (prependWord w x) :=
  Stream'.append_append_stream v w x

/-- A point is recovered from its first `w.length` coordinates, here given by the word `w`, and
its remaining coordinates. -/
theorem prependWord_eq_self (hy : ∀ i (h : i < w.length), y i = w[i]) :
    prependWord w (fun n => y (w.length + n)) = y := by
  ext n
  rcases lt_or_ge n w.length with h | h
  · rw [prependWord_apply_of_lt h, hy n h]
  · rw [prependWord_apply_of_le h, Nat.add_sub_cancel' h]

/-- Prepending a fixed word is injective. -/
theorem prependWord_injective (w : List α) : Injective (prependWord w) :=
  Stream'.append_right_injective w

@[simp]
theorem prependWord_inj : prependWord w x = prependWord w y ↔ x = y :=
  (prependWord_injective w).eq_iff

/-- For any topology on the alphabet, prepending a word is continuous for the product topology on
`ℕ → α`. -/
@[fun_prop]
theorem continuous_prependWord [TopologicalSpace α] (w : List α) :
    Continuous (prependWord w) := by
  refine continuous_pi fun n => ?_
  rcases lt_or_ge n w.length with h | h
  · simpa only [prependWord_apply_of_lt h] using continuous_const
  · simpa only [prependWord_apply_of_le h] using continuous_apply _

/-- For any measurable structure on the alphabet, prepending a word is measurable for the product
σ-algebra on `ℕ → α`. -/
@[fun_prop]
theorem measurable_prependWord [MeasurableSpace α] (w : List α) :
    Measurable (prependWord w) := by
  refine Measurable.of_eval fun n => ?_
  rcases lt_or_ge n w.length with h | h
  · simpa only [prependWord_apply_of_lt h] using measurable_const
  · simpa only [prependWord_apply_of_le h] using measurable_pi_apply _

/-! ### Word cylinders -/

/-- The cylinder of the word `w`: the set of points of `ℕ → α` that start with the letters of `w`,
as the range of `prependWord w`. -/
def wordCylinder (w : List α) : Set (ℕ → α) :=
  range (prependWord w)

@[simp]
theorem range_prependWord (w : List α) : range (prependWord w) = wordCylinder w := (rfl)

@[simp]
theorem prependWord_mem_wordCylinder (w : List α) (x : ℕ → α) :
    prependWord w x ∈ wordCylinder w :=
  mem_range_self x

/-- A point lies in the cylinder of `w` iff its first `w.length` coordinates are the letters of
`w`, in order. -/
theorem mem_wordCylinder_iff : y ∈ wordCylinder w ↔ ∀ i (h : i < w.length), y i = w[i] := by
  refine ⟨?_, fun hy => ⟨_, prependWord_eq_self hy⟩⟩
  rintro ⟨x, rfl⟩ i hi
  exact prependWord_apply_of_lt hi

@[simp]
theorem wordCylinder_nil : wordCylinder ([] : List α) = univ := by
  simp [eq_univ_iff_forall, mem_wordCylinder_iff]

/-- Over a nonempty alphabet, every word cylinder is nonempty. -/
theorem wordCylinder_nonempty [Nonempty α] (w : List α) : (wordCylinder w).Nonempty :=
  ⟨_, prependWord_mem_wordCylinder w fun _ => Classical.arbitrary α⟩

/-- A longer word has a smaller cylinder. -/
theorem _root_.List.IsPrefix.wordCylinder_subset (h : v <+: w) :
    wordCylinder w ⊆ wordCylinder v := by
  obtain ⟨u, rfl⟩ := h
  rintro _ ⟨x, rfl⟩
  rw [prependWord_append]
  exact prependWord_mem_wordCylinder v _

/-- If `y` starts with both words `v` and `w`, then one of them is a prefix of the other. -/
theorem prefix_or_prefix_of_mem_wordCylinder (hv : y ∈ wordCylinder v)
    (hw : y ∈ wordCylinder w) : v <+: w ∨ w <+: v := by
  rw [mem_wordCylinder_iff] at hv hw
  wlog hvw : v.length ≤ w.length generalizing v w
  · exact (this hw hv (le_of_not_ge hvw)).symm
  refine .inl (List.prefix_iff_eq_take.2 (List.ext_getElem (by simpa using hvw) fun i hi _ => ?_))
  rw [List.getElem_take, ← hv i hi, ← hw i (by omega)]

/-- Over a nontrivial alphabet, inclusion of word cylinders is the reverse of the prefix order on
words. -/
theorem wordCylinder_subset_wordCylinder_iff [Nontrivial α] :
    wordCylinder w ⊆ wordCylinder v ↔ v <+: w := by
  refine ⟨fun h => ?_, List.IsPrefix.wordCylinder_subset⟩
  rcases le_or_gt v.length w.length with hvw | hwv
  · obtain ⟨x⟩ := (inferInstance : Nonempty α)
    refine (prefix_or_prefix_of_mem_wordCylinder (h (prependWord_mem_wordCylinder w fun _ => x))
      (prependWord_mem_wordCylinder w _)).elim id fun hwv' => ?_
    rw [hwv'.eq_of_length_le hvw]
  · obtain ⟨a, ha⟩ := exists_ne v[w.length]
    have := mem_wordCylinder_iff.1 (h (prependWord_mem_wordCylinder w fun _ => a)) w.length hwv
    simp [ha] at this

/-- Two word cylinders are disjoint iff neither word is a prefix of the other. -/
theorem disjoint_wordCylinder_iff [Nonempty α] :
    Disjoint (wordCylinder v) (wordCylinder w) ↔ ¬ (v <+: w ∨ w <+: v) := by
  refine ⟨fun hd h => ?_, fun h => disjoint_left.2 fun y hv hw =>
    h (prefix_or_prefix_of_mem_wordCylinder hv hw)⟩
  rcases h with h | h
  · exact (wordCylinder_nonempty w).ne_empty (hd.eq_bot_of_ge h.wordCylinder_subset)
  · exact (wordCylinder_nonempty v).ne_empty (hd.eq_bot_of_le h.wordCylinder_subset)

/-- The cylinder of `w` is the union of the cylinders of its one-letter extensions. -/
theorem iUnion_wordCylinder_append_singleton (w : List α) :
    ⋃ a, wordCylinder (w ++ [a]) = wordCylinder w := by
  refine Subset.antisymm (iUnion_subset fun a => (List.prefix_append w [a]).wordCylinder_subset)
    ?_
  rintro _ ⟨x, rfl⟩
  refine mem_iUnion.2 ⟨x 0, mem_wordCylinder_iff.2 fun i hi => ?_⟩
  rcases lt_or_ge i w.length with h | h
  · rw [prependWord_apply_of_lt h, List.getElem_append_left h]
  · obtain rfl : i = w.length := by simp at hi; omega
    simp

/-- The points that start with `w` are those of the Mathlib cylinder of length `w.length` around
any one of them. -/
theorem cylinder_eq_wordCylinder (hy : y ∈ wordCylinder w) : cylinder y w.length = wordCylinder w :=
  by
  ext z
  rw [mem_cylinder_iff, mem_wordCylinder_iff]
  rw [mem_wordCylinder_iff] at hy
  exact ⟨fun h i hi => (h i hi).trans (hy i hi), fun h i hi => (h i hi).trans (hy i hi).symm⟩

@[simp]
theorem cylinder_prependWord_length (w : List α) (x : ℕ → α) :
    cylinder (prependWord w x) w.length = wordCylinder w :=
  cylinder_eq_wordCylinder (prependWord_mem_wordCylinder w x)

/-- Mathlib's `res x n` lists the first `n` coordinates of `x` newest first, so its reverse is the
word of the first `n` coordinates of `x`, read left to right. -/
theorem reverse_res (x : ℕ → α) (n : ℕ) : (res x n).reverse = List.ofFn fun i : Fin n => x i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ']
    simp [res_succ, ih]

/-- The cylinder of the first `n` letters of `x`, read left to right, is Mathlib's cylinder of
length `n` around `x`. -/
@[simp]
theorem wordCylinder_reverse_res (x : ℕ → α) (n : ℕ) :
    wordCylinder (res x n).reverse = cylinder x n := by
  have hx : x ∈ wordCylinder (res x n).reverse :=
    mem_wordCylinder_iff.2 fun i hi => by simp [reverse_res]
  rw [← cylinder_eq_wordCylinder hx, List.length_reverse, res_length]

/-- The cylinder of `w` as the intersection of the coordinate conditions it imposes. -/
theorem wordCylinder_eq_iInter (w : List α) :
    wordCylinder w = ⋂ i, ⋂ (h : i < w.length), (fun y : ℕ → α => y i) ⁻¹' {w[i]} := by
  ext y
  simp [mem_wordCylinder_iff]

/-- Over a `T₁` alphabet, every word cylinder is closed in the product topology. -/
theorem isClosed_wordCylinder [TopologicalSpace α] [T1Space α] (w : List α) :
    IsClosed (wordCylinder w) := by
  rw [wordCylinder_eq_iInter]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (continuous_apply i)

/-- Over a discrete alphabet, every word cylinder is open in the product topology. -/
theorem isOpen_wordCylinder [TopologicalSpace α] [DiscreteTopology α] (w : List α) :
    IsOpen (wordCylinder w) :=
  isOpen_iff_mem_nhds.2 fun y hy => by
    rw [← cylinder_eq_wordCylinder hy]
    exact (isOpen_cylinder _ y _).mem_nhds (self_mem_cylinder y _)

/-- Over a discrete alphabet, every word cylinder is clopen in the product topology. -/
theorem isClopen_wordCylinder [TopologicalSpace α] [DiscreteTopology α] (w : List α) :
    IsClopen (wordCylinder w) :=
  ⟨isClosed_wordCylinder w, isOpen_wordCylinder w⟩

/-- Over an alphabet whose singletons are measurable, every word cylinder is measurable for the
product σ-algebra. -/
@[measurability]
theorem measurableSet_wordCylinder [MeasurableSpace α] [MeasurableSingletonClass α]
    (w : List α) : MeasurableSet (wordCylinder w) := by
  rw [wordCylinder_eq_iInter]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_singleton _ |>.preimage (measurable_pi_apply i)

/-- `prependWord w` is a topological embedding: its inverse on `wordCylinder w` forgets the first
`w.length` coordinates. -/
theorem isEmbedding_prependWord [TopologicalSpace α] (w : List α) :
    IsEmbedding (prependWord w) :=
  IsEmbedding.of_leftInverse (f := fun y n => y (w.length + n))
    (fun x => funext fun n => prependWord_apply_length_add w x n)
    (continuous_pi fun _ => continuous_apply _) (continuous_prependWord w)

/-- Over a discrete alphabet, `prependWord w` is an open embedding onto the clopen set
`wordCylinder w`. -/
theorem isOpenEmbedding_prependWord [TopologicalSpace α] [DiscreteTopology α] (w : List α) :
    IsOpenEmbedding (prependWord w) :=
  ⟨isEmbedding_prependWord w, isOpen_wordCylinder w⟩

/-- Over a `T₁` alphabet, `prependWord w` is a closed embedding onto `wordCylinder w`. -/
theorem isClosedEmbedding_prependWord [TopologicalSpace α] [T1Space α] (w : List α) :
    IsClosedEmbedding (prependWord w) :=
  ⟨isEmbedding_prependWord w, isClosed_wordCylinder w⟩

/-! ### The coordinate flip of Cantor space -/

/-- The homeomorphism of Cantor space `ℕ → Bool` negating the `n`-th coordinate. -/
def flipAt (n : ℕ) : (ℕ → Bool) ≃ₜ (ℕ → Bool) where
  toFun x := update x n (!x n)
  invFun x := update x n (!x n)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_id.update n (continuous_of_discreteTopology.comp
    (continuous_apply n))
  continuous_invFun := continuous_id.update n (continuous_of_discreteTopology.comp
    (continuous_apply n))

theorem flipAt_apply (n : ℕ) (x : ℕ → Bool) : flipAt n x = update x n (!x n) := (rfl)

@[simp]
theorem flipAt_apply_self (n : ℕ) (x : ℕ → Bool) : flipAt n x n = !x n := by
  simp [flipAt_apply]

@[simp]
theorem flipAt_apply_of_ne {m n : ℕ} (h : m ≠ n) (x : ℕ → Bool) : flipAt n x m = x m := by
  simp [flipAt_apply, h]

@[simp]
theorem symm_flipAt (n : ℕ) : (flipAt n).symm = flipAt n := (rfl)

@[simp]
theorem flipAt_flipAt (n : ℕ) (x : ℕ → Bool) : flipAt n (flipAt n x) = x :=
  (flipAt n).symm_apply_apply x

/-- The coordinate flip is an involution. -/
theorem flipAt_involutive (n : ℕ) : Involutive (flipAt n) :=
  flipAt_flipAt n

/-- The coordinate flip at `n` pulls the cylinder of `w` back to the cylinder of `w` with its
`n`-th letter negated; when `w.length ≤ n` the cylinder is unchanged. -/
theorem preimage_flipAt_wordCylinder (n : ℕ) (w : List Bool) :
    flipAt n ⁻¹' wordCylinder w = wordCylinder (w.modify n not) := by
  ext y
  simp only [mem_preimage, mem_wordCylinder_iff, List.length_modify, List.getElem_modify]
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  rcases eq_or_ne n i with rfl | h
  · simp [Bool.not_eq_eq_eq_not]
  · simp [h, Ne.symm h]

/-- The coordinate flip at `n` maps the cylinder of `w` onto the cylinder of `w` with its `n`-th
letter negated; when `w.length ≤ n` the cylinder is unchanged. -/
theorem image_flipAt_wordCylinder (n : ℕ) (w : List Bool) :
    flipAt n '' wordCylinder w = wordCylinder (w.modify n not) := by
  rw [Homeomorph.image_eq_preimage_symm, symm_flipAt, preimage_flipAt_wordCylinder]

/-- The coordinate flip at `s.length` exchanges `prependWord (s ++ [b]) x` and
`prependWord (s ++ [!b]) x`. -/
theorem flipAt_prependWord_append_singleton (s : List Bool) (b : Bool) (x : ℕ → Bool) :
    flipAt s.length (prependWord (s ++ [b]) x) = prependWord (s ++ [!b]) x := by
  ext m
  rcases eq_or_ne m s.length with rfl | h
  · simp [prependWord_apply_of_lt]
  · rw [flipAt_apply_of_ne h, prependWord_append, prependWord_append]
    rcases lt_or_ge m s.length with hm | hm
    · simp [prependWord_apply_of_lt hm]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_add_one.2 (by omega)
      simp [prependWord_apply_of_le]

/-- The coordinate flip at `s.length` maps the cylinder of `s ++ [b]` onto the cylinder of
`s ++ [!b]`, exchanging the two halves of the cylinder of `s`. -/
theorem image_flipAt_wordCylinder_append_singleton (s : List Bool) (b : Bool) :
    flipAt s.length '' wordCylinder (s ++ [b]) = wordCylinder (s ++ [!b]) := by
  rw [← range_prependWord, ← range_comp]
  exact congrArg range (funext (flipAt_prependWord_append_singleton s b))

end PiNat
