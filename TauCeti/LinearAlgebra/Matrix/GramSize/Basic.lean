/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Sizes of numbers, vectors and matrices

Let `A` be a commutative ring with an involution `star`, and let `J` be the Gram matrix, indexed
by a finite type `ι` with `r = #ι` elements, of a sesquilinear form `⟨v, w⟩ = star v ⬝ᵥ J *ᵥ w`
on `ι → A`. A **size** for `J` (`TauCeti.GramSize J`) is a family of subsets `A_(i) ⊆ A`,
`i : ℕ`, the *numbers of size `i`*, such that

* `A_(i) * A_(j) ⊆ A_(i + j)`;
* a sum of at most `r + 1` numbers of size `i` has size `i + 1`;
* `A_(i)` is stable under negation and under `star`;
* `0` and `1` have every size;
* the entries of `J` and of `J⁻¹` have size `1`.

A vector or a matrix has size `i` when all of its entries have (`TauCeti.GramSize.vecsOfSize`,
`TauCeti.GramSize.matsOfSize`). The axioms make sizes behave like logarithms of absolute values
on one scale: the sizes increase with `i` (`TauCeti.GramSize.ofSize_mono`, from `x = x * 1`), and
the product of a matrix of size `i` whose columns are indexed by `ι` and a vector or matrix of
size `j` whose rows are indexed by `ι` has size `i + j + 1`
(`TauCeti.GramSize.mulVec_mem_vecsOfSize`, `TauCeti.GramSize.mul_mem_matsOfSize`). In particular
the value `⟨u, v⟩` of the form at vectors of sizes `i` and `j` has size `i + j + 3`
(`TauCeti.GramSize.star_dotProduct_mulVec_mem`).

Sizes measure numbers at one place, uniformly at a real place and at finitely many finite places
read together. The two basic examples are:

* at a real place, `A_(i) = {x : ‖x‖ ≤ L ^ i}` for a normed ring `A` and a scale `L ≥ r + 1`
  bounding the entries of `J` and `J⁻¹` (`TauCeti.GramSize.ofNorm`);
* at finite places, `A_(i) = {x : α ^ i * x ∈ O}` for a `star`-stable subring `O` of `A` and a
  self-adjoint element `α ∈ O` such that `α • J` and `α • J⁻¹` have entries in `O`
  (`TauCeti.GramSize.ofSubring`).

Sizes are the yardstick for the lengths of vectors at points of the unitary group of `J`, in
`TauCeti.LinearAlgebra.Matrix.GramSize.Lengths`; they are used to compare the local orbital
integrals of Bessel functions at two points of a unitary group in the analysis of second moments
of Poincaré series.

## Main definitions

* `TauCeti.GramSize J`: a size for the Gram matrix `J`.
* `TauCeti.GramSize.vecsOfSize`, `TauCeti.GramSize.matsOfSize`: vectors and matrices of size `i`.
* `TauCeti.GramSize.ofNorm`, `TauCeti.GramSize.ofSubring`: the sizes at a real place and at
  finite places.

## Main results

* `TauCeti.GramSize.mulVec_mem_vecsOfSize`, `TauCeti.GramSize.mul_mem_matsOfSize`: products of
  matrices and vectors of sizes `i` and `j` have size `i + j + 1`.
* `TauCeti.GramSize.star_dotProduct_mulVec_mem`: the form has size `i + j + 3` on vectors of sizes
  `i` and `j`.

## Provenance

The notion of a size and its matrix rules follow the Lean project grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Spanning/Frames/Lengths.lean`, declarations `New.Floors.Size`,
`New.Floors.Size.vecsOfSize`, `New.Floors.Size.HasMatrixSize` and its lemmas `mono`, `mulVec` and
`mul`. Here the matrices need not be square and the size is attached to the Gram matrix alone.
-/

public section

open Matrix

namespace TauCeti

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [StarRing A]

/-- A **size** for the Gram matrix `J` of a sesquilinear form on `ι → A`: a family of subsets
`ofSize i ⊆ A`, the numbers of size `i`, closed under products (adding the sizes), under sums of
at most `#ι + 1` terms (raising the size by one), under negation and `star`, containing `0` and
`1` in every size, and containing the entries of `J` and `J⁻¹` in size `1`. -/
@[ext]
structure GramSize (J : Matrix ι ι A) where
  /-- The numbers of size `i`. -/
  ofSize : ℕ → Set A
  mul_mem' {i j : ℕ} {x y : A} : x ∈ ofSize i → y ∈ ofSize j → x * y ∈ ofSize (i + j)
  multiset_sum_mem' {i : ℕ} (s : Multiset A) : Multiset.card s ≤ Fintype.card ι + 1 →
    (∀ x ∈ s, x ∈ ofSize i) → s.sum ∈ ofSize (i + 1)
  neg_mem_iff' {i : ℕ} {x : A} : -x ∈ ofSize i ↔ x ∈ ofSize i
  star_mem_iff' {i : ℕ} {x : A} : star x ∈ ofSize i ↔ x ∈ ofSize i
  zero_mem' (i : ℕ) : (0 : A) ∈ ofSize i
  one_mem' (i : ℕ) : (1 : A) ∈ ofSize i
  gram_mem' (a b : ι) : J a b ∈ ofSize 1
  gram_inv_mem' (a b : ι) : J⁻¹ a b ∈ ofSize 1

namespace GramSize

variable {J : Matrix ι ι A} (S : GramSize J) {i j : ℕ} {x y : A}

theorem mul_mem (hx : x ∈ S.ofSize i) (hy : y ∈ S.ofSize j) : x * y ∈ S.ofSize (i + j) :=
  S.mul_mem' hx hy

theorem multiset_sum_mem (s : Multiset A) (hs : Multiset.card s ≤ Fintype.card ι + 1)
    (h : ∀ x ∈ s, x ∈ S.ofSize i) : s.sum ∈ S.ofSize (i + 1) :=
  S.multiset_sum_mem' s hs h

@[simp]
theorem neg_mem_iff : -x ∈ S.ofSize i ↔ x ∈ S.ofSize i :=
  S.neg_mem_iff'

@[simp]
theorem star_mem_iff : star x ∈ S.ofSize i ↔ x ∈ S.ofSize i :=
  S.star_mem_iff'

@[simp]
theorem zero_mem (i : ℕ) : (0 : A) ∈ S.ofSize i :=
  S.zero_mem' i

@[simp]
theorem one_mem (i : ℕ) : (1 : A) ∈ S.ofSize i :=
  S.one_mem' i

theorem gram_mem (a b : ι) : J a b ∈ S.ofSize 1 :=
  S.gram_mem' a b

theorem gram_inv_mem (a b : ι) : J⁻¹ a b ∈ S.ofSize 1 :=
  S.gram_inv_mem' a b

/-- **Sizes increase**: a number of size `i` has every size `j ≥ i`, since `x = x * 1`. -/
theorem ofSize_mono : Monotone S.ofSize := by
  intro i j hij x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  simpa using S.mul_mem hx (S.one_mem k)

theorem mem_of_le (hx : x ∈ S.ofSize i) (hij : i ≤ j) : x ∈ S.ofSize j :=
  S.ofSize_mono hij hx

/-- A sum, over a finite set of at most `#ι + 1` indices, of numbers of size `i` has size
`i + 1`. -/
theorem sum_mem {β : Type*} (s : Finset β) (f : β → A) (hs : s.card ≤ Fintype.card ι + 1)
    (h : ∀ b ∈ s, f b ∈ S.ofSize i) : ∑ b ∈ s, f b ∈ S.ofSize (i + 1) :=
  S.multiset_sum_mem (s.val.map f) (by simpa using hs) (by simpa using h)

/-- A sum of two numbers of size `i` has size `i + 1`, provided `ι` is nonempty (so that sums of
two terms are allowed). -/
theorem add_mem [Nonempty ι] (hx : x ∈ S.ofSize i) (hy : y ∈ S.ofSize i) :
    x + y ∈ S.ofSize (i + 1) := by
  have h := S.multiset_sum_mem {x, y}
    (by
      simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]
      have := Fintype.card_pos (α := ι)
      omega)
    (by
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
        forall_eq_or_imp, forall_eq]
      exact ⟨hx, hy⟩)
  simpa using h

/-- A difference of two numbers of size `i` has size `i + 1`, provided `ι` is nonempty. -/
theorem sub_mem [Nonempty ι] (hx : x ∈ S.ofSize i) (hy : y ∈ S.ofSize i) :
    x - y ∈ S.ofSize (i + 1) := by
  simpa [sub_eq_add_neg] using S.add_mem hx ((S.neg_mem_iff).mpr hy)

/-! ### Vectors and matrices of a given size -/

/-- The vectors of size `i`: those all of whose entries have size `i`. -/
def vecsOfSize (i : ℕ) {κ : Type*} : Set (κ → A) :=
  {v | ∀ k, v k ∈ S.ofSize i}

/-- The matrices of size `i`: those all of whose entries have size `i`. -/
def matsOfSize (i : ℕ) {m n : Type*} : Set (Matrix m n A) :=
  {M | ∀ a b, M a b ∈ S.ofSize i}

variable {κ m n : Type*}

theorem mem_vecsOfSize {v : κ → A} : v ∈ S.vecsOfSize i ↔ ∀ k, v k ∈ S.ofSize i :=
  Iff.rfl

theorem mem_matsOfSize {M : Matrix m n A} : M ∈ S.matsOfSize i ↔ ∀ a b, M a b ∈ S.ofSize i :=
  Iff.rfl

theorem vecsOfSize_mono : Monotone (fun i => S.vecsOfSize i (κ := κ)) :=
  fun _ _ hij _ hv k => S.ofSize_mono hij (hv k)

theorem matsOfSize_mono : Monotone (fun i => S.matsOfSize i (m := m) (n := n)) :=
  fun _ _ hij _ hM a b => S.ofSize_mono hij (hM a b)

theorem mem_vecsOfSize_of_le {v : κ → A} (hv : v ∈ S.vecsOfSize i) (hij : i ≤ j) :
    v ∈ S.vecsOfSize j :=
  S.vecsOfSize_mono hij hv

theorem mem_matsOfSize_of_le {M : Matrix m n A} (hM : M ∈ S.matsOfSize i) (hij : i ≤ j) :
    M ∈ S.matsOfSize j :=
  S.matsOfSize_mono hij hM

@[simp]
theorem zero_mem_vecsOfSize (i : ℕ) : (0 : κ → A) ∈ S.vecsOfSize i :=
  fun _ => S.zero_mem i

theorem single_one_mem_vecsOfSize [DecidableEq κ] (i : ℕ) (k : κ) :
    (Pi.single k 1 : κ → A) ∈ S.vecsOfSize i := by
  intro k'
  by_cases h : k' = k
  · subst h; simp
  · simp [h]

@[simp]
theorem neg_mem_vecsOfSize_iff {v : κ → A} : -v ∈ S.vecsOfSize i ↔ v ∈ S.vecsOfSize i := by
  simp [mem_vecsOfSize]

@[simp]
theorem star_mem_vecsOfSize_iff {v : κ → A} : star v ∈ S.vecsOfSize i ↔ v ∈ S.vecsOfSize i := by
  simp [mem_vecsOfSize]

theorem smul_mem_vecsOfSize {v : κ → A} (hx : x ∈ S.ofSize i) (hv : v ∈ S.vecsOfSize j) :
    x • v ∈ S.vecsOfSize (i + j) :=
  fun k => S.mul_mem hx (hv k)

/-- A sum of two vectors of size `i` in `ι → A` has size `i + 1`. -/
theorem add_mem_vecsOfSize {v w : ι → A} (hv : v ∈ S.vecsOfSize i) (hw : w ∈ S.vecsOfSize i) :
    v + w ∈ S.vecsOfSize (i + 1) := fun k =>
  have : Nonempty ι := ⟨k⟩
  S.add_mem (hv k) (hw k)

/-- A difference of two vectors of size `i` in `ι → A` has size `i + 1`. -/
theorem sub_mem_vecsOfSize {v w : ι → A} (hv : v ∈ S.vecsOfSize i) (hw : w ∈ S.vecsOfSize i) :
    v - w ∈ S.vecsOfSize (i + 1) := fun k =>
  have : Nonempty ι := ⟨k⟩
  S.sub_mem (hv k) (hw k)

@[simp]
theorem neg_mem_matsOfSize_iff {M : Matrix m n A} :
    -M ∈ S.matsOfSize i ↔ M ∈ S.matsOfSize i := by
  simp [mem_matsOfSize]

@[simp]
theorem conjTranspose_mem_matsOfSize_iff {M : Matrix m n A} :
    Mᴴ ∈ S.matsOfSize i ↔ M ∈ S.matsOfSize i := by
  simp only [mem_matsOfSize, conjTranspose_apply, star_mem_iff]
  exact forall_comm

@[simp]
theorem zero_mem_matsOfSize (i : ℕ) : (0 : Matrix m n A) ∈ S.matsOfSize i :=
  fun _ _ => S.zero_mem i

theorem one_mem_matsOfSize [DecidableEq n] (i : ℕ) : (1 : Matrix n n A) ∈ S.matsOfSize i := by
  intro a b
  by_cases h : a = b
  · subst h; simp
  · simp [one_apply_ne h]

theorem smul_mem_matsOfSize {M : Matrix m n A} (hx : x ∈ S.ofSize i) (hM : M ∈ S.matsOfSize j) :
    x • M ∈ S.matsOfSize (i + j) :=
  fun a b => S.mul_mem hx (hM a b)

/-- A sum of two matrices of size `i` has size `i + 1`, provided `ι` is nonempty. -/
theorem add_mem_matsOfSize [Nonempty ι] {M N : Matrix m n A} (hM : M ∈ S.matsOfSize i)
    (hN : N ∈ S.matsOfSize i) : M + N ∈ S.matsOfSize (i + 1) :=
  fun a b => S.add_mem (hM a b) (hN a b)

/-- A difference of two matrices of size `i` has size `i + 1`, provided `ι` is nonempty. -/
theorem sub_mem_matsOfSize [Nonempty ι] {M N : Matrix m n A} (hM : M ∈ S.matsOfSize i)
    (hN : N ∈ S.matsOfSize i) : M - N ∈ S.matsOfSize (i + 1) :=
  fun a b => S.sub_mem (hM a b) (hN a b)

theorem gram_mem_matsOfSize : J ∈ S.matsOfSize 1 :=
  S.gram_mem

theorem gram_inv_mem_matsOfSize : J⁻¹ ∈ S.matsOfSize 1 :=
  S.gram_inv_mem

/-- A matrix belongs to `matsOfSize i` when each of its columns does to `vecsOfSize i`. -/
theorem mem_matsOfSize_of_col {M : Matrix m n A} (h : ∀ b, M.col b ∈ S.vecsOfSize i) :
    M ∈ S.matsOfSize i :=
  fun a b => h b a

/-- A dot product of vectors indexed by `ι`, of sizes `i` and `j`, has size `i + j + 1`. -/
theorem dotProduct_mem {v w : ι → A} (hv : v ∈ S.vecsOfSize i) (hw : w ∈ S.vecsOfSize j) :
    v ⬝ᵥ w ∈ S.ofSize (i + j + 1) :=
  S.sum_mem _ _ (by simp) fun k _ => S.mul_mem (hv k) (hw k)

/-- **Matrix times vector**: the product of a matrix of size `i` with columns indexed by `ι` and
a vector of size `j` has size `i + j + 1`. -/
theorem mulVec_mem_vecsOfSize {M : Matrix κ ι A} {v : ι → A} (hM : M ∈ S.matsOfSize i)
    (hv : v ∈ S.vecsOfSize j) : M *ᵥ v ∈ S.vecsOfSize (i + j + 1) :=
  fun k => S.dotProduct_mem (fun l => hM k l) hv

/-- **Matrix times matrix**: the product of matrices of sizes `i` and `j`, along the index type
`ι`, has size `i + j + 1`. -/
theorem mul_mem_matsOfSize {M : Matrix κ ι A} {N : Matrix ι n A} (hM : M ∈ S.matsOfSize i)
    (hN : N ∈ S.matsOfSize j) : M * N ∈ S.matsOfSize (i + j + 1) :=
  fun a b => S.dotProduct_mem (fun l => hM a l) (fun l => hN l b)

/-- **The size of the form**: `⟨u, v⟩ = star u ⬝ᵥ J *ᵥ v` has size `i + j + 3` for vectors `u`
of size `i` and `v` of size `j`. -/
theorem star_dotProduct_mulVec_mem {u v : ι → A} (hu : u ∈ S.vecsOfSize i)
    (hv : v ∈ S.vecsOfSize j) : star u ⬝ᵥ J *ᵥ v ∈ S.ofSize (i + j + 3) := by
  have h := S.dotProduct_mem ((S.star_mem_vecsOfSize_iff).mpr hu)
    (S.mulVec_mem_vecsOfSize S.gram_mem_matsOfSize hv)
  exact S.mem_of_le h (by omega)

/-! ### The sizes at a real place and at finite places -/

section ofNorm

variable {B : Type*} [NormedCommRing B] [NormOneClass B] [StarRing B] [NormedStarGroup B]
  {K : Matrix ι ι B}

omit [DecidableEq ι] in
/-- A scale `L ≥ #ι + 1` is at least `1`. -/
private theorem one_le_of_card_add_one_le {L : ℝ} (hL : (Fintype.card ι : ℝ) + 1 ≤ L) : 1 ≤ L :=
  (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hL

/-- **The size at a real place**: in a normed commutative ring with an isometric involution, the
numbers of norm at most `L ^ i` are a size for a Gram matrix `K` whenever the scale `L` is at
least `#ι + 1` and bounds the norms of the entries of `K` and `K⁻¹`. -/
def ofNorm (L : ℝ) (hL : (Fintype.card ι : ℝ) + 1 ≤ L) (hK : ∀ a b, ‖K a b‖ ≤ L)
    (hK' : ∀ a b, ‖K⁻¹ a b‖ ≤ L) : GramSize K where
  ofSize i := {x | ‖x‖ ≤ L ^ i}
  mul_mem' {i j x y} hx hy := by
    have hL0 : 0 ≤ L := zero_le_one.trans (one_le_of_card_add_one_le hL)
    calc ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le x y
      _ ≤ L ^ i * L ^ j := mul_le_mul hx hy (norm_nonneg y) (pow_nonneg hL0 i)
      _ = L ^ (i + j) := (pow_add L i j).symm
  multiset_sum_mem' {i} s hs h := by
    have hL0 : 0 ≤ L := zero_le_one.trans (one_le_of_card_add_one_le hL)
    calc ‖s.sum‖ ≤ (s.map norm).sum := norm_multiset_sum_le s
      _ ≤ Multiset.card (s.map norm) • L ^ i :=
          Multiset.sum_le_card_nsmul _ _ (by simpa using fun x hx => h x hx)
      _ = Multiset.card s * L ^ i := by simp
      _ ≤ (Fintype.card ι + 1) * L ^ i :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (pow_nonneg hL0 i)
      _ ≤ L * L ^ i := mul_le_mul_of_nonneg_right hL (pow_nonneg hL0 i)
      _ = L ^ (i + 1) := by ring
  neg_mem_iff' := by simp
  star_mem_iff' := by simp
  zero_mem' i := by simpa using pow_nonneg (zero_le_one.trans (one_le_of_card_add_one_le hL)) i
  one_mem' i := by simpa using one_le_pow₀ (one_le_of_card_add_one_le hL)
  gram_mem' a b := by simpa using hK a b
  gram_inv_mem' a b := by simpa using hK' a b

@[simp]
theorem mem_ofNorm_ofSize {L : ℝ} {hL : (Fintype.card ι : ℝ) + 1 ≤ L} {hK : ∀ a b, ‖K a b‖ ≤ L}
    {hK' : ∀ a b, ‖K⁻¹ a b‖ ≤ L} {i : ℕ} {x : B} :
    x ∈ (ofNorm L hL hK hK').ofSize i ↔ ‖x‖ ≤ L ^ i :=
  Iff.rfl

end ofNorm

section ofSubring

/-- **The size at finite places**: for a `star`-stable subring `O` of `A` (the integers) and a
self-adjoint element `α ∈ O` such that `α • J` and `α • J⁻¹` have entries in `O`, the numbers `x`
with `α ^ i * x ∈ O` are a size for `J`. -/
def ofSubring (O : Subring A) (hO : ∀ x ∈ O, star x ∈ O) (α : A) (hα : α ∈ O)
    (hα' : star α = α) (hJ : ∀ a b, α * J a b ∈ O) (hJ' : ∀ a b, α * J⁻¹ a b ∈ O) :
    GramSize J where
  ofSize i := {x | α ^ i * x ∈ O}
  mul_mem' {i j x y} hx hy := by
    simpa [pow_add, mul_mul_mul_comm] using O.mul_mem hx hy
  multiset_sum_mem' {i} s _ h := by
    have h1 : α ^ i * s.sum ∈ O := by
      have := O.multiset_sum_mem (s.map fun x => α ^ i * x) fun z hz => by
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
        exact h x hx
      rwa [Multiset.sum_map_mul_left, Multiset.map_id'] at this
    simp only [Set.mem_ofPred_eq]
    rw [pow_succ', mul_assoc]
    exact O.mul_mem hα h1
  neg_mem_iff' := by simp
  star_mem_iff' {i x} := by
    have key (y : A) : star (α ^ i * y) = α ^ i * star y := by
      rw [star_mul, star_pow, hα', mul_comm]
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hO _ h
      rwa [key, star_star] at this
    · rw [← key]
      exact hO _ h
  zero_mem' i := by simp
  one_mem' i := by simpa using O.pow_mem hα i
  gram_mem' a b := by simpa using hJ a b
  gram_inv_mem' a b := by simpa using hJ' a b

@[simp]
theorem mem_ofSubring_ofSize {O : Subring A} {hO : ∀ x ∈ O, star x ∈ O} {α : A} {hα : α ∈ O}
    {hα' : star α = α} {hJ : ∀ a b, α * J a b ∈ O} {hJ' : ∀ a b, α * J⁻¹ a b ∈ O} {i : ℕ}
    {x : A} : x ∈ (ofSubring O hO α hα hα' hJ hJ').ofSize i ↔ α ^ i * x ∈ O :=
  Iff.rfl

end ofSubring

end GramSize

end TauCeti
