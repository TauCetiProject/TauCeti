/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Supports, splittings, determinants and coordinate separation for dependent products

For `s : Set ι`, the submodule `Submodule.pi sᶜ (fun _ ↦ ⊥)` of `∀ i, M i` consists of the families
vanishing outside `s`, the `Pi` analogue of `Finsupp.supported`; such submodules for disjoint
supports meet in `⊥`. This file also records the linear splitting of a dependent product along a
predicate on the indices, the linear splitting of a `Fin (n + 1)`-indexed product into its initial
segment and its last coordinate, and the determinant of a coordinatewise endomorphism of a finite
dependent product, which is used in finite-product norm calculations.

Finally, distinct sums and differences of standard coordinate vectors can be separated at a
coordinate where their difference is regular. In two of these separations the critical case is
one family being the negative of the other, so that their difference is `2` times a vector of
`±1`s; those two assume `2` is regular, while separating two unordered sums needs no such
hypothesis. These elementary facts are useful for identifying root spaces from their coordinate
weights.

## Main results

* `Submodule.disjoint_pi_compl_bot_of_disjoint`: disjoint index sets give disjoint submodules of
  families vanishing outside them.
* `LinearEquiv.piFinSnoc`: the linear splitting of a tuple of length `n + 1` into its initial `n`
  coordinates and its last one, with `Fin.snoc` as its inverse.
* `LinearEquiv.piEquivPiSubtypeProd`: `Equiv.piEquivPiSubtypeProd` as a linear equivalence,
  splitting `∀ i, M i` into the factors indexed by `p` and by `¬p`.
* `LinearMap.toMatrix_piMap`: in a product basis, `LinearMap.piMap f` is block diagonal.
* `LinearMap.det_piMap`: the determinant of a coordinatewise endomorphism `LinearMap.piMap f` of a
  finite dependent product is the product of the determinants of its components.
* `TauCeti.exists_isRegular_single_sub_single_sub`: an ordered difference of standard coordinate
  vectors on two different coordinates and any other ordered difference differ regularly at some
  coordinate.
* `TauCeti.exists_isRegular_single_add_single_sub`: a sum of standard coordinate vectors on two
  different coordinates and a sum with a different unordered index pair differ regularly at some
  coordinate.
* `TauCeti.exists_isRegular_neg_single_add_single_sub_single_add_single`: a negative coordinate
  sum and a coordinate sum on two different coordinates differ regularly at some coordinate.
-/

namespace Submodule

/-- Disjoint index sets give disjoint submodules of the families vanishing outside them: a family
vanishing outside `s` and outside `t`, for `s` and `t` disjoint, is zero. -/
public theorem disjoint_pi_compl_bot_of_disjoint {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {s t : Set ι} (h : Disjoint s t) :
    Disjoint (pi sᶜ fun i ↦ (⊥ : Submodule R (M i))) (pi tᶜ fun i ↦ (⊥ : Submodule R (M i))) :=
  disjoint_def.mpr fun f hs ht ↦ funext fun i ↦ by
    by_cases hi : i ∈ s
    · exact ht i (Set.disjoint_left.mp h hi)
    · exact hs i hi

end Submodule

namespace LinearEquiv

section FinSnoc

variable (R : Type*) [Semiring R] {n : ℕ} (M : Fin (n + 1) → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Splits a tuple of length `n + 1` into its initial `n` coordinates and its last one, with inverse
`Fin.snoc`. This is the inverse of `Fin.snocEquiv` as a `LinearEquiv`, with the factors swapped so
that the initial segment comes first, matching the argument order of `Fin.snoc`. -/
public def piFinSnoc :
    ((i : Fin (n + 1)) → M i) ≃ₗ[R] ((i : Fin n) → M i.castSucc) × M (Fin.last n) where
  toEquiv := (Fin.snocEquiv M).symm.trans (Equiv.prodComm _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
public theorem piFinSnoc_apply (v : (i : Fin (n + 1)) → M i) :
    piFinSnoc R M v = (Fin.init v, v (Fin.last n)) := by
  simp [piFinSnoc]

@[simp]
public theorem piFinSnoc_symm_apply (p : ((i : Fin n) → M i.castSucc) × M (Fin.last n)) :
    (piFinSnoc R M).symm p = Fin.snoc p.1 p.2 := by
  ext i
  simp [piFinSnoc]

end FinSnoc

variable (R : Type*) {ι : Type*} [Semiring R] (p : ι → Prop) [DecidablePred p] (M : ι → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Splits the indices of the module `∀ i, M i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `LinearEquiv`. -/
public def piEquivPiSubtypeProd :
    ((i : ι) → M i) ≃ₗ[R] ((i : {x : ι // p x}) → M i) × ((i : {x : ι // ¬p x}) → M i) where
  toEquiv := Equiv.piEquivPiSubtypeProd p M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
public theorem piEquivPiSubtypeProd_apply (f : (i : ι) → M i) :
    piEquivPiSubtypeProd R p M f =
      (fun i : {x : ι // p x} ↦ f i, fun i : {x : ι // ¬p x} ↦ f i) := (rfl)

@[simp]
public theorem piEquivPiSubtypeProd_symm_apply
    (f : ((i : {x : ι // p x}) → M i) × ((i : {x : ι // ¬p x}) → M i)) (i : ι) :
    (piEquivPiSubtypeProd R p M).symm f i = if h : p i then f.1 ⟨i, h⟩ else f.2 ⟨i, h⟩ := (rfl)

end LinearEquiv

namespace LinearMap

/-- In the product basis `Pi.basis b`, the coordinatewise endomorphism `LinearMap.piMap f` has the
block-diagonal matrix whose blocks are the matrices of the `f i` in the bases `b i`. -/
public theorem toMatrix_piMap {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (b : ∀ i, Module.Basis (κ i) R (M i))
    (f : ∀ i, M i →ₗ[R] M i) :
    toMatrix (Pi.basis b) (Pi.basis b) (piMap f) =
      Matrix.blockDiagonal' fun i ↦ toMatrix (b i) (b i) (f i) := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  simp only [toMatrix_apply', Pi.basis_apply, Matrix.blockDiagonal'_apply]
  split_ifs with h
  · subst h
    simp
  · simp [h]

/-- The determinant of the coordinatewise endomorphism `LinearMap.piMap f` of a finite dependent
product of finite free modules is the product of the determinants of the `f i`. This is the
dependent-family version of Mathlib's `LinearMap.det_pi`. -/
@[simp]
public theorem det_piMap {R ι : Type*} [CommRing R] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)] (f : ∀ i, M i →ₗ[R] M i) :
    (piMap f).det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  rw [← det_toMatrix (Pi.basis b), toMatrix_piMap, Matrix.det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ ↦ det_toMatrix (b i) (f i)

end LinearMap

namespace TauCeti

variable {K ι : Type*} [Ring K] [DecidableEq ι]

/-- If `i ≠ j` and the index pair `(a, b)` differs from `(i, j)`, then the ordered differences of
standard coordinate vectors `eₐ - e_b` and `eᵢ - eⱼ` differ by a regular scalar at some
coordinate, provided `2` is regular. -/
public theorem exists_isRegular_single_sub_single_sub (h2 : IsRegular (2 : K))
    {i j : ι} (hij : i ≠ j) (a b : ι) (hne : ¬(a = i ∧ b = j)) :
    ∃ k, IsRegular
      ((Pi.single a 1 - Pi.single b 1 - (Pi.single i 1 - Pi.single j 1) : ι → K) k) := by
  have h1 : IsRegular (-1 : K) := isUnit_neg_one.isRegular
  by_cases hab : a = b
  · exact ⟨i, by simpa [hab, hij] using h1⟩
  by_cases hai : a = i
  · have hbj : b ≠ j := fun h ↦ hne ⟨hai, h⟩
    exact ⟨b, by simpa [hai, hbj] using h1⟩
  refine ⟨a, ?_⟩
  by_cases haj : a = j
  · subst a
    simpa [hab, hai, hij, one_add_one_eq_two] using h2
  · simpa [hab, hai, haj] using isRegular_one

/-- If `i ≠ j` and the unordered index pair `{a, b}` differs from `{i, j}`, then the sums of
standard coordinate vectors `eₐ + e_b` and `eᵢ + eⱼ` differ by a regular scalar at some
coordinate. -/
public theorem exists_isRegular_single_add_single_sub {i j : ι} (hij : i ≠ j) (a b : ι)
    (hne : ¬((a = i ∧ b = j) ∨ (a = j ∧ b = i))) :
    ∃ k, IsRegular
      ((Pi.single a 1 + Pi.single b 1 - (Pi.single i 1 + Pi.single j 1) : ι → K) k) := by
  have h1 : IsRegular (1 : K) := isRegular_one
  by_cases hab : a = b
  · subst b
    by_cases hai : a = i
    · exact ⟨i, by simpa [hai, hij] using h1⟩
    by_cases haj : a = j
    · exact ⟨j, by simpa [haj, hij] using h1⟩
    exact ⟨i, by simpa [hai, hij] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))⟩
  by_cases hai : a = i
  · have hbi : b ≠ i := fun h ↦ hab (hai.trans h.symm)
    have hbj : b ≠ j := fun h ↦ hne (.inl ⟨hai, h⟩)
    exact ⟨b, by simpa [hab, hbi, hbj] using h1⟩
  by_cases haj : a = j
  · have hbi : b ≠ i := fun h ↦ hne (.inr ⟨haj, h⟩)
    have hbj : b ≠ j := fun h ↦ hab (haj.trans h.symm)
    exact ⟨b, by simpa [hab, hbi, hbj] using h1⟩
  exact ⟨a, by simpa [hab, hai, haj] using h1⟩

/-- If `i ≠ j`, then the negative sum of standard coordinate vectors `-(eₐ + e_b)` and the sum
`eᵢ + eⱼ` differ by a regular scalar at some coordinate, provided `2` is regular. -/
public theorem exists_isRegular_neg_single_add_single_sub_single_add_single
    (h2 : IsRegular (2 : K)) {i j : ι} (hij : i ≠ j) (a b : ι) :
    ∃ k, IsRegular
      ((-(Pi.single a 1 + Pi.single b 1) - (Pi.single i 1 + Pi.single j 1) : ι → K) k) := by
  have h1 : IsRegular (-1 : K) := isUnit_neg_one.isRegular
  have hneg2 : IsRegular (-(2 : K)) := by simpa using h1.mul h2
  by_cases hai : a = i <;> by_cases hbi : b = i
  · subst a b
    exact ⟨j, by simpa [hij] using h1⟩
  · exact ⟨i, by convert hneg2 using 1; norm_num [hai, hbi, hij]⟩
  · exact ⟨i, by convert hneg2 using 1; norm_num [hai, hbi, hij]⟩
  · exact ⟨i, by simpa [hai, hbi, hij] using h1⟩

end TauCeti
