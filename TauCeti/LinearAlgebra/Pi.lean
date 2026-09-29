/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Coordinate separation, supports, splittings and determinants of dependent products

Distinct sums and differences of standard coordinate vectors can be separated at a coordinate
where their difference is regular. Two of these separations compare families that agree after
doubling, so they assume `2` is regular; separating two unordered sums needs no such hypothesis.
These elementary facts are useful for identifying root spaces from their coordinate weights.

For `s : Set ι`, the submodule `Submodule.pi sᶜ (fun _ ↦ ⊥)` of `ι → M` consists of the families
vanishing outside `s` — the `Pi` analogue of `Finsupp.supported`. This file records that
complementary supports meet in `⊥`. It also records the linear splitting of a dependent product
along a predicate on the indices, and the determinant of a coordinatewise endomorphism of a finite
dependent product, which is used in finite-product norm calculations.

Mathlib has `Set.disjoint_pi`, but that is about `Set.pi` and characterises disjointness through
the fibres; it says nothing about the submodules cut out by a support condition.

## Main results

* `TauCeti.exists_isRegular_single_sub_single_sub`: distinct ordered differences of standard
  coordinate vectors differ regularly at some coordinate.
* `TauCeti.exists_isRegular_single_add_single_sub`: distinct unordered sums of two different
  standard coordinate vectors differ regularly at some coordinate.
* `TauCeti.exists_isRegular_neg_single_add_single_sub_single_add_single`: a negative coordinate
  sum and a coordinate sum on two different coordinates differ regularly at some coordinate.
* `Submodule.disjoint_pi_compl_bot_of_disjoint`: disjoint index sets give disjoint submodules of
  families vanishing outside them.
* `LinearEquiv.piEquivPiSubtypeProd`: `Equiv.piEquivPiSubtypeProd` as a linear equivalence,
  splitting `∀ i, M i` into the factors indexed by `p` and by `¬p`.
* `LinearMap.det_pi_of_apply_eq_dependent`: the determinant of a coordinatewise endomorphism of a
  finite dependent product is the product of the determinants on its factors.
-/

namespace Submodule

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]

/-- **Disjoint sets of indices give disjoint submodules of families vanishing outside them.**
A family vanishing outside `s` and outside `t` at once, for `s` and `t` disjoint, vanishes
everywhere. The submodules are `Submodule.pi` at the zero submodule.

Nothing here is topological or about any particular index type; the Huber two-sided series use it
at `ι = ℤ` with `s` and `t` the non-negative and negative degrees. -/
public theorem disjoint_pi_compl_bot_of_disjoint {ι : Type*} {s t : Set ι} (h : Disjoint s t) :
    Disjoint (Submodule.pi sᶜ fun _ ↦ (⊥ : Submodule A M))
      (Submodule.pi tᶜ fun _ ↦ (⊥ : Submodule A M)) :=
  Submodule.disjoint_def.mpr fun f hs ht ↦ funext fun i ↦ by
    by_cases hi : i ∈ s
    · exact ht i (Set.disjoint_left.mp h hi)
    · exact hs i hi

end Submodule

namespace LinearEquiv

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

namespace TauCeti

open scoped BigOperators

universe u v

section CoordinateSeparation

variable {K ι : Type*} [CommRing K] [DecidableEq ι]

/-- If two ordered differences of standard coordinate vectors are distinct by their indices, then
they differ by a regular scalar at some coordinate, provided `2` is regular. -/
public theorem exists_isRegular_single_sub_single_sub (h2 : IsRegular (2 : K))
    {i j : ι} (hij : i ≠ j) (a b : ι) (hne : ¬(a = i ∧ b = j)) :
    ∃ k, IsRegular
      ((Pi.single (M := fun _ : ι => K) a 1) k -
        (Pi.single (M := fun _ : ι => K) b 1) k -
        ((Pi.single (M := fun _ : ι => K) i 1) k -
          (Pi.single (M := fun _ : ι => K) j 1) k)) := by
  classical
  by_cases hab : a = b
  · subst b
    refine ⟨i, ?_⟩
    simpa [hij] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))
  · by_cases hai : a = i
    · have hbj : b ≠ j := fun h => hne ⟨hai, h⟩
      refine ⟨b, ?_⟩
      simpa [hai, hbj] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))
    · refine ⟨a, ?_⟩
      by_cases haj : a = j
      · subst a
        simpa [hab, hai, hij, one_add_one_eq_two] using h2
      · simpa [hab, hai, haj] using (isRegular_one : IsRegular (1 : K))

/-- If two unordered sums of standard coordinate vectors on different target coordinates have
different index pairs, then they differ by a regular scalar at some coordinate. -/
public theorem exists_isRegular_single_add_single_sub
    {i j : ι} (hij : i ≠ j) (a b : ι)
    (hne : ¬((a = i ∧ b = j) ∨ (a = j ∧ b = i))) :
    ∃ k, IsRegular
      ((Pi.single (M := fun _ : ι => K) a 1) k +
        (Pi.single (M := fun _ : ι => K) b 1) k -
        ((Pi.single (M := fun _ : ι => K) i 1) k +
          (Pi.single (M := fun _ : ι => K) j 1) k)) := by
  classical
  by_cases hab : a = b
  · subst b
    by_cases hai : a = i
    · exact ⟨i, by simpa [hai, hij] using (isRegular_one : IsRegular (1 : K))⟩
    · by_cases haj : a = j
      · exact ⟨j, by simpa [haj, hij] using (isRegular_one : IsRegular (1 : K))⟩
      · exact ⟨i, by simpa [hai, hij] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))⟩
  · by_cases hai : a = i
    · have hbj : b ≠ j := fun h => hne (Or.inl ⟨hai, h⟩)
      have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
      refine ⟨b, ?_⟩
      simpa [hab, hbi, hbj] using (isRegular_one : IsRegular (1 : K))
    · by_cases haj : a = j
      · have hbi : b ≠ i := fun h => hne (Or.inr ⟨haj, h⟩)
        have hbj : b ≠ j := fun h => hab (haj.trans h.symm)
        refine ⟨b, ?_⟩
        simpa [hab, hbi, hbj] using (isRegular_one : IsRegular (1 : K))
      · refine ⟨a, ?_⟩
        simpa [hab, hai, haj] using (isRegular_one : IsRegular (1 : K))

/-- A negative sum of two standard coordinate vectors and a sum on two different coordinates
differ by a regular scalar at some coordinate, provided `2` is regular. -/
public theorem exists_isRegular_neg_single_add_single_sub_single_add_single
    (h2 : IsRegular (2 : K)) {i j : ι} (hij : i ≠ j) (a b : ι) :
    ∃ k, IsRegular
      (-((Pi.single (M := fun _ : ι => K) a 1) k +
          (Pi.single (M := fun _ : ι => K) b 1) k) -
        ((Pi.single (M := fun _ : ι => K) i 1) k +
          (Pi.single (M := fun _ : ι => K) j 1) k)) := by
  classical
  have hneg2 : IsRegular (-(2 : K)) := by
    simpa using isUnit_neg_one.isRegular.mul h2
  by_cases hai : a = i
  · by_cases hbi : b = i
    · subst a
      subst b
      refine ⟨j, ?_⟩
      simpa [hij] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))
    · refine ⟨i, ?_⟩
      convert hneg2 using 1
      simp [hai, hbi, hij]
      ring
  · by_cases hbi : b = i
    · refine ⟨i, ?_⟩
      convert hneg2 using 1
      simp [hai, hbi, hij]
      ring
    · refine ⟨i, ?_⟩
      simpa [hai, hbi, hij] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))

end CoordinateSeparation

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι]

/-- The determinant of a coordinatewise endomorphism of a finite dependent product. -/
public theorem _root_.LinearMap.det_pi_of_apply_eq_dependent {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)]
    (T : ((i : ι) → M i) →ₗ[R] ((i : ι) → M i)) (f : ∀ i, M i →ₗ[R] M i)
    (hT : ∀ x i, T x i = f i (x i)) :
    T.det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  let _ (i : ι) : Fintype (Module.Free.ChooseBasisIndex R (M i)) := Fintype.ofFinite _
  let B : Module.Basis (Σ i, Module.Free.ChooseBasisIndex R (M i)) R ((i : ι) → M i) :=
    Pi.basis b
  rw [← LinearMap.det_toMatrix B]
  have hmatrix :
      (LinearMap.toMatrix B B T) =
        Matrix.blockDiagonal' (fun i ↦ LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [LinearMap.toMatrix_apply', B, b, Pi.basis_apply, Matrix.blockDiagonal'_apply]
    split_ifs with h
    · subst i₂
      simp [hT]
    · simp [hT, h]
  rw [hmatrix]
  let _ : LinearOrder ι := Equiv.linearOrder (Fintype.equivFin ι)
  rw [(Matrix.blockTriangular_blockDiagonal' _).det_fintype]
  apply Finset.prod_congr rfl
  intro i hi
  let e : Module.Free.ChooseBasisIndex R (M i) ≃
      {a : Σ i, Module.Free.ChooseBasisIndex R (M i) // a.1 = i} :=
    { toFun := fun j ↦ ⟨⟨i, j⟩, rfl⟩
      invFun := fun a ↦ cast (by rw [a.2]) a.1.2
      left_inv := by intro j; rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rcases a with ⟨⟨a, j⟩, ha⟩
        dsimp at ha
        subst a
        rfl }
  rw [← LinearMap.det_toMatrix (b i)]
  rw [← Matrix.det_reindex_self e]
  congr 1
  ext j k
  rcases j with ⟨⟨j₁, j₂⟩, hj⟩
  rcases k with ⟨⟨k₁, k₂⟩, hk⟩
  dsimp at hj hk
  subst j₁
  subst k₁
  simp [e, Matrix.toSquareBlock_def, Matrix.reindex]

end TauCeti
