/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The even and odd parts of a contractible complex

A cochain complex `K` is *contractible* when its identity is null-homotopic, that is, when there
is a homotopy `h : Homotopy (𝟙 K) 0`. If moreover the terms of `K` vanish outside a finite set `s`
of degrees, then the biproduct of the terms of `K` in the even degrees of `s` is isomorphic to the
biproduct of the terms in the odd degrees of `s`:

```text
⨁_{n ∈ s, n even} Kⁿ ≅ ⨁_{n ∈ s, n odd} Kⁿ.
```

This is the mechanism behind the vanishing of every additive invariant on contractible bounded
complexes, and hence behind the homotopy invariance of Euler characteristics.

The isomorphism is the operator `d + h`. It squares to `d h + h d + h h = 1 + h h`, so it is an
involution exactly when the contracting homotopy squares to zero. A null-homotopy of the identity
is a contraction of `K` onto the zero complex, and `TauCeti.Contraction.normalize` replaces its
homotopy by one which squares to zero (`Homotopy.normalize`). For that normalized homotopy,
`d + h`, read as a matrix between the even and the odd terms, is inverse to itself; the only
bookkeeping is that the entries `d h + h d` sum to the identity on each term and to zero between
distinct terms, which is where the finite support of `K` enters.

## Main definitions

* `Homotopy.normalize`: a null-homotopy of the identity whose components compose to zero,
  `Homotopy.normalize_hom_comp_hom`.
* `Homotopy.biproductEvenIsoBiproductOdd`: the isomorphism between the even and the odd parts of
  a contractible complex supported on a finite set of degrees.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15, where this isomorphism underlies the comparison of `K₀` of an additive category
  with `K₀` of its bounded homotopy category.
* Bernhard Keller, *Introduction to A-infinity algebras and modules*, Section 3.3, for the
  normalization of a contracting homotopy to one squaring to zero, carried out in
  `TauCeti/Algebra/Homology/Contraction.lean`.
-/

public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex.HomComplex ZeroObject

universe v u

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] {K : CochainComplex C ℤ}

section Normalize

variable [HasZeroObject C] (h : Homotopy (𝟙 K) 0)

/-- A null-homotopy of the identity of `K`, as a contraction of `K` onto the zero complex. -/
noncomputable def toContractionZero : TauCeti.Contraction K 0 where
  incl := 0
  proj := 0
  homotopy := Cochain.ofHomotopy h
  incl_comp_proj := (isZero_zero _).eq_of_src _ _
  δ_homotopy := by rw [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero, zero_comp, sub_zero]

@[simp] lemma toContractionZero_incl : h.toContractionZero.incl = 0 := (rfl)

@[simp] lemma toContractionZero_proj : h.toContractionZero.proj = 0 := (rfl)

/-- The null-homotopy of the identity of `K` obtained by normalizing `h`: its components compose
to zero, `Homotopy.normalize_hom_comp_hom`. -/
noncomputable def normalize : Homotopy (𝟙 K) 0 :=
  (Cochain.equivHomotopy _ _).symm ⟨h.toContractionZero.normalize.homotopy, by
    rw [Cochain.ofHom_zero, add_zero, h.toContractionZero.normalize.δ_homotopy]
    simp⟩

private lemma normalize_hom (i j : ℤ) :
    h.normalize.hom i j =
      if hij : i + (-1) = j then h.toContractionZero.normalize.homotopy.v i j hij else 0 :=
  (rfl)

/-- The components of the normalized null-homotopy compose to zero. -/
@[simp]
lemma normalize_hom_comp_hom (i j k : ℤ) :
    h.normalize.hom i j ≫ h.normalize.hom j k = 0 := by
  rw [normalize_hom, normalize_hom]
  split_ifs with hij hjk
  · have := Cochain.congr_v h.toContractionZero.normalize.homotopy_comp_homotopy i k (by omega)
    rwa [Cochain.comp_v _ _ _ i j k hij hjk, Cochain.zero_v] at this
  · rw [comp_zero]
  · rw [zero_comp]
  · rw [zero_comp]

end Normalize

section EvenOdd

/-! The operator `d + h` and the identities satisfied by its square, for a null-homotopy `H` of
the identity whose components compose to zero. -/

variable (H : Homotopy (𝟙 K) 0)

/-- The `(n, m)` entry `d + h` of the operator comparing the even and the odd terms. -/
private def evenOddEntry (n m : ℤ) : K.X n ⟶ K.X m := K.d n m + H.hom n m

/-- The `(n, k)` entry of the square of `d + h`, before summing over the intermediate degree. -/
private def evenOddSquareEntry (n k m : ℤ) : K.X n ⟶ K.X k :=
  K.d n m ≫ H.hom m k + H.hom n m ≫ K.d m k

variable (hH : ∀ i j k, H.hom i j ≫ H.hom j k = 0)
include hH

private lemma evenOddEntry_comp_evenOddEntry (n m k : ℤ) :
    evenOddEntry H n m ≫ evenOddEntry H m k = evenOddSquareEntry H n k m := by
  simp only [evenOddEntry, evenOddSquareEntry, Preadditive.add_comp, Preadditive.comp_add,
    d_comp_d, hH, zero_add, add_zero]
  exact add_comm _ _

omit hH

private lemma evenOddSquareEntry_eq_zero_of_ne {n k : ℤ} (hnk : n ≠ k) (m : ℤ) :
    evenOddSquareEntry H n k m = 0 := by
  have h₁ : K.d n m ≫ H.hom m k = 0 := by
    by_cases h : n + 1 = m
    · rw [H.zero m k (by simp only [ComplexShape.up_Rel]; omega), comp_zero]
    · rw [K.shape n m (by simpa only [ComplexShape.up_Rel] using h), zero_comp]
  have h₂ : H.hom n m ≫ K.d m k = 0 := by
    by_cases h : m + 1 = n
    · rw [K.shape m k (by simp only [ComplexShape.up_Rel]; omega), comp_zero]
    · rw [H.zero n m (by simpa only [ComplexShape.up_Rel] using h), zero_comp]
  rw [evenOddSquareEntry, h₁, h₂, add_zero]

private lemma evenOddSquareEntry_eq_zero_of_isZero (n k : ℤ) {m : ℤ} (hm : IsZero (K.X m)) :
    evenOddSquareEntry H n k m = 0 := by
  rw [evenOddSquareEntry, hm.eq_of_tgt (K.d n m) 0, hm.eq_of_tgt (H.hom n m) 0, zero_comp,
    zero_comp, add_zero]

private lemma evenOddSquareEntry_eq_zero_of_not_adjacent (n k : ℤ) {m : ℤ} (h₁ : m ≠ n + 1)
    (h₂ : m + 1 ≠ n) : evenOddSquareEntry H n k m = 0 := by
  rw [evenOddSquareEntry, K.shape n m (by simpa only [ComplexShape.up_Rel] using h₁.symm),
    H.zero n m (by simpa only [ComplexShape.up_Rel] using h₂), zero_comp, zero_comp, add_zero]

/-- Summing the entries of the square of `d + h` over a set of degrees containing every degree
adjacent to `n` on which `K` is nonzero gives the identity of `Kⁿ`. -/
private lemma sum_evenOddSquareEntry_self (n : ℤ) (T : Finset ℤ)
    (hT : ∀ m, m ∉ T → IsZero (K.X m) ∨ (m ≠ n + 1 ∧ m + 1 ≠ n)) :
    ∑ m ∈ T, evenOddSquareEntry H n n m = 𝟙 (K.X n) := by
  have h₁ : ∑ m ∈ T, evenOddSquareEntry H n n m =
      ∑ m ∈ T ∪ {n - 1, n + 1}, evenOddSquareEntry H n n m :=
    Finset.sum_subset Finset.subset_union_left fun m _ hm => by
      rcases hT m hm with hm | ⟨h₁, h₂⟩
      · exact evenOddSquareEntry_eq_zero_of_isZero H n n hm
      · exact evenOddSquareEntry_eq_zero_of_not_adjacent H n n h₁ h₂
  have h₂ : ∑ m ∈ ({n - 1, n + 1} : Finset ℤ), evenOddSquareEntry H n n m =
      ∑ m ∈ T ∪ {n - 1, n + 1}, evenOddSquareEntry H n n m :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact evenOddSquareEntry_eq_zero_of_not_adjacent H n n hm.2 (by omega)
  have hpair : ∑ m ∈ T, evenOddSquareEntry H n n m =
      ∑ m ∈ ({n - 1, n + 1} : Finset ℤ), evenOddSquareEntry H n n m := h₁.trans h₂.symm
  have hcomm := H.comm n
  rw [dNext_eq H.hom (i' := n + 1) (by simp), prevD_eq H.hom (j' := n - 1) (by simp)] at hcomm
  simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero] at hcomm
  rw [hpair, Finset.sum_pair (by omega), hcomm, evenOddSquareEntry, evenOddSquareEntry,
    K.shape n (n - 1) (by simp only [ComplexShape.up_Rel]; omega),
    H.zero n (n + 1) (by simp only [ComplexShape.up_Rel]; omega), zero_comp, zero_comp, zero_add,
    add_zero, add_comm]

include hH

/-- The matrix `d + h` from the terms of `K` in the degrees `E` to those in the degrees `O`,
composed with the same matrix back, is the identity, provided that every degree adjacent to a
degree of `E` either lies in `O` or carries a zero term. -/
private lemma matrix_comp_matrix [HasFiniteBiproducts C] (E O : Finset ℤ)
    (hEO : ∀ n ∈ E, ∀ m, m ∉ O → IsZero (K.X m) ∨ (m ≠ n + 1 ∧ m + 1 ≠ n)) :
    (biproduct.matrix fun (n : E) (m : O) => evenOddEntry H n m) ≫
      (biproduct.matrix fun (m : O) (n : E) => evenOddEntry H m n) = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun n => biproduct.hom_ext _ _ fun k => ?_
  simp only [Category.assoc, biproduct.matrix_π, biproduct.ι_matrix_assoc, biproduct.lift_desc,
    Category.id_comp]
  simp only [evenOddEntry_comp_evenOddEntry H hH]
  by_cases hnk : n = k
  · subst hnk
    rw [biproduct.ι_π_self, Finset.sum_coe_sort O fun m => evenOddSquareEntry H n n m]
    exact sum_evenOddSquareEntry_self H n O (hEO n n.2)
  · rw [biproduct.ι_π_ne _ hnk]
    exact Finset.sum_eq_zero fun m _ =>
      evenOddSquareEntry_eq_zero_of_ne H (fun h => hnk (Subtype.ext h)) m

omit hH

variable [HasFiniteBiproducts C]

/-- **The even and odd parts of a contractible complex are isomorphic.** If the identity of `K`
is null-homotopic and the terms of `K` vanish outside the finite set `s` of degrees, then the
biproduct of the terms of `K` in the even degrees of `s` is isomorphic to the biproduct of its
terms in the odd degrees of `s`. The isomorphism is the operator `d + h` for the normalized
homotopy `h`, which is its own inverse. -/
noncomputable def biproductEvenIsoBiproductOdd (h : Homotopy (𝟙 K) 0) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → IsZero (K.X n)) :
    (⨁ fun n : (s.filter fun n => n % 2 = 0) => K.X n) ≅
      ⨁ fun n : (s.filter fun n => ¬ n % 2 = 0) => K.X n where
  hom := biproduct.matrix fun n m => evenOddEntry h.normalize n m
  inv := biproduct.matrix fun m n => evenOddEntry h.normalize m n
  hom_inv_id := matrix_comp_matrix h.normalize h.normalize_hom_comp_hom _ _ fun n hn m hm => by
    simp only [Finset.mem_filter, not_and, not_not] at hn hm
    by_cases hms : m ∈ s
    · exact Or.inr (by have := hm hms; omega)
    · exact Or.inl (hs m hms)
  inv_hom_id := matrix_comp_matrix h.normalize h.normalize_hom_comp_hom _ _ fun n hn m hm => by
    simp only [Finset.mem_filter, not_and] at hn hm
    by_cases hms : m ∈ s
    · exact Or.inr (by have := hm hms; omega)
    · exact Or.inl (hs m hms)

end EvenOdd

end Homotopy
