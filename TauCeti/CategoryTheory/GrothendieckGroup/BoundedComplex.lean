/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contractible
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The Euler characteristic of a bounded complex in split `K₀`

For a cochain complex `K` over an additive category `C` and a biproduct-additive invariant `v`,
the alternating sum

```text
∑ n ∈ s, (-1)ⁿ v(Kⁿ)
```

over a finite set `s` of degrees is the **Euler characteristic** of `K` relative to `v`. When `v`
is the class map of split `K₀`, this is `TauCeti.SplitK0.eulerChar K s`. As in the abelian case
(`TauCeti.AbelianK0.eulerChar`), the summation range is data: no `finsum` is used, and what
boundedness buys is that every range containing the support of `K` gives the same value.

The main theorem is **homotopy invariance**: the Euler characteristic of a bounded complex depends
only on its homotopy type. Its heart is the vanishing on contractible complexes, which is the
statement that the even and the odd parts of a contractible bounded complex are isomorphic
(`Homotopy.biproductEvenIsoBiproductOdd`). Homotopy invariance follows from it through the
mapping cone: the cone of a homotopy equivalence is contractible, and its terms are the biproducts
`Kⁿ⁺¹ ⊞ Lⁿ`, so its Euler characteristic is `χ(L) - χ(K)`.

These are the ingredients of the standard comparison between split `K₀` of an additive category
and the triangulated `K₀` of its bounded homotopy category, which sends a bounded complex to the
alternating sum of the classes of its terms: homotopy invariance makes that assignment well
defined on the objects of the homotopy category, and the mapping-cone formula makes it additive
on distinguished triangles.

## Main definitions

* `TauCeti.SplitK0.eulerChar`: the alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` in split `K₀` of the
  terms of a cochain complex over a finite set of degrees.

## Main results

* `TauCeti.SplitK0.AdditiveInvariant.sum_negOnePow_obj_X_eq_zero_of_homotopy_id_zero` and
  `TauCeti.SplitK0.eulerChar_eq_zero_of_homotopy_id_zero`: a contractible complex supported on
  `s` has vanishing Euler characteristic over `s`.
* `TauCeti.SplitK0.AdditiveInvariant.sum_negOnePow_obj_X_eq_of_homotopyEquiv` and
  `TauCeti.SplitK0.eulerChar_eq_of_homotopyEquiv`: **homotopy invariance** of the Euler
  characteristic of bounded complexes.
* `TauCeti.SplitK0.eulerChar_mappingCone` and `TauCeti.SplitK0.eulerChar_shift`: the Euler
  characteristic of a mapping cone is `χ(L) - χ(K)`, and that of the shift `K⟦1⟧` is `-χ(K)`.
* `TauCeti.SplitK0.eulerChar_eq_eulerChar`: independence of the summation range for a bounded
  complex.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15, for the comparison of `K₀` of an additive category with `K₀` of its bounded
  homotopy category through the alternating sum of the terms.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject HomologicalComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

namespace SplitK0.AdditiveInvariant

variable {G : Type*} [AddCommGroup G] (v : SplitK0.AdditiveInvariant C G)

section Range

variable (K : CochainComplex C ℤ)

/-- Two finite sets of degrees both containing the support of a complex give the same alternating
sum of the values of an additive invariant on its terms. -/
theorem sum_negOnePow_obj_X_eq_of_isZero {s t : Finset ℤ} (hs : ∀ n, n ∉ s → IsZero (K.X n))
    (ht : ∀ n, n ∉ t → IsZero (K.X n)) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n) =
      ∑ n ∈ t, ((n.negOnePow : ℤ)) • v.obj (K.X n) := by
  have h₁ : ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n) =
      ∑ n ∈ s ∪ t, ((n.negOnePow : ℤ)) • v.obj (K.X n) :=
    Finset.sum_subset Finset.subset_union_left fun n _ hn => by
      rw [v.obj_eq_zero_of_isZero (hs n hn), smul_zero]
  have h₂ : ∑ n ∈ t, ((n.negOnePow : ℤ)) • v.obj (K.X n) =
      ∑ n ∈ s ∪ t, ((n.negOnePow : ℤ)) • v.obj (K.X n) :=
    Finset.sum_subset Finset.subset_union_right fun n _ hn => by
      rw [v.obj_eq_zero_of_isZero (ht n hn), smul_zero]
  rw [h₁, h₂]

/-- The Euler characteristic of the shift `K⟦1⟧` over `s` is minus the Euler characteristic of `K`
over the translate `s + 1`. -/
theorem sum_negOnePow_obj_X_shift (s : Finset ℤ) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj ((K⟦(1 : ℤ)⟧).X n) =
      -∑ n ∈ s.map (Equiv.addRight (1 : ℤ)).toEmbedding, ((n.negOnePow : ℤ)) • v.obj (K.X n) := by
  rw [Finset.sum_map, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [v.map_iso (eqToIso (CochainComplex.shiftFunctor_obj_X' K 1 n))]
  simp [Int.negOnePow_succ]

end Range

section MappingCone

variable {K L : CochainComplex C ℤ}

/-- The Euler characteristic of a mapping cone: over any finite set `s` of degrees, it is the Euler
characteristic of the target over `s` minus that of the source over the translate `s + 1`, the
terms of the cone being the biproducts `Kⁿ⁺¹ ⊞ Lⁿ`. -/
theorem sum_negOnePow_obj_X_mappingCone (f : K ⟶ L) (s : Finset ℤ) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj ((CochainComplex.mappingCone f).X n) =
      ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (L.X n) -
        ∑ n ∈ s.map (Equiv.addRight (1 : ℤ)).toEmbedding, ((n.negOnePow : ℤ)) • v.obj (K.X n) := by
  rw [Finset.sum_map, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  -- `mappingCone f` is `homotopyCofiber f` by definition, as in Mathlib's
  -- `CochainComplex.mappingCone.isZero_X_iff`, so the biproduct decomposition of the terms of the
  -- homotopy cofiber applies to it.
  have e : (CochainComplex.mappingCone f).X n ≅ K.X (n + 1) ⊞ L.X n :=
    homotopyCofiber.XIsoBiprod f n (n + 1) rfl
  rw [v.map_iso e, v.map_biprod]
  simp [Int.negOnePow_succ, smul_add, add_comm]

variable [HasZeroObject C]

/-- **A contractible complex has vanishing Euler characteristic.** If the identity of `K` is
null-homotopic and the terms of `K` vanish outside the finite set `s` of degrees, then the
alternating sum over `s` of the values of a biproduct-additive invariant on the terms of `K` is
zero. -/
theorem sum_negOnePow_obj_X_eq_zero_of_homotopy_id_zero (h : Homotopy (𝟙 K) 0) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → IsZero (K.X n)) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n) = 0 := by
  have := hasFiniteBiproducts_of_hasBinaryBiproducts (C := C)
  have key := v.map_iso (h.biproductEvenIsoBiproductOdd hs)
  rw [v.obj_biproduct, v.obj_biproduct, Finset.sum_coe_sort _ fun n => v.obj (K.X n),
    Finset.sum_coe_sort _ fun n => v.obj (K.X n)] at key
  have h₁ : ∑ n ∈ s.filter (fun n => n % 2 = 0), ((n.negOnePow : ℤ)) • v.obj (K.X n) =
      ∑ n ∈ s.filter (fun n => n % 2 = 0), v.obj (K.X n) :=
    Finset.sum_congr rfl fun n hn => by
      rw [Int.negOnePow_even n (Int.even_iff.2 (Finset.mem_filter.1 hn).2), Units.val_one,
        one_smul]
  have h₂ : ∑ n ∈ s.filter (fun n => ¬ n % 2 = 0), ((n.negOnePow : ℤ)) • v.obj (K.X n) =
      -∑ n ∈ s.filter (fun n => ¬ n % 2 = 0), v.obj (K.X n) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hodd : Odd n := Int.odd_iff.2 (by have := (Finset.mem_filter.1 hn).2; omega)
    rw [Int.negOnePow_odd n hodd, Units.val_neg, Units.val_one, neg_smul, one_smul]
  rw [← Finset.sum_filter_add_sum_filter_not s fun n => n % 2 = 0, h₁, h₂, key, add_neg_cancel]

/-- **Homotopy invariance of the Euler characteristic.** Homotopy equivalent complexes supported
on finite sets of degrees have the same Euler characteristic relative to every biproduct-additive
invariant. -/
theorem sum_negOnePow_obj_X_eq_of_homotopyEquiv (e : HomotopyEquiv K L) {s t : Finset ℤ}
    (hs : ∀ n, n ∉ s → IsZero (K.X n)) (ht : ∀ n, n ∉ t → IsZero (L.X n)) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n) =
      ∑ n ∈ t, ((n.negOnePow : ℤ)) • v.obj (L.X n) := by
  -- The cone of `e.hom` is supported on `u`, while `K` is supported on `u + 1`.
  set u : Finset ℤ := t ∪ s.map (Equiv.addRight (-1 : ℤ)).toEmbedding with hu
  have hK : ∀ n, n ∉ u.map (Equiv.addRight (1 : ℤ)).toEmbedding → IsZero (K.X n) := by
    intro n hn
    refine hs n fun hns => hn (Finset.mem_map_equiv.2 ?_)
    rw [hu, Finset.mem_union, Finset.mem_map_equiv]
    exact Or.inr (by simpa using hns)
  have hL : ∀ n, n ∉ u → IsZero (L.X n) := fun n hn =>
    ht n fun hnt => hn (Finset.mem_union_left _ hnt)
  have hcone : ∀ n, n ∉ u → IsZero ((CochainComplex.mappingCone e.hom).X n) := by
    intro n hn
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hK (n + 1) fun h => hn (by simpa using Finset.mem_map_equiv.1 h), hL n hn⟩
  obtain ⟨h⟩ := CochainComplex.mappingCone.nonempty_homotopy_id_zero_of_homotopyEquiv e
  have h0 := v.sum_negOnePow_obj_X_eq_zero_of_homotopy_id_zero h hcone
  rw [v.sum_negOnePow_obj_X_mappingCone, sub_eq_zero] at h0
  rw [v.sum_negOnePow_obj_X_eq_of_isZero K hs hK, v.sum_negOnePow_obj_X_eq_of_isZero L ht hL, h0]

end MappingCone

end SplitK0.AdditiveInvariant

namespace SplitK0

variable [EssentiallySmall.{w} C]

section CochainComplex

variable (K : CochainComplex C ℤ)

/-- The alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` in split `K₀` of the terms of a cochain complex
over a finite set `s` of degrees. The set of degrees is data: the value is the truncation of the
alternating sum to `s`, and `TauCeti.SplitK0.eulerChar_eq_eulerChar` shows that it stops depending
on `s` once `s` contains the support of a bounded complex. -/
noncomputable def eulerChar (s : Finset ℤ) : SplitK0 C :=
  ∑ n ∈ s, ((n.negOnePow : ℤ)) • of (K.X n)

@[simp] theorem eulerChar_empty : eulerChar K ∅ = 0 := Finset.sum_empty

@[simp] theorem eulerChar_insert {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    eulerChar K (insert n s) = ((n.negOnePow : ℤ)) • of (K.X n) + eulerChar K s :=
  Finset.sum_insert hn

/-- The Euler characteristic of a complex does not depend on the finite range of degrees over
which it is summed, as long as that range contains the support. -/
theorem eulerChar_eq_eulerChar_of_isZero {s t : Finset ℤ} (hs : ∀ n, n ∉ s → IsZero (K.X n))
    (ht : ∀ n, n ∉ t → IsZero (K.X n)) : eulerChar K s = eulerChar K t := by
  simpa [eulerChar] using (ofInvariant C).sum_negOnePow_obj_X_eq_of_isZero K hs ht

/-- The Euler characteristic of a bounded complex does not depend on the finite range of degrees
over which it is summed, as long as that range contains the bounding interval. -/
theorem eulerChar_eq_eulerChar (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] {s t : Finset ℤ}
    (hs : Finset.Icc a b ⊆ s) (ht : Finset.Icc a b ⊆ t) : eulerChar K s = eulerChar K t :=
  eulerChar_eq_eulerChar_of_isZero K (fun _ hn => K.isZero_X_of_notMem_Icc a b fun h => hn (hs h))
    fun _ hn => K.isZero_X_of_notMem_Icc a b fun h => hn (ht h)

/-- The Euler characteristic of the shift `K⟦1⟧` over `s` is minus the Euler characteristic of `K`
over the translate `s + 1`. -/
theorem eulerChar_shift (s : Finset ℤ) :
    eulerChar (K⟦(1 : ℤ)⟧) s = -eulerChar K (s.map (Equiv.addRight (1 : ℤ)).toEmbedding) := by
  simpa [eulerChar] using (ofInvariant C).sum_negOnePow_obj_X_shift K s

variable {K} {L : CochainComplex C ℤ}

/-- The Euler characteristic of a mapping cone is the Euler characteristic of the target minus that
of the source over the translated range: `χ(cone f) = χ(L) - χ(K)`. -/
theorem eulerChar_mappingCone (f : K ⟶ L) (s : Finset ℤ) :
    eulerChar (CochainComplex.mappingCone f) s =
      eulerChar L s - eulerChar K (s.map (Equiv.addRight (1 : ℤ)).toEmbedding) := by
  simpa [eulerChar] using (ofInvariant C).sum_negOnePow_obj_X_mappingCone f s

variable [HasZeroObject C]

/-- **A contractible complex has vanishing Euler characteristic**, over any finite set of degrees
containing its support. -/
theorem eulerChar_eq_zero_of_homotopy_id_zero_of_isZero (h : Homotopy (𝟙 K) 0) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → IsZero (K.X n)) : eulerChar K s = 0 := by
  simpa [eulerChar] using (ofInvariant C).sum_negOnePow_obj_X_eq_zero_of_homotopy_id_zero h hs

/-- **A contractible bounded complex has vanishing Euler characteristic.** -/
theorem eulerChar_eq_zero_of_homotopy_id_zero (h : Homotopy (𝟙 K) 0) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) : eulerChar K s = 0 :=
  eulerChar_eq_zero_of_homotopy_id_zero_of_isZero h
    fun _ hn => K.isZero_X_of_notMem_Icc a b fun h => hn (hs h)

/-- **Homotopy invariance of the Euler characteristic**, for complexes supported on finite sets of
degrees. -/
theorem eulerChar_eq_of_homotopyEquiv_of_isZero (e : HomotopyEquiv K L) {s t : Finset ℤ}
    (hs : ∀ n, n ∉ s → IsZero (K.X n)) (ht : ∀ n, n ∉ t → IsZero (L.X n)) :
    eulerChar K s = eulerChar L t := by
  simpa [eulerChar] using (ofInvariant C).sum_negOnePow_obj_X_eq_of_homotopyEquiv e hs ht

/-- **Homotopy invariance of the Euler characteristic of bounded complexes.** Homotopy equivalent
bounded complexes have the same Euler characteristic in split `K₀`, over any finite ranges of
degrees containing their respective bounding intervals. -/
theorem eulerChar_eq_of_homotopyEquiv (e : HomotopyEquiv K L) (a b a' b' : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] [L.IsStrictlyGE a'] [L.IsStrictlyLE b'] {s t : Finset ℤ}
    (hs : Finset.Icc a b ⊆ s) (ht : Finset.Icc a' b' ⊆ t) : eulerChar K s = eulerChar L t :=
  eulerChar_eq_of_homotopyEquiv_of_isZero e
    (fun _ hn => K.isZero_X_of_notMem_Icc a b fun h => hn (hs h))
    fun _ hn => L.isZero_X_of_notMem_Icc a' b' fun h => hn (ht h)

end CochainComplex

end SplitK0

end TauCeti
