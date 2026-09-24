/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contractible
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The Euler characteristic of a bounded complex in split `K₀`, and the bounded homotopy category

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
and the triangulated `K₀` of its bounded homotopy category, proved in the last section. The
Euler characteristic of a representing complex is well defined on the objects of the homotopy
category by homotopy invariance, and additive on distinguished triangles by the mapping-cone
formula, so it induces a homomorphism out of triangulated `K₀`. It is inverse to the map placing an
object in degree zero: splitting off the top term of a bounded complex is a degreewise split short
exact sequence, hence a distinguished triangle, and induction on the length of the complex shows
that the class of a bounded complex is the alternating sum of the classes of its terms.

## Main definitions

* `TauCeti.SplitK0.eulerChar`: the alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` in split `K₀` of the
  terms of a cochain complex over a finite set of degrees.
* `TauCeti.SplitK0.boundedHomotopyEquiv`: the isomorphism between split `K₀` of an additive
  category and triangulated `K₀` of its bounded homotopy category.

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
* `TauCeti.TriangulatedK0.of_bounded_quotient_obj`: in triangulated `K₀` of the bounded homotopy
  category, the class of a bounded complex is the alternating sum of the classes of its terms
  placed in degree zero; `TauCeti.TriangulatedK0.of_boundedSingleFunctor_obj` computes the class
  of an object placed in degree `n` as `(-1)ⁿ` times its class in degree zero.
* `TauCeti.SplitK0.boundedHomotopyEquiv_symm_of_quotient_obj`: the inverse comparison is the Euler
  characteristic.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15, for the comparison of `K₀` of an additive category with `K₀` of its bounded
  homotopy category through the alternating sum of the terms.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
  HomologicalComplex

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

/-- The Euler characteristic of a mapping cone, for complexes supported on finite sets of degrees:
`χ(cone f) = χ(L) - χ(K)`, each summed over a finite set of degrees containing its support. -/
theorem eulerChar_mappingCone_of_isZero (f : K ⟶ L) {s t u : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero (K.X n)) (ht : ∀ n ∉ t, IsZero (L.X n))
    (hu : ∀ n ∉ u, IsZero ((CochainComplex.mappingCone f).X n)) :
    eulerChar (CochainComplex.mappingCone f) u = eulerChar L t - eulerChar K s := by
  -- Sum over a common range `v`, containing the supports of the cone and of `L`, and whose
  -- translate `v + 1` contains the support of `K`.
  set v : Finset ℤ := u ∪ t ∪ s.map (Equiv.addRight (-1 : ℤ)).toEmbedding with hv
  have hK : ∀ n, n ∉ v.map (Equiv.addRight (1 : ℤ)).toEmbedding → IsZero (K.X n) := fun n hn ↦
    hs n fun hns ↦ hn (Finset.mem_map_equiv.2 (by simp [hv, hns]))
  have hL : ∀ n ∉ v, IsZero (L.X n) := fun n hn ↦ ht n fun h ↦ hn (by simp [hv, h])
  have hcone : ∀ n ∉ v, IsZero ((CochainComplex.mappingCone f).X n) := fun n hn ↦
    hu n fun h ↦ hn (by simp [hv, h])
  rw [eulerChar_eq_eulerChar_of_isZero _ hu hcone, eulerChar_mappingCone,
    eulerChar_eq_eulerChar_of_isZero _ hL ht, eulerChar_eq_eulerChar_of_isZero _ hK hs]

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

section BoundedHomotopy

/-! ### Split `K₀` and the bounded homotopy category -/

variable [HasZeroObject C] [EssentiallySmall.{w} C]

namespace SplitK0

omit [HasBinaryBiproducts C] [HasZeroObject C] [EssentiallySmall.{w} C] in
private lemma exists_finset_isZero_X (K : HomotopyCategory.Bounded C) :
    ∃ s : Finset ℤ, ∀ n ∉ s, IsZero (K.obj.as.X n) :=
  (CochainComplex.bounded_iff_exists_finset_isZero_X _ K.obj.as).1
    ((HomotopyCategory.bounded_quotient_obj_iff _).1 K.property)

variable (C) in
/-- The Euler characteristic of the representing bounded complex, as a triangle-additive invariant
on the bounded homotopy category. Homotopy invariance makes it constant on isomorphism classes,
and the mapping-cone formula makes it additive on distinguished triangles. -/
private noncomputable def boundedHomotopyEulerChar :
    TriangulatedK0.AdditiveInvariant (HomotopyCategory.Bounded C) (SplitK0 C) where
  obj K := eulerChar K.obj.as (exists_finset_isZero_X K).choose
  map_iso K L e := eulerChar_eq_of_homotopyEquiv_of_isZero
    (_root_.HomotopyCategory.homotopyEquivOfIso ((HomotopyCategory.Bounded.ι C).mapIso e))
    (exists_finset_isZero_X K).choose_spec (exists_finset_isZero_X L).choose_spec
  map_distTriang T hT := by
    obtain ⟨s₁, hs₁⟩ := exists_finset_isZero_X T.obj₁
    obtain ⟨s₂, hs₂⟩ := exists_finset_isZero_X T.obj₂
    obtain ⟨f, hf⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (X := T.obj₁.obj.as) (Y := T.obj₂.obj.as) T.mor₁.hom
    -- The third vertex is isomorphic in the homotopy category to the standard mapping cone of a
    -- representative of the first morphism.
    let e := Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
      ((HomotopyCategory.Bounded.ι C).map_distinguished _ hT)
      (_root_.HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (hf.symm.trans (Category.id_comp _).symm)))
    have hcone : ∀ n ∉ s₂ ∪ s₁.map (Equiv.addRight (-1 : ℤ)).toEmbedding,
        IsZero ((CochainComplex.mappingCone f).X n) := by
      intro n hn
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨hs₁ _ fun h ↦ hn (by simp [h]), hs₂ _ fun h ↦ hn (by simp [h])⟩
    rw [eulerChar_eq_of_homotopyEquiv_of_isZero
      (_root_.HomotopyCategory.homotopyEquivOfIso (C := T.obj₃.obj.as)
        (D := CochainComplex.mappingCone f) e)
      (exists_finset_isZero_X T.obj₃).choose_spec hcone,
      eulerChar_mappingCone_of_isZero f hs₁ hs₂ hcone,
      eulerChar_eq_eulerChar_of_isZero _ (exists_finset_isZero_X T.obj₁).choose_spec hs₁,
      eulerChar_eq_eulerChar_of_isZero _ (exists_finset_isZero_X T.obj₂).choose_spec hs₂]
    abel

private lemma boundedHomotopyEulerChar_obj (K : HomotopyCategory.Bounded C) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero (K.obj.as.X n)) :
    (boundedHomotopyEulerChar C).obj K = eulerChar K.obj.as s :=
  eulerChar_eq_eulerChar_of_isZero _ (exists_finset_isZero_X K).choose_spec hs

private lemma boundedHomotopyEulerChar_obj_quotient (K : CochainComplex.Bounded C)
    {s : Finset ℤ} (hs : ∀ n ∉ s, IsZero (K.obj.X n)) :
    (boundedHomotopyEulerChar C).obj ((HomotopyCategory.Bounded.quotient C).obj K) =
      eulerChar K.obj s := by
  have h := boundedHomotopyEulerChar_obj ((HomotopyCategory.Bounded.quotient C).obj K) (s := s)
    (by rw [HomotopyCategory.Bounded.quotient_obj_obj]; exact hs)
  rwa [HomotopyCategory.Bounded.quotient_obj_obj] at h

variable (C) in
/-- The comparison map sending the class of an object to the class of that object placed in
degree zero. -/
private noncomputable def toBoundedHomotopy :
    SplitK0 C →+ TriangulatedK0 (HomotopyCategory.Bounded C) :=
  (TriangulatedK0.fromSplit _).comp (map (HomotopyCategory.Bounded.singleFunctor C 0))

private lemma toBoundedHomotopy_of (X : C) :
    toBoundedHomotopy C (of X) =
      TriangulatedK0.of ((HomotopyCategory.Bounded.singleFunctor C 0).obj X) := by
  simp [toBoundedHomotopy]

end SplitK0

namespace TriangulatedK0

private lemma of_bounded_eq_of_obj_eq {K L : HomotopyCategory.Bounded C} (h : K.obj = L.obj) :
    (of K : TriangulatedK0 (HomotopyCategory.Bounded C)) = of L :=
  of_congr ((HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso (eqToIso h))

/-- The object `X` placed in degree `n` in the bounded homotopy category is the class of the
single complex on `X`. -/
private lemma of_boundedSingleFunctor_obj_eq_of_quotient_obj (n : ℤ) (X : C)
    (h : CochainComplex.bounded C ((single C (.up ℤ) n).obj X)) :
    (of ((HomotopyCategory.Bounded.singleFunctor C n).obj X) :
      TriangulatedK0 (HomotopyCategory.Bounded C)) =
      of ((HomotopyCategory.Bounded.quotient C).obj ⟨_, h⟩) :=
  of_congr ((HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso
    ((HomotopyCategory.Bounded.singleFunctorCompιIso C n).app X ≪≫ eqToIso (by
      rw [ObjectProperty.ι_obj, HomotopyCategory.Bounded.quotient_obj_obj]
      exact (_root_.HomotopyCategory.quotient_obj_singleFunctors_obj C n X).symm)))

/-- In triangulated `K₀` of the bounded homotopy category, an object placed in degree `n` has the
class of the same object placed in degree zero, multiplied by the sign `(-1)ⁿ`. -/
theorem of_boundedSingleFunctor_obj (n : ℤ) (X : C) :
    (of ((HomotopyCategory.Bounded.singleFunctor C n).obj X) :
      TriangulatedK0 (HomotopyCategory.Bounded C)) =
      (n.negOnePow : ℤ) • of ((HomotopyCategory.Bounded.singleFunctor C 0).obj X) := by
  have h := of_congr (((HomotopyCategory.Bounded.singleFunctors C).shiftIso n 0 n
    (add_zero n)).app X)
  rw [Functor.comp_obj, of_shift] at h
  rw [← h, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

/-- The induction behind `TauCeti.TriangulatedK0.of_bounded_quotient_obj`, on the upper bound of
a complex: splitting off the top term expresses a complex as an extension of a shorter complex by
a complex concentrated in a single degree. -/
private lemma of_bounded_quotient_obj_aux (a : ℤ) : ∀ b, a - 1 ≤ b →
    ∀ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b)
      (hK : CochainComplex.bounded C K),
      (of ((HomotopyCategory.Bounded.quotient C).obj ⟨K, hK⟩) :
        TriangulatedK0 (HomotopyCategory.Bounded C)) =
        SplitK0.toBoundedHomotopy C (SplitK0.eulerChar K (Finset.Icc a b)) := by
  intro b hb
  induction b, hb using Int.leInduction with
  | base =>
    intro K _ _ hK
    have hK0 : IsZero K := (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i ↦
      (K.isZero_X_of_notMem_Icc a (a - 1) (n := i) (by simp)).eq_of_src _ _)
    rw [Finset.Icc_eq_empty (by omega), SplitK0.eulerChar_empty, map_zero]
    refine of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
      (HomotopyCategory.Bounded.ι C) _ ?_)
    rw [ObjectProperty.ι_obj, HomotopyCategory.Bounded.quotient_obj_obj]
    exact Functor.map_isZero _ hK0
  | succ b hb ih =>
    intro K _ _ hK
    let X₃ := K.stupidTrunc (ComplexShape.embeddingUpIntLE b)
    have hb₁ : CochainComplex.bounded C ((single C (.up ℤ) (b + 1)).obj (K.X (b + 1))) :=
      (CochainComplex.bounded_iff _ _).2 ⟨b + 1, b + 1, inferInstance, inferInstance⟩
    have hb₃ : CochainComplex.bounded C X₃ :=
      (CochainComplex.bounded_iff _ _).2 ⟨a, b, inferInstance, inferInstance⟩
    let T := CochainComplex.trianglehOfDegreewiseSplit _ (K.topShortComplexSplitting b)
    have h₁ : HomotopyCategory.bounded C T.obj₁ :=
      (HomotopyCategory.bounded_quotient_obj_iff _).2 (by simpa using hb₁)
    have h₂ : HomotopyCategory.bounded C T.obj₂ :=
      (HomotopyCategory.bounded_quotient_obj_iff _).2 (by simpa using hK)
    have h₃ : HomotopyCategory.bounded C T.obj₃ :=
      (HomotopyCategory.bounded_quotient_obj_iff _).2 (by simpa using hb₃)
    have hT := of_fullSubcategory_distTriang (HomotopyCategory.bounded C)
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _) h₁ h₂ h₃
    -- The three vertices of the splitting triangle are the bounded homotopy classes of the top
    -- term in degree `b + 1`, of `K`, and of its truncation `X₃`.
    rw [of_bounded_eq_of_obj_eq (K := ⟨T.obj₂, h₂⟩)
        (L := (HomotopyCategory.Bounded.quotient C).obj ⟨K, hK⟩)
        (by simp [T, HomotopyCategory.Bounded.quotient_obj_obj]),
      of_bounded_eq_of_obj_eq (K := ⟨T.obj₁, h₁⟩)
        (L := (HomotopyCategory.Bounded.quotient C).obj ⟨_, hb₁⟩)
        (by simp [T, HomotopyCategory.Bounded.quotient_obj_obj]),
      of_bounded_eq_of_obj_eq (K := ⟨T.obj₃, h₃⟩)
        (L := (HomotopyCategory.Bounded.quotient C).obj ⟨X₃, hb₃⟩)
        (by simp [T, X₃, HomotopyCategory.Bounded.quotient_obj_obj]),
      ← of_boundedSingleFunctor_obj_eq_of_quotient_obj] at hT
    have hX₃ : SplitK0.eulerChar X₃ (Finset.Icc a b) = SplitK0.eulerChar K (Finset.Icc a b) :=
      Finset.sum_congr rfl fun n hn ↦ by
        have := K.isIso_πStupidTruncLE_f b (Finset.mem_Icc.1 hn).2
        rw [SplitK0.of_congr (asIso ((K.πStupidTruncLE b).f n))]
    have hIcc : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hT, of_boundedSingleFunctor_obj, ← SplitK0.toBoundedHomotopy_of, ← map_zsmul,
      ih X₃ inferInstance inferInstance hb₃, hX₃, hIcc, SplitK0.eulerChar_insert K (by simp),
      map_add]

/-- **The class of a bounded complex** in triangulated `K₀` of the bounded homotopy category is
the alternating sum of the classes of its terms, each placed in degree zero. The sum runs over any
finite set of degrees outside which the complex vanishes. -/
theorem of_bounded_quotient_obj (K : CochainComplex.Bounded C) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero (K.obj.X n)) :
    (of ((HomotopyCategory.Bounded.quotient C).obj K) :
      TriangulatedK0 (HomotopyCategory.Bounded C)) =
      ∑ n ∈ s, (n.negOnePow : ℤ) • of ((HomotopyCategory.Bounded.singleFunctor C 0).obj
        (K.obj.X n)) := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ _).1 K.property
  have hb' : K.obj.IsStrictlyLE (max b (a - 1)) := K.obj.isStrictlyLE_of_le b _ (le_max_left _ _)
  rw [of_bounded_quotient_obj_aux a _ (le_max_right _ _) K.obj ha hb' K.property,
    SplitK0.eulerChar_eq_eulerChar_of_isZero _
      (fun _ hn ↦ K.obj.isZero_X_of_notMem_Icc a (max b (a - 1)) hn) hs]
  simp [SplitK0.eulerChar, SplitK0.toBoundedHomotopy_of]

end TriangulatedK0

namespace SplitK0

variable (C) in
/-- **Split `K₀` of an additive category is triangulated `K₀` of its bounded homotopy category.**
The class of an object goes to the class of that object placed in degree zero, and in the inverse
direction the class of a bounded complex goes to its Euler characteristic, the alternating sum of
the classes of its terms. -/
noncomputable def boundedHomotopyEquiv :
    SplitK0 C ≃+ TriangulatedK0 (HomotopyCategory.Bounded C) :=
  AddMonoidHom.toAddEquiv (toBoundedHomotopy C)
    (TriangulatedK0.lift (boundedHomotopyEulerChar C))
    (hom_ext fun X ↦ by
      have h : CochainComplex.bounded C ((single C (.up ℤ) 0).obj X) :=
        (CochainComplex.bounded_iff _ _).2 ⟨0, 0, inferInstance, inferInstance⟩
      rw [AddMonoidHom.comp_apply, toBoundedHomotopy_of,
        TriangulatedK0.of_boundedSingleFunctor_obj_eq_of_quotient_obj 0 X h,
        TriangulatedK0.lift_of, boundedHomotopyEulerChar_obj_quotient (s := {0}) _
          fun n hn ↦ isZero_single_obj_X (.up ℤ) _ _ _ (by simpa using hn)]
      simp [eulerChar])
    (TriangulatedK0.hom_ext fun K ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.Bounded.quotient_obj_surjective K
      obtain ⟨s, hs⟩ := (CochainComplex.bounded_iff_exists_finset_isZero_X _ K.obj).1 K.property
      rw [AddMonoidHom.comp_apply, TriangulatedK0.lift_of,
        boundedHomotopyEulerChar_obj_quotient _ hs, AddMonoidHom.id_apply,
        TriangulatedK0.of_bounded_quotient_obj K hs]
      simp [eulerChar, toBoundedHomotopy_of])

/-- `TauCeti.SplitK0.boundedHomotopyEquiv` sends the class of an object to the class of that object
placed in degree zero. -/
@[simp]
lemma boundedHomotopyEquiv_of (X : C) :
    boundedHomotopyEquiv C (of X) =
      TriangulatedK0.of ((HomotopyCategory.Bounded.singleFunctor C 0).obj X) :=
  toBoundedHomotopy_of X

/-- The inverse of `TauCeti.SplitK0.boundedHomotopyEquiv` sends the class of a bounded complex to
its Euler characteristic, summed over any finite set of degrees outside which it vanishes. -/
theorem boundedHomotopyEquiv_symm_of_quotient_obj (K : CochainComplex.Bounded C) {s : Finset ℤ}
    (hs : ∀ n ∉ s, IsZero (K.obj.X n)) :
    (boundedHomotopyEquiv C).symm
        (TriangulatedK0.of ((HomotopyCategory.Bounded.quotient C).obj K)) =
      eulerChar K.obj s := by
  rw [boundedHomotopyEquiv, AddMonoidHom.toAddEquiv_symm_apply, TriangulatedK0.lift_of,
    boundedHomotopyEulerChar_obj_quotient _ hs]

/-- The inverse of `TauCeti.SplitK0.boundedHomotopyEquiv` sends the class of an object placed in
degree `n` to `(-1)ⁿ` times its class. -/
@[simp]
theorem boundedHomotopyEquiv_symm_of_singleFunctor_obj (n : ℤ) (X : C) :
    (boundedHomotopyEquiv C).symm
        (TriangulatedK0.of ((HomotopyCategory.Bounded.singleFunctor C n).obj X)) =
      (n.negOnePow : ℤ) • of X := by
  rw [TriangulatedK0.of_boundedSingleFunctor_obj, map_zsmul, ← boundedHomotopyEquiv_of,
    AddEquiv.symm_apply_apply]

end SplitK0

end BoundedHomotopy

end TauCeti
