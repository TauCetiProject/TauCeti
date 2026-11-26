/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.TensorProduct.Pair
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MorphismSpectral

/-!
# Rational preimages on adic spectra of completed tensor products

Let `(B, B⁺)` and `(C, C⁺)` be Huber pairs over `A`, `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` their
completed tensor product, and `p_B`, `p_C` the maps on `Spa` induced by `inl` and `inr`. For
rational subsets `R(T/s) ⊆ Spa(B, B⁺)` and `R(T'/s') ⊆ Spa(C, C⁺)`, this file computes the
preimages `p_B⁻¹(R(T/s))`, `p_C⁻¹(R(T'/s'))`, and their intersection
`p_B⁻¹(R(T/s)) ∩ p_C⁻¹(R(T'/s'))` as rational subsets of `Spa(D, D⁺)` and shows membership in
`spaRationalFamily`.

## Main results

* `TauCeti.Huber.Pair.completedTensor.inl_spaComap_preimage_rationalSubset`,
  `TauCeti.Huber.Pair.completedTensor.inr_spaComap_preimage_rationalSubset`: preimages of rational
  subsets under `inl.spaComap` and `inr.spaComap`.
* `TauCeti.Huber.Pair.completedTensor.inl_preimage_inter_inr_preimage_rationalSubset` and
  `TauCeti.Huber.Pair.completedTensor.inl_preimage_inter_inr_preimage_mem_spaRationalFamily`:
  rational intersection formula and membership in `spaRationalFamily` on
  `Spa((B, B⁺) ⊗̂_A (C, C⁺))`.
* `TauCeti.Huber.Pair.completedTensor.inl_spaComap_preimage_mem_spaRationalFamily`,
  `TauCeti.Huber.Pair.completedTensor.inr_spaComap_preimage_mem_spaRationalFamily`: preimages of
  `spaRationalFamily` members stay in `spaRationalFamily`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §1, Lemma 1.5(ii) and §3, Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.5, Lemma 7.46(3).
-/

public section

namespace TauCeti.Huber.Pair

open CompletedTensor ValuationSpectrum
open scoped Pointwise

section Preimage

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] (UB : Pair B) (UC : Pair C)

open Classical in
/-- Preimage of a rational subset `R(T/s) ⊆ Spa(B, B⁺)` under the left projection from
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inl_spaComap_preimage_rationalSubset (T : Finset B) (s : B) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C s) := by
  simpa only [completedTensor.toRingHom_inl] using
    (completedTensor.inl A UB UC).spaComap_preimage_rationalSubset T s

open Classical in
/-- Preimage of a rational subset `R(T'/s') ⊆ Spa(C, C⁺)` under the right projection from
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inr_spaComap_preimage_rationalSubset (T' : Finset C) (s' : C) :
    (completedTensor.inr A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UC.plus T' s') =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (T'.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C s') := by
  simpa only [completedTensor.toRingHom_inr] using
    (completedTensor.inr A UB UC).spaComap_preimage_rationalSubset T' s'

open Classical in
/-- Intersection of the preimages of `R(T/s) ⊆ Spa(B, B⁺)` and `R(T'/s') ⊆ Spa(C, C⁺)` inside
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem completedTensor.inl_preimage_inter_inr_preimage_rationalSubset
    (T : Finset B) (s : B) (T' : Finset C) (s' : C) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus T' s') =
      Subtype.val ⁻¹' rationalSubset (UB.completedTensor A UC).plus
        (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') := by
  rw [completedTensor.inl_spaComap_preimage_rationalSubset,
    completedTensor.inr_spaComap_preimage_rationalSubset, ← Set.preimage_inter,
    rationalSubset_inter]

/-- Preimage of a member of `spaRationalFamily UB.plus` along `(inl A UB UC).spaComap` belongs to
`spaRationalFamily` of the completed tensor pair (Wedhorn, Lemma 7.46(3)). -/
theorem completedTensor.inl_spaComap_preimage_mem_spaRationalFamily
    {U : Set (spa UB.plus)} (hU : U ∈ spaRationalFamily UB.plus) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' U ∈
      spaRationalFamily (UB.completedTensor A UC).plus :=
  (completedTensor.inl A UB UC).spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ by
      simpa only [completedTensor.toRingHom_inl] using
        (CompletedTensor.isAdicHom_inl A B C).isOpen_map hJ) hU

/-- Preimage of a member of `spaRationalFamily UC.plus` along `(inr A UB UC).spaComap` belongs to
`spaRationalFamily` of the completed tensor pair (Wedhorn, Lemma 7.46(3)). -/
theorem completedTensor.inr_spaComap_preimage_mem_spaRationalFamily
    {V : Set (spa UC.plus)} (hV : V ∈ spaRationalFamily UC.plus) :
    (completedTensor.inr A UB UC).spaComap ⁻¹' V ∈
      spaRationalFamily (UB.completedTensor A UC).plus :=
  (completedTensor.inr A UB UC).spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ by
      simpa only [completedTensor.toRingHom_inr] using
        (CompletedTensor.isAdicHom_inr A B C).isOpen_map hJ) hV

/-- Intersection of the preimages of two rational subsets with open numerator ideals belongs to
`spaRationalFamily` of the completed tensor pair. -/
theorem completedTensor.inl_preimage_inter_inr_preimage_mem_spaRationalFamily
    {T : Finset B} (s : B) {T' : Finset C} (s' : C)
    (hT : IsOpen (Ideal.span (T : Set B) : Set B))
    (hT' : IsOpen (Ideal.span (T' : Set C) : Set C)) :
    (completedTensor.inl A UB UC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset UB.plus T s) ∩
        (completedTensor.inr A UB UC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset UC.plus T' s') ∈
      spaRationalFamily (UB.completedTensor A UC).plus :=
  inter_mem_spaRationalFamily
    (completedTensor.inl_spaComap_preimage_mem_spaRationalFamily UB UC
      (mem_spaRationalFamily_iff.mpr ⟨T, s, hT, rfl⟩))
    (completedTensor.inr_spaComap_preimage_mem_spaRationalFamily UB UC
      (mem_spaRationalFamily_iff.mpr ⟨T', s', hT', rfl⟩))

end Preimage

end TauCeti.Huber.Pair
