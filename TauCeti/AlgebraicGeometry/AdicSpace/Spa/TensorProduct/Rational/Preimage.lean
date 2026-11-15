/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MorphismSpectral
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction

/-!
# Rational preimages and intersections in completed tensor adic spectra

Let `(B, B⁺)` and `(C, C⁺)` be Huber pairs with adic structure homomorphisms from a Huber ring `A`,
and write `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` for their completed tensor Huber pair with projection
maps `p_B : Spa (D, D⁺) → Spa (B, B⁺)` and `p_C : Spa (D, D⁺) → Spa (C, C⁺)`.

For rational presentations `U = R(T_B/s_B) ⊆ Spa (B, B⁺)` and `V = R(T_C/s_C) ⊆ Spa (C, C⁺)` with
open numerator ideals, this file shows that:

1. `p_B⁻¹(U) = R(inl(T_B)/inl(s_B))` and `p_C⁻¹(V) = R(inr(T_C)/inr(s_C))` are rational subsets of
   `Spa (D, D⁺)` with open numerator ideals;
2. `p_B⁻¹(U) ∩ p_C⁻¹(V)` is the rational subset presented over `inl(s_B) * inr(s_C)` by the product
   numerator set `insert (inl s_B) (inl T_B) * insert (inr s_C) (inr T_C)`, whose span in `D` is
   open.

## Main results

* `TauCeti.Huber.Pair.completedTensor.inl_spaComap_preimage_rationalSubset`,
  `TauCeti.Huber.Pair.completedTensor.inr_spaComap_preimage_rationalSubset`: explicit rational
  presentations of preimages under the completed tensor projections.
* `TauCeti.Huber.Pair.completedTensor.inl_spaComap_preimage_mem_spaRationalFamily`,
  `TauCeti.Huber.Pair.completedTensor.inr_spaComap_preimage_mem_spaRationalFamily`: preimages of
  rational subsets under the completed tensor projections lie in `spaRationalFamily`.
* `TauCeti.Huber.Pair.completedTensor.inter_preimage_rationalSubset`,
  `TauCeti.Huber.Pair.completedTensor.isOpen_span_inter_inl_inr`: rational presentation and open
  numerator ideal for `p_B⁻¹(U) ∩ p_C⁻¹(V)`.
* `TauCeti.Huber.Pair.completedTensorRationalEquiv_preimage`: combined rational preimage and
  intersection theorem for completed tensor spectra.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.30(5) and Lemma 7.46(3).
-/

public section

open scoped Pointwise

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

namespace Pair.completedTensor

open scoped Classical in
/-- If `T_B` generates an open ideal in `B`, its image under `CompletedTensor.inl` generates an open
ideal in `B ⊗̂_A C`. -/
theorem isOpen_span_image_inl {TB : Finset B} (hTB : IsOpen (Ideal.span (TB : Set B) : Set B)) :
    IsOpen (Ideal.span
      ((TB.image (CompletedTensor.inl A B C) : Finset (CompletedTensor A B C)) :
        Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)) := by
  rw [Finset.coe_image, ← Ideal.map_span]
  exact (CompletedTensor.isAdicHom_inl A B C).isOpen_map hTB

open scoped Classical in
/-- If `T_C` generates an open ideal in `C`, its image under `CompletedTensor.inr` generates an open
ideal in `B ⊗̂_A C`. -/
theorem isOpen_span_image_inr {TC : Finset C} (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)) :
    IsOpen (Ideal.span
      ((TC.image (CompletedTensor.inr A B C) : Finset (CompletedTensor A B C)) :
        Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)) := by
  rw [Finset.coe_image, ← Ideal.map_span]
  exact (CompletedTensor.isAdicHom_inr A B C).isOpen_map hTC

open scoped Classical in
/-- If `T_B · B` and `T_C · C` are open, the product numerator set
`insert (inl s_B) (inl T_B) * insert (inr s_C) (inr T_C)` generates an open ideal in `B ⊗̂_A C`. -/
theorem isOpen_span_inter_inl_inr {TB : Finset B} (sB : B) {TC : Finset C} (sC : C)
    (hTB : IsOpen (Ideal.span (TB : Set B) : Set B))
    (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)) :
    IsOpen (Ideal.span
      ((insert (CompletedTensor.inl A B C sB) (TB.image (CompletedTensor.inl A B C)) *
        insert (CompletedTensor.inr A B C sC) (TC.image (CompletedTensor.inr A B C)) :
          Finset (CompletedTensor A B C)) : Set (CompletedTensor A B C)) :
      Set (CompletedTensor A B C)) :=
  (IsHuberRing.nonempty_pairOfDefinition (A := CompletedTensor A B C)).some
    |>.isOpen_span_insert_mul_insert (isOpen_span_image_inl (A := A) (C := C) hTB)
      (isOpen_span_image_inr (A := A) (B := B) hTC)

section Pairs

variable [IsHuberRing B] [IsHuberRing C]

open scoped Classical in
/-- Preimage of a rational subset `R(T_B/s_B) ⊆ Spa (B, B⁺)` under the left projection of the
completed tensor adic spectrum. -/
theorem inl_spaComap_preimage_rationalSubset (SB : Pair B) (SC : Pair C) (TB : Finset B) (sB : B) :
    (inl A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SB.plus TB sB) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (TB.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C sB) := by
  simpa using (inl A SB SC).spaComap_preimage_rationalSubset TB sB

open scoped Classical in
/-- Preimage of a rational subset `R(T_C/s_C) ⊆ Spa (C, C⁺)` under the right projection of the
completed tensor adic spectrum. -/
theorem inr_spaComap_preimage_rationalSubset (SB : Pair B) (SC : Pair C) (TC : Finset C) (sC : C) :
    (inr A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SC.plus TC sC) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (TC.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C sC) := by
  simpa using (inr A SB SC).spaComap_preimage_rationalSubset TC sC

/-- Preimage under `(inl A SB SC).spaComap` preserves membership in `spaRationalFamily`. -/
theorem inl_spaComap_preimage_mem_spaRationalFamily (SB : Pair B) (SC : Pair C)
    {U : Set (spa SB.plus)} (hU : U ∈ spaRationalFamily SB.plus) :
    (inl A SB SC).spaComap ⁻¹' U ∈ spaRationalFamily (SB.completedTensor A SC).plus :=
  (inl A SB SC).spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ by simpa using (CompletedTensor.isAdicHom_inl A B C).isOpen_map hJ) hU

/-- Preimage under `(inr A SB SC).spaComap` preserves membership in `spaRationalFamily`. -/
theorem inr_spaComap_preimage_mem_spaRationalFamily (SB : Pair B) (SC : Pair C)
    {V : Set (spa SC.plus)} (hV : V ∈ spaRationalFamily SC.plus) :
    (inr A SB SC).spaComap ⁻¹' V ∈ spaRationalFamily (SB.completedTensor A SC).plus :=
  (inr A SB SC).spaComap_preimage_mem_spaRationalFamily
    (fun _ hJ ↦ by simpa using (CompletedTensor.isAdicHom_inr A B C).isOpen_map hJ) hV

open scoped Classical in
/-- Intersection of the preimages of `R(T_B/s_B)` and `R(T_C/s_C)` in the completed tensor adic
spectrum, presented over the product denominator `inl(s_B) * inr(s_C)`. -/
theorem inter_preimage_rationalSubset (SB : Pair B) (SC : Pair C)
    (TB : Finset B) (sB : B) (TC : Finset C) (sC : C) :
    ((inl A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((inr A SB SC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (insert (CompletedTensor.inl A B C sB) (TB.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C sC) (TC.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C sB * CompletedTensor.inr A B C sC) := by
  rw [inl_spaComap_preimage_rationalSubset, inr_spaComap_preimage_rationalSubset,
    ← Set.preimage_inter, rationalSubset_inter]

end Pairs

end Pair.completedTensor

open scoped Classical in
/-- **Rational preimages and intersections in the completed tensor adic spectrum**
(Wedhorn Lemma 7.46(3) and Remark 7.30(5)). For rational presentations `(T_B, s_B)` of `U` in
`Spa (B, B⁺)` and `(T_C, s_C)` of `V` in `Spa (C, C⁺)` with open numerator ideals, the preimages
`p_B⁻¹(U)` and `p_C⁻¹(V)` under the completed tensor projections are rational subsets presented by
`(inl(T_B), inl(s_B))` and `(inr(T_C), inr(s_C))`, and their intersection is the rational subset
presented by `insert (inl s_B) (inl T_B) * insert (inr s_C) (inr T_C)` over `inl(s_B) * inr(s_C)`
with open numerator ideal. -/
theorem Pair.completedTensorRationalEquiv_preimage [IsHuberRing B] [IsHuberRing C]
    (SB : Pair B) (SC : Pair C)
    {TB : Finset B} (sB : B) {TC : Finset C} (sC : C)
    (hTB : IsOpen (Ideal.span (TB : Set B) : Set B))
    (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)) :
    ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (TB.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C sB) ∧
      IsOpen (Ideal.span
        ((TB.image (CompletedTensor.inl A B C) : Finset (CompletedTensor A B C)) :
          Set (CompletedTensor A B C)) : Set (CompletedTensor A B C))) ∧
    ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (TC.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C sC) ∧
      IsOpen (Ideal.span
        ((TC.image (CompletedTensor.inr A B C) : Finset (CompletedTensor A B C)) :
          Set (CompletedTensor A B C)) : Set (CompletedTensor A B C))) ∧
    (((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
        ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)) =
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus
        (insert (CompletedTensor.inl A B C sB) (TB.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C sC) (TC.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C sB * CompletedTensor.inr A B C sC) ∧
      IsOpen (Ideal.span
        ((insert (CompletedTensor.inl A B C sB) (TB.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C sC) (TC.image (CompletedTensor.inr A B C)) :
            Finset (CompletedTensor A B C)) : Set (CompletedTensor A B C)) :
        Set (CompletedTensor A B C))) :=
  ⟨⟨Pair.completedTensor.inl_spaComap_preimage_rationalSubset SB SC TB sB,
      Pair.completedTensor.isOpen_span_image_inl hTB⟩,
    ⟨Pair.completedTensor.inr_spaComap_preimage_rationalSubset SB SC TC sC,
      Pair.completedTensor.isOpen_span_image_inr hTC⟩,
    ⟨Pair.completedTensor.inter_preimage_rationalSubset SB SC TB sB TC sC,
      Pair.completedTensor.isOpen_span_inter_inl_inr sB sC hTB hTC⟩⟩

end TauCeti.Huber

end
