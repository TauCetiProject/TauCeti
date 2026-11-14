/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Preimages and intersections of rational subsets in completed tensor spectra

Let `A → B` and `A → C` be adic homomorphisms of topological rings with `B` and `C` Huber, let
`(B, B⁺)` and `(C, C⁺)` be Huber pairs, and let `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` be Huber's
completed tensor product with projections
`p_B = (Pair.completedTensor.inl A PB PC).spaComap : Spa(D, D⁺) → Spa(B, B⁺)` and
`p_C = (Pair.completedTensor.inr A PB PC).spaComap : Spa(D, D⁺) → Spa(C, C⁺)`.

For rational subsets `U = R(T_B / s_B) ⊆ Spa(B, B⁺)` and `V = R(T_C / s_C) ⊆ Spa(C, C⁺)`:

* `p_B ⁻¹' U = R(inl(T_B) / inl(s_B))` and `p_C ⁻¹' V = R(inr(T_C) / inr(s_C))`;
* when `T_B · B` and `T_C · C` are open ideals, `p_B ⁻¹' U`, `p_C ⁻¹' V`, and their intersection
  `p_B ⁻¹' U ∩ p_C ⁻¹' V` belong to `spaRationalFamily D⁺`, because `CompletedTensor.inl` and
  `CompletedTensor.inr` are adic;
* the intersection `p_B ⁻¹' U ∩ p_C ⁻¹' V` is the rational subset presented by the product
  numerators `({inl(s_B)} ∪ inl(T_B)) · ({inr(s_C)} ∪ inr(T_C))` over `inl(s_B) · inr(s_C)`.

## Main results

* `TauCeti.Huber.Pair.completedTensor.inl_spaComap_preimage_rationalSubset`,
  `TauCeti.Huber.Pair.completedTensor.inr_spaComap_preimage_rationalSubset`: rational presentations
  of `p_B ⁻¹' U` and `p_C ⁻¹' V`.
* `TauCeti.Huber.Pair.completedTensor.inl_spaComap_preimage_mem_spaRationalFamily`,
  `TauCeti.Huber.Pair.completedTensor.inr_spaComap_preimage_mem_spaRationalFamily`: membership of
  `p_B ⁻¹' U` and `p_C ⁻¹' V` in `spaRationalFamily D⁺`.
* `TauCeti.Huber.Pair.completedTensor.inl_inter_inr_spaComap_preimage_rationalSubset`: explicit
  product presentation of `p_B ⁻¹' U ∩ p_C ⁻¹' V`.
* `TauCeti.Huber.Pair.completedTensorRationalEquiv_preimage`: combined preimage, intersection, and
  rationality statement.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.30(5) and Lemma 7.46(3).
-/

public section

open scoped Pointwise

namespace TauCeti.Huber.Pair

open TauCeti.ValuationSpectrum

variable {A B C : Type*}
  [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

open scoped Classical in
/-- Preimage of `R(T_B / s_B) ⊆ Spa(B, B⁺)` along the left projection `p_B : Spa D → Spa B` is
`R(inl(T_B) / inl(s_B))`. -/
theorem completedTensor.inl_spaComap_preimage_rationalSubset (PB : Pair B) (PC : Pair C)
    (TB : Finset B) (sB : B) :
    (completedTensor.inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus TB sB) =
      Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus
        (TB.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C sB) := by
  simpa only [completedTensor.toRingHom_inl] using
    (completedTensor.inl A PB PC).spaComap_preimage_rationalSubset TB sB

open scoped Classical in
/-- Preimage of `R(T_C / s_C) ⊆ Spa(C, C⁺)` along the right projection `p_C : Spa D → Spa C` is
`R(inr(T_C) / inr(s_C))`. -/
theorem completedTensor.inr_spaComap_preimage_rationalSubset (PB : Pair B) (PC : Pair C)
    (TC : Finset C) (sC : C) :
    (completedTensor.inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus TC sC) =
      Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus
        (TC.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C sC) := by
  simpa only [completedTensor.toRingHom_inr] using
    (completedTensor.inr A PB PC).spaComap_preimage_rationalSubset TC sC

/-- Preimage under `p_B` carries members of `spaRationalFamily B⁺` to members of
`spaRationalFamily D⁺`, since `CompletedTensor.inl` is adic. -/
theorem completedTensor.inl_spaComap_preimage_mem_spaRationalFamily (PB : Pair B) (PC : Pair C)
    {U : Set (spa PB.plus)} (hU : U ∈ spaRationalFamily PB.plus) :
    (completedTensor.inl A PB PC).spaComap ⁻¹' U ∈
      spaRationalFamily (PB.completedTensor A PC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun _ hJ ↦ by
      rw [completedTensor.toRingHom_inl]
      exact (CompletedTensor.isAdicHom_inl A B C).isOpen_map hJ) hU

/-- Preimage under `p_C` carries members of `spaRationalFamily C⁺` to members of
`spaRationalFamily D⁺`, since `CompletedTensor.inr` is adic. -/
theorem completedTensor.inr_spaComap_preimage_mem_spaRationalFamily (PB : Pair B) (PC : Pair C)
    {V : Set (spa PC.plus)} (hV : V ∈ spaRationalFamily PC.plus) :
    (completedTensor.inr A PB PC).spaComap ⁻¹' V ∈
      spaRationalFamily (PB.completedTensor A PC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun _ hJ ↦ by
      rw [completedTensor.toRingHom_inr]
      exact (CompletedTensor.isAdicHom_inr A B C).isOpen_map hJ) hV

open scoped Classical in
/-- The intersection `p_B ⁻¹' R(T_B / s_B) ∩ p_C ⁻¹' R(T_C / s_C)` in `Spa(D, D⁺)` is the
rational subset presented by `({inl(s_B)} ∪ inl(T_B)) · ({inr(s_C)} ∪ inr(T_C))` over
`inl(s_B) · inr(s_C)`. -/
theorem completedTensor.inl_inter_inr_spaComap_preimage_rationalSubset (PB : Pair B) (PC : Pair C)
    (TB : Finset B) (sB : B) (TC : Finset C) (sC : C) :
    ((completedTensor.inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)) ∩
        ((completedTensor.inr A PB PC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset PC.plus TC sC)) =
      Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus
        (insert (CompletedTensor.inl A B C sB) (TB.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C sC) (TC.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C sB * CompletedTensor.inr A B C sC) := by
  rw [completedTensor.inl_spaComap_preimage_rationalSubset,
    completedTensor.inr_spaComap_preimage_rationalSubset, ← Set.preimage_inter,
    rationalSubset_inter]

open scoped Classical in
/-- **Preimages and intersection of rational subsets in a completed tensor product**
(Wedhorn Lemma 7.46(3) and Remark 7.30(5)): for rational subsets `U = R(T_B / s_B) ⊆ Spa(B, B⁺)`
and `V = R(T_C / s_C) ⊆ Spa(C, C⁺)` with open numerator ideals, `p_B ⁻¹' U`, `p_C ⁻¹' V`, and
`p_B ⁻¹' U ∩ p_C ⁻¹' V` belong to `spaRationalFamily` of `(B, B⁺) ⊗̂_A (C, C⁺)` and are presented
respectively by `inl(T_B) / inl(s_B)`, `inr(T_C) / inr(s_C)`, and
`({inl(s_B)} ∪ inl(T_B)) · ({inr(s_C)} ∪ inr(T_C)) / (inl(s_B) · inr(s_C))`. -/
theorem completedTensorRationalEquiv_preimage (PB : Pair B) (PC : Pair C)
    {TB : Finset B} (sB : B) (hTB : IsOpen (Ideal.span (TB : Set B) : Set B))
    {TC : Finset C} (sC : C) (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)) :
    let pB := (completedTensor.inl A PB PC).spaComap
    let pC := (completedTensor.inr A PB PC).spaComap
    let UB : Set (spa PB.plus) := Subtype.val ⁻¹' rationalSubset PB.plus TB sB
    let VC : Set (spa PC.plus) := Subtype.val ⁻¹' rationalSubset PC.plus TC sC
    let Dplus := (PB.completedTensor A PC).plus
    pB ⁻¹' UB = Subtype.val ⁻¹' rationalSubset Dplus
        (TB.image (CompletedTensor.inl A B C)) (CompletedTensor.inl A B C sB) ∧
      pB ⁻¹' UB ∈ spaRationalFamily Dplus ∧
      pC ⁻¹' VC = Subtype.val ⁻¹' rationalSubset Dplus
        (TC.image (CompletedTensor.inr A B C)) (CompletedTensor.inr A B C sC) ∧
      pC ⁻¹' VC ∈ spaRationalFamily Dplus ∧
      pB ⁻¹' UB ∩ pC ⁻¹' VC = Subtype.val ⁻¹' rationalSubset Dplus
        (insert (CompletedTensor.inl A B C sB) (TB.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C sC) (TC.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C sB * CompletedTensor.inr A B C sC) ∧
      pB ⁻¹' UB ∩ pC ⁻¹' VC ∈ spaRationalFamily Dplus := by
  have hUB : (Subtype.val ⁻¹' rationalSubset PB.plus TB sB : Set (spa PB.plus)) ∈
      spaRationalFamily PB.plus := mem_spaRationalFamily_iff.mpr ⟨TB, sB, hTB, rfl⟩
  have hVC : (Subtype.val ⁻¹' rationalSubset PC.plus TC sC : Set (spa PC.plus)) ∈
      spaRationalFamily PC.plus := mem_spaRationalFamily_iff.mpr ⟨TC, sC, hTC, rfl⟩
  exact ⟨completedTensor.inl_spaComap_preimage_rationalSubset PB PC TB sB,
    completedTensor.inl_spaComap_preimage_mem_spaRationalFamily PB PC hUB,
    completedTensor.inr_spaComap_preimage_rationalSubset PB PC TC sC,
    completedTensor.inr_spaComap_preimage_mem_spaRationalFamily PB PC hVC,
    completedTensor.inl_inter_inr_spaComap_preimage_rationalSubset PB PC TB sB TC sC,
    inter_mem_spaRationalFamily
      (completedTensor.inl_spaComap_preimage_mem_spaRationalFamily PB PC hUB)
      (completedTensor.inr_spaComap_preimage_mem_spaRationalFamily PB PC hVC)⟩

end TauCeti.Huber.Pair

end
