/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Homeomorph
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Map
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Plus
public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
public import TauCeti.RingTheory.Huber.TensorProduct.Rational

import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Completed tensor products of rational localisations over an unlocalized base

Let `(B, B⁺)` and `(C, C⁺)` be Huber pairs over an adic base ring `A`, and write
`(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` for their completed tensor product with canonical projections
`p_B : Spa(D, D⁺) → Spa(B, B⁺)` and `p_C : Spa(D, D⁺) → Spa(C, C⁺)`. Given rational subsets
`U = R_B(T_B / s_B) ⊆ Spa(B, B⁺)` and `V = R_C(T_C / s_C) ⊆ Spa(C, C⁺)`:

1. The intersection `p_B⁻¹(U) ∩ p_C⁻¹(V)` is presented by
   `T_D = ({inl(s_B)} ∪ inl(T_B)) · ({inr(s_C)} ∪ inr(T_C))` over `s_D = inl(s_B) · inr(s_C)`,
   and belongs to `spaRationalFamily D⁺` whenever `U` and `V` belong to `spaRationalFamily B⁺`
   and `spaRationalFamily C⁺`.
2. For *any* rational presentation `(T_D, s_D)` of `(D, D⁺)` cutting out `p_B⁻¹(U) ∩ p_C⁻¹(V)`,
   the completed tensor product of rational localisation pairs
   `(B⟨T_B/s_B⟩, B_U⁺) ⊗̂_A (C⟨T_C/s_C⟩, C_V⁺)` is canonically homeomorphically isomorphic as a
   Huber pair to `(D⟨T_D/s_D⟩, D_{U×V}⁺)` (`ratLocEquiv`, `map_ratLocEquiv_plus`), uniquely
   characterized among continuous ring homomorphisms by its action on `B` and `C`
   (`eq_ratLocEquiv_of_inl_of_inr`).
3. Consequently, `Spa((B⟨T_B/s_B⟩, B_U⁺) ⊗̂_A (C⟨T_C/s_C⟩, C_V⁺))` is canonically homeomorphic to
   `p_B⁻¹(U) ∩ p_C⁻¹(V) ⊆ Spa(D, D⁺)` compatibly with both projections (`ratLocSpaHomeomorph`,
   `spaComap_inl_ratLocSpaHomeomorph`, `spaComap_inr_ratLocSpaHomeomorph`), and preimage along this
   homeomorphism bijects rational subsets of `Spa(D, D⁺)` contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto
   the rational family of the completed tensor spectrum
   (`bijOn_preimage_ratLocSpaHomeomorph_spaRationalFamily`,
   `bijOn_preimage_ratLocSpaHomeomorph_canonical`).

Neither completeness, separatedness, Tateness, nor sheafiness is assumed on `A`, `B`, or `C`, and
all three rings live in independent universes. Base change over a localized base `A⟨T_A/s_A⟩` and
single-factor completed base change are developed in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.LocalizedBase`.

## Main definitions and results

* `Pair.completedTensor.spaComap_inl_preimage_inter_spaComap_inr_preimage_rationalSubset`:
  explicit presentation of `p_B⁻¹(R_B(T/s)) ∩ p_C⁻¹(R_C(T'/s'))`.
* `TauCeti.Huber.ratLocBaseAlgebra`: the `A`-algebra structure on `B⟨T_B/s_B⟩` via `A → B`.
* `TauCeti.Huber.Pair.completedTensor.ratLocEquiv` and
  `TauCeti.Huber.Pair.completedTensor.map_ratLocEquiv_plus`: Huber-pair isomorphism
  `(B⟨T_B/s_B⟩, B_U⁺) ⊗̂_A (C⟨T_C/s_C⟩, C_V⁺) ≃ (D⟨T_D/s_D⟩, D_{U×V}⁺)`.
* `TauCeti.Huber.Pair.completedTensor.ratLocSpaHomeomorph` and
  `TauCeti.Huber.Pair.completedTensor.bijOn_preimage_ratLocSpaHomeomorph_spaRationalFamily`:
  homeomorphism with `p_B⁻¹(U) ∩ p_C⁻¹(V)` and bijection on rational subsets.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2, Proposition
  1.2.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2.
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber

open PairOfDefinition ValuationSpectrum

universe u v w

/-! ### Preimages and intersections of rational subsets on completed tensor spectra -/

namespace Pair.completedTensor

section PreimageInter

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- Preimages of rational subsets of `Spa(B, B⁺)` along `(inl A PB PC).spaComap` are rational in
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem spaComap_inl_preimage_mem_spaRationalFamily {PB : Pair B} {PC : Pair C}
    {U : Set (spa PB.plus)} (hU : U ∈ spaRationalFamily PB.plus) :
    (inl A PB PC).spaComap ⁻¹' U ∈ spaRationalFamily (PB.completedTensor A PC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun _ hJ ↦ by rw [toRingHom_inl]; exact (CompletedTensor.isAdicHom_inl A B C).isOpen_map hJ)
    hU

/-- Preimages of rational subsets of `Spa(C, C⁺)` along `(inr A PB PC).spaComap` are rational in
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`. -/
theorem spaComap_inr_preimage_mem_spaRationalFamily {PB : Pair B} {PC : Pair C}
    {V : Set (spa PC.plus)} (hV : V ∈ spaRationalFamily PC.plus) :
    (inr A PB PC).spaComap ⁻¹' V ∈ spaRationalFamily (PB.completedTensor A PC).plus := by
  rw [Hom.spaComap_def]
  exact spaComap_preimage_mem_spaRationalFamily _ _ _ _ _
    (fun _ hJ ↦ by rw [toRingHom_inr]; exact (CompletedTensor.isAdicHom_inr A B C).isOpen_map hJ)
    hV

open scoped Pointwise in
/-- **Explicit rational presentation of `p_B⁻¹(R_B(T/s)) ∩ p_C⁻¹(R_C(T'/s'))` inside
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`.** -/
theorem spaComap_inl_preimage_inter_spaComap_inr_preimage_rationalSubset
    [inst : DecidableEq (CompletedTensor A B C)]
    (PB : Pair B) (PC : Pair C) (T : Finset B) (s : B) (T' : Finset C) (s' : C) :
    (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T s) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T' s') =
      Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus
        (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)))
        (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') := by
  have hdec : inst = Classical.decEq (CompletedTensor A B C) := Subsingleton.elim _ _
  subst hdec
  rw [Hom.spaComap_preimage_rationalSubset, Hom.spaComap_preimage_rationalSubset,
    toRingHom_inl, toRingHom_inr, ← Set.preimage_inter, rationalSubset_inter]

/-- **The intersection `p_B⁻¹(U) ∩ p_C⁻¹(V)` of preimages of two rational subsets is rational in
`Spa((B, B⁺) ⊗̂_A (C, C⁺))`.** -/
theorem spaComap_inl_preimage_inter_spaComap_inr_preimage_mem_spaRationalFamily
    {PB : Pair B} {PC : Pair C} {U : Set (spa PB.plus)} {V : Set (spa PC.plus)}
    (hU : U ∈ spaRationalFamily PB.plus) (hV : V ∈ spaRationalFamily PC.plus) :
    (inl A PB PC).spaComap ⁻¹' U ∩ (inr A PB PC).spaComap ⁻¹' V ∈
      spaRationalFamily (PB.completedTensor A PC).plus :=
  inter_mem_spaRationalFamily
    (spaComap_inl_preimage_mem_spaRationalFamily hU)
    (spaComap_inr_preimage_mem_spaRationalFamily hV)

end PreimageInter

end Pair.completedTensor

/-! ### Base-algebra structure on `ratLoc` -/

section RatLocBaseAlgebra

/-- For any pair of definition `P`, the structure map `A →+* A⟨T/s⟩` is adic. -/
instance isAdicHom_algebraMap_ratLoc {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower T s (Localization.Away s)) :
    IsAdicHom (algebraMap A (ratLoc P T s hden)) := by
  rw [algebraMap_ratLoc]
  exact P.isAdicHom_toCompletionLoc T s (Localization.Away s) hden

/-- The `A`-algebra structure on a completed rational localisation `B⟨T_B/s_B⟩` of an `A`-algebra
`B`, given by composing `A → B → B⟨T_B/s_B⟩`. -/
@[expose, instance_reducible]
noncomputable def ratLocBaseAlgebra (A : Type*) [CommRing A] {B : Type*} [CommRing B]
    [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
    (QB : PairOfDefinition B) (T_B : Finset B) (s_B : B)
    (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B)) :
    Algebra A (ratLoc QB T_B s_B hden_B) :=
  ((QB.toCompletionLoc T_B s_B (Localization.Away s_B) hden_B).comp (algebraMap A B)).toAlgebra

section

variable (A : Type*) [CommRing A] {B : Type*} [CommRing B]
  [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
  (QB : PairOfDefinition B) (T_B : Finset B) (s_B : B)
  (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))

attribute [local instance 900] ratLocBaseAlgebra

/-- The structure map of `ratLocBaseAlgebra` is
`(algebraMap B B⟨T_B/s_B⟩).comp (algebraMap A B)`. -/
theorem algebraMap_ratLocBaseAlgebra :
    algebraMap A (ratLoc QB T_B s_B hden_B) =
      (algebraMap B (ratLoc QB T_B s_B hden_B)).comp (algebraMap A B) := by
  rw [algebraMap_ratLoc QB]
  rfl

/-- When `A → B` is adic, `A → B⟨T_B/s_B⟩` is adic. -/
theorem isAdicHom_ratLocBaseAlgebra [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicHom (algebraMap A B)] :
    IsAdicHom (algebraMap A (ratLoc QB T_B s_B hden_B)) :=
  (isAdicHom_toCompletionLoc QB T_B s_B (Localization.Away s_B) hden_B).comp inferInstance

end

end RatLocBaseAlgebra

/-! ### Completed tensor products of rational localisations over an unlocalized base -/

namespace Pair.completedTensor

section UnlocalizedBase

private theorem comap_comap_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (v : Spv T) :
    comap f (comap g v) = comap (g.comp f) v :=
  (congr_fun (comap_comp f g) v).symm

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

attribute [local instance 900] ratLocBaseAlgebra isAdicHom_ratLocBaseAlgebra

variable (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
  (T_B : Finset B) (s_B : B) (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
  (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
  (T_C : Finset C) (s_C : C) (hden_C : QC.HasDenominatorPower T_C s_C (Localization.Away s_C))
  (QD : PairOfDefinition (CompletedTensor A B C))
  (hQD : QD.ringOfDefinition ≤ (PB.completedTensor A PC).plus)
  (T_D : Finset (CompletedTensor A B C)) (s_D : CompletedTensor A B C)
  (hden_D : QD.HasDenominatorPower T_D s_D (Localization.Away s_D))

private theorem mapsTo_inl_of_subset
    (hsub : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) ⊆
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B)) :
    Set.MapsTo (comap (CompletedTensor.inl A B C))
      (rationalSubset (PB.completedTensor A PC).plus T_D s_D)
      (rationalSubset PB.plus T_B s_B) := by
  rw [Hom.spaComap_def] at hsub
  have h := (mapsTo_spaComap_preimage_rationalSubset_iff (inl A PB PC).toRingHom
    (inl A PB PC).continuous_toRingHom (inl A PB PC).map_mem_plus T_B s_B T_D s_D).mp hsub
  rwa [toRingHom_inl] at h

private theorem mapsTo_inr_of_subset
    (hsub : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) ⊆
      (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    Set.MapsTo (comap (CompletedTensor.inr A B C))
      (rationalSubset (PB.completedTensor A PC).plus T_D s_D)
      (rationalSubset PC.plus T_C s_C) := by
  rw [Hom.spaComap_def] at hsub
  have h := (mapsTo_spaComap_preimage_rationalSubset_iff (inr A PB PC).toRingHom
    (inr A PB PC).continuous_toRingHom (inr A PB PC).map_mem_plus T_C s_C T_D s_D).mp hsub
  rwa [toRingHom_inr] at h

/-- **The forward morphism of Huber pairs
`(B⟨T_B/s_B⟩, B_U⁺) ⊗̂_A (C⟨T_C/s_C⟩, C_V⁺) → (D⟨T_D/s_D⟩, D_{U×V}⁺)`** whenever `R_D(T_D/s_D)`
cuts out `p_B⁻¹(R_B(T_B/s_B)) ∩ p_C⁻¹(R_C(T_C/s_C))`. -/
noncomputable def ratLocHom
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    Hom
      ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
        A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C))
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD T_D s_D
        (Localization.Away s_D) hden_D) :=
  lift
    (pairHomOfMapsToRationalSubset QB PB hQB T_B s_B (Localization.Away s_B) hden_B
      QD (PB.completedTensor A PC) hQD T_D s_D (Localization.Away s_D) hden_D
      (CompletedTensor.inl A B C) (CompletedTensor.continuous_inl A B C)
      (mapsTo_inl_of_subset PB T_B s_B PC T_D s_D (hUV.le.trans Set.inter_subset_left)))
    (pairHomOfMapsToRationalSubset QC PC hQC T_C s_C (Localization.Away s_C) hden_C
      QD (PB.completedTensor A PC) hQD T_D s_D (Localization.Away s_D) hden_D
      (CompletedTensor.inr A B C) (CompletedTensor.continuous_inr A B C)
      (mapsTo_inr_of_subset PB PC T_C s_C T_D s_D (hUV.le.trans Set.inter_subset_right)))
    (by
      rw [toRingHom_pairHomOfMapsToRationalSubset, toRingHom_pairHomOfMapsToRationalSubset,
        algebraMap_ratLocBaseAlgebra, algebraMap_ratLocBaseAlgebra,
        algebraMap_ratLoc QB, algebraMap_ratLoc QC,
        ← RingHom.comp_assoc, ringHomOfMapsToRationalSubset_comp_toCompletionLoc,
        ← RingHom.comp_assoc, ringHomOfMapsToRationalSubset_comp_toCompletionLoc,
        RingHom.comp_assoc, RingHom.comp_assoc, CompletedTensor.inl_comp_algebraMap])

private noncomputable def toTensorLocHom :
    Hom (PB.completedTensor A PC)
      ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
        A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)) :=
  lift
    ((inl A
      (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B)
      (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).comp
      (toCompletionLocHom QB PB hQB T_B s_B (Localization.Away s_B) hden_B))
    ((inr A
      (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B)
      (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).comp
      (toCompletionLocHom QC PC hQC T_C s_C (Localization.Away s_C) hden_C))
    (by
      rw [Hom.toRingHom_comp, Hom.toRingHom_comp, toRingHom_inl, toRingHom_inr,
        toRingHom_toCompletionLocHom, toRingHom_toCompletionLocHom,
        RingHom.comp_assoc, RingHom.comp_assoc,
        ← algebraMap_ratLoc QB, ← algebraMap_ratLoc QC,
        ← algebraMap_ratLocBaseAlgebra, ← algebraMap_ratLocBaseAlgebra,
        CompletedTensor.inl_comp_algebraMap])

private theorem comap_toTensorLocHom_mem_rationalSubset
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C))
    {w : Spv (CompletedTensor A (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C))}
    (hw : w ∈ spa
      ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
        A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) :
    comap (toTensorLocHom (A := A) QB PB hQB T_B s_B hden_B
        QC PC hQC T_C s_C hden_C).toRingHom w ∈
      rationalSubset (PB.completedTensor A PC).plus T_D s_D := by
  let PB' : Pair (ratLoc QB T_B s_B hden_B) :=
    rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B
  let PC' : Pair (ratLoc QC T_C s_C hden_C) :=
    rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C
  let j := toTensorLocHom (A := A) QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
  let w₀ : spa (PB'.completedTensor A PC').plus := ⟨w, hw⟩
  have hB : j.spaComap w₀ ∈ (inl A PB PC).spaComap ⁻¹'
      (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) := by
    have hcomp : j.comp (inl A PB PC) = (inl A PB' PC').comp
        (toCompletionLocHom QB PB hQB T_B s_B (Localization.Away s_B) hden_B) := by
      simp [j, toTensorLocHom, PB', PC']
    have hpt := congr_fun (Hom.spaComap_comp j (inl A PB PC)).symm w₀
    rw [hcomp, Hom.spaComap_comp] at hpt
    change (inl A PB PC).spaComap (j.spaComap w₀) ∈ Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B
    rw [← Function.comp_apply (f := (inl A PB PC).spaComap), hpt, Function.comp_apply,
      Set.mem_preimage, Hom.spaComap_val, toRingHom_toCompletionLocHom]
    let _ := QB.locUniformSpace T_B s_B (Localization.Away s_B) hden_B
    have _ := QB.isUniformAddGroup_locUniformSpace T_B s_B (Localization.Away s_B) hden_B
    have _ := QB.isTopologicalRing_locUniformSpace T_B s_B (Localization.Away s_B) hden_B
    simpa only [spaComapLoc_val] using
      spaComapLoc_mem_rationalSubset QB PB.plus T_B s_B (Localization.Away s_B) hden_B
        ⟨((inl A PB' PC').spaComap w₀).1, by
          simpa only [PB', rationalLocalizationPair_plus] using ((inl A PB' PC').spaComap w₀).2⟩
  have hC : j.spaComap w₀ ∈ (inr A PB PC).spaComap ⁻¹'
      (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C) := by
    have hcomp : j.comp (inr A PB PC) = (inr A PB' PC').comp
        (toCompletionLocHom QC PC hQC T_C s_C (Localization.Away s_C) hden_C) := by
      simp [j, toTensorLocHom, PB', PC']
    have hpt := congr_fun (Hom.spaComap_comp j (inr A PB PC)).symm w₀
    rw [hcomp, Hom.spaComap_comp] at hpt
    change (inr A PB PC).spaComap (j.spaComap w₀) ∈ Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C
    rw [← Function.comp_apply (f := (inr A PB PC).spaComap), hpt, Function.comp_apply,
      Set.mem_preimage, Hom.spaComap_val, toRingHom_toCompletionLocHom]
    let _ := QC.locUniformSpace T_C s_C (Localization.Away s_C) hden_C
    have _ := QC.isUniformAddGroup_locUniformSpace T_C s_C (Localization.Away s_C) hden_C
    have _ := QC.isTopologicalRing_locUniformSpace T_C s_C (Localization.Away s_C) hden_C
    simpa only [spaComapLoc_val] using
      spaComapLoc_mem_rationalSubset QC PC.plus T_C s_C (Localization.Away s_C) hden_C
        ⟨((inr A PB' PC').spaComap w₀).1, by
          simpa only [PC', rationalLocalizationPair_plus] using ((inr A PB' PC').spaComap w₀).2⟩
  have hmem : j.spaComap w₀ ∈
      Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :=
    hUV.symm ▸ ⟨hB, hC⟩
  simpa only [Set.mem_preimage, Hom.spaComap_val] using hmem

private theorem existsUnique_ofRatLoc
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    ∃! g : ratLoc QD T_D s_D hden_D →+*
        CompletedTensor A (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C),
      Continuous g ∧
        g.comp (QD.toCompletionLoc T_D s_D (Localization.Away s_D) hden_D) =
          (toTensorLocHom (A := A) QB PB hQB T_B s_B hden_B
            QC PC hQC T_C s_C hden_C).toRingHom :=
  existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    QD (PB.completedTensor A PC).plus T_D s_D (Localization.Away s_D) hden_D
    ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
      A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus
    ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
      A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C)
        hden_C)).isRingOfIntegralElements
    (toTensorLocHom (A := A) QB PB hQB T_B s_B hden_B
      QC PC hQC T_C s_C hden_C).continuous_toRingHom.continuousAt
    fun _ hw ↦ comap_toTensorLocHom_mem_rationalSubset QB PB hQB T_B s_B hden_B
      QC PC hQC T_C s_C hden_C T_D s_D hUV hw

/-- **The inverse morphism of Huber pairs
`(D⟨T_D/s_D⟩, D_{U×V}⁺) → (B⟨T_B/s_B⟩, B_U⁺) ⊗̂_A (C⟨T_C/s_C⟩, C_V⁺)`** constructed from
Wedhorn's Lemma 8.1. -/
noncomputable def ratLocSymmHom
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    Hom
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD T_D s_D
        (Localization.Away s_D) hden_D)
      ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
        A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)) where
  toRingHom := (existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD T_D s_D hden_D hUV).choose
  continuous_toRingHom := (existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD T_D s_D hden_D hUV).choose_spec.1.1
  map_mem_plus f hf := by
    let PE :=
      (rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
        A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)
    have hcont := (existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD T_D s_D hden_D hUV).choose_spec.1.1
    have hcomp := (existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD T_D s_D hden_D hUV).choose_spec.1.2
    refine PE.isRingOfIntegralElements.mem_of_forall_vle_one fun w hw ↦ ?_
    let _ := QD.locUniformSpace T_D s_D (Localization.Away s_D) hden_D
    have _ := QD.isUniformAddGroup_locUniformSpace T_D s_D (Localization.Away s_D) hden_D
    have _ := QD.isTopologicalRing_locUniformSpace T_D s_D (Localization.Away s_D) hden_D
    have hspa := comap_mem_spa_completedPlusSubring QD (PB.completedTensor A PC).plus T_D s_D
      (Localization.Away s_D) hden_D _ hcont ((ValuationSpectrum.mem_spa_iff _ _).mp hw).1
      (by
        rw [hcomp]
        exact comap_toTensorLocHom_mem_rationalSubset QB PB hQB T_B s_B hden_B
          QC PC hQC T_C s_C hden_C T_D s_D hUV hw)
    rw [rationalLocalizationPair_plus] at hf
    simpa only [comap_vle, map_one] using ((ValuationSpectrum.mem_spa_iff _ _).mp hspa).2 f hf

/-- `ratLocHom` followed by `ratLocSymmHom` is the identity on the completed tensor pair. -/
@[simp]
theorem ratLocSymmHom_comp_ratLocHom
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    (ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
        hUV).comp
      (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV) =
      Hom.id _ := by
  have hcomp := (existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD T_D s_D hden_D hUV).choose_spec.1.2
  refine hom_ext ?_ ?_
  · rw [Hom.id_comp]
    apply Hom.ext
    refine completion_locTopology_ringHom_ext_of_continuous QB T_B s_B (Localization.Away s_B)
      hden_B _ _
      (((ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
        hUV).comp _).comp _).continuous_toRingHom
      (inl A _ _).continuous_toRingHom ?_
    have h₁ :
        (((ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
          hUV).comp
          (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
            hUV)).comp (inl A _ _)).toRingHom.comp
          (QB.toCompletionLoc T_B s_B (Localization.Away s_B) hden_B) =
        ((ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
          hUV).toRingHom.comp
          (QD.toCompletionLoc T_D s_D (Localization.Away s_D) hden_D)).comp
          (CompletedTensor.inl A B C) := by
      simp only [ratLocHom, Hom.comp_assoc, lift_comp_inl, Hom.toRingHom_comp,
        toRingHom_pairHomOfMapsToRationalSubset, RingHom.comp_assoc,
        ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
    rw [h₁]
    change ((existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD T_D s_D hden_D hUV).choose.comp
        (QD.toCompletionLoc T_D s_D (Localization.Away s_D) hden_D)).comp
        (CompletedTensor.inl A B C) = _
    rw [hcomp]
    ext b
    simp [toTensorLocHom]
  · rw [Hom.id_comp]
    apply Hom.ext
    refine completion_locTopology_ringHom_ext_of_continuous QC T_C s_C (Localization.Away s_C)
      hden_C _ _
      (((ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
        hUV).comp _).comp _).continuous_toRingHom
      (inr A _ _).continuous_toRingHom ?_
    have h₁ :
        (((ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
          hUV).comp
          (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
            hUV)).comp (inr A _ _)).toRingHom.comp
          (QC.toCompletionLoc T_C s_C (Localization.Away s_C) hden_C) =
        ((ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
          hUV).toRingHom.comp
          (QD.toCompletionLoc T_D s_D (Localization.Away s_D) hden_D)).comp
          (CompletedTensor.inr A B C) := by
      simp only [ratLocHom, Hom.comp_assoc, lift_comp_inr, Hom.toRingHom_comp,
        toRingHom_pairHomOfMapsToRationalSubset, RingHom.comp_assoc,
        ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
    rw [h₁]
    change ((existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD T_D s_D hden_D hUV).choose.comp
        (QD.toCompletionLoc T_D s_D (Localization.Away s_D) hden_D)).comp
        (CompletedTensor.inr A B C) = _
    rw [hcomp]
    ext c
    simp [toTensorLocHom]

/-- `ratLocSymmHom` followed by `ratLocHom` is the identity on `D⟨T_D/s_D⟩`. -/
@[simp]
theorem ratLocHom_comp_ratLocSymmHom
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV).comp
      (ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
        hUV) =
      Hom.id _ := by
  have hcomp := (existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD T_D s_D hden_D hUV).choose_spec.1.2
  apply Hom.ext
  refine completion_locTopology_ringHom_ext_of_continuous QD T_D s_D (Localization.Away s_D)
    hden_D _ _
    ((ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV).comp
      _).continuous_toRingHom
    (Hom.id _).continuous_toRingHom ?_
  rw [Hom.toRingHom_comp, Hom.toRingHom_id, RingHom.id_comp, RingHom.comp_assoc]
  change (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
      hUV).toRingHom.comp
      ((existsUnique_ofRatLoc QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD T_D s_D hden_D hUV).choose.comp
        (QD.toCompletionLoc T_D s_D (Localization.Away s_D) hden_D)) = _
  rw [hcomp]
  refine CompletedTensor.hom_ext
    ((ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
      hUV).continuous_toRingHom.comp
      (toTensorLocHom (A := A) QB PB hQB T_B s_B hden_B
        QC PC hQC T_C s_C hden_C).continuous_toRingHom)
    (QD.continuous_toCompletionLoc T_D s_D (Localization.Away s_D) hden_D) ?_ ?_
  · have h₁ : (toTensorLocHom (A := A) QB PB hQB T_B s_B hden_B
        QC PC hQC T_C s_C hden_C).toRingHom.comp (CompletedTensor.inl A B C) =
        (CompletedTensor.inl A _ _).comp
          (QB.toCompletionLoc T_B s_B (Localization.Away s_B) hden_B) := by
      rw [← toRingHom_inl, ← Hom.toRingHom_comp]
      simp only [toTensorLocHom, lift_comp_inl, Hom.toRingHom_comp, toRingHom_inl,
        toRingHom_toCompletionLocHom]
    have h₂ : (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV).toRingHom.comp (CompletedTensor.inl A _ _) =
        ringHomOfMapsToRationalSubset QB PB.plus T_B s_B (Localization.Away s_B) hden_B
          QD (PB.completedTensor A PC).plus
          (PB.completedTensor A PC).isRingOfIntegralElements.isPowerBounded_of_mem
          T_D s_D (Localization.Away s_D) hden_D (CompletedTensor.inl A B C)
          (CompletedTensor.continuous_inl A B C)
          (mapsTo_inl_of_subset PB T_B s_B PC T_D s_D
            (hUV.le.trans Set.inter_subset_left)) := by
      rw [← toRingHom_inl, ← Hom.toRingHom_comp]
      simp only [ratLocHom, lift_comp_inl, toRingHom_pairHomOfMapsToRationalSubset]
    rw [RingHom.comp_assoc, h₁, ← RingHom.comp_assoc, h₂,
      ringHomOfMapsToRationalSubset_comp_toCompletionLoc]
  · have h₁ : (toTensorLocHom (A := A) QB PB hQB T_B s_B hden_B
        QC PC hQC T_C s_C hden_C).toRingHom.comp (CompletedTensor.inr A B C) =
        (CompletedTensor.inr A _ _).comp
          (QC.toCompletionLoc T_C s_C (Localization.Away s_C) hden_C) := by
      rw [← toRingHom_inr, ← Hom.toRingHom_comp]
      simp only [toTensorLocHom, lift_comp_inr, Hom.toRingHom_comp, toRingHom_inr,
        toRingHom_toCompletionLocHom]
    have h₂ : (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV).toRingHom.comp (CompletedTensor.inr A _ _) =
        ringHomOfMapsToRationalSubset QC PC.plus T_C s_C (Localization.Away s_C) hden_C
          QD (PB.completedTensor A PC).plus
          (PB.completedTensor A PC).isRingOfIntegralElements.isPowerBounded_of_mem
          T_D s_D (Localization.Away s_D) hden_D (CompletedTensor.inr A B C)
          (CompletedTensor.continuous_inr A B C)
          (mapsTo_inr_of_subset PB PC T_C s_C T_D s_D
            (hUV.le.trans Set.inter_subset_right)) := by
      rw [← toRingHom_inr, ← Hom.toRingHom_comp]
      simp only [ratLocHom, lift_comp_inr, toRingHom_pairHomOfMapsToRationalSubset]
    rw [RingHom.comp_assoc, h₁, ← RingHom.comp_assoc, h₂,
      ringHomOfMapsToRationalSubset_comp_toCompletionLoc]

/-- **Huber-pair ring isomorphism `B⟨T_B/s_B⟩ ⊗̂_A C⟨T_C/s_C⟩ ≃+* D⟨T_D/s_D⟩` for any presentation
`(T_D, s_D)` cutting out `p_B⁻¹(U) ∩ p_C⁻¹(V)`.** -/
noncomputable def ratLocEquiv
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    CompletedTensor A (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C) ≃+*
      ratLoc QD T_D s_D hden_D :=
  RingEquiv.ofRingHom
    (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
      hUV).toRingHom
    (ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
      hUV).toRingHom
    (by
      simpa only [Hom.toRingHom_comp, Hom.toRingHom_id] using
        congrArg Hom.toRingHom
          (ratLocHom_comp_ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
            QD hQD T_D s_D hden_D hUV))
    (by
      simpa only [Hom.toRingHom_comp, Hom.toRingHom_id] using
        congrArg Hom.toRingHom
          (ratLocSymmHom_comp_ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
            QD hQD T_D s_D hden_D hUV))

/-- `ratLocEquiv` is continuous. -/
@[fun_prop]
theorem continuous_ratLocEquiv
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    Continuous (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV) :=
  (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
    hUV).continuous_toRingHom

/-- `(ratLocEquiv …).symm` is continuous. -/
@[fun_prop]
theorem continuous_ratLocEquiv_symm
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    Continuous (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV).symm :=
  (ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D
    hUV).continuous_toRingHom

/-- `ratLocEquiv` is a homeomorphism. -/
theorem isHomeomorph_ratLocEquiv
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)) :
    IsHomeomorph (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV) :=
  (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD hQD T_D s_D hden_D hUV).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV,
     continuous_ratLocEquiv_symm QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV⟩

/-- `ratLocEquiv` sends `inl (algebraMap B B⟨T_B/s_B⟩ b)` to `algebraMap D D⟨T_D/s_D⟩ (inl b)`. -/
@[simp]
theorem ratLocEquiv_inl_algebraMap
    (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
        Set (spa (PB.completedTensor A PC).plus)) =
      (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C))
    (b : B) :
    ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV
        (CompletedTensor.inl A _ _ (algebraMap B (ratLoc QB T_B s_B hden_B) b)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.inl A B C b) := by
  rw [algebraMap_ratLoc QB, algebraMap_ratLoc QD]
  simpa [ratLocEquiv, ratLocHom] using
    ringHomOfMapsToRationalSubset_toCompletionLoc QB PB.plus T_B s_B (Localization.Away s_B)
      hden_B QD (PB.completedTensor A PC).plus
      (PB.completedTensor A PC).isRingOfIntegralElements.isPowerBounded_of_mem T_D s_D
      (Localization.Away s_D) hden_D (CompletedTensor.inl A B C)
      (CompletedTensor.continuous_inl A B C)
      (mapsTo_inl_of_subset PB T_B s_B PC T_D s_D
        (hUV.le.trans Set.inter_subset_left)) b

section RatLocEquivProps

variable
  (hUV : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D :
      Set (spa (PB.completedTensor A PC).plus)) =
    (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
      (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C))

/-- `ratLocEquiv` sends `inr (algebraMap C C⟨T_C/s_C⟩ c)` to `algebraMap D D⟨T_D/s_D⟩ (inr c)`. -/
@[simp]
theorem ratLocEquiv_inr_algebraMap (c : C) :
    ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV
        (CompletedTensor.inr A _ _ (algebraMap C (ratLoc QC T_C s_C hden_C) c)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.inr A B C c) := by
  rw [algebraMap_ratLoc QC, algebraMap_ratLoc QD]
  simpa [ratLocEquiv, ratLocHom] using
    ringHomOfMapsToRationalSubset_toCompletionLoc QC PC.plus T_C s_C (Localization.Away s_C)
      hden_C QD (PB.completedTensor A PC).plus
      (PB.completedTensor A PC).isRingOfIntegralElements.isPowerBounded_of_mem T_D s_D
      (Localization.Away s_D) hden_D (CompletedTensor.inr A B C)
      (CompletedTensor.continuous_inr A B C)
      (mapsTo_inr_of_subset PB PC T_C s_C T_D s_D
        (hUV.le.trans Set.inter_subset_right)) c

/-- `ratLocEquiv` sends pure tensors of elements from `B` and `C` to the image of `b ⊗ₜ[A] c`. -/
theorem ratLocEquiv_tmul_algebraMap (b : B) (c : C) :
    ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV
        (CompletedTensor.toCompletion A _ _
          (algebraMap B (ratLoc QB T_B s_B hden_B) b ⊗ₜ[A]
            algebraMap C (ratLoc QC T_C s_C hden_C) c)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.toCompletion A B C (b ⊗ₜ[A] c)) := by
  simp

/-- `(ratLocEquiv …).symm` sends `algebraMap D D⟨T_D/s_D⟩ (inl b)` to
`inl (algebraMap B B⟨T_B/s_B⟩ b)`. -/
@[simp]
theorem ratLocEquiv_symm_algebraMap_inl (b : B) :
    (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV).symm
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
          (CompletedTensor.inl A B C b)) =
      CompletedTensor.inl A _ _ (algebraMap B (ratLoc QB T_B s_B hden_B) b) := by
  apply (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD hQD T_D s_D hden_D hUV).injective
  simp

/-- `(ratLocEquiv …).symm` sends `algebraMap D D⟨T_D/s_D⟩ (inr c)` to
`inr (algebraMap C C⟨T_C/s_C⟩ c)`. -/
@[simp]
theorem ratLocEquiv_symm_algebraMap_inr (c : C) :
    (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV).symm
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
          (CompletedTensor.inr A B C c)) =
      CompletedTensor.inr A _ _ (algebraMap C (ratLoc QC T_C s_C hden_C) c) := by
  apply (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD hQD T_D s_D hden_D hUV).injective
  simp

/-- **`ratLocEquiv` preserves membership in the rings of integral elements in both directions.** -/
@[simp]
theorem ratLocEquiv_mem_plus_iff
    (x : CompletedTensor A (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)) :
    ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV x ∈
        (rationalLocalizationPair QD (PB.completedTensor A PC) hQD T_D s_D
          (Localization.Away s_D) hden_D).plus ↔
      x ∈ ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor A
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ (ratLocHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD hQD T_D s_D hden_D hUV).map_mem_plus x hx⟩
  have h := (ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD hQD T_D s_D hden_D hUV).map_mem_plus _ hx
  simpa only [show (ratLocSymmHom QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV).toRingHom
      (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV x) = x from
    (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV).symm_apply_apply x] using h

/-- **`ratLocEquiv` carries the completed tensor plus ring `(B_U⁺ ⊗_A C_V⁺)^∧_int` onto
`D_{U×V}⁺`.** -/
theorem map_ratLocEquiv_plus :
    ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B) hden_B).completedTensor
        A (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus.map
        (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV :
          _ →+* _) =
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD T_D s_D
        (Localization.Away s_D) hden_D).plus := by
  ext y
  rw [Subring.mem_map_equiv]
  have h := (ratLocEquiv_mem_plus_iff QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
    QD hQD T_D s_D hden_D hUV
    ((ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV).symm y)).symm
  simpa using h

/-- **Uniqueness of `ratLocEquiv`**: any continuous ring homomorphism
`B⟨T_B/s_B⟩ ⊗̂_A C⟨T_C/s_C⟩ →+* D⟨T_D/s_D⟩` sending `inl (algebraMap B _ b)` to
`algebraMap D _ (inl b)` and `inr (algebraMap C _ c)` to `algebraMap D _ (inr c)` coincides with
`ratLocEquiv`. In particular, for the canonical presentation of `p_B⁻¹(U) ∩ p_C⁻¹(V)`, `ratLocEquiv`
agrees with `CompletedTensor.completionLocEquiv`. -/
theorem eq_ratLocEquiv_of_inl_of_inr
    {f : CompletedTensor A (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C) →+*
      ratLoc QD T_D s_D hden_D}
    (hf : Continuous f)
    (hinl : ∀ b : B, f (CompletedTensor.inl A _ _ (algebraMap B (ratLoc QB T_B s_B hden_B) b)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.inl A B C b))
    (hinr : ∀ c : C, f (CompletedTensor.inr A _ _ (algebraMap C (ratLoc QC T_C s_C hden_C) c)) =
      algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D)
        (CompletedTensor.inr A B C c)) :
    f = (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV : _ →+* _) := by
  let e := ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV
  refine CompletedTensor.hom_ext hf
    (continuous_ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV) ?_ ?_
  · refine completion_locTopology_ringHom_ext_of_continuous QB T_B s_B (Localization.Away s_B)
      hden_B _ _
      (hf.comp (CompletedTensor.continuous_inl A _ _))
      ((continuous_ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV).comp (CompletedTensor.continuous_inl A _ _)) ?_
    ext b
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ← algebraMap_ratLoc QB, e,
      ratLocEquiv_inl_algebraMap] using hinl b
  · refine completion_locTopology_ringHom_ext_of_continuous QC T_C s_C (Localization.Away s_C)
      hden_C _ _
      (hf.comp (CompletedTensor.continuous_inr A _ _))
      ((continuous_ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV).comp (CompletedTensor.continuous_inr A _ _)) ?_
    ext c
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ← algebraMap_ratLoc QC, e,
      ratLocEquiv_inr_algebraMap] using hinr c

/-- **Homeomorphism identifying `Spa((B⟨T_B/s_B⟩, B_U⁺) ⊗̂_A (C⟨T_C/s_C⟩, C_V⁺))` with
`p_B⁻¹(U) ∩ p_C⁻¹(V) ⊆ Spa((B, B⁺) ⊗̂_A (C, C⁺))`.** -/
noncomputable def ratLocSpaHomeomorph :
    spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor A
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus ≃ₜ
      ((inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
        (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C) :
        Set (spa (PB.completedTensor A PC).plus)) :=
  (((spaHomeomorphOfRingEquiv
      (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV)
      (continuous_ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV)
      (continuous_ratLocEquiv_symm QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV)
      (map_ratLocEquiv_plus QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV)).symm).trans
    (spaRationalLocalizationPairHomeomorph QD (PB.completedTensor A PC) hQD T_D s_D
      (Localization.Away s_D) hden_D)).trans
    (Homeomorph.setCongr hUV)

/-- Explicit valuation-level formula for `ratLocSpaHomeomorph`. -/
theorem ratLocSpaHomeomorph_coe_val
    (w : spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor A
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) :
    ((ratLocSpaHomeomorph QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
        QD hQD T_D s_D hden_D hUV w : spa (PB.completedTensor A PC).plus)).1 =
      comap (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D))
        (comap (RingEquiv.toRingHom
          (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
            QD hQD T_D s_D hden_D hUV).symm) w.1) := by
  simp only [ratLocSpaHomeomorph, Homeomorph.trans_apply, Homeomorph.setCongr_apply,
    spaRationalLocalizationPairHomeomorph_coe_val, spaHomeomorphOfRingEquiv_symm_val,
    algebraMap_ratLoc QD]
  rfl

/-- **`ratLocSpaHomeomorph` commutes with the first projection to `Spa(B, B⁺)`.** -/
theorem spaComap_inl_ratLocSpaHomeomorph
    (w : spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor A
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) :
    (inl A PB PC).spaComap
        (ratLocSpaHomeomorph QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
          QD hQD T_D s_D hden_D hUV w : spa (PB.completedTensor A PC).plus) =
      (spaRationalLocalizationPairHomeomorph QB PB hQB T_B s_B (Localization.Away s_B) hden_B
        ((inl A _ _).spaComap w) : spa PB.plus) := by
  apply Subtype.ext
  rw [Hom.spaComap_val, toRingHom_inl, ratLocSpaHomeomorph_coe_val,
    spaRationalLocalizationPairHomeomorph_coe_val, Hom.spaComap_val, toRingHom_inl,
    ← algebraMap_ratLoc QB, comap_comap_apply, comap_comap_apply, comap_comap_apply,
    ← RingHom.comp_assoc]
  have hhom :
      (RingEquiv.toRingHom
          (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
            QD hQD T_D s_D hden_D hUV).symm |>.comp
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D))).comp
        (CompletedTensor.inl A B C) =
      (CompletedTensor.inl A (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)).comp
        (algebraMap B (ratLoc QB T_B s_B hden_B)) := by
    ext b
    simp
  rw [hhom]

/-- **`ratLocSpaHomeomorph` commutes with the second projection to `Spa(C, C⁺)`.** -/
theorem spaComap_inr_ratLocSpaHomeomorph
    (w : spa ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor A
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) :
    (inr A PB PC).spaComap
        (ratLocSpaHomeomorph QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
          QD hQD T_D s_D hden_D hUV w : spa (PB.completedTensor A PC).plus) =
      (spaRationalLocalizationPairHomeomorph QC PC hQC T_C s_C (Localization.Away s_C) hden_C
        ((inr A _ _).spaComap w) : spa PC.plus) := by
  apply Subtype.ext
  rw [Hom.spaComap_val, toRingHom_inr, ratLocSpaHomeomorph_coe_val,
    spaRationalLocalizationPairHomeomorph_coe_val, Hom.spaComap_val, toRingHom_inr,
    ← algebraMap_ratLoc QC, comap_comap_apply, comap_comap_apply, comap_comap_apply,
    ← RingHom.comp_assoc]
  have hhom :
      (RingEquiv.toRingHom
          (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
            QD hQD T_D s_D hden_D hUV).symm |>.comp
        (algebraMap (CompletedTensor A B C) (ratLoc QD T_D s_D hden_D))).comp
        (CompletedTensor.inr A B C) =
      (CompletedTensor.inr A (ratLoc QB T_B s_B hden_B) (ratLoc QC T_C s_C hden_C)).comp
        (algebraMap C (ratLoc QC T_C s_C hden_C)) := by
    ext c
    simp
  rw [hhom]

/-- **Pullback along `ratLocSpaHomeomorph` bijects rational subsets of `Spa(D, D⁺)` contained in
`p_B⁻¹(U) ∩ p_C⁻¹(V)` onto `spaRationalFamily` of the completed tensor spectrum.** -/
theorem bijOn_preimage_ratLocSpaHomeomorph_spaRationalFamily
    (hTD : IsOpen (Ideal.span (T_D : Set (CompletedTensor A B C)) : Set (CompletedTensor A B C))) :
    Set.BijOn (fun W : Set (spa (PB.completedTensor A PC).plus) ↦
        ratLocSpaHomeomorph QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
          QD hQD T_D s_D hden_D hUV ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
          (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)}
      (spaRationalFamily ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor A
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) := by
  have hbij₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_symm_spaRationalFamily
    (ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD T_D s_D hden_D hUV)
    (continuous_ratLocEquiv QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV)
    (continuous_ratLocEquiv_symm QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV)
    (map_ratLocEquiv_plus QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C
      QD hQD T_D s_D hden_D hUV)
  have hbij₂ := bijOn_preimage_spaRationalLocalizationPairHomeomorph_spaRationalFamily
    QD (PB.completedTensor A PC) hQD T_D s_D hTD (Localization.Away s_D) hden_D
  have hdom :
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
          (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)} =
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus T_D s_D} := by
    rw [hUV]
  exact hdom ▸ (hbij₁.comp hbij₂).congr fun W _ ↦ by
    ext w
    simp [ratLocSpaHomeomorph]

end RatLocEquivProps

end UnlocalizedBase

section CanonicalPresentation

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

attribute [local instance 900] ratLocBaseAlgebra isAdicHom_ratLocBaseAlgebra

open scoped Pointwise in
/-- **Specialization of `bijOn_preimage_ratLocSpaHomeomorph_spaRationalFamily` to the canonical
presentation `T_D = ({inl(s_B)} ∪ inl(T_B)) · ({inr(s_C)} ∪ inr(T_C))`,
`s_D = inl(s_B) · inr(s_C)`.** -/
theorem bijOn_preimage_ratLocSpaHomeomorph_canonical
    [inst : DecidableEq (CompletedTensor A B C)]
    (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
    (T_B : Finset B) (s_B : B) (hTB : IsOpen (Ideal.span (T_B : Set B) : Set B))
    (hden_B : QB.HasDenominatorPower T_B s_B (Localization.Away s_B))
    (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
    (T_C : Finset C) (s_C : C) (hTC : IsOpen (Ideal.span (T_C : Set C) : Set C))
    (hden_C : QC.HasDenominatorPower T_C s_C (Localization.Away s_C))
    (QD : PairOfDefinition (CompletedTensor A B C))
    (hQD : QD.ringOfDefinition ≤ (PB.completedTensor A PC).plus) :
    Set.BijOn (fun W : Set (spa (PB.completedTensor A PC).plus) ↦
        ratLocSpaHomeomorph QB PB hQB T_B s_B hden_B QC PC hQC T_C s_C hden_C QD hQD
          (insert (CompletedTensor.inl A B C s_B) (T_B.image (CompletedTensor.inl A B C)) *
            insert (CompletedTensor.inr A B C s_C) (T_C.image (CompletedTensor.inr A B C)))
          (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)
          (CompletedTensor.hasDenominatorPower_inl_mul_inr QD hTB hTC
            (Localization.Away (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)))
          (spaComap_inl_preimage_inter_spaComap_inr_preimage_rationalSubset
            PB PC T_B s_B T_C s_C).symm
          ⁻¹' (Subtype.val ⁻¹' W))
      {W ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        W ⊆ (inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus T_B s_B) ∩
          (inr A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PC.plus T_C s_C)}
      (spaRationalFamily ((rationalLocalizationPair QB PB hQB T_B s_B (Localization.Away s_B)
        hden_B).completedTensor A
        (rationalLocalizationPair QC PC hQC T_C s_C (Localization.Away s_C) hden_C)).plus) := by
  refine bijOn_preimage_ratLocSpaHomeomorph_spaRationalFamily QB PB hQB T_B s_B hden_B
    QC PC hQC T_C s_C hden_C QD hQD
    (insert (CompletedTensor.inl A B C s_B) (T_B.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C s_C) (T_C.image (CompletedTensor.inr A B C)))
    (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)
    (CompletedTensor.hasDenominatorPower_inl_mul_inr QD hTB hTC
      (Localization.Away (CompletedTensor.inl A B C s_B * CompletedTensor.inr A B C s_C)))
    (spaComap_inl_preimage_inter_spaComap_inr_preimage_rationalSubset PB PC T_B s_B T_C s_C).symm
    ?_
  have hdec : inst = Classical.decEq (CompletedTensor A B C) := Subsingleton.elim _ _
  subst hdec
  classical
  exact QD.isOpen_span_insert_mul_insert
    (by
      rw [Finset.coe_image, ← Ideal.map_span]
      exact (CompletedTensor.isAdicHom_inl A B C).isOpen_map hTB)
    (by
      rw [Finset.coe_image, ← Ideal.map_span]
      exact (CompletedTensor.isAdicHom_inr A B C).isOpen_map hTC)

end CanonicalPresentation

end Pair.completedTensor

end TauCeti.Huber

end
