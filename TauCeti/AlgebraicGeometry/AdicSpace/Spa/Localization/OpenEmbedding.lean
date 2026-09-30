/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# The adic spectrum of `A⟨T/s⟩` is an open subspace of `Spa (A, A⁺)`

For a rational subset `R(T/s)` of `Spa (A, A⁺)`, the map `j : Spa (A⟨T/s⟩, A_U⁺) → Spa (A, A⁺)`
induced by the structure map `A → A⟨T/s⟩` is an open embedding with range `R(T/s)`. This is the
form of Wedhorn's Proposition 8.2 (2), first assertion, that the structure presheaves consume: the
presheaf of `Spa (A, A⁺)` restricted along `j` is a presheaf on `Spa (A⟨T/s⟩, A_U⁺)`, whose value
at an open `W` is the value of the original presheaf at the image `j(W)`.

The file records the calculus of images and preimages of opens along `j` — the pullback
`locOpensComap` is a left inverse of the image functor `j''`, and a right inverse of it on the
opens contained in `R(T/s)` — and that both carry rational opens to rational opens. Together with
`exists_mem_spaRationalOpens_locOpensComap_eq` this makes `j''` a bijection from the rational opens
of `Spa (A⟨T/s⟩, A_U⁺)` onto the rational opens of `Spa (A, A⁺)` contained in `R(T/s)`, which is
Proposition 8.2 (2), second assertion, for `Opens`.

## Main definitions

* `TauCeti.ValuationSpectrum.spaComapLocHom`: the map `j` as a morphism of `TopCat`.

## Main results

* `TauCeti.ValuationSpectrum.isOpenEmbedding_spaComapLoc`,
  `TauCeti.ValuationSpectrum.isOpenEmbedding_spaComapLocHom`: `j` is an open embedding.
* `TauCeti.ValuationSpectrum.range_spaComapLoc`: the range of `j` is `R(T/s)`.
* `TauCeti.ValuationSpectrum.locOpensComap_spaComapLoc_functor_obj`,
  `TauCeti.ValuationSpectrum.spaComapLoc_functor_obj_locOpensComap`: `j⁻¹(j(W)) = W`, and
  `j(j⁻¹(V)) = V` for `V ⊆ R(T/s)`.
* `TauCeti.ValuationSpectrum.spaComapLoc_functor_obj_mono`,
  `TauCeti.ValuationSpectrum.spaComapLoc_functor_obj_le_spaBasicOpen`: the image along `j` is
  monotone and lies in `R(T/s)`.
* `TauCeti.ValuationSpectrum.spaComapLoc_functor_obj_mem_spaRationalOpens`,
  `TauCeti.ValuationSpectrum.locOpensComap_mem_spaRationalOpens`: images and preimages of rational
  opens along `j` are rational opens.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2 (2).
-/

public section

open CategoryTheory Topology TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

namespace TauCeti.ValuationSpectrum

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A)
  (s : A) (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

/-! ### `Spa (A⟨T/s⟩, A_U⁺) → Spa (A, A⁺)` is an open embedding -/

include hP in
/-- **The range of `j : Spa (A⟨T/s⟩, A_U⁺) → Spa (A, A⁺)` is `R(T/s)`**, as a subset of
`Spa (A, A⁺)`. The containment `⊆` is `range_spaComapLoc_subset`; equality is the surjectivity of
`spaCompletedLocalizationHomeomorph` onto the rational subset. -/
theorem range_spaComapLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Set.range (spaComapLoc P Aplus T s S hden) = spaBasicOpen Aplus T s := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [← val_comp_spaCompletedLocalizationHomeomorph P Aplus hP T s S hden, Set.range_comp,
    (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).surjective.range_eq, Set.image_univ,
    Subtype.range_val]
  exact Set.ext fun _ ↦ mem_spaBasicOpen.symm

include hP in
/-- **`j : Spa (A⟨T/s⟩, A_U⁺) → Spa (A, A⁺)` is an open embedding.** It is the homeomorphism
`spaCompletedLocalizationHomeomorph` onto `R(T/s)` followed by the inclusion of that open
subset. -/
theorem isOpenEmbedding_spaComapLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsOpenEmbedding (spaComapLoc P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [← val_comp_spaCompletedLocalizationHomeomorph P Aplus hP T s S hden]
  exact (isOpen_val_preimage_rationalSubset Aplus T s).isOpenEmbedding_subtypeVal.comp
    (spaCompletedLocalizationHomeomorph P Aplus hP T s S hden).isOpenEmbedding

/-- **The map `j : Spa (A⟨T/s⟩, A_U⁺) → Spa (A, A⁺)` as a morphism of `TopCat`**, the form in
which a presheafed space is restricted along it. -/
noncomputable def spaComapLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    TopCat.of ↥(spa (completedPlusSubring P Aplus T s S hden)) ⟶ TopCat.of ↥(spa Aplus) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  TopCat.ofHom ⟨spaComapLoc P Aplus T s S hden, continuous_spaComapLoc P Aplus T s S hden⟩

/-- The morphism `spaComapLocHom` is the function `spaComapLoc`. -/
@[simp]
theorem coe_spaComapLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ⇑(spaComapLocHom P Aplus T s S hden) = spaComapLoc P Aplus T s S hden := by
  rfl

include hP in
/-- **`j : Spa (A⟨T/s⟩, A_U⁺) → Spa (A, A⁺)` is an open embedding**, for the morphism of
`TopCat`. -/
theorem isOpenEmbedding_spaComapLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsOpenEmbedding (spaComapLocHom P Aplus T s S hden) :=
  isOpenEmbedding_spaComapLoc P Aplus hP T s S hden

/-! ### Images and preimages of opens along `j` -/

/-- The pullback of an open along `j` is the preimage of its underlying set. -/
@[simp]
theorem coe_locOpensComap (V : Opens ↥(spa Aplus)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (locOpensComap P Aplus T s S hden V : Set ↥(spa (completedPlusSubring P Aplus T s S hden))) =
      spaComapLoc P Aplus T s S hden ⁻¹' V :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  Set.ext fun v ↦ mem_locOpensComap P Aplus T s S hden V v

/-- **Pulling back the image of an open along `j` gives the open back**: `j⁻¹(j(W)) = W`, since
`j` is injective. -/
@[simp]
theorem locOpensComap_spaComapLoc_functor_obj :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      locOpensComap P Aplus T s S hden
        ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W) = W := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W
  refine Opens.ext ?_
  rw [coe_locOpensComap, IsOpenMap.coe_functor_obj, coe_spaComapLocHom]
  exact Set.preimage_image_eq _ (isOpenEmbedding_spaComapLoc P Aplus hP T s S hden).injective

/-- **The image of the pullback of an open contained in `R(T/s)` is the open itself**:
`j(j⁻¹(V)) = V` for `V ⊆ R(T/s)`, since `R(T/s)` is the range of `j`. -/
@[simp]
theorem spaComapLoc_functor_obj_locOpensComap {V : Opens ↥(spa Aplus)}
    (hV : V ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj
      (locOpensComap P Aplus T s S hden V) = V := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  refine Opens.ext ?_
  rw [IsOpenMap.coe_functor_obj, coe_locOpensComap, coe_spaComapLocHom]
  refine Set.image_preimage_eq_of_subset ?_
  rw [range_spaComapLoc P Aplus hP T s S hden]
  exact hV

/-- The image along `j` preserves containment of opens. This is `CategoryTheory.Functor.monotone`
for the image functor of `j`, in the form the restriction maps between presentation limits
take as their argument. -/
theorem spaComapLoc_functor_obj_mono :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {W W' : Opens ↥(spa (completedPlusSubring P Aplus T s S hden))}, W' ≤ W →
      (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W' ≤
        (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W :=
  fun h ↦ ((isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.map (homOfLE h)).le

/-- The image along `j` of every open of `Spa (A⟨T/s⟩, A_U⁺)` lies in `R(T/s)`. -/
theorem spaComapLoc_functor_obj_le_spaBasicOpen :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W : Opens ↥(spa (completedPlusSubring P Aplus T s S hden)),
      (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W ≤
        spaBasicOpen Aplus T s := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W
  rw [← SetLike.coe_subset_coe, IsOpenMap.coe_functor_obj, coe_spaComapLocHom,
    ← range_spaComapLoc P Aplus hP T s S hden]
  exact Set.image_subset_range _ _

/-! ### Rational opens correspond -/

/-- **The image along `j` of a rational open is a rational open**, when `T` spans an open ideal.
This is the injectivity half of Wedhorn's Proposition 8.2 (2), second assertion, for `Opens`:
combined with `exists_mem_spaRationalOpens_locOpensComap_eq`, the pullback along `j` and the image
along `j` are inverse bijections between the rational opens of `Spa (A, A⁺)` contained in
`R(T/s)` and the rational opens of `Spa (A⟨T/s⟩, A_U⁺)`. -/
theorem spaComapLoc_functor_obj_mem_spaRationalOpens
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ W ∈ spaRationalOpens (completedPlusSubring P Aplus T s S hden),
      (isOpenEmbedding_spaComapLocHom P Aplus hP T s S hden).functor.obj W ∈
        spaRationalOpens Aplus := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro W hW
  obtain ⟨V, hV, hVT, rfl⟩ :=
    exists_mem_spaRationalOpens_locOpensComap_eq P Aplus T s S hden hT W hW
  rw [spaComapLoc_functor_obj_locOpensComap P Aplus hP T s S hden hVT]
  exact hV

/-- **The pullback along `j` of a rational open is a rational open.** This is
`spaComapLoc_preimage_mem_spaRationalFamily` for `Opens`. -/
theorem locOpensComap_mem_spaRationalOpens {V : Opens ↥(spa Aplus)}
    (hV : V ∈ spaRationalOpens Aplus) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    locOpensComap P Aplus T s S hden V ∈
      spaRationalOpens (completedPlusSubring P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [mem_spaRationalOpens, coe_locOpensComap]
  exact spaComapLoc_preimage_mem_spaRationalFamily P Aplus T s S hden (mem_spaRationalOpens.mp hV)

end TauCeti.ValuationSpectrum

end
