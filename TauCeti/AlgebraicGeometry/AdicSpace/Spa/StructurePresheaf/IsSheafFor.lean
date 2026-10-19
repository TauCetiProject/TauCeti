/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Localization
public import Mathlib.CategoryTheory.Sites.IsSheafFor

import TauCeti.CategoryTheory.Sites.IsSheafFor

/-!
# The sheaf condition for a family of opens of `Spa(A, A⁺)`

Let `𝒪` be the presentation-limit presheaf of `Spa(A, A⁺)`, regarded as a presheaf of sets. This
file gives two descriptions of the sheaf condition of `𝒪` for a family of opens `U i ⊆ W`.

* Read on the presentation limits themselves, it says that sections over the `U i` agreeing on
  the pairwise overlaps `U i ⊓ U j` are the restrictions of a unique section over `W`
  (`isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap`).
* When `W` and the `U i` are rational opens inside a rational subset `R(T/s)`, it is equivalent to
  the sheaf condition of the presentation-limit presheaf of `B = A⟨T/s⟩` for the family of their
  pullbacks along `j : Spa(B, A_U⁺) → Spa(A, A⁺)` (`isSheafFor_ofArrows_iff_locOpensComap`). This
  is Wedhorn's Remark 8.4, `presentationLimitLocIso`, applied to every member of the family and to
  the pairwise overlaps.

The second statement reduces the sheaf condition for a cover of a rational subset to the sheaf
condition for a cover of the whole adic spectrum of a complete ring, where elements that vanish
nowhere on the rational subset become units. This is how Wedhorn's proof of Lemma 8.34 passes
between a rational subset and its coordinate ring.

## Main results

* `TauCeti.ValuationSpectrum.isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap` : the
  sheaf condition for a family of opens, in terms of `presentationLimitMap`.
* `TauCeti.ValuationSpectrum.isSheafFor_ofArrows_iff_locOpensComap` : the sheaf condition for a
  family of rational opens inside `R(T/s)` is the sheaf condition for their pullbacks to the adic
  spectrum of `A⟨T/s⟩`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.4 and Lemma 8.34.
-/

public section

open CategoryTheory Opposite TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

section Characterization

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) {Aplus : Subring A}

/-- **The restriction maps of the presheaf of sets are those of `presentationLimit`.** Read through
the transports along `presentationLimitPresheaf_obj`, restricting a section of the
presentation-limit presheaf of sets from `V` to `W ≤ V` is applying `presentationLimitMap`. -/
theorem eqToHom_apply_presentationLimitPresheaf_map_apply {V W : Opens ↥(spa Aplus)}
    (h : W ≤ V) (x : (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
      forget _root_.TopCommRingCat).obj (Opposite.op V)) :
    (eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op W))).hom.1
      ((presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat).map (homOfLE h).op x) =
      (presentationLimitMap (P := P) h).hom.1
        ((eqToHom (presentationLimitPresheaf_obj P Aplus (Opposite.op V))).hom.1 x) := by
  rw [Functor.comp_map, Functor.comp_map, presentationLimitPresheaf_map]
  exact Iso.hom_inv_id_apply
    (eqToIso (presentationLimitPresheaf_obj P Aplus (Opposite.op W)).symm) _

/-- **The sheaf condition for a family of opens, read on presentation limits.** The
presentation-limit presheaf of sets satisfies the sheaf condition for a family of opens `U i ≤ W`
exactly when every family of sections `x i` of `presentationLimit` over the `U i` that agree on
the pairwise overlaps `U i ⊓ U j` is the family of restrictions of a unique section over `W`. -/
theorem isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap {W : Opens ↥(spa Aplus)}
    {ι : Type*} {U : ι → Opens ↥(spa Aplus)} (hUW : ∀ i, U i ≤ W) :
    (Presieve.ofArrows U fun i ↦ homOfLE (hUW i)).IsSheafFor
        (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
          forget _root_.TopCommRingCat) ↔
      ∀ x : ∀ i, presentationLimit (P := P) Aplus (U i),
        (∀ i j, (presentationLimitMap (P := P) (inf_le_left : U i ⊓ U j ≤ U i)).hom.1 (x i) =
          (presentationLimitMap (P := P) (inf_le_right : U i ⊓ U j ≤ U j)).hom.1 (x j)) →
        ∃! a : presentationLimit (P := P) Aplus W, ∀ i,
          (presentationLimitMap (P := P) (hUW i)).hom.1 a = x i := by
  -- `τ V` reads a section of the presheaf of sets as an element of `presentationLimit V`, and
  -- `τ' V` is its inverse
  let e (V : Opens ↥(spa Aplus)) := presentationLimitPresheaf_obj P Aplus (op V)
  let τ (V : Opens ↥(spa Aplus)) := (eqToHom (e V)).hom.1
  let τ' (V : Opens ↥(spa Aplus)) := (eqToHom (e V).symm).hom.1
  have hττ' (V : Opens ↥(spa Aplus)) y : τ V (τ' V y) = y := (eqToIso (e V).symm).hom_inv_id_apply y
  have hτ'τ (V : Opens ↥(spa Aplus)) y : τ' V (τ V y) = y := (eqToIso (e V)).hom_inv_id_apply y
  have hτ (V : Opens ↥(spa Aplus)) : Function.Injective (τ V) :=
    Function.LeftInverse.injective (hτ'τ V)
  have hmap {V V' : Opens ↥(spa Aplus)} (h : V' ≤ V) y :=
    eqToHom_apply_presentationLimitPresheaf_map_apply P h y
  rw [Presieve.isSheafFor_arrows_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · -- read `x` as a compatible family of the presheaf of sets and glue it there
    obtain ⟨t, ht, hu⟩ := h (fun i ↦ τ' _ (x i)) <|
      (Presieve.Arrows.compatible_homOfLE_iff hUW _).2 fun i j ↦ hτ _ <| by
        rw [hmap, hmap, hττ', hττ']
        exact hx i j
    refine ⟨τ W t, fun i ↦ ?_, fun a ha ↦ ?_⟩
    · rw [← hmap, ht i, hττ']
    · rw [← hu (τ' W a) fun i ↦ hτ _ (by rw [hmap, hττ', hττ', ha i]), hττ']
  · obtain ⟨a, ha, hu⟩ := h (fun i ↦ τ _ (x i)) fun i j ↦ by
      rw [← hmap, ← hmap]
      exact congrArg _ ((Presieve.Arrows.compatible_homOfLE_iff hUW x).1 hx i j)
    refine ⟨τ' W a, fun i ↦ hτ _ (by rw [hmap, hττ', ha]), fun t ht ↦ ?_⟩
    rw [← hu (τ W t) fun i ↦ by rw [← hmap, ht i], hτ'τ]

end Characterization

section Transport

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
  (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hT : IsOpen (Ideal.span (T : Set A) : Set A))

include hAplus hT

-- Unique gluing of sections of `presentationLimit` over a family of rational opens `U i ⊆ W` of
-- `R(T/s)` is equivalent, along Wedhorn's Remark 8.4, to unique gluing over the pullbacks of `W`
-- and the `U i` to `Spa(A⟨T/s⟩, A_U⁺)`.
private theorem existsUnique_presentationLimitMap_eq_iff_locOpensComap {W : Opens ↥(spa Aplus)}
    (hW : W ∈ spaRationalOpens Aplus) (hWT : W ≤ spaBasicOpen Aplus T s) {ι : Type*}
    {U : ι → Opens ↥(spa Aplus)} (hU : ∀ i, U i ∈ spaRationalOpens Aplus) (hUW : ∀ i, U i ≤ W) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (∀ y : ∀ i, presentationLimit (P := completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden) (locOpensComap P Aplus T s S hden (U i)),
      (∀ i j, (presentationLimitMap (P := completionLocalization P T s S hden)
          (inf_le_left : locOpensComap P Aplus T s S hden (U i) ⊓
            locOpensComap P Aplus T s S hden (U j) ≤ _)).hom.1 (y i) =
        (presentationLimitMap (P := completionLocalization P T s S hden)
          (inf_le_right : locOpensComap P Aplus T s S hden (U i) ⊓
            locOpensComap P Aplus T s S hden (U j) ≤ _)).hom.1 (y j)) →
      ∃! c : presentationLimit (P := completionLocalization P T s S hden)
          (completedPlusSubring P Aplus T s S hden) (locOpensComap P Aplus T s S hden W), ∀ i,
        (presentationLimitMap (P := completionLocalization P T s S hden)
          (locOpensComap_mono P Aplus T s S hden (hUW i))).hom.1 c = y i) ↔
    ∀ x : ∀ i, presentationLimit (P := P) Aplus (U i),
      (∀ i j, (presentationLimitMap (P := P) (inf_le_left : U i ⊓ U j ≤ U i)).hom.1 (x i) =
        (presentationLimitMap (P := P) (inf_le_right : U i ⊓ U j ≤ U j)).hom.1 (x j)) →
      ∃! a : presentationLimit (P := P) Aplus W, ∀ i,
        (presentationLimitMap (P := P) (hUW i)).hom.1 a = x i := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  -- `σ V` is Remark 8.4 at a rational open `V ⊆ R(T/s)`: a bijection on sections, natural in `V`
  let σ (V : Opens ↥(spa Aplus)) (hV : V ∈ spaRationalOpens Aplus)
      (hVT : V ≤ spaBasicOpen Aplus T s) :=
    (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVT).hom.hom.1
  have hσ (V : Opens ↥(spa Aplus)) (hV hVT) : Function.Bijective (σ V hV hVT) :=
    bijective_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT hV hVT
  have nat {V V' : Opens ↥(spa Aplus)} (hV hV' hVT) (h : V' ≤ V) z :=
    presentationLimitLocIso_hom_presentationLimitMap_apply P Aplus T s S hden hAplus hT hV hV' hVT
      h z
  have hUT (i : ι) : U i ≤ spaBasicOpen Aplus T s := (hUW i).trans hWT
  have hO (i j : ι) : U i ⊓ U j ∈ spaRationalOpens Aplus := inf_mem_spaRationalOpens (hU i) (hU j)
  -- a family agrees on the overlaps exactly when its image under `σ` agrees on the overlaps of
  -- the pullbacks, which are the pullbacks of the overlaps
  have hcompat (x : ∀ i, presentationLimit (P := P) Aplus (U i)) (i j : ι) :
      (presentationLimitMap (P := P) (inf_le_left : U i ⊓ U j ≤ U i)).hom.1 (x i) =
          (presentationLimitMap (P := P) (inf_le_right : U i ⊓ U j ≤ U j)).hom.1 (x j) ↔
        (presentationLimitMap (P := completionLocalization P T s S hden)
          (inf_le_left : locOpensComap P Aplus T s S hden (U i) ⊓
            locOpensComap P Aplus T s S hden (U j) ≤ _)).hom.1 (σ _ (hU i) (hUT i) (x i)) =
        (presentationLimitMap (P := completionLocalization P T s S hden)
          (inf_le_right : locOpensComap P Aplus T s S hden (U i) ⊓
            locOpensComap P Aplus T s S hden (U j) ≤ _)).hom.1 (σ _ (hU j) (hUT j) (x j)) := by
    have hOij := locOpensComap_inf P Aplus T s S hden (U i) (U j)
    rw [← (hσ _ (hO i j) (inf_le_left.trans (hUT i))).1.eq_iff,
      nat (hU i) (hO i j) (hUT i) inf_le_left, nat (hU j) (hO i j) (hUT j) inf_le_right]
    refine ⟨fun e ↦ ?_, fun e ↦ ?_⟩
    · simpa only [presentationLimitMap_apply_presentationLimitMap_apply] using
        congrArg (presentationLimitMap (P := completionLocalization P T s S hden) hOij.ge).hom.1 e
    · simpa only [presentationLimitMap_apply_presentationLimitMap_apply] using
        congrArg (presentationLimitMap (P := completionLocalization P T s S hden) hOij.le).hom.1 e
  refine ⟨fun h x hx ↦ ?_, fun h y hy ↦ ?_⟩
  · -- glue the images of the `x i` and pull the gluing back to `W`
    obtain ⟨c, hc, hcu⟩ := h _ fun i j ↦ (hcompat x i j).1 (hx i j)
    obtain ⟨a, rfl⟩ := (hσ W hW hWT).2 c
    refine ⟨a, fun i ↦ (hσ _ (hU i) (hUT i)).1 ?_, fun a' ha' ↦ (hσ W hW hWT).1 ?_⟩
    · rw [nat hW (hU i) hWT (hUW i), hc i]
    · refine hcu _ fun i ↦ ?_
      rw [← nat hW (hU i) hWT (hUW i), ha' i]
  · -- pull the `y i` back along `σ`, glue there, and push the gluing forward
    choose x hx using fun i ↦ (hσ _ (hU i) (hUT i)).2 (y i)
    obtain rfl : y = fun i ↦ σ _ (hU i) (hUT i) (x i) := funext fun i ↦ (hx i).symm
    obtain ⟨a, ha, hau⟩ := h x fun i j ↦ (hcompat x i j).2 (hy i j)
    refine ⟨σ W hW hWT a, fun i ↦ by rw [← nat hW (hU i) hWT (hUW i), ha i], fun c hc ↦ ?_⟩
    obtain ⟨a', rfl⟩ := (hσ W hW hWT).2 c
    rw [hau a' fun i ↦ (hσ _ (hU i) (hUT i)).1 (by rw [nat hW (hU i) hWT (hUW i), hc i])]

/-- **The sheaf condition transported along Wedhorn's Remark 8.4.** Let `W ⊆ R(T/s)` be rational
opens of `Spa(A, A⁺)`, where `T` spans an open ideal and `A⁺` consists of power-bounded elements,
and let `U i ⊆ W` be rational opens. Write `j : Spa(A⟨T/s⟩, A_U⁺) → Spa(A, A⁺)` for the map
induced by the structure map, with pullback `locOpensComap`. The presentation-limit presheaf of
sets of `A` satisfies the sheaf condition for the family `U i ⊆ W` exactly when the
presentation-limit presheaf of sets of `A⟨T/s⟩` satisfies it for the family `j⁻¹(U i) ⊆ j⁻¹(W)`.
-/
theorem isSheafFor_ofArrows_iff_locOpensComap {W : Opens ↥(spa Aplus)}
    (hW : W ∈ spaRationalOpens Aplus) (hWT : W ≤ spaBasicOpen Aplus T s) {ι : Type*}
    {U : ι → Opens ↥(spa Aplus)} (hU : ∀ i, U i ∈ spaRationalOpens Aplus) (hUW : ∀ i, U i ≤ W) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (Presieve.ofArrows U fun i ↦ homOfLE (hUW i)).IsSheafFor
        (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
          forget _root_.TopCommRingCat) ↔
      (Presieve.ofArrows (fun i ↦ locOpensComap P Aplus T s S hden (U i))
        fun i ↦ homOfLE (locOpensComap_mono P Aplus T s S hden (hUW i))).IsSheafFor
          (presentationLimitPresheaf (completionLocalization P T s S hden)
              (completedPlusSubring P Aplus T s S hden) ⋙
            TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap,
    isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap]
  exact (existsUnique_presentationLimitMap_eq_iff_locOpensComap P Aplus T s S hden hAplus hT hW
    hWT hU hUW).symm

end Transport

end TauCeti.ValuationSpectrum
