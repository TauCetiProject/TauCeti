/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Localization
public import Mathlib.CategoryTheory.Sites.IsSheafFor

import TauCeti.CategoryTheory.Sites.IsSheafFor
import TauCeti.CategoryTheory.Sites.IsSheafForTrans
import TauCeti.Topology.Homeomorph.Inducing

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
  the pairwise overlaps; both directions are an instance of the transport of the sheaf condition
  along bijections of sections, `TauCeti.TopologicalSpace.Opens.isSheafFor_ofArrows_iff_of_equiv`.

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

/-- **Restriction to opens `V i ≤ W` is inducing on sections of the presentation-limit presheaf
exactly when it is inducing on presentation limits.** The two spaces of sections are identified
by the transports along `presentationLimitPresheaf_obj`. -/
theorem isInducing_restrictionMap_iff_isInducing_presentationLimitMap {ι : Type*}
    {W : Opens ↥(spa Aplus)} {V : ι → Opens ↥(spa Aplus)} (h : ∀ i, V i ≤ W) :
    Topology.IsInducing (fun (x : (presentationLimitPresheaf P Aplus).obj (op W)) (i : ι) ↦
      ((presentationLimitPresheaf P Aplus).map (homOfLE (h i)).op).hom.1 x) ↔
    Topology.IsInducing (fun (x : presentationLimit (P := P) Aplus W) (i : ι) ↦
      (presentationLimitMap (P := P) (h i)).hom.1 x) := by
  let G := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ _root_.TopCommRingCat TopCat
  let e (V : Opens ↥(spa Aplus)) :
      (presentationLimitPresheaf P Aplus).obj (op V) ≃ₜ presentationLimit (P := P) Aplus V :=
    TopCat.homeoOfIso (G.mapIso (eqToIso (presentationLimitPresheaf_obj P Aplus (op V))))
  have e_apply (V : Opens ↥(spa Aplus)) (x : (presentationLimitPresheaf P Aplus).obj (op V)) :
      e V x = (eqToHom (presentationLimitPresheaf_obj P Aplus (op V))).hom.1 x := rfl
  exact (e W).isInducing_pi_iff_of_homeomorph (fun i ↦ e (V i)) fun x i ↦ by
    rw [e_apply, e_apply]
    exact eqToHom_apply_presentationLimitPresheaf_map_apply P (h i) x

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

/-- **Wedhorn's Remark 8.4 as isomorphisms of sections commuting with restriction.** For the
rational opens `V ⊆ R(T/s)` of `Spa(A, A⁺)`, the presentation-limit sections over `V` are isomorphic
to those of `Spa(A⟨T/s⟩, A_U⁺)` over `locOpensComap P Aplus T s S hden V`, and these
isomorphisms commute with the restriction maps. -/
theorem exists_iso_presentationLimitPresheaf_locOpensComap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃ σ : (∀ V : Opens ↥(spa Aplus), V ∈ spaRationalOpens Aplus → V ≤ spaBasicOpen Aplus T s →
        Iso ((presentationLimitPresheaf P Aplus).obj (op V))
          ((presentationLimitPresheaf (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden)).obj
              (op (locOpensComap P Aplus T s S hden V)))),
      ∀ {V V' : Opens ↥(spa Aplus)} (hV : V ∈ spaRationalOpens Aplus)
        (hV' : V' ∈ spaRationalOpens Aplus) (hVT : V ≤ spaBasicOpen Aplus T s) (h : V' ≤ V),
        (presentationLimitPresheaf P Aplus).map (homOfLE h).op ≫ (σ V' hV' (h.trans hVT)).hom =
          (σ V hV hVT).hom ≫ (presentationLimitPresheaf (completionLocalization P T s S hden)
            (completedPlusSubring P Aplus T s S hden)).map
              (homOfLE (locOpensComap_mono P Aplus T s S hden h)).op := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  let Bplus := completedPlusSubring P Aplus T s S hden
  let Q := completionLocalization P T s S hden
  let F := presentationLimitPresheaf P Aplus
  let FB := presentationLimitPresheaf Q Bplus
  let σ (V : Opens ↥(spa Aplus)) (hV : V ∈ spaRationalOpens Aplus)
      (hVW : V ≤ spaBasicOpen Aplus T s) :
      F.obj (op V) ≅ FB.obj (op (locOpensComap P Aplus T s S hden V)) :=
    eqToIso (presentationLimitPresheaf_obj P Aplus (op V)) ≪≫
      presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW ≪≫
      eqToIso (presentationLimitPresheaf_obj Q Bplus
        (op (locOpensComap P Aplus T s S hden V))).symm
  refine ⟨σ, fun {V V'} hV hV' hVT h ↦ ?_⟩
  dsimp only [σ]
  rw [presentationLimitPresheaf_map, presentationLimitPresheaf_map]
  simp only [Iso.trans_hom]
  simp only [Category.assoc]
  simp only [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  slice_lhs 2 3 =>
    rw [presentationLimitMap_comp_presentationLimitLocIso_hom P Aplus T s S hden hAplus hT
      hV hV' hVT h]
  simp only [Category.assoc]

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
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  -- Remark 8.4 gives bijections of sections that commute with restriction
  obtain ⟨σ, σ_nat⟩ := exists_iso_presentationLimitPresheaf_locOpensComap P Aplus T s S hden
    hAplus hT
  refine TauCeti.TopologicalSpace.Opens.isSheafFor_ofArrows_iff_of_equiv
    (F := presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
      forget _root_.TopCommRingCat)
    (G := presentationLimitPresheaf (completionLocalization P T s S hden)
      (completedPlusSubring P Aplus T s S hden) ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
      forget _root_.TopCommRingCat)
    (locOpensComap P Aplus T s S hden) (fun _ _ h ↦ locOpensComap_mono P Aplus T s S hden h)
    (locOpensComap_inf P Aplus T s S hden) (fun V hV V' hV' ↦ inf_mem_spaRationalOpens hV hV')
    hW hU hUW (fun V hV hVW ↦ ((forget _root_.TopCommRingCat).mapIso
      (TopCommRingCat.isCompleteSeparated.ι.mapIso (σ V hV (hVW.trans hWT)))).toEquiv) ?_
  intro V V' hV hV' hVW h x
  have := congrArg (fun f ↦ ConcreteCategory.hom (TopCommRingCat.isCompleteSeparated.ι.map f))
    (σ_nat hV hV' (hVW.trans hWT) h)
  simp only [Functor.map_comp] at this
  exact DFunLike.congr_fun this x

end Transport

end TauCeti.ValuationSpectrum
