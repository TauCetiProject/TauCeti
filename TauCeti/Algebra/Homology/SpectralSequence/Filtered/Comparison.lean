/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality

/-!
# The comparison theorem for filtered complexes

A morphism `α : filtrationFunctor F hF ⟶ filtrationFunctor G hG` of filtered complexes induces
the morphism of spectral sequences `spectralSequenceMap coreE₂Cohomological (spectralObjectMap α)`.
If the filtrations are finite and this morphism is an isomorphism on some page, then `α.app ⊤`
induces isomorphisms in cohomology. The last step, from the abutments to the cohomology of the
filtered complexes, holds for all filtrations.

## Main results

* `CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality`:
  on the first page, the morphism of spectral sequences is the map in cohomology of the induced
  morphism of graded pieces.
* `CochainComplex.spectralObjectMap_filtrationFunctorMap_abutment_comp`:
  on the abutment, the morphism of spectral objects induced by a morphism `f` of filtered
  complexes is the map in cohomology of `f`.
* `CochainComplex.isIso_homologyMap_app_top_of_isIso_abutment`: an isomorphism on the abutments
  gives an isomorphism in cohomology.
* `CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page`: the comparison theorem.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K L : CochainComplex C ℤ}

/-- The map in cohomology induced by `α.app ⊤` is an isomorphism as soon as the morphism of
spectral objects induced by `α` is an isomorphism on the abutment `H^n(⊥ ≤ ⊤)`. -/
lemma isIso_homologyMap_app_top_of_isIso_abutment {F : ℤ → Subobject K} {hF : Monotone F}
    {G : ℤ → Subobject L} {hG : Monotone G} (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG)
    (n : ℤ)
    (h : IsIso (((spectralObjectMap α).hom n).app (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))))) :
    IsIso (HomologicalComplex.homologyMap (α.app ⊤) n) := by
  have hc := (Iso.eq_inv_comp _).mpr
    (spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom α
      (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)) n).symm
  have : IsIso (HomologicalComplex.homologyMap (cokernel.map _ _ _ _
      (α.naturality (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n) := by
    rw [hc]
    infer_instance
  have := cokernel.π_of_zero (filtrationFunctor_map_bot F hF ⊤)
  have := cokernel.π_of_zero (filtrationFunctor_map_bot G hG ⊤)
  have e : HomologicalComplex.homologyMap (α.app ⊤) n ≫ HomologicalComplex.homologyMap
      (cokernel.π ((filtrationFunctor G hG).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n =
      HomologicalComplex.homologyMap
        (cokernel.π ((filtrationFunctor F hF).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n ≫
        HomologicalComplex.homologyMap (cokernel.map _ _ _ _
          (α.naturality (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n := by
    simp only [← HomologicalComplex.homologyMap_comp, cokernel.π_desc]
  have : IsIso (HomologicalComplex.homologyMap (α.app ⊤) n ≫ HomologicalComplex.homologyMap
      (cokernel.π ((filtrationFunctor G hG).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap
    (cokernel.π ((filtrationFunctor G hG).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n)

/-- **The comparison theorem for filtered complexes.** Let `α` be a morphism between the
functors of finite increasing filtrations `F` of `K` and `G` of `L` (`F_a = G_a = ⊥` and
`F_b = G_b = ⊤`). If the induced morphism of spectral sequences is an isomorphism on every object
of some page `r ≥ 2`, then `α.app ⊤` induces isomorphisms in cohomology. -/
theorem isIso_homologyMap_of_isIso_spectralSequence_page (F : ℤ → Subobject K)
    (hF : Monotone F) (G : ℤ → Subobject L) (hG : Monotone G)
    (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG) {a b : ℤ}
    (hFa : F a = ⊥) (hGa : G a = ⊥) (hFb : F b = ⊤) (hGb : G b = ⊤) (r : ℤ) (hr : 2 ≤ r)
    (h : ∀ pq, IsIso (((spectralSequenceMap coreE₂Cohomological
      (spectralObjectMap α)).hom r hr).f pq)) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (α.app ⊤) n) :=
  isIso_homologyMap_app_top_of_isIso_abutment α n <|
    isIso_hom_app_abutment_of_isIso_page (spectralObjectMap α) n
    (fun m i _ _ hi => isZero_spectralObject_H_bot F hF i m
      ((F i).isZero_homology_of_eq_bot (le_bot_iff.mp (hFa ▸ hF hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_bot G hG i m
      ((G i).isZero_homology_of_eq_bot (le_bot_iff.mp (hGa ▸ hG hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_top F hF i m
      ((F i).isZero_homology_cokernel_of_eq_top (top_le_iff.mp (hFb ▸ hF hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_top G hG i m
      ((G i).isZero_homology_cokernel_of_eq_top (top_le_iff.mp (hGb ▸ hG hi)) m)) r hr h


/-- **The morphism of spectral sequences on the first page.** For monomorphisms `F_q ⟶ F_{q+1}`
and `G_q ⟶ G_{q+1}`, under the identifications of the objects of the first pages with the
cohomology of the graded pieces, the morphism of spectral sequences induced by `α : F ⟶ G` is the
map in cohomology of the induced morphism of cokernels. -/
@[reassoc]
lemma spectralSequenceFirstPageXIsoCokernel_hom_naturality
    {F G : EInt ⥤ CochainComplex C ℤ} (α : F ⟶ G) (pq : ℤ × ℤ) (i₁ i₂ : ℤ)
    (hi₁ : i₁ = pq.2) (hi₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2)
    [Mono (F.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))]
    [Mono (G.map (homOfLE (coe_le_coe_of_eq_add_one hi₁ hi₂)))] :
    ((spectralSequenceMap coreE₂Cohomological (spectralObjectMap α)).hom 2 le_rfl).f pq ≫
        (spectralSequenceFirstPageXIsoCokernel G pq i₁ i₂ hi₁ hi₂ n hn).hom =
      (spectralSequenceFirstPageXIsoCokernel F pq i₁ i₂ hi₁ hi₂ n hn).hom ≫
        HomologicalComplex.homologyMap
          (cokernel.map _ _ (α.app i₁) (α.app i₂) (α.naturality _)) n := by
  rw [spectralSequenceMap_hom, spectralSequencePageMap_f, spectralSequenceFirstPageXIsoCokernel_eq,
    spectralSequenceFirstPageXIsoCokernel_eq, Iso.trans_hom, Iso.trans_hom, Category.assoc,
    ← spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom]
  -- The degree `pq.1 + pq.2` is `coreE₂Cohomological.deg pq` only up to unfolding, so the first
  -- page square is applied with `exact` rather than `rw`.
  exact spectralSequencePageXMap_comp_spectralSequenceFirstPageXIso_hom_assoc _ _ _ _ _ _ _ _ _ _

/-- **The morphism of spectral objects on the abutment.** For a morphism `f : K ⟶ L` carrying a
filtration `F` of `K` into a filtration `G` of `L`, under the identifications of the abutments
with the cohomology of `K` and `L`, the morphism of spectral objects induced by `f` is the map in
cohomology of `f`. -/
@[reassoc]
lemma spectralObjectMap_filtrationFunctorMap_abutment_comp
    {F : ℤ → Subobject K} (hF : Monotone F) {G : ℤ → Subobject L} (hG : Monotone G) (f : K ⟶ L)
    (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)) (n : ℤ) :
    ((spectralObjectMap (filtrationFunctorMap hF hG f hf)).hom n).app
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫ (filtrationAbutmentIso G hG n).hom =
      (filtrationAbutmentIso F hF n).hom ≫ HomologicalComplex.homologyMap f n := by
  rw [filtrationAbutmentIso_hom, filtrationAbutmentIso_hom, ← Category.assoc,
    spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom, Category.assoc, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  rw [← cancel_epi (cokernel.π _)]
  simp

end CochainComplex
