/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
import TauCeti.Algebra.Homology.HomologicalComplex.QuasiIso
import TauCeti.Algebra.Homology.SpectralSequence.Comparison

/-!
# The comparison theorem for filtered complexes

A morphism `α : filtrationFunctor F hF ⟶ filtrationFunctor G hG` of filtered complexes induces
the morphism of spectral sequences `spectralSequenceMap coreE₂Cohomological (spectralObjectMap α)`.
If the filtrations are finite and this morphism is an isomorphism on some page, then `α.app ⊤`
induces isomorphisms in cohomology. The last step, from the abutments to the cohomology of the
filtered complexes, holds for all filtrations.

Conversely, if `α` is a quasi-isomorphism `F_q ⟶ G_q` on every piece of the filtrations, it
induces quasi-isomorphisms of the graded pieces `F_{q+1}/F_q ⟶ G_{q+1}/G_q`, so the morphism of
spectral sequences is an isomorphism from the first page on. This holds for all filtrations.

## Main results

* `CochainComplex.isIso_spectralObjectMap_hom_app_abutment_of_isIso_spectralSequence_page`: for
  finite filtrations, an isomorphism on some page gives an isomorphism on the abutments.
* `CochainComplex.isIso_homologyMap_app_top_of_isIso_abutment`: an isomorphism on the abutments
  gives an isomorphism in cohomology.
* `CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page`: the comparison theorem.
* `CochainComplex.isIso_spectralSequenceMap_hom_f_of_quasiIso`: a morphism of filtrations which
  is a quasi-isomorphism on every piece induces isomorphisms on every page `r ≥ 2`.
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
      (α.naturality (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))).symm) n) := by
    rw [hc]
    infer_instance
  have := cokernel.π_of_zero (filtrationFunctor_map_bot F hF ⊤)
  have := cokernel.π_of_zero (filtrationFunctor_map_bot G hG ⊤)
  have e : HomologicalComplex.homologyMap (α.app ⊤) n ≫ HomologicalComplex.homologyMap
      (cokernel.π ((filtrationFunctor G hG).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n =
      HomologicalComplex.homologyMap
        (cokernel.π ((filtrationFunctor F hF).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n ≫
        HomologicalComplex.homologyMap (cokernel.map _ _ _ _
          (α.naturality (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))).symm) n := by
    simp only [← HomologicalComplex.homologyMap_comp, cokernel.π_desc]
  have : IsIso (HomologicalComplex.homologyMap (α.app ⊤) n ≫ HomologicalComplex.homologyMap
      (cokernel.π ((filtrationFunctor G hG).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap
    (cokernel.π ((filtrationFunctor G hG).map (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n)

/-- **The comparison theorem for filtered complexes, on the abutments.** Let `α` be a morphism
between the functors of finite increasing filtrations `F` of `K` and `G` of `L` (`F_a = G_a = ⊥`
and `F_b = G_b = ⊤`). If the induced morphism of spectral sequences is an isomorphism on every
object of some page `r ≥ 2`, then the induced morphism of spectral objects is an isomorphism on the
abutment `H^n(⊥ ≤ ⊤)`. -/
theorem isIso_spectralObjectMap_hom_app_abutment_of_isIso_spectralSequence_page
    (F : ℤ → Subobject K) (hF : Monotone F) (G : ℤ → Subobject L) (hG : Monotone G)
    (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG) {a b : ℤ}
    (hFa : F a = ⊥) (hGa : G a = ⊥) (hFb : F b = ⊤) (hGb : G b = ⊤) (r : ℤ) (hr : 2 ≤ r)
    (h : ∀ pq, IsIso (((spectralSequenceMap coreE₂Cohomological
      (spectralObjectMap α)).hom r hr).f pq)) (n : ℤ) :
    IsIso (((spectralObjectMap α).hom n).app (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) :=
  isIso_hom_app_abutment_of_isIso_page (spectralObjectMap α) n
    (fun m i _ _ hi => isZero_spectralObject_H_bot F hF i m
      ((F i).isZero_homology_of_eq_bot (le_bot_iff.mp (hFa ▸ hF hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_bot G hG i m
      ((G i).isZero_homology_of_eq_bot (le_bot_iff.mp (hGa ▸ hG hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_top F hF i m
      ((F i).isZero_homology_cokernel_of_eq_top (top_le_iff.mp (hFb ▸ hF hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_top G hG i m
      ((G i).isZero_homology_cokernel_of_eq_top (top_le_iff.mp (hGb ▸ hG hi)) m)) r hr h

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
    isIso_spectralObjectMap_hom_app_abutment_of_isIso_spectralSequence_page F hF G hG α hFa hGa
      hFb hGb r hr h n

/-- **The comparison theorem for quasi-isomorphisms of filtrations.** A morphism `α` between the
functors of increasing filtrations `F` of `K` and `G` of `L` which is a quasi-isomorphism
`F_q ⟶ G_q` on every piece induces an isomorphism of spectral sequences on every object of every
page `r ≥ 2`, that is, from the first page on. -/
theorem isIso_spectralSequenceMap_hom_f_of_quasiIso {F : ℤ → Subobject K} {hF : Monotone F}
    {G : ℤ → Subobject L} {hG : Monotone G} (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG)
    (h : ∀ q : ℤ, QuasiIso (α.app q)) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((spectralSequenceMap coreE₂Cohomological (spectralObjectMap α)).hom r hr).f pq) := by
  refine SpectralSequence.Hom.isIso_hom_f_of_le _ 2 le_rfl (fun pq ↦ ?_) r hr pq
  -- On the first page, the morphism is the map in cohomology of the graded pieces.
  have e := spectralSequenceFirstPageXIsoCokernel_hom_naturality α pq pq.2 (pq.2 + 1) rfl rfl _
    rfl
  rw [← Iso.eq_comp_inv] at e
  have := h pq.2
  have := h (pq.2 + 1)
  have := HomologicalComplex.quasiIso_cokernel_map _ _ _ _
    (α.naturality (homOfLE (coe_le_coe_of_eq_add_one (rfl : pq.2 = pq.2) rfl)))
  rw [e]
  infer_instance

end CochainComplex
