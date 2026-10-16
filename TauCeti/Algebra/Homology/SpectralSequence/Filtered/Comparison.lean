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
induces isomorphisms in cohomology.

## Main results

* `CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page`: the comparison theorem.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K L : CochainComplex C ℤ}

/-- **The comparison theorem for filtered complexes.** Let `α` be a morphism between the
functors of finite increasing filtrations `F` of `K` and `G` of `L` (`F_a = G_a = ⊥` and
`F_b = G_b = ⊤`). If the induced morphism of spectral sequences is an isomorphism on every object
of some page `r ≥ 2`, then `α.app ⊤` induces isomorphisms in cohomology. -/
theorem isIso_homologyMap_of_isIso_spectralSequence_page (F : ℤ → Subobject K)
    (hF : Monotone F) (G : ℤ → Subobject L) (hG : Monotone G)
    (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG) {a b : ℤ} (hab : a ≤ b)
    (hFa : F a = ⊥) (hGa : G a = ⊥) (hFb : F b = ⊤) (hGb : G b = ⊤) (r : ℤ) (hr : 2 ≤ r)
    (h : ∀ pq, IsIso (((spectralSequenceMap coreE₂Cohomological
      (spectralObjectMap α)).hom r hr).f pq)) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (α.app ⊤) n) := by
  have hA := isIso_hom_app_abutment_of_isIso_page (spectralObjectMap α) hab n
    (fun m i _ _ hi => isZero_spectralObject_H_bot F hF i m
      ((F i).isZero_homology_of_eq_bot (le_bot_iff.mp (hFa ▸ hF hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_bot G hG i m
      ((G i).isZero_homology_of_eq_bot (le_bot_iff.mp (hGa ▸ hG hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_top F hF i m
      ((F i).isZero_homology_cokernel_of_eq_top (top_le_iff.mp (hFb ▸ hF hi)) m))
    (fun m i _ _ hi => isZero_spectralObject_H_top G hG i m
      ((G i).isZero_homology_cokernel_of_eq_top (top_le_iff.mp (hGb ▸ hG hi)) m)) r hr h
  have hc := (Iso.eq_inv_comp _).mpr
    (spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom α
      (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)) n).symm
  have : IsIso (HomologicalComplex.homologyMap (cokernel.map _ _ _ _
      (α.naturality (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) n) := by
    rw [hc]
    infer_instance
  have := cokernel.π_of_zero (filtrationFunctor_map_bot_top F hF)
  have := cokernel.π_of_zero (filtrationFunctor_map_bot_top G hG)
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

end CochainComplex
