/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing

/-!
# The first differential of a filtered complex through the connecting map of a pair

For an increasing filtration `F` of a chain complex, regarded as a cochain complex `K` with
`K^{-n} = C_n`, the first differential `d¹ : E¹_{p,q} ⟶ E¹_{p-1,q}` of the homological spectral
sequence is the connecting map `H_{p+q}(F_p/F_{p-1}) ⟶ H_{p+q-1}(F_{p-1}/F_{p-2})` of the short
exact sequence of quotients `F_{p-1}/F_{p-2} ⟶ F_p/F_{p-2} ⟶ F_p/F_{p-1}`
(`CochainComplex.homologicalFiltrationSpectralSequence_first_page_d_eq`). This file factors it
through the connecting map `H_{p+q}(K/F_{p-1}) ⟶ H_{p+q-1}(F_{p-1})` of the pair `F_{p-1} ⊆ K`, the
short exact sequence `F_{p-1} ⟶ K ⟶ K/F_{p-1}` (`CochainComplex.pairSequence`): `d¹` is the map
`F_p/F_{p-1} ⟶ K/F_{p-1}` induced by the inclusion of `F_p`, followed by that connecting map and the
projection `F_{p-1} ⟶ F_{p-1}/F_{p-2}`
(`CochainComplex.homologicalFiltrationSpectralSequence_first_page_d_eq_δ`).

This holds for any subcomplexes `X ≤ Y ≤ Z` of `K`: the connecting map of `Y/X ⟶ Z/X ⟶ Z/Y` is the
map `Z/Y ⟶ K/Y`, the connecting map of `Y ⟶ K ⟶ K/Y` and the projection `Y ⟶ Y/X`
(`CochainComplex.δ_cokernelCompSequence_ofLE`), by naturality of connecting maps along the two
morphisms of short exact sequences out of `Y ⟶ Z ⟶ Z/Y`. When `F_{p-2} = 0` and `F_p = K`, the two
outer maps are isomorphisms, and `d¹` is the connecting map of the pair itself.

## Main definitions

* `CochainComplex.pairSequence`: the short exact sequence `Y ⟶ K ⟶ K/Y` of a subcomplex.

## Main results

* `CochainComplex.δ_cokernelCompSequence_ofLE`: the connecting map of `Y/X ⟶ Z/X ⟶ Z/Y` through
  that of `Y ⟶ K ⟶ K/Y`.
* `CochainComplex.homologicalFiltrationSpectralSequence_first_page_d_eq_δ`: the first differential
  of a filtered complex through the connecting map of the pair `F_{p-1} ⊆ K`.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2.
-/

public section

noncomputable section

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ}

/-- The short exact sequence `Y ⟶ K ⟶ K/Y` of a subcomplex `Y`, whose connecting maps are those of
the long exact sequence of the pair `Y ⊆ K`. It is `ShortComplex.cokernelSequence Y.arrow`, written
as a reducible structure so that its terms are `Y`, `K` and `cokernel Y.arrow` up to reducible
unfolding. -/
abbrev pairSequence (Y : Subobject K) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk Y.arrow (cokernel.π Y.arrow) (cokernel.condition _)

/-- The sequence `Y ⟶ K ⟶ K/Y` of a subcomplex is short exact. -/
lemma pairSequence_shortExact (Y : Subobject K) : (pairSequence Y).ShortExact :=
  TauCeti.cokernelSequence_shortExact Y.arrow

/-- For subobjects `X ≤ Y ≤ Z` of `K`, the connecting map of the sequence
`Y/X ⟶ Z/X ⟶ Z/Y` of quotients factors through the connecting map of `Y ⟶ K ⟶ K/Y`: it is the map
`Z/Y ⟶ K/Y` induced by the inclusion of `Z`, followed by the connecting map of `Y ⟶ K ⟶ K/Y` and
the projection `Y ⟶ Y/X`. -/
theorem δ_cokernelCompSequence_ofLE {X Y Z : Subobject K} (h₁ : X ≤ Y) (h₂ : Y ≤ Z)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (TauCeti.cokernelCompSequence_shortExact (Subobject.ofLE X Y h₁)
        (Subobject.ofLE Y Z h₂)).δ i j hij =
      HomologicalComplex.homologyMap
          (cokernel.map (Subobject.ofLE Y Z h₂) Y.arrow (𝟙 _) Z.arrow (by simp)) i ≫
        (pairSequence_shortExact Y).δ i j hij ≫
        HomologicalComplex.homologyMap (cokernel.π (Subobject.ofLE X Y h₁)) j := by
  -- The morphism from `Y ⟶ Z ⟶ Z/Y` to `Y/X ⟶ Z/X ⟶ Z/Y` given by the cokernel projections.
  have h₁₂ := HomologicalComplex.HomologySequence.δ_naturality
    (TauCeti.cokernelSequenceToCokernelCompSequence (Subobject.ofLE X Y h₁)
      (Subobject.ofLE Y Z h₂)) (TauCeti.cokernelSequence_shortExact _)
    (TauCeti.cokernelCompSequence_shortExact _ _) i j hij
  simp only [TauCeti.cokernelSequenceToCokernelCompSequence_τ₁,
    TauCeti.cokernelSequenceToCokernelCompSequence_τ₃] at h₁₂
  -- The morphism from `Y ⟶ Z ⟶ Z/Y` to `Y ⟶ K ⟶ K/Y` given by the inclusion of `Z`.
  have h₂₃ := HomologicalComplex.HomologySequence.δ_naturality
    (S₁ := ShortComplex.cokernelSequence (Subobject.ofLE Y Z h₂)) (S₂ := pairSequence Y)
    (ShortComplex.homMk (𝟙 (Y : CochainComplex C ℤ)) Z.arrow
      (cokernel.map (Subobject.ofLE Y Z h₂) Y.arrow (𝟙 _) Z.arrow (by simp))
      ((Category.id_comp _).trans (Subobject.ofLE_arrow _).symm) (cokernel.π_desc _ _ _).symm)
    (TauCeti.cokernelSequence_shortExact _) (pairSequence_shortExact Y) i j hij
  -- The identity components act as identities in homology. The equations are composed as terms:
  -- the sequence `Y ⟶ Z ⟶ Z/Y` is `ShortComplex.cokernelSequence`, whose terms are reached only by
  -- unfolding its definition, so rewriting with them would need that unfolding.
  have e₁ := h₁₂.trans ((congrArg (· ≫ _) (HomologicalComplex.homologyMap_id _ i)).trans
    (Category.id_comp _))
  have e₂ := ((congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_id _ j)).trans
    (Category.comp_id _)).symm.trans h₂₃
  exact e₁.symm.trans ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))

variable (F : ℤ → Subobject K) (hF : Monotone F)

/-- **The first differential of a filtered complex through the connecting map of a pair.** The
differential `d¹ : E¹_{p,q} ⟶ E¹_{p-1,q}`, from `H_{p+q}(F_p/F_{p-1})` to
`H_{p+q-1}(F_{p-1}/F_{p-2})`, is the map `F_p/F_{p-1} ⟶ K/F_{p-1}` induced by the inclusion
`F_p ⊆ K`, followed by the connecting map of the pair `F_{p-1} ⊆ K` and the projection
`F_{p-1} ⟶ F_{p-1}/F_{p-2}`. -/
theorem homologicalFiltrationSpectralSequence_first_page_d_eq_δ (p q : ℤ) :
    ((homologicalFiltrationSpectralSequence F hF).page 1).d (p, q) (p - 1, q) =
      (homologicalFiltrationSpectralSequenceFirstPageXIso F hF p q).hom ≫
        (HomologicalComplex.homologyMap
          (cokernel.map (Subobject.ofLE (F (p - 1)) (F p) (hF (by lia))) (F (p - 1)).arrow (𝟙 _)
            (F p).arrow (by simp)) _ ≫
        (pairSequence_shortExact (F (p - 1))).δ (-(p + q)) (-(p - 1 + q))
          (by simp only [ComplexShape.up_Rel]; lia) ≫
        HomologicalComplex.homologyMap
          (cokernel.π (Subobject.ofLE (F (p - 1 - 1)) (F (p - 1)) (hF (by lia)))) _) ≫
        (homologicalFiltrationSpectralSequenceFirstPageXIso F hF (p - 1) q).inv := by
  rw [homologicalFiltrationSpectralSequence_first_page_d_eq, δ_cokernelCompSequence_ofLE]

end CochainComplex
