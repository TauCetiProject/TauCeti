/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The connecting map of a pair of subcomplexes

For a subcomplex `Y` of a homological complex `K` of any shape, the short exact sequence
`Y ⟶ K ⟶ K/Y` (`HomologicalComplex.pairSequence`) gives the long exact homology sequence of the
pair `Y ⊆ K`.

For subcomplexes `X ≤ Y ≤ Z` of `K`, the connecting map of the sequence of quotients
`Y/X ⟶ Z/X ⟶ Z/Y` is the map `Z/Y ⟶ K/Y` induced by the inclusion of `Z`, followed by the
connecting map of `Y ⟶ K ⟶ K/Y` and the projection `Y ⟶ Y/X`
(`HomologicalComplex.δ_cokernelCompSequence_ofLE`). This follows by naturality of connecting maps
along the two morphisms of short exact sequences out of `Y ⟶ Z ⟶ Z/Y`.

## Main definitions

* `HomologicalComplex.pairSequence`: the short exact sequence `Y ⟶ K ⟶ K/Y` of a subcomplex.

## Main results

* `HomologicalComplex.pairSequence_shortExact`: the sequence `Y ⟶ K ⟶ K/Y` is short exact.
* `HomologicalComplex.δ_cokernelCompSequence_ofLE`: the connecting map of `Y/X ⟶ Z/X ⟶ Z/Y` through
  that of `Y ⟶ K ⟶ K/Y`.
-/

public section

noncomputable section

namespace HomologicalComplex

open CategoryTheory Limits

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- The short exact sequence `Y ⟶ K ⟶ K/Y` of a subcomplex `Y`, whose connecting maps are those of
the long exact sequence of the pair `Y ⊆ K`. It is `ShortComplex.cokernelSequence Y.arrow`, written
as a reducible structure so that its terms are `Y`, `K` and `cokernel Y.arrow` up to reducible
unfolding. -/
abbrev pairSequence (Y : Subobject K) : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk Y.arrow (cokernel.π Y.arrow) (cokernel.condition _)

/-- The sequence `Y ⟶ K ⟶ K/Y` of a subcomplex is short exact. -/
lemma pairSequence_shortExact (Y : Subobject K) : (pairSequence Y).ShortExact :=
  TauCeti.cokernelSequence_shortExact Y.arrow

/-- For subobjects `X ≤ Y ≤ Z` of `K`, the connecting map of the sequence
`Y/X ⟶ Z/X ⟶ Z/Y` of quotients factors through the connecting map of `Y ⟶ K ⟶ K/Y`: it is the map
`Z/Y ⟶ K/Y` induced by the inclusion of `Z`, followed by the connecting map of `Y ⟶ K ⟶ K/Y` and
the projection `Y ⟶ Y/X`. -/
theorem δ_cokernelCompSequence_ofLE {X Y Z : Subobject K} (h₁ : X ≤ Y) (h₂ : Y ≤ Z)
    (i j : ι) (hij : c.Rel i j) :
    (TauCeti.cokernelCompSequence_shortExact (Subobject.ofLE X Y h₁)
        (Subobject.ofLE Y Z h₂)).δ i j hij =
      homologyMap (cokernel.map (Subobject.ofLE Y Z h₂) Y.arrow (𝟙 _) Z.arrow (by simp)) i ≫
        (pairSequence_shortExact Y).δ i j hij ≫
        homologyMap (cokernel.π (Subobject.ofLE X Y h₁)) j := by
  -- The morphism from `Y ⟶ Z ⟶ Z/Y` to `Y/X ⟶ Z/X ⟶ Z/Y` given by the cokernel projections.
  have h₁₂ := HomologySequence.δ_naturality
    (TauCeti.cokernelSequenceToCokernelCompSequence (Subobject.ofLE X Y h₁)
      (Subobject.ofLE Y Z h₂)) (TauCeti.cokernelSequence_shortExact _)
    (TauCeti.cokernelCompSequence_shortExact _ _) i j hij
  simp only [TauCeti.cokernelSequenceToCokernelCompSequence_τ₁,
    TauCeti.cokernelSequenceToCokernelCompSequence_τ₃] at h₁₂
  -- The morphism from `Y ⟶ Z ⟶ Z/Y` to `Y ⟶ K ⟶ K/Y` given by the inclusion of `Z`.
  have h₂₃ := HomologySequence.δ_naturality
    (S₁ := ShortComplex.cokernelSequence (Subobject.ofLE Y Z h₂)) (S₂ := pairSequence Y)
    (ShortComplex.homMk (𝟙 (Y : HomologicalComplex C c)) Z.arrow
      (cokernel.map (Subobject.ofLE Y Z h₂) Y.arrow (𝟙 _) Z.arrow (by simp))
      ((Category.id_comp _).trans (Subobject.ofLE_arrow _).symm) (cokernel.π_desc _ _ _).symm)
    (TauCeti.cokernelSequence_shortExact _) (pairSequence_shortExact Y) i j hij
  -- The identity components act as identities in homology. The equations are composed as terms:
  -- the sequence `Y ⟶ Z ⟶ Z/Y` is `ShortComplex.cokernelSequence`, whose terms are reached only by
  -- unfolding its definition, so rewriting with them would need that unfolding.
  have e₁ := h₁₂.trans ((congrArg (· ≫ _) (homologyMap_id _ i)).trans (Category.id_comp _))
  have e₂ := ((congrArg (_ ≫ ·) (homologyMap_id _ j)).trans (Category.comp_id _)).symm.trans h₂₃
  exact e₁.symm.trans ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))

end HomologicalComplex
