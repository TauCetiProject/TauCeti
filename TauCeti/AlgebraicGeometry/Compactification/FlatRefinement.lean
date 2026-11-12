/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.BaseChange
public import TauCeti.AlgebraicGeometry.Compactification.Refinement
public import TauCeti.AlgebraicGeometry.Compactification.Uniqueness

/-!
# Base change of schematic common refinements

The schematic common refinement of two base-changed compactifications maps canonically to the
base change of their common refinement. The comparison commutes with both refinement projections
for every base change. For flat base change it is an isomorphism: the pulled-back schematic
closure still has schematically dense interior and hence satisfies the same refinement property.

The comparison requires no density or flatness hypotheses on the original compactifications.
Its construction uses schematic density of the new common refinement to factor its map into the
original product through the original schematic closure.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RA).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti.Compactification

variable {X S T : Scheme.{u}} {f : X ⟶ S}

noncomputable section

/-- The canonical map from the schematic common refinement after arbitrary base change to the
base change of the schematic common refinement. -/
def commonRefinementBaseChange (C₁ C₂ : Compactification f) (g : T ⟶ S) :
    (commonRefinement (C₁.baseChange g) (C₂.baseChange g)).obj ⟶
      (commonRefinement C₁ C₂).obj.baseChange g := by
  let E := commonRefinement (C₁.baseChange g) (C₂.baseChange g)
  let h₁ := commonRefinementFst (C₁.baseChange g) (C₂.baseChange g)
  let h₂ := commonRefinementSnd (C₁.baseChange g) (C₂.baseChange g)
  have h₁p : h₁.hom.h ≫ pullback.snd C₁.p g = E.obj.p := by
    simpa only [baseChange_p] using h₁.hom.h_π
  have h₂p : h₂.hom.h ≫ pullback.snd C₂.p g = E.obj.p := by
    simpa only [baseChange_p] using h₂.hom.h_π
  let k : E.obj.Xbar ⟶ pullback C₁.p C₂.p :=
    pullback.lift (h₁.hom.h ≫ pullback.fst C₁.p g)
      (h₂.hom.h ≫ pullback.fst C₂.p g) (by
        simp only [Category.assoc, pullback.condition]
        rw [← Category.assoc, h₁p, ← Category.assoc, h₂p])
  have hj : E.obj.j ≫ k = pullback.fst f g ≫ C₁.toPullback C₂ := by
    apply pullback.hom_ext <;> simp [k, E, h₁, h₂]
  have H : (C₁.toPullback C₂).imageι.ker ≤ k.ker := by
    rw [← E.obj.j.ker_comp_of_isSchemeTheoreticallyDominant k, hj,
      Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _
  let l := IsClosedImmersion.lift (C₁.toPullback C₂).imageι k H
  have hl : l ≫ (C₁.toPullback C₂).imageι = k := IsClosedImmersion.lift_fac _ _ _
  have hlp : l ≫ (commonRefinement C₁ C₂).obj.p = E.obj.p ≫ g := by
    rw [commonRefinement_p, ← Category.assoc, ← Category.assoc, hl]
    simp only [k, pullback.lift_fst_assoc, Category.assoc]
    rw [pullback.condition, ← Category.assoc, h₁p]
  refine ObjectProperty.homMk
    { h := pullback.lift l E.obj.p hlp
      ι_h := ?_
      h_π := pullback.lift_snd _ _ _ }
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, baseChange_j_fst]
    rw [← cancel_mono (C₁.toPullback C₂).imageι, Category.assoc, hl, hj,
      commonRefinement_j, Category.assoc, Scheme.Hom.toImage_imageι]
  · rw [Category.assoc, pullback.lift_snd]
    exact E.obj.obj.ι_π.trans
      ((commonRefinement C₁ C₂).obj.baseChange g).obj.ι_π.symm

/-- The comparison preserves the first refinement projection. -/
@[reassoc (attr := simp)]
theorem commonRefinementBaseChange_fst (C₁ C₂ : Compactification f) (g : T ⟶ S) :
    commonRefinementBaseChange C₁ C₂ g ≫ baseChangeMap (commonRefinementFst C₁ C₂) g =
      commonRefinementFst (C₁.baseChange g) (C₂.baseChange g) :=
  hom_unique _ _

/-- The comparison preserves the second refinement projection. -/
@[reassoc (attr := simp)]
theorem commonRefinementBaseChange_snd (C₁ C₂ : Compactification f) (g : T ⟶ S) :
    commonRefinementBaseChange C₁ C₂ g ≫ baseChangeMap (commonRefinementSnd C₁ C₂) g =
      commonRefinementSnd (C₁.baseChange g) (C₂.baseChange g) :=
  hom_unique _ _

/-- Flat base change preserves the schematic-closure common refinement. -/
instance isIso_commonRefinementBaseChange (C₁ C₂ : Compactification f) (g : T ⟶ S) [Flat g] :
    IsIso (commonRefinementBaseChange C₁ C₂ g) := by
  let E : DenseCompactification (pullback.snd f g) :=
    ⟨(commonRefinement C₁ C₂).obj.baseChange g,
      (denseCompactificationProperty_iff _ _).mpr inferInstance⟩
  refine ⟨commonRefinementLift E (baseChangeMap (commonRefinementFst C₁ C₂) g)
    (baseChangeMap (commonRefinementSnd C₁ C₂) g), hom_unique _ _, ?_⟩
  exact hom_unique _ _

end

end TauCeti.Compactification
