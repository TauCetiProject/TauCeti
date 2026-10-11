/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.AlgebraicGeometry.Curves.Node.Nodal

/-!
# The singular locus of a proper nodal curve

For a proper nodal curve over a field, the relative singular subscheme is finite étale over the
field. Finiteness follows from properness and the fact that a nodal singular locus is
unramified; flatness over a field then gives étaleness. This is the scheme that records the
nodes before passing to a separable extension that labels them.

## References

* [Stacks Project, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

/-- The singular subscheme of a proper nodal curve over a field is finite étale over that field.
The nodal hypothesis is expressed by the scheme-theoretic criterion for an affine base. -/
theorem _root_.AlgebraicGeometry.Scheme.isFinite_etale_singularLocus
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
    IsFinite ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) ∧
      Etale ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  let s := (X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))
  have hfu : FormallyUnramified s := hnodal.singular_formallyUnramified
  have hlfp : LocallyOfFinitePresentation s := by
    dsimp [s]
    infer_instance
  have hflat : Flat s := by
    have : Subsingleton (Spec (.of K)) := inferInstance
    have : IsIntegral (Spec (.of K)) := inferInstance
    exact inferInstance
  have heta : Etale s :=
    Etale.of_formallyUnramified_of_flat s
  have hqf : LocallyQuasiFinite s := by
    rw [locallyQuasiFinite_iff]
    intro U hU V hV e
    have hform := hfu.formallyUnramified_appLE hU hV e
    have htype : (s.appLE U V e).hom.FiniteType :=
      (show LocallyOfFiniteType s from inferInstance).finiteType_appLE hU hV e
    algebraize [(s.appLE U V e).hom]
    have : Algebra.EssFiniteType _ _ := htype.essFiniteType
    have : Algebra.FormallyUnramified _ _ := hform
    exact RingHom.quasiFinite_algebraMap.mpr inferInstance
  have hproper : IsProper s := by
    dsimp [s]
    infer_instance
  have hfinite : IsFinite s := IsFinite.of_isProper_of_locallyQuasiFinite s
  exact ⟨hfinite, heta⟩

end TauCeti.AlgebraicGeometry
