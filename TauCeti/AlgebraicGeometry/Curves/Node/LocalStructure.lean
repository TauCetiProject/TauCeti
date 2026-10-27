/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.LocalStructure

/-!
# The singular locus of a nodal curve is étale locally a closed subscheme of the base

Let `X` be a nodal relative curve over `Spec R`. Its singular subscheme `Sing(X/R)` is unramified
over `Spec R`, so by the étale local structure of unramified morphisms it becomes, near any of its
points and after an étale extension `R → E`, a closed subscheme of the base `Spec E`. Here the
singular subscheme of the base change `X_E` is the base change of `Sing(X/R)`
(`AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`).

The theorem below shows that the singular subscheme of every nodal curve is, near each of its
points and after an étale extension of the base, a closed subscheme of the base. It does not
identify that closed subscheme. For the node chart `R[u,v]/(uv - a)` the singular subscheme is
the principal closed subscheme `Spec R/(a)` of the base (`TauCeti.NodeAlgebra.singularLocusIso`);
showing that a nodal curve is étale locally such a chart is not established here.

## Main result

* `AlgebraicGeometry.Scheme.exists_isClosedImmersion_singularLocus_of_isPullback_etale`: after an
  étale extension of the base, an open neighbourhood of a singular point in the singular subscheme
  is an open subscheme of the original singular subscheme and a closed subscheme of the base.

## References

* [Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): families
  of nodal curves.
* The Stacks Project, Chapter *Étale Morphisms of Schemes*, Section *Étale local structure of
  unramified morphisms*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- **The singular locus of a nodal curve is étale locally a closed subscheme of the base.** Let
`X` be a nodal relative curve over `Spec R` and `z` a point of its singular subscheme. There is an
étale `R`-algebra `E` such that, for every base change `X'` of `X` along `Spec E ⟶ Spec R` with
projection `g : X' ⟶ X`, some open subscheme `σ : W ⟶ Sing(X'/E)` containing a point above `z`
maps isomorphically onto an open subscheme of `Sing(X/R)` under the projection
`q : Sing(X'/E) ⟶ Sing(X/R)` and is a closed subscheme of `Spec E`. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_isClosedImmersion_singularLocus_of_isPullback_etale
    (X : Scheme.{u}) [X.Over (Spec (.of R))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R))) :
    letI : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
    ∀ z : (X.singularLocus R).subscheme,
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E),
      ∀ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of E))) (g : X' ⟶ X)
        (H : IsPullback g (X' ↘ Spec (.of E)) (X ↘ Spec (.of R)) (Spec.algebraMap R E)),
        letI : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of E)) :=
          (MorphismProperty.of_isPullback H hnodal).syntomic
        ∃ (W : Scheme.{u}) (σ : W ⟶ (X'.singularLocus E).subscheme)
          (q : (X'.singularLocus E).subscheme ⟶ (X.singularLocus R).subscheme) (w : W),
          q ≫ (X.singularLocus R).subschemeι = (X'.singularLocus E).subschemeι ≫ g ∧
          IsOpenImmersion σ ∧ IsOpenImmersion (σ ≫ q) ∧
          IsClosedImmersion (σ ≫ (X'.singularLocus E).subschemeι ≫ (X' ↘ Spec (.of E))) ∧
          q (σ w) = z := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  intro z
  have hAffine : AffineAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)) :=
    (atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _)).mp hnodal
  have : Unramified ((X.singularLocus R).subschemeι ≫ (X ↘ Spec (.of R))) :=
    hAffine.unramified_singularLocus
  obtain ⟨E, _, _, _, hE⟩ := ((X.singularLocus R).subschemeι ≫
    (X ↘ Spec (.of R))).exists_isClosedImmersion_of_isPullback_etale z
  refine ⟨E, inferInstance, inferInstance, inferInstance, fun X' _ g H ↦ ?_⟩
  have : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of E)) :=
    (MorphismProperty.of_isPullback H hnodal).syntomic
  -- `Sing(X'/E)` is the base change of `Sing(X/R)` along `Spec E ⟶ Spec R`.
  have Hsing := Scheme.isPullback_singularLocus_subschemeι H
  obtain ⟨W, σ, w, hσ, hσq, hσg, hw⟩ := hE _ _ (Hsing.flip.paste_vert H)
  exact ⟨W, σ, _, w, Hsing.w.symm, hσ, hσq, by simpa using hσg, hw⟩

end TauCeti.AlgebraicGeometry
