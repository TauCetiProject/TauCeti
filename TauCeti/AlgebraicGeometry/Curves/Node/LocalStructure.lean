/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.LocalStructure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Etale
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Flat
import TauCeti.RingTheory.Spectrum.Prime.Finite

/-!
# The singular locus of a nodal curve is étale locally a closed subscheme of the base

Let `X` be a nodal relative curve over `Spec R`. Its singular subscheme `Sing(X/R)` is unramified
over `Spec R`, so by the étale local structure of unramified morphisms it becomes, near any of its
points and after an étale extension `R → E`, a closed subscheme of the base `Spec E`. Here the
singular subscheme of the base change `X_E` is the base change of `Sing(X/R)`
(`AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`).

The first theorem below shows that the singular subscheme of every nodal curve is, near each of its
points and after an étale extension of the base, a closed subscheme of the base.

Over a discrete valuation ring `R` with uniformizer `π`, and at a point of the special fibre, the
étale extension can be taken to be a discrete valuation ring `R'`, étale and local over `R`, in
which `π` remains a uniformizer. The closed subscheme is then identified: it is `Spec R'/(h)` with
`h = 0` or `h = πⁿ` for some `n > 0`, because every proper ideal of a discrete valuation ring is
zero or a positive power of the maximal ideal. These are the two shapes `uv = 0` and `uv = πⁿ` of
the étale local normal form of a node: for the node chart `R'[u,v]/(uv - h)` the singular
subscheme is the same closed subscheme `Spec R'/(h)` of the base
(`TauCeti.NodeAlgebra.singularLocusIso`). Showing that a nodal curve is étale locally such a chart
is not established here.

## Main results

* `AlgebraicGeometry.Scheme.exists_isClosedImmersion_singularLocus_of_isPullback_etale`: after an
  étale extension of the base, an open neighbourhood of a singular point in the singular subscheme
  is an open subscheme of the original singular subscheme and a closed subscheme of the base.
* `AlgebraicGeometry.Scheme.exists_singularLocus_iso_spec_quotient_of_isPullback_etale`: over a
  discrete valuation ring, near a singular point of the special fibre and after an étale extension
  of discrete valuation rings `R → R'`, this closed subscheme is `Spec R'/(h)` with `h = 0` or
  `h = πⁿ`, `n > 0`.

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

/-- **The singular locus of a nodal curve over a discrete valuation ring, étale locally.** Let `R`
be a discrete valuation ring with uniformizer `π`, `X` a nodal relative curve over `Spec R`, and
`z` a point of its singular subscheme lying over the closed point of `Spec R`. There is a discrete
valuation ring `R'`, étale over `R` with `R → R'` local and `π` a uniformizer of `R'`, such that
for every base change `X'` of `X` along `Spec R' ⟶ Spec R`, with projection `g : X' ⟶ X`, some
open subscheme `σ : W ⟶ Sing(X'/R')` containing a point above `z` maps isomorphically onto an open
subscheme of `Sing(X/R)` under the projection `q : Sing(X'/R') ⟶ Sing(X/R)`, and is isomorphic
over `Spec R'` to `Spec R'/(h)`, where `h = 0` or `h = πⁿ` for some `n > 0`. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_singularLocus_iso_spec_quotient_of_isPullback_etale
    [IsDomain R] [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    (X : Scheme.{u}) [X.Over (Spec (.of R))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R))) :
    letI : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
    ∀ z : (X.singularLocus R).subscheme,
    ((X.singularLocus R).subschemeι ≫ (X ↘ Spec (.of R))) z = IsLocalRing.closedPoint R →
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')) (_ : Algebra.Etale R R'),
      Irreducible (algebraMap R R' π) ∧
      ∀ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of R'))) (g : X' ⟶ X)
        (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R)) (Spec.algebraMap R R')),
        letI : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of R')) :=
          (MorphismProperty.of_isPullback H hnodal).syntomic
        ∃ (W : Scheme.{u}) (σ : W ⟶ (X'.singularLocus R').subscheme)
          (q : (X'.singularLocus R').subscheme ⟶ (X.singularLocus R).subscheme) (w : W)
          (h : R) (e : W ≅ Spec (.of (R' ⧸ Ideal.span {algebraMap R R' h}))),
          (h = 0 ∨ ∃ n : ℕ, 0 < n ∧ h = π ^ n) ∧
          q ≫ (X.singularLocus R).subschemeι = (X'.singularLocus R').subschemeι ≫ g ∧
          IsOpenImmersion σ ∧ IsOpenImmersion (σ ≫ q) ∧
          σ ≫ (X'.singularLocus R').subschemeι ≫ (X' ↘ Spec (.of R')) = e.hom ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap R R' h}))) ∧
          q (σ w) = z := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  intro z hz
  have hAffine : AffineAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)) :=
    (atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _)).mp hnodal
  have : Unramified ((X.singularLocus R).subschemeι ≫ (X ↘ Spec (.of R))) :=
    hAffine.unramified_singularLocus
  obtain ⟨E, _, _, _, _, hE₀, hE⟩ := ((X.singularLocus R).subschemeι ≫
    (X ↘ Spec (.of R))).exists_isClosedImmersion_of_isPullback_isLocalRing_etale z
  -- The closed point of `Spec E` lies over the closed point of `Spec R`, so the local étale
  -- `R`-algebra `E` is a discrete valuation ring in which `π` remains a uniformizer. The points
  -- of `Spec` are prime ideals, so `hE₀.trans hz` is an equality of prime ideals.
  have : IsLocalHom (algebraMap R E) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R E)).out 5 1).mp
      congr(PrimeSpectrum.asIdeal $(hE₀.trans hz))
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing R E
  have hmax := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := E)
  have : _root_.IsRegularLocalRing E := IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq hmax
  have : IsDiscreteValuationRing E := IsDiscreteValuationRing.of_flat_of_map_maximalIdeal_eq hmax
  have hπE := IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal_eq hmax hπ
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hπE, fun X' _ g H ↦ ?_⟩
  have : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of E)) :=
    (MorphismProperty.of_isPullback H hnodal).syntomic
  -- `Sing(X'/E)` is the base change of `Sing(X/R)` along `Spec E ⟶ Spec R`.
  have Hsing := Scheme.isPullback_singularLocus_subschemeι H
  obtain ⟨W, σ, w, hσ, hσq, hσg, hw, -⟩ := hE _ _ (Hsing.flip.paste_vert H)
  -- A closed subscheme of `Spec E` is the spectrum of a quotient of `E` by a proper ideal, since
  -- it contains the point `w`.
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hσg
  have hI : I ≠ ⊤ := by
    rintro rfl
    exact isEmptyElim (α := PrimeSpectrum (E ⧸ (⊤ : Ideal E))) (e.hom w)
  -- Every proper ideal of the discrete valuation ring `E` is zero or a positive power of `(π)`.
  obtain ⟨h, hh, rfl⟩ : ∃ h : R, (h = 0 ∨ ∃ n : ℕ, 0 < n ∧ h = π ^ n) ∧
      I = Ideal.span {algebraMap R E h} := by
    rcases eq_or_ne I ⊥ with rfl | hI₀
    · exact ⟨0, .inl rfl, by simp⟩
    obtain ⟨n, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI₀ hπE
    refine ⟨π ^ n, .inr ⟨n, Nat.pos_of_ne_zero fun hn ↦ hI ?_, rfl⟩, by rw [map_pow]⟩
    simp [hn]
  exact ⟨W, σ, _, w, h, e, hh, Hsing.w.symm, hσ, hσq, he, hw⟩

end TauCeti.AlgebraicGeometry
