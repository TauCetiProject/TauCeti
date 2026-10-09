/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Graph

/-!
# Relative effective Cartier divisors of degree one are sections

Let `f : X ⟶ S` be locally of finite presentation with fibres of dimension at most one, and let
`D` be a relative effective Cartier divisor on `X` over `S` which is proper over `S`. Then `D` is
finite locally free over `S`, and it maps isomorphically to `S` exactly when its degree, the rank
of `D ⟶ S`, is `1` at every point of `S`. When `f` is moreover separated, `D` is then the divisor
`[s]` of a unique section `s` of `f`, the section
`AlgebraicGeometry.Scheme.IdealSheafData.sectionOfIsIso` cut out by `D`. Conversely, the divisor
of a section of a separated `f` has degree one.

Applied to the base changes `X_T = T ×_S X ⟶ T` of a proper `f`, this identifies the `T`-points
of `X` over `S` with the relative effective Cartier divisors of degree one on `X_T` over `T`, a
point `x` corresponding to its graph `Γₓ`
(`TauCeti.AlgebraicGeometry.exists_ker_graphSection_eq_iff_finrank_eq_one`).
When `f` is smooth of relative dimension one, every graph is a relative effective Cartier divisor,
and this is the statement that the graph divisor `TauCeti.AlgebraicGeometry.graphDivisor` is
injective, by `TauCeti.AlgebraicGeometry.graphDivisor_app_injective`, with image the divisors of
degree one. Since `graphDivisor` is a natural transformation, the correspondence between points
and divisors of degree one commutes with arbitrary base change `T' ⟶ T`.

## Main results

In the namespace `AlgebraicGeometry.Scheme.IdealSheafData`:

* `IsRelativeEffectiveCartier.isIso_subschemeι_comp_iff_finrank_eq_one`: a proper relative
  effective Cartier divisor on a relative curve maps isomorphically to the base exactly when it
  has degree one;
* `IsRelativeEffectiveCartier.exists_comp_eq_id_and_ker_eq_iff_finrank_eq_one`: it is the
  divisor of a section exactly when it has degree one.

In the namespace `TauCeti.AlgebraicGeometry`:

* `exists_ker_graphSection_eq_iff_finrank_eq_one`: the graphs of the `T`-points of `X` over `S`
  are exactly the relative effective Cartier divisors of degree one on `X_T` over `T`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.2.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}} {I : X.IdealSheafData} {f : X ⟶ S}

/-- **A relative effective Cartier divisor maps isomorphically to the base exactly when it has
degree one.** If `f : X ⟶ S` is locally of finite presentation with fibres of dimension at most
one, then the closed subscheme of a relative effective Cartier divisor on `X` over `S` which is
proper over `S` maps isomorphically to `S` if and only if its rank is `1` at every point of `S`. -/
theorem IsRelativeEffectiveCartier.isIso_subschemeι_comp_iff_finrank_eq_one
    [LocallyOfFinitePresentation f]
    [TauCeti.AlgebraicGeometry.RelativeDimensionLE 1 f] [IsProper (I.subschemeι ≫ f)]
    (hI : I.IsRelativeEffectiveCartier f) :
    IsIso (I.subschemeι ≫ f) ↔ (I.subschemeι ≫ f).finrank = 1 := by
  -- The divisor is finite, flat and locally of finite presentation over `S`.
  have := hI.isFinite_iff_isProper.mpr inferInstance
  have := hI.flat
  have := TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier
    hI.isEffectiveCartier (f := f)
  exact Scheme.Hom.isIso_iff_finrank_eq _

/-- **Relative effective Cartier divisors of degree one are sections.** If `f : X ⟶ S` is
separated and locally of finite presentation with fibres of dimension at most one, then a relative
effective Cartier divisor on `X` over `S` which is proper over `S` is the divisor of a section of
`f` if and only if it has degree one, that is, rank `1` over every point of `S`. The section is
then unique (`AlgebraicGeometry.Scheme.Hom.ker_eq_ker_iff_of_comp_eq_id`); it is
`AlgebraicGeometry.Scheme.IdealSheafData.sectionOfIsIso`. -/
theorem IsRelativeEffectiveCartier.exists_comp_eq_id_and_ker_eq_iff_finrank_eq_one
    [IsSeparated f] [LocallyOfFinitePresentation f]
    [TauCeti.AlgebraicGeometry.RelativeDimensionLE 1 f] [IsProper (I.subschemeι ≫ f)]
    (hI : I.IsRelativeEffectiveCartier f) :
    (∃ s : S ⟶ X, s ≫ f = 𝟙 S ∧ s.ker = I) ↔ (I.subschemeι ≫ f).finrank = 1 := by
  rw [← isIso_subschemeι_comp_iff, hI.isIso_subschemeι_comp_iff_finrank_eq_one]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {S X : Scheme.{u}} {f : X ⟶ S} [IsProper f] [LocallyOfFinitePresentation f]
  [RelativeDimensionLE 1 f]

/-- **The graphs of points are the divisors of degree one.** Let `f : X ⟶ S` be proper and
locally of finite presentation with fibres of dimension at most one. For a scheme `T` over `S`, a
relative effective Cartier divisor `D` on `X_T = T ×_S X` over `T` is the graph `Γₓ` of a
`T`-point `x` of `X` over `S` if and only if `D` has degree one over `T`. The point `x` is then
unique, by `ker_graphSection_inj`. -/
theorem exists_ker_graphSection_eq_iff_finrank_eq_one {T : Over S}
    {D : (pullback T.hom f).IdealSheafData}
    (hD : D.IsRelativeEffectiveCartier (pullback.fst T.hom f)) :
    (∃ x : T ⟶ Over.mk f, (graphSection x).ker = D) ↔
      (D.subschemeι ≫ pullback.fst T.hom f).finrank = 1 := by
  rw [← hD.exists_comp_eq_id_and_ker_eq_iff_finrank_eq_one]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨graphSection x, graphSection_fst x, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    -- The section `s` is the graph of its second component `s ≫ pullback.snd`.
    refine ⟨Over.homMk (s ≫ pullback.snd T.hom f)
      (by simp [← pullback.condition, reassoc_of% hs]), ?_⟩
    congr 1
    apply pullback.hom_ext <;> simp [hs]

end TauCeti.AlgebraicGeometry
