/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.SectionDegree
public import TauCeti.AlgebraicGeometry.Morphisms.Proper

/-!
# Ample line bundles have positive degree on proper curves

Let `X` be an integral scheme, proper over a field `k` with fibres of dimension at most one, with
finite-dimensional `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, and with more than one point; for instance an
integral proper curve over `k`, singular or not. Then every ample line bundle on `X` has positive
Euler-characteristic degree (`TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.eulerDegree_pos`).

The argument uses only the definition of ampleness. Some positive power `L^⊗n` has a global section
`s` whose nonvanishing locus `X_s` is affine and nonempty. Since `X` has more than one point, it is
not affine (`AlgebraicGeometry.Scheme.subsingleton_of_isAffine_of_universallyClosed`), so `s`
vanishes somewhere. A nonzero section of a line bundle has nonnegative degree, and degree zero only
when the line bundle is trivial
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_eq_zero_iff_of_ne_zero`).
On the trivial line bundle a section vanishes everywhere or nowhere, because the global functions
on `X` form a field
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.nonvanishingLocus_eq_bot_or_eq_top_of_mk_eq_one`).
Hence `n · deg L = deg L^⊗n > 0`.

This is one direction of the ampleness criterion on a proper curve, for an integral curve: an ample
line bundle has positive degree. The converse, that a line bundle of positive degree is ample, is
not proved here.

## Main results

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.nonvanishingLocus_eq_bot_or_eq_top_of_mk_eq_one`: on
  an integral scheme universally closed over a field, a global section of a trivial line bundle
  vanishes everywhere or nowhere.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.eulerDegree_pos`: an ample line bundle on an
  integral proper curve has positive degree.

## References

* [The Stacks Project, Section 33.44](https://stacks.math.columbia.edu/tag/0AYQ), *Degrees on
  curves*, where an invertible module on a proper curve over a field is shown to be ample exactly
  when its degree on every irreducible component is positive.
* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Corollary 3.3.
-/

public section

open CategoryTheory AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules (Cohomology)

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

namespace InvertibleSheaf

/-- On an integral scheme universally closed over a field, for instance an integral proper curve,
a global section of a line bundle of trivial class vanishes either everywhere or nowhere: under an
isomorphism with `𝒪_X` it becomes a global function, and the global functions form a field. -/
theorem nonvanishingLocus_eq_bot_or_eq_top_of_mk_eq_one [UniversallyClosed (X ↘ Spec (.of k))]
    {L : InvertibleSheaf X} (hL : LineBundleClass.mk L = 1) (s : Γ(L.obj, ⊤)) :
    L.obj.nonvanishingLocus s = ⊥ ∨ L.obj.nonvanishingLocus s = ⊤ := by
  obtain ⟨r, hr⟩ : L.obj.nonvanishingLocus s ∈ Set.range (X.basicOpen (U := ⊤)) := by
    rw [← LineBundleClass.range_nonvanishingLocus_eq_of_mk_eq_one hL ⊤]
    exact ⟨s, rfl⟩
  let := (isField_of_universallyClosed k (X ↘ Spec (.of k))).toField
  rw [← hr]
  obtain rfl | hr₀ := eq_or_ne r 0
  · exact Or.inl (X.basicOpen_zero ⊤)
  · exact Or.inr (X.basicOpen_of_isUnit hr₀.isUnit)

end InvertibleSheaf

namespace LineBundleClass

variable [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **An ample line bundle on a proper curve has positive degree.** Let `X` be an integral scheme
with more than one point, proper over `k` with fibres of dimension at most one, such that
`H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` are finite-dimensional. Then every ample line-bundle class on `X`
has positive Euler-characteristic degree. The curve `X` may be singular, and `k` is arbitrary. -/
theorem IsAmple.eulerDegree_pos [Nontrivial X] {a : LineBundleClass X} (ha : a.IsAmple) :
    0 < eulerDegree k a := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨n, -, L, hL, s, hx, hs⟩ := ha.exists_isAffineOpen_nonvanishingLocus x
  have hs₀ : s ≠ 0 := by
    rintro rfl
    simp at hx
  -- The section `s` vanishes somewhere, since its nonvanishing locus is affine but `X` is not.
  have hne : L.obj.nonvanishingLocus s ≠ ⊤ := fun htop ↦ by
    rw [htop] at hs
    -- `IsAffineOpen U` is by definition `IsAffine U`.
    have : IsAffine (⊤ : X.Opens) := hs
    have : IsAffine X := IsAffine.of_isIso X.topIso.inv
    exact not_subsingleton X
      (Scheme.subsingleton_of_isAffine_of_universallyClosed (X ↘ Spec (.of k)))
  -- So `L` is not trivial, and its nonzero section gives it positive degree.
  have hdeg : 0 < L.eulerDegree k := by
    refine (L.eulerDegree_nonneg_of_ne_zero k s hs₀).lt_of_ne' fun h ↦ hne ?_
    refine (InvertibleSheaf.nonvanishingLocus_eq_bot_or_eq_top_of_mk_eq_one k
      ((L.eulerDegree_eq_zero_iff_of_ne_zero k s hs₀).mp h) s).resolve_left fun hbot ↦ ?_
    simp [hbot] at hx
  rw [← eulerDegree_mk, hL, eulerDegree_pow_of_isIntegral] at hdeg
  exact pos_of_mul_pos_right hdeg (Int.natCast_nonneg n)

end LineBundleClass

end TauCeti.AlgebraicGeometry
