/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness

/-!
# Degree and `Pic⁰` on smooth proper curves

On a proper integral curve over a field `k` whose points have codimension at most one, whose
codimension-one local rings are discrete valuation rings and whose `H¹(X, 𝒪_X)` is
finite-dimensional, principal divisors have degree zero and the Euler-characteristic degree
`χ(L) - χ(𝒪_X)` of a line bundle is the degree of any of its divisors. This file proves both on
every proper integral scheme smooth of relative dimension one over `k`, assuming only the
instances needed to state them. Neither a rational point nor perfectness of `k` is assumed.

Smoothness gives regular local rings, hence discrete valuation rings at the points of codimension
one; relative dimension one bounds the codimension of every point by one
(`TauCeti.AlgebraicGeometry.coheight_le_of_relativeDimensionLE_of_field`); and properness gives
finite-dimensional `H¹(X, 𝒪_X)`. A smooth proper geometrically connected curve is integral, by
`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`, so the results apply to it.

The degree of a line bundle does not change under an extension `K/k` of the base field
(`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback`). Consequently a line-bundle
class on a proper curve lies in `Pic⁰` exactly when its pullback to the base change `X_K` lies in
`Pic⁰ X_K`: `Pic⁰ X` is the preimage of `Pic⁰ X_K` under pullback. This uses no smoothness.

## Main results

* `SchemeWeilDivisor.relativeDegree_principalDivisor_of_smooth`: principal divisors on a proper
  integral smooth curve have degree zero;
* `InvertibleSheaf.eulerDegree_eq_relativeDegree_of_smooth`: on such a curve, the
  Euler-characteristic degree of `𝒪_X(D)` is `Σ_y D(y) [κ(y) : k]`;
* `LineBundleClass.pullback_mem_picZero_iff` and `LineBundleClass.comap_picZero`: `Pic⁰` is
  compatible with extension of the base field.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Corollary 6.10, Chapter III,
  Proposition 9.3, and Chapter IV, Section 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **A principal divisor on a smooth proper curve has degree zero.** On a proper integral scheme
smooth of relative dimension one over a field `k`, the divisor of a nonzero rational function
has degree `Σ_y ord_y(f) [κ(y) : k] = 0`. -/
theorem relativeDegree_principalDivisor_of_smooth [IsNoetherian X]
    (f : Additive X.functionFieldˣ) :
    relativeDegree (X ↘ Spec (.of k))
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor f) = 0 := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := isDiscreteValuationRing_stalk_of_smooth k (X := X)
  have := finiteDimensional_cohomology_one_trivial_of_smooth k X
  exact relativeDegree_principalDivisor k
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k))) f

end SchemeWeilDivisor

namespace InvertibleSheaf

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **The degree of a line bundle on a smooth proper curve is the degree of its divisors.** On a
proper integral scheme smooth of relative dimension one over a field `k`, a line bundle
`L ≅ 𝒪_X(D)` has `χ(L) - χ(𝒪_X) = Σ_y D(y) [κ(y) : k]`. -/
theorem eulerDegree_eq_relativeDegree_of_smooth [IsLocallyNoetherian X]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    {L : InvertibleSheaf X} {D : SchemeWeilDivisor X} (e : L.obj ≅ SchemeWeilDivisor.sheaf D) :
    L.eulerDegree k = SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D := by
  have := finiteDimensional_cohomology_one_trivial_of_smooth k X
  exact eulerDegree_eq_relativeDegree k
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k))) e

end InvertibleSheaf

namespace LineBundleClass

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [IsIntegral X] [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [Fact (∀ y : X, coheight y ≤ 1)] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  [IsIntegral Y] [∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y))]
  [Fact (∀ y : Y, coheight y ≤ 1)] [IsProper (Y ↘ Spec (.of K))]
  [FiniteDimensional K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1)]

include H in
/-- **`Pic⁰` is compatible with extension of the base field.** Let `X` be a proper integral curve
over `k` whose codimension-one local rings are discrete valuation rings and whose `H¹(X, 𝒪_X)` is
finite-dimensional, and let `Y = X_K` be its base change to a field extension `K`, satisfying the
same hypotheses over `K`. A line-bundle class on `X` has degree zero exactly when its pullback to
`X_K` does. -/
theorem pullback_mem_picZero_iff {a : Additive (LineBundleClass X)} :
    Additive.ofMul (pullback g a.toMul) ∈ picZero K Y ↔ a ∈ picZero k X := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  rw [mem_picZero_iff, mem_picZero_iff, toMul_ofMul, eulerDegree_pullback H]

include H in
/-- `Pic⁰ X` is the preimage of `Pic⁰ X_K` under pullback of line-bundle classes along the base
change `X_K ⟶ X` to a field extension `K`, for curves `X` and `X_K` as in
`LineBundleClass.pullback_mem_picZero_iff`. -/
theorem comap_picZero :
    (picZero K Y).comap (pullbackHom g).toAdditive = picZero k X := by
  ext a
  rw [AddSubgroup.mem_comap, MonoidHom.toAdditive_apply_apply, pullbackHom_apply]
  exact pullback_mem_picZero_iff H

end LineBundleClass

end TauCeti.AlgebraicGeometry
