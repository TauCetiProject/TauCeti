/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.OpenRestriction
public import TauCeti.AlgebraicGeometry.SpecialFiber.Components

/-!
# Restriction of line-bundle classes to the generic fibre over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction ring `K`, and let `toBase : X ⟶ Spec R` be a
regular Noetherian integral scheme all of whose points have codimension at most two and whose
generic point does not map to the closed point of `Spec R`. Since `genericFiberι R K toBase` is a
nonempty open immersion whose image is `{x : X | toBase x ≠ closedPoint R}`
(`TauCeti.range_genericFiberι_eq_setOf_base_ne_closedPoint`), applying the open-restriction exact
sequence of `TauCeti.AlgebraicGeometry.LineBundle.OpenRestriction` shows that:

1. Restriction `LineBundleClass.pullback (genericFiberι R K toBase)` from `Pic(X)` to `Pic(X_K)` is
   surjective (`TauCeti.pullback_genericFiberι_surjective`).
2. A line-bundle class `a` on `X` restricts to `1` on `X_K` if and only if it is an integer-power
   product of the line bundles `[𝒪_X(Cᵢ)]` attached to the finitely many irreducible components
   `Cᵢ = closure {ηᵢ}` of the special fibre (`TauCeti.pullback_genericFiberι_eq_one_iff`).

## Main declarations

* `TauCeti.pullback_genericFiberι_surjective`: surjectivity of `Pic(X) → Pic(X_K)` over a discrete
  valuation ring;
* `TauCeti.pullback_genericFiberι_eq_one_iff`: vertical-component characterization of the kernel of
  `Pic(X) → Pic(X_K)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.5 and Corollary II.6.16.
* [The Stacks Project, Section 55.9 (0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y), the
  geometry of regular models over a discrete valuation ring.
-/

public section

noncomputable section

open CategoryTheory Order AlgebraicGeometry IsLocalRing
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))
  [IsIntegral X] [IsNoetherian X] [TauCeti.AlgebraicGeometry.IsRegular X]

/-- **Surjectivity of Picard restriction to the generic fibre.** Let `X` be a regular Noetherian
integral scheme over a discrete valuation ring `R` with fraction ring `K`, all of whose points have
codimension at most two and whose generic point lies outside the special fibre. Then restriction
`Pic(X) → Pic(X_K)` along `genericFiberι R K toBase` is surjective. -/
theorem pullback_genericFiberι_surjective (hX : ∀ x : X, coheight x ≤ 2)
    (hη : toBase (genericPoint X) ≠ closedPoint R) :
    Function.Surjective (LineBundleClass.pullback (genericFiberι R K toBase)) := by
  have := isOpenImmersion_genericFiberι R K toBase
  have := nonempty_genericFiber_of_base_ne_closedPoint R K toBase hη
  exact LineBundleClass.pullback_surjective_of_isRegular hX (genericFiberι R K toBase)

/-- **Kernel of Picard restriction to the generic fibre.** Let `X` be a regular Noetherian integral
scheme over a discrete valuation ring `R` with fraction ring `K`, all of whose points have
codimension at most two and whose generic point lies outside the special fibre. A line-bundle class
on `X` restricts to `1` on the generic fibre `X_K` if and only if it is an integer-power product of
the line bundles `[𝒪_X(Cᵢ)]` attached to the irreducible components `Cᵢ` of the special fibre. -/
theorem pullback_genericFiberι_eq_one_iff (hX : ∀ x : X, coheight x ≤ 2)
    (hη : toBase (genericPoint X) ≠ closedPoint R) {a : LineBundleClass X} :
    LineBundleClass.pullback (genericFiberι R K toBase) a = 1 ↔
      ∃ c : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ,
        a = ∏ i, (LineBundleClass.mk
          (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
            i.1.2).toInvertibleSheaf)⁻¹ ^ c i := by
  have := isOpenImmersion_genericFiberι R K toBase
  have := nonempty_genericFiber_of_base_ne_closedPoint R K toBase hη
  refine LineBundleClass.pullback_eq_one_iff_of_isRegular hX (genericFiberι R K toBase) ?_
  ext η
  simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    range_genericFiberι_eq_setOf_base_ne_closedPoint, Classical.not_not]

end TauCeti
