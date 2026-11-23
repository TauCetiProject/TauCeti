/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

/-!
# Restriction of line-bundle classes on a regular model to its generic fibre

For a model `M : Model R K C toK` over a discrete valuation ring `R` with fraction field `K` whose
total space `M.total` is an integral Noetherian regular scheme all of whose points have codimension
at most two, flatness of `M.toBase` ensures that `genericPoint M.total` lies outside the special
fibre (`M.nonempty_generic`), and `M.genericι : C ⟶ M.total` is a nonempty open immersion whose
image is `{x : M.total | M.toBase x ≠ closedPoint R}`. Specializing the open-immersion Picard
excision of `TauCeti.AlgebraicGeometry.CartierDivisor.Excision` gives:

1. Surjectivity of `LineBundleClass.pullback M.genericι : Pic(M.total) → Pic(C)`
   (`TauCeti.Model.pullback_genericι_surjective`).
2. Identification of the kernel of `LineBundleClass.pullback M.genericι` with integer-power products
   of the line bundles `[𝒪_{M.total}(Cᵢ)]` attached to the irreducible components `Cᵢ` of the
   special fibre (`TauCeti.Model.pullback_genericι_eq_one_iff`).

## Main declarations

* `TauCeti.Model.pullback_genericι_surjective`: surjectivity of `Pic(M.total) → Pic(C)` for a
  regular model of codimension at most two;
* `TauCeti.Model.pullback_genericι_eq_one_iff`: vertical-component characterization of the kernel
  of `Pic(M.total) → Pic(C)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.5 and Corollary II.6.16.
* [The Stacks Project, Section 55.9 (0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y), the
  geometry of regular models over a discrete valuation ring.
-/

public section

noncomputable section

open CategoryTheory Order AlgebraicGeometry IsLocalRing
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Model

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)} (M : Model R K C toK)
  [IsIntegral M.total] [IsNoetherian M.total] [TauCeti.AlgebraicGeometry.IsRegular M.total]

/-- **Surjectivity of `Pic(M.total) → Pic(C)` for a regular model.** If `M : Model R K C toK` is a
model over a discrete valuation ring `R` with fraction field `K` whose total space `M.total` is a
regular Noetherian integral scheme all of whose points have codimension at most two, then
restriction `LineBundleClass.pullback M.genericι` to the generic fibre `C` is surjective. -/
theorem pullback_genericι_surjective (hM : ∀ x : M.total, coheight x ≤ 2) :
    Function.Surjective (LineBundleClass.pullback M.genericι) := by
  have := M.isOpenImmersion_genericι
  exact LineBundleClass.pullback_surjective_of_isOpenImmersion_of_isRegular M.genericι hM

/-- **Kernel of `Pic(M.total) → Pic(C)` for a regular model.** If `M : Model R K C toK` is a model
over a discrete valuation ring `R` with fraction field `K` whose total space `M.total` is a regular
Noetherian integral scheme all of whose points have codimension at most two, then a line-bundle
class `a` on `M.total` restricts to `1` on `C` along `M.genericι` if and only if `a` is an
integer-power product of the line bundles `[𝒪_{M.total}(Cᵢ)]` attached to the finitely many
irreducible components `Cᵢ` of the special fibre of `M`. -/
theorem pullback_genericι_eq_one_iff (hM : ∀ x : M.total, coheight x ≤ 2)
    {a : LineBundleClass M.total} :
    LineBundleClass.pullback M.genericι a = 1 ↔
      ∃ c : (M.toBase.finite_setOf_base_eq_closedPoint (IsDiscreteValuationRing.not_a_field R)
          (M.toBase.base_genericPoint_ne_closedPoint
            (IsDiscreteValuationRing.not_a_field R))).toFinset → ℤ,
        a = ∏ i, (LineBundleClass.mk
          (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hM
            i.val.property).toInvertibleSheaf)⁻¹ ^ c i := by
  have := M.isOpenImmersion_genericι
  refine LineBundleClass.pullback_eq_one_iff_exists_prod_of_isOpenImmersion_of_isRegular
    M.genericι hM fun η ↦ ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    M.range_genericι_eq_setOf_base_ne_closedPoint, Classical.not_not]

end TauCeti.Model
