/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PointSeparation
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness

/-!
# Rational points of a curve of positive genus are separated by their ideal sheaves

Let `Y` be a smooth proper integral curve over a field `K`, with `K` algebraically closed in the
function field `K(Y)` and with positive genus. Two rational points `s` and `t` of `Y` whose ideal
line bundles `𝒪(-s)` and `𝒪(-t)` are isomorphic coincide.

The ideal sheaf of a rational point `s` hitting the closed point `p` is `𝒪(-p)`
(`AlgebraicGeometry.Scheme.Hom.kerSheafIsoNegPoint`), so isomorphic ideal sheaves make the two
points linearly equivalent as Weil divisors. Linearly equivalent rational points on a curve of
positive genus are equal
(`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.eq_of_linearlyEquivalent_ofPoint_of_genus_pos`), and
a section of `Y ⟶ Spec K` is determined by its underlying point.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.eq_of_mk_toInvertibleSheaf_eq_of_genus_pos`: two rational points
  of a smooth proper curve of positive genus whose ideal sheaves are isomorphic coincide.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1: on a curve of positive genus
  distinct points are not linearly equivalent.
-/

public section

open CategoryTheory AlgebraicGeometry Order

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {K : Type u} [Field K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] [IsIntegral Y]
  [IsProper (Y ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K))]

/-- **Rational points of a curve of positive genus are separated by their ideal sheaves.** Let
`Y` be a smooth proper integral curve over a field `K`, with `K` algebraically closed in the
function field `K(Y)` and with positive genus. If two rational points `s` and `t` have isomorphic
ideal line bundles `𝒪(-s) ≅ 𝒪(-t)`, then `s = t`. -/
theorem eq_of_mk_toInvertibleSheaf_eq_of_genus_pos (hk : IsIntegrallyClosedIn K Y.functionField)
    (hg : haveI := finiteDimensional_cohomology_one_trivial_of_smooth K Y; 0 < Y.genus K)
    {s t : Spec (.of K) ⟶ Y} (hs : s ≫ (Y ↘ Spec (.of K)) = 𝟙 (Spec (.of K)))
    (ht : t ≫ (Y ↘ Spec (.of K)) = 𝟙 (Spec (.of K)))
    (h : LineBundleClass.mk (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
          s hs).isEffectiveCartier.toInvertibleSheaf =
      LineBundleClass.mk (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
          t ht).isEffectiveCartier.toInvertibleSheaf) :
    s = t := by
  have := finiteDimensional_cohomology_one_trivial_of_smooth K Y
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of K))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have : CompactSpace Y := (quasiCompact_iff_compactSpace (Y ↘ Spec (.of K))).mp inferInstance
  have : IsNoetherian Y := {}
  have : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth (Y ↘ Spec (.of K))
  have : ∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y)) :=
    fun y ↦ inferInstance
  have := isClosedImmersion_of_comp_eq_id s hs
  have := isClosedImmersion_of_comp_eq_id t ht
  have hdim : topologicalKrullDim Y = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ Spec (.of K))
  have hX : ∀ y : Y, coheight y ≤ 1 := fun y ↦ by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hdim.le
  have : Fact (∀ y : Y, coheight y ≤ 1) := ⟨hX⟩
  let x : CodimensionOnePoint Y := ⟨_, coheight_eq_of_isClosed_of_smoothOfRelativeDimension
    (Y ↘ Spec (.of K)) (isClosed_singleton_of_section hs)⟩
  let y : CodimensionOnePoint Y := ⟨_, coheight_eq_of_isClosed_of_smoothOfRelativeDimension
    (Y ↘ Spec (.of K)) (isClosed_singleton_of_section ht)⟩
  -- The ideal line bundle of a rational point is the divisor line bundle of `-p`.
  have hclass (r : Spec (.of K) ⟶ Y) [IsClosedImmersion r] (p : CodimensionOnePoint Y)
      (hp : (p : Y) = r (IsLocalRing.closedPoint K)) (hIr : r.ker.IsEffectiveCartier) :
      SchemeWeilDivisor.toLineBundleClass hX (-WeilDivisor.ofPoint p) =
        LineBundleClass.mk hIr.toInvertibleSheaf :=
    (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hX).mpr
      ⟨eqToIso (SchemeWeilDivisor.toInvertibleSheaf_obj hX _) ≪≫
        (kerSheafIsoNegPoint r hp hX).symm ≪≫ eqToIso hIr.toInvertibleSheaf_obj.symm⟩
  have hlin := (SchemeWeilDivisor.toLineBundleClass_eq_iff hX).mp
    ((hclass s x rfl _).trans (h.trans (hclass t y rfl _).symm))
  rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff, neg_sub_neg,
    ← WeilDivisor.OrderSystem.linearlyEquivalent_iff] at hlin
  have hxy : x = y := SchemeWeilDivisor.eq_of_linearlyEquivalent_ofPoint_of_genus_pos K hk hg
    (residueDegree_eq_one_of_section hs _) hlin.symm
  have : IsIso ((Y ↘ Spec (.of K)).residueFieldMap (s (IsLocalRing.closedPoint K))) :=
    isIso_residueFieldMap_of_section hs _
  exact hom_ext_of_isIso_residueFieldMap (f := Y ↘ Spec (.of K)) (hs.trans ht.symm)
    (congrArg Subtype.val hxy)

end AlgebraicGeometry.Scheme.Hom
