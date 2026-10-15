/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RationalPoint.Degree
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ZeroLocus
public import TauCeti.AlgebraicGeometry.Curves.Degree

/-!
# The ideal sheaf of a rational point

On an integral regular curve, the ideal sheaf of a closed field-valued point is canonically
isomorphic to the divisor sheaf `𝒪_X(-x)`. The comparison identifies both inclusions into the
sheaf of rational functions. It therefore connects points presented as closed immersions with
points presented as Weil divisors, without choosing a local parameter.

For a rational point on a proper curve, the ideal line bundle has Euler-characteristic degree
`-1`. Its dual is the degree-one line bundle used by the Abel map. The sheaf comparison needs
only a closed immersion from a field spectrum and dimension at most one; the degree calculation
additionally uses a section of the structure morphism and finite-dimensional `H¹(X, 𝒪_X)`.

## References

* R. Hartshorne, *Algebraic Geometry*, II.6 and IV.1: the ideal sheaf of a point on a nonsingular
  curve is `𝒪_X(-x)`, and `deg 𝒪_X(x) = [κ(x) : k]`.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (s : Spec (.of k) ⟶ X) [IsClosedImmersion s]

private lemma mem_ker_sections_iff_notMem_basicOpen {U : X.Opens} (a : Γ(X, U)) :
    a ∈ s.ker.sections U ↔ s (IsLocalRing.closedPoint k) ∉ X.basicOpen a := by
  have hpre : s ⁻¹ᵁ X.basicOpen a = ⊥ ↔
      s (IsLocalRing.closedPoint k) ∉ X.basicOpen a := by
    have hrange : Set.range s = {s (IsLocalRing.closedPoint k)} :=
      Set.range_eq_singleton fun z ↦ congrArg s (Subsingleton.elim z _)
    rw [← TopologicalSpace.Opens.coe_eq_empty, Scheme.Hom.coe_preimage,
      Set.preimage_eq_empty_iff, hrange, Set.disjoint_singleton_right]
    rfl
  rw [mem_ker_sections_iff, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  exact hpre

variable [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  {x : CodimensionOnePoint X} (hx : (x : X) = s (IsLocalRing.closedPoint k))

include hx in
private lemma toRationalFunctions_app_mem_sections_neg_point_iff
    (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U a ∈
        SchemeWeilDivisor.sections (-WeilDivisor.ofPoint x) U ↔ a ∈ s.ker.sections U := by
  rw [mem_ker_sections_iff_notMem_basicOpen]
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hxU : (x : X) ∈ U
  · have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have haF : X.germToFunctionField U a ≠ 0 :=
      fun h ↦ ha (X.germToFunctionField_injective U (by simpa using h))
    rw [SchemeWeilDivisor.mem_sections_iff,
      Scheme.rationalFunctionsEquiv_toRationalFunctions_app]
    simp only [haF, false_or]
    constructor
    · intro h
      have hpos := h x hxU
      simp only [WeilDivisor.coeff_neg, WeilDivisor.coeff_ofPoint_self, neg_neg] at hpos
      have hzero := (Scheme.ord_germToFunctionField_pos_iff ha hxU x.property).mp
        (by omega)
      simpa [Scheme.zeroLocus_singleton, hx] using hzero
    · intro h y hy
      by_cases hyx : y = x
      · subst y
        have hzero : (x : X) ∈ X.zeroLocus {a} := by
          simpa [Scheme.zeroLocus_singleton, hx] using h
        have hpos := (Scheme.ord_germToFunctionField_pos_iff ha hxU x.property).mpr hzero
        simp only [WeilDivisor.coeff_neg, WeilDivisor.coeff_ofPoint_self, neg_neg]
        omega
      · simpa [WeilDivisor.coeff_ofPoint_of_ne hyx] using
          Scheme.ord_germToFunctionField_nonneg a hy
  · have hnot : s (IsLocalRing.closedPoint k) ∉ X.basicOpen a := by
      rw [← hx]
      exact fun h ↦ hxU (X.basicOpen_le a h)
    simp only [hnot, not_false_eq_true, iff_true]
    refine SchemeWeilDivisor.mem_sections.mpr fun y hy ↦ ?_
    have : Nonempty U := ⟨⟨y, hy⟩⟩
    have hyx : y ≠ x := fun h ↦ hxU (h ▸ hy)
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app]
    simpa [WeilDivisor.coeff_ofPoint_of_ne hyx] using
      Or.inr (Scheme.ord_germToFunctionField_nonneg a hy)

variable (hX : ∀ y : X, coheight y ≤ 1)

private def kerToNegPoint : s.ker.sheaf ⟶ SchemeWeilDivisor.sheaf (-WeilDivisor.ofPoint x) :=
  SchemeWeilDivisor.sheafLift _ (s.ker.sheafι ≫ Scheme.toRationalFunctions X)
    fun U a ↦ (toRationalFunctions_app_mem_sections_neg_point_iff s hx U _).mpr
      (s.ker.sheafι_app_mem U a)

include hX in
private lemma isIso_kerToNegPoint : IsIso (kerToNegPoint s hx) := by
  apply SchemeWeilDivisor.isIso_sheafLift
  · intro U
    exact (Scheme.toRationalFunctions_app_injective U).comp (s.ker.sheafι_app_injective U)
  · intro U a ha
    have hzero := SchemeWeilDivisor.sections_mono
      (neg_nonpos.mpr (WeilDivisor.zero_le_ofPoint x)) U ha
    obtain ⟨b, rfl⟩ := (SchemeWeilDivisor.mem_sections_zero_iff (fun y _ ↦ hX y) a).mp hzero
    have hb := (toRationalFunctions_app_mem_sections_neg_point_iff s hx U b).mp ha
    refine ⟨s.ker.sectionMk b hb, ?_⟩
    simpa only [ConcreteCategory.comp_apply, Scheme.IdealSheafData.sheafι_app_sectionMk] using
      ConcreteCategory.congr_hom (Scheme.Modules.Hom.comp_app (U := U) s.ker.sheafι
        (Scheme.toRationalFunctions X)) (s.ker.sectionMk b hb)

/-- The ideal sheaf of a closed field-valued point on a regular integral curve is `𝒪_X(-x)`.
The comparison respects the embeddings into rational functions (`kerSheafIsoNegPoint_hom_ι`).
The dimension bound is only needed to recover regular functions from rational sections. -/
def kerSheafIsoNegPoint : s.ker.sheaf ≅ SchemeWeilDivisor.sheaf (-WeilDivisor.ofPoint x) :=
  haveI := isIso_kerToNegPoint s hx hX
  asIso (kerToNegPoint s hx)

/-- The comparison from the ideal sheaf of a point to `𝒪_X(-x)` sends a regular function to
the same rational function. -/
@[reassoc (attr := simp)]
lemma kerSheafIsoNegPoint_hom_ι :
    (kerSheafIsoNegPoint s hx hX).hom ≫ SchemeWeilDivisor.sheafι (-WeilDivisor.ofPoint x) =
      s.ker.sheafι ≫ Scheme.toRationalFunctions X :=
  SchemeWeilDivisor.sheafLift_ι _ _ _

include hx hX in
/-- The ideal line bundle of a rational point on a proper regular integral curve has
Euler-characteristic degree `-1`. -/
theorem eulerDegree_ker [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    (hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k)))
    (hI : s.ker.IsEffectiveCartier) : hI.toInvertibleSheaf.eulerDegree k = -1 := by
  let e := eqToIso hI.toInvertibleSheaf_obj ≪≫ kerSheafIsoNegPoint s hx hX
  rw [InvertibleSheaf.eulerDegree_eq_relativeDegree k hX e,
    map_neg, relativeDegree_ofPoint_of_section hs hx]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [ConnectedSpace X] (s : Spec (.of k) ⟶ X)
  (hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k)))

/-- On a connected smooth proper curve, the ideal line bundle of a rational point has degree
`-1`. The geometric hypotheses supply discrete valuation stalks and finite-dimensional
cohomology, without a perfect-field assumption. -/
@[simp]
theorem eulerDegree_ker_of_smooth :
    let hI := (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
    hI.toInvertibleSheaf.eulerDegree k = -1 := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have : ∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X)) :=
    fun y ↦ inferInstance
  have := AlgebraicGeometry.Scheme.Hom.isClosedImmersion_of_comp_eq_id s hs
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hdim
  have hclosed := isClosed_singleton_of_section hs
  have hstalk := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 1).mp inferInstance).2 _ hclosed
  have hcodim : coheight (s (IsLocalRing.closedPoint k)) = 1 := by
    exact_mod_cast (ringKrullDim_stalk_eq_coheight _).symm.trans hstalk
  exact eulerDegree_ker s (x := ⟨_, hcodim⟩) rfl
    (fun y ↦ by exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hdim.le)
    hs (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier

/-- The dual of the ideal line bundle of a rational point has degree one on a
connected smooth proper curve. This is the class `𝒪_X(x)` used by the Abel map. -/
@[simp]
theorem eulerDegree_dual_ker_of_smooth :
    let hI := (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
    (InvertibleSheaf.dual hI.toInvertibleSheaf).eulerDegree k = 1 := by
  let hI := (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
  let a := LineBundleClass.mk hI.toInvertibleSheaf
  have ha : LineBundleClass.eulerDegree k a = -1 := by
    rw [LineBundleClass.eulerDegree_mk]
    exact eulerDegree_ker_of_smooth s hs
  have h := LineBundleClass.eulerDegree_mul_of_smooth k a a⁻¹
  simp only [mul_inv_cancel, LineBundleClass.eulerDegree_one, ha] at h
  have hinv : LineBundleClass.eulerDegree k a⁻¹ = 1 := by omega
  simpa only [a, LineBundleClass.inv_mk, LineBundleClass.eulerDegree_mk] using hinv

end AlgebraicGeometry.Scheme.Hom
