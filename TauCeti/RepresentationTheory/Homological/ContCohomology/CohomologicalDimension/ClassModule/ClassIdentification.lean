/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Extension
public import TauCeti.Topology.Algebra.GroupExtension.Cohomology
import TauCeti.Algebra.GroupAction.TypeTags

/-!
# The cohomology class of the pro-p class-module extension

For an open normal subgroup `V` of a profinite group `G`, the bundled extension
`1 → Vᵃᵇ(p) → G / ker(V → Vᵃᵇ(p)) → G/V → 1` has class `abelianizationProPClass`.
This identifies the class used in extension lifting with the explicit cocycle built from
quotient representatives. In particular, generation results about the explicit class apply to
the actual profinite extension.

The quotient representatives need not send `1` to `1`. Their section still gives the explicit
cocycle, and comparison with a normalized continuous section changes it by a continuous
coboundary.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.6.2)
  and the proof of (7.4.1).
-/

public section

namespace TauCeti

open ContCohomology TauCeti.GroupExtension

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : Subgroup G) [V.Normal]

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The continuous cohomology class of the bundled pro-`p` class-module extension is the
explicit class `u_{G/V}(p)` defined by quotient representatives. -/
@[simp]
theorem abelianizationProPProfiniteExtension_contCohomologyClass
    (hV : IsOpen (V : Set G)) :
    letI : IsClosed (V : Set G) := V.isClosed_of_isOpen hV
    (abelianizationProPProfiniteExtension p G V).contCohomologyClass =
      abelianizationProPClass p G V hV := by
  let : IsClosed (V : Set G) := V.isClosed_of_isOpen hV
  let : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  let X := abelianizationProPProfiniteExtension p G V
  let σ := X.continuousSection
  let τ := abelianizationProPExtensionSection p G V
  have hτ : Continuous ⇑τ := continuous_of_discreteTopology
  rw [ProfiniteGroupExtension.contCohomologyClass_def,
    _root_.GroupExtension.contCohomologyClass_eq _ _ _ _
      X.continuous_continuousSection X.continuousSection_one,
    FactorSet.contCohomologyClass_def, abelianizationProPClass_def]
  apply H2pi_eq_iff.mpr
  refine mem_B2_iff'.mpr ⟨fun q ↦ Additive.ofMul (sectionDiff σ τ q),
    continuous_ofMul.comp (continuous_sectionDiff
      (X.continuous_inl.isClosedEmbedding X.toGroupExtension.inl_injective).isEmbedding
      X.continuous_continuousSection hτ), fun q r ↦ ?_⟩
  have h := σ.factorSetFun_div_factorSetFun τ X.inducesAction q r
  have hτqr := factorSetFun_abelianizationProPExtensionSection p G V q r
  simpa only [FactorSet.coe_toZ2, coe_factorSet, Pi.sub_apply, ofMul_div, ofMul_mul,
    Additive.ofMul_smul, τ, σ, hτqr] using (congrArg Additive.ofMul h).symm

end TauCeti
