/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupExtension.Cohomology

/-!
# The class of an extension under quotient relabelling

Relabelling the quotient of a profinite extension along a continuous multiplicative
equivalence pulls its continuous second cohomology class back along the inverse
equivalence. Thus the class generates cohomology before relabelling exactly when it
does afterwards. This allows the class of an arithmetic extension to be read over
a finite Galois group instead of a quotient of the absolute Galois group.

The comparison uses `ContCohomology.explicitMap2Equiv` and the section-independent
extension class of `GroupExtension.contCohomologyClass_eq`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Chapter I, §2 and the proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti.ProfiniteGroupExtension

open ContCohomology TauCeti.GroupExtension

universe u

variable {G H M : Type u} [Group G] [Group H] [CommGroup M]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace M]
  [ContinuousMul G] [ContinuousMul H] [IsTopologicalGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]
  [ContinuousSMul G M] [ContinuousSMul H M] [CompactSpace M] [T2Space G] [T2Space H]
  (X : ProfiniteGroupExtension G M) (e : G ≃ₜ* H)
  (hsmul : ∀ (g : G) (m : M), e g • m = g • m)

/-- Relabelling the quotient pulls the extension class back along the inverse
quotient equivalence, with the identity on coefficients. -/
theorem contCohomologyClass_relabelQuotient :
    (X.relabelQuotient e hsmul).contCohomologyClass =
      explicitMap2 G (Additive M) H (Additive M) e.symm
        (AddMonoidHom.id _) continuous_id
        (fun h m ↦ by
          simpa using
            congrArg (@Additive.ofMul M) (hsmul (e.symm h) m.toMul).symm)
        X.contCohomologyClass := by
  let Y := X.relabelQuotient e hsmul
  let σ := X.continuousSection
  let τ : Y.toGroupExtension.Section :=
    { toFun := fun h ↦ σ (e.symm h)
      rightInverse_rightHom := fun h ↦ by
        simp [Y, _root_.GroupExtension.Section.rightHom_section] }
  have hτ : Continuous ⇑τ := X.continuous_continuousSection.comp e.symm.continuous
  have hτ₁ : τ 1 = 1 := by simp [τ, σ, continuousSection_one]
  have hi : Y.toGroupExtension.inl = X.toGroupExtension.inl := by simp [Y]
  have hfactor (h k : H) :
      factorSet τ hτ₁ Y.inducesAction (h, k) =
        factorSet σ X.continuousSection_one X.inducesAction (e.symm h, e.symm k) := by
    apply X.toGroupExtension.inl_injective
    rw [← hi, GroupExtension.inl_factorSet, hi, GroupExtension.inl_factorSet]
    simp [τ, σ]
  rw [contCohomologyClass_def,
    _root_.GroupExtension.contCohomologyClass_eq _ _ _ _ hτ hτ₁,
    contCohomologyClass_def,
    _root_.GroupExtension.contCohomologyClass_eq _ _ _ _
      X.continuous_continuousSection X.continuousSection_one,
    FactorSet.contCohomologyClass_def, FactorSet.contCohomologyClass_def]
  -- The cocycle pullback has the same factor set after inclusion into the total group.
  -- Applying the quotient map as a term avoids abstracting its dependent continuity proof.
  refine Eq.trans ?_ (explicitMap2_mk _ _ _ _ _ _ _ _ _).symm
  apply congrArg (H2pi H (Additive M))
  ext ⟨h, k⟩
  simp only [FactorSet.coe_toZ2, cocyclesMap2_apply, AddMonoidHom.id_apply]
  exact congrArg (@Additive.ofMul M) (hfactor h k)

/-- The extension class generates second cohomology exactly when the class of the
extension with relabelled quotient does. -/
@[simp]
theorem zmultiples_contCohomologyClass_relabelQuotient_eq_top_iff :
    AddSubgroup.zmultiples (X.relabelQuotient e hsmul).contCohomologyClass = ⊤ ↔
      AddSubgroup.zmultiples X.contCohomologyClass = ⊤ := by
  let c := explicitMap2Equiv G (Additive M) H (Additive M) e.symm
    (AddEquiv.refl _) continuous_id continuous_id
    (fun h m ↦ by
      simpa using
        congrArg (@Additive.ofMul M) (hsmul (e.symm h) m.toMul).symm)
  have hc : (X.relabelQuotient e hsmul).contCohomologyClass = c X.contCohomologyClass := by
    -- Use the evaluation lemma as a term: its continuity argument depends on the
    -- coefficient homomorphism, so rewriting through the identity equivalence is fragile.
    exact (X.contCohomologyClass_relabelQuotient e hsmul).trans
      (explicitMap2Equiv_apply G (Additive M) H (Additive M) e.symm (AddEquiv.refl _)
        _ _ _ X.contCohomologyClass).symm
  rw [hc]
  constructor
  · intro h
    apply AddSubgroup.map_injective (f := c.toAddMonoidHom) c.injective
    simpa only [AddMonoidHom.map_zmultiples, AddEquiv.coe_toAddMonoidHom,
      AddSubgroup.map_top_of_surjective c.toAddMonoidHom c.surjective]
      using h
  · intro h
    have hm := congrArg (AddSubgroup.map c.toAddMonoidHom) h
    simpa only [AddMonoidHom.map_zmultiples, AddEquiv.coe_toAddMonoidHom,
      AddSubgroup.map_top_of_surjective c.toAddMonoidHom c.surjective]
      using hm

end TauCeti.ProfiniteGroupExtension
