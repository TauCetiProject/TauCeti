/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Functor
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso.CoeffMap
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.DegreeTwo
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Comparing degree-two corestriction for finite groups

For a finite discrete group, the comparison from explicit continuous second cohomology to
ordinary group cohomology carries the explicit corestriction to the ordinary cohomological
corestriction. Thus operations on finite layers can be compared with continuous operations
using the same corestriction normalization.

The comparison also identifies the explicit Shapiro map with ordinary Shapiro after transporting
coinduced coefficients by `discreteCoindEquivAlgebraic`.

Both corestrictions are inverse Shapiro followed by the coefficient trace. The proof uses the
existing comparison between locally constant and algebraic coinduction, identifies the Shapiro
maps through restriction and evaluation at the identity, and identifies the traces through
inversion of cosets. No new cochain formula for corestriction is introduced.

The coefficient ring is `ℤ`, and the group and coefficient carrier lie in `Type`, as in
`explicitH2IsoGroupCohomology` at the pinned Mathlib version.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9, the coinduced-module construction
  of cohomological corestriction.
-/

public noncomputable section

open CategoryTheory _root_.groupCohomology

namespace TauCeti.ContCohomology

variable (G M : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  (U : Subgroup G)

section Shapiro

variable [DistribMulAction U M] [ContinuousSMul U M]

private def coindEquiv :
    DiscreteCoind G U M ≃+ Rep.coind U.subtype
      (Rep.ofDistribMulAction ℤ U M) :=
  (discreteCoindEquivAlgebraic ℤ G ⟨U, isOpen_discrete _⟩
    ⟨ofDiscreteModule ℤ U M, ofDiscreteModule_isSmoothDiscrete ℤ U M⟩).toAddEquiv

private theorem coindEquiv_apply (f : DiscreteCoind G U M) (g : G) :
    (coindEquiv G M U f).1 g = f g :=
  discreteCoindEquivAlgebraic_apply ℤ G ⟨U, isOpen_discrete _⟩
    ⟨ofDiscreteModule ℤ U M, ofDiscreteModule_isSmoothDiscrete ℤ U M⟩ f g

private theorem coindEquiv_smul (g : G) (f : DiscreteCoind G U M) :
    coindEquiv G M U (g • f) =
      (Rep.coind U.subtype (Rep.ofDistribMulAction ℤ U M)).ρ g
        (coindEquiv G M U f) :=
  discreteCoindEquivAlgebraic_smul ℤ G ⟨U, isOpen_discrete _⟩
    ⟨ofDiscreteModule ℤ U M, ofDiscreteModule_isSmoothDiscrete ℤ U M⟩ g f

variable [Finite G]

private theorem coindEquiv_eval (f : DiscreteCoind G U M) :
    ((Rep.resCoindAdjunction ℤ U.subtype).counit.app
      (Rep.ofDistribMulAction ℤ U M)).hom (coindEquiv G M U f) = f 1 := by
  let A : SmoothDiscreteTopRep ℤ U :=
    ⟨ofDiscreteModule ℤ U M, ofDiscreteModule_isSmoothDiscrete ℤ U M⟩
  exact (LinearMap.congr_fun (algebraicCoindCounit_toLinearMap
    (R := ℤ) ⟨U, isOpen_discrete _⟩ A) _).symm.trans
      ((algebraicCoindCounit_apply ℤ G ⟨U, isOpen_discrete _⟩ A _).trans
        (coindEquiv_apply G M U f 1))

private def coindH2Equiv :
    H2 G (DiscreteCoind G U M) ≃+
      groupCohomology (Rep.coind U.subtype
        (Rep.ofDistribMulAction ℤ U M)) 2 :=
  explicitH2AddEquivGroupCohomology (MulEquiv.refl G) (coindEquiv G M U)
    (coindEquiv_smul G M U)

private theorem coindH2Equiv_shapiro (x : H2 G (DiscreteCoind G U M)) :
    (groupCohomology.coindIso
      (Rep.ofDistribMulAction ℤ U M) 2).hom (coindH2Equiv G M U x) =
        explicitH2IsoGroupCohomology U M (explicitShapiroMap2 G U M x) := by
  classical
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    let c : cocycles₂ (Rep.coind U.subtype
        (Rep.ofDistribMulAction ℤ U M)) :=
      ⟨fun p ↦ coindEquiv G M U ((z : G × G → DiscreteCoind G U M) p),
        (mem_cocycles₂_iff _).2 fun g h j ↦ by
        have hz := congrArg (coindEquiv G M U) ((mem_Z2_iff.1 z.2).2 g h j)
        simp only [map_add] at hz
        exact hz.trans (congrArg (· + _) (coindEquiv_smul G M U g _))⟩
    have hc : coindH2Equiv G M U (z : H2 G (DiscreteCoind G U M)) = H2π _ c :=
      explicitH2AddEquivGroupCohomology_mk (MulEquiv.refl G) (coindEquiv G M U)
        (coindEquiv_smul G M U) z c (fun _ ↦ rfl)
    rw [hc, TauCeti.groupCohomology.coindIso_hom]
    refine (H2π_comp_map_apply U.subtype
      ((Rep.resCoindAdjunction ℤ U.subtype).counit.app
        (Rep.ofDistribMulAction ℤ U M)) c).trans ?_
    rw [explicitShapiroMap2_mk, explicitH2IsoGroupCohomology_mk]
    congr 1
    apply Subtype.ext
    funext p
    refine (TauCeti.groupCohomology.mapCocycles₂_apply U.subtype
      ((Rep.resCoindAdjunction ℤ U.subtype).counit.app
        (Rep.ofDistribMulAction ℤ U M)) c p).trans ?_
    -- The algebraic counit and explicit Shapiro both evaluate the coefficient at the identity.
    exact (coindEquiv_eval G M U _).trans
      ((shapiroCocycles2_apply G U M z p.1 p.2).symm.trans
        (congrFun (Z2AddEquivCocycles₂_coe U M (shapiroCocycles2 G U M z)) p).symm)

/-- For a finite discrete group, the explicit-to-ordinary comparison in degree two preserves
Shapiro's map after the canonical identification of locally constant and algebraic coinduction.
The local name `A` supplies the smooth discrete presentation of the caller's coefficient module. -/
theorem explicitH2IsoGroupCohomology_explicitShapiroMap2
    (x : H2 G (DiscreteCoind G U M)) :
    let A : SmoothDiscreteTopRep ℤ U :=
      ⟨ofDiscreteModule ℤ U M, ofDiscreteModule_isSmoothDiscrete ℤ U M⟩
    explicitH2IsoGroupCohomology U M (explicitShapiroMap2 G U M x) =
      (groupCohomology.coindIso
        (Rep.ofDistribMulAction ℤ U M) 2).hom
          (explicitH2AddEquivGroupCohomology (MulEquiv.refl G)
            (discreteCoindEquivAlgebraic ℤ G ⟨U, isOpen_discrete _⟩ A).toAddEquiv
            (discreteCoindEquivAlgebraic_smul ℤ G ⟨U, isOpen_discrete _⟩ A) x) :=
  (coindH2Equiv_shapiro G M U x).symm

end Shapiro

section Corestriction

variable [Finite G] [DistribMulAction G M] [ContinuousSMul G M]

open Classical in
private theorem coindEquiv_trace (f : DiscreteCoind G U M) :
    ((Rep.coindResAdjunction ℤ U).counit.app (Rep.ofDistribMulAction ℤ G M)).hom
        (coindEquiv G M U f) = DiscreteCoind.trace G U M f := by
  classical
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel U
  let t : G ⧸ U → G := fun q ↦ ((e.symm q).out)⁻¹
  have ht (q : G ⧸ U) : (QuotientGroup.mk (t q) : G ⧸ U) = q :=
    (congrArg e (Quotient.out_eq (e.symm q))).trans (e.apply_symm_apply q)
  refine (Subgroup.coindResAdjunction_counit_app_hom_apply U
    (Rep.ofDistribMulAction ℤ G M) (coindEquiv G M U f)).trans ?_
  rw [DiscreteCoind.trace_eq_sum_transversal t ht]
  let : Fintype (G ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  exact Fintype.sum_equiv e _ _ fun q ↦ by
    simp only [t, e.symm_apply_apply, inv_inv]
    exact (congrArg (fun m : M ↦ (Rep.ofDistribMulAction ℤ G M).ρ q.out⁻¹ m)
      (coindEquiv_apply G M U f q.out)).trans
        (Rep.ofDistribMulAction_ρ_apply_apply ℤ G M q.out⁻¹ (f q.out))

/-- For a finite discrete group, the explicit-to-ordinary comparison in degree two preserves
cohomological corestriction from every subgroup. -/
theorem explicitH2IsoGroupCohomology_explicitCor2 (x : H2 U M) :
    explicitH2IsoGroupCohomology G M (explicitCor2 G M U (isOpen_discrete _) x) =
      TauCeti.groupCohomology.corestriction U (Rep.ofDistribMulAction ℤ G M) 2
        (explicitH2IsoGroupCohomology U M x) := by
  classical
  let y := (explicitShapiro2 G U M (isClosed_discrete _)).symm x
  have hsh : explicitH2IsoGroupCohomology U M x =
      (groupCohomology.coindIso
        (Rep.res U.subtype (Rep.ofDistribMulAction ℤ G M)) 2).hom (coindH2Equiv G M U y) := by
    have hs := (coindH2Equiv_shapiro G M U y).symm
    rw [← explicitShapiro2_apply G U M (isClosed_discrete _),
      AddEquiv.apply_symm_apply] at hs
    exact hs
  have hcor :
      TauCeti.groupCohomology.corestriction U (Rep.ofDistribMulAction ℤ G M) 2
          (explicitH2IsoGroupCohomology U M x) =
        groupCohomology.map (MonoidHom.id G)
          ((Rep.coindResAdjunction ℤ U).counit.app (Rep.ofDistribMulAction ℤ G M)) 2
            (coindH2Equiv G M U y) :=
    (congrArg (TauCeti.groupCohomology.corestriction U
      (Rep.ofDistribMulAction ℤ G M) 2) hsh).trans
        ((ConcreteCategory.comp_apply _ _ _).symm.trans
          (ConcreteCategory.congr_hom
            (TauCeti.groupCohomology.coindIso_hom_comp_corestriction U
              (Rep.ofDistribMulAction ℤ G M) 2) (coindH2Equiv G M U y)))
  have hformula : explicitCor2 G M U (isOpen_discrete _) x =
      explicitCoeff2 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M)
        DiscreteCoind.continuous_trace y :=
    congrArg (fun f : H2 U M →+ H2 G M ↦ f x)
      (explicitCor2_eq_explicitCoeff2_trace (G := G) (M := M) (U := U) (isOpen_discrete _))
  refine (congrArg (explicitH2IsoGroupCohomology G M) hformula).trans
    (Eq.trans ?_ hcor.symm)
  rw [explicitH2IsoGroupCohomology_def]
  exact explicitH2AddEquivGroupCohomology_explicitCoeff2 (MulEquiv.refl G)
    (coindEquiv G M U) (AddEquiv.refl M) (coindEquiv_smul G M U) (fun _ _ ↦ rfl)
    (DiscreteCoind.trace G U M) DiscreteCoind.continuous_trace
    ((Rep.coindResAdjunction ℤ U).counit.app (Rep.ofDistribMulAction ℤ G M))
    (fun f ↦ (coindEquiv_trace G M U f).symm) y

end Corestriction

end TauCeti.ContCohomology
