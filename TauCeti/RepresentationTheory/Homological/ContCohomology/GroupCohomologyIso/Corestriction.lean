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
import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
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
coinduced coefficients by `discreteCoindAddEquivAlgebraic`.

Both corestrictions are inverse Shapiro followed by the coefficient trace. The proof uses the
existing comparison between locally constant and algebraic coinduction, identifies the Shapiro
maps through restriction and evaluation at the identity, and identifies the traces through
inversion of cosets. No new cochain formula for corestriction is introduced.

The coefficient ring is `ℤ`, and the group and coefficient carrier lie in `Type`, because
`explicitH2IsoGroupCohomology` compares with the group cohomology of
`Rep.ofDistribMulAction ℤ G M` for `G M : Type`.

## Main results

* `TauCeti.ContCohomology.explicitH2IsoGroupCohomology_explicitCor2`: the degree-two comparison
  preserves corestriction from every subgroup of a finite discrete group.
* `TauCeti.ContCohomology.explicitH2IsoGroupCohomology_explicitShapiroMap2`: the degree-two
  comparison preserves Shapiro's map after identifying the coinduced coefficients.

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

variable [Finite G]

private def coindH2Equiv :
    H2 G (DiscreteCoind G U M) ≃+
      groupCohomology (Rep.coind U.subtype
        (Rep.ofDistribMulAction ℤ U M)) 2 :=
  explicitH2AddEquivGroupCohomology (MulEquiv.refl G) (discreteCoindAddEquivAlgebraic G M U)
    (discreteCoindAddEquivAlgebraic_smul G M U)

private theorem coindH2Equiv_shapiro (x : H2 G (DiscreteCoind G U M)) :
    (groupCohomology.coindIso
      (Rep.ofDistribMulAction ℤ U M) 2).hom (coindH2Equiv G M U x) =
        explicitH2IsoGroupCohomology U M (explicitShapiroMap2 G U M x) := by
  classical
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    let c : cocycles₂ (Rep.coind U.subtype
        (Rep.ofDistribMulAction ℤ U M)) :=
      ⟨fun p ↦ discreteCoindAddEquivAlgebraic G M U ((z : G × G → DiscreteCoind G U M) p),
        (mem_cocycles₂_iff_of_equiv (MulEquiv.refl G)
          (discreteCoindAddEquivAlgebraic G M U)
          (discreteCoindAddEquivAlgebraic_smul G M U) z).2 (mem_Z2_iff.1 z.2).2⟩
    have hc : coindH2Equiv G M U (z : H2 G (DiscreteCoind G U M)) = H2π _ c :=
      explicitH2AddEquivGroupCohomology_mk (MulEquiv.refl G) (discreteCoindAddEquivAlgebraic G M U)
        (discreteCoindAddEquivAlgebraic_smul G M U) z c (fun _ ↦ rfl)
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
    exact (discreteCoindAddEquivAlgebraic_eval G M U _).trans
      ((shapiroCocycles2_apply G U M z p.1 p.2).symm.trans
        (congrFun (Z2AddEquivCocycles₂_coe U M (shapiroCocycles2 G U M z)) p).symm)

/-- For a finite discrete group, the explicit-to-ordinary comparison in degree two preserves
Shapiro's map after the canonical identification of locally constant and algebraic coinduction. -/
theorem explicitH2IsoGroupCohomology_explicitShapiroMap2
    (x : H2 G (DiscreteCoind G U M)) :
    explicitH2IsoGroupCohomology U M (explicitShapiroMap2 G U M x) =
      (groupCohomology.coindIso
        (Rep.ofDistribMulAction ℤ U M) 2).hom
          (explicitH2AddEquivGroupCohomology (MulEquiv.refl G)
            (discreteCoindAddEquivAlgebraic G M U)
            (discreteCoindAddEquivAlgebraic_smul G M U) x) :=
  (coindH2Equiv_shapiro G M U x).symm

end Shapiro

section Corestriction

variable [Finite G] [DistribMulAction G M] [ContinuousSMul G M]

/-- For a finite discrete group, the explicit-to-ordinary comparison in degree two preserves
cohomological corestriction from every subgroup. -/
theorem explicitH2IsoGroupCohomology_explicitCor2 (x : H2 U M) :
    explicitH2IsoGroupCohomology G M (explicitCor2 G M U (isOpen_discrete _) x) =
      TauCeti.groupCohomology.corestriction U (Rep.ofDistribMulAction ℤ G M) 2
        (explicitH2IsoGroupCohomology U M x) := by
  classical
  -- Restricting the associated representation is definitionally the representation of the
  -- restricted action. Type the comparison directly in the presentation used by corestriction.
  let e : H2 G (DiscreteCoind G U M) ≃+
      groupCohomology
        (Rep.coind U.subtype (Rep.res U.subtype (Rep.ofDistribMulAction ℤ G M))) 2 :=
    coindH2Equiv G M U
  let y := (explicitShapiro2 G U M (isClosed_discrete _)).symm x
  have hsh : explicitH2IsoGroupCohomology U M x =
      (groupCohomology.coindIso
        (Rep.res U.subtype (Rep.ofDistribMulAction ℤ G M)) 2).hom (e y) := by
    have hs := (coindH2Equiv_shapiro G M U y).symm
    rw [← explicitShapiro2_apply G U M (isClosed_discrete _),
      AddEquiv.apply_symm_apply] at hs
    exact hs
  have hcor :
      TauCeti.groupCohomology.corestriction U (Rep.ofDistribMulAction ℤ G M) 2
          (explicitH2IsoGroupCohomology U M x) =
        groupCohomology.map (MonoidHom.id G)
          ((Rep.coindResAdjunction ℤ U).counit.app (Rep.ofDistribMulAction ℤ G M)) 2
            (e y) := by
    rw [hsh, ← ConcreteCategory.comp_apply,
      TauCeti.groupCohomology.coindIso_hom_comp_corestriction]
  have hformula : explicitCor2 G M U (isOpen_discrete _) x =
      explicitCoeff2 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M)
        DiscreteCoind.continuous_trace y :=
    DFunLike.congr_fun
      (explicitCor2_eq_explicitCoeff2_trace (G := G) (M := M) (U := U) (isOpen_discrete _)) x
  refine (congrArg (explicitH2IsoGroupCohomology G M) hformula).trans
    (Eq.trans ?_ hcor.symm)
  rw [explicitH2IsoGroupCohomology_def]
  exact explicitH2AddEquivGroupCohomology_explicitCoeff2 (MulEquiv.refl G)
    (discreteCoindAddEquivAlgebraic G M U) (AddEquiv.refl M)
    (discreteCoindAddEquivAlgebraic_smul G M U) (fun _ _ ↦ rfl)
    (DiscreteCoind.trace G U M) DiscreteCoind.continuous_trace
    ((Rep.coindResAdjunction ℤ U).counit.app (Rep.ofDistribMulAction ℤ G M))
    (fun f ↦ (discreteCoindAddEquivAlgebraic_trace G M U f).symm) y

end Corestriction

end TauCeti.ContCohomology
