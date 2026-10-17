/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.RelativeTrace
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.DegreeOne
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.DegreeTwo
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-!
# Explicit Shapiro is compatible with corestriction

For subgroups `V ≤ U ≤ G` of a profinite group, with `U` compact and `V` open of
finite index in `U`, the relative trace `Coind_V^G A → Coind_U^G A` commutes with
the forward Shapiro maps and corestriction in degrees zero, one and two. Closedness
identifies these Shapiro maps with isomorphisms; the equations themselves require
no closedness assumption. The coefficients `A` carry only a `U`-action, with a
compatible `V`-action; a `G`-action on `A` is not needed.

The source of the lower transfer is identified with `V.subgroupOf U`, the copy of `V`
inside `U`, by `Subgroup.subgroupOfContinuousMulEquivOfLe`. The statements retain this
transport explicitly, so both paths have precisely the same coefficient carriers.

The proof uses restriction of coinduced functions, the naturality of explicit Shapiro,
and the local trace/corestriction comparisons. Thus the outer group need not admit an
extension of the coefficient action from `U`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.6.4), with the terminology footnote on p. 61.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
* L. Ribes, P. Zalesskii, *Profinite Groups*, second edition, Theorem 6.10.5.
-/

public section

namespace TauCeti.ContCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U V : Subgroup G) (hVU : V ≤ U) (A : Type*) [AddCommGroup A]
  [DistribMulAction U A] [DistribMulAction V A]
  (hsmul : ∀ (v : V.subgroupOf U) (w : V) (a : A),
    ((v : U) : G) = (w : G) → w • a = v • a)
  [(V.subgroupOf U).FiniteIndex]

local notation "κ" =>
  (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V)
local notation "hκ" =>
  (fun v : V.subgroupOf U =>
    Eq.trans (Eq.symm (Subgroup.subgroupOfEquivOfLe_apply_coe hVU v))
      (congrArg (fun w : V => (w : G))
        (Eq.symm (Subgroup.subgroupOfContinuousMulEquivOfLe_apply hVU v))))
local notation "hA" =>
  (fun (v : V.subgroupOf U) (a : A) => hsmul v (κ v) a (hκ v))
local notation "p" =>
  DiscreteCoind.pullback (ContinuousMonoidHom.subgroupSubtype U) κ hκ
    (AddMonoidHom.id A) hA
local notation "t" =>
  DiscreteCoind.relativeTrace U V hVU A hsmul isClosed_closure.isCompact
local notation "τ" => DiscreteCoind.trace U (V.subgroupOf U) A

include hsmul in
omit [TotallyDisconnectedSpace G] in
private theorem eval_relativeTrace :
    (DiscreteCoind.eval G U A).comp (t).toAddMonoidHom = (τ).toAddMonoidHom.comp p := by
  ext f
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, DiscreteCoind.eval_apply]
  -- The bundled action homomorphisms and their additive maps have identical values.
  change (t f) 1 = τ (p f)
  rw [DiscreteCoind.relativeTrace_apply]
  congr 1
  ext u
  simp only [DiscreteCoind.transEquiv_symm_apply, mul_one, DiscreteCoind.pullback_apply,
    AddMonoidHom.id_apply, ContinuousMonoidHom.subgroupSubtype_apply]

/-! ### Degree zero -/

omit [TotallyDisconnectedSpace G] in
/-- Shapiro turns the relative coinduced trace into degree-zero corestriction inside `U`,
after transporting the source from `V` to its copy inside `U`. -/
theorem explicitShapiro0_relativeTrace_corestriction (x : H0 G (DiscreteCoind G V A)) :
    explicitShapiro0 G U A (explicitCoeff0 G (DiscreteCoind G V A) t x) =
      explicitCor0 U A (V.subgroupOf U)
        (explicitMap0 V A (κ : V.subgroupOf U →* V) (AddMonoidHom.id A) hA
          (explicitShapiro0 G V A x)) := by
  rw [← explicitShapiro0_pullback (ContinuousMonoidHom.subgroupSubtype U) κ hκ
    (AddMonoidHom.id A) hA x]
  have htrace := DFunLike.congr_fun
    (explicitCoeff0_trace_eq_explicitCor0_comp_explicitShapiro0
      (G := U) (U := V.subgroupOf U) (M := A))
    (explicitMap0 G (DiscreteCoind G V A) (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      p (DiscreteCoind.pullback_smul _ _ _ _ _) x)
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at htrace
  rw [← htrace]
  apply Subtype.ext
  rw [coe_explicitCoeff0, explicitShapiro0_apply, coe_explicitCoeff0, coe_explicitMap0]
  -- The additive projections of the bundled traces share their function fields.
  change ((t).toAddMonoidHom (x : DiscreteCoind G V A)) 1 =
    (τ).toAddMonoidHom (p (x : DiscreteCoind G V A))
  have heval := DFunLike.congr_fun (eval_relativeTrace U V hVU A hsmul)
    (x : DiscreteCoind G V A)
  simpa only [AddMonoidHom.comp_apply, DiscreteCoind.eval_apply,
    DistribMulActionHom.coe_fn_coe] using heval

/-! ### Positive degrees -/

variable [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul U A] [ContinuousSMul V A]

-- A closed subgroup of a profinite group supplies this instance; the equations
-- themselves require only compactness of the intermediate group.
variable [CompactSpace U]

include hsmul in
omit [ContinuousSMul V A] [TotallyDisconnectedSpace G] in
private theorem shapiroMap1_relativeTrace (x : H1 G (DiscreteCoind G V A)) :
    explicitShapiroMap1 G U A
        (explicitCoeff1 G (DiscreteCoind G V A) t continuous_of_discreteTopology x) =
      explicitCoeff1 U (DiscreteCoind U (V.subgroupOf U) A) τ
        DiscreteCoind.continuous_trace
        (explicitMap1 G (DiscreteCoind G V A) U (DiscreteCoind U (V.subgroupOf U) A)
          (ContinuousMonoidHom.subgroupSubtype U) p continuous_of_discreteTopology
          (DiscreteCoind.pullback_smul _ _ _ _ _) x) := by
  rw [explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq G (DiscreteCoind G V A)
    G (DiscreteCoind G U A) (ContinuousMonoidHom.id G) (t).toAddMonoidHom
    continuous_of_discreteTopology (fun g f => (t).map_smul g f)
    U A (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A)
    DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)
    (ContinuousMonoidHom.subgroupSubtype U) p continuous_of_discreteTopology
    (DiscreteCoind.pullback_smul _ _ _ _ _) (ContinuousMonoidHom.id U)
    (τ).toAddMonoidHom DiscreteCoind.continuous_trace (fun u f => (τ).map_smul u f)
    (by ext u; rfl) (eval_relativeTrace U V hVU A hsmul) x

omit [TotallyDisconnectedSpace G] in
/-- In degree one, outer Shapiro intertwines the relative trace of coinduced modules
with corestriction from `V` to `U`, for an arbitrary discrete `U`-module. -/
theorem explicitShapiroMap1_relativeTrace_corestriction
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U))
    (x : H1 G (DiscreteCoind G V A)) :
    explicitShapiroMap1 G U A
        (explicitCoeff1 G (DiscreteCoind G V A) t continuous_of_discreteTopology x) =
      explicitCor1 U A (V.subgroupOf U) hV
        (explicitMap1 V A (V.subgroupOf U) A κ (AddMonoidHom.id A) continuous_id hA
          (explicitShapiroMap1 G V A x)) := by
  rw [shapiroMap1_relativeTrace U V hVU A hsmul,
    ← explicitCor1_comp_explicitShapiroMap1_eq_explicitCoeff1_trace hV,
    AddMonoidHom.comp_apply,
    explicitShapiroMap1_pullback (ContinuousMonoidHom.subgroupSubtype U) κ hκ
      (AddMonoidHom.id A) hA]

include hsmul in
omit [ContinuousSMul V A] [TotallyDisconnectedSpace G] in
private theorem shapiroMap2_relativeTrace (x : H2 G (DiscreteCoind G V A)) :
    explicitShapiroMap2 G U A
        (explicitCoeff2 G (DiscreteCoind G V A) t continuous_of_discreteTopology x) =
      explicitCoeff2 U (DiscreteCoind U (V.subgroupOf U) A) τ
        DiscreteCoind.continuous_trace
        (explicitMap2 G (DiscreteCoind G V A) U (DiscreteCoind U (V.subgroupOf U) A)
          (ContinuousMonoidHom.subgroupSubtype U) p continuous_of_discreteTopology
          (DiscreteCoind.pullback_smul _ _ _ _ _) x) := by
  rw [explicitCoeff2_eq_explicitMap2, explicitCoeff2_eq_explicitMap2,
    explicitShapiroMap2_def]
  have hleft := explicitMap2_comp G (DiscreteCoind G V A)
    G (DiscreteCoind G U A) (ContinuousMonoidHom.id G) (t).toAddMonoidHom
    continuous_of_discreteTopology (fun g f => (t).map_smul g f)
    U A (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A)
    DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)
  have hright := explicitMap2_comp G (DiscreteCoind G V A)
    U (DiscreteCoind U (V.subgroupOf U) A) (ContinuousMonoidHom.subgroupSubtype U)
    p continuous_of_discreteTopology (DiscreteCoind.pullback_smul _ _ _ _ _)
    U A (ContinuousMonoidHom.id U) (τ).toAddMonoidHom DiscreteCoind.continuous_trace
    (fun u f => (τ).map_smul u f)
  have hcomm := explicitMap2_congr_of_eq G (DiscreteCoind G V A) U A
    ((ContinuousMonoidHom.id G).comp (ContinuousMonoidHom.subgroupSubtype U))
    ((ContinuousMonoidHom.subgroupSubtype U).comp (ContinuousMonoidHom.id U))
    ((DiscreteCoind.eval G U A).comp (t).toAddMonoidHom)
    ((τ).toAddMonoidHom.comp p)
    (hf := DiscreteCoind.continuous_eval.comp continuous_of_discreteTopology)
    (hq := DiscreteCoind.continuous_trace.comp continuous_of_discreteTopology)
    (hφ := (ContinuousMonoidHom.id G).comp_map_smul
      (ContinuousMonoidHom.subgroupSubtype U) (t).toAddMonoidHom (DiscreteCoind.eval G U A)
      (fun g f => (t).map_smul g f) (eval_subgroupSubtype_smul G U A))
    (hψ := (ContinuousMonoidHom.subgroupSubtype U).comp_map_smul (ContinuousMonoidHom.id U)
      p (τ).toAddMonoidHom (DiscreteCoind.pullback_smul _ _ _ _ _)
      (fun u f => (τ).map_smul u f))
    (by ext u; rfl) (eval_relativeTrace U V hVU A hsmul)
  exact (DFunLike.congr_fun hleft x).symm.trans
    ((DFunLike.congr_fun hcomm x).trans (DFunLike.congr_fun hright x))

/-- In degree two, outer Shapiro intertwines the relative trace of coinduced modules
with corestriction from `V` to `U`, for an arbitrary discrete `U`-module. -/
theorem explicitShapiroMap2_relativeTrace_corestriction
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U))
    (x : H2 G (DiscreteCoind G V A)) :
    explicitShapiroMap2 G U A
        (explicitCoeff2 G (DiscreteCoind G V A) t continuous_of_discreteTopology x) =
      explicitCor2 U A (V.subgroupOf U) hV
        (explicitMap2 V A (V.subgroupOf U) A κ (AddMonoidHom.id A) continuous_id hA
          (explicitShapiroMap2 G V A x)) := by
  rw [shapiroMap2_relativeTrace U V hVU A hsmul,
    explicitCor2_eq_explicitCoeff2_trace hV, AddMonoidHom.comp_apply,
    ← explicitShapiroMap2_pullback (ContinuousMonoidHom.subgroupSubtype U) κ hκ
      (AddMonoidHom.id A) hA]
  congr 1
  rw [← explicitShapiro2_apply _ _ _ (Subgroup.isClosed_of_isOpen _ hV),
    AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]

end TauCeti.ContCohomology
