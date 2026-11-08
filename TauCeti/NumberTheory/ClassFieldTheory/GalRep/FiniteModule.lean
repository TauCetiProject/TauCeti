/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso

/-!
# Finite discrete modules as Galois representations

A finite discrete module for the separable-closure Galois group gives a `GalRep` over
`ZMod (Nat.card M)`. The carrier dictionary and the comparisons in degrees zero, one and two
transport explicit cohomology to continuous cohomology without choosing scalars at use sites.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable (K : Type) [Field K] (M : Type) [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction (AbsoluteGaloisGroup K) M]
  [ContinuousSMul (AbsoluteGaloisGroup K) M] [Finite M]

/-- A finite discrete Galois module as a representation over `ZMod (Nat.card M)`,
with the algebraic-closure Galois group acting by restriction to the separable closure. -/
def finiteModuleRep : GalRep (Nat.card M) K :=
  let : Module (ZMod (Nat.card M)) M := AddCommGroup.zmodModule
    (fun _ ↦ card_nsmul_eq_zero')
  let : ContinuousSMul (ZMod (Nat.card M)) M := ⟨continuous_of_discreteTopology⟩
  TopRep.res
    (absoluteGaloisGroupRestrictEquiv K : Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
    (ofDiscreteModule (ZMod (Nat.card M)) (AbsoluteGaloisGroup K) M)

/-- The representation keeps the discrete topology of the original module. -/
instance : DiscreteTopology (finiteModuleRep K M).V :=
  inferInstanceAs (DiscreteTopology M)

/-- The representation keeps the finite carrier of the original module. -/
instance : Finite (finiteModuleRep K M).V := inferInstanceAs (Finite M)

/-- The carrier dictionary for a finite discrete Galois module.
`TopRep.res` and `ofDiscreteModule` retain the carrier, so this map is the identity. -/
def finiteModuleEquivRep : M ≃+ (finiteModuleRep K M).V := AddEquiv.refl _

attribute [local instance] TopRep.distribMulAction

omit [ContinuousSMul (AbsoluteGaloisGroup K) M] [Finite M] in
/-- The carrier dictionary respects the Galois action along restriction. -/
@[simp]
theorem finiteModuleEquivRep_smul (g : Field.absoluteGaloisGroup K) (x : M) :
    finiteModuleEquivRep K M (absoluteGaloisGroupRestrictEquiv K g • x) =
      g • finiteModuleEquivRep K M x := by
  rw [TopRep.distribMulAction_smul]
  -- Restriction composes the original action and does not change its operators.
  rfl

/-- Continuity of the original action makes the associated representation smooth discrete. -/
instance : Fact (IsSmoothDiscrete (ZMod (Nat.card M)) (finiteModuleRep K M)) := by
  let : Module (ZMod (Nat.card M)) M := AddCommGroup.zmodModule
    (fun _ ↦ card_nsmul_eq_zero')
  let : ContinuousSMul (ZMod (Nat.card M)) M := ⟨continuous_of_discreteTopology⟩
  exact ⟨(ofDiscreteModule_isSmoothDiscrete (ZMod (Nat.card M))
    (AbsoluteGaloisGroup K) M).res (absoluteGaloisGroupRestrictEquiv K).continuous⟩

/-- The action on the associated representation is continuous. -/
instance : ContinuousSMul (Field.absoluteGaloisGroup K) (finiteModuleRep K M).V :=
  (Fact.out : IsSmoothDiscrete (ZMod (Nat.card M)) (finiteModuleRep K M)).continuousSMul

/-- Explicit invariants agree with degree-zero continuous cohomology of the representation. -/
def finiteModuleRepH0Equiv :
    H0 (AbsoluteGaloisGroup K) M ≃+ continuousCohomology 0 (finiteModuleRep K M) :=
  (AddEquiv.ofBijective _ (explicitMap0_bijective (AbsoluteGaloisGroup K) M
    (absoluteGaloisGroupRestrictEquiv K : Field.absoluteGaloisGroup K →* _)
    (absoluteGaloisGroupRestrictEquiv K).surjective (finiteModuleEquivRep K M).toAddMonoidHom
    (finiteModuleEquivRep K M).bijective (finiteModuleEquivRep_smul K M))).trans <|
    (explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup K)
      (finiteModuleRep K M).V).toContinuousLinearEquiv.toAddEquiv.trans
      (ofDiscreteModuleRestrictScalarsIntEquiv (finiteModuleRep K M) 0)

/-- Explicit first cohomology agrees with continuous cohomology of the representation. -/
def finiteModuleRepH1Equiv :
    H1 (AbsoluteGaloisGroup K) M ≃+ continuousCohomology 1 (finiteModuleRep K M) :=
  (explicitMap1Equiv (AbsoluteGaloisGroup K) M (Field.absoluteGaloisGroup K)
    (finiteModuleRep K M).V (absoluteGaloisGroupRestrictEquiv K) (finiteModuleEquivRep K M)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (finiteModuleEquivRep_smul K M)).trans
      (finiteModuleRep K M).explicitH1AddEquivContinuousCohomologyOfDiscrete

/-- Explicit second cohomology agrees with continuous cohomology of the representation. -/
def finiteModuleRepH2Equiv :
    H2 (AbsoluteGaloisGroup K) M ≃+ continuousCohomology 2 (finiteModuleRep K M) :=
  (explicitMap2Equiv (AbsoluteGaloisGroup K) M (Field.absoluteGaloisGroup K)
    (finiteModuleRep K M).V (absoluteGaloisGroupRestrictEquiv K) (finiteModuleEquivRep K M)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (finiteModuleEquivRep_smul K M)).trans
      (finiteModuleRep K M).explicitH2AddEquivContinuousCohomologyOfDiscrete

end TauCeti.ClassFieldTheory
