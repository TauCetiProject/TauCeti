/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.RestrictScalars

/-!
# The local Tate-duality pairing on explicit cocycles

The local Tate-duality pairing `TauCeti.ClassFieldTheory.tateDualityPairing` of a Galois
representation `A : GalRep n F` is the canonical cup product on Mathlib's continuous cohomology of
`Field.absoluteGaloisGroup F`, along the evaluation pairing `Hom(A, μₙ) × A → μₙ`. Tate's duality
maps `TauCeti.ContCohomology.dualityMap0`, `dualityMap1`, `dualityMap2`, and the local duality
theorems about them, live on explicit inhomogeneous cocycles of `AbsoluteGaloisGroup F`, the Galois
group of the separable closure, with coefficients `μₙ = TauCeti.KummerCoeff F n` and the internal
hom `Hom(A, μₙ)`. This file identifies the two.

The carrier of `A` is a module over `AbsoluteGaloisGroup F` through the comparison
`absoluteGaloisGroupRestrictEquiv` (`TauCeti.ClassFieldTheory.absoluteGaloisGroupAction`), and the
internal hom from `A` to `KummerCoeff F n` for that action is the Tate dual
(`TauCeti.ClassFieldTheory.internalHomEquivTateDual`). Pulling the explicit cocycles back along
the comparison and passing to continuous cohomology, the Tate-duality pairing of the resulting
classes is the image in `ZMod n` of their explicit evaluation cup, in each of the three bidegrees
of total degree two.

## Main definitions

* `TauCeti.ClassFieldTheory.absoluteGaloisGroupAction`: the action of `AbsoluteGaloisGroup F` on
  the carrier of a Galois representation.
* `TauCeti.ClassFieldTheory.internalHomEquivTateDual`: the internal hom from `A` to `μₙ` over the
  separable closure is the Tate dual.

## Main results

* `TauCeti.ClassFieldTheory.tateDualityPairing_eq_explicitDualityPairing02`,
  `tateDualityPairing_eq_explicitDualityPairing11` and
  `tateDualityPairing_eq_explicitDualityPairing20`: the Tate-duality pairing on explicit cocycles.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

attribute [local instance] TopRep.distribMulAction

variable {n : ℕ} {F : Type} [Field F]

/-! ### Restricting the action to the separable closure -/

/-- The action of `AbsoluteGaloisGroup F` on a Galois representation `A`, through the comparison
`absoluteGaloisGroupRestrictEquiv` with `Field.absoluteGaloisGroup F`. -/
@[instance_reducible]
def absoluteGaloisGroupAction (A : GalRep n F) : DistribMulAction (AbsoluteGaloisGroup F) A.V :=
  DistribMulAction.compHom A.V
    (absoluteGaloisGroupRestrictEquiv F).symm.toMulEquiv.toMonoidHom

attribute [local instance] absoluteGaloisGroupAction

/-- `AbsoluteGaloisGroup F` acts through the inverse of `absoluteGaloisGroupRestrictEquiv`. -/
theorem absoluteGaloisGroupAction_smul (A : GalRep n F) (g : AbsoluteGaloisGroup F) (a : A.V) :
    g • a = A.ρ ((absoluteGaloisGroupRestrictEquiv F).symm g) a :=
  (rfl)

/-- Restricting the action back along `absoluteGaloisGroupRestrictEquiv` recovers the action of
`A`. -/
theorem absoluteGaloisGroupRestrictEquiv_smul (A : GalRep n F) (h : Field.absoluteGaloisGroup F)
    (a : A.V) : absoluteGaloisGroupRestrictEquiv F h • a = A.ρ h a := by
  rw [absoluteGaloisGroupAction_smul, ContinuousMulEquiv.symm_apply_apply]

/-- The restricted action is continuous when the action of `A` is. -/
theorem continuousSMul_absoluteGaloisGroupAction (A : GalRep n F)
    [ContinuousSMul (Field.absoluteGaloisGroup F) A.V] :
    ContinuousSMul (AbsoluteGaloisGroup F) A.V :=
  MulAction.continuousSMul_compHom (absoluteGaloisGroupRestrictEquiv F).symm.continuous

/-! ### The Tate dual over the separable closure -/

section TateDual

variable (A : GalRep n F)

/-- **The Tate dual read over the separable closure**: the internal hom from `A` to
`μₙ = KummerCoeff F n` for the restricted action of `AbsoluteGaloisGroup F` is the Tate dual
`tateDual A`, a homomorphism `φ` going to `kummerCoeffEquivMuNRep ∘ φ`. -/
def internalHomEquivTateDual :
    InternalHom (AbsoluteGaloisGroup F) A.V (KummerCoeff F n) ≃+ (tateDual A).V :=
  ((AddEquiv.mk ⟨InternalHom.toAddMonoidHom, InternalHom.of _, fun _ => rfl, fun _ => rfl⟩
    fun _ _ => rfl).trans (AddEquiv.addMonoidHomCongrRight (kummerCoeffEquivMuNRep n F))).trans
    (tateDualEquiv A).symm

/-- `internalHomEquivTateDual` sends `φ` to the character `kummerCoeffEquivMuNRep ∘ φ`. -/
@[simp]
theorem tateDualEquiv_internalHomEquivTateDual_apply
    (φ : InternalHom (AbsoluteGaloisGroup F) A.V (KummerCoeff F n)) (a : A.V) :
    tateDualEquiv A (internalHomEquivTateDual A φ) a =
      kummerCoeffEquivMuNRep n F (InternalHom.evalPairing _ φ a) := by
  simp [internalHomEquivTateDual, InternalHom.evalPairing_apply]

/-- `internalHomEquivTateDual` intertwines the restricted action with the action on the Tate
dual. -/
theorem internalHomEquivTateDual_smul (h : Field.absoluteGaloisGroup F)
    (φ : InternalHom (AbsoluteGaloisGroup F) A.V (KummerCoeff F n)) :
    internalHomEquivTateDual A (absoluteGaloisGroupRestrictEquiv F h • φ) =
      (tateDual A).ρ h (internalHomEquivTateDual A φ) := by
  refine (tateDualEquiv A).injective (AddMonoidHom.ext fun a => ?_)
  rw [tateDualEquiv_ρ_apply, tateDualEquiv_internalHomEquivTateDual_apply,
    tateDualEquiv_internalHomEquivTateDual_apply, InternalHom.evalPairing_apply,
    InternalHom.toAddMonoidHom_smul, homAction_apply, ← kummerCoeffEquivMuNRep_smul,
    ← map_inv, absoluteGaloisGroupRestrictEquiv_smul, InternalHom.evalPairing_apply]

end TateDual

/-! ### The pairing on explicit cocycles -/

section Comparison

variable (A : GalRep n F) [DiscreteTopology A.V]
  [ContinuousSMul (Field.absoluteGaloisGroup F) A.V]
  [ContinuousSMul (Field.absoluteGaloisGroup F) (tateDual A).V]
  (tr : continuousCohomology 2 (muNRep n F) ≃+ ZMod n)

attribute [local instance] continuousSMul_absoluteGaloisGroupAction

/-- **The `(0, 2)` Tate-duality pairing on explicit cocycles.** For an invariant `x` of the
internal hom and a two-cocycle class `y` of `A` over `AbsoluteGaloisGroup F`, pulled back along
`absoluteGaloisGroupRestrictEquiv` and read in continuous cohomology, the Tate-duality pairing is
the class of the explicit evaluation cup `explicitDualityPairing02 x y`, read in `ZMod n` through
`tr`. -/
theorem tateDualityPairing_eq_explicitDualityPairing02 (hij : 0 + 2 = 2)
    (x : H0 (AbsoluteGaloisGroup F) (InternalHom (AbsoluteGaloisGroup F) A.V (KummerCoeff F n)))
    (y : H2 (AbsoluteGaloisGroup F) A.V) :
    tateDualityPairing A tr 0 2 hij
        (ofDiscreteModuleRestrictScalarsIntEquiv (tateDual A) 0
          ((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F) (tateDual A).V).hom
            (explicitMap0 _ _ (absoluteGaloisGroupRestrictEquiv F :
                Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
              (internalHomEquivTateDual A).toAddMonoidHom (internalHomEquivTateDual_smul A) x)))
        (A.explicitH2AddEquivContinuousCohomologyOfDiscrete
          (explicitMap2 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (AddMonoidHom.id A.V)
            continuous_of_discreteTopology (absoluteGaloisGroupRestrictEquiv_smul A) y)) =
      tr ((muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F)
          (kummerCoeffEquivMuNRep n F).toAddMonoidHom continuous_of_discreteTopology
          (kummerCoeffEquivMuNRep_smul n F)
          (explicitDualityPairing02 (AbsoluteGaloisGroup F) A.V (KummerCoeff F n) x y))) := by
  have hμ : ∀ (φ : (tateDual A).V) (a : A.V),
      (tateDualEquiv A).toAddMonoidHom φ a = (tateEvaluationPairing A).bil φ a := fun φ a =>
    (tateEvaluationPairing_bil A φ a).symm
  rw [tateDualityPairing_def, TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply,
    ← TopPairing.cup_zero_two_ofDiscreteModuleRestrictScalarsInt _ _ hμ,
    explicitAddEquiv_cup02, explicitDualityPairing02_def,
    TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply]
  exact congrArg (fun z => tr (ofDiscreteModuleRestrictScalarsIntEquiv (muNRep n F) 2
      (explicitH2AddEquivContinuousCohomology (Field.absoluteGaloisGroup F) (muNRep n F).V z)))
    (explicitMap2_explicitCup02 (H := Field.absoluteGaloisGroup F) (P := KummerCoeff F n)
      (μ := InternalHom.evalPairing _) (μ' := (tateDualEquiv A).toAddMonoidHom)
      (hμ := continuous_of_discreteTopology) (hμ' := continuous_of_discreteTopology)
      (hequiv := InternalHom.evalPairing_equivariant)
      (hequiv' := TopPairing.equivariant_of_eq (tateEvaluationPairing A) _ hμ)
      (φ := absoluteGaloisGroupRestrictEquiv F)
      (fM := (internalHomEquivTateDual A).toAddMonoidHom) (fN := AddMonoidHom.id A.V)
      (fP := (kummerCoeffEquivMuNRep n F).toAddMonoidHom)
      (hcN := continuous_of_discreteTopology) (hcP := continuous_of_discreteTopology)
      (hfM := internalHomEquivTateDual_smul A) (hfN := absoluteGaloisGroupRestrictEquiv_smul A)
      (hfP := kummerCoeffEquivMuNRep_smul n F)
      (hpair := fun φ a => (tateDualEquiv_internalHomEquivTateDual_apply A φ a).symm) (m := x)
      (b := y)).symm

/-- **The `(1, 1)` Tate-duality pairing on explicit cocycles.** For one-cocycle classes `x` of
the internal hom and `y` of `A` over `AbsoluteGaloisGroup F`, pulled back along
`absoluteGaloisGroupRestrictEquiv` and read in continuous cohomology, the Tate-duality pairing is
the class of the explicit evaluation cup `explicitDualityPairing11 x y`, read in `ZMod n` through
`tr`. -/
theorem tateDualityPairing_eq_explicitDualityPairing11 [Finite A.V] (hij : 1 + 1 = 2)
    (x : H1 (AbsoluteGaloisGroup F) (InternalHom (AbsoluteGaloisGroup F) A.V (KummerCoeff F n)))
    (y : H1 (AbsoluteGaloisGroup F) A.V) :
    tateDualityPairing A tr 1 1 hij
        ((tateDual A).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F)
            (internalHomEquivTateDual A).toAddMonoidHom continuous_of_discreteTopology
            (internalHomEquivTateDual_smul A) x))
        (A.explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (AddMonoidHom.id A.V)
            continuous_of_discreteTopology (absoluteGaloisGroupRestrictEquiv_smul A) y)) =
      tr ((muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F)
          (kummerCoeffEquivMuNRep n F).toAddMonoidHom continuous_of_discreteTopology
          (kummerCoeffEquivMuNRep_smul n F)
          (explicitDualityPairing11 (AbsoluteGaloisGroup F) A.V (KummerCoeff F n) x y))) := by
  have hμ : ∀ (φ : (tateDual A).V) (a : A.V),
      (tateDualEquiv A).toAddMonoidHom φ a = (tateEvaluationPairing A).bil φ a := fun φ a =>
    (tateEvaluationPairing_bil A φ a).symm
  rw [tateDualityPairing_def,
    TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete _ _ hμ,
    explicitDualityPairing11_def]
  exact congrArg (fun z => tr ((muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete z))
    (explicitMap2_explicitCup11 (H := Field.absoluteGaloisGroup F) (P := KummerCoeff F n)
      (μ := InternalHom.evalPairing _) (μ' := (tateDualEquiv A).toAddMonoidHom)
      (hμ := continuous_of_discreteTopology) (hμ' := continuous_of_discreteTopology)
      (hequiv := InternalHom.evalPairing_equivariant)
      (hequiv' := TopPairing.equivariant_of_eq (tateEvaluationPairing A) _ hμ)
      (φ := absoluteGaloisGroupRestrictEquiv F)
      (fM := (internalHomEquivTateDual A).toAddMonoidHom) (fN := AddMonoidHom.id A.V)
      (fP := (kummerCoeffEquivMuNRep n F).toAddMonoidHom)
      (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
      (hcP := continuous_of_discreteTopology)
      (hfM := internalHomEquivTateDual_smul A) (hfN := absoluteGaloisGroupRestrictEquiv_smul A)
      (hfP := kummerCoeffEquivMuNRep_smul n F)
      (hpair := fun φ a => (tateDualEquiv_internalHomEquivTateDual_apply A φ a).symm) (a := x)
      (b := y)).symm

/-- **The `(2, 0)` Tate-duality pairing on explicit cocycles.** For a two-cocycle class `x` of
the internal hom and an invariant `y` of `A` over `AbsoluteGaloisGroup F`, pulled back along
`absoluteGaloisGroupRestrictEquiv` and read in continuous cohomology, the Tate-duality pairing is
the class of the explicit evaluation cup `explicitDualityPairing20 x y`, read in `ZMod n` through
`tr`. -/
theorem tateDualityPairing_eq_explicitDualityPairing20 [Finite A.V] (hij : 2 + 0 = 2)
    (x : H2 (AbsoluteGaloisGroup F) (InternalHom (AbsoluteGaloisGroup F) A.V (KummerCoeff F n)))
    (y : H0 (AbsoluteGaloisGroup F) A.V) :
    tateDualityPairing A tr 2 0 hij
        ((tateDual A).explicitH2AddEquivContinuousCohomologyOfDiscrete
          (explicitMap2 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F)
            (internalHomEquivTateDual A).toAddMonoidHom continuous_of_discreteTopology
            (internalHomEquivTateDual_smul A) x))
        (ofDiscreteModuleRestrictScalarsIntEquiv A 0
          ((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F) A.V).hom
            (explicitMap0 _ _ (absoluteGaloisGroupRestrictEquiv F :
                Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
              (AddMonoidHom.id A.V) (absoluteGaloisGroupRestrictEquiv_smul A) y))) =
      tr ((muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F)
          (kummerCoeffEquivMuNRep n F).toAddMonoidHom continuous_of_discreteTopology
          (kummerCoeffEquivMuNRep_smul n F)
          (explicitDualityPairing20 (AbsoluteGaloisGroup F) A.V (KummerCoeff F n) x y))) := by
  have hμ : ∀ (φ : (tateDual A).V) (a : A.V),
      (tateDualEquiv A).toAddMonoidHom φ a = (tateEvaluationPairing A).bil φ a := fun φ a =>
    (tateEvaluationPairing_bil A φ a).symm
  rw [tateDualityPairing_def, TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply,
    ← TopPairing.cup_two_zero_ofDiscreteModuleRestrictScalarsInt _ _ hμ,
    explicitAddEquiv_cup20, explicitDualityPairing20_def,
    TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply]
  exact congrArg (fun z => tr (ofDiscreteModuleRestrictScalarsIntEquiv (muNRep n F) 2
      (explicitH2AddEquivContinuousCohomology (Field.absoluteGaloisGroup F) (muNRep n F).V z)))
    (explicitMap2_explicitCup20 (G := AbsoluteGaloisGroup F)
      (M := InternalHom (AbsoluteGaloisGroup F) A.V (KummerCoeff F n)) (N := A.V)
      (M' := (tateDual A).V) (N' := A.V) (P' := (muNRep n F).V)
      (H := Field.absoluteGaloisGroup F) (P := KummerCoeff F n)
      (μ := InternalHom.evalPairing _) (μ' := (tateDualEquiv A).toAddMonoidHom)
      (hμ := continuous_of_discreteTopology) (hμ' := continuous_of_discreteTopology)
      (hequiv := InternalHom.evalPairing_equivariant)
      (hequiv' := TopPairing.equivariant_of_eq (tateEvaluationPairing A) _ hμ)
      (φ := absoluteGaloisGroupRestrictEquiv F)
      (fM := (internalHomEquivTateDual A).toAddMonoidHom) (fN := AddMonoidHom.id A.V)
      (fP := (kummerCoeffEquivMuNRep n F).toAddMonoidHom)
      (hcM := continuous_of_discreteTopology) (hcP := continuous_of_discreteTopology)
      (hfM := internalHomEquivTateDual_smul A) (hfN := absoluteGaloisGroupRestrictEquiv_smul A)
      (hfP := kummerCoeffEquivMuNRep_smul n F)
      (hpair := fun φ a => (tateDualEquiv_internalHomEquivTateDual_apply A φ a).symm) (a := x)
      (n := y)).symm

end Comparison

end TauCeti.ClassFieldTheory
