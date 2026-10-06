/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Explicit
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule

import TauCeti.Algebra.Group.Hom.Instances

/-!
# Local Tate duality for the named evaluation pairing

Let `F` be a nonarchimedean local field, `n` a natural number invertible in `F`, and `A` a finite
smooth discrete `ZMod n`-representation of `G_F`, with Tate dual `A' = Hom(A, μₙ)`
(`TauCeti.ClassFieldTheory.tateDual`). For `i + j = 2`, the local Tate-duality pairing

```text
Hⁱ(G_F, A') × Hʲ(G_F, A) → H²(G_F, μₙ) ≃ ZMod n
```

(`TauCeti.ClassFieldTheory.tateDualityPairing`, the cup product along the evaluation pairing
followed by an identification `tr` of `H²(G_F, μₙ)` with `ZMod n`) induces bijections
`Hʲ(G_F, A) ≃ Hom(Hⁱ(G_F, A'), ZMod n)`: it separates the points of `Hʲ(G_F, A)`, and every
homomorphism `Hⁱ(G_F, A') → ZMod n` is pairing with a class of `Hʲ(G_F, A)`
(`TauCeti.ClassFieldTheory.tateDualityPairing_flip_perfect`).

These are Tate's duality maps `αⱼ : Hʲ(G_F, A) → Hom(Hⁱ(G_F, A'), H²(G_F, μₙ))` on explicit
cocycles, which are bijective (`TauCeti.ClassFieldTheory.dualityMap0_kummerCoeff_bijective` and
its companions), read through the identification of the pairing with the explicit evaluation cup
(`TauCeti.ClassFieldTheory.tateDualityPairing_eq_explicitDualityPairing02` and its companions).

## Main results

* `TauCeti.ClassFieldTheory.tateDualityPairing_flip_perfect`: for `n` invertible in `F`, the
  Tate-duality pairing identifies `Hʲ(G_F, A)` with the `ZMod n`-dual of `Hⁱ(G_F, A')`.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.2, Theorem 2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.6).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.1.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

attribute [local instance] TopRep.distribMulAction absoluteGaloisGroupAction
  continuousSMul_absoluteGaloisGroupAction

variable {n : ℕ}

section Degrees

variable {F : Type} [Field F] (tr : continuousCohomology 2 (muNRep n F) ≃+ ZMod n)

/-- `tr`, read on the explicit second cohomology of `AbsoluteGaloisGroup F` with coefficients
`μₙ = KummerCoeff F n`. -/
private def explicitTr : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n) ≃+ ZMod n :=
  ((explicitMap2Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (kummerCoeffEquivMuNRep n F)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (kummerCoeffEquivMuNRep_smul n F)).trans
    (muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete).trans tr

/-- `explicitTr` applies the explicit pullback before `tr`. -/
private theorem explicitTr_apply (z : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    explicitTr tr z = tr ((muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete
      (explicitMap2 _ _ _ _ (absoluteGaloisGroupRestrictEquiv F)
        (kummerCoeffEquivMuNRep n F).toAddMonoidHom continuous_of_discreteTopology
        (kummerCoeffEquivMuNRep_smul n F) z)) :=
  congrArg (fun w => tr ((muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete w))
    (explicitMap2Equiv_apply _ _ _ _ _ _ _ _ _ z)

variable [NeZero n] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (hn : IsUnit (n : F)) (A : GalRep n F) [DiscreteTopology A.V] [Finite A.V]
  [hA : Fact (IsSmoothDiscrete (ZMod n) A)]

include hn

/-- Duality in degrees `(0, 2)`: Tate's `α₂` on explicit cocycles
(`dualityMap2_kummerCoeff_bijective`), read through
`tateDualityPairing_eq_explicitDualityPairing02`. -/
private theorem flip_perfect_zero_two (hij : 0 + 2 = 2) :
    (∀ y : continuousCohomology 2 A,
        (∀ x : continuousCohomology 0 (tateDual A), tateDualityPairing A tr 0 2 hij x y = 0) →
          y = 0) ∧
      ∀ ψ : continuousCohomology 0 (tateDual A) →+ ZMod n,
        ∃ y : continuousCohomology 2 A,
          ∀ x : continuousCohomology 0 (tateDual A), tateDualityPairing A tr 0 2 hij x y = ψ x := by
  have := hA.out.continuousSMul
  have := (isSmoothDiscrete_tateDual A hA.out).continuousSMul
  refine forall_eq_zero_and_exists_eq_of_bijective_of_addEquiv
    (tateDualityPairing A tr 0 2 hij)
    (((AddEquiv.ofBijective _ (explicitMap0_bijective _ _
        (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
        (absoluteGaloisGroupRestrictEquiv F).surjective (internalHomEquivTateDual A)
        (internalHomEquivTateDual_smul A))).trans
      (explicitH0IsoContinuousCohomology _ (tateDual A).V).toContinuousLinearEquiv.toAddEquiv).trans
      (ofDiscreteModuleRestrictScalarsIntEquiv (tateDual A) 0))
    ((explicitMap2Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (AddEquiv.refl A.V)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (absoluteGaloisGroupRestrictEquiv_smul A)).trans
      A.explicitH2AddEquivContinuousCohomologyOfDiscrete)
    ((AddMonoidHom.compHom (explicitTr (F := F) tr).toAddMonoidHom).comp
      (dualityMap2 _ A.V (KummerCoeff F n)))
    ((AddEquiv.bijective (AddEquiv.addMonoidHomCongrRight (explicitTr (F := F) tr))).comp
      (dualityMap2_kummerCoeff_bijective hn A.V (ZModModule.char_nsmul_eq_zero n))) fun x y => ?_
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [dualityMap2_eq_explicitDualityPairing02, explicitTr_apply]
  -- The comparison theorem is stated with the underlying maps of the equivalences, whose
  -- compatibility proofs mention `toAddMonoidHom`; `convert` matches them up to those proofs.
  convert tateDualityPairing_eq_explicitDualityPairing02 A tr hij x y using 3
  · exact congrArg (ofDiscreteModuleRestrictScalarsIntEquiv (tateDual A) 0)
      (Iso.toContinuousLinearEquiv_apply _ _)
  · exact congrArg A.explicitH2AddEquivContinuousCohomologyOfDiscrete
      (explicitMap2Equiv_apply _ _ _ _ _ _ _ _ _ y)

/-- Duality in degrees `(1, 1)`: Tate's `α₁` on explicit cocycles
(`dualityMap1_kummerCoeff_bijective`), which is minus the swapped evaluation cup, read through
`tateDualityPairing_eq_explicitDualityPairing11`. -/
private theorem flip_perfect_one_one (hij : 1 + 1 = 2) :
    (∀ y : continuousCohomology 1 A,
        (∀ x : continuousCohomology 1 (tateDual A), tateDualityPairing A tr 1 1 hij x y = 0) →
          y = 0) ∧
      ∀ ψ : continuousCohomology 1 (tateDual A) →+ ZMod n,
        ∃ y : continuousCohomology 1 A,
          ∀ x : continuousCohomology 1 (tateDual A), tateDualityPairing A tr 1 1 hij x y = ψ x := by
  have := hA.out.continuousSMul
  have := (isSmoothDiscrete_tateDual A hA.out).continuousSMul
  refine forall_eq_zero_and_exists_eq_of_bijective_of_addEquiv
    (tateDualityPairing A tr 1 1 hij)
    ((explicitMap1Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (internalHomEquivTateDual A)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (internalHomEquivTateDual_smul A)).trans
      (tateDual A).explicitH1AddEquivContinuousCohomologyOfDiscrete)
    ((explicitMap1Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (AddEquiv.refl A.V)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (absoluteGaloisGroupRestrictEquiv_smul A)).trans
      A.explicitH1AddEquivContinuousCohomologyOfDiscrete)
    (-(AddMonoidHom.compHom (explicitTr (F := F) tr).toAddMonoidHom).comp
      (dualityMap1 _ A.V (KummerCoeff F n)))
    (neg_involutive.bijective.comp
      ((AddEquiv.bijective (AddEquiv.addMonoidHomCongrRight (explicitTr (F := F) tr))).comp
        (dualityMap1_kummerCoeff_bijective hn A.V (ZModModule.char_nsmul_eq_zero n)))) fun x y => ?_
  simp only [AddMonoidHom.neg_apply, AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [dualityMap1_eq_neg_explicitDualityPairing11, map_neg, neg_neg, explicitTr_apply]
  -- As in degrees `(0, 2)`, `convert` matches the equivalences with their underlying maps.
  convert tateDualityPairing_eq_explicitDualityPairing11 A tr hij x y using 3
  · exact congrArg (tateDual A).explicitH1AddEquivContinuousCohomologyOfDiscrete
      (explicitMap1Equiv_apply _ _ _ _ _ _ _ _ _ x)
  · exact congrArg A.explicitH1AddEquivContinuousCohomologyOfDiscrete
      (explicitMap1Equiv_apply _ _ _ _ _ _ _ _ _ y)

/-- Duality in degrees `(2, 0)`: Tate's `α₀` on explicit cocycles
(`dualityMap0_kummerCoeff_bijective`), read through
`tateDualityPairing_eq_explicitDualityPairing20`. -/
private theorem flip_perfect_two_zero (hij : 2 + 0 = 2) :
    (∀ y : continuousCohomology 0 A,
        (∀ x : continuousCohomology 2 (tateDual A), tateDualityPairing A tr 2 0 hij x y = 0) →
          y = 0) ∧
      ∀ ψ : continuousCohomology 2 (tateDual A) →+ ZMod n,
        ∃ y : continuousCohomology 0 A,
          ∀ x : continuousCohomology 2 (tateDual A), tateDualityPairing A tr 2 0 hij x y = ψ x := by
  have := hA.out.continuousSMul
  have := (isSmoothDiscrete_tateDual A hA.out).continuousSMul
  refine forall_eq_zero_and_exists_eq_of_bijective_of_addEquiv
    (tateDualityPairing A tr 2 0 hij)
    ((explicitMap2Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F) (internalHomEquivTateDual A)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (internalHomEquivTateDual_smul A)).trans
      (tateDual A).explicitH2AddEquivContinuousCohomologyOfDiscrete)
    (((AddEquiv.ofBijective _ (explicitMap0_bijective _ _
        (absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F →* AbsoluteGaloisGroup F)
        (absoluteGaloisGroupRestrictEquiv F).surjective (AddEquiv.refl A.V)
        (absoluteGaloisGroupRestrictEquiv_smul A))).trans
      (explicitH0IsoContinuousCohomology _ A.V).toContinuousLinearEquiv.toAddEquiv).trans
      (ofDiscreteModuleRestrictScalarsIntEquiv A 0))
    ((AddMonoidHom.compHom (explicitTr (F := F) tr).toAddMonoidHom).comp
      (dualityMap0 _ A.V (KummerCoeff F n)))
    ((AddEquiv.bijective (AddEquiv.addMonoidHomCongrRight (explicitTr (F := F) tr))).comp
      (dualityMap0_kummerCoeff_bijective hn A.V (ZModModule.char_nsmul_eq_zero n))) fun x y => ?_
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [dualityMap0_eq_explicitDualityPairing20, explicitTr_apply]
  -- As in degrees `(0, 2)`, `convert` matches the equivalences with their underlying maps.
  convert tateDualityPairing_eq_explicitDualityPairing20 A tr hij x y using 3
  · exact congrArg (tateDual A).explicitH2AddEquivContinuousCohomologyOfDiscrete
      (explicitMap2Equiv_apply _ _ _ _ _ _ _ _ _ x)
  · exact congrArg (ofDiscreteModuleRestrictScalarsIntEquiv A 0)
      (Iso.toContinuousLinearEquiv_apply _ _)

end Degrees

/-- **Local Tate duality for the named evaluation pairing.** Let `F` be a nonarchimedean local
field, `n` invertible in `F`, and `A` a finite smooth discrete `ZMod n`-representation of `G_F`,
with Tate dual `A' = Hom(A, μₙ)`. For complementary degrees `i + j = 2`, the Tate-duality pairing
`Hⁱ(G_F, A') × Hʲ(G_F, A) → ZMod n`, formed with the evaluation pairing and an identification
`tr` of `H²(G_F, μₙ)` with `ZMod n`, identifies `Hʲ(G_F, A)` with `Hom(Hⁱ(G_F, A'), ZMod n)`: it
separates the points of `Hʲ(G_F, A)`, and every homomorphism `Hⁱ(G_F, A') → ZMod n` is pairing
with some class of `Hʲ(G_F, A)`. -/
theorem tateDualityPairing_flip_perfect {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (hn : IsUnit (n : F)) (A : GalRep n F)
    [DiscreteTopology A.V] [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)]
    (tr : continuousCohomology 2 (muNRep n F) ≃+ ZMod n) (i j : ℕ) (hij : i + j = 2) :
    (∀ y : continuousCohomology j A,
        (∀ x : continuousCohomology i (tateDual A), tateDualityPairing A tr i j hij x y = 0) →
          y = 0) ∧
      ∀ ψ : continuousCohomology i (tateDual A) →+ ZMod n,
        ∃ y : continuousCohomology j A,
          ∀ x : continuousCohomology i (tateDual A), tateDualityPairing A tr i j hij x y = ψ x := by
  have : NeZero n := NeZero.of_neZero_natCast F (h := ⟨hn.ne_zero⟩)
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : i = 0 ∧ j = 2 ∨ i = 1 ∧ j = 1 ∨ i = 2 ∧ j = 0 := by
    omega
  · exact flip_perfect_zero_two tr hn A hij
  · exact flip_perfect_one_one tr hn A hij
  · exact flip_perfect_two_zero tr hn A hij

end TauCeti.ClassFieldTheory
