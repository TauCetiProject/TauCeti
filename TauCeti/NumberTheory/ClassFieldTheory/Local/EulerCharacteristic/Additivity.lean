/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Exact
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.RightExact
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact

/-!
# Additivity of the local Euler characteristic

This file proves that the three-term local Euler characteristic `χ_F` is multiplicative in short
exact sequences: if `0 → A → B → C → 0` is exact, then `χ_F(B) = χ_F(A) χ_F(C)`. Thus `χ_F`
respects the relations defining the Grothendieck group of finite smooth discrete Galois
representations, and by dévissage along a composition series the value of `χ_F` on any finite
representation is the product of its values on the simple constituents. This is the reduction that
underlies Tate's local Euler characteristic formula `χ_F(A) = [𝒪_F : #A · 𝒪_F]⁻¹`.

## Main results

* `TauCeti.ClassFieldTheory.localEulerCharacteristic_mul_of_exact`: multiplicativity in a short
  exact sequence `0 → A → B → C → 0` with `B` finite and smooth discrete and `C` discrete.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.8.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.3.1).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

attribute [local instance] TopRep.distribMulAction

variable {n : ℕ} {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The explicit `H⁰` of a discrete module has the cardinality of the continuous cohomology
`H⁰`. -/
private theorem natCard_H0_eq (X : GalRep n F) [DiscreteTopology X.V] :
    Nat.card (H0 (Field.absoluteGaloisGroup F) X.V) = Nat.card (continuousCohomology 0 X) :=
  Nat.card_congr
    (((explicitH0IsoContinuousCohomology (Field.absoluteGaloisGroup F) X.V
      ).toContinuousLinearEquiv.toAddEquiv).trans
        (ofDiscreteModuleRestrictScalarsIntEquiv X 0)).toEquiv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The explicit `H¹` of a discrete module has the cardinality of the continuous cohomology
`H¹`. -/
private theorem natCard_H1_eq (X : GalRep n F) [DiscreteTopology X.V]
    [ContinuousSMul (Field.absoluteGaloisGroup F) X.V] :
    Nat.card (H1 (Field.absoluteGaloisGroup F) X.V) = Nat.card (continuousCohomology 1 X) :=
  Nat.card_congr X.explicitH1AddEquivContinuousCohomologyOfDiscrete.toEquiv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The explicit `H²` of a discrete module has the cardinality of the continuous cohomology
`H²`. -/
private theorem natCard_H2_eq (X : GalRep n F) [DiscreteTopology X.V]
    [ContinuousSMul (Field.absoluteGaloisGroup F) X.V] :
    Nat.card (H2 (Field.absoluteGaloisGroup F) X.V) = Nat.card (continuousCohomology 2 X) :=
  Nat.card_congr X.explicitH2AddEquivContinuousCohomologyOfDiscrete.toEquiv

/-- The cardinality identity of the nine-term long exact sequence `H⁰ → H¹ → H²` of a short exact
sequence `0 → A → B → C → 0`, in terms of the continuous cohomology of `A`, `B` and `C`. -/
private theorem natCard_continuousCohomology_identity_of_exact (hn : IsUnit (n : F))
    {A B C : GalRep n F} [Finite B.V] [Fact (IsSmoothDiscrete (ZMod n) B)]
    [DiscreteTopology A.V] [DiscreteTopology B.V] [DiscreteTopology C.V]
    [ContinuousSMul (Field.absoluteGaloisGroup F) A.V]
    [ContinuousSMul (Field.absoluteGaloisGroup F) B.V]
    [ContinuousSMul (Field.absoluteGaloisGroup F) C.V]
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    Nat.card (continuousCohomology 0 B) * Nat.card (continuousCohomology 2 B) *
        (Nat.card (continuousCohomology 1 A) * Nat.card (continuousCohomology 1 C)) =
      Nat.card (continuousCohomology 1 B) *
        (Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
          (Nat.card (continuousCohomology 0 C) * Nat.card (continuousCohomology 2 C))) := by
  let S : DiscreteShortExact (Field.absoluteGaloisGroup F) A.V B.V C.V :=
    { incl := f.hom.toAddMonoidHom
      proj := g.hom.toAddMonoidHom
      incl_equivariant := fun σ a ↦ f.hom.isIntertwining σ a
      proj_equivariant := fun σ b ↦ g.hom.isIntertwining σ b
      incl_injective := hf
      proj_surjective := hg
      exact := hfg }
  have hlast := explicitCoeff2_surjective hn g hg S.projDistribMulActionHom
    S.projDistribMulActionHom_apply
  have hex := AddMonoidHom.card_mul_card_mul_card_mul_card_mul_card_of_exact
    (explicitCoeff0 _ A.V S.inclDistribMulActionHom)
    (explicitCoeff0 _ B.V S.projDistribMulActionHom) S.explicitDelta0
    (explicitCoeff1 _ A.V S.inclDistribMulActionHom continuous_of_discreteTopology)
    (explicitCoeff1 _ B.V S.projDistribMulActionHom continuous_of_discreteTopology)
    S.explicitDelta1
    (explicitCoeff2 _ A.V S.inclDistribMulActionHom continuous_of_discreteTopology)
    (explicitCoeff2 _ B.V S.projDistribMulActionHom continuous_of_discreteTopology)
    S.explicitLongExact_H0A S.explicitLongExact_H0B S.explicitLongExact_H0C
    S.explicitLongExact_H1A S.explicitLongExact_H1B S.explicitLongExact_H1C
    S.explicitLongExact_H2A S.explicitLongExact_H2B hlast
  rw [natCard_H0_eq A, natCard_H0_eq B, natCard_H0_eq C, natCard_H1_eq A, natCard_H1_eq B,
    natCard_H1_eq C, natCard_H2_eq A, natCard_H2_eq B, natCard_H2_eq C] at hex
  ring_nf at hex ⊢
  exact hex.symm

/-- Multiplicativity of the local Euler characteristic follows from the cardinality identity
relating the continuous cohomology of `A`, `B` and `C`. -/
private theorem localEulerCharacteristic_mul_of_natCard_identity (hn : (n : F) ≠ 0)
    {A B C : GalRep n F} [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] [Finite B.V]
    [Fact (IsSmoothDiscrete (ZMod n) B)] [Finite C.V] [Fact (IsSmoothDiscrete (ZMod n) C)]
    (h : Nat.card (continuousCohomology 0 B) * Nat.card (continuousCohomology 2 B) *
        (Nat.card (continuousCohomology 1 A) * Nat.card (continuousCohomology 1 C)) =
      Nat.card (continuousCohomology 1 B) *
        (Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
          (Nat.card (continuousCohomology 0 C) * Nat.card (continuousCohomology 2 C)))) :
    localEulerCharacteristic hn B =
      localEulerCharacteristic hn A * localEulerCharacteristic hn C := by
  apply Subtype.ext
  apply Units.ext
  simp only [localEulerCharacteristic_coe, Subgroup.coe_mul, Units.val_mul]
  have hhex : (Nat.card (continuousCohomology 0 B) : ℚ) *
          Nat.card (continuousCohomology 2 B) *
          (Nat.card (continuousCohomology 1 A) * Nat.card (continuousCohomology 1 C)) =
        Nat.card (continuousCohomology 1 B) *
          (Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
            (Nat.card (continuousCohomology 0 C) * Nat.card (continuousCohomology 2 C))) := by
    exact_mod_cast h
  have hA₁ : Finite (continuousCohomology 1 A) := finite_H hn A Fact.out (by omega)
  have hB₁ : Finite (continuousCohomology 1 B) := finite_H hn B Fact.out (by omega)
  have hC₁ : Finite (continuousCohomology 1 C) := finite_H hn C Fact.out (by omega)
  have hA₁ne : (Nat.card (continuousCohomology 1 A) : ℚ) ≠ 0 := by
    exact_mod_cast (@Nat.card_pos (continuousCohomology 1 A) inferInstance hA₁).ne'
  have hB₁ne : (Nat.card (continuousCohomology 1 B) : ℚ) ≠ 0 := by
    exact_mod_cast (@Nat.card_pos (continuousCohomology 1 B) inferInstance hB₁).ne'
  have hC₁ne : (Nat.card (continuousCohomology 1 C) : ℚ) ≠ 0 := by
    exact_mod_cast (@Nat.card_pos (continuousCohomology 1 C) inferInstance hC₁).ne'
  field_simp [hA₁ne, hB₁ne, hC₁ne]
  ring_nf at hhex ⊢
  exact hhex

/-- **Additivity of the local Euler characteristic.** If
`0 → A → B → C → 0` is an exact sequence of representations with `B` finite and smooth discrete
and `C` discrete, then `χ_F(B) = χ_F(A) χ_F(C)`. Finiteness of `A` and `C` and smoothness of `A`
and `C` follow from the sequence (`TauCeti.IsSmoothDiscrete.of_injective`,
`TauCeti.IsSmoothDiscrete.of_surjective`). Discreteness of `C` is assumed: the topology of `C` is
part of its data, and a continuous surjection from a discrete module need not have discrete
target. -/
theorem localEulerCharacteristic_mul_of_exact (hn : IsUnit (n : F)) {A B C : GalRep n F}
    [Finite B.V] [Fact (IsSmoothDiscrete (ZMod n) B)] [DiscreteTopology C.V]
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    haveI : Finite A.V := .of_injective _ hf
    haveI : Finite C.V := .of_surjective _ hg
    haveI : Fact (IsSmoothDiscrete (ZMod n) A) := ⟨.of_injective f hf Fact.out⟩
    haveI : Fact (IsSmoothDiscrete (ZMod n) C) :=
      ⟨.of_surjective g hg (IsSmoothDiscrete.stabilizer_isOpen Fact.out)⟩
    localEulerCharacteristic hn.ne_zero B =
      localEulerCharacteristic hn.ne_zero A * localEulerCharacteristic hn.ne_zero C := by
  have : Finite A.V := .of_injective _ hf
  have : Finite C.V := .of_surjective _ hg
  have : Fact (IsSmoothDiscrete (ZMod n) A) := ⟨.of_injective f hf Fact.out⟩
  have : Fact (IsSmoothDiscrete (ZMod n) C) :=
    ⟨.of_surjective g hg (IsSmoothDiscrete.stabilizer_isOpen Fact.out)⟩
  let _ : DiscreteTopology A.V :=
    (Fact.out : IsSmoothDiscrete (ZMod n) A).discreteTopology
  let _ : DiscreteTopology B.V :=
    (Fact.out : IsSmoothDiscrete (ZMod n) B).discreteTopology
  let _ : ContinuousSMul (Field.absoluteGaloisGroup F) A.V :=
    (Fact.out : IsSmoothDiscrete (ZMod n) A).continuousSMul
  let _ : ContinuousSMul (Field.absoluteGaloisGroup F) B.V :=
    (Fact.out : IsSmoothDiscrete (ZMod n) B).continuousSMul
  let _ : ContinuousSMul (Field.absoluteGaloisGroup F) C.V :=
    (Fact.out : IsSmoothDiscrete (ZMod n) C).continuousSMul
  exact localEulerCharacteristic_mul_of_natCard_identity hn.ne_zero
    (natCard_continuousCohomology_identity_of_exact hn f g hf hfg hg)

end TauCeti.ClassFieldTheory
