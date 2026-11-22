/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.DotOrbit
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Linear
import TauCeti.Algebra.Lie.Weights.InvariantForm
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import TauCeti.RingTheory.Invariant.OrbitSeparation

/-!
# Dot-invariant and Weyl-invariant polynomials separate orbits

Via `TauCeti.linearInvariants_eq_symmetricAlgebraInvariants`, the linear Weyl invariants `S(H)^W`
coincide with the fixed points of the coroot representation `RootPairing.weylGroupCorootRep`, so
`FixedPoints.exists_mem_subalgebra_eq_zero_and_eq_one` and
`FixedPoints.forall_mem_subalgebra_eq_iff` show that distinct linear Weyl orbits on `H*` are
separated by a Weyl invariant taking value `0` at one weight and `1` at the other
(`TauCeti.exists_mem_linearInvariants_lift_eq_zero_one`,
`TauCeti.forall_mem_linearInvariants_lift_eq_iff`), and via `LieAlgebra.IsKilling.cartanEquivDual`
they separate Weyl orbits on `H`
(`TauCeti.forall_mem_linearInvariants_lift_cartanEquivDual_eq_iff`).

Transporting linear Weyl separation along translation by `ρ`
(`TauCeti.translation_neg_weylVector_mem_linearInvariants_iff`) gives the analogous separation for
dot-invariant polynomials (`TauCeti.exists_mem_dotInvariants_lift_eq_zero_one`,
`TauCeti.forall_mem_dotInvariants_lift_eq_iff`).

This is the invariant-theoretic step of the Harish-Chandra central-character orbit theorem.
It is independent of surjectivity of the Harish-Chandra projection.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §8, central characters.
-/

public section

namespace TauCeti

open LieAlgebra Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

section Linear

open LieAlgebra.IsKilling

/-- Precomposing evaluation at `lam` with the coroot action of `w` is evaluation at `w • lam`. -/
private theorem symmetricAlgebraLift_comp_corootRep_eq
    (w : (rootSystem H).weylGroup) (lam : Dual K H) :
    letI := (rootSystem H).weylGroupCorootRep.symmetricAlgebraMulSemiringAction
    haveI := (rootSystem H).weylGroupCorootRep.smulCommClass_symmetricAlgebraMulSemiringAction
    (SymmetricAlgebra.lift lam).comp
        (MulSemiringAction.toAlgHom K (SymmetricAlgebra K H)
          (Subgroup.equivOp (rootSystem H).weylGroup w)) =
      SymmetricAlgebra.lift (w • lam) := by
  let := (rootSystem H).weylGroupCorootRep.symmetricAlgebraMulSemiringAction
  have := (rootSystem H).weylGroupCorootRep.smulCommClass_symmetricAlgebraMulSemiringAction
  refine _root_.SymmetricAlgebra.algHom_ext <| LinearMap.ext fun h ↦ ?_
  change (SymmetricAlgebra.lift lam)
      ((MulSemiringAction.toAlgHom K (SymmetricAlgebra K H)
        (Subgroup.equivOp (rootSystem H).weylGroup w)) (SymmetricAlgebra.ι K H h)) =
    SymmetricAlgebra.lift (w • lam) (SymmetricAlgebra.ι K H h)
  rw [MulSemiringAction.toAlgHom_apply, Representation.symmetricAlgebraMulSemiringAction_smul,
    Representation.symmetricAlgebra_apply, _root_.SymmetricAlgebra.map_apply_ι,
    SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.lift_ι_apply,
    RootPairing.weylGroupCorootRep_equivOp_apply]
  exact (RootPairing.Equiv.toLinearMap_weightEquiv (w : (rootSystem H).Aut) lam h).symm

/-- **Distinct linear Weyl orbits on `H*` are separated by a Weyl invariant** taking value `0` at
`lam` and `1` at `mu`. -/
theorem exists_mem_linearInvariants_lift_eq_zero_one {lam mu : Dual K H}
    (h : ¬ ∃ w : (rootSystem H).weylGroup, w • lam = mu) :
    ∃ p ∈ linearInvariants H,
      SymmetricAlgebra.lift lam p = 0 ∧ SymmetricAlgebra.lift mu p = 1 := by
  have : Finite (rootSystem H).weylGroup := RootPairing.finite_weylGroup (rootSystem H)
  have : Finite (rootSystem H).weylGroup.op := Finite.of_equiv _ (Subgroup.equivOp _)
  let ρ := (rootSystem H).weylGroupCorootRep
  let := ρ.symmetricAlgebraMulSemiringAction
  have := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  rw [linearInvariants_eq_symmetricAlgebraInvariants,
    ρ.symmetricAlgebraInvariants_eq_fixedPoints]
  refine FixedPoints.exists_mem_subalgebra_eq_zero_and_eq_one fun g hg ↦ h ?_
  let w : (rootSystem H).weylGroup := (Subgroup.equivOp _).symm g
  have hgw : g = Subgroup.equivOp _ w := ((Subgroup.equivOp _).apply_symm_apply g).symm
  rw [hgw, symmetricAlgebraLift_comp_corootRep_eq] at hg
  exact ⟨w, SymmetricAlgebra.lift.injective hg⟩

/-- **The Weyl invariants `S(H)^W` separate linear Weyl orbits on `H*`.** -/
theorem forall_mem_linearInvariants_lift_eq_iff {lam mu : Dual K H} :
    (∀ p ∈ linearInvariants H,
        SymmetricAlgebra.lift lam p = SymmetricAlgebra.lift mu p) ↔
      ∃ w : (rootSystem H).weylGroup, w • lam = mu := by
  have : Finite (rootSystem H).weylGroup := RootPairing.finite_weylGroup (rootSystem H)
  have : Finite (rootSystem H).weylGroup.op := Finite.of_equiv _ (Subgroup.equivOp _)
  let ρ := (rootSystem H).weylGroupCorootRep
  let := ρ.symmetricAlgebraMulSemiringAction
  have := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
  rw [linearInvariants_eq_symmetricAlgebraInvariants,
    ρ.symmetricAlgebraInvariants_eq_fixedPoints, FixedPoints.forall_mem_subalgebra_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    let w : (rootSystem H).weylGroup := (Subgroup.equivOp _).symm g
    have hgw : g = Subgroup.equivOp _ w := ((Subgroup.equivOp _).apply_symm_apply g).symm
    rw [hgw, symmetricAlgebraLift_comp_corootRep_eq] at hg
    exact ⟨w, SymmetricAlgebra.lift.injective hg⟩
  · rintro ⟨w, hw⟩
    refine ⟨Subgroup.equivOp _ w, ?_⟩
    rw [symmetricAlgebraLift_comp_corootRep_eq, hw]

/-- **The Weyl invariants `S(H)^W` separate Weyl orbits on `H`** when read through
`LieAlgebra.IsKilling.cartanEquivDual`. -/
theorem forall_mem_linearInvariants_lift_cartanEquivDual_eq_iff {h₁ h₂ : H} :
    (∀ p ∈ linearInvariants H,
        SymmetricAlgebra.lift (cartanEquivDual H h₁) p =
          SymmetricAlgebra.lift (cartanEquivDual H h₂) p) ↔
      ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv h₁ = h₂ := by
  rw [forall_mem_linearInvariants_lift_eq_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    refine ⟨w⁻¹, (cartanEquivDual H).injective ?_⟩
    rw [cartanEquivDual_coweightEquiv, inv_inv, hw]
  · rintro ⟨w, rfl⟩
    exact ⟨w⁻¹, (cartanEquivDual_coweightEquiv w h₁).symm⟩

end Linear

section Dot

variable {b : (IsKilling.rootSystem H).Base}

/-- Two distinct dot orbits are separated by a dot-invariant polynomial with values zero
and one. The weights need not be integral or dominant. -/
theorem exists_mem_dotInvariants_lift_eq_zero_one {lam mu : Dual K H}
    (h : ¬ ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu) :
    ∃ p ∈ dotInvariants b, SymmetricAlgebra.lift lam p = 0 ∧
      SymmetricAlgebra.lift mu p = 1 := by
  have hlin : ¬ ∃ w : (IsKilling.rootSystem H).weylGroup,
      w • (lam + weylVector (IsKilling.rootSystem H) b) =
        mu + weylVector (IsKilling.rootSystem H) b := by
    rintro ⟨w, hw⟩
    apply h
    refine ⟨w, ?_⟩
    have hw' := congrArg (· - weylVector (IsKilling.rootSystem H) b) hw
    simpa [dotAction_def] using hw'
  obtain ⟨q, hq, hqlam, hqmu⟩ := exists_mem_linearInvariants_lift_eq_zero_one hlin
  refine ⟨(_root_.SymmetricAlgebra.translation (-weylVector (IsKilling.rootSystem H) b)).symm q,
    (translation_neg_weylVector_mem_linearInvariants_iff b).mp (by simpa using hq), ?_, ?_⟩
  · simpa [_root_.SymmetricAlgebra.translation_symm] using hqlam
  · simpa [_root_.SymmetricAlgebra.translation_symm] using hqmu

/-- Equality of all dot-invariant polynomial values characterizes a dot orbit. -/
theorem forall_mem_dotInvariants_lift_eq_iff {lam mu : Dual K H} :
    (∀ p ∈ dotInvariants b, SymmetricAlgebra.lift lam p = SymmetricAlgebra.lift mu p) ↔
      ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu := by
  constructor
  · intro heq
    by_contra h
    obtain ⟨p, hp, hlam, hmu⟩ := exists_mem_dotInvariants_lift_eq_zero_one h
    simpa [hlam, hmu] using heq p hp
  · rintro ⟨w, rfl⟩ p hp
    exact ((mem_dotInvariants_iff.mp hp) w lam).symm

end Dot

end TauCeti
