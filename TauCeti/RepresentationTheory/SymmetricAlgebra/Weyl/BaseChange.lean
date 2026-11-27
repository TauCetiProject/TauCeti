/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Rational
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
import TauCeti.Algebra.Algebra.Pi
import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import TauCeti.RepresentationTheory.BaseChange.Dual
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.SymmetricAlgebra.BaseChange
import TauCeti.RepresentationTheory.SymmetricAlgebra.Degrees
import TauCeti.RingTheory.GradedAlgebra.HilbertSeries
import TauCeti.RingTheory.GradedAlgebra.Subalgebra

/-!
# Field-invariance of Weyl polynomial invariant degrees

This module specializes
`Representation.finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule`, which
establishes graded invariant-dimension invariance under field extensions for an arbitrary
representation, to the Weyl reflection representation on `Dual`: extending a coordinate root
pairing `Q` on `σ → ℚ` to any characteristic-zero field `S` preserves the graded dimensions of
`Sym(M*)^W`:
`RootPairing.finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_rootPairingBaseChange`.
Combined with `RootPairing.Base.equivBaseChangeRationalModel`, this yields the Weyl-specific
graded comparison and multiset invariance of basic invariant degrees across characteristic-zero
ground fields (in `RootPairing.Base`):
`finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_eq_rootPairingBaseChange_rationalModel`
and
`map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual_rootPairingBaseChange_rationalModel`.
-/

public section

open Finset Function Module Representation SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra
  TensorProduct

namespace RootPairing

/-- Extending a coordinate root pairing on `σ → ℚ` to a characteristic-zero field `S` preserves
the dimension of each graded component of the Weyl invariants in `Sym(M*)`. -/
theorem finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_rootPairingBaseChange
    {ι σ S : Type*} [Finite ι] [Fintype σ] [Field S] [CharZero S]
    (Q : RootPairing ι ℚ (σ → ℚ) (σ → ℚ))
    (hQ : ∀ x y, Q.toLinearMap x y = x ⬝ᵥ y) [Q.IsRootSystem] (n : ℕ) :
    Module.finrank S
        ↥(Subalgebra.toSubmodule
            (rootPairingBaseChange S Q hQ).weylGroupRootRep.dual.symmetricAlgebraInvariants ⊓
          homogeneousSubmodule S (Module.Dual S (σ → S)) n) =
      Module.finrank ℚ
        ↥(Subalgebra.toSubmodule Q.weylGroupRootRep.dual.symmetricAlgebraInvariants ⊓
          homogeneousSubmodule ℚ (Module.Dual ℚ (σ → ℚ)) n) := by
  classical
  have : Finite Q.weylGroup := Q.finite_weylGroup
  let eG := weylGroupBaseChangeEquiv S Q hQ
  let ePi : S ⊗[ℚ] (σ → ℚ) ≃ₗ[S] (σ → S) := TensorProduct.piScalarRight ℚ S S σ
  have hePi_tmul (s : S) (x : σ → ℚ) :
      ePi (s ⊗ₜ[ℚ] x) = s • Pi.algebraMap σ ℚ S x := by
    ext j
    simp [ePi, TensorProduct.piScalarRight_apply, Algebra.smul_def, mul_comm, piAlgebraMap_apply]
  have hePi (w : Q.weylGroup) :
      ePi.toLinearMap ∘ₗ (Q.weylGroupRootRep.baseChange S) w =
        ((rootPairingBaseChange S Q hQ).weylGroupRootRep.comp eG.toMonoidHom) w ∘ₗ
          ePi.toLinearMap := by
    refine LinearMap.ext fun z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, _root_.Representation.baseChange_apply,
        LinearMap.baseChange_tmul, hePi_tmul, weylGroupRootRep_apply, map_smul]
      dsimp only [eG]
      rw [weylGroupBaseChangeEquiv_smul]
    | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  let eqvPi : Representation.Equiv (Q.weylGroupRootRep.baseChange S)
      ((rootPairingBaseChange S Q hQ).weylGroupRootRep.comp eG.toMonoidHom) :=
    Representation.Equiv.mk ePi hePi
  let eDual : S ⊗[ℚ] Module.Dual ℚ (σ → ℚ) ≃ₗ[S] Module.Dual S (σ → S) :=
    (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := ℚ) (A := S) (M := σ → ℚ)).trans
      eqvPi.dual.toLinearEquiv
  have heDual (w : Q.weylGroup) (ψ : S ⊗[ℚ] Module.Dual ℚ (σ → ℚ)) :
      (rootPairingBaseChange S Q hQ).weylGroupRootRep.dual (eG w) (eDual ψ) =
        eDual ((Q.weylGroupRootRep.dual.baseChange S) w ψ) := by
    dsimp only [eDual, LinearEquiv.trans_apply]
    rw [← _root_.Representation.dual_baseChange_baseChangeEvaluationEquiv Q.weylGroupRootRep w ψ]
    have h₁ := IntertwiningMap.isIntertwining _ _ eqvPi.dual.toIntertwiningMap w
      (TauCeti.Module.Dual.baseChangeEvaluationEquiv ψ)
    simpa only [_root_.Representation.dual_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_inv, _root_.Representation.Equiv.coe_toIntertwiningMap,
      _root_.Representation.Equiv.toLinearEquiv_apply] using h₁.symm
  let ρS := Q.weylGroupRootRep.dual.baseChange S
  rw [← ρS.finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_of_equiv
    eG eDual heDual n]
  exact finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule
    Q.weylGroupRootRep.dual (L := S) n

namespace Base

/-- **Graded Weyl invariant dimension invariance across characteristic-zero fields.** For any
finite crystallographic root system `P` over a characteristic-zero field `K` with base `b`, and any
characteristic-zero field `L`, the graded components of `Sym(M*)^W` over `K` have the same
dimension as those over `L` for the base-changed rational model `b.rationalModel`. -/
theorem
    finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_eq_rootPairingBaseChange_rationalModel
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {P : RootPairing ι K M N}
    [Finite ι] [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)
    (L : Type*) [Field L] [CharZero L] (n : ℕ) :
    Module.finrank K
        ↥(Subalgebra.toSubmodule P.weylGroupRootRep.dual.symmetricAlgebraInvariants ⊓
          homogeneousSubmodule K (Module.Dual K M) n) =
      Module.finrank L
        ↥(Subalgebra.toSubmodule (rootPairingBaseChange L b.rationalModel
            b.rationalModel_toLinearMap).weylGroupRootRep.dual.symmetricAlgebraInvariants ⊓
          homogeneousSubmodule L (Module.Dual L (b.support → L)) n) := by
  let eqv := b.equivBaseChangeRationalModel
  let PK := rootPairingBaseChange K b.rationalModel b.rationalModel_toLinearMap
  let eqvRep : Representation.Equiv P.weylGroupRootRep
      (PK.weylGroupRootRep.comp eqv.weylGroupEquiv.toMonoidHom) :=
    Representation.Equiv.mk eqv.weightEquiv fun w ↦ LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, weylGroupRootRep_apply, RootPairing.Equiv.weightEquiv_apply]
      exact (eqv.weylGroupEquiv_smul w x).symm
  have heDual (w : P.weylGroup) (φ : Module.Dual K M) :
      PK.weylGroupRootRep.dual (eqv.weylGroupEquiv w) (eqvRep.dual φ) =
        eqvRep.dual (P.weylGroupRootRep.dual w φ) := by
    simpa only [_root_.Representation.dual_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_inv, _root_.Representation.Equiv.coe_toIntertwiningMap,
      _root_.Representation.Equiv.toLinearEquiv_apply] using
      (IntertwiningMap.isIntertwining _ _ eqvRep.dual.toIntertwiningMap w φ).symm
  rw [P.weylGroupRootRep.dual.finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_of_equiv
    eqv.weylGroupEquiv eqvRep.dual.toLinearEquiv heDual n,
    finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_rootPairingBaseChange (S := K) _ _ n,
    ← finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_rootPairingBaseChange
      (S := L) _ _ n]

/-- **Base-change invariance of basic invariant degrees.** For any finite crystallographic root
system `P` over a characteristic-zero field `K` with base `b`, and any other characteristic-zero
field `L`, the basic invariant degrees of `P.weylGroupRootRep.dual` agree (as multisets) with those
of the base change of `b.rationalModel` to `L`. -/
theorem map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual_rootPairingBaseChange_rationalModel
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {P : RootPairing ι K M N}
    [Finite ι] [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)
    (L : Type*) [Field L] [CharZero L]
    {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    {f : κ₁ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ₁ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {g : κ₂ → (rootPairingBaseChange L b.rationalModel
        b.rationalModel_toLinearMap).weylGroupRootRep.dual.symmetricAlgebraInvariants}
    {e : κ₂ → ℕ}
    (hg : ∀ j, (g j : SymmetricAlgebra L (Module.Dual L (b.support → L))) ∈
      homogeneousSubmodule L (Module.Dual L (b.support → L)) (e j))
    (hgbij : Function.Bijective (MvPolynomial.aeval (R := L) g)) :
    Finset.univ.val.map d = Finset.univ.val.map e := by
  set PL := rootPairingBaseChange L b.rationalModel b.rationalModel_toLinearMap
  have hd : ∀ i, d i ≠ 0 :=
    P.weylGroupRootRep.dual.ne_zero_of_injective_aeval_symmetricAlgebraInvariants hf hbij.1
  have he : ∀ j, e j ≠ 0 :=
    PL.weylGroupRootRep.dual.ne_zero_of_injective_aeval_symmetricAlgebraInvariants hg hgbij.1
  let := Subalgebra.gradedAlgebra P.weylGroupRootRep.dual.isHomogeneous_symmetricAlgebraInvariants
  let := Subalgebra.gradedAlgebra PL.weylGroupRootRep.dual.isHomogeneous_symmetricAlgebraInvariants
  refine Multiset.map_univ_eq_of_natCard_weight_eq hd he fun n ↦ ?_
  rw [← TauCeti.GradedAlgebra.finrank_eq_natCard_weight _
      (fun i ↦ (Subalgebra.mem_grading_iff _ _).2 (hf i)) hbij n,
    ← TauCeti.GradedAlgebra.finrank_eq_natCard_weight _
      (fun j ↦ (Subalgebra.mem_grading_iff _ _).2 (hg j)) hgbij n,
    Subalgebra.finrank_grading, Subalgebra.finrank_grading]
  exact
    finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_eq_rootPairingBaseChange_rationalModel
      b L n

end Base

end RootPairing
