/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Rational
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import TauCeti.RepresentationTheory.SymmetricAlgebra.BaseChange
import TauCeti.RepresentationTheory.SymmetricAlgebra.Degrees
import TauCeti.RingTheory.PowerSeries.ProdOneSubXPow

/-!
# Field-invariance of Weyl polynomial invariant degrees

Extending `b.rationalModel` to any characteristic-zero field `S` preserves the graded dimensions
of `Sym(M*)^W`. Combined with `RootPairing.Base.equivBaseChangeRationalModel`, the multiset of
basic invariant degrees of `P.weylGroupRootRep.dual` is independent of the characteristic-zero
ground field.
-/

public section

open Finset Function Module Representation SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra
  TensorProduct

namespace RootPairing

private theorem finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_rootPairingBaseChange
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
  let eDual : S ⊗[ℚ] Module.Dual ℚ (σ → ℚ) ≃ₗ[S] Module.Dual S (σ → S) :=
    (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := ℚ) (A := S) (M := σ → ℚ)).trans
      ePi.symm.dualMap
  have hePi_tmul (s : S) (x : σ → ℚ) :
      ePi (s ⊗ₜ[ℚ] x) = s • Pi.algebraMap σ ℚ S x := by
    ext j; simp [ePi, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_comm, piAlgebraMap_apply]
  have hePi (w : Q.weylGroup) (z : S ⊗[ℚ] (σ → ℚ)) :
      eG w • ePi z = ePi ((Q.weylGroupRootRep.baseChange S) w z) := by
    induction z with
    | add x y hx hy => simp [smul_add, map_add, hx, hy]
    | tmul s x =>
      simp only [hePi_tmul, smul_comm, Representation.baseChange_apply, LinearMap.baseChange_tmul,
        weylGroupRootRep_apply]
      dsimp only [eG]
      rw [weylGroupBaseChangeEquiv_smul]
  have heDual (w : Q.weylGroup) (ψ : S ⊗[ℚ] Module.Dual ℚ (σ → ℚ)) :
      (rootPairingBaseChange S Q hQ).weylGroupRootRep.dual (eG w) (eDual ψ) =
        eDual ((Q.weylGroupRootRep.dual.baseChange S) w ψ) := by
    induction ψ with
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul s φ =>
      apply LinearMap.ext; intro y
      obtain ⟨z, rfl⟩ := ePi.surjective y
      induction z with
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | tmul t x =>
        have hinv := hePi w⁻¹ (t ⊗ₜ[ℚ] x)
        simp only [Representation.baseChange_apply, LinearMap.baseChange_tmul] at hinv
        simp only [eDual, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
          Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
          Representation.baseChange_apply, LinearMap.baseChange_tmul, ← map_inv eG]
        rw [weylGroupRootRep_apply, hinv, ePi.symm_apply_apply, ePi.symm_apply_apply,
          TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
          TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
          TauCeti.Module.Dual.baseChangeEvaluation_tmul,
          TauCeti.Module.Dual.baseChangeEvaluation_tmul]; rfl
  rw [← finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_of_equiv eG eDual heDual n]
  exact finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule
    Q.weylGroupRootRep.dual (L := S) n

namespace Base

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
  have hfin (n : ℕ) :
      Module.finrank K
          ↥(Subalgebra.toSubmodule P.weylGroupRootRep.dual.symmetricAlgebraInvariants ⊓
            homogeneousSubmodule K (Module.Dual K M) n) =
        Module.finrank L
          ↥(Subalgebra.toSubmodule PL.weylGroupRootRep.dual.symmetricAlgebraInvariants ⊓
            homogeneousSubmodule L (Module.Dual L (b.support → L)) n) := by
    let eqv := b.equivBaseChangeRationalModel
    have heDual : ∀ w φ, P.weylGroupRootRep.dual (eqv.weylGroupEquiv.symm w)
        (eqv.weightEquiv.dualMap φ) = eqv.weightEquiv.dualMap ((rootPairingBaseChange K
          b.rationalModel b.rationalModel_toLinearMap).weylGroupRootRep.dual w φ) := by
      intro w φ; obtain ⟨u, rfl⟩ := eqv.weylGroupEquiv.surjective w; ext x
      simp only [MulEquiv.symm_apply_apply, Representation.dual_apply, Module.Dual.transpose_apply,
        LinearMap.comp_apply, LinearEquiv.dualMap_apply, weylGroupRootRep_apply, ← map_inv,
        eqv.weylGroupEquiv_smul]
    rw [← finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_of_equiv
      eqv.weylGroupEquiv.symm eqv.weightEquiv.dualMap heDual n,
      finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_rootPairingBaseChange _ _ n,
      finrank_symmetricAlgebraInvariants_weylGroupRootRep_dual_rootPairingBaseChange _ _ n]
  have hH1 := mk_finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_mul_prod_one_sub_X_pow
    P.weylGroupRootRep.dual ℤ hf hbij
  have hH2 := mk_finrank_symmetricAlgebraInvariants_inf_homogeneousSubmodule_mul_prod_one_sub_X_pow
    PL.weylGroupRootRep.dual ℤ hg hgbij
  simp_rw [hfin] at hH1
  refine Multiset.eq_of_prod_map_one_sub_X_pow_eq (R := ℤ) (by simpa using hd)
    (by simpa using he) ?_
  simpa [Multiset.map_map, Function.comp_def] using
    left_inv_eq_right_inv ((mul_comm _ _).trans hH1) hH2

end Base

end RootPairing
