/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.JordanChain.Partition
public import TauCeti.RingTheory.Polynomial.Truncated.Centralizer
import TauCeti.RingTheory.Polynomial.Truncated.Module
import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite

/-!
# Centralizer dimensions of nilpotent endomorphisms

The dimension of the endomorphism centralizer of a nilpotent linear map is the sum
of the squares of the successive increases of its kernel dimensions. These increases
are the column lengths of its Jordan partition, so the formula is intrinsic and needs
neither an algebraically closed field nor a selected Jordan-chain basis. In terms of the
Jordan partition `λ` and its conjugate `λ'`, the dimension is `∑ⱼ (λ'ⱼ)²`.

The proof uses the finite-module decomposition over the truncated polynomial ring
from `TauCeti.RingTheory.Polynomial.Truncated.Module`, together with the cyclic-block
kernel and centralizer calculations. The original scalar action on the vector space
is retained throughout.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §6.1: centralizer dimensions from homomorphisms between Jordan blocks.
-/

public section

open Polynomial MulOpposite

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- The centralizer dimension of a nilpotent endomorphism is the sum of squared
successive kernel-dimension increases. Any bound with `f ^ n = 0` is allowed,
including `n = 0` when the vector space is zero. -/
theorem finrank_centralizer_eq_sum_sq_ker (f : Module.End K V) {n : ℕ}
    (hn : f ^ n = 0) :
    Module.finrank K (Subalgebra.centralizer K {f}) =
      ∑ k ∈ Finset.range n,
        (Module.finrank K (LinearMap.ker (f ^ (k + 1))) -
          Module.finrank K (LinearMap.ker (f ^ k))) ^ 2 := by
  classical
  -- Evaluation makes the original vector space a module over the truncated algebra.
  have hvan : ∀ p ∈ Ideal.span {(X ^ n : K[X])}, aeval f p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp [hn]
  let ρ₀ : AdjoinRoot (X ^ n : K[X]) →ₐ[K] Module.End K V :=
    Ideal.Quotient.liftₐ _ (aeval f) hvan
  let A := (AdjoinRoot (X ^ n : K[X]))ᵐᵒᵖ
  let ρ : A →ₐ[K] Module.End K V := ρ₀.comp (AlgEquiv.toOpposite K _).symm.toAlgHom
  let : Module A V := Module.compHom V ρ.toRingHom
  have hact (a : A) (v : V) : a • v = ρ a v := rfl
  let : IsScalarTower K A V := ⟨fun c a v => by
    simp only [hact, map_smul, LinearMap.smul_apply]⟩
  have hroot : ρ (op (AdjoinRoot.root (X ^ n : K[X]))) = f := by
    -- The opposite equivalence cancels the opposite scalar in the action.
    change ρ₀ (AdjoinRoot.root (X ^ n : K[X])) = f
    exact (congrArg (fun g : K[X] →ₐ[K] Module.End K V => g X)
      (Ideal.Quotient.liftₐ_comp (Ideal.span {(X ^ n : K[X])}) (aeval f) hvan)).trans
        (aeval_X f)
  have : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V
  obtain ⟨r, len, hlen, ⟨e₀⟩⟩ :=
    TauCeti.exists_linearEquiv_directSum_quotient_span_op_root_X_pow_pow (K := K) (n := n) V
  let M (i : Fin r) := A ⧸ Ideal.span {op (AdjoinRoot.root (X ^ n : K[X]) ^ len i)}
  let e := e₀.trans (DirectSum.linearEquivFunOnFintype A (Fin r) M)
  let eK := e.restrictScalars K
  -- Transport the scalar-linear endomorphism algebra to the finite block product.
  have hgen : Algebra.adjoin K {op (AdjoinRoot.root (X ^ n : K[X]))} = ⊤ := by
    have hset : unop ⁻¹' {AdjoinRoot.root (X ^ n : K[X])} =
        {op (AdjoinRoot.root (X ^ n : K[X]))} := by
      ext a
      exact unop_injective.eq_iff' rfl
    simpa only [Subalgebra.op_adjoin, Subalgebra.op_top, hset] using
      congrArg Subalgebra.op (AdjoinRoot.adjoinRoot_eq_top (f := (X ^ n : K[X])))
  have hscalar : Algebra.lsmul K K V (op (AdjoinRoot.root (X ^ n : K[X]))) = f := by
    ext v
    exact congrArg (fun g : Module.End K V => g v) hroot
  have hdim : Module.finrank K (Subalgebra.centralizer K {f}) =
      ∑ k ∈ Finset.range n, (Finset.univ.filter fun i => k < len i).card ^ 2 := by
    have ec := TauCeti.centralizerLsmulAlgEquivEnd (M := V) _ hgen
    rw [Set.image_singleton, hscalar] at ec
    rw [ec.toLinearEquiv.finrank_eq, (e.conjAlgEquiv K).toLinearEquiv.finrank_eq,
      TauCeti.finrank_end_pi_cyclic_root_pow len (fun i => (hlen i).2)]
    exact Finset.sum_sum_min_eq_sum_sq_card_filter Finset.univ len n fun i _ => (hlen i).2
  -- The same decomposition computes every kernel, hence identifies the columns intrinsically.
  have hker (k : ℕ) : Module.finrank K (LinearMap.ker (f ^ k)) =
      ∑ i, min k (len i) := by
    let g := DistribSMul.toLinearMap K ((i : Fin r) → M i)
      (op (AdjoinRoot.root (X ^ n : K[X]) ^ k))
    have hpow (v : V) : op (AdjoinRoot.root (X ^ n : K[X]) ^ k) • v = (f ^ k) v := by
      rw [hact, op_pow, map_pow, hroot]
    have hinter (v : V) : eK ((f ^ k) v) = g (eK v) := by
      rw [← hpow]
      exact e.map_smul _ v
    have heq : LinearMap.ker (f ^ k) = (LinearMap.ker g).comap eK.toLinearMap := by
      ext v
      simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearEquiv.coe_coe,
        ← hinter, eK.map_eq_zero_iff]
    rw [(LinearEquiv.ofEq _ _ heq).finrank_eq,
      (eK.ofSubmodule' (LinearMap.ker g)).finrank_eq]
    exact TauCeti.finrank_ker_smul_pi_cyclic_root_pow len (fun i => (hlen i).2) k
  rw [hdim]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [hker, hker, ← Finset.sum_tsub_distrib Finset.univ
    (fun i _ => min_le_min_right (len i) (Nat.le_succ k))]
  have hcount := Finset.sum_boole (R := ℕ) (fun i => k < len i) Finset.univ
  simp only [Nat.cast_id] at hcount
  rw [← hcount]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> omega

/-- **The centralizer dimension of a nilpotent endomorphism** is `∑ⱼ (λ'ⱼ)²`, the sum of the
squares of the parts of the conjugate `λ'` of its Jordan partition `λ`. -/
theorem finrank_centralizer_eq_sum_sq_conjugate_jordanPartition (f : Module.End K V)
    (hf : IsNilpotent f) :
    Module.finrank K (Subalgebra.centralizer K {f}) =
      ((f.jordanPartition hf).conjugate.parts.map (· ^ 2)).sum := by
  obtain ⟨n, hn⟩ := id hf
  -- No Jordan block is longer than the nilpotency bound.
  have hle (i : ℕ) (hi : i ∈ (f.jordanPartition hf).parts) : i ≤ n := by
    by_contra! hlt
    have hcol := f.card_filter_jordanPartition_parts hf n
    rw [pow_succ, hn, zero_mul, Nat.sub_self, Multiset.card_eq_zero,
      Multiset.filter_eq_nil] at hcol
    exact hcol i hi hlt
  rw [finrank_centralizer_eq_sum_sq_ker f hn,
    Nat.Partition.sum_map_conjugate_parts _ (· ^ 2) (zero_pow two_ne_zero) hle]
  simp only [card_filter_jordanPartition_parts]

end Module.End
