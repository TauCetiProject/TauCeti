/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.FiniteField
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
import TauCeti.RingTheory.Derivation.Basic

/-!
# Vanishing of the differential of the Frobenius

For a commutative bialgebra `H` over a finite field `F` of cardinality `q`, every derivation
annihilates `q`-th powers because `q = 0` in `F` (and in any `F`-algebra `K`). Consequently, both
the Frobenius bialgebra endomorphism `TauCeti.frobeniusBialgHom F H` and the geometric Frobenius
`TauCeti.FiniteField.geometricFrobeniusBialgHom F K H` (together with its positive iterates) have
identically zero differential on counit-valued derivations.

## Main results

* `TauCeti.derivationComp_frobeniusBialgHom_eq_zero`: the Frobenius endomorphism
  `TauCeti.frobeniusBialgHom F H` has zero differential.
* `TauCeti.FiniteField.derivationComp_geometricFrobeniusBialgHom_eq_zero` and
  `TauCeti.FiniteField.derivationComp_geometricFrobeniusBialgHom_pow_eq_zero`: the geometric
  Frobenius `id ⊗ Frob` on a base change `K ⊗[F] H` and all its positive powers have zero
  differential.
-/

public section

open scoped TensorProduct

universe u v w

namespace TauCeti

/-- The differential of the Frobenius endomorphism `TauCeti.frobeniusBialgHom F H` vanishes
identically: every `F`-derivation annihilates `q`-th powers because `q = |F|` is zero in `F`. -/
@[simp]
theorem derivationComp_frobeniusBialgHom_eq_zero
    (F : Type u) [Field F] [Fintype F]
    (H : Type v) [CommSemiring H] [_root_.Bialgebra F H]
    {B : Type*} [Semiring B] [Algebra F B] :
    derivationComp (B := B) (frobeniusBialgHom F H) = 0 := by
  ext d h : 2
  rw [derivationComp_apply, LinearMap.zero_apply, zero_apply, BialgHom.coe_toAlgHom,
    frobeniusBialgHom_apply, d.map_pow_eq_zero_of_natCast_eq_zero (Nat.cast_card_eq_zero F)]

namespace FiniteField

/-- The differential of the geometric Frobenius `id ⊗ Frob` on a base change `K ⊗[F] H` vanishes
identically: every `K`-derivation annihilates `q`-th powers because `q = |F|` is zero in `K`. -/
@[simp]
theorem derivationComp_geometricFrobeniusBialgHom_eq_zero
    (F : Type u) [Field F] [Fintype F]
    (K : Type w) [CommSemiring K] [Algebra F K]
    (H : Type v) [CommSemiring H] [_root_.Bialgebra F H]
    {B : Type*} [Semiring B] [Algebra K B] :
    TauCeti.derivationComp (B := B) (geometricFrobeniusBialgHom F K H) = 0 := by
  have hcardK : (Fintype.card F : K) = 0 := by
    rw [← map_natCast (algebraMap F K), Nat.cast_card_eq_zero, map_zero]
  ext d x : 2
  rw [TauCeti.derivationComp_apply, LinearMap.zero_apply, zero_apply]
  induction x using TensorProduct.inductionOn with
  | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
  | tmul s h =>
    have htmul :
        (geometricFrobeniusBialgHom F K H : K ⊗[F] H →ₐ[K] K ⊗[F] H) (s ⊗ₜ[F] h) =
          s • (((1 : K) ⊗ₜ[F] h) ^ Fintype.card F) := by
      rw [BialgHom.coe_toAlgHom, geometricFrobeniusBialgHom_tmul, Algebra.TensorProduct.tmul_pow,
        one_pow, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [htmul, Derivation.map_smul, d.map_pow_eq_zero_of_natCast_eq_zero hcardK, smul_zero]

/-- Every positive power of the geometric Frobenius `id ⊗ Frob` on a base change `K ⊗[F] H`
has zero differential. -/
theorem derivationComp_geometricFrobeniusBialgHom_pow_eq_zero
    (F : Type u) [Field F] [Fintype F]
    (K : Type w) [CommSemiring K] [Algebra F K]
    (H : Type v) [CommSemiring H] [_root_.Bialgebra F H]
    {B : Type*} [Semiring B] [Algebra K B] {n : ℕ} (hn : n ≠ 0) :
    TauCeti.derivationComp (B := B) ((geometricFrobeniusBialgHom F K H) ^ n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ', BialgHom.End_toMul_mul, TauCeti.derivationComp_comp,
    derivationComp_geometricFrobeniusBialgHom_eq_zero, LinearMap.comp_zero]

end FiniteField

end TauCeti
