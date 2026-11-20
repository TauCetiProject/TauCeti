/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
public import TauCeti.RingTheory.Nilpotent.Exp.Basic
import Mathlib.Algebra.Module.Rat

/-!
# Exponential curves acting on comodules and unipotent exponential points

Let `H` be a commutative bialgebra over a commutative ring `R` which is also a `ℚ`-algebra, and
let `d` be a tangent vector at the identity whose left-invariant derivation
`D = TauCeti.Bialgebra.leftInvariantDerivation d` is locally nilpotent on `H`. Building on
`TauCeti.Comodule.pow_differential_apply` and nilpotence of `Comodule.differential` for
finitely generated comodules,
the intrinsic one-parameter exponential curve `t ↦ Bialgebra.expPointAt d hd t` acts on every
finitely generated `H`-comodule `M` over any commutative `R`-algebra `B` (automatically a
`ℚ`-algebra via the counit) as the finite operator exponential
`IsNilpotent.exp (t • (Comodule.differential d).baseChange B)`.

In particular, when `H` is a Hopf algebra, every point `Bialgebra.expPointAt d hd t` on an
exponential curve — and hence `Bialgebra.expPoint d hd` — is unipotent
(`TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt`,
`TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`).

## Main declarations

* `TauCeti.Comodule.endOfPoint_expPointAt` and
  `TauCeti.Comodule.basePointsRepresentation_expPointAt`: exponential curves act on finitely
  generated comodules by `IsNilpotent.exp` of the scaled differentiated action.
* `TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt` and
  `TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`: exponential points and exponential curves are
  unipotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

section ExponentialAction

variable {R H M : Type*} [CommRing R] [CommRing H] [Bialgebra R H] [Algebra ℚ H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

private theorem pow_baseChange_tmul {B : Type*} [CommRing B] [Algebra R B]
    (f : Module.End R M) (k : ℕ) (b : B) (m : M) :
    (f.baseChange B ^ k) (b ⊗ₜ[R] m) = b ⊗ₜ[R] ((f ^ k) m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih,
      LinearMap.baseChange_tmul]

private theorem pow_smul_baseChange_eq_zero {B : Type*} [CommRing B] [Algebra R B]
    {f : Module.End R M} {K : ℕ} (hK : f ^ K = 0) (t : B) :
    (t • f.baseChange B) ^ K = 0 := by
  rw [smul_pow]
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    rw [LinearMap.smul_apply, pow_baseChange_tmul, hK, LinearMap.zero_apply,
      TensorProduct.tmul_zero, smul_zero, LinearMap.zero_apply]
  | add x y hx hy => simp [map_add, hx, hy]

/-- **Exponential points act on finitely generated comodules by the exponential of the
differentiated action.** For any value algebra `B` and parameter `t : B`, the exponential point
`expPointAt d hd t` acts on `B ⊗[R] M` as `exp (t • (differential d).baseChange B)`. -/
theorem endOfPoint_expPointAt [Module.Finite R M] {B : Type*} [CommRing B] [Algebra R B]
    [Algebra ℚ B] (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : B) :
    endOfPoint M (Bialgebra.expPointAt d hd t).ofConv =
      IsNilpotent.exp (t • (differential (R := R) (H := H) (M := M) d).baseChange B) := by
  -- The counit pulls the `ℚ`-algebra structure of `H` back to `R`.
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  set D := Bialgebra.leftInvariantDerivation d
  set f := differential (R := R) (H := H) (M := M) d
  have hnil : IsNilpotent (t • f.baseChange B) := by
    obtain ⟨K, hK⟩ :=
      isNilpotent_differential_of_finite_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
        (R := R) (H := H) (M := M) hd
    exact ⟨K, pow_smul_baseChange_eq_zero hK t⟩
  -- Expand the `endOfPoint` action on any tensor `z : M ⊗[R] H` into a finite Taylor sum.
  have hexpand : ∀ (b : B) (z : M ⊗[R] H), ∃ N, ∀ n ≥ N,
      b • TensorProduct.comm R M B
          (((Bialgebra.expPointAt d hd t).ofConv.toLinearMap.lTensor M) z) =
        ∑ k ∈ Finset.range n, (k.factorial : ℚ)⁻¹ •
          ((t ^ k * b) ⊗ₜ[R]
            LinearMap.tensorComponent (Coalgebra.counit (R := R) ∘ₗ D.toLinearMap ^ k) z) := by
    intro b z
    induction z using TensorProduct.inductionOn with
    | tmul m h =>
      obtain ⟨N, hN⟩ := hd h
      refine ⟨N + 1, fun n hn ↦ ?_⟩
      have hdeg : (Bialgebra.expPointPolynomial d hd h).natDegree < n := by
        refine lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_)
          (Nat.lt_of_succ_le hn)
        have hzero : D^[k] h = 0 := by
          simpa [FunLike.coe_pow_eq_iterate] using
            Module.End.pow_map_zero_of_le (f := D.toLinearMap) hk.le
              (by simpa [FunLike.coe_pow_eq_iterate] using hN)
        simp [Bialgebra.coeff_expPointPolynomial, D, hzero]
      have haeval : (Bialgebra.expPointAt d hd t).ofConv h =
          ∑ k ∈ Finset.range n,
            algebraMap R B ((Bialgebra.expPointPolynomial d hd h).coeff k) * t ^ k := by
        simpa [Bialgebra.expPointAt_apply, Algebra.smul_def] using
          Polynomial.aeval_eq_sum_range' hdeg t
      simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, haeval,
        TensorProduct.comm_tmul, TensorProduct.sum_tmul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Bialgebra.coeff_expPointPolynomial, map_rat_smul, map_rat_smul,
        LinearMap.tensorComponent_tmul, LinearMap.comp_apply, FunLike.coe_pow_eq_iterate,
        Derivation.coeFn_coe, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        ← TensorProduct.smul_tmul]
      congr 1
      simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, D]
      ring
    | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨N₁, hN₁⟩ := ih₁
      obtain ⟨N₂, hN₂⟩ := ih₂
      refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
      simp only [map_add, smul_add, TensorProduct.tmul_add, Finset.sum_add_distrib,
        hN₁ n (le_of_max_le_left hn), hN₂ n (le_of_max_le_right hn)]
  -- Match the finite sum with `IsNilpotent.exp` on pure tensors.
  apply LinearMap.ext_iff.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul b m =>
    obtain ⟨K, hK⟩ := hnil
    obtain ⟨N, hN⟩ := hexpand b (coact (R := R) (C := H) m)
    let M' := max K N
    have hM' : (t • f.baseChange B) ^ M' = 0 :=
      pow_eq_zero_of_le (le_max_left K N) hK
    rw [endOfPoint_tmul, hN M' (le_max_right K N), IsNilpotent.exp_eq_sum hM',
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [LinearMap.smul_apply, smul_pow, LinearMap.smul_apply, pow_baseChange_tmul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, ← pow_differential_apply d k m]

end ExponentialAction

section BasePoints

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H] [Algebra ℚ H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] [Module.Finite R M]
variable [Algebra ℚ R] [Module ℚ M]

/-- Over a `ℚ`-algebra base ring, the base-valued action of `expPointAt d hd t` on a finitely
generated comodule is `exp (t • differential d)`. -/
theorem basePointsRepresentation_expPointAt
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : R) :
    basePointsRepresentation (R := R) (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  set f := differential (R := R) (H := H) (M := M) d
  obtain ⟨K, hK⟩ :=
    isNilpotent_differential_of_finite_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
      (R := R) (H := H) (M := M) hd
  have hKt : (t • f) ^ K = 0 := by rw [smul_pow, hK, smul_zero]
  have hK' : (t • f.baseChange R) ^ K = 0 := pow_smul_baseChange_eq_zero hK t
  apply LinearMap.ext
  intro m
  rw [basePointsRepresentation_apply, endOfPoint_expPointAt d hd t,
    IsNilpotent.exp_eq_sum hK', IsNilpotent.exp_eq_sum hKt, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_rat_smul, smul_pow, smul_pow,
    LinearMap.smul_apply, LinearMap.smul_apply, pow_baseChange_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one, TensorProduct.lid_tmul, ← LinearMap.smul_apply]

end BasePoints

end TauCeti.Comodule

namespace TauCeti.HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {B : Type w}
variable [CommRing R] [CommRing H] [_root_.HopfAlgebra R H] [Algebra ℚ H]

/-- Every point on the exponential curve of a tangent vector with locally nilpotent invariant
derivation is unipotent, over any commutative value algebra `B`. -/
theorem isUnipotentPoint_expPointAt [CommRing B] [Algebra R B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : B) :
    IsUnipotentPoint (Bialgebra.expPointAt d hd t) := by
  -- The counit pulls the `ℚ`-algebra structure of `H` to `R` and then to `B`.
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  let : Algebra ℚ B :=
    ((algebraMap R B).comp (algebraMap ℚ R)).toAlgebra
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  rw [Comodule.endOfPoint_expPointAt d hd t]
  obtain ⟨K, hK⟩ := by
    open Comodule in
    exact
      isNilpotent_differential_of_finite_of_forall_exists_iterate_leftInvariantDerivation_eq_zero
        (R := R) (H := H) (M := M) hd
  exact ⟨K, IsNilpotent.pow_exp_sub_one_eq_zero (Comodule.pow_smul_baseChange_eq_zero hK t)⟩

/-- The exponential point of a tangent vector with locally nilpotent invariant derivation is
unipotent. -/
theorem isUnipotentPoint_expPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsUnipotentPoint (WithConv.toConv (Bialgebra.expPoint d hd)) := by
  rw [← Bialgebra.expPointAt_one]
  exact isUnipotentPoint_expPointAt d hd (1 : R)

end TauCeti.HopfAlgebra
