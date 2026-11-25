/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
import Mathlib.Algebra.Module.Rat
import TauCeti.Algebra.Bialgebra.CounitBaseAlgebra
import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# Exponential curves on comodules and unipotent exponential points

Let `H` be a commutative Hopf algebra over `R` which is also a `ℚ`-algebra, and let `d` be a
tangent vector at the identity whose left-invariant derivation `D` is locally nilpotent. Building on
`TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Comodule` (which treats the exponential point
`expPoint d hd` at parameter `1`), this module describes the action of the entire polynomial
exponential curve `t ↦ expPointAt d hd t` on scalar extensions `A ⊗[R] M` and deduces representation
criteria for unipotence:

* in the convolution dual of `H`, the functional `ε ∘ Dⁿ` is the `n`-th convolution power of `d`,
  so `(Comodule.differential d) ^ n` is the convolution action of `ε ∘ Dⁿ`;
* whenever `Comodule.differential d` is nilpotent on `M` and `A` is a commutative `R`-algebra that
  is a `ℚ`-module, evaluating the exponential curve at `t : A` acts on `A ⊗[R] M` by the finite
  operator exponential `IsNilpotent.exp (t • (Comodule.differential d).baseChange A)`, and on `M`
  itself at `t : R` by `IsNilpotent.exp (t • Comodule.differential d)`;
* every point `expPointAt d hd t` (and `expPoint d hd`) is unipotent in the representation-theoretic
  sense (`HopfAlgebra.IsUnipotentPoint`) whenever `d` acts nilpotently on every finitely generated
  `H`-comodule.

## Main declarations

* `TauCeti.Bialgebra.toConv_counit_comp_pow_leftInvariantDerivation`: in the convolution dual,
  `ε ∘ Dⁿ` is the `n`-th convolution power of `d`.
* `TauCeti.Comodule.differential_pow`: `(Comodule.differential d) ^ n` is the convolution action of
  `ε ∘ Dⁿ`.
* `TauCeti.Comodule.endOfPoint_expPointAt` and
  `TauCeti.Comodule.basePointsRepresentation_expPointAt`: on `A ⊗[R] M` and on `M`, the exponential
  curve at parameter `t` acts by `IsNilpotent.exp (t • (Comodule.differential d).baseChange A)` and
  `IsNilpotent.exp (t • Comodule.differential d)`.
* `TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt` and
  `TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`: exponential points of tangent vectors acting
  nilpotently on every finitely generated comodule are unipotent points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
-/

public section

open scoped TensorProduct
open LinearMap TensorProduct WithConv

namespace TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H]

/-- In the convolution dual of `H`, the functional `ε ∘ Dⁿ` attached to the `n`-th iterate of the
left-invariant derivation of `d` is the `n`-th convolution power of `d`. -/
theorem toConv_counit_comp_pow_leftInvariantDerivation
    (d : Derivation R H (CounitAlgebra R H R)) (n : ℕ) :
    toConv (Coalgebra.counit (R := R) ∘ₗ (leftInvariantDerivation d).toLinearMap ^ n) =
      toConv ((CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) ^ n := by
  induction n with
  | zero =>
    apply ofConv_injective
    simp [Module.End.one_eq_id]
  | succ n ih =>
    conv_rhs => rw [pow_succ, ← ih]
    apply ofConv_injective
    ext h
    rw [LinearMap.convMul_eq_comp_tensorComponent]
    simp [← leftInvariantDerivation_apply, pow_succ]

end TauCeti.Bialgebra

namespace TauCeti.Comodule

section DifferentialPow

variable {R H M : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The `n`-th power of the differentiated action of `d` on a comodule is the convolution action
of `ε ∘ Dⁿ`, where `D` is the left-invariant derivation of `d`. -/
theorem differential_pow (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (n : ℕ) :
    differential (R := R) (H := H) (M := M) d ^ n =
      convolutionAction (R := R) (C := H) (M := M)
        (toConv (Coalgebra.counit (R := R) ∘ₗ
          (Bialgebra.leftInvariantDerivation d).toLinearMap ^ n)) := by
  have hd : differential (R := R) (H := H) (M := M) d =
      convolutionAction (R := R) (C := H) (M := M)
        (toConv ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap)) := by
    ext m
    simp [differential_apply]
  rw [Bialgebra.toConv_counit_comp_pow_leftInvariantDerivation, map_pow, ← hd]

end DifferentialPow

section ExponentialAction

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The base-valued points representation acts by the convolution action of the underlying linear
functional. -/
theorem basePointsRepresentation_apply_eq_convolutionAction
    (g : WithConv (H →ₐ[R] R)) (m : M) :
    basePointsRepresentation (H := H) M g m =
      convolutionAction (R := R) (C := H) (M := M) (toConv g.ofConv.toLinearMap) m := by
  rw [basePointsRepresentation_apply, endOfPoint_tmul, one_smul, TensorProduct.lid_comm]
  simp [convolutionAction_apply, tensorComponent_def]

variable [Algebra ℚ H]

omit [Comodule R H M] in
/-- On any tensor `x : M ⊗[R] H`, contracting the right factor against `expPointAt d hd t` agrees
with the truncated Taylor sum past a uniform nilpotence bound for `D` on `x`. -/
private theorem comm_lTensor_expPointAt_eq_sum {A : Type*} [CommRing A] [Algebra R A] [Module ℚ A]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (t : A) (x : M ⊗[R] H) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      TensorProduct.comm R M A ((Bialgebra.expPointAt d hd t).ofConv.toLinearMap.lTensor M x) =
        ∑ k ∈ Finset.range N, (k.factorial : ℚ)⁻¹ • (t ^ k •
          ((1 : A) ⊗ₜ[R] tensorComponent (Coalgebra.counit (R := R) ∘ₗ
            (Bialgebra.leftInvariantDerivation d).toLinearMap ^ k) x)) := by
  let : Algebra ℚ R := Bialgebra.counitBaseAlgebra ℚ R H
  let D := Bialgebra.leftInvariantDerivation d
  induction x using TensorProduct.inductionOn with
  | tmul m' h =>
    obtain ⟨n₀, hn₀⟩ := hd h
    refine ⟨n₀, fun N hN => ?_⟩
    have hk0 : D^[N] h = 0 := by
      simpa [pow_apply_eq_iterate] using
        Module.End.pow_map_zero_of_le (f := D.toLinearMap) hN
          (by simpa [pow_apply_eq_iterate] using hn₀)
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, Bialgebra.expPointAt_apply,
      Bialgebra.aeval_expPointPolynomial_eq_sum d hd t hk0, TensorProduct.comm_tmul,
      TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_rat_smul]
    simp [smul_tmul', ← smul_assoc, FunLike.coe_pow_eq_iterate]
  | add x y hx hy =>
    obtain ⟨N₁, hN₁⟩ := hx
    obtain ⟨N₂, hN₂⟩ := hy
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    rw [map_add, map_add, hN₁ N (le_of_max_le_left hN), hN₂ N (le_of_max_le_right hN),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, tmul_add, smul_add, smul_add]

/-- Evaluating the exponential curve at `t : A` acts on the scalar extension `A ⊗[R] M` by the
operator exponential `IsNilpotent.exp (t • (differential d).baseChange A)` whenever
`differential d` is nilpotent on `M`. -/
theorem endOfPoint_expPointAt {A : Type*} [CommRing A] [Algebra R A] [Module ℚ A]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hdiff : IsNilpotent (differential (R := R) (H := H) (M := M) d)) (t : A) :
    endOfPoint M (Bialgebra.expPointAt d hd t).ofConv =
      IsNilpotent.exp (t • (differential (R := R) (H := H) (M := M) d).baseChange A) := by
  let f := differential (R := R) (H := H) (M := M) d
  obtain ⟨K, hK⟩ := hdiff
  have hbaseK : (t • f.baseChange A) ^ K = 0 := by
    simp [f, smul_pow, ← LinearMap.baseChange_pow, hK]
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.restrictScalars_apply]
  -- Since both operators are `A`-linear, reduce from `a ⊗ₜ m` to `1 ⊗ₜ m`.
  have hatm : (a ⊗ₜ[R] m : A ⊗[R] M) = a • (1 ⊗ₜ[R] m) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [hatm, LinearMap.map_smul, LinearMap.map_smul]
  congr 1
  obtain ⟨N₀, hN₀⟩ := comm_lTensor_expPointAt_eq_sum d hd t (coact (R := R) (C := H) m)
  let N := max N₀ K
  have hbaseN : (t • f.baseChange A) ^ N = 0 :=
    pow_eq_zero_of_le (le_max_right N₀ K) hbaseK
  rw [endOfPoint_tmul, one_smul, hN₀ N (le_max_left N₀ K), IsNilpotent.exp_eq_sum hbaseN,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← pow_differential_apply]
  simp [smul_pow, ← LinearMap.baseChange_pow]

/-- The exponential curve evaluated at a base scalar `t : R` acts on a comodule `M` by
`IsNilpotent.exp (t • differential d)` whenever `differential d` is nilpotent on `M`. -/
theorem basePointsRepresentation_expPointAt [Module ℚ M]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hdiff : IsNilpotent (differential (R := R) (H := H) (M := M) d)) (t : R) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  let : Algebra ℚ R := Bialgebra.counitBaseAlgebra ℚ R H
  have hrat : ∀ (q : ℚ) (x : R ⊗[R] M),
      TensorProduct.lid R M (q • x) = q • TensorProduct.lid R M x :=
    map_rat_smul (TensorProduct.lid R M).toAddMonoidHom
  ext m
  obtain ⟨K, hK⟩ := hdiff
  have htK : (t • differential (R := R) (H := H) (M := M) d) ^ K = 0 := by
    simp [smul_pow, hK]
  have hbaseK : (t • (differential (R := R) (H := H) (M := M) d).baseChange R) ^ K = 0 := by
    simp [smul_pow, ← LinearMap.baseChange_pow, hK]
  rw [basePointsRepresentation_apply, endOfPoint_expPointAt d hd ⟨K, hK⟩ t,
    IsNilpotent.exp_eq_sum hbaseK, IsNilpotent.exp_eq_sum htK]
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [hrat, smul_pow, ← LinearMap.baseChange_pow]

end ExponentialAction

end TauCeti.Comodule

namespace TauCeti.HopfAlgebra

universe u v x

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [_root_.HopfAlgebra R H]
variable [Algebra ℚ H]

/-- Every point on the exponential curve of a tangent vector `d` is unipotent whenever the
differentiated action of `d` is nilpotent on every finitely generated `H`-comodule. -/
theorem isUnipotentPoint_expPointAt {A : Type x} [CommRing A] [Algebra R A]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hdiff : ∀ M : FGComoduleCat.{u, v, u} R H,
      _root_.IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d))
    (t : A) :
    IsUnipotentPoint (Bialgebra.expPointAt d hd t) := by
  let : Algebra ℚ R := Bialgebra.counitBaseAlgebra ℚ R H
  let : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ R)
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  rw [Comodule.endOfPoint_expPointAt d hd (hdiff M) t]
  obtain ⟨k, hk⟩ := hdiff M
  refine ⟨k, IsNilpotent.pow_exp_sub_one_eq_zero ?_⟩
  simp [smul_pow, ← LinearMap.baseChange_pow, hk]

/-- The exponential point `expPoint d hd` is unipotent whenever the differentiated action of `d`
is nilpotent on every finitely generated `H`-comodule. -/
theorem isUnipotentPoint_expPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hdiff : ∀ M : FGComoduleCat.{u, v, u} R H,
      _root_.IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    IsUnipotentPoint (toConv (Bialgebra.expPoint d hd)) := by
  rw [← Bialgebra.expPointAt_one]
  exact isUnipotentPoint_expPointAt d hd hdiff 1

end TauCeti.HopfAlgebra
