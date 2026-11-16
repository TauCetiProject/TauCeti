/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
public import TauCeti.RingTheory.Nilpotent.Exp.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Exponential

/-!
# Exponential points acting on comodules

Let `H` be a commutative bialgebra over a commutative ring `R`, and let `d` be a tangent vector
at the identity with left-invariant derivation `D = TauCeti.Bialgebra.leftInvariantDerivation d`.
In any right `H`-comodule `M`, comodule coassociativity implies that the differentiated action
`Comodule.differential d` satisfies

```text
coact (differential d m) = (id ⊗ D) (coact m),
```

and therefore `(differential d)^[n] m` is obtained by contracting `coact m` against `ε ∘ Dⁿ`.
Consequently, when `D` is locally nilpotent on `H`, `differential d` is locally nilpotent on every
comodule `M` and nilpotent on every finitely generated comodule `M`.

Conversely, for a finite free comodule `M` with basis `b : Basis (Fin n) R M`, the tangent matrix
of the coordinate morphism `Comodule.coordinateBialgHom b` at `d` is literally the matrix of
`Comodule.differential d` in the basis `b`. Thus, if `coordinateBialgHom b` is surjective and
`Comodule.differential d` is nilpotent, then `D` is locally nilpotent on `H`.

When `H` is a `ℚ`-algebra and `D` is locally nilpotent, the intrinsic exponential curve
`t ↦ expPointAt d hd t` acts on every finitely generated comodule `M` over any commutative
`R`-algebra `B` (which is automatically a `ℚ`-algebra via the counit) as the finite matrix
exponential `exp (t • differential d)`. In particular, every exponential point `expPointAt d hd t`
is unipotent (`TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt`).

## Main declarations

* `TauCeti.Comodule.coact_differential` and `TauCeti.Comodule.iterate_differential_apply`:
  intertwining of `Comodule.differential d` with `Bialgebra.leftInvariantDerivation d`.
* `TauCeti.Comodule.exists_iterate_differential_eq_zero` and
  `TauCeti.Comodule.isNilpotent_differential`: local nilpotence of `leftInvariantDerivation d`
  forces nilpotence of `differential d`.
* `Derivation.tangentMatrix_derivationComp_coordinateBialgHom_eq_toMatrix`: the tangent matrix of
  a coordinate morphism is the matrix of `Comodule.differential d`.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential`:
  nilpotence of `differential d` on a faithful finite free comodule forces local nilpotence of
  `leftInvariantDerivation d`.
* `TauCeti.Comodule.endOfPoint_expPointAt`, `TauCeti.Comodule.basePointsRepresentation_expPointAt`,
  and `TauCeti.Comodule.basePointsRepresentation_expPoint`: exponential points act on finitely
  generated comodules by `IsNilpotent.exp` of the differentiated action.
* `TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt` and
  `TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`: exponential points are unipotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

section Differential

variable {R H M : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The differentiated action of a tangent vector intertwines the coaction with the
left-invariant derivation on the coefficient leg. -/
theorem coact_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (m : M) :
    coact (R := R) (C := H) (differential (R := R) (H := H) (M := M) d m) =
      (Bialgebra.leftInvariantDerivation d).toLinearMap.lTensor M (coact (R := R) (C := H) m) := by
  set φ := (Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap
  have hD : (Bialgebra.leftInvariantDerivation d).toLinearMap =
      LinearMap.tensorComponent φ ∘ₗ Coalgebra.comul :=
    LinearMap.ext (Bialgebra.leftInvariantDerivation_apply d)
  rw [differential_apply, ← LinearMap.tensorComponent_rTensor, ← coassoc_symm_apply,
    LinearMap.tensorComponent_assoc_symm, hD, LinearMap.lTensor_comp_apply]

/-- Iterates of the differentiated action intertwine the coaction with iterates of the
left-invariant derivation. -/
theorem coact_iterate_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (n : ℕ) (m : M) :
    coact (R := R) (C := H)
        ((differential (R := R) (H := H) (M := M) d)^[n] m) =
      ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n).lTensor M
        (coact (R := R) (C := H) m) := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
    rw [Function.iterate_succ_apply', coact_differential, ih, pow_succ',
      LinearMap.lTensor_mul, mul_apply_eq_comp]

/-- The `n`-th iterate of `differential d` contracts the coaction against `ε ∘ Dⁿ`. -/
theorem iterate_differential_apply (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (n : ℕ) (m : M) :
    (differential (R := R) (H := H) (M := M) d)^[n] m =
      LinearMap.tensorComponent
        (Coalgebra.counit (R := R) ∘ₗ (Bialgebra.leftInvariantDerivation d).toLinearMap ^ n)
        (coact (R := R) (C := H) m) := by
  have hcounit := congrArg (TensorProduct.rid R M)
    (lTensor_counit_coact (R := R) (C := H)
      ((differential (R := R) (H := H) (M := M) d)^[n] m))
  rw [TensorProduct.rid_tmul, one_smul] at hcounit
  rw [← hcounit, coact_iterate_differential, ← LinearMap.lTensor_comp_apply,
    LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- If the left-invariant derivation of `d` is locally nilpotent on `H`, then `differential d` is
locally nilpotent on every `H`-comodule. -/
theorem exists_iterate_differential_eq_zero
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (m : M) :
    ∃ n, (differential (R := R) (H := H) (M := M) d)^[n] m = 0 := by
  set D := Bialgebra.leftInvariantDerivation d
  suffices ∀ z : M ⊗[R] H, ∃ N, ∀ n ≥ N,
      LinearMap.tensorComponent (Coalgebra.counit (R := R) ∘ₗ D.toLinearMap ^ n) z = 0 by
    obtain ⟨N, hN⟩ := this (coact (R := R) (C := H) m)
    exact ⟨N, by rw [iterate_differential_apply]; exact hN N le_rfl⟩
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x h =>
    obtain ⟨N, hN⟩ := hd h
    refine ⟨N, fun n hn ↦ ?_⟩
    have hzero : (D.toLinearMap ^ n) h = 0 :=
      Module.End.pow_map_zero_of_le hn (by simpa [FunLike.coe_pow_eq_iterate] using hN)
    simp [LinearMap.tensorComponent_tmul, hzero]
  | add z₁ z₂ ih₁ ih₂ =>
    obtain ⟨N₁, hN₁⟩ := ih₁
    obtain ⟨N₂, hN₂⟩ := ih₂
    exact ⟨max N₁ N₂, fun n hn ↦ by
      rw [map_add, hN₁ n (le_of_max_le_left hn), hN₂ n (le_of_max_le_right hn), add_zero]⟩

/-- If the left-invariant derivation of `d` is locally nilpotent on `H`, then `differential d` is
nilpotent on every finitely generated `H`-comodule. -/
theorem isNilpotent_differential [Module.Finite R M]
    {d : Derivation R H (Bialgebra.CounitAlgebra R H R)}
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsNilpotent (differential (R := R) (H := H) (M := M) d) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose deg hdeg using exists_iterate_differential_eq_zero (M := M) hd
  refine ⟨s.sup deg, ?_⟩
  apply LinearMap.ext
  intro m
  have hm : m ∈ Submodule.span R (s : Set M) := hs.symm ▸ Submodule.mem_top
  rw [LinearMap.zero_apply]
  refine Submodule.span_induction (p := fun x _ ↦ (differential (R := R) (H := H) (M := M) d ^
      s.sup deg) x = 0) ?_ (map_zero _) (fun x y _ _ hx hy ↦ by rw [map_add, hx, hy, add_zero])
    (fun r x _ hx ↦ by rw [map_smul, hx, smul_zero]) hm
  intro x hx
  exact Module.End.pow_map_zero_of_le (Finset.le_sup hx)
    (by simpa [FunLike.coe_pow_eq_iterate] using hdeg x)

end Differential

end TauCeti.Comodule

namespace Derivation

open TauCeti

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] {n : ℕ}

/-- The tangent matrix of a representation's coordinate morphism at `d` is the matrix of the
differentiated representation `Comodule.differential d` in the chosen basis. -/
theorem tangentMatrix_derivationComp_coordinateBialgHom_eq_toMatrix
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M) :
    GeneralLinear.tangentMatrix n
        (derivationComp (Comodule.coordinateBialgHom (H := H) b) d) =
      LinearMap.toMatrix b b (Comodule.differential (R := R) (H := H) (M := M) d) := by
  ext i j
  rw [d.tangentMatrix_derivationComp_coordinateBialgHom_apply b i j,
    Comodule.coefficientMatrix_apply, d.apply_matrixCoefficient, LinearMap.toMatrix_apply,
    Module.Basis.coord_apply]

/-- The tangent matrix of a representation's coordinate morphism is nilpotent if and only if
`Comodule.differential d` is nilpotent. -/
theorem isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_iff
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M) :
    IsNilpotent (GeneralLinear.tangentMatrix n
        (derivationComp (Comodule.coordinateBialgHom (H := H) b) d)) ↔
      IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d) := by
  rw [d.tangentMatrix_derivationComp_coordinateBialgHom_eq_toMatrix b]
  change IsNilpotent (LinearMap.toMatrixAlgEquiv b
      (Comodule.differential (R := R) (H := H) (M := M) d)) ↔ _
  exact ⟨fun h ↦ by simpa using h.map (LinearMap.toMatrixAlgEquiv b).symm,
    fun h ↦ h.map (LinearMap.toMatrixAlgEquiv b)⟩

/-- **Local nilpotence from a faithful representation.** If `d` acts nilpotently on a finite free
comodule whose coordinate morphism `O(GLₙ) → H` is surjective, then the left-invariant derivation
of `d` is locally nilpotent on `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hf : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (hnil : IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 :=
  BialgHom.exists_iterate_leftInvariantDerivation_eq_zero_of_surjective
    (Comodule.coordinateBialgHom (H := H) b) hf d
    (GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero n _
      ((d.isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_iff b).mpr hnil))

end Derivation

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
    obtain ⟨K, hK⟩ := isNilpotent_differential (R := R) (H := H) (M := M) hd
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
      smul_eq_mul, ← iterate_differential_apply d k m, FunLike.coe_pow_eq_iterate]

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
  obtain ⟨K, hK⟩ := isNilpotent_differential (R := R) (H := H) (M := M) hd
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

/-- Over a `ℚ`-algebra base ring, the base-valued action of `expPoint d hd` on a finitely
generated comodule is `exp (differential d)`. -/
theorem basePointsRepresentation_expPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    basePointsRepresentation (R := R) (H := H) M (WithConv.toConv (Bialgebra.expPoint d hd)) =
      IsNilpotent.exp (differential (R := R) (H := H) (M := M) d) := by
  rw [← Bialgebra.expPointAt_one, basePointsRepresentation_expPointAt, one_smul]

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
  obtain ⟨K, hK⟩ := Comodule.isNilpotent_differential (R := R) (H := H) (M := M) hd
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
