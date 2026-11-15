/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Exponential
import TauCeti.Algebra.AlgebraicGroup.Representation.Kernel
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# Comodule representations of tangent exponentials

Let `H` be a commutative Hopf algebra over `R` which is also a `ℚ`-algebra, and let `d` be a
tangent vector at the identity whose left-invariant derivation `D` is locally nilpotent. On any
right `H`-comodule `M`, the powers of the differentiated action `Comodule.differential d` contract
the coaction against the counits `ε ∘ Dⁿ` of the iterated invariant derivation. Consequently,
whenever `Comodule.differential d` is nilpotent on `M` (and `M` carries a `ℚ`-module structure, or
after extending scalars to a commutative `R`-algebra `A` that is a `ℚ`-module), the exponential
curve `t ↦ expPointAt d hd t` acts on `A ⊗[R] M` by the finite operator exponential
`IsNilpotent.exp (t • (Comodule.differential d).baseChange A)`, and on `M` itself at `t : R` by
`IsNilpotent.exp (t • Comodule.differential d)`.

Quantifying over all finitely generated comodules yields two consequences:

* every point `expPointAt d hd t` (and `expPoint d hd`) is unipotent in the representation-theoretic
  sense (`HopfAlgebra.IsUnipotentPoint`) whenever `d` acts nilpotently on every finitely generated
  `H`-comodule;
* conversely, if `H` has a finite free representation with surjective coordinate map `O(GLₙ) ⟶ H`
  on which `Comodule.differential d` is nilpotent, or if `H` is projective as an `R`-module (in
  particular whenever `R` is a field, without any finite-type assumption on `H`) and `d` acts
  nilpotently on every finitely generated `H`-comodule, then the left-invariant derivation of `d`
  is locally nilpotent on `H`.

## Main declarations

* `TauCeti.Bialgebra.toConv_counit_comp_pow_leftInvariantDerivation`: in the convolution dual,
  `ε ∘ Dⁿ` is the `n`-th convolution power of `d`.
* `TauCeti.Comodule.differential_pow` and `TauCeti.Comodule.differential_pow_apply`: powers of the
  differentiated comodule action contract the coaction against `ε ∘ Dⁿ`.
* `TauCeti.Comodule.endOfPoint_expPointAt`: on `A ⊗[R] M`, the exponential curve acts by
  `IsNilpotent.exp (t • (Comodule.differential d).baseChange A)`.
* `TauCeti.Comodule.basePointsRepresentation_expPointAt` and
  `TauCeti.Comodule.basePointsRepresentation_expPoint`: on `M`, the base-valued exponential curve
  and exponential point act by `IsNilpotent.exp (t • Comodule.differential d)` and
  `IsNilpotent.exp (Comodule.differential d)`.
* `TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt` and
  `TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`: exponential points of tangent vectors acting
  nilpotently on every finitely generated comodule are unipotent points.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential` and
  `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_forall_fgComodule`: local
  nilpotence of the left-invariant derivation from nilpotence of differentiated representations.

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

/-- Applying the `n`-th power of the differentiated action of `d` contracts the coaction against
`ε ∘ Dⁿ`. -/
theorem differential_pow_apply (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (n : ℕ) (m : M) :
    (differential (R := R) (H := H) (M := M) d ^ n) m =
      tensorComponent
        (Coalgebra.counit (R := R) ∘ₗ (Bialgebra.leftInvariantDerivation d).toLinearMap ^ n)
        (coact (R := R) (C := H) m) := by
  rw [differential_pow, convolutionAction_apply, ofConv_toConv]

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
  let : Algebra ℚ R :=
    ((Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  let D := Bialgebra.leftInvariantDerivation d
  induction x using TensorProduct.inductionOn with
  | tmul m' h =>
    obtain ⟨n₀, hn₀⟩ := hd h
    refine ⟨n₀, fun N hN => ?_⟩
    have hdeg : ∀ k ≥ N, (Bialgebra.expPointPolynomial d hd h).coeff k = 0 := by
      intro k hk
      have hk0 : D^[k] h = 0 := by
        simpa [pow_apply_eq_iterate] using
          Module.End.pow_map_zero_of_le (f := D.toLinearMap) (le_trans hN hk)
            (by simpa [pow_apply_eq_iterate] using hn₀)
      rw [Bialgebra.coeff_expPointPolynomial, hk0, smul_zero, map_zero]
    have haeval : Polynomial.aeval t (Bialgebra.expPointPolynomial d hd h) =
        ∑ k ∈ Finset.range N,
          Coalgebra.counit (R := R) ((k.factorial : ℚ)⁻¹ • D^[k] h) • t ^ k := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      refine (Finset.sum_subset (fun k hk => Finset.mem_range.mpr
        (lt_of_not_ge fun hge => Polynomial.mem_support_iff.mp hk (hdeg k hge))) ?_).trans ?_
      · intro k _ hk
        rw [Polynomial.notMem_support_iff.mp hk, map_zero, zero_mul]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [Bialgebra.coeff_expPointPolynomial, ← Algebra.smul_def]
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, Bialgebra.expPointAt_apply,
      TensorProduct.comm_tmul, haeval, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    let c : R := Coalgebra.counit (R := R) (D^[k] h)
    have hrat : ((k.factorial : ℚ)⁻¹ • c) • ((t ^ k) ⊗ₜ[R] m') =
        (k.factorial : ℚ)⁻¹ • (c • ((t ^ k) ⊗ₜ[R] m')) :=
      map_rat_smul (AddMonoidHom.mk' (fun s : R => s • ((t ^ k) ⊗ₜ[R] m'))
        fun s₁ s₂ => add_smul s₁ s₂ _) (k.factorial : ℚ)⁻¹ c
    have hsmul : (((k.factorial : ℚ)⁻¹ • c) • t ^ k) ⊗ₜ[R] m' =
        (k.factorial : ℚ)⁻¹ • (t ^ k • ((1 : A) ⊗ₜ[R] (c • m'))) := by
      calc (((k.factorial : ℚ)⁻¹ • c) • t ^ k) ⊗ₜ[R] m'
          = ((k.factorial : ℚ)⁻¹ • c) • ((t ^ k) ⊗ₜ[R] m') := (smul_tmul' _ _ _).symm
        _ = (k.factorial : ℚ)⁻¹ • (c • ((t ^ k) ⊗ₜ[R] m')) := hrat
        _ = (k.factorial : ℚ)⁻¹ • ((t ^ k) ⊗ₜ[R] (c • m')) := by
          congr 1
          rw [smul_tmul', smul_tmul]
        _ = (k.factorial : ℚ)⁻¹ • ((t ^ k * 1) ⊗ₜ[R] (c • m')) := by rw [mul_one]
        _ = (k.factorial : ℚ)⁻¹ • (t ^ k • ((1 : A) ⊗ₜ[R] (c • m'))) := rfl
    rw [map_rat_smul, hsmul]
    simp [c, D, FunLike.coe_pow_eq_iterate]
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
  rw [← differential_pow_apply]
  simp [smul_pow, ← LinearMap.baseChange_pow]

/-- The exponential curve evaluated at a base scalar `t : R` acts on a comodule `M` by
`IsNilpotent.exp (t • differential d)` whenever `differential d` is nilpotent on `M`. -/
theorem basePointsRepresentation_expPointAt [Module ℚ M]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hdiff : IsNilpotent (differential (R := R) (H := H) (M := M) d)) (t : R) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  let : Algebra ℚ R :=
    ((Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
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

/-- The exponential point `expPoint d hd` acts on a comodule `M` by
`IsNilpotent.exp (differential d)` whenever `differential d` is nilpotent on `M`. -/
theorem basePointsRepresentation_expPoint [Module ℚ M]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (hdiff : IsNilpotent (differential (R := R) (H := H) (M := M) d)) :
    basePointsRepresentation (H := H) M (toConv (Bialgebra.expPoint d hd)) =
      IsNilpotent.exp (differential (R := R) (H := H) (M := M) d) := by
  rw [← Bialgebra.expPointAt_one, basePointsRepresentation_expPointAt d hd hdiff 1, one_smul]

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
  let : Algebra ℚ R :=
    ((Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  let : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
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

namespace Derivation

open TauCeti

section SurjectiveCoordinate

universe u v w

variable {R : Type u} {H : Type v} {M : Type w} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] {n : ℕ}

/-- If a finite free representation of `H` has surjective coordinate bialgebra morphism
`O(GLₙ) ⟶ H` and `d` acts nilpotently on it, then the left-invariant derivation of `d` is locally
nilpotent on `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hb : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (hdiff : IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    ∀ h : H, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  let f := Comodule.coordinateBialgHom (H := H) b
  have hmat : IsNilpotent (GeneralLinear.tangentMatrix n (derivationComp f d)) := by
    rw [d.tangentMatrix_comp_coordinateBialgHom b]
    exact hdiff.map (LinearMap.toMatrixAlgEquiv b).toRingHom
  exact f.exists_iterate_leftInvariantDerivation_eq_zero_of_surjective hb d
    (GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero n _ hmat)

end SurjectiveCoordinate

section ProjectiveBialgebra

universe u v

/-- If `H` is projective as an `R`-module (for instance whenever `R` is a field, without any
finite-type assumption on `H`) and `d` acts nilpotently on every finitely generated `H`-comodule,
then the left-invariant derivation of `d` is locally nilpotent on `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_forall_fgComodule
    {R : Type u} {H : Type v} [CommRing R] [CommRing H] [Bialgebra R H] [Module.Projective R H]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hdiff : ∀ M : FGComoduleCat.{u, v, v} R H,
      IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    ∀ h : H, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  intro h
  obtain ⟨W, hWfin, hh⟩ := Subcomodule.exists_finite_subcomodule_mem (R := R) (C := H) h
  let _ : Module.Finite R W := hWfin
  let M : FGComoduleCat.{u, v, v} R H := FGComoduleCat.of (R := R) (C := H) W
  obtain ⟨m, hm⟩ := hdiff M
  refine ⟨m, ?_⟩
  let fM := @Comodule.differential R H M _ _ _ M.instAddCommGroupCarrier M.instModuleCarrier
    M.instComoduleCarrier d
  have hsemi : Function.Semiconj W.subtype fM (Bialgebra.leftInvariantDerivation d) := fun w => by
    have hfw : fM w = Comodule.differential (R := R) (H := H) (M := W) d w := by
      simp only [fM, M, Comodule.differential_apply]
    rw [hfw, ← Derivation.coeFn_coe, Bialgebra.toLinearMap_leftInvariantDerivation,
      ← W.subtype.map_differential d w]
  have hm0 : (⇑fM)^[m] ⟨h, hh⟩ = 0 := by
    simpa [fM, pow_apply_eq_iterate] using LinearMap.congr_fun hm ⟨h, hh⟩
  rw [show h = W.subtype ⟨h, hh⟩ from (W.subtype_apply ⟨h, hh⟩).symm,
    ← hsemi.iterate_right m ⟨h, hh⟩, hm0, map_zero]

end ProjectiveBialgebra

end Derivation
