/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.TensorProduct.Tower
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Exponential

/-!
# Exponential points acting on comodule representations

Let `H` be a commutative bialgebra over a commutative ring `R`, and let `d` be a tangent vector at
the identity with left-invariant derivation `D = Bialgebra.leftInvariantDerivation d`. On any right
`H`-comodule `M`, differentiating the coaction yields `Comodule.differential d : Module.End R M`.
Coassociativity shows that `ρ ∘ (differential d)ⁿ = (id ⊗ Dⁿ) ∘ ρ`, whence `(differential d)ⁿ`
contracts the coaction against `ε ∘ Dⁿ`.

This gives two complementary bridges between local nilpotence of `D` on `H` and nilpotence of
`differential d` on finite comodules:

* **Forward direction (exponential action and unipotence).** Whenever `D` is locally nilpotent on
  `H`, `differential d` is locally nilpotent on every right comodule `M` and globally nilpotent on
  every finitely generated comodule `M`. If in addition `H` is a `ℚ`-algebra, then for any
  commutative `R`-algebra `B` and parameter `t : B`, the exponential point `expPointAt d hd t`
  acts on `B ⊗[R] M` as `IsNilpotent.exp (t • (differential d).baseChange B)` whenever `B` carries
  a `ℚ`-algebra structure. Over a Hopf algebra, every exponential point `expPointAt d hd t` is
  therefore unipotent (`HopfAlgebra.IsUnipotentPoint`), with no `ℚ`-algebra assumption needed on
  the base `R` or value algebra `B` beyond `[Algebra ℚ H]`.
* **Backward direction (descent of local nilpotence).** For a free finite-rank comodule `M` with
  basis `b : Module.Basis (Fin n) R M`, the tangent matrix of the coordinate morphism
  `Comodule.coordinateBialgHom b` is literally `LinearMap.toMatrix b b (Comodule.differential d)`.
  Consequently, when `coordinateBialgHom b` is surjective, `D` is locally nilpotent on `H` if and
  only if `differential d` is nilpotent on `M`.

## Main declarations

* `TauCeti.Comodule.coact_differential` and `TauCeti.Comodule.coact_pow_differential`:
  `ρ ((differential d)ⁿ m) = (id ⊗ Dⁿ) (ρ m)`.
* `TauCeti.Comodule.pow_differential_apply`:
  `(differential d)ⁿ m = tensorComponent (ε ∘ Dⁿ) (ρ m)`.
* `TauCeti.Comodule.isNilpotent_differential`: local nilpotence of `D` implies nilpotence of
  `differential d` on any finitely generated comodule.
* `TauCeti.Comodule.endOfPoint_expPointAt`: the point `expPointAt d hd t` acts on `B ⊗[R] M` as
  `IsNilpotent.exp (t • (differential d).baseChange B)`.
* `TauCeti.Comodule.basePointsRepresentation_expPointAt` and
  `TauCeti.Comodule.basePointsRepresentation_expPoint`: the base-ring specialization on `M`.
* `TauCeti.HopfAlgebra.isUnipotentPoint_expPointAt` and
  `TauCeti.HopfAlgebra.isUnipotentPoint_expPoint`: exponential points are unipotent over any
  commutative value algebra.
* `Derivation.tangentMatrix_derivationComp_coordinateBialgHom`: the tangent matrix of
  `coordinateBialgHom b` equals `LinearMap.toMatrix b b (Comodule.differential d)`.
* `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential` and
  `Derivation.exists_iterate_leftInvariantDerivation_eq_zero_iff_isNilpotent_differential`: local
  nilpotence of `D` descends from nilpotence of `differential d` on a faithful free representation.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 12.
-/

public section

open TensorProduct LinearMap

namespace TauCeti.Comodule

section Coaction

variable {R H M : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The coaction intertwines the differentiated action with the left-invariant derivation on the
coefficient factor. -/
theorem coact_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (m : M) :
    coact (R := R) (C := H) (differential (R := R) (H := H) d m) =
      (Bialgebra.leftInvariantDerivation d).toLinearMap.lTensor M
        (coact (R := R) (C := H) m) := by
  have hD : (Bialgebra.leftInvariantDerivation d).toLinearMap =
      tensorComponent
        ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) ∘ₗ
          Coalgebra.comul :=
    LinearMap.ext (Bialgebra.leftInvariantDerivation_apply d)
  rw [hD, differential_apply, ← coactComponent_apply, coact_coactComponent]

/-- Iterating `differential d` intertwines with iterating the left-invariant derivation on the
coefficient factor. -/
theorem coact_pow_differential (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (n : ℕ) (m : M) :
    coact (R := R) (C := H) ((differential (R := R) (H := H) d ^ n) m) =
      ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n).lTensor M
        (coact (R := R) (C := H) m) := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, coact_differential, ih, pow_succ',
      LinearMap.lTensor_mul, mul_apply_eq_comp]

/-- The `n`-th power of the differentiated action contracts the coaction against the counit of
the `n`-th power of the left-invariant derivation. -/
theorem pow_differential_apply (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (n : ℕ) (m : M) :
    (differential (R := R) (H := H) d ^ n) m =
      tensorComponent (Coalgebra.counit (R := R) ∘ₗ
          (Bialgebra.leftInvariantDerivation d).toLinearMap ^ n)
        (coact (R := R) (C := H) m) := by
  have hcounit := congrArg (TensorProduct.rid R M)
    (lTensor_counit_coact (R := R) (C := H) ((differential (R := R) (H := H) d ^ n) m))
  rw [TensorProduct.rid_tmul, one_smul] at hcounit
  rw [← hcounit, coact_pow_differential, ← LinearMap.lTensor_comp_apply,
    tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe]

omit [Comodule R H M] in
private theorem exists_forall_pow_leftInvariantDerivation_lTensor_eq_zero
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (x : M ⊗[R] H) :
    ∃ N, ∀ n ≥ N, ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n).lTensor M x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul m h =>
    obtain ⟨N, hN⟩ := hd h
    refine ⟨N, fun n hn ↦ ?_⟩
    have hzero : ((Bialgebra.leftInvariantDerivation d).toLinearMap ^ n) h = 0 :=
      Module.End.pow_map_zero_of_le hn (by simpa [pow_apply_eq_iterate] using hN)
    rw [LinearMap.lTensor_tmul, hzero, tmul_zero]
  | add x y hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
    rw [map_add, h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn), add_zero]

/-- If the left-invariant derivation of `d` is locally nilpotent on `H`, then `differential d` is
locally nilpotent on every right `H`-comodule `M`. -/
theorem exists_pow_differential_apply_eq_zero
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) (m : M) :
    ∃ n, (differential (R := R) (H := H) d ^ n) m = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_pow_leftInvariantDerivation_lTensor_eq_zero (M := M) d hd
    (coact (R := R) (C := H) m)
  refine ⟨N, ?_⟩
  rw [pow_differential_apply, tensorComponent_def, LinearMap.comp_apply,
    LinearMap.lTensor_comp_apply, hN N le_rfl, map_zero, map_zero]

/-- **Local nilpotence of the invariant derivation implies nilpotence of every finite-rank
differentiated representation.** No field or characteristic hypothesis is needed. -/
theorem isNilpotent_differential [Module.Finite R M]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsNilpotent (differential (R := R) (H := H) (M := M) d) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose deg hdeg using fun m : M ↦ exists_pow_differential_apply_eq_zero (M := M) d hd m
  refine ⟨s.sup deg, LinearMap.ext fun m ↦ ?_⟩
  rw [LinearMap.zero_apply]
  have hmem : m ∈ LinearMap.ker (differential (R := R) (H := H) (M := M) d ^ s.sup deg) := by
    have hle : (⊤ : Submodule R M) ≤
        LinearMap.ker (differential (R := R) (H := H) (M := M) d ^ s.sup deg) := by
      rw [← hs, Submodule.span_le]
      intro v hv
      exact Module.End.pow_map_zero_of_le (Finset.le_sup (f := deg) hv) (hdeg v)
    exact hle Submodule.mem_top
  exact hmem

end Coaction

section ExponentialAction

variable {R H M : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H] [Algebra ℚ H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

omit [Algebra ℚ H] [Comodule R H M] in
private theorem comm_lTensor_algebraOfId_comp
    {B : Type*} [CommRing B] [Algebra R B] (f : H →ₗ[R] R) (x : M ⊗[R] H) :
    TensorProduct.comm R M B
        ((((Algebra.ofId R B).toLinearMap ∘ₗ f).lTensor M) x) =
      1 ⊗ₜ[R] tensorComponent f x := by
  induction x using TensorProduct.inductionOn with
  | tmul m h =>
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, hx, hy]

omit [Comodule R H M] in
private theorem aeval_expPointPolynomial_eq_sum_range
    {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (t : B) {h : H} {N₀ N : ℕ}
    (hN₀ : (Bialgebra.leftInvariantDerivation d)^[N₀] h = 0) (hN : N₀ ≤ N) :
    let : Algebra ℚ R :=
      ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
    Polynomial.aeval t (Bialgebra.expPointPolynomial d hd h) =
      ∑ k ∈ Finset.range N,
        algebraMap R B ((Bialgebra.expPointPolynomial d hd h).coeff k) * t ^ k := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  set p : Polynomial R := Bialgebra.expPointPolynomial d hd h
  have hcoeff_zero : ∀ k ≥ N, p.coeff k = 0 := fun k hk ↦ by
    have hk0 : (Bialgebra.leftInvariantDerivation d)^[k] h = 0 := by
      simpa [pow_apply_eq_iterate] using
        Module.End.pow_map_zero_of_le (f := (Bialgebra.leftInvariantDerivation d).toLinearMap)
          (le_trans hN hk) (by simpa [pow_apply_eq_iterate] using hN₀)
    rw [Bialgebra.coeff_expPointPolynomial, hk0, smul_zero, map_zero]
  rw [Polynomial.aeval_eq_sum_range]
  simp only [Algebra.smul_def]
  by_cases hlt : p.natDegree < N
  · exact Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hlt)) fun k _ hk ↦ by
      rw [Finset.mem_range, not_lt] at hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hk), map_zero, zero_mul]
  · push Not at hlt
    exact (Finset.sum_subset (Finset.range_mono (Nat.le_succ_of_le hlt)) fun k _ hk ↦ by
      rw [Finset.mem_range, not_lt] at hk
      rw [hcoeff_zero k hk, map_zero, zero_mul]).symm

omit [Comodule R H M] in
private theorem exists_comm_lTensor_expPointAt_eq_sum
    {B : Type*} [CommRing B] [Algebra R B] [Algebra ℚ B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (t : B) (x : M ⊗[R] H) :
    ∃ N₀, ∀ N ≥ N₀,
      TensorProduct.comm R M B
          ((Bialgebra.expPointAt d hd t).ofConv.toLinearMap.lTensor M x) =
        ∑ k ∈ Finset.range N, (k.factorial : ℚ)⁻¹ • (t ^ k •
          TensorProduct.comm R M B
            ((((Algebra.ofId R B).toLinearMap ∘ₗ Coalgebra.counit (R := R) ∘ₗ
              (Bialgebra.leftInvariantDerivation d).toLinearMap ^ k).lTensor M) x)) := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul m h =>
    obtain ⟨N₀, hN₀⟩ := hd h
    refine ⟨N₀, fun N hN ↦ ?_⟩
    rw [LinearMap.lTensor_tmul, TensorProduct.comm_tmul, AlgHom.toLinearMap_apply,
      Bialgebra.expPointAt_apply d hd t h,
      aeval_expPointPolynomial_eq_sum_range d hd t hN₀ hN, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [LinearMap.lTensor_tmul, TensorProduct.comm_tmul]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, FunLike.coe_pow_eq_iterate,
      Derivation.coeFn_coe, TensorProduct.smul_tmul', smul_eq_mul]
    have hcp : (Bialgebra.expPointPolynomial d hd h).coeff k =
        (k.factorial : ℚ)⁻¹ • Coalgebra.counit (R := R)
          ((Bialgebra.leftInvariantDerivation d)^[k] h) := by
      rw [Bialgebra.coeff_expPointPolynomial, map_rat_smul]
    rw [hcp, map_rat_smul, smul_mul_assoc, mul_comm (algebraMap R B _) (t ^ k)]
    rfl
  | add x y hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    refine ⟨max N₁ N₂, fun N hN ↦ ?_⟩
    rw [map_add, map_add, h₁ N (le_of_max_le_left hN), h₂ N (le_of_max_le_right hN),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_add, map_add, smul_add, smul_add]

/-- **The exponential point acts on every finite-rank comodule as the finite exponential of its
differentiated action.** For any `B`-parameter `t`, `expPointAt d hd t` acts on `B ⊗[R] M` as
`IsNilpotent.exp (t • (differential d).baseChange B)`. -/
theorem endOfPoint_expPointAt [Module.Finite R M]
    {B : Type*} [CommRing B] [Algebra R B] [Algebra ℚ B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (t : B) :
    endOfPoint M (Bialgebra.expPointAt d hd t).ofConv =
      IsNilpotent.exp (t • (differential (R := R) (H := H) (M := M) d).baseChange B) := by
  obtain ⟨K, hK⟩ := isNilpotent_differential (M := M) d hd
  have hK' : (t • (differential (R := R) (H := H) (M := M) d).baseChange B) ^ K = 0 := by
    rw [smul_pow, ← LinearMap.baseChange_pow, hK, LinearMap.baseChange_zero, smul_zero]
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    have hsmul : b ⊗ₜ[R] m = b • (1 ⊗ₜ[R] m) := by simp [TensorProduct.smul_tmul']
    rw [hsmul, map_smul, map_smul]
    congr 1
    obtain ⟨N₀, hN₀⟩ := exists_comm_lTensor_expPointAt_eq_sum (M := M) d hd t
      (coact (R := R) (C := H) m)
    set N := max N₀ K
    have hNK : (t • (differential (R := R) (H := H) (M := M) d).baseChange B) ^ N = 0 :=
      pow_eq_zero_of_le (le_max_right N₀ K) hK'
    rw [endOfPoint_tmul, one_smul, hN₀ N (le_max_left N₀ K), IsNilpotent.exp_eq_sum hNK,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [comm_lTensor_algebraOfId_comp, ← pow_differential_apply, LinearMap.smul_apply,
      smul_pow, LinearMap.smul_apply, ← LinearMap.baseChange_pow, LinearMap.baseChange_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

end ExponentialAction

section BasePoints

variable {R H M : Type*} [CommRing R] [CommRing H] [_root_.HopfAlgebra R H] [Algebra ℚ H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

/-- On the original comodule `M` over the base ring `R`, the exponential curve `expPointAt d hd t`
acts by `IsNilpotent.exp (t • differential d)`. -/
theorem basePointsRepresentation_expPointAt [Module.Finite R M] [Module ℚ M]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    (t : R) :
    basePointsRepresentation (H := H) M (Bialgebra.expPointAt d hd t) =
      IsNilpotent.exp (t • differential (R := R) (H := H) (M := M) d) := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  obtain ⟨K, hK⟩ := isNilpotent_differential (M := M) d hd
  have hK1 : (t • (differential (R := R) (H := H) (M := M) d).baseChange R) ^ K = 0 := by
    rw [smul_pow, ← LinearMap.baseChange_pow, hK, LinearMap.baseChange_zero, smul_zero]
  have hK2 : (t • differential (R := R) (H := H) (M := M) d) ^ K = 0 := by
    rw [smul_pow, hK, smul_zero]
  ext m
  rw [basePointsRepresentation_apply, endOfPoint_expPointAt (B := R) d hd t,
    IsNilpotent.exp_eq_sum hK1, IsNilpotent.exp_eq_sum hK2,
    LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_rat_smul, smul_pow, smul_pow,
    LinearMap.smul_apply, LinearMap.smul_apply, ← LinearMap.baseChange_pow,
    LinearMap.baseChange_tmul, map_smul, TensorProduct.lid_tmul, one_smul]

/-- On the original comodule `M` over `R`, the exponential point `expPoint d hd` acts by
`IsNilpotent.exp (differential d)`. -/
theorem basePointsRepresentation_expPoint [Module.Finite R M] [Module ℚ M]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    basePointsRepresentation (H := H) M (WithConv.toConv (Bialgebra.expPoint d hd)) =
      IsNilpotent.exp (differential (R := R) (H := H) (M := M) d) := by
  rw [← Bialgebra.expPointAt_one, basePointsRepresentation_expPointAt d hd 1, one_smul]

end BasePoints

end TauCeti.Comodule

namespace TauCeti.HopfAlgebra

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.HopfAlgebra R H] [Algebra ℚ H]

/-- **Every point on an exponential one-parameter subgroup is unipotent**, over any commutative
value algebra `B`. No `ℚ`-algebra hypothesis is required separately on `R` or `B`. -/
theorem isUnipotentPoint_expPointAt
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    {B : Type*} [CommRing B] [Algebra R B] (t : B) :
    IsUnipotentPoint (Bialgebra.expPointAt d hd t) := by
  let : Algebra ℚ R :=
    ((_root_.Bialgebra.counitAlgHom R H).toRingHom.comp (algebraMap ℚ H)).toAlgebra
  let : Algebra ℚ B := ((algebraMap R B).comp (algebraMap ℚ R)).toAlgebra
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  rw [Comodule.endOfPoint_expPointAt d hd t]
  obtain ⟨K, hK⟩ := Comodule.isNilpotent_differential (M := M) d hd
  refine IsNilpotent.isNilpotent_exp_sub_one ⟨K, ?_⟩
  rw [smul_pow, ← LinearMap.baseChange_pow, hK, LinearMap.baseChange_zero, smul_zero]

/-- **The exponential of a tangent vector with locally nilpotent invariant derivation is a
unipotent point.** -/
theorem isUnipotentPoint_expPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ h, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0) :
    IsUnipotentPoint (WithConv.toConv (Bialgebra.expPoint d hd)) := by
  rw [← Bialgebra.expPointAt_one]
  exact isUnipotentPoint_expPointAt d hd (1 : R)

end TauCeti.HopfAlgebra

namespace Derivation

open TauCeti

variable {R H M : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] {n : ℕ}

/-- The tangent matrix of a free finite-rank representation's coordinate morphism is the matrix of
its differentiated action in the given basis. -/
theorem tangentMatrix_derivationComp_coordinateBialgHom
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M) :
    GeneralLinear.tangentMatrix n
        (derivationComp (Comodule.coordinateBialgHom (H := H) b) d) =
      LinearMap.toMatrix b b (Comodule.differential (R := R) (H := H) (M := M) d) := by
  ext i j
  rw [d.tangentMatrix_derivationComp_coordinateBialgHom_apply b i j,
    Comodule.coefficientMatrix_apply, d.apply_matrixCoefficient, LinearMap.toMatrix_apply,
    Module.Basis.coord_apply]

/-- The tangent matrix of a free finite-rank representation's coordinate morphism is nilpotent if
and only if its differentiated action is nilpotent. -/
theorem isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_iff
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M) :
    IsNilpotent (GeneralLinear.tangentMatrix n
        (derivationComp (Comodule.coordinateBialgHom (H := H) b) d)) ↔
      IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d) := by
  rw [d.tangentMatrix_derivationComp_coordinateBialgHom b]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, (LinearMap.toMatrixAlgEquiv b).injective <| by
      rw [map_pow, map_zero]
      have hmat :
          LinearMap.toMatrixAlgEquiv b (Comodule.differential (R := R) (H := H) (M := M) d) =
            LinearMap.toMatrix b b (Comodule.differential (R := R) (H := H) (M := M) d) := by
        ext i j; rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
      rw [hmat, hk]⟩,
    fun h ↦ h.map (LinearMap.toMatrixAlgEquiv b).toRingHom⟩

/-- **Descent of local nilpotence along a faithful free representation.** If the coordinate
morphism of a free finite-rank comodule is surjective and `differential d` is nilpotent, then the
left-invariant derivation of `d` is locally nilpotent on the coordinate algebra `H`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hf : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (hn : IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d)) :
    ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 :=
  BialgHom.exists_iterate_leftInvariantDerivation_eq_zero_of_surjective
    (Comodule.coordinateBialgHom (H := H) b) hf d
    (GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero n _
      ((d.isNilpotent_tangentMatrix_derivationComp_coordinateBialgHom_iff b).2 hn))

/-- **Characterization of local nilpotence via a faithful free representation.** When the
coordinate morphism of a free finite-rank comodule is surjective, the left-invariant derivation of
`d` is locally nilpotent if and only if `differential d` is nilpotent. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_iff_isNilpotent_differential
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M)
    (hf : Function.Surjective (Comodule.coordinateBialgHom (H := H) b)) :
    (∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0) ↔
      IsNilpotent (Comodule.differential (R := R) (H := H) (M := M) d) :=
  ⟨fun hd ↦
    have : Module.Finite R M := Module.Finite.of_basis b
    Comodule.isNilpotent_differential d hd,
    d.exists_iterate_leftInvariantDerivation_eq_zero_of_isNilpotent_differential b hf⟩

end Derivation
