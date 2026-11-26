/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Analysis.Polynomial.Ultra
public import TauCeti.LinearAlgebra.HermiteInterpolation
import TauCeti.RingTheory.PowerSeries.GaussNorm.Estimates
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Ultrametric coefficient bounds for Hermite interpolation

Over an ultrametric normed field `K` (or more generally an ultrametric seminormed commutative ring
with `‖1‖ = 1` and multiplicative norm), let `a : ι → K` be nodes in the closed unit ball whose
differences from `a r` are units of norm at least `ϱ ∈ (0, 1]`. Although the Hermite basis
polynomial `Polynomial.hermiteBasis ha m ⟨r, s⟩` has degree below `M = ∑ i, m i` and vanishes to
order `m i` at every node `a i` with `i ≠ r` and to order `s` at `a r` (with Hasse jets `δ_{k, s}`
for `k < m r`), bounding its coefficients by `ϱ ^ (-M)` requires working in a local shifted
variable at radius `ϱ` rather than at radius `1`.

Specifically, `Polynomial.hermiteBasis_eq_prod_mul_pow_mul_taylor` expresses
`hermiteBasis ha m ⟨r, s⟩` as
`(∏ i ≠ r, (X - C (a i)) ^ m i) * (X - C (a r)) ^ s * taylor (-a r) h`, where `h` is the
truncation `PowerSeries.trunc (m r - s)` of
`∏ i ≠ r, (C (v i) * ∑ k, (-v i) ^ k * X ^ k) ^ m i` with `(a r - a i) * v i = 1`. Bounding each
truncated geometric series naively at radius `1` would give a bound of `ϱ ^ (-(m r - s))` per
linear factor and lose a quadratic exponent `ϱ ^ (-(m r - s) * ∑ i ≠ r, m i)`. At the Gauss radius
`ϱ`, however, `‖v i‖ * ϱ ≤ 1` bounds the `ϱ`-weighted coefficients of each truncated geometric
factor by `‖v i‖` (`PowerSeries.norm_coeff_trunc_C_mul_mk_pow_mul_pow_le`). Ultrametric
submultiplicativity of `ϱ`-weighted coefficient bounds (`Polynomial.norm_coeff_prod_mul_pow_le`)
then bounds the `d`-th coefficient of the truncated product by `(∏ i ≠ r, ‖v i‖ ^ m i) * ϱ ^ (-d)`
for every `d`. Rescaling from `ϱ` to the node radius `B ≥ ϱ` across natural degree at most
`m r - 1 - s` (`Polynomial.norm_coeff_mul_pow_le_of_natDegree_le`), shifting back by `-a r` via
Taylor invariance (`Polynomial.norm_coeff_taylor_mul_pow_le`), and multiplying by the global linear
factors gives the sharp exponent `M - 1 - s ≤ M`.

In characteristic zero, passing from Hasse derivatives `hasseDeriv j` to ordinary derivatives
`derivative^[j] = j ! • hasseDeriv j` divides the `(r, s)` basis polynomial by `s!`, multiplying the
ultrametric coefficient bound by `‖((s! : ℕ) : K)⁻¹‖`
(`Polynomial.exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist`).

## Main results

* `Polynomial.norm_coeff_hermiteBasis_mul_pow_le`: `B`-weighted coefficient bound for
  `hermiteBasis ha m x` over an ultrametric seminormed commutative ring in terms of explicit
  inverses of `a x.1 - a i`.
* `Polynomial.norm_coeff_hermiteBasis_mul_pow_le_prod_mul_pow_mul_pow`,
  `Polynomial.norm_coeff_hermiteBasis_mul_pow_le_of_le_norm_sub`: `B`-weighted product and
  uniform-separation bounds for `hermiteBasis ha m x` when `[NormMulClass R]`.
* `Polynomial.norm_coeff_hermiteBasis_le_inv_prod_mul_inv_pow`,
  `Polynomial.norm_coeff_hermiteBasis_le_inv_pow_sub`, `Polynomial.norm_coeff_hermiteBasis_le`:
  unit-ball bounds for `hermiteBasis ha m x` under local separation from `a x.1`.
* `Polynomial.norm_coeff_mul_pow_le_of_norm_eval_hasseDeriv_mul_pow_le`,
  `Polynomial.norm_coeff_le_of_norm_eval_hasseDeriv_mul_pow_le`: `B`-weighted and unit-ball
  coefficient bounds from Cauchy-scaled Hasse jets `‖(hasseDeriv k f).eval (a i)‖ * ϱ ^ k ≤ C`.
* `Polynomial.norm_coeff_hermiteJetEquiv_symm_le`: coefficient bound
  `C * (ϱ ^ ((∑ i, m i) - 1))⁻¹` for Hermite interpolation of Hasse jets bounded by `C`.
* `Polynomial.exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist`: existence of a
  polynomial with Kronecker-delta iterated ordinary derivatives on `ϱ`-separated unit-ball nodes and
  coefficients bounded by `‖((s.factorial : ℕ) : K)⁻¹‖ * (ϱ ^ (Fintype.card ι * S))⁻¹`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2, Lemma 7.
* M. Karatarakis, Lean 4 formalization of `p`-adic Hermite interpolation in `mkaratarakis/mathlib4`
  (branch `baker-padic`, commit `65cdef5722`,
  `Mathlib/NumberTheory/Transcendental/Baker/Padic/Hermite.lean`), from which the statement of
  `Polynomial.exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist` is adapted.
-/

public section

open Finset Polynomial
open scoped Nat

namespace Polynomial

section SeminormedCommRing

variable {ι R : Type*} [Fintype ι] [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Weighted ultrametric bound for the Hermite basis.** Over an ultrametric seminormed
commutative ring with `‖1‖ = 1`, if all nodes lie in the closed ball of radius `B`, `0 < ϱ ≤ B`, and
each difference `a x.1 - a i` (`i ≠ x.1`) has an inverse `v i` of norm at most `ϱ⁻¹`, then the
`B`-weighted coefficients of `hermiteBasis ha m x` are bounded by
`(∏ i ≠ x.1, (B * ‖v i‖) ^ m i) * B ^ x.2 * (B / ϱ) ^ (m x.1 - 1 - x.2)`. -/
theorem norm_coeff_hermiteBasis_mul_pow_le [DecidableEq ι] {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    {B ϱ : ℝ} (haB : ∀ i, ‖a i‖ ≤ B) (hϱ0 : 0 < ϱ) (hϱB : ϱ ≤ B) {v : ι → R}
    (hv : ∀ i, i ≠ x.1 → (a x.1 - a i) * v i = 1) (hvϱ : ∀ i, i ≠ x.1 → ‖v i‖ ≤ ϱ⁻¹) (n : ℕ) :
    ‖(hermiteBasis ha m x : R[X]).coeff n‖ * B ^ n ≤
      (∏ i ∈ univ.erase x.1, (B * ‖v i‖) ^ m i) * B ^ (x.2 : ℕ) *
        (B / ϱ) ^ (m x.1 - 1 - x.2) := by
  have hB0 : 0 ≤ B := hϱ0.le.trans hϱB
  set d : ℕ := m x.1 - 1 - x.2
  have hN : m x.1 - x.2 = d + 1 := by have := x.2.isLt; omega
  let g : ι → PowerSeries R := fun i ↦ PowerSeries.C (v i) * PowerSeries.mk fun k ↦ (-v i) ^ k
  let G : PowerSeries R := ∏ i ∈ univ.erase x.1, g i ^ m i
  let P : R[X] := ∏ i ∈ univ.erase x.1, PowerSeries.trunc (d + 1) (g i) ^ m i
  -- Bound each truncated geometric factor at radius `ϱ`, then multiply across `i ≠ x.1`.
  have hq (i : ι) (hi : i ∈ univ.erase x.1) (k : ℕ) :
      ‖(PowerSeries.trunc (d + 1) (g i)).coeff k‖ * ϱ ^ k ≤ ‖v i‖ := by
    have hvϱ' : ‖-v i‖ * ϱ ≤ 1 := by
      rw [norm_neg]
      exact (mul_le_mul_of_nonneg_right (hvϱ i (mem_erase.1 hi).1) hϱ0.le).trans_eq
        (inv_mul_cancel₀ hϱ0.ne')
    exact PowerSeries.norm_coeff_trunc_C_mul_mk_pow_mul_pow_le (v i) hϱ0.le hvϱ' (d + 1) k
  have hP (k : ℕ) : ‖P.coeff k‖ * ϱ ^ k ≤ ∏ i ∈ univ.erase x.1, ‖v i‖ ^ m i :=
    norm_coeff_prod_mul_pow_le _ _ hϱ0.le
      (fun i hi l ↦ norm_coeff_pow_mul_pow_le hϱ0.le (hq i hi) (m i) l) k
  -- Replace `trunc (d + 1) G` by `trunc (d + 1) P` and rescale from radius `ϱ` to `B`.
  have htrunc : PowerSeries.trunc (d + 1) G = PowerSeries.trunc (d + 1) (P : PowerSeries R) := by
    simp only [G, P, ← coeToPowerSeries.ringHom_apply, map_prod, map_pow]
    exact PowerSeries.trunc_prod_eq_of_trunc_eq _ fun i _ ↦
      (PowerSeries.trunc_trunc_pow (g i) (d + 1) (m i)).symm
  have hh (k : ℕ) :
      ‖(PowerSeries.trunc (m x.1 - x.2) G).coeff k‖ * B ^ k ≤
        (∏ i ∈ univ.erase x.1, ‖v i‖ ^ m i) * (B / ϱ) ^ d := by
    rw [hN]
    refine norm_coeff_mul_pow_le_of_natDegree_le hϱ0 hϱB
      (Nat.lt_succ_iff.1 (PowerSeries.natDegree_trunc_lt G d)) ?_
    rw [htrunc]
    exact PowerSeries.norm_coeff_trunc_mul_pow_le (by positivity) fun _ ↦ by simpa using hP k
  -- Shift by `-a x.1` and multiply by the global linear factors at radius `B`.
  rw [hermiteBasis_eq_prod_mul_pow_mul_taylor ha m x hv]
  have hQ (k : ℕ) :
      ‖(∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i).coeff k‖ * B ^ k ≤
        ∏ i ∈ univ.erase x.1, B ^ m i :=
    norm_coeff_prod_mul_pow_le _ _ hB0
      (fun i _ l ↦ norm_coeff_X_sub_C_pow_mul_pow_le (haB i) (m i) l) k
  refine (norm_coeff_mul_mul_pow_le hB0
    (norm_coeff_mul_mul_pow_le hB0 hQ (norm_coeff_X_sub_C_pow_mul_pow_le (haB x.1) x.2))
    (norm_coeff_taylor_mul_pow_le (r := -a x.1) (by simpa using haB x.1) hh) n).trans_eq ?_
  simp_rw [mul_pow, prod_mul_distrib]
  ring

variable [NormMulClass R]

/-- **Product-refined `B`-weighted bound for the Hermite basis.** Over an ultrametric seminormed
commutative ring with `‖1‖ = 1` and multiplicative norm, if all nodes have norm at most `B`,
`0 < ϱ ≤ B`, and every other node has distance at least `ϱ` from `a x.1`, then the `B`-weighted
coefficients of `hermiteBasis ha m x` are bounded by
`(∏ i ≠ x.1, (B / ‖a x.1 - a i‖) ^ m i) * B ^ x.2 * (B / ϱ) ^ (m x.1 - 1 - x.2)`. -/
theorem norm_coeff_hermiteBasis_mul_pow_le_prod_mul_pow_mul_pow [DecidableEq ι] {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    {B ϱ : ℝ} (haB : ∀ i, ‖a i‖ ≤ B) (hϱ0 : 0 < ϱ) (hϱB : ϱ ≤ B)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : R[X]).coeff n‖ * B ^ n ≤
      (∏ i ∈ univ.erase x.1, (B / ‖a x.1 - a i‖) ^ m i) * B ^ (x.2 : ℕ) *
        (B / ϱ) ^ (m x.1 - 1 - x.2) := by
  let v : ι → R := fun i ↦ if hi : i = x.1 then 0 else ↑(ha (Ne.symm hi)).unit⁻¹
  have hv (i : ι) (hi : i ≠ x.1) : (a x.1 - a i) * v i = 1 := by
    simp [v, hi]
  have hv_norm (i : ι) (hi : i ≠ x.1) : ‖v i‖ = ‖a x.1 - a i‖⁻¹ := by
    have hpos : 0 < ‖a x.1 - a i‖ := hϱ0.trans_le (hsep i hi)
    apply mul_left_cancel₀ hpos.ne'
    rw [← norm_mul, hv i hi, norm_one, mul_inv_cancel₀ hpos.ne']
  have hvϱ (i : ι) (hi : i ≠ x.1) : ‖v i‖ ≤ ϱ⁻¹ := by
    rw [hv_norm i hi]
    exact inv_anti₀ hϱ0 (hsep i hi)
  refine (norm_coeff_hermiteBasis_mul_pow_le ha m x haB hϱ0 hϱB hv hvϱ n).trans_eq ?_
  have hprod : ∏ i ∈ univ.erase x.1, (B * ‖v i‖) ^ m i =
      ∏ i ∈ univ.erase x.1, (B / ‖a x.1 - a i‖) ^ m i :=
    prod_congr rfl fun i hi ↦ by rw [hv_norm i (mem_erase.1 hi).1, div_eq_mul_inv]
  rw [hprod]

/-- Over an ultrametric seminormed commutative ring with `‖1‖ = 1` and multiplicative norm, if all
nodes have norm at most `B`, `0 < ϱ ≤ B`, and every other node has distance at least `ϱ` from
`a x.1`, then the `B`-weighted coefficients of `hermiteBasis ha m x` are bounded by
`B ^ x.2 * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2)`. -/
theorem norm_coeff_hermiteBasis_mul_pow_le_of_le_norm_sub {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    {B ϱ : ℝ} (haB : ∀ i, ‖a i‖ ≤ B) (hϱ0 : 0 < ϱ) (hϱB : ϱ ≤ B)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : R[X]).coeff n‖ * B ^ n ≤
      B ^ (x.2 : ℕ) * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2) := by
  classical
  have hB0 : 0 ≤ B := hϱ0.le.trans hϱB
  refine (norm_coeff_hermiteBasis_mul_pow_le_prod_mul_pow_mul_pow ha m x haB hϱ0 hϱB hsep
    n).trans ?_
  have hprod : ∏ i ∈ univ.erase x.1, (B / ‖a x.1 - a i‖) ^ m i ≤
      (B / ϱ) ^ (∑ i ∈ univ.erase x.1, m i) := by
    rw [← prod_pow_eq_pow_sum]
    gcongr with i hi
    exact hsep i (mem_erase.1 hi).1
  have hsum : (∑ i ∈ univ.erase x.1, m i) + (m x.1 - 1 - x.2) = (∑ i, m i) - 1 - x.2 := by
    have herase := sum_erase_add univ m (mem_univ x.1)
    have hx := x.2.isLt
    omega
  calc (∏ i ∈ univ.erase x.1, (B / ‖a x.1 - a i‖) ^ m i) * B ^ (x.2 : ℕ) *
        (B / ϱ) ^ (m x.1 - 1 - x.2)
      ≤ (B / ϱ) ^ (∑ i ∈ univ.erase x.1, m i) * B ^ (x.2 : ℕ) *
          (B / ϱ) ^ (m x.1 - 1 - x.2) := by gcongr
    _ = B ^ (x.2 : ℕ) *
          ((B / ϱ) ^ (∑ i ∈ univ.erase x.1, m i) * (B / ϱ) ^ (m x.1 - 1 - x.2)) := by ring
    _ = B ^ (x.2 : ℕ) * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2) := by rw [← pow_add, hsum]

/-- **Product-refined unit-ball bound for the Hermite basis.** For nodes in the closed unit ball
whose distances from `a x.1` are at least `ϱ ∈ (0, 1]`, every coefficient of `hermiteBasis ha m x`
has norm at most `(∏ i ≠ x.1, ‖a x.1 - a i‖ ^ m i)⁻¹ * (ϱ ^ (m x.1 - 1 - x.2))⁻¹`. -/
theorem norm_coeff_hermiteBasis_le_inv_prod_mul_inv_pow [DecidableEq ι] {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : R[X]).coeff n‖ ≤
      (∏ i ∈ univ.erase x.1, ‖a x.1 - a i‖ ^ m i)⁻¹ * (ϱ ^ (m x.1 - 1 - x.2))⁻¹ := by
  simpa [inv_pow, prod_inv_distrib] using
    norm_coeff_hermiteBasis_mul_pow_le_prod_mul_pow_mul_pow ha m x ha1 hϱ0 hϱ1 hsep n

/-- **Sharp uniform-separation bound for the Hermite basis.** For nodes in the closed unit ball
whose distances from `a x.1` are at least `ϱ ∈ (0, 1]`, every coefficient of `hermiteBasis ha m x`
has norm at most `(ϱ ^ ((∑ i, m i) - 1 - x.2))⁻¹`. -/
theorem norm_coeff_hermiteBasis_le_inv_pow_sub {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : R[X]).coeff n‖ ≤ (ϱ ^ ((∑ i, m i) - 1 - x.2))⁻¹ := by
  simpa [inv_pow] using
    norm_coeff_hermiteBasis_mul_pow_le_of_le_norm_sub ha m x ha1 hϱ0 hϱ1 hsep n

/-- For nodes in the closed unit ball whose distances from `a x.1` are at least `ϱ ∈ (0, 1]`, every
coefficient of `hermiteBasis ha m x` has norm at most `(ϱ ^ ∑ i, m i)⁻¹`. -/
theorem norm_coeff_hermiteBasis_le {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : R[X]).coeff n‖ ≤ (ϱ ^ ∑ i, m i)⁻¹ :=
  (norm_coeff_hermiteBasis_le_inv_pow_sub ha m x ha1 hϱ0 hϱ1 hsep n).trans <|
    inv_anti₀ (pow_pos hϱ0 _) (pow_le_pow_of_le_one hϱ0.le hϱ1 (by omega))

/-- **Weighted polynomial coefficient bound from Cauchy-scaled Hasse jets.** If `f` has degree below
`∑ i, m i`, all nodes have norm at most `B` with pairwise unit differences of norm at least
`ϱ ∈ (0, B]`, and `‖(hasseDeriv k f).eval (a i)‖ * ϱ ^ k ≤ C` for all `i` and `k < m i`, then
`‖f.coeff n‖ * B ^ n ≤ C * (B / ϱ) ^ ((∑ i, m i) - 1)`. -/
theorem norm_coeff_mul_pow_le_of_norm_eval_hasseDeriv_mul_pow_le {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) {m : ι → ℕ} {f : R[X]}
    (hf : f.degree < ∑ i, m i) {B ϱ C : ℝ} (haB : ∀ i, ‖a i‖ ≤ B) (hϱ0 : 0 < ϱ) (hϱB : ϱ ≤ B)
    (hsep : ∀ i j, i ≠ j → ϱ ≤ ‖a i - a j‖) (hC0 : 0 ≤ C)
    (hjet : ∀ i, ∀ k < m i, ‖(hasseDeriv k f).eval (a i)‖ * ϱ ^ k ≤ C) (n : ℕ) :
    ‖f.coeff n‖ * B ^ n ≤ C * (B / ϱ) ^ ((∑ i, m i) - 1) := by
  have hB0 : 0 ≤ B := hϱ0.le.trans hϱB
  have hBϱ0 : 0 ≤ B / ϱ := div_nonneg hB0 hϱ0.le
  rw [← sum_eval_hasseDeriv_smul_hermiteBasis ha m hf]
  refine norm_coeff_sum_mul_pow_le univ _ hB0 (by positivity) fun x _ ↦ ?_
  have hb := norm_coeff_hermiteBasis_mul_pow_le_of_le_norm_sub ha m x haB hϱ0 hϱB
    (fun i hi ↦ hsep x.1 i hi.symm) n
  have hexp : (x.2 : ℕ) + ((∑ i, m i) - 1 - x.2) = (∑ i, m i) - 1 := by
    have hm : m x.1 ≤ ∑ i, m i := single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ x.1)
    have hx := x.2.isLt
    omega
  have hBpow : B ^ (x.2 : ℕ) = ϱ ^ (x.2 : ℕ) * (B / ϱ) ^ (x.2 : ℕ) := by
    rw [← mul_pow, mul_div_cancel₀ _ hϱ0.ne']
  refine (norm_coeff_smul_mul_pow_le _ hB0 hb).trans ?_
  calc ‖(hasseDeriv x.2 f).eval (a x.1)‖ * (B ^ (x.2 : ℕ) * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2))
      = (‖(hasseDeriv x.2 f).eval (a x.1)‖ * ϱ ^ (x.2 : ℕ)) *
          ((B / ϱ) ^ (x.2 : ℕ) * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2)) := by rw [hBpow]; ring
    _ = (‖(hasseDeriv x.2 f).eval (a x.1)‖ * ϱ ^ (x.2 : ℕ)) *
          (B / ϱ) ^ ((∑ i, m i) - 1) := by rw [← pow_add, hexp]
    _ ≤ C * (B / ϱ) ^ ((∑ i, m i) - 1) :=
        mul_le_mul_of_nonneg_right (hjet x.1 x.2 x.2.isLt) (pow_nonneg hBϱ0 _)

/-- **Ultrametric bound for Hasse-jet Hermite interpolation.** If the nodes lie in the closed unit
ball with pairwise unit differences of norm at least `ϱ ∈ (0, 1]` and all prescribed Hasse jets have
norm at most `C ≥ 0`, then every coefficient of the Hermite interpolation polynomial has norm at
most `C * (ϱ ^ ((∑ i, m i) - 1))⁻¹`. -/
theorem norm_coeff_hermiteJetEquiv_symm_le {a : ι → R}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ)
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ C : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ϱ ≤ ‖a i - a j‖) (c : ∀ i, Fin (m i) → R)
    (hC0 : 0 ≤ C) (hc : ∀ i k, ‖c i k‖ ≤ C) (n : ℕ) :
    ‖((hermiteJetEquiv ha m).symm c : R[X]).coeff n‖ ≤ C * (ϱ ^ ((∑ i, m i) - 1))⁻¹ := by
  have hjet (i : ι) (k : ℕ) (hk : k < m i) :
      ‖(hasseDeriv k ((hermiteJetEquiv ha m).symm c : R[X])).eval (a i)‖ * ϱ ^ k ≤ C := by
    rw [eval_hasseDeriv_hermiteJetEquiv_symm ha m c i ⟨k, hk⟩]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hϱ0.le hϱ1)).trans (hc i ⟨k, hk⟩)
  simpa [inv_pow] using norm_coeff_mul_pow_le_of_norm_eval_hasseDeriv_mul_pow_le ha
    (degree_hermiteJetEquiv_symm_lt ha m c) ha1 hϱ0 hϱ1 hsep hC0 hjet n

end SeminormedCommRing

section NormedField

variable {ι K : Type*} [Fintype ι] [NormedField K] [IsUltrametricDist K]

/-- **Polynomial coefficient bound from Cauchy-scaled Hasse jets.** If `f` has degree below
`∑ i, m i`, the nodes lie in the closed unit ball with pairwise distance at least `ϱ ∈ (0, 1]`, and
`‖(hasseDeriv k f).eval (a i)‖ * ϱ ^ k ≤ C` for all `i` and `k < m i`, then every coefficient of `f`
has norm at most `C * (ϱ ^ ((∑ i, m i) - 1))⁻¹`. The factor `ϱ ^ (-k)` in the `k`-th jet bound
cancels against the `ϱ ^ k` saving in `Polynomial.norm_coeff_hermiteBasis_le_inv_pow_sub`. -/
theorem norm_coeff_le_of_norm_eval_hasseDeriv_mul_pow_le {a : ι → K} {m : ι → ℕ} {f : K[X]}
    (hf : f.degree < ∑ i, m i) (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ C : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ϱ ≤ ‖a i - a j‖) (hC0 : 0 ≤ C)
    (hjet : ∀ i, ∀ k < m i, ‖(hasseDeriv k f).eval (a i)‖ * ϱ ^ k ≤ C) (n : ℕ) :
    ‖f.coeff n‖ ≤ C * (ϱ ^ ((∑ i, m i) - 1))⁻¹ := by
  have ha : Pairwise fun i j ↦ IsUnit (a i - a j) :=
    fun i j hij ↦ Ne.isUnit (norm_pos_iff.1 (hϱ0.trans_le (hsep i j hij)))
  simpa [inv_pow] using
    norm_coeff_mul_pow_le_of_norm_eval_hasseDeriv_mul_pow_le ha hf ha1 hϱ0 hϱ1 hsep hC0 hjet n

/-- **Hermite interpolation with ultrametric bounds** (Baker, Chapter 2, Lemma 7, non-archimedean
analogue). Given `ϱ`-separated points `σ : ι → K` in the closed unit ball of a characteristic-zero
ultrametric normed field, a multiplicity bound `S`, an index `r : ι`, and an order `s < S`, there
exists a polynomial `W : K[X]` whose ordinary derivatives `(derivative^[j] W).eval (σ i)` for
`j < S` form the Kronecker delta at `(r, s)` and whose coefficients satisfy
`‖W.coeff n‖ ≤ ‖((s.factorial : ℕ) : K)⁻¹‖ * (ϱ ^ (Fintype.card ι * S))⁻¹`. -/
theorem exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist {K : Type*}
    [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : ι → K)
    (hσ : ∀ i, ‖σ i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ϱ ≤ ‖σ i - σ j‖) (S : ℕ) (r : ι) {s : ℕ} (hs : s < S) :
    ∃ W : K[X], (∀ i, ∀ j < S, (derivative^[j] W).eval (σ i) = if i = r ∧ j = s then 1 else 0) ∧
      ∀ n, ‖W.coeff n‖ ≤ ‖((s.factorial : ℕ) : K)⁻¹‖ * (ϱ ^ (Fintype.card ι * S))⁻¹ := by
  have ha : Pairwise fun i j ↦ IsUnit (σ i - σ j) :=
    fun i j hij ↦ Ne.isUnit (norm_pos_iff.1 (hϱ0.trans_le (hsep i j hij)))
  have hs0 : ((s.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero s)
  let x : Σ _ : ι, Fin S := ⟨r, ⟨s, hs⟩⟩
  refine ⟨((s.factorial : ℕ) : K)⁻¹ • (hermiteBasis ha (fun _ ↦ S) x : K[X]),
    fun i j hj ↦ eval_iterate_derivative_smul_hermiteBasis ha (fun _ ↦ S) x
      (mul_inv_cancel₀ hs0) i hj, fun n ↦ ?_⟩
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simpa using norm_coeff_hermiteBasis_le ha (fun _ ↦ S) x hσ hϱ0 hϱ1
    (fun i hi ↦ hsep r i hi.symm) n

end NormedField

end Polynomial
