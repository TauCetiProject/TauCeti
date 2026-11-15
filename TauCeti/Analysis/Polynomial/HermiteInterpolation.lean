/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Analysis.Polynomial.Ultra
public import TauCeti.LinearAlgebra.HermiteInterpolation

/-!
# Ultrametric coefficient bounds for Hermite interpolation

Over an ultrametric normed field `K`, let `a : ι → K` be nodes in the closed unit ball whose
differences from `a r` have norm at least `ϱ ∈ (0, 1]`. Although the Hermite basis polynomial
`Polynomial.hermiteBasis ha m ⟨r, s⟩` has degree below `M = ∑ i, m i` and vanishes to order `m i` at
every node `a i`, bounding its coefficients by `ϱ ^ (-M)` requires working in a local shifted
variable at radius `ϱ` rather than at radius `1`.

Specifically, `Polynomial.hermiteBasis_eq_prod_mul_pow_mul_taylor` expresses
`hermiteBasis ha m ⟨r, s⟩` as
`(∏ i ≠ r, (X - C (a i)) ^ m i) * (X - C (a r)) ^ s * taylor (-a r) h`, where `h` is the
truncation below degree `N = m r - s` of
`∏ i ≠ r, (∑ k < N, v i * (-v i) ^ k * X ^ k) ^ m i` with `v i = (a r - a i)⁻¹`. Bounding each
truncated geometric series naively at radius `1` would give a bound of `ϱ ^ (-N)` per linear
factor and lose a quadratic exponent `ϱ ^ (-N * ∑ i ≠ r, m i)`. At the Gauss radius `ϱ`, however,
`‖v i‖ * ϱ ≤ 1` makes `‖v i * (-v i) ^ k‖ * ϱ ^ k ≤ ‖v i‖` uniformly in `k`. Ultrametric
submultiplicativity of `ϱ`-weighted coefficient bounds (`Polynomial.norm_coeff_prod_mul_pow_le`)
then bounds the `d`-th coefficient of the product by `(∏ i ≠ r, ‖v i‖ ^ m i) * ϱ ^ (-d)` for
every `d`. Rescaling from `ϱ` to the node radius `B ≥ ϱ` only across the degrees `d < m r - s`
(so `d ≤ m r - 1 - s`), shifting back by `-a r` via Taylor invariance
(`Polynomial.norm_coeff_taylor_mul_pow_le`), and multiplying by the global linear factors gives
the sharp exponent `M - 1 - s ≤ M`.

In characteristic zero, passing from Hasse derivatives `hasseDeriv j` to ordinary derivatives
`derivative^[j] = j ! • hasseDeriv j` divides the `(r, s)` basis polynomial by `s!`, multiplying the
ultrametric coefficient bound by `‖((s! : ℕ) : K)⁻¹‖`
(`Polynomial.exists_iterate_derivative_eval_eq_ite_of_isUltrametricDist`).

## Main results

* `Polynomial.norm_coeff_hermiteBasis_mul_pow_le`: `B`-weighted coefficient bound for
  `hermiteBasis ha m x` over an ultrametric seminormed commutative ring in terms of explicit
  inverses of `a x.1 - a i`.
* `Polynomial.norm_coeff_hermiteBasis_mul_pow_le_of_le_norm_sub`: `B`-weighted bound
  `B ^ x.2 * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2)` over an ultrametric normed field.
* `Polynomial.norm_coeff_hermiteBasis_le_prod_mul_inv_pow`,
  `Polynomial.norm_coeff_hermiteBasis_le_inv_pow_sub`, `Polynomial.norm_coeff_hermiteBasis_le`:
  unit-ball bounds for `hermiteBasis ha m x` under local separation from `a x.1`.
* `Polynomial.norm_coeff_hermiteJetEquiv_symm_le`: coefficient bound `C * (ϱ ^ ∑ i, m i)⁻¹` for
  Hermite interpolation of Hasse jets bounded by `C`.
* `Polynomial.norm_coeff_le_of_norm_eval_hasseDeriv_mul_pow_le`: coefficient bound
  `C * (ϱ ^ ((∑ i, m i) - 1))⁻¹` for a polynomial of degree below `∑ i, m i` whose Cauchy-scaled
  Hasse jets `‖(hasseDeriv k f).eval (a i)‖ * ϱ ^ k` are bounded by `C`.
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
  set N : ℕ := m x.1 - x.2
  set q : ι → R[X] := fun i ↦ ∑ k ∈ range N, monomial k (v i * (-v i) ^ k)
  set P : R[X] := ∏ i ∈ univ.erase x.1, q i ^ m i
  -- Bound the product of truncated geometric inverses at radius `ϱ`, then rescale to `B`.
  have hP (d : ℕ) : ‖P.coeff d‖ * ϱ ^ d ≤ ∏ i ∈ univ.erase x.1, ‖v i‖ ^ m i :=
    norm_coeff_prod_mul_pow_le _ _ hϱ0.le (fun i hi k ↦ norm_coeff_pow_mul_pow_le hϱ0.le
      (norm_coeff_sum_monomial_mul_neg_pow_mul_pow_le hϱ0 (hvϱ i (mem_erase.1 hi).1) N) (m i) k) d
  have hh (d : ℕ) : ‖(∑ l ∈ range N, monomial l (P.coeff l)).coeff d‖ * B ^ d ≤
      (∏ i ∈ univ.erase x.1, ‖v i‖ ^ m i) * (B / ϱ) ^ (m x.1 - 1 - x.2) := by
    simpa [N, Nat.sub_right_comm] using norm_coeff_sum_range_monomial_mul_pow_le hϱ0 hϱB hP N d
  rw [hermiteBasis_eq_prod_mul_pow_mul_taylor ha m x hv]
  have hQ (k : ℕ) :
      ‖(∏ i ∈ univ.erase x.1, (X - C (a i)) ^ m i).coeff k‖ * B ^ k ≤
        ∏ i ∈ univ.erase x.1, B ^ m i :=
    norm_coeff_prod_mul_pow_le _ _ hB0
      (fun i _ l ↦ norm_coeff_X_sub_C_pow_mul_pow_le (haB i) (m i) l) k
  have hmain := norm_coeff_mul_mul_pow_le hB0
    (norm_coeff_mul_mul_pow_le hB0 hQ (norm_coeff_X_sub_C_pow_mul_pow_le (haB x.1) x.2))
    (norm_coeff_taylor_mul_pow_le (r := -a x.1) (by simpa using haB x.1) hh) n
  refine hmain.trans_eq ?_
  have hcombine :
      (∏ i ∈ univ.erase x.1, B ^ m i) * (∏ i ∈ univ.erase x.1, ‖v i‖ ^ m i) =
        ∏ i ∈ univ.erase x.1, (B * ‖v i‖) ^ m i := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ ↦ (mul_pow B ‖v i‖ (m i)).symm
  calc (∏ i ∈ univ.erase x.1, B ^ m i) * B ^ (x.2 : ℕ) *
        ((∏ i ∈ univ.erase x.1, ‖v i‖ ^ m i) * (B / ϱ) ^ (m x.1 - 1 - x.2))
      = ((∏ i ∈ univ.erase x.1, B ^ m i) * (∏ i ∈ univ.erase x.1, ‖v i‖ ^ m i)) *
          B ^ (x.2 : ℕ) * (B / ϱ) ^ (m x.1 - 1 - x.2) := by ring
    _ = (∏ i ∈ univ.erase x.1, (B * ‖v i‖) ^ m i) * B ^ (x.2 : ℕ) *
          (B / ϱ) ^ (m x.1 - 1 - x.2) := by rw [hcombine]

end SeminormedCommRing

section NormedField

variable {ι K : Type*} [Fintype ι] [NormedField K] [IsUltrametricDist K]

/-- Over an ultrametric normed field, if all nodes have norm at most `B`, `0 < ϱ ≤ B`, and every
other node has distance at least `ϱ` from `a x.1`, then the `B`-weighted coefficients of
`hermiteBasis ha m x` are bounded by `B ^ x.2 * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2)`. -/
theorem norm_coeff_hermiteBasis_mul_pow_le_of_le_norm_sub {a : ι → K}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    {B ϱ : ℝ} (haB : ∀ i, ‖a i‖ ≤ B) (hϱ0 : 0 < ϱ) (hϱB : ϱ ≤ B)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : K[X]).coeff n‖ * B ^ n ≤
      B ^ (x.2 : ℕ) * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2) := by
  classical
  have hB0 : 0 ≤ B := hϱ0.le.trans hϱB
  have hv (i : ι) (hi : i ≠ x.1) : (a x.1 - a i) * (a x.1 - a i)⁻¹ = 1 :=
    mul_inv_cancel₀ (norm_pos_iff.1 (hϱ0.trans_le (hsep i hi)))
  have hvϱ (i : ι) (hi : i ≠ x.1) : ‖(a x.1 - a i)⁻¹‖ ≤ ϱ⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hϱ0 (hsep i hi)
  refine (norm_coeff_hermiteBasis_mul_pow_le ha m x haB hϱ0 hϱB hv hvϱ n).trans ?_
  have hprod : ∏ i ∈ univ.erase x.1, (B * ‖(a x.1 - a i)⁻¹‖) ^ m i ≤
      (B / ϱ) ^ (∑ i ∈ univ.erase x.1, m i) := by
    rw [← prod_pow_eq_pow_sum]
    gcongr with i hi
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (hvϱ i (mem_erase.1 hi).1) hB0
  have hsum : (∑ i ∈ univ.erase x.1, m i) + (m x.1 - 1 - x.2) = (∑ i, m i) - 1 - x.2 := by
    have herase := sum_erase_add univ m (mem_univ x.1)
    have hx := x.2.isLt
    omega
  calc (∏ i ∈ univ.erase x.1, (B * ‖(a x.1 - a i)⁻¹‖) ^ m i) * B ^ (x.2 : ℕ) *
        (B / ϱ) ^ (m x.1 - 1 - x.2)
      ≤ (B / ϱ) ^ (∑ i ∈ univ.erase x.1, m i) * B ^ (x.2 : ℕ) *
          (B / ϱ) ^ (m x.1 - 1 - x.2) := by gcongr
    _ = B ^ (x.2 : ℕ) *
          ((B / ϱ) ^ (∑ i ∈ univ.erase x.1, m i) * (B / ϱ) ^ (m x.1 - 1 - x.2)) := by ring
    _ = B ^ (x.2 : ℕ) * (B / ϱ) ^ ((∑ i, m i) - 1 - x.2) := by rw [← pow_add, hsum]

/-- **Product-refined unit-ball bound for the Hermite basis.** For nodes in the closed unit ball
whose distances from `a x.1` are at least `ϱ ∈ (0, 1]`, every coefficient of `hermiteBasis ha m x`
has norm at most `(∏ i ≠ x.1, ‖a x.1 - a i‖ ^ m i)⁻¹ * (ϱ ^ (m x.1 - 1 - x.2))⁻¹`. -/
theorem norm_coeff_hermiteBasis_le_prod_mul_inv_pow [DecidableEq ι] {a : ι → K}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : K[X]).coeff n‖ ≤
      (∏ i ∈ univ.erase x.1, ‖a x.1 - a i‖ ^ m i)⁻¹ * (ϱ ^ (m x.1 - 1 - x.2))⁻¹ := by
  have hv (i : ι) (hi : i ≠ x.1) : (a x.1 - a i) * (a x.1 - a i)⁻¹ = 1 :=
    mul_inv_cancel₀ (norm_pos_iff.1 (hϱ0.trans_le (hsep i hi)))
  have hvϱ (i : ι) (hi : i ≠ x.1) : ‖(a x.1 - a i)⁻¹‖ ≤ ϱ⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hϱ0 (hsep i hi)
  have h := norm_coeff_hermiteBasis_mul_pow_le ha m x ha1 hϱ0 hϱ1 hv hvϱ n
  simpa [inv_pow, prod_inv_distrib] using h

/-- **Sharp uniform-separation bound for the Hermite basis.** For nodes in the closed unit ball
whose distances from `a x.1` are at least `ϱ ∈ (0, 1]`, every coefficient of `hermiteBasis ha m x`
has norm at most `(ϱ ^ ((∑ i, m i) - 1 - x.2))⁻¹`. -/
theorem norm_coeff_hermiteBasis_le_inv_pow_sub {a : ι → K}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : K[X]).coeff n‖ ≤ (ϱ ^ ((∑ i, m i) - 1 - x.2))⁻¹ := by
  simpa [inv_pow] using
    norm_coeff_hermiteBasis_mul_pow_le_of_le_norm_sub ha m x ha1 hϱ0 hϱ1 hsep n

/-- For nodes in the closed unit ball whose distances from `a x.1` are at least `ϱ ∈ (0, 1]`, every
coefficient of `hermiteBasis ha m x` has norm at most `(ϱ ^ ∑ i, m i)⁻¹`. -/
theorem norm_coeff_hermiteBasis_le {a : ι → K}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ) (x : Σ i, Fin (m i))
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i, i ≠ x.1 → ϱ ≤ ‖a x.1 - a i‖) (n : ℕ) :
    ‖(hermiteBasis ha m x : K[X]).coeff n‖ ≤ (ϱ ^ ∑ i, m i)⁻¹ :=
  (norm_coeff_hermiteBasis_le_inv_pow_sub ha m x ha1 hϱ0 hϱ1 hsep n).trans <|
    inv_anti₀ (pow_pos hϱ0 _) (pow_le_pow_of_le_one hϱ0.le hϱ1 (by omega))

/-- **Ultrametric bound for Hasse-jet Hermite interpolation.** If the nodes lie in the closed unit
ball with pairwise distance at least `ϱ ∈ (0, 1]` and all prescribed Hasse jets have norm at most
`C ≥ 0`, then every coefficient of the Hermite interpolation polynomial has norm at most
`C * (ϱ ^ ∑ i, m i)⁻¹`. -/
theorem norm_coeff_hermiteJetEquiv_symm_le {a : ι → K}
    (ha : Pairwise fun i j ↦ IsUnit (a i - a j)) (m : ι → ℕ)
    (ha1 : ∀ i, ‖a i‖ ≤ 1) {ϱ C : ℝ} (hϱ0 : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ϱ ≤ ‖a i - a j‖) (c : ∀ i, Fin (m i) → K)
    (hC0 : 0 ≤ C) (hc : ∀ i k, ‖c i k‖ ≤ C) (n : ℕ) :
    ‖((hermiteJetEquiv ha m).symm c : K[X]).coeff n‖ ≤ C * (ϱ ^ ∑ i, m i)⁻¹ := by
  rw [← sum_eval_hasseDeriv_smul_hermiteBasis ha m (degree_hermiteJetEquiv_symm_lt ha m c),
    finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ ↦ ?_
  rw [eval_hasseDeriv_hermiteJetEquiv_symm, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul,
    norm_mul]
  exact mul_le_mul (hc x.1 x.2)
    (norm_coeff_hermiteBasis_le ha m x ha1 hϱ0 hϱ1 (fun i hi ↦ hsep x.1 i hi.symm) n)
    (norm_nonneg _) hC0

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
  rw [← sum_eval_hasseDeriv_smul_hermiteBasis ha m hf, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, norm_mul]
  have hjetx : ‖(hasseDeriv x.2 f).eval (a x.1)‖ ≤ C * (ϱ ^ (x.2 : ℕ))⁻¹ :=
    (le_div_iff₀ (pow_pos hϱ0 _)).2 (hjet x.1 x.2 x.2.isLt)
  have hb := norm_coeff_hermiteBasis_le_inv_pow_sub ha m x ha1 hϱ0 hϱ1
    (fun i hi ↦ hsep x.1 i hi.symm) n
  have hexp : (x.2 : ℕ) + ((∑ i, m i) - 1 - x.2) = (∑ i, m i) - 1 := by
    have hm : m x.1 ≤ ∑ i, m i := single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ x.1)
    have hx := x.2.isLt
    omega
  calc ‖(hasseDeriv x.2 f).eval (a x.1)‖ * ‖(hermiteBasis ha m x : K[X]).coeff n‖
      ≤ C * (ϱ ^ (x.2 : ℕ))⁻¹ * (ϱ ^ ((∑ i, m i) - 1 - x.2))⁻¹ :=
        mul_le_mul hjetx hb (norm_nonneg _) (by positivity)
    _ = C * (ϱ ^ ((x.2 : ℕ) + ((∑ i, m i) - 1 - x.2)))⁻¹ := by rw [pow_add, mul_inv, mul_assoc]
    _ = C * (ϱ ^ ((∑ i, m i) - 1))⁻¹ := by rw [hexp]

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
