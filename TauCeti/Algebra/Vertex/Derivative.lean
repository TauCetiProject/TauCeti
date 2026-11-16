/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.VertexOperator
public import TauCeti.RingTheory.LaurentSeries.HahnModuleDerivative
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Algebra.Module.Rat
import TauCeti.Algebra.Vertex.FormalDistribution
import TauCeti.Data.Nat.Choose.Sum
import Mathlib.Tactic.Module

/-!
# Formal and Hasse derivatives of vertex operators

The formal derivative `VertexOperator.derivative` satisfies `(∂A)[[n]] = -n • A[[n - 1]]`.
Transporting Mathlib's `LaurentSeries.hasseDeriv` defines the `k`-th Hasse derivative
`VertexOperator.hasseDeriv k`, with modes `(∂^{(k)} A)[[n]] = (-1)ᵏ (n choose k) • A[[n - k]]`,
satisfying `k! • ∂^{(k)} A = ∂ᵏ A` and `∂^{(k)} (∂^{(l)} A) = ((k + l) choose k) • ∂^{(k + l)} A`
over any commutative ring. Both derivatives preserve mutual locality and translation covariance;
under `HasUniqueDiv V`, nonnegative modes of a translation-covariant field annihilate `ker T`.

## Main definitions and results

* `VertexOperator.derivative`, `VertexOperator.hasseDeriv`: formal and `k`-th Hasse derivatives.
* `VertexOperator.ncoeff_derivative`, `ncoeff_hasseDeriv`, `hasseDeriv_comp`,
  `factorial_smul_hasseDeriv`: normalized mode, composition, and factorial scaling formulas.
* `VertexOperator.IsLocalOfOrder.derivative_left`, `hasseDeriv_left`: locality bounds.
* `VertexOperator.lie_ncoeff_hasseDeriv`, `ncoeff_apply_eq_zero_of_lie_of_nonneg`,
  `factorial_smul_ncoeff_neg_succ_apply_of_lie`: translation covariance and action on `ker T`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2.
-/

public section

noncomputable section

open Finset TauCeti

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Formal differentiation of fields, defined on Laurent coefficients by
`(∂A).coeff n = (n + 1) • A.coeff (n + 1)`. -/
def derivative : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R (HahnModule.derivative R)

/-- Applying the derivative of a field differentiates its value as a Laurent series. -/
@[simp]
theorem derivative_apply (A : VertexOperator R V) (v : V) :
    derivative A v = HahnModule.derivative R (A v) := (rfl)

-- As with Mathlib's coefficient API, this is not a simp lemma: the simp normal form
-- uses normalized coefficients instead.
/-- Differentiation shifts the unnormalized Laurent coefficients down by one. -/
theorem coeff_derivative (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (derivative A) n = (n + 1) • HVertexOperator.coeff A (n + 1) := by
  ext v
  simpa only [derivative, LinearMap.compRight_apply, LinearMap.comp_apply,
    HVertexOperator.coeff_apply_apply, LinearMap.smul_apply] using
    HahnModule.coeff_derivative (A v) n

/-- The normalized modes of the derivative are `(∂A)₍ₙ₎ = -n A₍ₙ₋₁₎`. -/
@[simp]
theorem ncoeff_derivative (A : VertexOperator R V) (n : ℤ) :
    (derivative A)[[n]] = (-n) • A[[n - 1]] := by
  simp only [ncoeff_apply, coeff_derivative]
  have h₁ : -n - 1 + 1 = -n := by omega
  have h₂ : -(n - 1) - 1 = -n := by omega
  rw [h₁, h₂]

/-- The formal derivative of the identity field is zero. -/
@[simp]
theorem derivative_id : derivative (VertexOperator.id R V) = 0 := by
  ext v
  simp

/-! ### Hasse derivatives of vertex operators -/

/-- The `k`-th Hasse (divided-power) derivative `∂_z^{(k)}` of a vertex operator, obtained by
transporting Mathlib's `LaurentSeries.hasseDeriv`. Its normalized modes are
`(∂_z^{(k)} A)₍ₙ₎ = (-1)ᵏ (n choose k) • A₍ₙ₋ₖ₎`. -/
def hasseDeriv (k : ℕ) : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R ((HahnModule.ofLinearEquiv R).toLinearMap ∘ₗ
    LaurentSeries.hasseDeriv R k ∘ₗ (HahnModule.ofLinearEquiv R).symm.toLinearMap)

/-- Applying the `k`-th Hasse derivative applies `LaurentSeries.hasseDeriv` to Laurent values. -/
@[simp] theorem hasseDeriv_apply (k : ℕ) (A : VertexOperator R V) (v : V) :
    hasseDeriv k A v =
      HahnModule.of R (LaurentSeries.hasseDeriv R k ((HahnModule.of R).symm (A v))) := by
  simp [hasseDeriv]

/-- The normalized modes of the `k`-th Hasse derivative are `(-1)ᵏ (n choose k) • A₍ₙ₋ₖ₎`. -/
@[simp] theorem ncoeff_hasseDeriv (k : ℕ) (A : VertexOperator R V) (n : ℤ) :
    (hasseDeriv k A)[[n]] = ((-1 : ℤ) ^ k * Ring.choose n k) • A[[n - k]] := by
  ext v
  simp only [ncoeff_apply, HVertexOperator.coeff_apply_apply, hasseDeriv_apply,
    Equiv.symm_apply_apply, LaurentSeries.hasseDeriv_coeff, LinearMap.smul_apply]
  rw [show -n - 1 + (k : ℤ) = -(n + 1 - k) by omega, Ring.choose_neg,
    show n + 1 - (k : ℤ) + k - 1 = n by omega, Units.smul_def, Int.coe_negOnePow_natCast,
    zsmul_eq_mul, Int.cast_id, show -(n + 1 - (k : ℤ)) = -(n - k) - 1 by omega]

/-- The `0`-th Hasse derivative is the identity. -/
@[simp] theorem hasseDeriv_zero (A : VertexOperator R V) : hasseDeriv 0 A = A :=
  LinearMap.ext fun v ↦ by simp [LaurentSeries.hasseDeriv_zero]

/-- The `1`-st Hasse derivative is the formal derivative. -/
@[simp] theorem hasseDeriv_one (A : VertexOperator R V) : hasseDeriv 1 A = derivative A :=
  LinearMap.ext fun v ↦ by
    rw [hasseDeriv_apply, derivative_apply, ← LaurentSeries.derivative_apply,
      ← HahnModule.derivative_of, Equiv.apply_symm_apply]

/-- The `(-1)`-st mode of `∂_z^{(k)} A` is `A₍₋ₖ₋₁₎`. -/
theorem ncoeff_neg_one_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    (hasseDeriv k A)[[-1]] = A[[-(k : ℤ) - 1]] := by
  ext v
  simp only [ncoeff_apply, HVertexOperator.coeff_apply_apply, hasseDeriv_apply,
    Equiv.symm_apply_apply, LaurentSeries.hasseDeriv_coeff, neg_neg, sub_self, zero_add,
    Ring.choose_natCast, Nat.choose_self, Nat.cast_one, one_smul]
  congr 2; omega

/-- Every positive Hasse derivative of the identity field is zero. -/
@[simp] theorem hasseDeriv_succ_id (k : ℕ) : hasseDeriv (k + 1) (VertexOperator.id R V) = 0 :=
  LinearMap.ext fun v ↦ by simp [LaurentSeries.hasseDeriv_single, Ring.choose_zero_succ]

/-- Composition of Hasse derivatives:
`∂_z^{(k)} (∂_z^{(l)} A) = ((k + l) choose k) • ∂_z^{(k + l)} A`. -/
@[simp] theorem hasseDeriv_comp (k l : ℕ) (A : VertexOperator R V) :
    hasseDeriv k (hasseDeriv l A) = (k + l).choose k • hasseDeriv (k + l) A :=
  LinearMap.ext fun v ↦ by
    rw [hasseDeriv_apply, hasseDeriv_apply, Equiv.symm_apply_apply, LaurentSeries.hasseDeriv_comp,
      LinearMap.smul_apply, hasseDeriv_apply]
    simpa only [HahnModule.ofLinearEquiv_apply] using
      map_nsmul (HahnModule.ofLinearEquiv R (Γ := ℤ) (V := V)) ((k + l).choose k) _

/-- Differentiating the `k`-th Hasse derivative gives `(k + 1)` times the `(k + 1)`-st. -/
theorem derivative_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDeriv k A) = (k + 1) • hasseDeriv (k + 1) A := by
  rw [← hasseDeriv_one, hasseDeriv_comp, Nat.add_comm 1 k, Nat.choose_one_right]

/-- Taking the `k`-th Hasse derivative of `∂A` also gives `(k + 1)` times the `(k + 1)`-st. -/
theorem hasseDeriv_derivative (k : ℕ) (A : VertexOperator R V) :
    hasseDeriv k (derivative A) = (k + 1) • hasseDeriv (k + 1) A := by
  rw [← hasseDeriv_one, hasseDeriv_comp, Nat.choose_succ_self_right]

/-- Formal differentiation commutes with every Hasse derivative. -/
theorem derivative_hasseDeriv_comm (k : ℕ) (A : VertexOperator R V) :
    derivative (hasseDeriv k A) = hasseDeriv k (derivative A) := by
  rw [derivative_hasseDeriv, hasseDeriv_derivative]

/-- Multiplying the `k`-th Hasse derivative by `k!` recovers the `k`-th iterated derivative,
without any division assumption on `R`. -/
theorem factorial_smul_hasseDeriv (k : ℕ) (A : VertexOperator R V) :
    k.factorial • hasseDeriv k A = (derivative^[k]) A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, map_nsmul, derivative_hasseDeriv, Nat.factorial_succ,
      mul_nsmul, smul_comm]

/-- Over a `ℚ`-algebra, the `k`-th Hasse derivative is `(k!)⁻¹ • ∂_zᵏ A`. -/
theorem hasseDeriv_eq_smul_iterate_derivative [Algebra ℚ R] (k : ℕ) (A : VertexOperator R V) :
    hasseDeriv k A = algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (derivative^[k]) A :=
  TauCeti.eq_inv_smul_of_nsmul k.factorial_ne_zero (factorial_smul_hasseDeriv k A)

namespace IsLocalOfOrder

variable {A B : VertexOperator R V} {N : ℕ}

/-- Differentiating the first field increases a locality bound by one. -/
theorem derivative_left (h : A.IsLocalOfOrder B N) :
    (derivative A).IsLocalOfOrder B (N + 1) := by
  rw [isLocalOfOrder_iff]
  intro m n
  -- The derivative sum is -m times the shifted order-(N+1) sum, minus the
  -- binomially weighted sum. The latter is (N+1) times the order-N sum.
  have hweighted : ∑ ij ∈ antidiagonal (N + 1), (N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
      (ij.1 : ℤ) • (A[[m + ij.1 - 1]] * B[[n + ij.2]] -
        B[[n + ij.2]] * A[[m + ij.1 - 1]]) = 0 := by
    simp_rw [natCast_zsmul, smul_comm ((-1 : ℤ) ^ _) (_ : ℕ)]
    rw [sum_antidiagonal_choose_succ_nsmul_nsmul (fun i j ↦ (-1 : ℤ) ^ j •
      (A[[m + i - 1]] * B[[n + j]] - B[[n + j]] * A[[m + i - 1]])) N]
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc, add_sub_cancel_right, smul_zero] using
      congrArg (fun x ↦ (N + 1) • x) (isLocalOfOrder_iff.mp h m n)
  have e : ∀ ij ∈ antidiagonal (N + 1),
      (N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[m + ij.1]] * B[[n + ij.2]] -
          B[[n + ij.2]] * (derivative A)[[m + ij.1]]) =
      (-m) • ((N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(m - 1) + ij.1]] * B[[n + ij.2]] -
          B[[n + ij.2]] * A[[(m - 1) + ij.1]])) -
      (N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • (ij.1 : ℤ) •
        (A[[m + ij.1 - 1]] * B[[n + ij.2]] -
          B[[n + ij.2]] * A[[m + ij.1 - 1]]) := by
    intro ij _
    have hi : m - 1 + ↑ij.1 = m + ↑ij.1 - 1 := by omega
    rw [ncoeff_derivative, hi]
    simp only [smul_mul_assoc, mul_smul_comm]
    module
  rw [sum_congr rfl e, sum_sub_distrib, ← smul_sum,
    isLocalOfOrder_iff.mp h.succ (m - 1) n, hweighted, smul_zero, sub_zero]

/-- Differentiating the second field increases a locality bound by one. -/
theorem derivative_right (h : A.IsLocalOfOrder B N) :
    A.IsLocalOfOrder (derivative B) (N + 1) :=
  h.symm.derivative_left.symm

/-- Iterated differentiation in the first variable preserves locality. -/
theorem iterate_derivative_left (h : A.IsLocalOfOrder B N) (k : ℕ) :
    ((derivative (R := R) (V := V))^[k] A).IsLocalOfOrder B (N + k) := by
  induction k with
  | zero => simpa using h
  | succ k ih => simpa [Function.iterate_succ_apply', Nat.add_assoc] using ih.derivative_left

/-- Derivatives of orders `k` and `l` of local fields are local of order at most `N + k + l`. -/
theorem iterate_derivative (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    ((derivative (R := R) (V := V))^[k] A).IsLocalOfOrder
      ((derivative (R := R) (V := V))^[l] B) (N + k + l) := by
  exact ((h.iterate_derivative_left k).symm.iterate_derivative_left l).symm

/-- Taking the `k`-th Hasse derivative in the first variable increases a locality bound by `k`,
over any commutative ring. -/
theorem hasseDeriv_left (h : A.IsLocalOfOrder B N) (k : ℕ) :
    (hasseDeriv k A).IsLocalOfOrder B (N + k) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  have hexp : (hasseDeriv k A).commutatorDistribution B = ∑ j ∈ range N,
      FormalDistribution.deltaTerm (k + j) (fun r ↦ ((-1 : ℤ) ^ k * ((k + j).choose k : ℤ)) •
        FormalDistribution.residue ((FormalDistribution.mulSub ^ j)
          (A.commutatorDistribution B)) r) := funext fun m ↦ funext fun n ↦ by
    have hsum := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm (m - k)) n
    simp only [Finset.sum_apply, FormalDistribution.deltaTerm_apply] at hsum ⊢
    rw [commutatorDistribution_apply, ncoeff_hasseDeriv, smul_mul_assoc, mul_smul_comm,
      ← smul_sub, ← commutatorDistribution_apply, hsum, smul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    have hc := Ring.choose_smul_choose m (Nat.le_add_right k j)
    rw [Nat.add_sub_cancel_left, nsmul_eq_mul] at hc
    rw [smul_smul, smul_smul, show m - (k : ℤ) + n - j = m + n - ↑(k + j) by omega]
    congr 1; linear_combination (-1 : ℤ) ^ k * hc.symm
  rw [hexp, map_sum]
  exact sum_eq_zero fun j hj ↦
    FormalDistribution.mulSub_pow_deltaTerm_eq_zero (by have := mem_range.mp hj; omega) _

/-- Taking the `k`-th Hasse derivative in the second variable increases a locality bound by `k`. -/
theorem hasseDeriv_right (h : A.IsLocalOfOrder B N) (k : ℕ) :
    A.IsLocalOfOrder (hasseDeriv k B) (N + k) := (h.symm.hasseDeriv_left k).symm

/-- Hasse derivatives of orders `k` and `l` of local fields are local of order `N + k + l`. -/
theorem hasseDeriv (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    (hasseDeriv k A).IsLocalOfOrder (hasseDeriv l B) (N + k + l) :=
  (h.hasseDeriv_left k).hasseDeriv_right l

end IsLocalOfOrder

/-! ### Translation covariance and Hasse derivatives -/

section TranslationCovariance

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Hasse derivatives preserve translation covariance. -/
theorem lie_ncoeff_hasseDeriv {T : Module.End R V} {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, (hasseDeriv k A)[[m]]⁆ = (derivative (hasseDeriv k A))[[m]] := by
  rw [ncoeff_hasseDeriv, derivative_hasseDeriv_comm, ncoeff_hasseDeriv, lie_zsmul, hA]

/-- If `vac` is annihilated by nonnegative modes of `A`, it is also annihilated by nonnegative
modes of every Hasse derivative of `A`. -/
theorem ncoeff_hasseDeriv_apply_eq_zero_of_nonneg {A : VertexOperator R V} {vac : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) vac = 0) (k : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    ((hasseDeriv k A)[[m]]) vac = 0 := by
  rw [ncoeff_hasseDeriv, LinearMap.smul_apply]
  rcases lt_or_ge m k with hlt | hge
  · lift m to ℕ using hm; simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (Int.ofNat_lt.mp hlt)]
  · rw [hA (m - k) (by omega), smul_zero]

/-- If `T vac = 0` and `B` is translation-covariant with respect to `T`, then
`T (B₍ₘ₎ vac) = -m B₍ₘ₋₁₎ vac` for every integer `m`. -/
theorem apply_ncoeff_apply_of_lie {T : Module.End R V} {vac : V} {B : VertexOperator R V}
    (hT : T vac = 0) (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    T ((B[[m]]) vac) = (-m) • (B[[m - 1]]) vac := by
  simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, hT, map_zero, sub_zero,
    ncoeff_derivative, LinearMap.smul_apply] using LinearMap.congr_fun (hcov m) vac

/-- If `T vac = 0` and `B` is translation-covariant with respect to `T`, then
`k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)` without any division hypothesis on `R`. -/
theorem factorial_smul_ncoeff_neg_succ_apply_of_lie {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    k.factorial • (B[[-(k : ℤ) - 1]]) vac = (T ^ k) ((B[[-1]]) vac) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := apply_ncoeff_apply_of_lie hT hcov (-(k : ℤ) - 1)
    rw [show -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) by omega,
      show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by omega, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul, smul_comm]

/-- If `V` has unique division by positive integers, `T vac = 0`, and `B` is translation-covariant
with respect to `T`, then all nonnegative modes of `B` annihilate `vac`. -/
theorem ncoeff_apply_eq_zero_of_lie_of_nonneg [HasUniqueDiv V] {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) {m : ℤ} (hm : 0 ≤ m) :
    (B[[m]]) vac = 0 := by
  lift m to ℕ using hm
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero vac
  suffices ∀ d k : ℕ, N - d ≤ k → (B[[(k : ℤ)]]) vac = 0 from this N m (by omega)
  intro d; induction d with
  | zero => exact fun k hk ↦ hN k (by exact_mod_cast hk)
  | succ d ih =>
    intro k hk; have hrec := apply_ncoeff_apply_of_lie hT hcov ((k + 1 : ℕ) : ℤ)
    rw [ih (k + 1) (by omega), map_zero, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega,
      neg_smul, eq_comm, neg_eq_zero, natCast_zsmul] at hrec
    exact nsmul_right_injective (Nat.succ_ne_zero k) (by simpa only [smul_zero] using hrec)

/-- Over a `ℚ`-algebra, if `T vac = 0` and `B` is translation-covariant with respect to `T`,
then `B₍₋ₖ₋₁₎ vac = (k!)⁻¹ • Tᵏ (B₍₋₁₎ vac)`. -/
theorem ncoeff_neg_succ_apply_of_lie [Algebra ℚ R] {T : Module.End R V} {vac : V}
    {B : VertexOperator R V} (hT : T vac = 0)
    (hcov : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    (B[[-(k : ℤ) - 1]]) vac = algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (T ^ k) ((B[[-1]]) vac) :=
  TauCeti.eq_inv_smul_of_nsmul k.factorial_ne_zero
    (factorial_smul_ncoeff_neg_succ_apply_of_lie hT hcov k)

end TranslationCovariance

end VertexOperator
