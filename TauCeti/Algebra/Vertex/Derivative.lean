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
import TauCeti.Data.Nat.Choose.Sum
import Mathlib.Tactic.Module

/-!
# Formal derivatives of vertex operators

The formal derivative of a field is again a field: differentiating a Laurent series lowers
its lower bound by at most one. In normalized mode indexing its coefficients are
`(∂A)[[n]] = -n • A[[n - 1]]`. This construction is linear over the coefficient ring and
requires no characteristic-zero assumption. When an endomorphism `T` kills a vector `vac` and acts
as `∂` by commutation on a field `B`, this mode formula gives the recursion
`T (B₍ₘ₎ vac) = -m • B₍ₘ₋₁₎ vac` (`VertexOperator.apply_ncoeff_apply_of_lie`), and iterating it
yields the division-free creation identity `k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)`
(`VertexOperator.factorial_smul_ncoeff_apply`).
Descending from the truncation of `B(z) vac`, the same recursion shows that the nonnegative modes
of `B` kill `vac` when `V` has unique divisibility (`VertexOperator.ncoeff_apply_of_nonneg`).

Differentiation preserves mutual locality, increasing a locality bound by one. More generally,
iterated derivatives in the two variables increase the bound by the sum of their orders.
These are the formal-calculus identities used for translation-covariant fields and reconstruction
of vertex algebras.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2.
-/

public section

noncomputable section

open Finset

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

/-- The identity field is constant: `∂ id = 0`. -/
@[simp]
theorem derivative_idField : derivative (idField : VertexOperator R V) = 0 :=
  ext_ncoeff fun n ↦ by
    rw [ncoeff_derivative, ncoeff_idField]
    split_ifs <;> simp_all

/-- **Creation recursion.** If an endomorphism `T` kills `vac` and acts as `∂` on a field `B` by
commutation, then `T (B₍ₘ₎ vac) = -m • B₍ₘ₋₁₎ vac` for every `m : ℤ`. -/
theorem apply_ncoeff_apply_of_lie {T : Module.End R V} {vac : V} (hvac : T vac = 0)
    {B : VertexOperator R V} (hT : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    T ((B[[m]]) vac) = (-m) • (B[[m - 1]]) vac := by
  have h := LinearMap.congr_fun (hT m) vac
  rwa [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hvac, map_zero,
    sub_zero, ncoeff_derivative, LinearMap.smul_apply] at h

/-- **Division-free creation recursion.** If an endomorphism `T` kills `vac` and acts as `∂` on a
field `B` by commutation, then `k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)` for every `k : ℕ`. -/
theorem factorial_smul_ncoeff_apply {T : Module.End R V} {vac : V} (hvac : T vac = 0)
    {B : VertexOperator R V} (hT : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    k.factorial • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := apply_ncoeff_apply_of_lie hvac hT (-(k : ℤ) - 1)
    have h₁ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have h₂ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [h₁, h₂, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul,
      smul_comm]

/-- **Creation from translation covariance.** If `V` has unique divisibility, an endomorphism `T`
kills `vac` and acts as `∂` on a field `B` by commutation, then every nonnegative mode of `B` kills
`vac`: `B(z) vac` has no negative powers of `z`. -/
theorem ncoeff_apply_of_nonneg [HasUniqueDiv V] {T : Module.End R V} {vac : V}
    (hvac : T vac = 0) {B : VertexOperator R V}
    (hT : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) {n : ℤ} (hn : 0 ≤ n) :
    (B[[n]]) vac = 0 := by
  -- Descend from the truncation of `B(z) vac`: `T (B₍ₖ₊₁₎ vac) = -(k + 1) • B₍ₖ₎ vac`.
  obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero vac
  suffices hd : ∀ d k : ℕ, P ≤ k + d → (B[[k]]) vac = 0 by
    simpa [hn] using hd P n.toNat (by omega)
  intro d
  induction d with
  | zero => exact fun k hk ↦ hP k (by omega)
  | succ d ih =>
    intro k hk
    have h := apply_ncoeff_apply_of_lie hvac hT ((k + 1 : ℕ) : ℤ)
    have hk' : ((k + 1 : ℕ) : ℤ) - 1 = k := by push_cast; ring
    rw [hk', ih (k + 1) (by omega), map_zero, eq_comm, neg_smul, neg_eq_zero, natCast_zsmul] at h
    exact nsmul_right_injective k.succ_ne_zero (h.trans (smul_zero _).symm)

/-- Over a `ℚ`-algebra, if `T vac = 0` and `B` is translation-covariant with respect to `T`,
then `B₍₋ₖ₋₁₎ vac = (k!)⁻¹ • Tᵏ (B₍₋₁₎ vac)`. -/
theorem ncoeff_neg_succ_apply_of_lie [Algebra ℚ R] {T : Module.End R V} {vac : V}
    (hvac : T vac = 0) {B : VertexOperator R V}
    (hT : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    (B[[-(k : ℤ) - 1]]) vac = algebraMap ℚ R (k.factorial : ℚ)⁻¹ • (T ^ k) ((B[[-1]]) vac) :=
  TauCeti.eq_inv_smul_of_nsmul k.factorial_ne_zero
    (by simpa only [natCast_zsmul, show -(k : ℤ) - 1 = -k - 1 by omega] using
      factorial_smul_ncoeff_apply hvac hT k)

/-- If `V` has unique divisibility, `T vac = 0`, and two `T`-covariant fields agree at mode `-1`
on `vac`, then all of their modes agree on `vac`. -/
theorem ncoeff_apply_eq_of_lie_of_neg_one_eq [HasUniqueDiv V] {T : Module.End R V} {vac : V}
    (hvac : T vac = 0) {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]])
    (hneg : (A[[-1]]) vac = (B[[-1]]) vac) (n : ℤ) : (A[[n]]) vac = (B[[n]]) vac := by
  rcases le_or_gt 0 n with hn | hn
  · rw [ncoeff_apply_of_nonneg hvac hA hn, ncoeff_apply_of_nonneg hvac hB hn]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    exact (nsmul_right_inj k.factorial_ne_zero).mp <| by
      simpa only [show -(k : ℤ) - 1 = (-k - 1 : ℤ) by omega,
        factorial_smul_ncoeff_apply hvac hA k, factorial_smul_ncoeff_apply hvac hB k] using
        congrArg (T ^ k) hneg

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

end IsLocalOfOrder

end VertexOperator
