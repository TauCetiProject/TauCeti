/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.WittVector.Isocrystal
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.LinearAlgebra.Charpoly.Semilinear
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# Nilpotence of monodromy

Let `R` be a commutative ring with an automorphism `σ`, and let `V` be a finite free `R`-module
with a bijective `σ`-semilinear Frobenius `φ`. A *monodromy operator* is an `R`-linear
endomorphism `N` of `V` satisfying the Frobenius–monodromy relation `N φ = c φ N` for a fixed
scalar `c`. For `(φ, N)`-modules over the fraction field `K₀ = W(k)[1/p]` of the Witt vectors of a
perfect field `k`, such as the Hyodo–Kato cohomology of a semistable degeneration, `σ` is the
Witt vector Frobenius and `c = p`.

If `σ` preserves a valuation `v` with `v c ≠ 1`, the relation forces `N ^ dim V = 0`. The
general statements only ask that the equation `σ(a) c ^ k = a` with `k ≥ 1` have no solution
`a ≠ 0`; over `K₀` with `c = p` this holds without choosing a valuation. The coefficients of the
reversed characteristic polynomial of `N` satisfy this equation, because `φ` conjugates `N` to a
scalar multiple of itself.

Neither the bijectivity of `φ` nor the finiteness of `V` can be dropped: for `φ = 0` every `N`
satisfies the relation, and on the `ℚ_p`-vector space with basis `(e_i)_(i ∈ ℤ)` the shift
`φ (e_i) = e_(i+1)` and `N (e_i) = p ^ i e_(i-1)` satisfy `N φ = p φ N`, while `N` is not
nilpotent.

## Main results

* `TauCeti.charpoly_eq_X_pow_finrank_of_frobenius_monodromy`,
  `TauCeti.pow_finrank_eq_zero_of_frobenius_monodromy`: if `N φ = c φ N` and `σ(a) c ^ k = a`
  with `k ≥ 1` forces `a = 0`, then `N.charpoly = X ^ dim V` and `N ^ dim V = 0`.
* `TauCeti.pow_finrank_eq_zero_of_frobenius_monodromy_of_valuation`: the same conclusion over a
  field when `σ` preserves a valuation `v` with `v c ≠ 1`.
* `TauCeti.eq_zero_of_frobenius_mul_p_pow_eq`: in the fraction field of the Witt vectors of a
  perfect domain `k`, `φ(a) p ^ n = a` with `n ≥ 1` forces `a = 0`.
* `TauCeti.pow_finrank_eq_zero_of_isocrystal_monodromy`: on a finite-dimensional isocrystal over
  the fraction field `K(p, k)` of `W(k)` in the sense of Mathlib's `WittVector.Isocrystal`, every
  linear `N` with `N Φ = p Φ N` satisfies `N ^ dim V = 0`.

## References

* O. Hyodo and K. Kato, *Semi-stable reduction and crystalline cohomology with logarithmic poles*,
  Astérisque 223 (1994), 221–268, §3.2 and §3.4.
-/

public section

open Module Polynomial

namespace TauCeti

section General

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V] {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {φ : V ≃ₛₗ[σ] V} {N : Module.End R V} {c : R}

/-- Under the Frobenius–monodromy relation `N φ = c φ N`, the coefficient `a_k` of `X ^ k` in the
reversed characteristic polynomial of `N` satisfies `σ(a_k) c ^ k = a_k`. -/
private theorem map_coeff_reverse_charpoly_mul_pow (hN : ∀ x, N (φ x) = c • φ (N x)) (k : ℕ) :
    σ (N.charpoly.reverse.coeff k) * c ^ k = N.charpoly.reverse.coeff k := by
  -- `φ` conjugates `σ⁻¹(c) • N` to `N`.
  have hsemi : Function.Semiconj φ ⇑(σ' c • N) N := fun x ↦ by
    rw [LinearMap.coe_smul, Pi.smul_apply, map_smulₛₗ, RingHomInvPair.comp_apply_eq₂, hN]
  have hunit : IsUnit ((σ' c • N).charpoly.leadingCoeff) := by
    rw [(LinearMap.charpoly_monic _).leadingCoeff]
    exact isUnit_one
  calc σ (N.charpoly.reverse.coeff k) * c ^ k
      = ((σ' c • N).charpoly.map σ).reverse.coeff k := by
        rw [reverse_map_of_isUnit_leadingCoeff hunit, coeff_map, LinearMap.reverse_charpoly_smul,
          comp_C_mul_X_coeff, map_mul, map_pow, RingHomInvPair.comp_apply_eq₂]
    _ = N.charpoly.reverse.coeff k := by
        rw [← φ.charpoly_eq_map_charpoly_of_semiconj hsemi]

/-- **Nilpotence of monodromy**, characteristic polynomial form. Let `φ` be a `σ`-semilinear
automorphism of a finite free module `V` and `N` an endomorphism with `N φ = c φ N`. If the only
solution of `σ(a) c ^ k = a` with `k ≥ 1` is `a = 0`, then the characteristic polynomial of `N`
is `X ^ dim V`. -/
theorem charpoly_eq_X_pow_finrank_of_frobenius_monodromy (hN : ∀ x, N (φ x) = c • φ (N x))
    (hc : ∀ a : R, ∀ k : ℕ, k ≠ 0 → σ a * c ^ k = a → a = 0) :
    N.charpoly = X ^ finrank R V := by
  nontriviality R
  have hrev (k : ℕ) (hk : k ≠ 0) : N.charpoly.reverse.coeff k = 0 :=
    hc _ k hk (map_coeff_reverse_charpoly_mul_pow hN k)
  ext j
  rw [coeff_X_pow]
  rcases lt_trichotomy j (finrank R V) with hj | rfl | hj
  · -- Below the degree, the coefficient of `X ^ j` is that of `X ^ (dim V - j)` in the reversal.
    rw [ite_eq_right hj.ne, ← hrev (finrank R V - j) (by omega), coeff_reverse,
      LinearMap.charpoly_natDegree, revAt_le (by omega), Nat.sub_sub_self hj.le]
  · rw [ite_eq_left rfl, ← LinearMap.charpoly_natDegree]
    exact (LinearMap.charpoly_monic N).coeff_natDegree
  · rw [ite_eq_right hj.ne', coeff_eq_zero_of_natDegree_lt (by rwa [LinearMap.charpoly_natDegree])]

/-- **Nilpotence of monodromy**. Let `φ` be a `σ`-semilinear automorphism of a finite free
module `V` and `N` an endomorphism with `N φ = c φ N`. If the only solution of `σ(a) c ^ k = a`
with `k ≥ 1` is `a = 0`, then `N ^ dim V = 0`. -/
theorem pow_finrank_eq_zero_of_frobenius_monodromy (hN : ∀ x, N (φ x) = c • φ (N x))
    (hc : ∀ a : R, ∀ k : ℕ, k ≠ 0 → σ a * c ^ k = a → a = 0) :
    N ^ finrank R V = 0 := by
  simpa [charpoly_eq_X_pow_finrank_of_frobenius_monodromy hN hc] using N.aeval_self_charpoly

end General

section Valuation

variable {L V Γ₀ : Type*} [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
  [LinearOrderedCommGroupWithZero Γ₀] {σ σ' : L →+* L} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] {φ : V ≃ₛₗ[σ] V} {N : Module.End L V} {c : L}

/-- **Nilpotence of monodromy** over a valued field. Let `σ` be an automorphism of a field `L`
preserving a valuation `v`, let `φ` be a `σ`-semilinear automorphism of a finite-dimensional
`L`-vector space `V`, and let `N` be an endomorphism with `N φ = c φ N`, where `v c ≠ 1`. Then
`N ^ dim V = 0`. -/
theorem pow_finrank_eq_zero_of_frobenius_monodromy_of_valuation {v : Valuation L Γ₀}
    (hv : ∀ x, v (σ x) = v x) (hvc : v c ≠ 1) (hN : ∀ x, N (φ x) = c • φ (N x)) :
    N ^ finrank L V = 0 :=
  pow_finrank_eq_zero_of_frobenius_monodromy hN fun a k hk ha ↦ by
    by_contra ha0
    have hva := congrArg v ha
    rw [map_mul, map_pow, hv] at hva
    have hpow : v c ^ k = 1 :=
      mul_left_cancel₀ ((map_ne_zero v).2 ha0) (hva.trans (mul_one _).symm)
    exact hvc (pow_eq_one_iff.1 hpow |>.resolve_right hk)

end Valuation

section Witt

open WittVector
open scoped Isocrystal

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [IsDomain k] [CharP k p]
  [PerfectRing k p]

/-- In the fraction field `K(p, k)` of the Witt vectors `W(k)` of a perfect domain `k` of
characteristic `p` (which is `W(k)[1/p]` when `k` is a field), the equation `φ(a) p ^ n = a` with
`n ≥ 1` only has the solution `a = 0`. -/
theorem eq_zero_of_frobenius_mul_p_pow_eq {a : K(p, k)} {n : ℕ} (hn : n ≠ 0)
    (ha : φ(p, k) a * (p : K(p, k)) ^ n = a) : a = 0 := by
  by_contra ha0
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := WittVector p k) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha0
  have hinj := IsFractionRing.injective (WittVector p k) K(p, k)
  have hσ (z : WittVector p k) : φ(p, k) (algebraMap (WittVector p k) K(p, k) z) =
      algebraMap (WittVector p k) K(p, k) (frobenius z) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (frobeniusEquiv p k) z
  have hAy : algebraMap (WittVector p k) K(p, k) y ≠ 0 := by simpa using hinj.ne hy0
  have hAFy : algebraMap (WittVector p k) K(p, k) (frobenius y) ≠ 0 := by
    have : frobenius y ≠ 0 := by simpa using (frobenius_bijective p k).injective.ne hy0
    simpa using hinj.ne this
  -- Clear denominators: `F(x) p ^ n y = x F(y)` in `W(k)`.
  have hW : frobenius x * (p : WittVector p k) ^ n * y = x * frobenius y := by
    apply hinj
    rw [map_div₀, hσ, hσ] at ha
    simp only [map_mul, map_pow, map_natCast]
    field_simp at ha
    linear_combination ha
  -- Write `x = p ^ m u` and `y = p ^ l w` with `u, w` of nonzero constant coefficient; after
  -- cancelling `p ^ (m + l)`, the constant coefficients give `0 = u₀ w₀ ^ p`.
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_p_mul x hx0
  obtain ⟨l, w, hw, rfl⟩ := exists_eq_pow_p_mul y hy0
  simp only [map_mul, map_pow, map_natCast] at hW
  have hcancel : frobenius u * (p : WittVector p k) ^ n * w = u * frobenius w := by
    apply mul_left_cancel₀ (pow_ne_zero (m + l) (p_ne_zero p k))
    linear_combination hW
  have h0 := congrArg WittVector.constantCoeff hcancel
  simp only [map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow hn, mul_zero, zero_mul,
    WittVector.constantCoeff_apply, coeff_frobenius_charP] at h0
  exact mul_ne_zero hu (pow_ne_zero _ hw) h0.symm

/-- **Nilpotence of Hyodo–Kato monodromy**. On a finite-dimensional isocrystal `V` over the
fraction field `K(p, k)` of the Witt vectors `W(k)` of a perfect domain `k` of characteristic `p`,
every linear endomorphism `N` satisfying `N Φ = p Φ N` with the Frobenius `Φ` of `V` has
`N ^ dim V = 0`. -/
theorem pow_finrank_eq_zero_of_isocrystal_monodromy {V : Type*} [AddCommGroup V]
    [Isocrystal p k V] [FiniteDimensional K(p, k) V] {N : V →ₗ[K(p, k)] V}
    (hN : ∀ x, N (Φ(p, k) x) = (p : K(p, k)) • Φ(p, k) (N x)) :
    N ^ finrank K(p, k) V = 0 :=
  pow_finrank_eq_zero_of_frobenius_monodromy hN fun _ _ hn ha ↦
    eq_zero_of_frobenius_mul_p_pow_eq p k hn ha

end Witt

end TauCeti
