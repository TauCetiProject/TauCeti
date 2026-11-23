/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.FormalGroup.AddCocycle.Basic
import Mathlib.Order.Filter.Cofinite
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Bounded denominators for additive analytic 2-cocycles

Let `E` be a normed space over `ℚ_[p]`, for instance `ℂ_p`, a Tate algebra over it, or any
`p`-adic Banach space. An additive 2-cocycle `f(Y, Z)` with coefficients `b_{i,j}` in `E` is a
coboundary `u(Y + Z) - u(Y) - u(Z)` (`TauCeti.IsAddCocycleCoeff.exists_addCoboundaryCoeff_eq`).
This file shows that the primitive `u` loses at most one power of `p`: if every coefficient of `f`
has norm at most `M`, then every coefficient of `u`, normalized by `u₁ = 0`, has norm at most
`p * M`; and if the coefficients of `f` tend to zero, so do those of `u`. Thus a cocycle in
`O_C{Y, Z}` is the coboundary of some `u ∈ p⁻¹ O_C{X}` with `u(0) = -f(0, 0)` and no linear term,
and the same denominator bound holds for vector-valued coefficients.

The reason is that the coefficient of `YⁱZᵏ⁻ⁱ` in `u(Y + Z) - u(Y) - u(Z)` is
`k.choose i • a_k` for `0 < i < k`, and for every `k ≥ 2` some such binomial coefficient is not
divisible by `p ^ 2` (`Nat.Prime.exists_not_sq_dvd_choose`), for instance `i = 1` when `p ∤ k`,
and `i = p ^ (r - 1)` when `p ^ r` exactly divides `k`. Its `p`-adic norm is then at least
`p⁻¹`. The
constant `p` cannot be improved: for `f = YZ` the primitive `X² / 2` needs it at `p = 2`, and in
general `u = Xᵖ / p` gives a cocycle with integral coefficients `p.choose i / p`.

Conversely, in an ultrametric space the coboundary of `u` has coefficients no larger than those
of `u` (`TauCeti.norm_addCoboundaryCoeff_le`), so it preserves bounded and convergent coefficient
families.

## Main results

* `TauCeti.exists_norm_le_mul_norm_addCoboundaryCoeff`: for `k ≥ 2` there is `0 < i < k` with
  `‖a_k‖ ≤ p * ‖b_{i,k-i}‖`, where `b = addCoboundaryCoeff a`.
* `TauCeti.norm_le_mul_of_forall_norm_addCoboundaryCoeff_le`: if `‖b_{i,j}‖ ≤ M` for all `i, j`,
  then `‖a_k‖ ≤ p * M` for all `k ≠ 1`.
* `TauCeti.tendsto_of_tendsto_addCoboundaryCoeff`: if the coefficients of `b` tend to zero, so do
  those of `a`.
* `TauCeti.IsAddCocycleCoeff.exists_addCoboundaryCoeff_eq_of_norm_le`: **bounded denominators**:
  a cocycle with coefficients of norm at most `M` tending to zero is the coboundary of a series
  with coefficients of norm at most `p * M` tending to zero, constant coefficient `-b_{0,0}` and
  linear coefficient `0`.

## References

* P. Colmez and W. Nizioł, *On the cohomology of p-adic analytic spaces, II: The
  C_st-conjecture* (2025), Lemma 4.13 and its proof.
-/

public section

open Filter Topology

namespace TauCeti

section Ultrametric

variable {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]

/-- In an ultrametric group, each coefficient of `u(Y + Z) - u(Y) - u(Z)` is no larger than the
coefficient of `u` in the same total degree. -/
theorem norm_addCoboundaryCoeff_le (a : ℕ → E) (i j : ℕ) :
    ‖addCoboundaryCoeff a (i, j)‖ ≤ ‖a (i + j)‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [addCoboundaryCoeff_apply_zero_left a hj]
  rcases eq_or_ne j 0 with rfl | hj
  · simp [addCoboundaryCoeff_apply_zero_right a hi]
  rw [addCoboundaryCoeff_apply_of_ne_zero a hi hj]
  exact IsUltrametricDist.norm_nsmul_le _ _

/-- In an ultrametric group, the coboundary of a series whose coefficients tend to zero has
coefficients tending to zero. -/
theorem tendsto_addCoboundaryCoeff {a : ℕ → E} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (addCoboundaryCoeff a) cofinite (𝓝 0) := by
  -- The total degree `i + j` tends to infinity along the cofinite filter of `ℕ × ℕ`.
  have hdeg : Tendsto (fun ij : ℕ × ℕ => ij.1 + ij.2) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    refine Tendsto.cofinite_of_finite_preimage_singleton fun n => ?_
    exact ((Finset.antidiagonal n).finite_toSet.subset fun ij hij => by simpa using hij).to_subtype
  exact squeeze_zero_norm (fun ij => norm_addCoboundaryCoeff_le a ij.1 ij.2)
    ((tendsto_norm_zero.comp ha).comp hdeg)

end Ultrametric

section Padic

variable {p : ℕ} [Fact p.Prime] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℚ_[p] E]

/-- **The denominator bound for a single coefficient.** For `k ≥ 2` some mixed coefficient
`b_{i,k-i} = k.choose i • a_k`, `0 < i < k`, of `u(Y + Z) - u(Y) - u(Z)` controls `a_k` up to the
factor `p`: `‖a_k‖ ≤ p * ‖b_{i,k-i}‖`. -/
theorem exists_norm_le_mul_norm_addCoboundaryCoeff (a : ℕ → E) {k : ℕ} (hk : 2 ≤ k) :
    ∃ i, 0 < i ∧ i < k ∧ ‖a k‖ ≤ p * ‖addCoboundaryCoeff a (i, k - i)‖ := by
  obtain ⟨i, hi, hik, hdvd⟩ := (Fact.out : p.Prime).exists_not_sq_dvd_choose hk
  refine ⟨i, hi, hik, ?_⟩
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnorm : (p : ℝ)⁻¹ ≤ ‖(k.choose i : ℚ_[p])‖ := by
    simpa using (Padic.zpow_neg_le_norm_natCast_iff (p := p) (k := 1)).2 hdvd
  rw [addCoboundaryCoeff_apply_of_ne_zero a hi.ne' (by omega), Nat.add_sub_cancel' hik.le,
    ← Nat.cast_smul_eq_nsmul ℚ_[p], norm_smul, ← mul_assoc]
  refine le_mul_of_one_le_left (norm_nonneg _) ?_
  calc (1 : ℝ) = p * (p : ℝ)⁻¹ := (mul_inv_cancel₀ hp.ne').symm
    _ ≤ p * ‖(k.choose i : ℚ_[p])‖ := by gcongr

/-- **Bounded denominators.** If every coefficient of `u(Y + Z) - u(Y) - u(Z)` has norm at most
`M`, then every coefficient of `u` other than the linear one has norm at most `p * M`. -/
theorem norm_le_mul_of_forall_norm_addCoboundaryCoeff_le {a : ℕ → E} {M : ℝ}
    (hM : ∀ ij, ‖addCoboundaryCoeff a ij‖ ≤ M) {k : ℕ} (hk : k ≠ 1) : ‖a k‖ ≤ p * M := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0))
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 0 := by omega
    simpa using (hM (0, 0)).trans (le_mul_of_one_le_left hM0 hp)
  · obtain ⟨i, -, -, hi⟩ := exists_norm_le_mul_norm_addCoboundaryCoeff (p := p) a hk2
    exact hi.trans (by gcongr; exact hM _)

variable (p) in
include p in
/-- If the coefficients of `u(Y + Z) - u(Y) - u(Z)` tend to zero, so do those of `u`, for `u` with
coefficients in a normed `ℚ_[p]`-space. -/
theorem tendsto_of_tendsto_addCoboundaryCoeff {a : ℕ → E}
    (h : Tendsto (addCoboundaryCoeff a) cofinite (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  -- For `k ≥ 2`, pick `0 < i_k < k` as in `exists_norm_le_mul_norm_addCoboundaryCoeff`; the
  -- indices `(i_k, k - i_k)` are pairwise distinct, so `b` tends to zero along them.
  choose! i hi using fun k (hk : 2 ≤ k) =>
    exists_norm_le_mul_norm_addCoboundaryCoeff (p := p) a hk
  let g : ℕ → ℕ × ℕ := fun n => (i (n + 2), n + 2 - i (n + 2))
  have hg : Function.Injective g := by
    intro m n hmn
    have h1 := congrArg (fun ij : ℕ × ℕ => ij.1 + ij.2) hmn
    have hm := (hi (m + 2) (by omega)).2.1
    have hn := (hi (n + 2) (by omega)).2.1
    simp only [g] at h1
    omega
  have hb : Tendsto (fun n => addCoboundaryCoeff a (g n)) atTop (𝓝 0) :=
    Nat.cofinite_eq_atTop ▸ h.comp hg.tendsto_cofinite
  rw [← tendsto_add_atTop_iff_nat 2]
  refine squeeze_zero_norm (fun n => (hi (n + 2) (by omega)).2.2) ?_
  simpa using (tendsto_norm_zero.comp hb).const_mul (p : ℝ)

/-- **Bounded denominators for additive analytic 2-cocycles.** Let `b` be the coefficient family
of an additive 2-cocycle `f(Y, Z)` with coefficients in a normed `ℚ_[p]`-space, of norm at most `M`
and tending to zero. Then `f(Y, Z) = u(Y + Z) - u(Y) - u(Z)` for a series `u` whose coefficients
have norm at most `p * M` and tend to zero, with `u(0) = -f(0, 0)` and no linear term. For `M = 1`
and coefficients in `ℂ_p`: a cocycle in `O_C{Y, Z}` is the coboundary of some `u ∈ p⁻¹ O_C{X}`. -/
theorem IsAddCocycleCoeff.exists_addCoboundaryCoeff_eq_of_norm_le {b : ℕ × ℕ → E}
    (hb : IsAddCocycleCoeff b) {M : ℝ} (hM : ∀ ij, ‖b ij‖ ≤ M)
    (hb0 : Tendsto b cofinite (𝓝 0)) :
    ∃ a : ℕ → E, addCoboundaryCoeff a = b ∧ a 0 = -b (0, 0) ∧ a 1 = 0 ∧
      (∀ k, ‖a k‖ ≤ p * M) ∧ Tendsto a atTop (𝓝 0) := by
  obtain ⟨a, rfl, ha0, ha1⟩ := hb.exists_addCoboundaryCoeff_eq ℚ_[p]
  refine ⟨a, rfl, ha0, ha1, fun k => ?_, tendsto_of_tendsto_addCoboundaryCoeff p hb0⟩
  rcases eq_or_ne k 1 with rfl | hk
  · have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    simpa [ha1] using mul_nonneg hp ((norm_nonneg _).trans (hM (0, 0)))
  · exact norm_le_mul_of_forall_norm_addCoboundaryCoeff_le hM hk

end Padic

end TauCeti
