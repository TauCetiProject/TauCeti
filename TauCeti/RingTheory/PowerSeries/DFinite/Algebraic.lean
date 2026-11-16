/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.PowerSeries.DFinite.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Algebraic coefficients of D-finite power series

Let `f : K⟦X⟧` be D-finite over a field `k` algebraic over a base field `F`, in characteristic
zero. If every coefficient of `f` is algebraic over `F`, then all coefficients of `f` lie in a
single finite-dimensional intermediate field `E` of `K / F`
(`PowerSeries.IsDFinite.exists_finiteDimensional_intermediateField`). When `F = ℚ`, this means
that all coefficients of `f` lie in a single number field
(`PowerSeries.IsDFinite.exists_numberField`).

In Diophantine approximation and transcendence theory, Siegel's E-functions and G-functions are
defined a priori with Taylor coefficients in `ℚ̄` satisfying a linear differential equation over
`ℚ̄[X]`. Because a nontrivial polynomial recurrence in characteristic zero expresses all
sufficiently late coefficients rationally in terms of finitely many initial terms and the
coefficients of the recurrence polynomials, the coefficients cannot generate an infinite algebraic
extension: this reduces all height, denominator, and Siegel-lemma constructions for an E- or
G-function to a single number field of finite degree over `ℚ`.

## Main results

* `PowerSeries.IsDFinite.exists_finiteDimensional_intermediateField`: if `f : K⟦X⟧` is D-finite
  over an algebraic extension `k` of `F` in characteristic zero and every coefficient of `f` is
  algebraic over `F`, then all coefficients of `f` lie in a common finite-dimensional intermediate
  field of `K / F`.
* `PowerSeries.IsDFinite.exists_numberField`: if `f : K⟦X⟧` is D-finite over an algebraic
  extension `k` of `ℚ` in characteristic zero and every coefficient of `f` is algebraic over `ℚ`,
  then all coefficients of `f` lie in a common intermediate `NumberField`.

## References

* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §3.1,
  remark on coefficients lying in a fixed number field.
-/

public section

open Polynomial

namespace PowerSeries

private theorem coeff_mem_of_pRecursive {F k K : Type*} [Field F] [Field k] [Field K]
    [Algebra k K] [Algebra F K]
    {f : K⟦X⟧} {E : IntermediateField F K} {r N₀ : ℕ} {q : Fin (r + 1) → k[X]}
    (hqne : ∀ {n : ℕ}, N₀ + 1 ≤ n → (q (Fin.last r)).eval (n : k) ≠ 0)
    (hrec_all : ∀ n : ℕ, ∑ i : Fin (r + 1), (q i).eval (n : k) • coeff (n + i) f = 0)
    (hqmem : ∀ (i : Fin (r + 1)) (n : ℕ), algebraMap k K ((q i).eval (n : k)) ∈ E)
    (hinit : ∀ (m : ℕ), m < N₀ + 1 + r → coeff m f ∈ E) (m : ℕ) :
    coeff m f ∈ E := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hm : m < N₀ + 1 + r
    · exact hinit m hm
    · set n : ℕ := m - r
      have hmr : n + r = m := by omega
      have hn : N₀ + 1 ≤ n := by omega
      have hrec := hrec_all n
      rw [Fin.sum_univ_castSucc, Fin.val_last] at hrec
      have hc0 : algebraMap k K ((q (Fin.last r)).eval (n : k)) ≠ 0 :=
        (map_ne_zero_iff (algebraMap k K) (algebraMap k K).injective).mpr (hqne hn)
      have hsolve : coeff (n + r) f =
          -(algebraMap k K ((q (Fin.last r)).eval (n : k)))⁻¹ *
            ∑ i : Fin r, (q i.castSucc).eval (n : k) • coeff (n + i.castSucc) f := by
        rw [Algebra.smul_def] at hrec
        have hmul : algebraMap k K ((q (Fin.last r)).eval (n : k)) * coeff (n + r) f =
            -∑ i : Fin r, (q i.castSucc).eval (n : k) • coeff (n + i.castSucc) f :=
          eq_neg_of_add_eq_zero_right hrec
        calc coeff (n + r) f
            = (algebraMap k K ((q (Fin.last r)).eval (n : k)))⁻¹ *
                (algebraMap k K ((q (Fin.last r)).eval (n : k)) * coeff (n + r) f) := by
              rw [inv_mul_cancel_left₀ hc0]
          _ = -(algebraMap k K ((q (Fin.last r)).eval (n : k)))⁻¹ *
                ∑ i : Fin r, (q i.castSucc).eval (n : k) • coeff (n + i.castSucc) f := by
              rw [hmul, mul_neg, neg_mul]
      rw [← hmr, hsolve]
      refine mul_mem (neg_mem (inv_mem (hqmem (Fin.last r) n))) (sum_mem fun i _ ↦ ?_)
      rw [Algebra.smul_def, Fin.val_castSucc]
      exact mul_mem (hqmem i.castSucc n) (ih (n + i) (by have := i.isLt; omega))

/-- If `f : K⟦X⟧` is D-finite over a field `k` that is algebraic over `F`, in characteristic zero,
and every coefficient of `f` is algebraic over `F`, then all coefficients of `f` lie in a single
finite-dimensional intermediate field of `K / F`. -/
theorem IsDFinite.exists_finiteDimensional_intermediateField
    {F k K : Type*} [Field F] [Field k] [Field K] [CharZero K]
    [Algebra F k] [Algebra k K] [Algebra F K] [IsScalarTower F k K] [Algebra.IsAlgebraic F k]
    {f : K⟦X⟧} (hf : IsDFinite k f) (halg : ∀ n, IsAlgebraic F (coeff n f)) :
    ∃ E : IntermediateField F K, FiniteDimensional F E ∧ ∀ n, coeff n f ∈ E := by
  classical
  have hnat : Function.Injective (Nat.cast : ℕ → k) := fun a b hab ↦
    Nat.cast_injective (R := K) (by simpa using congrArg (algebraMap k K) hab)
  obtain ⟨r, q, hq, h⟩ := isDFinite_iff_pRecursive.mp hf
  have hfin : ((Nat.cast : ℕ → k) ⁻¹' ((q (Fin.last r)).roots.toFinset : Set k)).Finite :=
    Set.Finite.preimage hnat.injOn (Finset.finite_toSet _)
  obtain ⟨N₀, hN₀⟩ := hfin.bddAbove
  have hqne {n : ℕ} (hn : N₀ + 1 ≤ n) : (q (Fin.last r)).eval (n : k) ≠ 0 := by
    intro heval
    have hmem : n ∈ (Nat.cast : ℕ → k) ⁻¹' ((q (Fin.last r)).roots.toFinset : Set k) := by
      simp [(Polynomial.mem_roots hq).mpr heval]
    have := hN₀ hmem
    omega
  let T₁ : Finset K := Finset.univ.biUnion fun i : Fin (r + 1) ↦
    (q i).support.image fun j ↦ algebraMap k K ((q i).coeff j)
  let T₂ : Finset K := (Finset.range (N₀ + 1 + r)).image fun m ↦ coeff m f
  let T : Finset K := T₁ ∪ T₂
  have hTint : ∀ x ∈ (T : Set K), IsIntegral F x := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with hx | hx
    · simp only [T₁, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hx
      obtain ⟨i, j, -, rfl⟩ := hx
      exact ((Algebra.IsAlgebraic.isAlgebraic (R := F) ((q i).coeff j)).isIntegral).map
        (IsScalarTower.toAlgHom F k K)
    · simp only [T₂, Finset.mem_image] at hx
      obtain ⟨m, -, rfl⟩ := hx
      exact (halg m).isIntegral
  let E : IntermediateField F K := IntermediateField.adjoin F (T : Set K)
  have hfd : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin hTint
  have hqmem (i : Fin (r + 1)) (n : ℕ) : algebraMap k K ((q i).eval (n : k)) ∈ E := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum]
    refine sum_mem fun j hj ↦ ?_
    rw [map_mul, map_pow, map_natCast]
    refine mul_mem ?_ (pow_mem (natCast_mem E n) j)
    refine IntermediateField.subset_adjoin F (T : Set K) ?_
    exact Finset.mem_coe.mpr (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hj⟩))
  refine ⟨E, hfd, coeff_mem_of_pRecursive hqne h hqmem fun m hm ↦ ?_⟩
  refine IntermediateField.subset_adjoin F (T : Set K) ?_
  exact Finset.mem_coe.mpr (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hm)))

/-- If `f : K⟦X⟧` is D-finite over an algebraic extension `k` of `ℚ`, in characteristic zero, and
every coefficient of `f` is algebraic over `ℚ`, then all coefficients of `f` lie in a common
intermediate number field of `K`. -/
theorem IsDFinite.exists_numberField
    {k K : Type*} [Field k] [Field K] [CharZero K] [Algebra k K] [Algebra ℚ k]
    [IsScalarTower ℚ k K] [Algebra.IsAlgebraic ℚ k]
    {f : K⟦X⟧} (hf : IsDFinite k f) (halg : ∀ n, IsAlgebraic ℚ (coeff n f)) :
    ∃ (E : IntermediateField ℚ K) (_ : NumberField E), ∀ n, coeff n f ∈ E := by
  obtain ⟨E, hfd, hmem⟩ := hf.exists_finiteDimensional_intermediateField (F := ℚ) halg
  exact ⟨E, {}, hmem⟩

end PowerSeries
