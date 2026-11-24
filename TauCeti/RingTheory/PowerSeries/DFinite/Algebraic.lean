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
import TauCeti.Algebra.LinearRecurrence.Subfield

/-!
# Algebraic coefficients of D-finite power series

Let `f : K⟦X⟧` be D-finite over a field `k` algebraic over a base field `F`, in characteristic
zero. If every coefficient of `f` is algebraic over `F`, then all coefficients of `f` lie in a
single finite-dimensional intermediate field `E` of `K / F`
(`PowerSeries.IsDFinite.exists_finiteDimensional_intermediateField`). When `F = ℚ`, this means
that all coefficients of `f` lie in a single number field
(`PowerSeries.IsDFinite.exists_numberField`).

In Diophantine approximation and transcendence theory, Siegel's E-functions and G-functions are
defined a priori with Taylor coefficients in `algebraicClosure ℚ ℂ` satisfying a linear
differential equation over `(algebraicClosure ℚ ℂ)[X]`. Because a nontrivial polynomial recurrence
in characteristic zero expresses all sufficiently late coefficients rationally in terms of finitely
many initial terms and the coefficients of the recurrence polynomials, the coefficients cannot
generate an infinite algebraic extension: this reduces all height, denominator, and Siegel-lemma
constructions for an E- or G-function to a single number field of finite degree over `ℚ`.

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
  have hinit {m : ℕ} (hm : m < N₀ + 1 + r) : coeff m f ∈ E :=
    IntermediateField.subset_adjoin F (T : Set K) <|
      Finset.mem_coe.mpr (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hm)))
  refine ⟨E, hfd, fun m ↦ ?_⟩
  by_cases hm : N₀ + 1 ≤ m
  · exact TauCeti.mem_of_sum_mul_add_eq_zero_of_le
      (c := fun n i ↦ algebraMap k K ((q i).eval (n : k)))
      (a := fun n ↦ coeff n f)
      (fun n hn ↦ (map_ne_zero_iff (algebraMap k K) (algebraMap k K).injective).mpr (hqne hn))
      (fun n _ ↦ by simpa only [Algebra.smul_def] using h n)
      (fun n _ i ↦ hqmem i n)
      (fun _ _ hm' ↦ hinit hm')
      hm
  · exact hinit (by omega)

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
