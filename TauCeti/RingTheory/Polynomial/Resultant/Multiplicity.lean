/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Resultant multiplicity bounds

For a bivariate polynomial `f : R[X][X]` of outer natural degree `n = f.natDegree`, write
`Res_{n, n - 1}(f, f.derivative) := f.resultant f.derivative n (n - 1)` for its fixed-degree
resultant with its derivative. When `(X - C a) ^ k` divides the specialization `f(X, b)` (with
`k - 1 ≤ n + (n - 1)`), `(X - C b) ^ (k - 1)` divides `Res_{n, n - 1}(f, f.derivative)`
(`Polynomial.X_sub_C_pow_dvd_resultant_deriv`). Note that this fixed-degree resultant can differ
from the ordinary resultant `f.resultant f.derivative` in positive characteristic when
`f.derivative.natDegree < n - 1`.

Whenever `Res_{n, n - 1}(f, f.derivative)` is nonzero, this divisibility bounds the fiberwise
root multiplicity of `f(X, b)` at `a` by `1` plus the root multiplicity of
`Res_{n, n - 1}(f, f.derivative)` at `b`
(`Polynomial.rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv`). Combined with the
coefficient-degree bound `Polynomial.natDegree_resultant_le` on Sylvester determinants, summing
over a finite set of points with distinct second coordinates bounds the total fiberwise root
multiplicity of an irreducible bivariate polynomial
(`Polynomial.sum_rootMultiplicity_le_of_irreducible`).

## Main results

* `Polynomial.X_sub_C_pow_dvd_resultant_deriv`: `(X - C b) ^ (k - 1)` divides the fixed-degree
  resultant `Res_{n, n - 1}(f, f.derivative) := f.resultant f.derivative f.natDegree
  (f.natDegree - 1)` whenever `k - 1 ≤ f.natDegree + (f.natDegree - 1)` and `(X - C a) ^ k`
  divides the specialization `f.map (evalRingHom b)`.
* `Polynomial.rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv`: when the
  fixed-degree resultant `Res_{n, n - 1}(f, f.derivative)` is nonzero, the fiberwise root
  multiplicity of `f.map (evalRingHom b)` at `a` is at most `1` plus the root multiplicity of
  `Res_{n, n - 1}(f, f.derivative)` at `b`.
* `Polynomial.sum_rootMultiplicity_le_of_irreducible`: sum of fiberwise root multiplicities of
  an irreducible bivariate polynomial over a set with distinct second coordinates.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, Appendix A.
* T. Tao, *A sketch of the proof of non-existence of Siegel zeroes*, blog post, 2026.
-/

public section

open Finset

namespace Polynomial

section MultiplicityDivisibility

variable {R : Type*} [CommRing R]

/-- If `k - 1 ≤ f.natDegree + (f.natDegree - 1)` and `X` divides `f.coeff i` for every `i < k`,
then `X ^ (k - 1)` divides the fixed-degree resultant
`f.resultant f.derivative f.natDegree (f.natDegree - 1)`. -/
private theorem X_pow_dvd_resultant_deriv_of_forall_dvd (f : R[X][X]) {k : ℕ}
    (hk : k - 1 ≤ f.natDegree + (f.natDegree - 1)) (hcoeff : ∀ i < k, X ∣ f.coeff i) :
    X ^ (k - 1) ∣ f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  set m := f.natDegree
  set n := f.natDegree - 1
  have hdvd := Matrix.prod_dvd_det_of_dvd_row (sylvester f f.derivative m n)
    (fun i ↦ if (i : ℕ) < k - 1 then X else 1) fun i j ↦ ?_
  · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
      Fin.card_filter_val_lt, min_eq_right hk] at hdvd
    exact hdvd
  · by_cases hi : (i : ℕ) < k - 1
    · rw [ite_eq_left hi]
      by_cases hj : (j : ℕ) < m
      · rw [sylvester_apply_of_lt f f.derivative i j hj]
        split_ifs with h
        · rw [coeff_derivative]
          exact dvd_mul_of_dvd_left (hcoeff ((i : ℕ) - j + 1) (by omega)) _
        · exact dvd_zero _
      · rw [sylvester_apply_of_le f f.derivative i j (Nat.le_of_not_lt hj)]
        split_ifs with h
        · exact hcoeff ((i : ℕ) + m - j) (by omega)
        · exact dvd_zero _
    · rw [ite_eq_right hi]
      exact one_dvd _

/-- **Resultant multiplicity divisibility.** If `(X - C a) ^ k` divides the specialization
`f.map (evalRingHom b)` of `f : R[X][X]` and `k - 1 ≤ f.natDegree + (f.natDegree - 1)`, then
`(X - C b) ^ (k - 1)` divides the fixed-degree resultant
`Res_{n, n - 1}(f, f.derivative) := f.resultant f.derivative f.natDegree (f.natDegree - 1)`. -/
theorem X_sub_C_pow_dvd_resultant_deriv (f : R[X][X]) {a b : R} {k : ℕ}
    (hk : k - 1 ≤ f.natDegree + (f.natDegree - 1))
    (hdvd : (X - C a) ^ k ∣ f.map (evalRingHom b)) :
    (X - C b) ^ (k - 1) ∣ f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  let e : R[X] ≃ₐ[R] R[X] := taylorEquiv b
  let f₁ : R[X][X] := f.map e.toRingHom
  have hf₁_deg : f₁.natDegree = f.natDegree := natDegree_map_eq_of_injective e.injective f
  let f₂ : R[X][X] := taylor (C a) f₁
  have hf₂_deg : f₂.natDegree = f.natDegree := by rw [natDegree_taylor, hf₁_deg]
  have heval0 : (evalRingHom (0 : R)).comp e.toRingHom = evalRingHom b :=
    RingHom.ext fun p ↦ by
      change eval 0 (taylor b p) = eval b p
      rw [taylor_eval, zero_add]
  have hf₂_eval0 : f₂.map (evalRingHom 0) = taylor a (f.map (evalRingHom b)) := by
    rw [map_taylor, Polynomial.map_map, heval0]
    simp
  have hX_pow_dvd : X ^ k ∣ f₂.map (evalRingHom 0) := by
    rw [hf₂_eval0, taylor_apply]
    exact X_sub_C_pow_dvd_iff.mp hdvd
  have hcoeff : ∀ i < k, X ∣ f₂.coeff i := by
    intro i hi
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    have h0 := (X_pow_dvd_iff.mp hX_pow_dvd) i hi
    rwa [coeff_map, coe_evalRingHom] at h0
  have hdvd_res₂ : X ^ (k - 1) ∣ f₂.resultant f₂.derivative f₂.natDegree (f₂.natDegree - 1) :=
    X_pow_dvd_resultant_deriv_of_forall_dvd f₂ (by rwa [hf₂_deg]) hcoeff
  have hder₁ : (taylor (C a) f₁).derivative = taylor (C a) f₁.derivative := by
    simp [taylor_apply, derivative_comp]
  have hres_eq : f₂.resultant f₂.derivative f₂.natDegree (f₂.natDegree - 1) =
      e (f.resultant f.derivative f.natDegree (f.natDegree - 1)) := by
    dsimp only [f₂]
    rw [hf₂_deg, ← hf₁_deg, hder₁,
      resultant_taylor_of_natDegree_le f₁ f₁.derivative (C a) le_rfl (natDegree_derivative_le f₁),
      hf₁_deg]
    dsimp only [f₁]
    rw [derivative_map, resultant_map_map]
    rfl
  rw [hres_eq] at hdvd_res₂
  have hdvd_symm := _root_.map_dvd e.symm.toAlgHom hdvd_res₂
  simp only [map_pow, AlgEquiv.coe_toAlgHom, e.symm_apply_apply] at hdvd_symm
  change (taylor (-b) X) ^ (k - 1) ∣ f.resultant f.derivative f.natDegree (f.natDegree - 1)
    at hdvd_symm
  simpa [taylor_X, sub_eq_add_neg] using hdvd_symm

/-- If the fixed-degree resultant `Res_{n, n - 1}(f, f.derivative) := f.resultant f.derivative
f.natDegree (f.natDegree - 1)` is nonzero, then the root multiplicity of `f.map (evalRingHom b)`
at `a` is at most `1` plus the root multiplicity of `Res_{n, n - 1}(f, f.derivative)` at `b`. -/
theorem rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv
    {f : R[X][X]} {a b : R}
    (hres : f.resultant f.derivative f.natDegree (f.natDegree - 1) ≠ 0) :
    (f.map (evalRingHom b)).rootMultiplicity a ≤
      1 + (f.resultant f.derivative f.natDegree (f.natDegree - 1)).rootMultiplicity b := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact absurd (Subsingleton.elim _ _) hres
  by_cases hfb : f.map (evalRingHom b) = 0
  · simp [hfb]
  set k := (f.map (evalRingHom b)).rootMultiplicity a
  have hk_eq : ((X - C a) ^ k).natDegree = k := by
    rw [(monic_X_sub_C a).natDegree_pow k, natDegree_X_sub_C, mul_one]
  have hk_le_deg : k ≤ f.natDegree := by
    rw [← hk_eq]
    exact (((monic_X_sub_C a).pow k).natDegree_le_of_dvd hfb
      (pow_rootMultiplicity_dvd _ a)).trans natDegree_map_le
  have hk : k - 1 ≤ f.natDegree + (f.natDegree - 1) := by omega
  have hdvd := X_sub_C_pow_dvd_resultant_deriv f hk (pow_rootMultiplicity_dvd _ a)
  have hle : k - 1 ≤ (f.resultant f.derivative f.natDegree (f.natDegree - 1)).rootMultiplicity b :=
    (le_rootMultiplicity_iff hres).mpr hdvd
  omega

end MultiplicityDivisibility

section IrreducibleBound

/-- **Sum of fiberwise root multiplicities of an irreducible bivariate polynomial.**
Over a GCD domain of characteristic zero, if `F : K[X][X]` is irreducible and every coefficient
`F.coeff i` has natural degree at most `dY`, then the sum of
`(F.map (evalRingHom p.2)).rootMultiplicity p.1` over a finite set `Ω` of points with distinct
second coordinates is bounded by the number of zeros of `F` in `Ω` plus
`(2 * F.natDegree - 1) * dY`. -/
theorem sum_rootMultiplicity_le_of_irreducible {K : Type*} [CommRing K] [IsDomain K]
    [IsGCDMonoid K] [CharZero K] [DecidableEq K]
    {F : K[X][X]} (hF : Irreducible F)
    {dY : ℕ} (hdY : ∀ i, (F.coeff i).natDegree ≤ dY)
    {Ω : Finset (K × K)} (hinj : Set.InjOn Prod.snd (Ω : Set (K × K))) :
    ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      (Ω.filter fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card +
        (2 * F.natDegree - 1) * dY := by
  set res := F.resultant F.derivative F.natDegree (F.natDegree - 1)
  have hres_ne : res ≠ 0 := resultant_deriv_ne_zero_of_squarefree hF.squarefree
  have hres_deg : res.natDegree ≤ (2 * F.natDegree - 1) * dY := by
    have hder_deg : ∀ i ≤ F.natDegree - 1, (F.derivative.coeff i).natDegree ≤ dY := by
      intro i _
      rw [coeff_derivative]
      exact (natDegree_mul_le).trans (by simpa [natDegree_natCast] using hdY (i + 1))
    calc res.natDegree ≤ F.natDegree * dY + (F.natDegree - 1) * dY :=
          natDegree_resultant_le (fun i _ ↦ hdY i) hder_deg
      _ = (2 * F.natDegree - 1) * dY := by
          rw [← add_mul]
          congr 1
          omega
  let Z : Finset (K × K) := Ω.filter fun p ↦ (F.map (evalRingHom p.2)).eval p.1 = 0
  have hsum_eq : ∑ p ∈ Ω, (F.map (evalRingHom p.2)).rootMultiplicity p.1 =
      ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1 := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ Ω) fun p hp hpZ ↦ ?_
    have hne : (F.map (evalRingHom p.2)).eval p.1 ≠ 0 := by
      simpa [Z, hp] using hpZ
    exact rootMultiplicity_eq_zero hne
  have hsum_Z : ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1 ≤
      Z.card + ∑ p ∈ Z, res.rootMultiplicity p.2 := by
    calc ∑ p ∈ Z, (F.map (evalRingHom p.2)).rootMultiplicity p.1
        ≤ ∑ p ∈ Z, (1 + res.rootMultiplicity p.2) :=
          Finset.sum_le_sum fun _ _ ↦
            rootMultiplicity_le_one_add_rootMultiplicity_resultant_deriv hres_ne
      _ = Z.card + ∑ p ∈ Z, res.rootMultiplicity p.2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hinjZ : Set.InjOn Prod.snd (Z : Set (K × K)) :=
    hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ Ω))
  have hsum_res : ∑ p ∈ Z, res.rootMultiplicity p.2 ≤ res.natDegree := by
    rw [← Finset.sum_image (f := fun b ↦ res.rootMultiplicity b) (g := Prod.snd) hinjZ]
    exact sum_rootMultiplicity_le_natDegree res (Z.image Prod.snd)
  exact hsum_eq.le.trans (hsum_Z.trans (Nat.add_le_add_left (hsum_res.trans hres_deg) Z.card))

end IrreducibleBound

end Polynomial
