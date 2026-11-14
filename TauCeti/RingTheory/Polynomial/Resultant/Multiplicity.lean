/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.RingTheory.Polynomial.GaussLemma
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Degree, Taylor divisibility, and fiber multiplicity for resultants

Let `f, g ∈ R[X][Y]` be bivariate polynomials viewed as polynomials in `Y` over `R[X]`. Expanding
the Sylvester determinant of `Res_Y(f, g)` along columns bounds its `X`-degree in terms of the
`X`-degrees of the coefficients of `f` and `g`, while expanding along rows after a Taylor shift in
`Y` relates vanishing of low-order Taylor coefficients to divisibility of `Res_Y(f, g)`.

Specifically:
* In the `(m + n) × (m + n)` Sylvester matrix `sylvester f g m n`, the first `m` columns carry
  coefficients of `g` of index at most `n` and the last `n` columns carry coefficients of `f` of
  index at most `m`, so `(resultant f g m n).natDegree ≤ m * d₂ + n * d₁`. For `g = ∂_Y f` this
  yields `(resultant f f.derivative).natDegree ≤ 2 * f.natDegree * d`.
* Row `i < k` of `sylvester f g m n` contains only coefficients of `f` and `g` of index at most
  `i < k`. Hence if those coefficients lie in an ideal `I` for all `i < k` (with `k ≤ m + n`),
  every entry of the first `k` rows lies in `I` and `resultant f g m n ∈ I ^ k`. Combining this
  with translation invariance `resultant (f.taylor a) (g.taylor a) = resultant f g` shows that if
  `r` divides the first `μ` Taylor coefficients of `f` at `a`, then `r ^ (μ - 1)` divides
  `resultant f f.derivative`.
* Over a characteristic-zero UFD `R`, if `f ∈ R[X][Y]` is irreducible of positive `Y`-degree, then
  `Res_Y(f, ∂_Y f) ≠ 0`, no fiber `f(x, Y)` vanishes identically, and the multiplicity of any root
  `y` of `f(x, Y)` satisfies
  `rootMultiplicity y (f.map (evalRingHom x)) ≤ 1 + rootMultiplicity x (resultant f f.derivative)`.

## Main results

* `Polynomial.natDegree_resultant_le`, `Polynomial.natDegree_resultant_derivative_le`: degree
  bounds in the coefficient variable for bivariate resultants and discriminants.
* `Polynomial.resultant_mem_pow_of_coeff_mem`, `Polynomial.resultant_mem_pow_of_taylor_coeff_mem`:
  ideal-power membership of the resultant from vanishing of low-degree (or Taylor) coefficients.
* `Polynomial.pow_dvd_resultant_of_dvd_taylor_coeff`,
  `Polynomial.pow_pred_dvd_resultant_derivative_of_dvd_taylor_coeff`: divisibility forms for a
  common divisor of low-order Taylor coefficients.
* `Squarefree.resultant_derivative_ne_zero`: `p.resultant p.derivative ≠ 0` for any squarefree
  polynomial `p` over a characteristic-zero GCD domain.
* `Polynomial.map_evalRingHom_ne_zero_of_irreducible`: an irreducible polynomial in `R[X][Y]` of
  positive `Y`-degree has no identically vanishing vertical fiber.
* `Polynomial.rootMultiplicity_map_evalRingHom_le_of_irreducible`: fiber root multiplicity bounded
  by `1` plus the root multiplicity of `resultant f f.derivative`.

## References

* [I. M. Gelfand, M. M. Kapranov, and A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*][gkz1994], Chapter 12, §1.
* [B. Green, *On Landau–Siegel zeros*][green2026], Appendix A.
-/

public section

open scoped Matrix Polynomial Polynomial.Bivariate

/-- Over a characteristic-zero GCD domain, a squarefree polynomial has nonzero resultant with its
derivative. -/
theorem Squarefree.resultant_derivative_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsGCDMonoid R] [CharZero R] {p : R[X]} (hp : Squarefree p) :
    p.resultant p.derivative ≠ 0 := by
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have : CharZero K := charZero_of_injective_algebraMap hinj
  have hsep : (p.map (algebraMap R K)).Separable :=
    PerfectField.separable_iff_squarefree.mpr hp.map_fraction_map
  have hne : (p.map (algebraMap R K)).resultant (p.map (algebraMap R K)).derivative ≠ 0 :=
    Polynomial.resultant_ne_zero _ _ hsep
  rw [Polynomial.derivative_map,
    Polynomial.resultant_map_of_natDegree_eq (algebraMap R K)
      (Polynomial.natDegree_map_eq_of_injective hinj p)
      (Polynomial.natDegree_map_eq_of_injective hinj p.derivative)] at hne
  exact fun h ↦ hne (by rw [h, map_zero])

namespace Polynomial

section BivariateDegree

variable {R : Type*} [CommRing R]

/-- **Bivariate resultant degree bound.** Viewing `f, g : R[X][Y]` as polynomials in the outer
variable with coefficients in `R[X]`, if the coefficients of `f` up to index `m` have degree at
most `d₁` and the coefficients of `g` up to index `n` have degree at most `d₂`, then
`resultant f g m n` has degree at most `m * d₂ + n * d₁`. -/
theorem natDegree_resultant_le {f g : R[X][Y]} {m n d₁ d₂ : ℕ}
    (hf : ∀ i ≤ m, (f.coeff i).natDegree ≤ d₁)
    (hg : ∀ j ≤ n, (g.coeff j).natDegree ≤ d₂) :
    (resultant f g m n).natDegree ≤ m * d₂ + n * d₁ := by
  -- Expand `det (sylvester f g m n)` by columns (`Matrix.det_apply`) so each permutation product
  -- splits over the first `m` columns (entries from `g`) and last `n` columns (entries from `f`).
  rw [resultant, Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_
  rcases Int.units_eq_one_or σ.sign with hs | hs <;>
    simp only [hs, one_smul, Units.neg_smul, natDegree_neg] <;>
  · rw [Fin.prod_univ_add]
    refine natDegree_mul_le.trans (Nat.add_le_add ?_ ?_)
    · refine (natDegree_prod_le _ _).trans ?_
      calc
        ∑ j : Fin m, (sylvester f g m n (σ (Fin.castAdd n j)) (Fin.castAdd n j)).natDegree
          ≤ ∑ _j : Fin m, d₂ := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc]
            split_ifs with h
            · exact hg _ (by omega)
            · simp
        _ = m * d₂ := by simp
    · refine (natDegree_prod_le _ _).trans ?_
      calc
        ∑ j : Fin n, (sylvester f g m n (σ (Fin.natAdd m j)) (Fin.natAdd m j)).natDegree
          ≤ ∑ _j : Fin n, d₁ := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc]
            split_ifs with h
            · exact hf _ (by omega)
            · simp
        _ = n * d₁ := by simp

/-- If every coefficient of `f : R[X][Y]` has `X`-degree at most `d`, then
`resultant f f.derivative` has `X`-degree at most `2 * f.natDegree * d`. -/
theorem natDegree_resultant_derivative_le {f : R[X][Y]} {d : ℕ}
    (hf : ∀ i, (f.coeff i).natDegree ≤ d) :
    (resultant f f.derivative).natDegree ≤ 2 * f.natDegree * d := by
  have hdf : ∀ j, (f.derivative.coeff j).natDegree ≤ d := fun j ↦ by
    rw [coeff_derivative]
    exact (natDegree_mul_le.trans (by simp [natDegree_natCast])).trans (hf (j + 1))
  calc
    (resultant f f.derivative).natDegree
      ≤ f.natDegree * d + f.derivative.natDegree * d :=
        natDegree_resultant_le (fun i _ ↦ hf i) (fun j _ ↦ hdf j)
    _ ≤ f.natDegree * d + f.natDegree * d :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_right d (f.natDegree_derivative_le.trans (Nat.sub_le _ _))) _
    _ = 2 * f.natDegree * d := by ring

end BivariateDegree

section TaylorDivisibility

variable {R : Type*} [CommRing R]

/-- If the coefficients of `f` and `g` below index `k` lie in an ideal `I`, with `k ≤ m + n`, then
`resultant f g m n ∈ I ^ k`. -/
theorem resultant_mem_pow_of_coeff_mem {f g : R[X]} {I : Ideal R} {m n k : ℕ}
    (hk : k ≤ m + n) (hf : ∀ i < k, f.coeff i ∈ I) (hg : ∀ j < k, g.coeff j ∈ I) :
    resultant f g m n ∈ I ^ k := by
  -- Put row `i` in `I` for `i < k` and in `⊤` for `i ≥ k`; the row-ideal product is `I ^ k`.
  let J : Fin (m + n) → Ideal R := fun i ↦ if (i : ℕ) < k then I else ⊤
  have hrow : ∀ i j : Fin (m + n), sylvester f g m n i j ∈ J i := by
    intro i j
    dsimp only [J]
    split_ifs with hi
    · induction j using Fin.addCases with
      | left j =>
        simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact hg _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hi)
        · exact I.zero_mem
      | right j =>
        simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact hf _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hi)
        · exact I.zero_mem
    · trivial
  have hdet := Matrix.det_mem_prod_row_ideals (sylvester f g m n) J hrow
  have hprod : ∏ i : Fin (m + n), J i = I ^ k := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hk
    have hcast : ∀ i : Fin (k + t), J (Fin.cast ht.symm i) = if (i : ℕ) < k then I else ⊤ :=
      fun _ ↦ rfl
    rw [← Equiv.prod_comp (finCongr ht.symm), Fin.prod_univ_add]
    simp [hcast, ← Ideal.one_eq_top]
  rwa [hprod] at hdet

/-- If the first `k` Taylor coefficients of `f` and `g` at `a` lie in `I` (with
`k ≤ f.natDegree + g.natDegree`), then `resultant f g ∈ I ^ k`. -/
theorem resultant_mem_pow_of_taylor_coeff_mem {f g : R[X]} {I : Ideal R} {a : R} {k : ℕ}
    (hk : k ≤ f.natDegree + g.natDegree)
    (hf : ∀ i < k, (f.taylor a).coeff i ∈ I) (hg : ∀ j < k, (g.taylor a).coeff j ∈ I) :
    resultant f g ∈ I ^ k := by
  rw [← resultant_taylor f g a]
  exact resultant_mem_pow_of_coeff_mem (by simpa using hk) hf hg

/-- If `r` divides the first `k` Taylor coefficients of `f` and `g` at `a` (with
`k ≤ f.natDegree + g.natDegree`), then `r ^ k ∣ resultant f g`. -/
theorem pow_dvd_resultant_of_dvd_taylor_coeff {f g : R[X]} {a r : R} {k : ℕ}
    (hk : k ≤ f.natDegree + g.natDegree)
    (hf : ∀ i < k, r ∣ (f.taylor a).coeff i) (hg : ∀ j < k, r ∣ (g.taylor a).coeff j) :
    r ^ k ∣ resultant f g := by
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
  exact resultant_mem_pow_of_taylor_coeff_mem hk
    (fun i hi ↦ Ideal.mem_span_singleton.mpr (hf i hi))
    (fun j hj ↦ Ideal.mem_span_singleton.mpr (hg j hj))

/-- Differentiation commutes with Taylor shift: `(f.derivative).taylor a = (f.taylor a).derivative`.
-/
private theorem taylor_derivative (f : R[X]) (a : R) :
    f.derivative.taylor a = (f.taylor a).derivative := by
  simp [taylor_apply, derivative_comp]

/-- If `r` divides the first `μ` Taylor coefficients of `f` at `a` (with
`μ - 1 ≤ f.natDegree + f.derivative.natDegree`), then `r ^ (μ - 1) ∣ resultant f f.derivative`. -/
theorem pow_pred_dvd_resultant_derivative_of_dvd_taylor_coeff {f : R[X]} {a r : R} {μ : ℕ}
    (hμ : μ - 1 ≤ f.natDegree + f.derivative.natDegree)
    (hf : ∀ i < μ, r ∣ (f.taylor a).coeff i) :
    r ^ (μ - 1) ∣ resultant f f.derivative := by
  refine pow_dvd_resultant_of_dvd_taylor_coeff hμ
    (fun i hi ↦ hf i (Nat.lt_of_lt_of_le hi (Nat.sub_le μ 1))) (fun j hj ↦ ?_)
  rw [taylor_derivative, coeff_derivative]
  exact dvd_mul_of_dvd_left (hf (j + 1) (by omega)) _

end TaylorDivisibility

section FiberMultiplicity

/-- An irreducible bivariate polynomial `f : R[X][Y]` over an integral domain `R` of positive
`Y`-degree has no identically zero vertical fiber `f(x, Y)`. -/
theorem map_evalRingHom_ne_zero_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X][Y]} (hf : Irreducible f) (hdeg : 0 < f.natDegree) (x : R) :
    f.map (evalRingHom x) ≠ 0 := by
  intro hzero
  -- Every coefficient of `f` vanishes at `x`, so `C (X - C x)` divides `f`.
  have hdvd : C (X - C x) ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [dvd_iff_isRoot, IsRoot.def]
    simpa using congr_arg (fun p ↦ p.coeff i) hzero
  rcases hdvd with ⟨q, hfq⟩
  rcases hf.isUnit_or_isUnit hfq with hu | hu
  · exact not_isUnit_of_natDegree_pos (X - C x) (by simp) (isUnit_C.mp hu)
  · rw [hfq, natDegree_C_mul (X_sub_C_ne_zero x), natDegree_eq_zero_of_isUnit hu] at hdeg
    exact lt_irrefl 0 hdeg

/-- **Fiber root multiplicity bound.** For an irreducible bivariate polynomial `f : R[X][Y]` of
positive `Y`-degree over a characteristic-zero UFD `R`, the multiplicity of any `y : R` as a root
of the specialized polynomial `f(x, Y)` is at most `1` plus the multiplicity of `x` as a root of
`resultant f f.derivative`. -/
theorem rootMultiplicity_map_evalRingHom_le_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CharZero R] {f : R[X][Y]} (hf : Irreducible f)
    (hdeg : 0 < f.natDegree) (x y : R) :
    rootMultiplicity y (f.map (evalRingHom x)) ≤
      1 + rootMultiplicity x (resultant f f.derivative) := by
  set g : R[X] := f.map (evalRingHom x)
  set μ : ℕ := rootMultiplicity y g
  have hg0 : g ≠ 0 := map_evalRingHom_ne_zero_of_irreducible hf hdeg x
  have hdvd_g : (X - C y) ^ μ ∣ g := pow_rootMultiplicity_dvd g y
  have hμdeg : μ ≤ f.natDegree := by
    calc
      μ = ((X - C y) ^ μ).natDegree := by simp
      _ ≤ g.natDegree := natDegree_le_of_dvd hdvd_g hg0
      _ ≤ f.natDegree := natDegree_map_le
  -- Shift by `y`: `X ^ μ` divides `g.taylor y`, so `(f.taylor (C y)).coeff i` vanishes at `x`
  -- for every `i < μ`.
  have hdvd_taylor : X ^ μ ∣ (f.taylor (C y)).map (evalRingHom x) := by
    have ht : ((X - C y) ^ μ).taylor y ∣ g.taylor y := _root_.map_dvd (taylorAlgHom y) hdvd_g
    have hmap : (f.taylor (C y)).map (evalRingHom x) = g.taylor y := by
      simp [g, map_taylor]
    rw [hmap]
    simpa using ht
  have hcoeff : ∀ i < μ, X - C x ∣ (f.taylor (C y)).coeff i := by
    intro i hi
    rw [dvd_iff_isRoot, IsRoot.def]
    have hc := (X_pow_dvd_iff.mp hdvd_taylor) i hi
    rwa [coeff_map, coe_evalRingHom] at hc
  have hdvd_res : (X - C x) ^ (μ - 1) ∣ resultant f f.derivative :=
    pow_pred_dvd_resultant_derivative_of_dvd_taylor_coeff (by omega) hcoeff
  have hres_ne : resultant f f.derivative ≠ 0 := hf.squarefree.resultant_derivative_ne_zero
  have hle : μ - 1 ≤ rootMultiplicity x (resultant f f.derivative) :=
    (le_rootMultiplicity_iff hres_ne).mpr hdvd_res
  omega

end FiberMultiplicity

end Polynomial
