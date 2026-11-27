/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Zsqrtd.Basic
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.Algebra.Polynomial.Bivariate.Vanishing
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Algebra.Ring.Parity
import TauCeti.Algebra.Squarefree
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.InnerProductSpace.Gram.ChangeOfFamily
import TauCeti.Analysis.InnerProductSpace.Gram.Integral
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.NumberTheory.Zsqrtd.Gram

/-!
# Green's Gram determinant for jet evaluations in `ℤ√d`

For a squarefree integer `d ≠ 1` and parameters `N, R, S : ℕ` satisfying the planar-grid degree
condition `N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3`, consider the `R * S` basis
polynomials `z ^ r * z' ^ s ∈ (ℤ√d)[z', z]` (`r < R`, `s < S`) together with their jet evaluations
`∂_z ^ j P(x + y√d, x - y√d)` on the grid `{0, …, N - 1}³`. Mapping `ℤ√d` into `ℝ²` via the
weighted Euclidean pairing `2 * (a₁ a₂ + |d| b₁ b₂)` gives an `(R * S) × (R * S)` integer Gram
matrix `G`:

1. **Positivity (`1 ≤ G.det`).** Any real linear relation among the jet vectors gives a complex
   bivariate polynomial of bidegree `< (R, S)` vanishing to order `N` in `z` at `(x + y√d, x - y√d)`
   for all `x, y < N`, which is forced to vanish by
   `Polynomial.eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd`.
2. **Archimedean upper bound.** Hadamard's inequality (`Matrix.log_det_le_of_map_eq_gram`) bounds
   `log G.det` in terms of `N, R, S` and `|d|`.
3. **`p`-adic divisibility.** At every prime `p` with `jacobiSym d p = -1`, Frobenius in
   `ℤ√d / (p)` flips `√d`, so the unitriangular change of family
   `z ^ r * z' ^ s ↦ z ^ (r - p * h) * (z ^ p - z') ^ h * z' ^ s` with
   `h = min (r / p) (S - 1 - s)` preserves `G.det` (`Matrix.det_gram_sum_smul_of_det_eq_one`)
   and makes every `j`-th derivative divisible by `p ^ h`.

## Main results

* `TauCeti.exists_pos_nat_log_le_and_pow_dvd_of_jacobiSym_eq_neg_one`: existence of a positive
  natural number `D` (namely `G.det`) satisfying both the Hadamard upper bound and the simultaneous
  `p`-adic divisibilities at all primes `p` with `jacobiSym d p = -1`.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon **2610.00311** (2026), §§2–5.
-/

public section

open Finset Polynomial
open scoped InnerProductSpace

namespace TauCeti

namespace InertPrimeSum

/-! ### Jet evaluations on `{0, …, N - 1}³` and positivity of `G.det` -/

/-- Evaluation of `∂_z^j P(z, z')` at `(x + y√d, x - y√d)` for `(x, y, j) ∈ Fin N × Fin N × Fin N`.
Here `C X` is the inner variable `z'` and `X` is the outer variable `z`. -/
private noncomputable def jetEval (d : ℤ) (N : ℕ) (P : (ℤ√d)[X][X])
    (k : Fin N × Fin N × Fin N) : ℤ√d :=
  (Polynomial.derivative^[k.2.2.val]
    (P.map (Polynomial.evalRingHom ⟨k.1.val, -(k.2.1.val : ℤ)⟩))).eval
      ⟨k.1.val, (k.2.1.val : ℤ)⟩

private theorem jetEval_sum (d : ℤ) (N : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (P : ι → (ℤ√d)[X][X]) (k : Fin N × Fin N × Fin N) :
    jetEval d N (∑ i ∈ s, c i • P i) k = ∑ i ∈ s, c i • jetEval d N (P i) k := by
  simp only [jetEval, zsmul_eq_mul, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_intCast,
    iterate_derivative_sum, iterate_derivative_intCast_mul, eval_finsetSum, eval_mul, eval_intCast]

/-- The monomial `z ^ r * z' ^ s` in `(ℤ√d)[z', z]`. -/
private noncomputable def basePoly (d : ℤ) {R S : ℕ} (i : Fin R × Fin S) : (ℤ√d)[X][X] :=
  Polynomial.C (Polynomial.X ^ i.2.val) * Polynomial.X ^ i.1.val

private noncomputable def baseFam (d : ℤ) (N R S : ℕ) (i : Fin R × Fin S) :
    Fin N × Fin N × Fin N → ℤ√d :=
  jetEval d N (basePoly d i)

private noncomputable def baseVec (d : ℤ) (N R S : ℕ) (i : Fin R × Fin S) :
    EuclideanSpace ℝ ((Fin N × Fin N × Fin N) × Fin 2) :=
  Zsqrtd.famToLp d _ (baseFam d N R S i)

private theorem jetEval_basePoly_eq (d : ℤ) (N : ℕ) {R S : ℕ} (i : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    baseFam d N R S i k =
      (⟨k.1.val, -(k.2.1.val : ℤ)⟩ : ℤ√d) ^ i.2.val *
        (i.1.val.descFactorial k.2.2.val : ℤ√d) *
        (⟨k.1.val, (k.2.1.val : ℤ)⟩ : ℤ√d) ^ (i.1.val - k.2.2.val) := by
  have hbase : basePoly d i =
      Polynomial.monomial i.1.val (Polynomial.monomial i.2.val (1 : ℤ√d)) := by
    simp [basePoly, ← C_mul_X_pow_eq_monomial]
  rw [baseFam, jetEval, hbase, eval_iterate_derivative_map_monomial_monomial, one_mul]

/-- Extracting the complex jet relation from a real linear dependence among `baseVec`. -/
private theorem sum_embPos_baseFam_eq_zero_of_sum_smul_eq_zero {d : ℤ} (hd0 : d ≠ 0)
    {N R S : ℕ} {c : Fin R × Fin S → ℝ}
    (hc : ∑ i : Fin R × Fin S, c i • baseVec d N R S i = 0)
    (k : Fin N × Fin N × Fin N) :
    ∑ i : Fin R × Fin S, (c i : ℂ) * Zsqrtd.embPos d (baseFam d N R S i k) = 0 := by
  have h0 := congrArg (fun w : EuclideanSpace ℝ _ ↦ w.ofLp (k, 0)) hc
  have h1 := congrArg (fun w : EuclideanSpace ℝ _ ↦ w.ofLp (k, 1)) hc
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply, Pi.smul_apply,
    Pi.zero_apply, baseVec, Zsqrtd.famToLp_ofLp_zero, Zsqrtd.famToLp_ofLp_one,
    smul_eq_mul] at h0 h1
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hsd : Real.sqrt (2 * (d.natAbs : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by positivity [Int.natAbs_pos.mpr hd0])
  have hre : ∑ i : Fin R × Fin S, c i * ((baseFam d N R S i k).re : ℝ) = 0 := by
    refine mul_left_cancel₀ hs2 ?_
    rw [Finset.mul_sum, mul_zero, ← h0]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have him : ∑ i : Fin R × Fin S, c i * ((baseFam d N R S i k).im : ℝ) = 0 := by
    refine mul_left_cancel₀ hsd ?_
    rw [Finset.mul_sum, mul_zero, ← h1]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  calc ∑ i : Fin R × Fin S, (c i : ℂ) * Zsqrtd.embPos d (baseFam d N R S i k)
      = (∑ i, (c i : ℂ) * ((baseFam d N R S i k).re : ℂ)) +
          Complex.sqrt d * ∑ i, (c i : ℂ) * ((baseFam d N R S i k).im : ℂ) := by
        simp only [Zsqrtd.embPos_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = 0 := by
        have hreC : ∑ i, (c i : ℂ) * ((baseFam d N R S i k).re : ℂ) = 0 := mod_cast hre
        have himC : ∑ i, (c i : ℂ) * ((baseFam d N R S i k).im : ℂ) = 0 := mod_cast him
        simp [hreC, himC]

private noncomputable def relationPoly {R S : ℕ} (c : Fin R × Fin S → ℝ) : ℂ[X][X] :=
  ∑ r : Fin R, Polynomial.monomial r.val (∑ s : Fin S, Polynomial.monomial s.val (c (r, s) : ℂ))

private theorem coeff_coeff_relationPoly {R S : ℕ} (c : Fin R × Fin S → ℝ) (i : Fin R × Fin S) :
    ((relationPoly c).coeff i.1.val).coeff i.2.val = (c i : ℂ) := by
  simp only [relationPoly, finsetSum_coeff, coeff_monomial_apply, ← Fin.ext_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private theorem natDegree_relationPoly_le {R S : ℕ} (c : Fin R × Fin S → ℝ) :
    (relationPoly c).natDegree ≤ R - 1 :=
  (natDegree_sum_le _ _).trans (Finset.sup_le fun r _ ↦ natDegree_monomial_le _ |>.trans (by omega))

private theorem natDegree_coeff_relationPoly_le {R S : ℕ} (c : Fin R × Fin S → ℝ) (n : ℕ) :
    ((relationPoly c).coeff n).natDegree ≤ S - 1 := by
  rw [relationPoly, finsetSum_coeff]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun r _ ↦ ?_)
  simp only [Function.comp_apply, coeff_monomial_apply]
  split_ifs
  · exact (natDegree_sum_le _ _).trans (Finset.sup_le fun s _ ↦
      natDegree_monomial_le _ |>.trans (by omega))
  · simp

private theorem dvd_map_evalRingHom_relationPoly {d : ℤ} (hd0 : d ≠ 0) {N R S : ℕ}
    {c : Fin R × Fin S → ℝ} (hc : ∑ i : Fin R × Fin S, c i • baseVec d N R S i = 0)
    {nx ny : ℕ} (hnx : nx < N) (hny : ny < N) :
    (X - C ((nx : ℂ) + (ny : ℂ) * Complex.sqrt d)) ^ N ∣
      (relationPoly c).map (evalRingHom ((nx : ℂ) - (ny : ℂ) * Complex.sqrt d)) := by
  rw [X_sub_C_pow_dvd_iff_forall_eval_iterate_derivative_eq_zero]
  intro j hj
  have hjet := sum_embPos_baseFam_eq_zero_of_sum_smul_eq_zero hd0 hc (⟨nx, hnx⟩, ⟨ny, hny⟩, ⟨j, hj⟩)
  calc (derivative^[j]
        ((relationPoly c).map (evalRingHom ((nx : ℂ) - (ny : ℂ) * Complex.sqrt d)))).eval
          ((nx : ℂ) + (ny : ℂ) * Complex.sqrt d)
      = ∑ i : Fin R × Fin S,
          (c i : ℂ) * Zsqrtd.embPos d (baseFam d N R S i (⟨nx, hnx⟩, ⟨ny, hny⟩, ⟨j, hj⟩)) := by
        have hrel : relationPoly c =
            ∑ r : Fin R, ∑ s : Fin S,
              Polynomial.monomial r.val (Polynomial.monomial s.val (c (r, s) : ℂ)) := by
          simp only [relationPoly, map_sum]
        rw [hrel, Fintype.sum_prod_type]
        simp only [Polynomial.map_sum, iterate_derivative_sum, eval_finsetSum,
          eval_iterate_derivative_map_monomial_monomial]
        refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
        simp only [jetEval_basePoly_eq, map_mul, map_pow, map_natCast, Zsqrtd.embPos_apply,
          Int.cast_natCast, Int.cast_neg]
        ring
    _ = 0 := hjet

private noncomputable def gridFinset (N : ℕ) : Finset ℂ :=
  (Finset.range N).image Nat.cast

private theorem card_gridFinset (N : ℕ) : (gridFinset N).card = N := by
  rw [gridFinset, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- The shear `(x, y) ↦ (x + y√d, x - y√d)` carrying the grid `{0, …, N - 1}²` to the evaluation
points `(z, z')` of the jets. -/
private noncomputable def gridMatrix (d : ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, Complex.sqrt d; 1, -Complex.sqrt d]

private theorem det_gridMatrix_ne_zero {d : ℤ} (hd0 : d ≠ 0) : (gridMatrix d).det ≠ 0 := by
  have hsqrt : Complex.sqrt (d : ℂ) ≠ 0 := by simpa using hd0
  have hdet : (gridMatrix d).det = -(2 * Complex.sqrt d) := by
    rw [gridMatrix, Matrix.det_fin_two_of]
    ring
  rw [hdet, neg_ne_zero]
  exact mul_ne_zero two_ne_zero hsqrt

private theorem toLinProd_gridMatrix_natCast (d : ℤ) (nx ny : ℕ) :
    Matrix.toLinProd (gridMatrix d) ((nx : ℂ), (ny : ℂ)) =
      ((nx : ℂ) + (ny : ℂ) * Complex.sqrt d, (nx : ℂ) - (ny : ℂ) * Complex.sqrt d) := by
  simp only [Matrix.toLinProd_apply, gridMatrix, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Prod.mk.injEq]
  constructor <;> ring

private theorem gridMatrix_snd_injOn {d : ℤ} (hd : ¬ IsSquare d) (N : ℕ) :
    Set.InjOn (Prod.snd ∘ Matrix.toLinProd (gridMatrix d))
      (gridFinset N ×ˢ gridFinset N : Finset (ℂ × ℂ)) := by
  rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ heq
  rw [Finset.coe_product, Set.mem_prod] at h₁ h₂
  rcases Finset.mem_image.mp h₁.1 with ⟨nx₁, -, rfl⟩
  rcases Finset.mem_image.mp h₁.2 with ⟨ny₁, -, rfl⟩
  rcases Finset.mem_image.mp h₂.1 with ⟨nx₂, -, rfl⟩
  rcases Finset.mem_image.mp h₂.2 with ⟨ny₂, -, rfl⟩
  rw [Function.comp_apply, Function.comp_apply, toLinProd_gridMatrix_natCast,
    toLinProd_gridMatrix_natCast] at heq
  have hemb : Zsqrtd.embPos d ⟨nx₁, -(ny₁ : ℤ)⟩ = Zsqrtd.embPos d ⟨nx₂, -(ny₂ : ℤ)⟩ := by
    simpa [sub_eq_add_neg, Zsqrtd.embPos_apply] using heq
  obtain ⟨hre, him⟩ := Zsqrtd.ext_iff.mp (Zsqrtd.embPos_injective hd hemb)
  dsimp at hre him
  rw [Prod.mk.injEq]
  exact ⟨by exact_mod_cast (by omega : nx₁ = nx₂), by exact_mod_cast (by omega : ny₁ = ny₂)⟩

/-- **Fact 1: Linear independence of the jet vectors**, hence `1 ≤ G.det`. -/
private theorem linearIndependent_baseVec {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {N R S : ℕ} (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    LinearIndependent ℝ (baseVec d N R S) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set F := relationPoly c
  have hvan : ∀ q ∈ gridFinset N ×ˢ gridFinset N,
      (X - C (Matrix.toLinProd (gridMatrix d) q).1) ^ N ∣
        F.map (evalRingHom (Matrix.toLinProd (gridMatrix d) q).2) := by
    rintro ⟨x, y⟩ hq
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hq
    rcases Finset.mem_image.mp hx with ⟨nx, hnx, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ny, hny, rfl⟩
    rw [toLinProd_gridMatrix_natCast]
    exact dvd_map_evalRingHom_relationPoly hd.ne_zero hc (Finset.mem_range.mp hnx)
      (Finset.mem_range.mp hny)
  have hlt : (gridFinset N).card * (R - 1) + max N (gridFinset N).card * (S - 1) +
      2 * (R - 1) * (S - 1) < N * (gridFinset N).card ^ 2 := by
    rw [card_gridFinset, max_self]
    convert hdeg using 1 <;> ring
  have hF0 : F = 0 := eq_zero_of_forall_linearGrid_X_sub_C_pow_dvd (natDegree_relationPoly_le c)
    (natDegree_coeff_relationPoly_le c) (det_gridMatrix_ne_zero hd.ne_zero)
    (gridMatrix_snd_injOn (Int.not_isSquare_of_squarefree_of_ne_one hd hd1) N) hvan hlt
  intro i
  have hval : (F.coeff i.1.val).coeff i.2.val = (c i : ℂ) := coeff_coeff_relationPoly c i
  exact Complex.ofReal_eq_zero.mp (hval.symm.trans (by simp [hF0]))

private theorem one_le_det_intGram {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {N R S : ℕ} (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    1 ≤ (Zsqrtd.intGram d (baseFam d N R S)).det :=
  Matrix.one_le_det_of_map_eq_gram (Zsqrtd.map_intGram_eq_gram d (baseFam d N R S))
    (linearIndependent_baseVec hd hd1 hdeg)

/-! ### Archimedean upper bound on `log G.det` -/

private theorem one_le_two_mul_mul_sqrt_natAbs {d : ℤ} (hd0 : d ≠ 0) {N : ℕ} (hN : 0 < N) :
    (1 : ℝ) ≤ 2 * N * Real.sqrt d.natAbs := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq1 : (1 : ℝ) ≤ Real.sqrt d.natAbs := Real.one_le_sqrt_natAbs hd0
  nlinarith

private theorem norm_emb_baseFam_le {d : ℤ} (hd0 : d ≠ 0) {N R S : ℕ}
    (i : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
    ‖Zsqrtd.embPos d (baseFam d N R S i k)‖ ≤
        (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.val + i.2.val) ∧
      ‖Zsqrtd.embNeg d (baseFam d N R S i k)‖ ≤
        (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.val + i.2.val) := by
  have hN : 0 < N := Nat.zero_lt_of_lt k.1.isLt
  have hR : 0 < R := Nat.zero_lt_of_lt i.1.isLt
  have h2Nd_ge : (1 : ℝ) ≤ 2 * N * Real.sqrt d.natAbs := one_le_two_mul_mul_sqrt_natAbs hd0 hN
  have hsq1 : (1 : ℝ) ≤ Real.sqrt d.natAbs := Real.one_le_sqrt_natAbs hd0
  have hpt (a b : ℤ) (ha : |a| ≤ N) (hb : |b| ≤ N) :
      |(a : ℝ)| + |(b : ℝ)| * Real.sqrt d.natAbs ≤ 2 * N * Real.sqrt d.natAbs := by
    have haR : |(a : ℝ)| ≤ N := by exact_mod_cast ha
    have hbR : |(b : ℝ)| ≤ N := by exact_mod_cast hb
    nlinarith
  have hk1 : |(k.1.val : ℤ)| ≤ N := abs_le.mpr ⟨by omega, mod_cast k.1.isLt.le⟩
  have hk2 : |(k.2.1.val : ℤ)| ≤ N := abs_le.mpr ⟨by omega, mod_cast k.2.1.isLt.le⟩
  have hdesc : (i.1.val.descFactorial k.2.2.val : ℝ) ≤ (R : ℝ) ^ N := by
    exact_mod_cast (Nat.descFactorial_le_pow _ _).trans
      ((Nat.pow_le_pow_left i.1.isLt.le _).trans (Nat.pow_le_pow_right hR k.2.2.isLt.le))
  have hbound (φ : ℤ√d →+* ℂ)
      (hnorm : ∀ u : ℤ√d, ‖φ u‖ ≤ |(u.re : ℝ)| + |(u.im : ℝ)| * Real.sqrt d.natAbs) :
      ‖φ (baseFam d N R S i k)‖ ≤
        (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.val + i.2.val) := by
    rw [jetEval_basePoly_eq, map_mul, map_mul, map_pow, map_pow, map_natCast, norm_mul, norm_mul,
      norm_pow, norm_pow, Complex.norm_natCast]
    have hp1 : ‖φ ⟨k.1.val, -(k.2.1.val : ℤ)⟩‖ ≤ 2 * N * Real.sqrt d.natAbs :=
      (hnorm _).trans (hpt _ _ hk1 (by rw [abs_neg]; exact hk2))
    have hp2 : ‖φ ⟨k.1.val, (k.2.1.val : ℤ)⟩‖ ≤ 2 * N * Real.sqrt d.natAbs :=
      (hnorm _).trans (hpt _ _ hk1 hk2)
    calc ‖φ ⟨k.1.val, -k.2.1.val⟩‖ ^ i.2.val * i.1.val.descFactorial k.2.2.val *
            ‖φ ⟨k.1.val, k.2.1.val⟩‖ ^ (i.1.val - k.2.2.val)
        ≤ (2 * N * Real.sqrt d.natAbs) ^ i.2.val * (R : ℝ) ^ N *
            (2 * N * Real.sqrt d.natAbs) ^ (i.1.val - k.2.2.val) := by gcongr
      _ = (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.val - k.2.2.val + i.2.val) := by
          rw [pow_add]; ring
      _ ≤ (R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.val + i.2.val) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h2Nd_ge (by omega)) (by positivity)
  exact ⟨hbound (Zsqrtd.embPos d) (Zsqrtd.norm_embPos_le d),
    hbound (Zsqrtd.embNeg d) (Zsqrtd.norm_embNeg_le d)⟩

private theorem two_mul_log_norm_baseVec_le {d : ℤ} (hd0 : d ≠ 0) {N R S : ℕ}
    (hN : 0 < N) {i : Fin R × Fin S} (hi : baseVec d N R S i ≠ 0) :
    2 * Real.log ‖baseVec d N R S i‖ ≤
      Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R +
        2 * ((i.1.val : ℝ) + i.2.val) * Real.log (2 * N * Real.sqrt d.natAbs) := by
  have hR : 0 < R := Nat.zero_lt_of_lt i.1.isLt
  have hv0 : 0 < ‖baseVec d N R S i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hi)
  have hsq : ‖baseVec d N R S i‖ ^ 2 ≤
      2 * (N : ℝ) ^ 3 * ((R : ℝ) ^ N) ^ 2 *
        ((2 * N * Real.sqrt d.natAbs) ^ (i.1.val + i.2.val)) ^ 2 := by
    rw [baseVec, Zsqrtd.norm_sq_famToLp]
    calc ∑ k : Fin N × Fin N × Fin N,
            (‖Zsqrtd.embPos d (baseFam d N R S i k)‖ ^ 2 +
              ‖Zsqrtd.embNeg d (baseFam d N R S i k)‖ ^ 2)
        ≤ ∑ _k : Fin N × Fin N × Fin N,
            2 * ((R : ℝ) ^ N * (2 * N * Real.sqrt d.natAbs) ^ (i.1.val + i.2.val)) ^ 2 := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          obtain ⟨h1, h2⟩ := norm_emb_baseFam_le hd0 i k
          nlinarith [sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h1,
            sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h2]
      _ = 2 * (N : ℝ) ^ 3 * ((R : ℝ) ^ N) ^ 2 *
            ((2 * N * Real.sqrt d.natAbs) ^ (i.1.val + i.2.val)) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  have _ : (0 : ℝ) < 2 * N * Real.sqrt d.natAbs :=
    lt_of_lt_of_le zero_lt_one (one_le_two_mul_mul_sqrt_natAbs hd0 hN)
  have hlog := Real.log_le_log hv0 hsq
  rw [Real.log_pow, Nat.cast_ofNat, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **Fact 2: Hadamard upper bound on `log G.det`.** -/
private theorem log_det_intGram_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {N R S : ℕ} (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    Real.log ((Zsqrtd.intGram d (baseFam d N R S)).det : ℝ) ≤
      (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
        (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt d.natAbs) := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hdeg
  have hlin := linearIndependent_baseVec hd hd1 hdeg
  have hfin_sq (n : ℕ) : ∑ r : Fin n, (2 * (r.val : ℝ)) ≤ (n : ℝ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ ↦ 2 * (r : ℝ)), ← Finset.mul_sum,
      mul_comm, Finset.sum_range_natCast_mul_two]
    nlinarith
  have hsum_idx : ∑ i : Fin R × Fin S, 2 * ((i.1.val : ℝ) + i.2.val) ≤ (R : ℝ) * S * (R + S) := by
    rw [Fintype.sum_prod_type]
    have hsplit : (∑ r : Fin R, ∑ s : Fin S, 2 * ((r.val : ℝ) + s.val)) =
        (S : ℝ) * (∑ r : Fin R, 2 * (r.val : ℝ)) + (R : ℝ) * (∑ s : Fin S, 2 * (s.val : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    rw [hsplit]
    nlinarith [hfin_sq R, hfin_sq S]
  calc Real.log ((Zsqrtd.intGram d (baseFam d N R S)).det : ℝ)
      ≤ ∑ i : Fin R × Fin S, 2 * Real.log ‖baseVec d N R S i‖ :=
        Matrix.log_det_le_of_map_eq_gram (Zsqrtd.map_intGram_eq_gram d (baseFam d N R S)) hlin
    _ ≤ ∑ i : Fin R × Fin S,
          (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R +
            2 * ((i.1.val : ℝ) + i.2.val) * Real.log (2 * N * Real.sqrt d.natAbs)) :=
        Finset.sum_le_sum fun i _ ↦
          two_mul_log_norm_baseVec_le hd.ne_zero hN (hlin.ne_zero i)
    _ = (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (∑ i : Fin R × Fin S, 2 * ((i.1.val : ℝ) + i.2.val)) *
            Real.log (2 * N * Real.sqrt d.natAbs) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
        push_cast; ring
    _ ≤ (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt d.natAbs) := by
        have hlog_nn : 0 ≤ Real.log (2 * N * Real.sqrt d.natAbs) :=
          Real.log_nonneg (one_le_two_mul_mul_sqrt_natAbs hd.ne_zero hN)
        nlinarith

/-! ### `p`-adic divisibility of `G.det` at inert primes -/

/-- Exponent `h = min (r / p) (S - 1 - s)` and the modified polynomial
`z ^ (r - p * h) * (z ^ p - z') ^ h * z' ^ s`. -/
private def shiftExp (p S : ℕ) (i : Fin R × Fin S) : ℕ :=
  min (i.1.val / p) (S - 1 - i.2.val)

private theorem mul_shiftExp_le (p S : ℕ) (i : Fin R × Fin S) :
    p * shiftExp p S i ≤ i.1.val :=
  (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le i.1.val p)

private theorem shift_fst_lt {p R S : ℕ} (hp : 0 < p) {i : Fin R × Fin S} {m : ℕ}
    (hm : m < shiftExp p S i) :
    i.1.val - p * shiftExp p S i + p * m < i.1.val := by
  have := mul_shiftExp_le p S i; have := Nat.mul_lt_mul_of_pos_left hm hp; omega

private noncomputable def shiftPoly (d : ℤ) (p : ℕ) {R S : ℕ} (i : Fin R × Fin S) :
    (ℤ√d)[X][X] :=
  let h := shiftExp p S i
  Polynomial.C (Polynomial.X ^ i.2.val) *
    (Polynomial.X ^ (i.1.val - p * h) * (Polynomial.X ^ p - Polynomial.C Polynomial.X) ^ h)

private noncomputable def shiftFam (d : ℤ) (p N R S : ℕ) (i : Fin R × Fin S) :
    Fin N × Fin N × Fin N → ℤ√d :=
  jetEval d N (shiftPoly d p i)

private def shiftIdx {p R S : ℕ} (hp : 0 < p) (i : Fin R × Fin S)
    (m : Fin (shiftExp p S i)) : Fin R × Fin S :=
  (⟨i.1.val - p * shiftExp p S i + p * m.val, (shift_fst_lt hp m.isLt).trans i.1.isLt⟩,
   ⟨i.2.val + (shiftExp p S i - m.val), by
     have : shiftExp p S i ≤ S - 1 - i.2.val := min_le_right _ _
     have := i.2.isLt; omega⟩)

private theorem shiftPoly_term_eq (d : ℤ) {p R S : ℕ} (hp : 0 < p) (i : Fin R × Fin S)
    (m : Fin (shiftExp p S i)) :
    Polynomial.C (Polynomial.X ^ i.2.val : (ℤ√d)[X]) *
        (Polynomial.X ^ (i.1.val - p * shiftExp p S i) *
          ((-1 : (ℤ√d)[X][X]) ^ (m.val + shiftExp p S i) *
            (Polynomial.X ^ p) ^ m.val *
            (Polynomial.C (Polynomial.X : (ℤ√d)[X])) ^ (shiftExp p S i - m.val) *
            ((shiftExp p S i).choose m.val : (ℤ√d)[X][X]))) =
      ((-1 : ℤ) ^ (shiftExp p S i - m.val) * (shiftExp p S i).choose m.val) •
        basePoly d (shiftIdx hp i m) := by
  rw [TauCeti.neg_one_pow_add_eq_sub (α := (ℤ√d)[X][X]) m.isLt.le]
  simp only [basePoly, shiftIdx, pow_add, C_mul, pow_mul, ← C_pow, zsmul_eq_mul]
  push_cast
  ring

private theorem shiftPoly_eq_add_sum (d : ℤ) {p R S : ℕ} (hp : 0 < p) (i : Fin R × Fin S) :
    shiftPoly d p i =
      basePoly d i +
        ∑ m : Fin (shiftExp p S i),
          ((-1 : ℤ) ^ (shiftExp p S i - m.val) * (shiftExp p S i).choose m.val) •
            basePoly d (shiftIdx hp i m) := by
  have htop : Polynomial.C (Polynomial.X ^ i.2.val : (ℤ√d)[X]) *
      (Polynomial.X ^ (i.1.val - p * shiftExp p S i) *
        (Polynomial.X ^ p) ^ shiftExp p S i) = basePoly d i := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel (mul_shiftExp_le p S i), basePoly]
  have hsub_pow : (X ^ p - C X : (ℤ√d)[X][X]) ^ shiftExp p S i =
      (∑ m ∈ Finset.range (shiftExp p S i),
        (-1 : (ℤ√d)[X][X]) ^ (m + shiftExp p S i) * (X ^ p) ^ m *
          (C (X : (ℤ√d)[X])) ^ (shiftExp p S i - m) *
          ((shiftExp p S i).choose m : (ℤ√d)[X][X])) +
        (X ^ p) ^ shiftExp p S i := by
    rw [sub_pow, Finset.sum_range_succ,
      TauCeti.neg_one_pow_add_eq_sub (α := (ℤ√d)[X][X]) le_rfl]
    simp
  dsimp only [shiftPoly]
  rw [hsub_pow, mul_add, mul_add, htop, add_comm _ (basePoly d i), Finset.mul_sum,
    Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl fun m _ ↦ shiftPoly_term_eq d hp i m

private def shiftMatrix {p R S : ℕ} (hp : 0 < p) : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
  Matrix.of fun i j ↦
    (if i = j then 1 else 0) +
      ∑ m : Fin (shiftExp p S i),
        if j = shiftIdx hp i m then
          (-1 : ℤ) ^ (shiftExp p S i - m.val) * (shiftExp p S i).choose m.val
        else 0

private theorem shiftPoly_eq_sum_basePoly (d : ℤ) {p R S : ℕ} (hp : 0 < p) (i : Fin R × Fin S) :
    shiftPoly d p i = ∑ j : Fin R × Fin S, shiftMatrix hp i j • basePoly d j := by
  rw [shiftPoly_eq_add_sum d hp i]
  simp only [shiftMatrix, Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private theorem det_shiftMatrix_eq_one {p R S : ℕ} (hp : 0 < p) :
    (shiftMatrix (R := R) (S := S) hp).det = 1 := by
  have hno_match {i j : Fin R × Fin S} (hij : i.1.val ≤ j.1.val) (m : Fin (shiftExp p S i)) :
      j ≠ shiftIdx hp i m := by
    intro h; subst h; exact Nat.not_lt.mpr hij (shift_fst_lt hp m.isLt)
  let rank : Fin R × Fin S → OrderDual (Fin R ×ₗ Fin S) := OrderDual.toDual ∘ toLex
  have htri : (shiftMatrix (R := R) (S := S) hp).BlockTriangular rank := by
    intro i j hij
    have hij' := OrderDual.toDual_lt_toDual.mp hij
    have hi_le_j : i.1.val ≤ j.1.val := by
      rcases Prod.Lex.lt_iff.mp hij' with h1 | ⟨h1, _⟩
      · exact Nat.le_of_lt h1
      · exact le_of_eq (congrArg Fin.val h1)
    have hne : i ≠ j := fun h ↦ lt_irrefl _ (h ▸ hij')
    simp only [shiftMatrix, Matrix.of_apply, hne, ↓reduceIte, zero_add]
    exact Finset.sum_eq_zero fun m _ ↦ ite_eq_right_iff.mpr fun h ↦ absurd h (hno_match hi_le_j m)
  rw [htri.det_eq_prod_diag (OrderDual.toDual.injective.comp toLex.injective)]
  exact Finset.prod_eq_one fun i _ ↦ by
    simp [shiftMatrix, Finset.sum_eq_zero fun m _ ↦
      ite_eq_right_iff.mpr fun h ↦ absurd h (hno_match le_rfl m)]

/-- Unitriangularity of the change of basis `basePoly ↦ shiftPoly` in reverse lexicographic
order preserves the integer Gram determinant. -/
private theorem det_intGram_shiftFam_eq (d : ℤ) {p N R S : ℕ} (hp : 0 < p) :
    (Zsqrtd.intGram d (shiftFam d p N R S)).det = (Zsqrtd.intGram d (baseFam d N R S)).det := by
  let U : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ := shiftMatrix hp
  have hvec (i : Fin R × Fin S) :
      Zsqrtd.famToLp d _ (shiftFam d p N R S i) =
        ∑ j : Fin R × Fin S, (U i j : ℝ) • baseVec d N R S j := by
    have hfam : shiftFam d p N R S i = ∑ j, U i j • baseFam d N R S j := funext fun k ↦ by
      simp only [shiftFam, shiftPoly_eq_sum_basePoly d hp i, U, baseFam, jetEval_sum,
        Finset.sum_apply, Pi.smul_apply]
    rw [hfam]
    simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul, baseVec]
  have hdetU : (U.map (Int.castRingHom ℝ)).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_shiftMatrix_eq_one hp, map_one]
  have hR : ((Zsqrtd.intGram d (shiftFam d p N R S)).det : ℝ) =
      ((Zsqrtd.intGram d (baseFam d N R S)).det : ℝ) := by
    rw [Zsqrtd.intCast_det_intGram, Zsqrtd.intCast_det_intGram, funext hvec]
    exact Matrix.det_gram_sum_smul_of_det_eq_one hdetU (baseVec d N R S)
  exact_mod_cast hR

/-- Every jet evaluation of `shiftPoly d p i` at an inert prime `p` is divisible by `p ^ h`. -/
private theorem pow_dvd_shiftFam {d : ℤ} {p : ℕ} (hp : p.Prime)
    (hjac : jacobiSym d p = -1) (N R S : ℕ) (i : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    (p : ℤ√d) ^ shiftExp p S i ∣ shiftFam d p N R S i k := by
  rw [shiftFam, jetEval]
  set h := shiftExp p S i
  set α : ℤ√d := ⟨k.1.val, (k.2.1.val : ℤ)⟩
  set α_bar : ℤ√d := ⟨k.1.val, -(k.2.1.val : ℤ)⟩
  set f : (ℤ√d)[X] := (shiftPoly d p i).map (evalRingHom α_bar)
  rw [eval_iterate_derivative_eq_factorial_mul, ← taylor_coeff]
  have hf : f = C (α_bar ^ i.2.val) * X ^ (i.1.val - p * h) * (X ^ p - C α_bar) ^ h := by
    simp [f, shiftPoly, h, mul_assoc]
  obtain ⟨A, hA⟩ := exists_taylor_X_pow_sub_C_eq_C_mul_add_X_pow hp
    (by simpa [α, α_bar, Zsqrtd.star_mk] using
      Zsqrtd.natCast_dvd_pow_sub_star_of_jacobiSym_eq_neg_one hp hjac α)
  have htf : taylor α f =
      C (α_bar ^ i.2.val) * (X + C α) ^ (i.1.val - p * h) * (X ^ p + C (p : ℤ√d) * A) ^ h := by
    rw [hf, taylor_mul, taylor_mul, taylor_C, taylor_X_pow, taylor_pow, hA,
      add_comm (C (p : ℤ√d) * A) (X ^ p)]
  rw [htf]
  exact pow_dvd_factorial_mul_coeff_mul_X_pow_add_C_mul hp.pos h k.2.2.val
    (C (α_bar ^ i.2.val) * (X + C α) ^ (i.1.val - p * h)) A

/-- **Fact 3: `p`-adic divisibility of `G.det`** at inert primes. -/
private theorem pow_dvd_det_intGram {d : ℤ} {p : ℕ} (hp : p.Prime)
    (hjac : jacobiSym d p = -1) (N R S : ℕ) :
    ((p : ℤ) ^ (2 * ∑ i : Fin R × Fin S, shiftExp p S i)) ∣
      (Zsqrtd.intGram d (baseFam d N R S)).det := by
  rw [← det_intGram_shiftFam_eq d hp.pos]
  have hdvd := Matrix.prod_mul_prod_dvd_det_of_dvd (Zsqrtd.intGram d (shiftFam d p N R S))
    (fun i ↦ (p : ℤ) ^ shiftExp p S i) (fun j ↦ (p : ℤ) ^ shiftExp p S j)
    fun i j ↦ Zsqrtd.mul_dvd_intGram d
      (fun k ↦ by exact_mod_cast pow_dvd_shiftFam hp hjac N R S i k)
      (fun k ↦ by exact_mod_cast pow_dvd_shiftFam hp hjac N R S j k)
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← two_mul] at hdvd
  exact hdvd

end InertPrimeSum

/-- **Green's Gram determinant for jet evaluations in `ℤ√d`.** For a squarefree integer `d ≠ 1`
and parameters `N, R, S : ℕ` satisfying `N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3`,
there exists a positive natural number `D` satisfying both the Hadamard upper bound
`log D ≤ R * S * (log (2 * N ^ 3) + 2 * N * log R) + R * S * (R + S) * log (2 * N * √|d|)`
and, at every prime `p` with `jacobiSym d p = -1`, the `p`-adic divisibility
`p ^ (2 * ∑ i : Fin R × Fin S, min (i.1 / p) (S - 1 - i.2)) ∣ D`. -/
theorem exists_pos_nat_log_le_and_pow_dvd_of_jacobiSym_eq_neg_one {d : ℤ} (hd : Squarefree d)
    (hd1 : d ≠ 1) {N R S : ℕ}
    (hdeg : N * ((R - 1) + (S - 1)) + 2 * (R - 1) * (S - 1) < N ^ 3) :
    ∃ D : ℕ, 0 < D ∧
      Real.log (D : ℝ) ≤
        (R : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log R) +
          (R : ℝ) * S * (R + S) * Real.log (2 * N * Real.sqrt d.natAbs) ∧
      ∀ p : ℕ, p.Prime → jacobiSym d p = -1 →
        p ^ (2 * ∑ i : Fin R × Fin S, min (i.1.val / p) (S - 1 - i.2.val)) ∣ D := by
  open InertPrimeSum in
  have h1 : 1 ≤ (Zsqrtd.intGram d (baseFam d N R S)).det := one_le_det_intGram hd hd1 hdeg
  set D := (Zsqrtd.intGram d (baseFam d N R S)).det.toNat
  have hD_cast : (D : ℤ) = (Zsqrtd.intGram d (baseFam d N R S)).det :=
    Int.toNat_of_nonneg (by omega)
  have hD_real : (D : ℝ) = ((Zsqrtd.intGram d (baseFam d N R S)).det : ℝ) := mod_cast hD_cast
  refine ⟨D, by omega, ?_, fun p hp hjac ↦ ?_⟩
  · rw [hD_real]
    exact log_det_intGram_le hd hd1 hdeg
  · rw [← Int.ofNat_dvd, Nat.cast_pow, hD_cast]
    exact pow_dvd_det_intGram hp hjac N R S

end TauCeti
