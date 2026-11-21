/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Algebra.Squarefree
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.NumberTheory.NumberField.Quadratic.EmbeddingBound
import TauCeti.NumberTheory.QuadraticOrder.Frobenius
import TauCeti.NumberTheory.QuadraticOrder.Reduction
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# Gram determinant method for inert primes in quadratic orders

For a squarefree integer `d ≠ 1` and grid parameters `R, S, N` satisfying
`N R + N S + 2 R S < N ^ 3`, this file forms the `R S` vectors of `z`-derivatives
`∂_z^j (z ^ r z' ^ s)` (`0 ≤ j < N`) evaluated on the quadratic grid `(x + yω, x - yω)`
(`0 ≤ x, y < N`) in `QuadraticAlgebra ℤ d 0`, embeds them into `ℝ²` via `(a, √|d| b)`, and
compares the archimedean upper bound on `log (det G_ℤ)` with the `p`-adic lower bound at odd inert
primes `p` (`jacobiSym d p = -1`).

## Main results

* `TauCeti.sum_min_div_log_le_of_jacobiSym_eq_neg_one`:
  `∑_{p ∈ P'} 2 (∑_{r < R, s < S} min (r / p) (S - 1 - s)) log p ≤ R S (3 log N + 2 N log R) +`
  `R S (R + S) log (2 N √|d|)` whenever `N R + N S + 2 R S < N ^ 3` and every `p ∈ P'` is an
  odd prime with `jacobiSym d p = -1`.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, §§2–6.
* OpenAI, *Uniform exclusion of Landau–Siegel zeros*, October 2026.
-/

public section

open scoped Polynomial Matrix QuadraticAlgebra

namespace TauCeti

/-! ### Quadratic grid injectivity and Schwartz–Zippel bound -/

section GridSchwartzZippel

/-- For squarefree `d ≠ 1`, the conjugate coordinate `(x, y) ↦ x - y √d` is injective on `ℕ × ℕ`. -/
private theorem quadGrid_snd_injective {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    Function.Injective fun xy : ℕ × ℕ ↦
      (xy.1 : ℂ) - (xy.2 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  have hinj := (QuadraticAlgebra.algHom_injective_iff
    (QuadraticAlgebra.negSqrtEmbedding (d : ℚ))).mpr
      (not_isSquare_intCast_of_squarefree_of_ne_one hd hd1)
  have heq : QuadraticAlgebra.negSqrtEmbedding (d : ℚ) ⟨(x₁ : ℚ), (y₁ : ℚ)⟩ =
      QuadraticAlgebra.negSqrtEmbedding (d : ℚ) ⟨(x₂ : ℚ), (y₂ : ℚ)⟩ := by
    simpa [QuadraticAlgebra.negSqrtEmbedding_apply] using h
  have hqa := QuadraticAlgebra.ext_iff.mp (hinj heq)
  exact Prod.ext (Nat.cast_injective hqa.1) (Nat.cast_injective hqa.2)

/-- Linear change of variables `z ↦ X₀ + s X₁`, `z' ↦ X₀ - s X₁` from `ℂ[X][X]` to
`MvPolynomial (Fin 2) ℂ`. -/
private noncomputable def toMvQuad (s : ℂ) : ℂ[X][X] →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1,
    MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1]).comp
    (Polynomial.Bivariate.equivMvPolynomial ℂ).toAlgHom

private theorem eval_toMvQuad (s x y : ℂ) (g : ℂ[X][X]) :
    MvPolynomial.eval ![x, y] (toMvQuad s g) =
      (g.map (Polynomial.evalRingHom (x - y * s))).eval (x + y * s) := by
  rw [Polynomial.map_evalRingHom_eval, ← Polynomial.coe_aevalAeval_eq_evalEval,
    ← MvPolynomial.aeval_eq_eval]
  change (MvPolynomial.aeval ![x, y])
    ((MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1,
      MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1])
      (Polynomial.Bivariate.equivMvPolynomial ℂ g)) = _
  rw [MvPolynomial.comp_aeval_apply]
  have hcomp : (MvPolynomial.aeval fun i : Fin 2 ↦ (MvPolynomial.aeval ![x, y])
      (![MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1,
        MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1] i)).comp
      (Polynomial.Bivariate.equivMvPolynomial ℂ).toAlgHom =
      Polynomial.aevalAeval (x - y * s) (x + y * s) := by
    have h := (Polynomial.aevalAevalEquiv ℂ ℂ).apply_symm_apply
      ((MvPolynomial.aeval fun i : Fin 2 ↦ (MvPolynomial.aeval ![x, y])
        (![MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1,
          MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1] i)).comp
        (Polynomial.Bivariate.equivMvPolynomial ℂ).toAlgHom)
    simpa [Polynomial.aevalAevalEquiv_apply, mul_comm] using h.symm
  exact congrArg (· g) hcomp

private theorem toMvQuad_ne_zero {s : ℂ} (hs : s ≠ 0) {g : ℂ[X][X]} (hg : g ≠ 0) :
    toMvQuad s g ≠ 0 := by
  let inv : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.aeval
      ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * s)) * (MvPolynomial.X 1 - MvPolynomial.X 0)]
  have hinv : inv.comp (MvPolynomial.aeval
      ![MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1,
        MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1]) = AlgHom.id _ _ := by
    have hss : (MvPolynomial.C (σ := Fin 2) s) * MvPolynomial.C s⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hs, map_one]
    have h2 : (MvPolynomial.C (σ := Fin 2) (2⁻¹ : ℂ)) + MvPolynomial.C 2⁻¹ = 1 := by
      rw [← map_add]; norm_num
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i
    · have ha : inv (MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1) =
          MvPolynomial.C (2⁻¹ : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1) -
            MvPolynomial.C s * (MvPolynomial.C s⁻¹ * MvPolynomial.C 2⁻¹ *
              (MvPolynomial.X 1 - MvPolynomial.X 0)) := by simp [inv]
      simp only [Fin.isValue, Fin.zero_eta, AlgHom.comp_apply, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, AlgHom.id_apply]
      rw [ha, ← mul_assoc (MvPolynomial.C s), ← mul_assoc (MvPolynomial.C s), hss, one_mul]
      linear_combination (MvPolynomial.X 0) * h2
    · have hb : inv (MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1) =
          MvPolynomial.C (2⁻¹ : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1) +
            MvPolynomial.C s * (MvPolynomial.C s⁻¹ * MvPolynomial.C 2⁻¹ *
              (MvPolynomial.X 1 - MvPolynomial.X 0)) := by simp [inv]
      simp only [Fin.isValue, Fin.mk_one, AlgHom.comp_apply, MvPolynomial.aeval_X,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, AlgHom.id_apply]
      rw [hb, ← mul_assoc (MvPolynomial.C s), ← mul_assoc (MvPolynomial.C s), hss, one_mul]
      linear_combination (MvPolynomial.X 1) * h2
  intro h0
  have h1 := congrArg inv h0
  change inv ((MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1,
    MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1])
    (Polynomial.Bivariate.equivMvPolynomial ℂ g)) = inv 0 at h1
  rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply, map_zero] at h1
  exact hg ((Polynomial.Bivariate.equivMvPolynomial ℂ).injective (h1.trans (map_zero _).symm))

private theorem totalDegree_toMvQuad_le (s : ℂ) (g : ℂ[X][X]) :
    (toMvQuad s g).totalDegree ≤
      g.natDegree + g.support.sup fun k ↦ (g.coeff k).natDegree := by
  have hlin (ε : ℂ) : (MvPolynomial.X 0 + MvPolynomial.C ε * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp [MvPolynomial.totalDegree_X])
      ((MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X])))
  have hlin_sub : (MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    simpa [sub_eq_add_neg, MvPolynomial.C_neg] using hlin (-s)
  have hinner (p : ℂ[X]) : (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) -
      MvPolynomial.C s * MvPolynomial.X (1 : Fin 2)) p).totalDegree ≤ p.natDegree := by
    rw [Polynomial.aeval_eq_sum_range]
    refine MvPolynomial.totalDegree_finsetSum_le fun j hj ↦ ?_
    have hj' : j ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left j hlin_sub).trans (by simpa using hj'))
  have hC (p : ℂ[X]) : toMvQuad s (Polynomial.C p) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.C s * MvPolynomial.X (1 : Fin 2)) p := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add, hp, hq]
    | monomial j a =>
      simp [← Polynomial.C_mul_X_pow_eq_monomial, toMvQuad, MvPolynomial.algebraMap_eq]
  have hX : toMvQuad s Polynomial.X =
      MvPolynomial.X (0 : Fin 2) + MvPolynomial.C s * MvPolynomial.X (1 : Fin 2) := by
    simp [toMvQuad]
  conv_lhs => rw [g.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun k hk ↦ ?_
  rw [map_mul, map_pow, hC, hX]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hk' : k ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hcoeff : (g.coeff k).natDegree ≤ g.support.sup fun j ↦ (g.coeff j).natDegree := by
    by_cases hmem : k ∈ g.support
    · exact Finset.le_sup (f := fun j ↦ (g.coeff j).natDegree) hmem
    · rw [Polynomial.notMem_support_iff.mp hmem, Polynomial.natDegree_zero]; exact Nat.zero_le _
  have hpow : ((MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C s * MvPolynomial.X (1 : Fin 2)) ^ k).totalDegree ≤ g.natDegree :=
    (MvPolynomial.totalDegree_pow _ _).trans ((Nat.mul_le_mul_left k (hlin s)).trans
      (by simpa using hk'))
  exact (Nat.add_le_add ((hinner _).trans hcoeff) hpow).trans (by omega)

/-- Schwartz–Zippel zero-count bound on the `N × N` quadratic grid `(x + y s, x - y s)`. -/
private theorem card_filter_quadGrid_eval_eq_zero_le {s : ℂ} (hs : s ≠ 0) (N : ℕ)
    {g : ℂ[X][X]} (hg : g ≠ 0) :
    (Finset.univ.filter fun xy : Fin N × Fin N ↦
        (g.map (Polynomial.evalRingHom ((xy.1 : ℂ) - (xy.2 : ℂ) * s))).eval
          ((xy.1 : ℂ) + (xy.2 : ℂ) * s) = 0).card ≤
      N * (g.natDegree + g.support.sup fun k ↦ (g.coeff k).natDegree) := by
  classical
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  let S : Finset ℂ := (Finset.range N).image Nat.cast
  have hScard : S.card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  let emb : Fin N × Fin N ↪ (Fin 2 → ℂ) :=
    ⟨fun xy ↦ ![(xy.1 : ℂ), (xy.2 : ℂ)], fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h ↦ by
      have h0 : (x₁ : ℂ) = (x₂ : ℂ) := by simpa using congrFun h 0
      have h1 : (y₁ : ℂ) = (y₂ : ℂ) := by simpa using congrFun h 1
      exact Prod.ext (Fin.ext (Nat.cast_injective h0)) (Fin.ext (Nat.cast_injective h1))⟩
  have hsub : (Finset.univ.filter fun xy : Fin N × Fin N ↦
      (g.map (Polynomial.evalRingHom ((xy.1 : ℂ) - (xy.2 : ℂ) * s))).eval
        ((xy.1 : ℂ) + (xy.2 : ℂ) * s) = 0).map emb ⊆
      (Fintype.piFinset fun _ : Fin 2 ↦ S).filter
        (fun f ↦ MvPolynomial.eval f (toMvQuad s g) = 0) := by
    intro f hf
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_map.mp hf
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_, ?_⟩
    · fin_cases i
      · exact Finset.mem_image.mpr ⟨xy.1.val, Finset.mem_range.mpr xy.1.isLt, rfl⟩
      · exact Finset.mem_image.mpr ⟨xy.2.val, Finset.mem_range.mpr xy.2.isLt, rfl⟩
    · rw [show emb xy = ![(xy.1 : ℂ), (xy.2 : ℂ)] from rfl, eval_toMvQuad]
      exact (Finset.mem_filter.mp hxy).2
  have hsz := MvPolynomial.schwartz_zippel_totalDegree (toMvQuad_ne_zero hs hg) S
  rw [hScard] at hsz
  have hNpos : (0 : NNRat) < (N : NNRat) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hmul : (((Fintype.piFinset fun _ : Fin 2 ↦ S).filter
      (fun f ↦ MvPolynomial.eval f (toMvQuad s g) = 0)).card : NNRat) ≤
      (N : NNRat) * ((toMvQuad s g).totalDegree : NNRat) := by
    rw [div_le_div_iff₀ (pow_pos hNpos 2) hNpos, sq] at hsz
    exact le_of_mul_le_mul_right (by simpa [mul_assoc, mul_left_comm, mul_comm] using hsz) hNpos
  exact (Finset.card_map emb).symm.le.trans ((Finset.card_le_card hsub).trans
    ((by exact_mod_cast hmul : _ ≤ N * (toMvQuad s g).totalDegree).trans
      (Nat.mul_le_mul_left N (totalDegree_toMvQuad_le s g))))

end GridSchwartzZippel

/-! ### Grid vectors, integer Gram matrix, linear independence, and Hadamard bound -/

section GramMatrix

/-- The grid point `x + yω` in `QuadraticAlgebra ℤ d 0`. -/
private def zPt (d : ℤ) (x y : ℕ) : QuadraticAlgebra ℤ d 0 := ⟨x, y⟩

/-- The conjugate grid point `x - yω` in `QuadraticAlgebra ℤ d 0`. -/
private def zConj (d : ℤ) (x y : ℕ) : QuadraticAlgebra ℤ d 0 := ⟨x, -(y : ℤ)⟩

/-- Canonical inclusion `QuadraticAlgebra ℤ d 0 →+* QuadraticAlgebra ℚ d 0`. -/
private noncomputable def toRatQA (d : ℤ) :
    QuadraticAlgebra ℤ d 0 →+* QuadraticAlgebra ℚ (d : ℚ) 0 :=
  algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ (d : ℚ) ((0 : ℤ) : ℚ))

/-- Row `(r, s)` evaluated at `(x, y, j)`: the `j`-th `z`-derivative of `z ^ r z' ^ s` at
`(x + yω, x - yω)` in `QuadraticAlgebra ℤ d 0`. -/
private def gridVec (d : ℤ) (R S N : ℕ) (rs : Fin R × Fin S)
    (xyj : Fin N × Fin N × Fin N) : QuadraticAlgebra ℤ d 0 :=
  (rs.1.val.descFactorial xyj.2.2.val : ℤ) •
    (zPt d xyj.1.val xyj.2.1.val ^ (rs.1.val - xyj.2.2.val) *
      zConj d xyj.1.val xyj.2.1.val ^ rs.2.val)

/-- Embedding `gridVec` into `EuclideanSpace ℝ ((Fin N × Fin N × Fin N) × Fin 2)` via
`a + bω ↦ (a, √|d| b)`. -/
private noncomputable def realGridVec (d : ℤ) (R S N : ℕ) (rs : Fin R × Fin S) :
    EuclideanSpace ℝ ((Fin N × Fin N × Fin N) × Fin 2) :=
  WithLp.toLp 2 fun k ↦
    if k.2 = 0 then ((gridVec d R S N rs k.1).re : ℝ)
    else Real.sqrt |(d : ℝ)| * ((gridVec d R S N rs k.1).im : ℝ)

/-- The integer Gram matrix of `realGridVec d R S N`. -/
private def intGram (d : ℤ) (R S N : ℕ) : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
  Matrix.of fun u v ↦
    ∑ k : Fin N × Fin N × Fin N,
      ((gridVec d R S N u k).re * (gridVec d R S N v k).re +
        |d| * (gridVec d R S N u k).im * (gridVec d R S N v k).im)

private theorem intGram_map_eq_gram (d : ℤ) (R S N : ℕ) :
    (intGram d R S N).map (Int.castRingHom ℝ) = Matrix.gram ℝ (realGridVec d R S N) := by
  ext u v
  simp only [Matrix.map_apply, Int.coe_castRingHom, intGram, Matrix.of_apply, Int.cast_sum,
    Int.cast_add, Int.cast_mul, Int.cast_abs, Matrix.gram_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type (f := fun p : (Fin N × Fin N × Fin N) × Fin 2 ↦ _)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Fin.sum_univ_two, realGridVec, Fin.isValue, ↓reduceIte, one_ne_zero]
  have hsq : Real.sqrt |(d : ℝ)| * Real.sqrt |(d : ℝ)| = |(d : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  linear_combination -((gridVec d R S N u k).im : ℝ) * ((gridVec d R S N v k).im : ℝ) * hsq

private theorem det_intGram_cast (d : ℤ) (R S N : ℕ) :
    ((intGram d R S N).det : ℝ) = (Matrix.gram ℝ (realGridVec d R S N)).det := by
  rw [← intGram_map_eq_gram]
  exact RingHom.map_det (Int.castRingHom ℝ) (intGram d R S N)

private theorem sqrtEmbedding_toRatQA (d : ℤ) (α : QuadraticAlgebra ℤ d 0) :
    QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d α) =
      (α.re : ℂ) + (α.im : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) :=
  by rw [QuadraticAlgebra.sqrtEmbedding_apply]; rfl

private theorem negSqrtEmbedding_toRatQA (d : ℤ) (α : QuadraticAlgebra ℤ d 0) :
    QuadraticAlgebra.negSqrtEmbedding (d : ℚ) (toRatQA d α) =
      (α.re : ℂ) - (α.im : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) :=
  by rw [QuadraticAlgebra.negSqrtEmbedding_apply]; rfl

private theorem sqrtEmbedding_gridVec (d : ℤ) (R S N : ℕ) (rs : Fin R × Fin S)
    (xyj : Fin N × Fin N × Fin N) :
    QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d (gridVec d R S N rs xyj)) =
      (rs.1.val.descFactorial xyj.2.2.val : ℂ) *
        ((xyj.1.val : ℂ) + (xyj.2.1.val : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)) ^
          (rs.1.val - xyj.2.2.val) *
        ((xyj.1.val : ℂ) - (xyj.2.1.val : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)) ^
          rs.2.val := by
  have hz : QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d (zPt d xyj.1.val xyj.2.1.val)) =
      (xyj.1.val : ℂ) + (xyj.2.1.val : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
    simp [sqrtEmbedding_toRatQA, zPt]
  have hc : QuadraticAlgebra.sqrtEmbedding (d : ℚ)
      (toRatQA d (zConj d xyj.1.val xyj.2.1.val)) =
      (xyj.1.val : ℂ) - (xyj.2.1.val : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
    simp [sqrtEmbedding_toRatQA, zConj, sub_eq_add_neg]
  simp only [gridVec, zsmul_eq_mul, map_mul, map_pow, Int.cast_natCast, map_natCast, hz, hc]
  ring

/-- The bivariate polynomial `∑_{r, s} f(r, s) z' ^ s z ^ r` in `ℂ[X][X]` attached to `f`. -/
private noncomputable def gridPoly {R S : ℕ} (f : Fin R × Fin S → ℝ) : ℂ[X][X] :=
  ∑ rs : Fin R × Fin S,
    Polynomial.C (Polynomial.C (f rs : ℂ) * Polynomial.X ^ rs.2.val) * Polynomial.X ^ rs.1.val

private theorem gridPoly_coeff {R S : ℕ} (f : Fin R × Fin S → ℝ) (k : ℕ) :
    (gridPoly f).coeff k = ∑ rs : Fin R × Fin S,
      if k = rs.1.val then Polynomial.C (f rs : ℂ) * Polynomial.X ^ rs.2.val else 0 := by
  rw [gridPoly, ← Polynomial.lcoeff_apply, map_sum]
  exact Finset.sum_congr rfl fun rs _ ↦ by
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]

private theorem gridPoly_ne_zero_and_deg_le {R S : ℕ} {f : Fin R × Fin S → ℝ}
    (hfne : ¬ ∀ rs, f rs = 0) :
    gridPoly f ≠ 0 ∧ (gridPoly f).natDegree ≤ R ∧
      ((gridPoly f).support.sup fun k ↦ ((gridPoly f).coeff k).natDegree) ≤ S := by
  have hcoeff (r s' : ℕ) (hr : r < R) (hs' : s' < S) :
      ((gridPoly f).coeff r).coeff s' = (f (⟨r, hr⟩, ⟨s', hs'⟩) : ℂ) := by
    rw [gridPoly_coeff, ← Polynomial.lcoeff_apply, map_sum,
      Finset.sum_eq_single (⟨r, hr⟩, ⟨s', hs'⟩)]
    · simp
    · intro rs _ hne
      by_cases hr' : r = rs.1.val
      · have hs'' : rs.2.val ≠ s' := fun h ↦ hne (Prod.ext (Fin.ext hr'.symm) (Fin.ext h))
        simp [hr', hs''.symm]
      · simp [hr']
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨?_, (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun rs _ ↦
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans rs.1.isLt.le),
    Finset.sup_le fun k _ ↦ ?_⟩
  · intro h0; apply hfne; intro ⟨r, s'⟩
    have h := hcoeff r.val s'.val r.isLt s'.isLt
    rw [h0, Polynomial.coeff_zero, Polynomial.coeff_zero] at h
    exact Complex.ofReal_eq_zero.mp h.symm
  · rw [gridPoly_coeff]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun rs _ ↦ ?_)
    dsimp only [Function.comp_apply]
    split_ifs
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans rs.2.isLt.le
    · simp

private theorem gridPoly_iterate_derivative_eval_eq (d : ℤ) {R S N : ℕ} (f : Fin R × Fin S → ℝ)
    (xy : Fin N × Fin N) (j : Fin N) :
    ((Polynomial.derivative^[j.val] (gridPoly f)).map
      (Polynomial.evalRingHom
        ((xy.1.val : ℂ) - (xy.2.val : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)))).eval
        ((xy.1.val : ℂ) + (xy.2.val : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)) =
      ∑ rs : Fin R × Fin S, (f rs : ℂ) *
        QuadraticAlgebra.sqrtEmbedding (d : ℚ)
          (toRatQA d (gridVec d R S N rs (xy.1, xy.2, j))) := by
  set s := QuadraticAlgebra.sqrtRadicand (d : ℚ)
  rw [gridPoly, Polynomial.iterate_derivative_sum, Polynomial.map_sum]
  change (Polynomial.evalRingHom ((xy.1.val : ℂ) + (xy.2.val : ℂ) * s)) (∑ rs, _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun rs _ ↦ ?_
  simp only [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_natCast, sqrtEmbedding_gridVec, s]
  ring

/-- A real linear relation on `realGridVec` forces the complex `sqrtEmbedding` combination to vanish
at every grid triple `(x, y, j)`. -/
private theorem sum_sqrtEmbedding_gridVec_eq_zero {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ}
    {f : Fin R × Fin S → ℝ} (hf : ∑ rs, f rs • realGridVec d R S N rs = 0)
    (k : Fin N × Fin N × Fin N) :
    ∑ rs : Fin R × Fin S, (f rs : ℂ) *
      QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d (gridVec d R S N rs k)) = 0 := by
  have hre : ∑ rs : Fin R × Fin S, f rs * ((gridVec d R S N rs k).re : ℝ) = 0 := by
    simpa [realGridVec] using congrFun (congrArg WithLp.ofLp hf) (k, 0)
  have him : ∑ rs : Fin R × Fin S, f rs * ((gridVec d R S N rs k).im : ℝ) = 0 := by
    have h1 := congrFun (congrArg WithLp.ofLp hf) (k, 1)
    have hsq0 : Real.sqrt |(d : ℝ)| ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr hd0))
    have hmul : Real.sqrt |(d : ℝ)| *
        ∑ rs : Fin R × Fin S, f rs * ((gridVec d R S N rs k).im : ℝ) = 0 := by
      rw [Finset.mul_sum]; simpa [realGridVec, mul_left_comm, mul_comm, mul_assoc] using h1
    exact (mul_eq_zero.mp hmul).resolve_left hsq0
  simp_rw [sqrtEmbedding_toRatQA, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  rw [(by exact_mod_cast hre :
      (∑ rs : Fin R × Fin S, (f rs : ℂ) * ((gridVec d R S N rs k).re : ℂ)) = 0),
    (by exact_mod_cast him :
      (∑ rs : Fin R × Fin S, (f rs : ℂ) * ((gridVec d R S N rs k).im : ℂ)) = 0),
    zero_mul, add_zero]

private theorem linearIndependent_realGridVec {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {R S N : ℕ} (hparam : N * R + N * S + 2 * R * S < N ^ 3) :
    LinearIndependent ℝ (realGridVec d R S N) := by
  classical
  set s := QuadraticAlgebra.sqrtRadicand (d : ℚ)
  have hs0 : s ≠ 0 :=
    QuadraticAlgebra.sqrtRadicand_eq_zero_iff.not.mpr (Int.cast_ne_zero.mpr hd.ne_zero)
  rw [Fintype.linearIndependent_iff]; intro f hf; by_contra hfne
  obtain ⟨hFne, hFdeg, hFpdeg⟩ := gridPoly_ne_zero_and_deg_le hfne
  have hvan : ∀ xy : Fin N × Fin N, ∀ j < N,
      ((Polynomial.derivative^[j] (gridPoly f)).map
        (Polynomial.evalRingHom ((xy.1.val : ℂ) - (xy.2.val : ℂ) * s))).eval
          ((xy.1.val : ℂ) + (xy.2.val : ℂ) * s) = 0 := fun xy j hj ↦ by
    rw [gridPoly_iterate_derivative_eval_eq d f xy ⟨j, hj⟩]
    exact sum_sqrtEmbedding_gridVec_eq_zero hd.ne_zero hf (xy.1, xy.2, ⟨j, hj⟩)
  have hmul := Polynomial.mul_card_le_of_forall_iterate_derivative_eval_eq_zero
    (P := fun xy : Fin N × Fin N ↦
      ((xy.1.val : ℂ) + (xy.2.val : ℂ) * s, (xy.1.val : ℂ) - (xy.2.val : ℂ) * s))
    (fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h ↦ by
      have hxy := quadGrid_snd_injective hd hd1
        (a₁ := (x₁.val, y₁.val)) (a₂ := (x₂.val, y₂.val)) h
      exact Prod.ext (Fin.ext (congrArg Prod.fst hxy)) (Fin.ext (congrArg Prod.snd hxy)))
    (fun g hg ↦ card_filter_quadGrid_eval_eq_zero_le hs0 N hg) hFne hvan
  have hcard : N * Fintype.card (Fin N × Fin N) = N ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]; ring
  rw [hcard] at hmul
  have := Nat.mul_le_mul_left N hFdeg; have := Nat.mul_le_mul_left N hFpdeg
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hFdeg) hFpdeg
  omega

/-- Unified identity `a² + |d| b² = (‖σ₊ α‖² + ‖σ₋ α‖²) / 2` for both signs of `d`. -/
private theorem re_sq_add_abs_mul_im_sq (d : ℤ) (α : QuadraticAlgebra ℤ d 0) :
    (α.re : ℝ) ^ 2 + |(d : ℝ)| * (α.im : ℝ) ^ 2 =
      (‖QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d α)‖ ^ 2 +
        ‖QuadraticAlgebra.negSqrtEmbedding (d : ℚ) (toRatQA d α)‖ ^ 2) / 2 := by
  rw [sqrtEmbedding_toRatQA, negSqrtEmbedding_toRatQA]
  have hpar := parallelogram_law_with_norm ℝ (α.re : ℂ)
    ((α.im : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ))
  simp only [norm_mul, Complex.norm_intCast, QuadraticAlgebra.norm_sqrtRadicand,
    Rat.cast_intCast, mul_pow, sq_abs, Real.sq_sqrt (abs_nonneg (d : ℝ))] at hpar
  linarith

/-- Complex-embedding norm bound for each entry of `gridVec`. -/
private theorem norm_embedding_gridVec_le {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ} (hR : 1 ≤ R)
    (hN : 1 ≤ N) (σ : QuadraticAlgebra ℚ (d : ℚ) 0 →ₐ[ℚ] ℂ) (rs : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    ‖σ (toRatQA d (gridVec d R S N rs k))‖ ≤
      (R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.val + rs.2.val) := by
  have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd0
  have hsqd1 : 1 ≤ Real.sqrt |(d : ℝ)| := by simpa using Real.sqrt_le_sqrt hd1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM1 : 1 ≤ 2 * (N : ℝ) * Real.sqrt |(d : ℝ)| := by nlinarith
  have hx : (k.1.val : ℝ) ≤ N := by exact_mod_cast k.1.isLt.le
  have hy : (k.2.1.val : ℝ) ≤ N := by exact_mod_cast k.2.1.isLt.le
  have hpt1 : ‖σ (toRatQA d (zPt d k.1.val k.2.1.val))‖ ≤
      2 * (N : ℝ) * Real.sqrt |(d : ℝ)| :=
    (QuadraticAlgebra.norm_embedding_algebraMap_le σ _).trans
      (by simp only [zPt, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
          nlinarith)
  have hpt2 : ‖σ (toRatQA d (zConj d k.1.val k.2.1.val))‖ ≤
      2 * (N : ℝ) * Real.sqrt |(d : ℝ)| :=
    (QuadraticAlgebra.norm_embedding_algebraMap_le σ _).trans
      (by simp only [zConj, Int.cast_natCast, Int.cast_neg, abs_neg,
            abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
          nlinarith)
  simp only [gridVec, zsmul_eq_mul, map_mul, map_pow, Int.cast_natCast, map_natCast, norm_mul,
    norm_pow, Complex.norm_natCast]
  have hdesc : (rs.1.val.descFactorial k.2.2.val : ℝ) ≤ (R : ℝ) ^ N := by
    exact_mod_cast (Nat.descFactorial_le_pow rs.1.val k.2.2.val).trans
      ((Nat.pow_le_pow_left rs.1.isLt.le _).trans (Nat.pow_le_pow_right hR k.2.2.isLt.le))
  have hpow1 : ‖σ (toRatQA d (zPt d k.1.val k.2.1.val))‖ ^ (rs.1.val - k.2.2.val) ≤
      (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ rs.1.val :=
    (pow_le_pow_left₀ (norm_nonneg _) hpt1 _).trans (pow_le_pow_right₀ hM1 (Nat.sub_le _ _))
  have hpow2 : ‖σ (toRatQA d (zConj d k.1.val k.2.1.val))‖ ^ rs.2.val ≤
      (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ rs.2.val :=
    pow_le_pow_left₀ (norm_nonneg _) hpt2 _
  rw [pow_add]
  exact mul_le_mul hdesc (mul_le_mul hpow1 hpow2 (by positivity) (by positivity))
    (by positivity) (by positivity)

/-- Row-norm bound for `realGridVec d R S N rs`. -/
private theorem norm_sq_realGridVec_le {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ} (hR : 1 ≤ R) (hN : 1 ≤ N)
    (rs : Fin R × Fin S) :
    ‖realGridVec d R S N rs‖ ^ 2 ≤
      (N : ℝ) ^ 3 *
        ((R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.val + rs.2.val)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  calc ∑ k : Fin N × Fin N × Fin N, ∑ j : Fin 2, realGridVec d R S N rs (k, j) ^ 2
      = ∑ k : Fin N × Fin N × Fin N,
          ((gridVec d R S N rs k).re ^ 2 + |(d : ℝ)| * (gridVec d R S N rs k).im ^ 2) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        simp only [Fin.sum_univ_two, realGridVec, Fin.isValue, ↓reduceIte, one_ne_zero, mul_pow,
          Real.sq_sqrt (abs_nonneg _)]
    _ ≤ ∑ _k : Fin N × Fin N × Fin N,
          ((R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.val + rs.2.val)) ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [re_sq_add_abs_mul_im_sq]
        have h1 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_embedding_gridVec_le hd0 hR hN (QuadraticAlgebra.sqrtEmbedding (d : ℚ)) rs k) 2
        have h2 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_embedding_gridVec_le hd0 hR hN (QuadraticAlgebra.negSqrtEmbedding (d : ℚ)) rs k) 2
        linarith
    _ = (N : ℝ) ^ 3 *
          ((R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.val + rs.2.val)) ^ 2 := by
        simp [pow_succ, mul_assoc]

private theorem sum_fin_val_le (m : ℕ) :
    ∑ i : Fin m, (i.val : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (i : ℝ)), Finset.sum_range_natCast]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

private theorem sum_fin_prod_add_le (R S : ℕ) :
    ∑ rs : Fin R × Fin S, 2 * ((rs.1.val : ℝ) + rs.2.val) ≤ (R : ℝ) * S * ((R : ℝ) + S) := by
  rw [Fintype.sum_prod_type]
  have hexp : ∑ r : Fin R, ∑ s : Fin S, 2 * ((r.val : ℝ) + s.val) =
      2 * (S : ℝ) * (∑ r : Fin R, (r.val : ℝ)) + 2 * (R : ℝ) * (∑ s : Fin S, (s.val : ℝ)) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]; ring
  rw [hexp]
  linarith [mul_le_mul_of_nonneg_left (sum_fin_val_le R) (by positivity : (0 : ℝ) ≤ 2 * S),
    mul_le_mul_of_nonneg_left (sum_fin_val_le S) (by positivity : (0 : ℝ) ≤ 2 * R)]

/-- Archimedean upper bound on `log (det (intGram d R S N))` via Hadamard's inequality. -/
private theorem log_det_intGram_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) {R S N : ℕ}
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hparam : N * R + N * S + 2 * R * S < N ^ 3) :
    0 < (intGram d R S N).det ∧
      Real.log ((intGram d R S N).det : ℝ) ≤
        (R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
          (R : ℝ) * S * ((R : ℝ) + S) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
  have hli := linearIndependent_realGridVec hd hd1 hparam
  have hposR : 0 < ((intGram d R S N).det : ℝ) := by
    rw [det_intGram_cast]; exact Matrix.det_gram_pos_iff.mpr hli
  refine ⟨by exact_mod_cast hposR, ?_⟩
  rw [det_intGram_cast]
  refine (Matrix.log_det_gram_le hli).trans ?_
  have hd0 : d ≠ 0 := hd.ne_zero
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hMpos : 0 < 2 * (N : ℝ) * Real.sqrt |(d : ℝ)| :=
    mul_pos (mul_pos two_pos hNpos) (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr hd0)))
  have hrow (rs : Fin R × Fin S) :
      2 * Real.log ‖realGridVec d R S N rs‖ ≤
        3 * Real.log N + 2 * N * Real.log R +
          2 * ((rs.1.val : ℝ) + rs.2.val) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
    have hne : ‖realGridVec d R S N rs‖ ≠ 0 := norm_ne_zero_iff.mpr (hli.ne_zero rs)
    rw [show 2 * Real.log ‖realGridVec d R S N rs‖ = Real.log (‖realGridVec d R S N rs‖ ^ 2) by
      simp [Real.log_pow]]
    refine (Real.log_le_log (sq_pos_of_ne_zero hne) (norm_sq_realGridVec_le hd0 hR hN rs)).trans ?_
    rw [Real.log_mul (pow_ne_zero 3 hNpos.ne') (pow_ne_zero 2 (mul_ne_zero (pow_ne_zero N hRpos.ne')
      (pow_ne_zero _ hMpos.ne'))), Real.log_pow, Real.log_pow,
      Real.log_mul (pow_ne_zero N hRpos.ne') (pow_ne_zero _ hMpos.ne'), Real.log_pow, Real.log_pow]
    push_cast; linarith
  have hlogM : 0 ≤ Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
    apply Real.log_nonneg
    have hsq1 : 1 ≤ Real.sqrt |(d : ℝ)| := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ |(d : ℝ)| by exact_mod_cast Int.one_le_abs hd0)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc ∑ rs : Fin R × Fin S, 2 * Real.log ‖realGridVec d R S N rs‖
      ≤ ∑ rs : Fin R × Fin S, (3 * Real.log N + 2 * N * Real.log R +
          2 * ((rs.1.val : ℝ) + rs.2.val) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|)) :=
        Finset.sum_le_sum fun rs _ ↦ hrow rs
    _ = (R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
          (∑ rs : Fin R × Fin S, 2 * ((rs.1.val : ℝ) + rs.2.val)) *
            Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Finset.sum_mul]
    _ ≤ (R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
          (R : ℝ) * S * ((R : ℝ) + S) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
        gcongr; exact sum_fin_prod_add_le R S

end GramMatrix

/-! ### Frobenius congruence and `p`-adic divisibility of the Gram determinant -/

section PadicDivisibility

/-- For an odd prime `p` with `jacobiSym d p = -1`, Frobenius sends `x + yω` to `x - yω` modulo `p`
in `QuadraticAlgebra ℤ d 0`. -/
private theorem frobenius_dvd_zPt_pow_sub_zConj {d : ℤ} {p : ℕ} (hp : p.Prime)
    (hinert : jacobiSym d p = -1) (x y : ℕ) :
    ((p : ℤ) : QuadraticAlgebra ℤ d 0) ∣ zPt d x y ^ p - zConj d x y := by
  have : Fact p.Prime := ⟨hp⟩
  have hnsq : ¬ IsSquare (d : ZMod p) :=
    (legendreSym.eq_neg_one_iff p).mp (by rwa [jacobiSym.legendreSym.to_jacobiSym])
  have hmem := QuadraticAlgebra.frobenius_congruence hnsq (zPt d x y)
  have hstar : star (zPt d x y) = zConj d x y := by ext <;> simp [zPt, zConj]
  rw [hstar] at hmem
  simpa using Ideal.mem_span_singleton.mp hmem

/-- If `(p : A) ∣ z₀ ^ p - z₁`, then `(p : A) ^ h` divides every `k`-th derivative of
`(X ^ p - C z₁) ^ h` evaluated at `z₀`. -/
private theorem pow_dvd_eval_iterate_derivative_pow {A : Type*} [CommRing A] {p : ℕ} {z₀ z₁ : A}
    (hcong : (p : A) ∣ z₀ ^ p - z₁) (h k : ℕ) :
    (p : A) ^ h ∣
      (Polynomial.derivative^[k] ((Polynomial.X ^ p - Polynomial.C z₁) ^ h)).eval z₀ := by
  have hdvd_desc (m : ℕ) : p ∣ p.descFactorial (m + 1) := by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.descFactorial_succ]; exact dvd_mul_of_dvd_right ih _
  have hbase (m : ℕ) :
      (p : A) ∣ (Polynomial.derivative^[m] (Polynomial.X ^ p - Polynomial.C z₁)).eval z₀ := by
    cases m with
    | zero => simpa using hcong
    | succ m =>
      rw [Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_X_pow_eq_C_mul,
        Function.iterate_succ_apply, Polynomial.derivative_C, Polynomial.iterate_derivative_zero,
        sub_zero, Polynomial.eval_mul, Polynomial.eval_C]
      obtain ⟨c, hc⟩ := hdvd_desc m
      exact dvd_mul_of_dvd_left ⟨(c : A), by rw [hc, Nat.cast_mul]⟩ _
  induction h generalizing k with
  | zero => simp
  | succ h ih =>
    rw [pow_succ (Polynomial.X ^ p - Polynomial.C z₁), Polynomial.iterate_derivative_mul]
    change (p : A) ^ (h + 1) ∣ (Polynomial.evalRingHom z₀) (∑ i ∈ Finset.range (k + 1), _)
    rw [map_sum]
    refine Finset.dvd_sum fun i _ ↦ ?_
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_smul, Polynomial.eval_mul, nsmul_eq_mul,
      pow_succ]
    exact dvd_mul_of_dvd_right (mul_dvd_mul (ih (k - i)) (hbase i)) _

/-- Divisibility of the `j`-th derivative of `X ^ (r - p * h) * (X ^ p - C z₁) ^ h * C (z₁ ^ s)`
evaluated at `z₀`. -/
private theorem pow_dvd_eval_iterate_derivative_basis {A : Type*} [CommRing A] {p : ℕ} {z₀ z₁ : A}
    (hcong : (p : A) ∣ z₀ ^ p - z₁) (r s h j : ℕ) :
    (p : A) ^ h ∣ (Polynomial.derivative^[j]
      (Polynomial.X ^ (r - p * h) * (Polynomial.X ^ p - Polynomial.C z₁) ^ h *
        Polynomial.C (z₁ ^ s))).eval z₀ := by
  rw [mul_assoc, Polynomial.iterate_derivative_mul]
  change (p : A) ^ h ∣ (Polynomial.evalRingHom z₀) (∑ i ∈ Finset.range (j + 1), _)
  rw [map_sum]
  refine Finset.dvd_sum fun i _ ↦ ?_
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_smul, Polynomial.eval_mul, nsmul_eq_mul,
    mul_comm _ (Polynomial.C (z₁ ^ s)), Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
    (pow_dvd_eval_iterate_derivative_pow hcong h i) _) _) _

/-- Binomial expansion of
`(derivative^[j] (X ^ (r - p * h) * (X ^ p - C z₁) ^ h * C (z₁ ^ s))).eval z₀`. -/
private theorem eval_iterate_derivative_basis_eq {A : Type*} [CommRing A] {p r s h j : ℕ}
    (hph : p * h ≤ r) (z₀ z₁ : A) :
    (Polynomial.derivative^[j]
      (Polynomial.X ^ (r - p * h) * (Polynomial.X ^ p - Polynomial.C z₁) ^ h *
        Polynomial.C (z₁ ^ s))).eval z₀ =
      ∑ t ∈ Finset.range (h + 1),
        ((-1 : ℤ) ^ t * (h.choose t : ℤ)) •
          (((r - p * t).descFactorial j : ℤ) • (z₀ ^ (r - p * t - j) * z₁ ^ (s + t))) := by
  have hexp : Polynomial.X ^ (r - p * h) * (Polynomial.X ^ p - Polynomial.C z₁) ^ h *
      Polynomial.C (z₁ ^ s) =
      ∑ t ∈ Finset.range (h + 1),
        Polynomial.C (((-1 : A) ^ t * (h.choose t : A)) * z₁ ^ (s + t)) *
          Polynomial.X ^ (r - p * t) := by
    rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have hth : t ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hpowX : (Polynomial.X : A[X]) ^ (r - p * h) * (Polynomial.X ^ p) ^ (h - t) =
        Polynomial.X ^ (r - p * t) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      have : p * t ≤ p * h := Nat.mul_le_mul_left p hth
      have : p * (h - t) = p * h - p * t := Nat.mul_sub_left_distrib p h t
      omega
    have hneg : (-Polynomial.C z₁) ^ t = Polynomial.C ((-1 : A) ^ t * z₁ ^ t) := by
      rw [← map_neg, ← map_pow, neg_eq_neg_one_mul, mul_pow]
    rw [hneg, pow_add, ← hpowX]
    simp only [map_mul, map_pow, map_neg, map_one, Polynomial.C_eq_natCast]
    ring
  rw [hexp, Polynomial.iterate_derivative_sum]
  change (Polynomial.evalRingHom z₀) (∑ t ∈ Finset.range (h + 1), _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Polynomial.coe_evalRingHom, Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    zsmul_eq_mul, zsmul_eq_mul]
  push_cast; ring

/-- The local divisibility exponent `h(r, s) = min (r / p) (S - 1 - s)` for row `(r, s)`. -/
private def padicExp {R : ℕ} (S p : ℕ) (rs : Fin R × Fin S) : ℕ :=
  min (rs.1.val / p) (S - 1 - rs.2.val)

/-- The unitriangular integer row-transformation matrix for an odd inert prime `p`. -/
private def unitriMat (R S p : ℕ) : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
  Matrix.of fun u v ↦
    if u.2.val ≤ v.2.val ∧ v.2.val ≤ u.2.val + padicExp S p u ∧
        v.1.val + p * (v.2.val - u.2.val) = u.1.val then
      (-1 : ℤ) ^ (v.2.val - u.2.val) * ((padicExp S p u).choose (v.2.val - u.2.val) : ℤ)
    else 0

private theorem det_unitriMat (R S p : ℕ) : (unitriMat R S p).det = 1 := by
  let e : (Fin R × Fin S) ≃ Lex (Fin S × Fin R) :=
    (Equiv.prodComm (Fin R) (Fin S)).trans toLex
  rw [← Matrix.det_reindex_self e (unitriMat R S p)]
  have htri : ((unitriMat R S p).reindex e e).BlockTriangular id := by
    intro a b hab
    change (unitriMat R S p) (e.symm a) (e.symm b) = 0
    simp only [unitriMat, Matrix.of_apply, ite_eq_right_iff]
    intro ⟨h1, _, h3⟩
    rcases Prod.Lex.lt_iff.mp hab with hs | ⟨hs, hr⟩
    · exact absurd h1 (not_le.mpr hs)
    · change (ofLex b).2.val + p * ((ofLex b).1.val - (ofLex a).1.val) = (ofLex a).2.val at h3
      dsimp at hs; rw [hs, Nat.sub_self, mul_zero, add_zero] at h3; exact absurd h3 (ne_of_lt hr)
  rw [Matrix.det_of_isUpperTriangular htri]
  exact Finset.prod_eq_one fun a _ ↦ by simp [unitriMat]

/-- Reindexing each transformed row into the binomial derivative combination. -/
private theorem transformed_row_eq_binomial {d : ℤ} {R S N p : ℕ} (u : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    ∑ v : Fin R × Fin S, unitriMat R S p u v • gridVec d R S N v k =
      ∑ t ∈ Finset.range (padicExp S p u + 1),
        ((-1 : ℤ) ^ t * ((padicExp S p u).choose t : ℤ)) •
          (((u.1.val - p * t).descFactorial k.2.2.val : ℤ) •
            (zPt d k.1.val k.2.1.val ^ (u.1.val - p * t - k.2.2.val) *
              zConj d k.1.val k.2.1.val ^ (u.2.val + t))) := by
  have hph : p * padicExp S p u ≤ u.1.val :=
    (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le u.1.val p)
  have hsh : u.2.val + padicExp S p u < S := by
    have : padicExp S p u ≤ S - 1 - u.2.val := min_le_right _ _; omega
  let P (v : Fin R × Fin S) : Prop :=
    u.2.val ≤ v.2.val ∧ v.2.val ≤ u.2.val + padicExp S p u ∧
      v.1.val + p * (v.2.val - u.2.val) = u.1.val
  rw [show ∑ v : Fin R × Fin S, unitriMat R S p u v • gridVec d R S N v k =
      ∑ v ∈ Finset.univ.filter P, unitriMat R S p u v • gridVec d R S N v k by
    rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun v _ ↦ ?_
    split_ifs with hv
    · rfl
    · simp only [unitriMat, Matrix.of_apply, show ¬ (u.2.val ≤ v.2.val ∧
        v.2.val ≤ u.2.val + padicExp S p u ∧ v.1.val + p * (v.2.val - u.2.val) = u.1.val) from hv,
        ↓reduceIte, zero_smul]]
  let f (t : ℕ) : Fin R × Fin S :=
    if ht : t ≤ padicExp S p u then
      (⟨u.1.val - p * t, lt_of_le_of_lt (Nat.sub_le _ _) u.1.isLt⟩, ⟨u.2.val + t, by omega⟩)
    else u
  have hth {t : ℕ} (ht : t ∈ Finset.range (padicExp S p u + 1)) : t ≤ padicExp S p u :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have hpt {t : ℕ} (ht : t ≤ padicExp S p u) : p * t ≤ u.1.val :=
    (Nat.mul_le_mul_left p ht).trans hph
  symm
  refine Finset.sum_nbij' f (fun v ↦ v.2.val - u.2.val) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩ <;>
      simp only [f, hth ht, ↓reduceDIte]
    · exact Nat.le_add_right _ _
    · exact Nat.add_le_add_left (hth ht) _
    · rw [Nat.add_sub_cancel_left]; exact Nat.sub_add_cancel (hpt (hth ht))
  · exact fun v hv ↦ Finset.mem_range.mpr (by have ⟨_, _, _⟩ := (Finset.mem_filter.mp hv).2; omega)
  · exact fun t ht ↦ by simp [f, hth ht]
  · intro v hv
    have ⟨_, _, _⟩ := (Finset.mem_filter.mp hv).2
    ext <;> simp only [f, show v.2.val - u.2.val ≤ padicExp S p u by omega, ↓reduceDIte] <;> omega
  · intro t ht
    have hcond : u.2.val ≤ u.2.val + t ∧ u.2.val + t ≤ u.2.val + padicExp S p u ∧
        u.1.val - p * t + p * t = u.1.val :=
      ⟨Nat.le_add_right _ _, Nat.add_le_add_left (hth ht) _, Nat.sub_add_cancel (hpt (hth ht))⟩
    simp only [unitriMat, Matrix.of_apply, f, hth ht, ↓reduceDIte, Nat.add_sub_cancel_left, hcond,
      and_self, ↓reduceIte, gridVec]

/-- Each transformed row is divisible by `p ^ (padicExp S p u)` in `QuadraticAlgebra ℤ d 0`. -/
private theorem pow_padicExp_dvd_transformed_row {d : ℤ} {R S N p : ℕ} (hp : p.Prime)
    (hinert : jacobiSym d p = -1) (u : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
    ((p : ℤ) : QuadraticAlgebra ℤ d 0) ^ padicExp S p u ∣
      ∑ v : Fin R × Fin S, unitriMat R S p u v • gridVec d R S N v k := by
  have hph : p * padicExp S p u ≤ u.1.val :=
    (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le u.1.val p)
  rw [transformed_row_eq_binomial, ← eval_iterate_derivative_basis_eq hph]
  simpa only [Int.cast_natCast] using pow_dvd_eval_iterate_derivative_basis (p := p)
    (frobenius_dvd_zPt_pow_sub_zConj hp hinert k.1.val k.2.1.val)
    u.1.val u.2.val (padicExp S p u) k.2.2.val

/-- Entry formula for the conjugated Gram matrix `U * intGram d R S N * Uᵀ`. -/
private theorem transformed_gram_entry {d : ℤ} {R S N : ℕ}
    (U : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ) (u v : Fin R × Fin S) :
    (U * intGram d R S N * Uᵀ) u v =
      ∑ k : Fin N × Fin N × Fin N,
        ((∑ a, U u a • gridVec d R S N a k).re * (∑ b, U v b • gridVec d R S N b k).re +
          |d| * (∑ a, U u a • gridVec d R S N a k).im * (∑ b, U v b • gridVec d R S N b k).im) := by
  let reHom : QuadraticAlgebra ℤ d 0 →+ ℤ :=
    ⟨⟨QuadraticAlgebra.re, by simp⟩, QuadraticAlgebra.re_add⟩
  let imHom : QuadraticAlgebra ℤ d 0 →+ ℤ :=
    ⟨⟨QuadraticAlgebra.im, by simp⟩, QuadraticAlgebra.im_add⟩
  have hre (u' : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
      (∑ a, U u' a • gridVec d R S N a k).re = ∑ a, U u' a * (gridVec d R S N a k).re := by
    change reHom (∑ a, U u' a • gridVec d R S N a k) = _
    simp [map_sum, reHom]
  have him (u' : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
      (∑ a, U u' a • gridVec d R S N a k).im = ∑ a, U u' a * (gridVec d R S N a k).im := by
    change imHom (∑ a, U u' a • gridVec d R S N a k) = _
    simp [map_sum, imHom]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, intGram, Matrix.of_apply,
    Finset.sum_mul, Finset.mul_sum, hre, him]
  rw [Finset.sum_comm]; conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm] <;>
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- **`p`-adic divisibility of the Gram determinant.** For every odd prime `p` with
`jacobiSym d p = -1`, `p ^ (2 ∑_{r, s} min (r / p) (S - 1 - s))` divides `(intGram d R S N).det`. -/
private theorem pow_two_mul_sum_padicExp_dvd_det_intGram {d : ℤ} {R S N p : ℕ} (hp : p.Prime)
    (hinert : jacobiSym d p = -1) :
    (p : ℤ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u) ∣ (intGram d R S N).det := by
  let U := unitriMat R S p
  let Gw := U * intGram d R S N * Uᵀ
  rw [show (intGram d R S N).det = Gw.det by
    simp [Gw, Matrix.det_mul, Matrix.det_transpose, U, det_unitriMat]]
  have hGw_dvd (u v : Fin R × Fin S) :
      (p : ℤ) ^ (padicExp S p u + padicExp S p v) ∣ Gw u v := by
    change (p : ℤ) ^ _ ∣ (U * intGram d R S N * Uᵀ) u v
    rw [transformed_gram_entry U u v]
    refine Finset.dvd_sum fun k _ ↦ ?_
    have hdvd_coord (w : Fin R × Fin S) :
        (p : ℤ) ^ padicExp S p w ∣ (∑ a, U w a • gridVec d R S N a k).re ∧
          (p : ℤ) ^ padicExp S p w ∣ (∑ a, U w a • gridVec d R S N a k).im := by
      have h := pow_padicExp_dvd_transformed_row (d := d) (R := R) (S := S) (N := N) hp hinert w k
      have hmem : ∑ a, U w a • gridVec d R S N a k ∈
          Ideal.span {((p ^ padicExp S p w : ℕ) : QuadraticAlgebra ℤ d 0)} :=
        Ideal.mem_span_singleton.mpr (by simpa [Nat.cast_pow] using h)
      simpa [Nat.cast_pow] using QuadraticAlgebra.mem_span_natCast_iff.mp hmem
    have hu := hdvd_coord u; have hv := hdvd_coord v
    rw [pow_add]
    refine dvd_add (mul_dvd_mul hu.1 hv.1) ?_
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul hu.2 hv.2) |d|
  choose Q hQ using hGw_dvd
  let D : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
    Matrix.diagonal fun u ↦ (p : ℤ) ^ padicExp S p u
  have hGw_fac : Gw = D * Matrix.of Q * D := by
    ext u v
    simp only [Matrix.mul_apply, D, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.of_apply]
    rw [hQ u v, pow_add]
    ring
  rw [hGw_fac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  exact ⟨(Matrix.of Q).det, by rw [two_mul, pow_add]; ring⟩

/-- Lower bound on `log (det (intGram d R S N))` from all odd inert primes in a finite set `P'`. -/
private theorem sum_padicExp_log_le_log_det_intGram {d : ℤ} {R S N : ℕ}
    (hdet : 0 < (intGram d R S N).det) {P' : Finset ℕ}
    (hP' : ∀ p ∈ P', p.Prime ∧ Odd p ∧ jacobiSym d p = -1) :
    ∑ p ∈ P', (2 * (∑ u : Fin R × Fin S, padicExp S p u : ℝ)) * Real.log p ≤
      Real.log ((intGram d R S N).det : ℝ) := by
  have hdvd : ∏ p ∈ P', (p : ℤ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u) ∣
      (intGram d R S N).det :=
    Finset.prod_dvd_of_coprime (fun p hp q hq hne ↦ (Int.isCoprime_iff_nat_coprime.mpr
      (by simpa using (Nat.coprime_primes (hP' p hp).1 (hP' q hq).1).mpr hne)).pow)
      fun p hp ↦ pow_two_mul_sum_padicExp_dvd_det_intGram (hP' p hp).1 (hP' p hp).2.2
  have hleR : (∏ p ∈ P', (p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u)) ≤
      ((intGram d R S N).det : ℝ) := by exact_mod_cast Int.le_of_dvd hdet hdvd
  have hpos : 0 < ∏ p ∈ P', (p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u) :=
    Finset.prod_pos fun p hp ↦ pow_pos (Nat.cast_pos.mpr (hP' p hp).1.pos) _
  calc ∑ p ∈ P', (2 * (∑ u : Fin R × Fin S, padicExp S p u : ℝ)) * Real.log p
      = ∑ p ∈ P', Real.log ((p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u)) :=
        Finset.sum_congr rfl fun p _ ↦ by rw [Real.log_pow]; push_cast; rfl
    _ = Real.log (∏ p ∈ P', (p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u)) :=
        (Real.log_prod fun p hp ↦ pow_ne_zero _ (Nat.cast_ne_zero.mpr (hP' p hp).1.ne_zero)).symm
    _ ≤ Real.log ((intGram d R S N).det : ℝ) := Real.log_le_log hpos hleR

end PadicDivisibility

/-- **Gram determinant comparison for inert primes.** For squarefree `d ≠ 1`, grid parameters
`R, S, N ≥ 1` with `N * R + N * S + 2 * R * S < N ^ 3`, and any finite set `P'` of odd primes
with `jacobiSym d p = -1`, the `p`-adic lower bound is at most the Hadamard upper bound on
`log (det G_ℤ)`. -/
theorem sum_min_div_log_le_of_jacobiSym_eq_neg_one {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {R S N : ℕ} (hR : 1 ≤ R) (hN : 1 ≤ N) (hparam : N * R + N * S + 2 * R * S < N ^ 3)
    {P' : Finset ℕ} (hP' : ∀ p ∈ P', p.Prime ∧ Odd p ∧ jacobiSym d p = -1) :
    ∑ p ∈ P', (2 * (∑ u : Fin R × Fin S, (min (u.1.val / p) (S - 1 - u.2.val) : ℕ) : ℝ)) *
        Real.log p ≤
      (R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
        (R : ℝ) * S * ((R : ℝ) + S) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
  obtain ⟨hdet_pos, hdet_ub⟩ := log_det_intGram_le hd hd1 hR hN hparam
  exact (sum_padicExp_log_le_log_det_intGram hdet_pos hP').trans hdet_ub

end TauCeti
