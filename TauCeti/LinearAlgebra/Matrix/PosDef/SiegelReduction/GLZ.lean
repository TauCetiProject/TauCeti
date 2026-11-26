/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SiegelDomain
public import TauCeti.LinearAlgebra.Matrix.PosDef.SiegelReduction.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fin.Rev
import TauCeti.Algebra.Module.Primitive
import TauCeti.LinearAlgebra.Matrix.Congruence
import TauCeti.LinearAlgebra.Matrix.CornerBlockSucc
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import TauCeti.LinearAlgebra.Matrix.PosDef.Northcott

/-!
# Siegel reduction for positive-definite forms and `GL_n(ℝ)`

The Gram map `TauCeti.RealSiegel.gram g = (g⁻¹)ᵀ * g⁻¹` relates standard real Siegel domains
`TauCeti.RealSiegel.siegelDomain n u t` (`Σ_n(u, t) ⊆ GL (Fin n) ℝ`) and `C`-reduced
positive-definite forms `TauCeti.RealSiegel.reducedSet n C` by two-sided cofinality. Over `ℤ`,
every positive-definite real form is `GL (Fin n) ℤ`-congruent to a size-reduced Cholesky form with
pivot ratio at most `4 / 3`, hence to a `C`-reduced form, and every `g : GL (Fin n) ℝ` decomposes
as `γ * s` with `γ : GL (Fin n) ℤ` and `s ∈ Σ_n(1 / 2, √3 / 2)`.

## Main results

* `TauCeti.RealSiegel.exists_reducedSet_of_siegelDomain` and
  `TauCeti.RealSiegel.exists_siegelDomain_of_reducedSet`: two-sided cofinality between
  `siegelDomain n u t` (`t > 0`) and `reducedSet n C` (`C > 1`).
* `TauCeti.RealSiegel.exists_cholesky_reduced_GLZ`, `TauCeti.RealSiegel.exists_reduced_GLZ`, and
  `TauCeti.RealSiegel.exists_mul_mem_siegelDomain_GLZ`: Siegel-type Cholesky reduction over `ℤ`
  (size-reduced, pivot ratio `≤ 4 / 3`), `C`-reduced `GL (Fin n) ℤ`-equivalence, and
  `GL_n(ℝ) = GL_n(ℤ) · Σ_n(1 / 2, √3 / 2)`.

## References

* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, second
  edition, Vol. 1, Cambridge University Press, 2023, §4.2 (Theorems 4.12 and 4.20).
* B. Bakker, B. Klingler, and J. Tsimerman, *Tame topology of arithmetic quotients and
  algebraicity of Hodge loci*, J. Amer. Math. Soc. 33 (2020), 917–939, §4.5, Definition 4.11.
* M. Orr, *Height bounds and the Siegel property*, Algebra Number Theory 12 (2018), §2.A.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti.RealSiegel

section Cofinality

private theorem gram_mul_diagGL {n : ℕ} (v : GL (Fin n) ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    gram (v * diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne')) =
      v⁻¹.valᵀ * Matrix.diagonal (fun i ↦ (a i)⁻¹ ^ 2) * v⁻¹.val := by
  let f : Fin n → ℝˣ := fun i ↦ Units.mk0 (a i) (ha i).ne'
  have hda_inv : (diagGL f)⁻¹.val = Matrix.diagonal (fun i ↦ (a i)⁻¹) := by
    simpa [f, diagGL_coe] using coe_inv_of_mem_posDiagonalSubgroup
      (diagGL_mem_posDiagonalSubgroup_iff (t := f).mpr fun i ↦ by simpa [f] using ha i)
  calc gram (v * diagGL f) = v⁻¹.valᵀ * ((diagGL f)⁻¹.valᵀ * (diagGL f)⁻¹.val) * v⁻¹.val := by
        simp only [gram_def, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = v⁻¹.valᵀ * Matrix.diagonal (fun i ↦ (a i)⁻¹ ^ 2) * v⁻¹.val := by
        rw [hda_inv, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
        congr 2; ext i; simp [sq]

/-- **Siegel domains map into reduced-form sets.** For every `u` and every `t > 0`, there is
`C > 1` depending only on `n`, `u`, and `t` such that `gram g ∈ reducedSet n C` for every
`g ∈ siegelDomain n u t`. -/
theorem exists_reducedSet_of_siegelDomain (n : ℕ) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 1 < C ∧ ∀ g ∈ siegelDomain n u t, gram g ∈ reducedSet n C := by
  let u_inv : ℝ := ∑ m ∈ Finset.range n, ((n : ℝ) * max u 0) ^ m
  obtain ⟨C, hC_gt, hC_red⟩ := exists_isReduced_of_cholesky_bound n (max (u_inv + 1) (t⁻¹ ^ 2))
  refine ⟨C, hC_gt, fun g hg ↦ mem_reducedSet_iff.mpr ⟨posDef_gram g, ?_⟩⟩
  obtain ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, rfl⟩ := mem_siegelDomain_iff.mp hg
  rw [gram_mul_orthogonal _ hk, gram_mul_diagGL v a ha]
  have hv_ut : v.val.IsUpperUnitriangular := UpperUnitriangularGroup.mem_iff.mp hv
  have hN_ut : v⁻¹.val.IsUpperUnitriangular :=
    UpperUnitriangularGroup.mem_iff.mp ((upperUnitriangularGroup (Fin n) ℝ).inv_mem hv)
  let d : Fin n → ℝ := fun i ↦ (a i)⁻¹ ^ 2
  have hd_pos : ∀ i, 0 < d i := fun i ↦ sq_pos_of_pos (inv_pos.mpr (ha i))
  refine (hC_red hN_ut hd_pos (fun i j _ ↦ ?_) (fun i hi ↦ ?_)).2
  · have hle : |v⁻¹.val i j| ≤ u_inv := by
      simpa only [show hv_ut.toGL = v from Units.ext hv_ut.coe_toGL, Fintype.card_fin] using
        hv_ut.abs_inv_toGL_apply_le (le_max_right u 0)
          (fun p q hpq ↦ (hv_bound p q hpq).trans (le_max_left u 0)) i j
    exact hle.trans ((lt_add_one u_inv).le.trans (le_max_left _ _))
  · have hinv : (a i)⁻¹ ≤ t⁻¹ * (a ⟨i.val + 1, hi⟩)⁻¹ := by
      rw [← mul_inv, inv_le_inv₀ (ha i) (mul_pos ht (ha ⟨i.val + 1, hi⟩))]
      exact (le_div_iff₀ (ha ⟨i.val + 1, hi⟩)).mp (ha_ratio i hi)
    have hsq : d i ≤ t⁻¹ ^ 2 * d ⟨i.val + 1, hi⟩ := by
      simpa only [d, sq, mul_mul_mul_comm] using mul_le_mul hinv hinv (inv_nonneg.mpr (ha i).le)
        (mul_nonneg (inv_nonneg.mpr ht.le) (inv_nonneg.mpr (ha ⟨i.val + 1, hi⟩).le))
    exact hsq.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hd_pos _).le)

private theorem exists_mem_siegelDomain_gram_eq {n : ℕ} {C B : ℝ} (hB : 0 < B)
    (hCh : ∀ {b N : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ},
      b.PosDef → IsReduced C b → N.IsUpperUnitriangular → (∀ i, 0 < d i) →
        b = Nᵀ * Matrix.diagonal d * N →
        (∀ i j, i < j → |N i j| ≤ B) ∧ (∀ i j, i < j → d i ≤ B * d j))
    {b : Matrix (Fin n) (Fin n) ℝ} (hb : b ∈ reducedSet n C) :
    ∃ g ∈ siegelDomain n ((∑ m ∈ Finset.range n, ((n : ℝ) * B) ^ m) + 1) (Real.sqrt B)⁻¹,
      gram g = b ∧ (b.det = 1 → (g : Matrix (Fin n) (Fin n) ℝ).det = 1) := by
  obtain ⟨hb_pos, hb_red⟩ := mem_reducedSet_iff.mp hb
  obtain ⟨N, d, hN_ut, hd_pos, hb_eq⟩ :=
    hb_pos.exists_isUpperUnitriangular_transpose_mul_diagonal_mul_eq
  obtain ⟨hN_bound, hd_ratio⟩ := hCh hb_pos hb_red hN_ut hd_pos hb_eq
  let v : GL (Fin n) ℝ := hN_ut.toGL⁻¹
  have hv_mem : v ∈ upperUnitriangularGroup (Fin n) ℝ := (upperUnitriangularGroup (Fin n) ℝ).inv_mem
    (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hN_ut)
  let a : Fin n → ℝ := fun i ↦ (Real.sqrt (d i))⁻¹
  have ha_pos : ∀ i, 0 < a i := fun i ↦ inv_pos.mpr (Real.sqrt_pos.mpr (hd_pos i))
  let g₀ : GL (Fin n) ℝ := v * diagGL (fun i ↦ Units.mk0 (a i) (ha_pos i).ne')
  have hgram_g₀ : gram g₀ = b := by
    rw [gram_mul_diagGL v a ha_pos, hb_eq, show v⁻¹.val = N by simp [v]]
    congr 2; ext i j; by_cases hij : i = j <;>
      simp [a, Matrix.diagonal, hij, Real.sq_sqrt (hd_pos _).le]
  refine ⟨g₀, mem_siegelDomain_iff.mpr ⟨v, hv_mem, a, ha_pos, 1, (GLOrthogonal (Fin n) ℝ).one_mem,
      fun i j _ ↦ ?_, fun i hi ↦ ?_, (mul_one g₀).symm⟩, hgram_g₀, fun hb_det ↦ ?_⟩
  · exact (show |hN_ut.toGL⁻¹.val i j| ≤ _ by
      simpa only [Fintype.card_fin] using hN_ut.abs_inv_toGL_apply_le hB.le hN_bound i j).trans
      (lt_add_one _).le
  · have hsqrt : Real.sqrt (d i) ≤ Real.sqrt B * Real.sqrt (d ⟨i.val + 1, hi⟩) := by
      rw [← Real.sqrt_mul hB.le]
      exact Real.sqrt_le_sqrt
        (hd_ratio i ⟨i.val + 1, hi⟩ (Fin.lt_def.mpr (Nat.lt_succ_self i.val)))
    rw [le_div_iff₀ (ha_pos ⟨i.val + 1, hi⟩)]
    simpa only [a, ← mul_inv] using (inv_le_inv₀
      (mul_pos (Real.sqrt_pos.mpr hB) (Real.sqrt_pos.mpr (hd_pos _)))
      (Real.sqrt_pos.mpr (hd_pos i))).mpr hsqrt
  · have hg₀_pos : 0 < g₀.val.det := by
      rw [Units.val_mul, Matrix.det_mul, (UpperUnitriangularGroup.mem_iff.mp hv_mem).det_eq_one,
        one_mul]
      exact det_pos_of_mem_posDiagonalSubgroup
        (diagGL_mem_posDiagonalSubgroup_iff.mpr fun i ↦ by simpa using ha_pos i)
    have hsq : g₀.val.det⁻¹ ^ 2 = 1 := by rw [← det_gram g₀, hgram_g₀, hb_det]
    exact inv_eq_one.mp ((sq_eq_sq₀ (inv_pos.mpr hg₀_pos).le zero_le_one).mp (by simpa using hsq))

/-- **Reduced-form sets lift into Siegel domains.** For every `C`, there are `u > 0` and `t > 0`
depending only on `n` and `C` such that every `g : GL (Fin n) ℝ` with `gram g ∈ reducedSet n C`
lies in `siegelDomain n u t`, and every `b ∈ reducedSet n C` has the form `b = gram g` for some
`g ∈ siegelDomain n u t` (with `det g = 1` whenever `det b = 1`). -/
theorem exists_siegelDomain_of_reducedSet (n : ℕ) (C : ℝ) :
    ∃ u > 0, ∃ t > 0,
      (∀ g : GL (Fin n) ℝ, gram g ∈ reducedSet n C → g ∈ siegelDomain n u t) ∧
      (∀ b ∈ reducedSet n C, ∃ g ∈ siegelDomain n u t,
        gram g = b ∧ (b.det = 1 → (g : Matrix (Fin n) (Fin n) ℝ).det = 1)) := by
  obtain ⟨B, hB, hCh⟩ := exists_cholesky_bound_of_isReduced n C
  refine ⟨_, add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ by positivity) zero_lt_one,
    (Real.sqrt B)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hB), fun g hg ↦ ?_,
    fun b hb ↦ exists_mem_siegelDomain_gram_eq hB hCh hb⟩
  obtain ⟨g₀, hg₀_mem, hgram_eq, -⟩ := exists_mem_siegelDomain_gram_eq hB hCh hg
  obtain ⟨k, hk, rfl⟩ := gram_eq_iff_exists_mem_GLOrthogonal.mp hgram_eq.symm
  exact mul_orthogonal_mem_siegelDomain hg₀_mem hk

end Cofinality

section Reduction

private theorem first_pivot_le_four_thirds {n : ℕ} {b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {v₀ : Fin (n + 1) → ℤ}
    (hv₀_min : ∀ x : Fin (n + 1) → ℤ, x ≠ 0 →
      (fun i ↦ (v₀ i : ℝ)) ⬝ᵥ b *ᵥ (fun i ↦ (v₀ i : ℝ)) ≤
        (fun i ↦ (x i : ℝ)) ⬝ᵥ b *ᵥ (fun i ↦ (x i : ℝ)))
    {γ : GL (Fin (n + 1)) ℤ} (hγ_col0 : γ.val *ᵥ Pi.single 0 1 = v₀)
    {d₀ : ℝ} (hd₀_pos : 0 < d₀) {d' w' : Fin n → ℝ} (hw'_bound : ∀ j, |w' j| ≤ 1 / 2)
    {N' : Matrix (Fin n) (Fin n) ℝ} (hN'_ut : N'.IsUpperUnitriangular)
    (hγ_eq : (γ.map (Int.castRingHom ℝ)).valᵀ * b * (γ.map (Int.castRingHom ℝ)).val =
      (Matrix.upperBorder w' N')ᵀ * Matrix.diagonal (Fin.cons d₀ d') * Matrix.upperBorder w' N')
    (i₀ : Fin n) (hi₀ : i₀.val = 0) : d₀ ≤ (4 / 3) * d' i₀ := by
  let b₃ := (Matrix.upperBorder w' N')ᵀ * Matrix.diagonal (Fin.cons d₀ d') *
    Matrix.upperBorder w' N'
  have hquad (p : Fin (n + 1)) :
      (fun i ↦ ((γ.val *ᵥ Pi.single p 1) i : ℝ)) ⬝ᵥ
        b *ᵥ (fun i ↦ ((γ.val *ᵥ Pi.single p 1) i : ℝ)) = b₃ p p := by
    have hvec : (fun i ↦ ((γ.val *ᵥ Pi.single p 1) i : ℝ)) =
        (γ.map (Int.castRingHom ℝ)).val *ᵥ Pi.single p 1 := by
      ext q; simp [Matrix.mulVec, dotProduct, Matrix.GeneralLinearGroup.map_apply, Pi.single_apply]
    have hsingle : Pi.single p 1 ⬝ᵥ b₃ *ᵥ Pi.single p 1 = b₃ p p := by
      rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply]
    rw [hvec, ← hsingle]
    simp only [b₃, ← hγ_eq, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      ← Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]
  have hb₃_form : b₃ = Matrix.of (Fin.cons (Fin.cons d₀ (fun j ↦ d₀ * w' j))
      fun i ↦ Fin.cons (w' i * d₀)
        (fun j ↦ d₀ * w' i * w' j + (N'ᵀ * Matrix.diagonal d' * N') i j)) := by
    dsimp only [b₃]
    rw [← Matrix.cornerBlockSucc_diagonal, Matrix.transpose_upperBorder_mul_cornerBlockSucc_mul]
  have hd₀_eq : (fun i ↦ (v₀ i : ℝ)) ⬝ᵥ b *ᵥ (fun i ↦ (v₀ i : ℝ)) = d₀ := by
    rw [← hγ_col0, hquad 0, hb₃_form]; simp only [Matrix.of_apply, Fin.cons_zero]
  let y₁ : Fin (n + 1) → ℤ := γ.val *ᵥ Pi.single i₀.succ 1
  have hy₁_ne : y₁ ≠ 0 := fun hy0 ↦ by
    simpa using congrFun (Matrix.mulVec_injective_of_isUnit γ.isUnit
      (hy0.trans (Matrix.mulVec_zero _).symm)) i₀.succ
  have hsub00 : (N'ᵀ * Matrix.diagonal d' * N') i₀ i₀ = d' i₀ := by
    rw [hN'_ut.transpose_mul_diagonal_mul_apply d' i₀ i₀, hN'_ut.apply_diag i₀, mul_one]
    have hempty : Finset.univ.filter (· < i₀) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ hlt ↦ by rw [Fin.lt_def, hi₀] at hlt; omega
    simp [hempty]
  have hmin := hv₀_min y₁ hy₁_ne
  rw [hd₀_eq, hquad i₀.succ,
    show b₃ i₀.succ i₀.succ = d₀ * w' i₀ ^ 2 + d' i₀ by
      rw [hb₃_form]; simp only [Matrix.of_apply, Fin.cons_succ, hsub00]; ring] at hmin
  have hw_sq : w' i₀ ^ 2 ≤ 1 / 4 := by
    simpa only [← sq, sq_abs] using
      (mul_le_mul (hw'_bound i₀) (hw'_bound i₀) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  linarith [mul_le_mul_of_nonneg_left hw_sq hd₀_pos.le]

/-- Composite congruence identity combining the first-column unimodular matrix `γ₁`, the
Schur-complement factorization of `γ₁ᵀ * b * γ₁`, the inductive reduction `γ'` of `b_sub`, and the
integer size-reduction shear `z` via the single bordered unit `Matrix.upperBorderUnit z γ'`. -/
private theorem composite_congruence_upperBorder {n : ℕ} {d₀ : ℝ}
    {b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b_sub N' : Matrix (Fin n) (Fin n) ℝ}
    {d' u₀ : Fin n → ℝ} {z : Fin n → ℤ} {γ₁ : GL (Fin (n + 1)) ℤ} {γ' : GL (Fin n) ℤ}
    (hb₁_schur : (γ₁.map (Int.castRingHom ℝ)).valᵀ * b * (γ₁.map (Int.castRingHom ℝ)).val =
      (Matrix.upperBorder u₀ 1)ᵀ * Matrix.cornerBlockSucc d₀ b_sub * Matrix.upperBorder u₀ 1)
    (hγ'_eq : (γ'.map (Int.castRingHom ℝ)).valᵀ * b_sub * (γ'.map (Int.castRingHom ℝ)).val =
      N'ᵀ * Matrix.diagonal d' * N') :
    ((γ₁ * Matrix.upperBorderUnit z γ').map (Int.castRingHom ℝ)).valᵀ * b *
      ((γ₁ * Matrix.upperBorderUnit z γ').map (Int.castRingHom ℝ)).val =
    (Matrix.upperBorder ((Int.cast ∘ z) + u₀ ᵥ* (γ'.map (Int.castRingHom ℝ)).val) N')ᵀ *
      Matrix.diagonal (Fin.cons d₀ d') *
      Matrix.upperBorder ((Int.cast ∘ z) + u₀ ᵥ* (γ'.map (Int.castRingHom ℝ)).val) N' := by
  let γ'R : Matrix (Fin n) (Fin n) ℝ := (γ'.map (Int.castRingHom ℝ)).val
  let w' : Fin n → ℝ := (Int.cast ∘ z) + u₀ ᵥ* γ'R
  have hmap : (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ)
      (Matrix.upperBorderUnit z γ')).val = Matrix.upperBorder (Int.cast ∘ z) γ'R := by
    simpa [γ'R, Matrix.GeneralLinearGroup.map] using
      Matrix.upperBorder_map (Int.castRingHom ℝ) z γ'.val
  have hUγ : Matrix.upperBorder u₀ 1 * Matrix.upperBorder (Int.cast ∘ z) γ'R =
      Matrix.upperBorder w' γ'R := by simp [w', γ'R]
  calc ((γ₁ * Matrix.upperBorderUnit z γ').map (Int.castRingHom ℝ)).valᵀ * b *
        ((γ₁ * Matrix.upperBorderUnit z γ').map (Int.castRingHom ℝ)).val
      = (Matrix.upperBorder (Int.cast ∘ z) γ'R)ᵀ * ((γ₁.map (Int.castRingHom ℝ)).valᵀ * b *
          (γ₁.map (Int.castRingHom ℝ)).val) * Matrix.upperBorder (Int.cast ∘ z) γ'R := by
        simp only [map_mul, Units.val_mul, hmap, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Matrix.upperBorder w' γ'R)ᵀ * Matrix.cornerBlockSucc d₀ b_sub *
          Matrix.upperBorder w' γ'R := by
        rw [hb₁_schur, ← hUγ]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Matrix.upperBorder w' N')ᵀ * Matrix.diagonal (Fin.cons d₀ d') *
          Matrix.upperBorder w' N' := by
        rw [Matrix.transpose_upperBorder_mul_cornerBlockSucc_mul, hγ'_eq,
          ← Matrix.cornerBlockSucc_diagonal, Matrix.transpose_upperBorder_mul_cornerBlockSucc_mul]

/-- **Siegel-type Cholesky reduction over `ℤ`.** Every positive-definite real `n × n` matrix `b`
is `GL (Fin n) ℤ`-congruent to `Nᵀ * diagonal d * N` for an upper-unitriangular matrix `N` with
size-reduced off-diagonal entries `|N i j| ≤ 1 / 2` (`i < j`) and positive diagonal `d` satisfying
the Siegel pivot bound `d i ≤ (4 / 3) * d ⟨i + 1, _⟩`. -/
theorem exists_cholesky_reduced_GLZ (n : ℕ) {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.PosDef) :
    ∃ (γ : GL (Fin n) ℤ) (N : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      N.IsUpperUnitriangular ∧ (∀ i, 0 < d i) ∧ (∀ i j, i < j → |N i j| ≤ 1 / 2) ∧
      (∀ (i : Fin n) (h : i.val + 1 < n), d i ≤ (4 / 3) * d ⟨i.val + 1, h⟩) ∧
      ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b *
        ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
          Nᵀ * Matrix.diagonal d * N := by
  -- HKZ-style induction on dimension `n`: pick a primitive shortest nonzero lattice vector `v₀`,
  -- complete it to `γ₁ ∈ GL_{n+1}(ℤ)`, pass to the `n × n` Schur complement `b_sub`, reduce
  -- `b_sub` inductively by `γ'`, and size-reduce the top row by an integer shear `z`.
  induction n with
  | zero =>
      exact ⟨1, 1, Fin.elim0, Matrix.isUpperUnitriangular_one, fun i ↦ i.elim0,
        fun i ↦ i.elim0, fun i ↦ i.elim0, Matrix.ext fun i ↦ i.elim0⟩
  | succ n ih =>
      obtain ⟨v₀, hv₀_prim, hv₀_min⟩ := hb.exists_isPrimitive_forall_dotProduct_mulVec_le
      obtain ⟨γ₁, hγ₁_col0⟩ := hv₀_prim.exists_units_matrix_mulVec_single_eq 0
      let γ₁R : GL (Fin (n + 1)) ℝ := Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ₁
      let b₁ := γ₁R.valᵀ * b * γ₁R.val
      have hb₁ : b₁.PosDef := by
        simpa only [b₁, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
          using (Matrix.IsUnit.posDef_star_left_conjugate_iff γ₁R.isUnit).mpr hb
      obtain ⟨u₀, b_sub, hb_sub, hb₁_schur⟩ :=
        hb₁.exists_eq_transpose_upperBorder_mul_cornerBlockSucc_mul
      obtain ⟨γ', N', d', hN'_ut, hd'_pos, hN'_bound, hd'_ratio, hγ'_eq⟩ := ih hb_sub
      let w : Fin n → ℝ := u₀ ᵥ* (γ'.map (Int.castRingHom ℝ)).val
      let z : Fin n → ℤ := fun j ↦ -⌊w j + 1 / 2⌋
      let w' : Fin n → ℝ := (Int.cast ∘ z) + w
      have hw'_bound (j : Fin n) : |w' j| ≤ 1 / 2 := abs_le.mpr
        ⟨by dsimp [w', z]; push_cast; linarith [Int.floor_le (w j + 1 / 2)],
          by dsimp [w', z]; push_cast; linarith [Int.lt_floor_add_one (w j + 1 / 2)]⟩
      let γ : GL (Fin (n + 1)) ℤ := γ₁ * Matrix.upperBorderUnit z γ'
      have hN_bound (i j : Fin (n + 1)) (hij : i < j) :
          |Matrix.upperBorder w' N' i j| ≤ 1 / 2 :=
        Fin.cases (fun h0 ↦ Fin.cases (fun h ↦ (lt_irrefl 0 h).elim)
          (fun j' _ ↦ by simpa using hw'_bound j') j h0)
          (fun i' h' ↦ Fin.cases (fun h ↦ (Fin.not_lt_zero _ h).elim)
            (fun j' h ↦ by simpa using hN'_bound i' j' (Fin.succ_lt_succ_iff.mp h)) j h') i hij
      have hγ_eq := composite_congruence_upperBorder (z := z) hb₁_schur hγ'_eq
      have hγ_col0 : γ.val *ᵥ Pi.single 0 1 = v₀ := by
        rw [show γ.val = γ₁.val * Matrix.upperBorder z γ'.val by simp [γ],
          ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_upperBorder_zero, hγ₁_col0]
      refine ⟨γ, Matrix.upperBorder w' N', Fin.cons (b₁ 0 0) d',
        (Matrix.isUpperUnitriangular_upperBorder_iff w' N').mpr hN'_ut,
        Fin.cases hb₁.diag_pos hd'_pos, hN_bound,
        fun i hi ↦ Fin.cases (fun _ ↦ ?_) (fun i' hi' ↦ ?_) i hi, hγ_eq⟩
      · exact first_pivot_le_four_thirds hv₀_min hγ_col0 hb₁.diag_pos hw'_bound hN'_ut hγ_eq
          ⟨0, by omega⟩ rfl
      · have hi'_lt : i'.val + 1 < n := by simp only [Fin.val_succ] at hi'; omega
        exact (show (⟨i'.succ.val + 1, hi'⟩ : Fin (n + 1)) = (⟨i'.val + 1, hi'_lt⟩ : Fin n).succ by
          ext; simp) ▸ hd'_ratio i' hi'_lt

/-- **Siegel reduction for positive-definite forms over `ℤ`.** There exists `C > 1` depending only
on `n` such that every positive-definite real `n × n` matrix is `GL (Fin n) ℤ`-congruent to a
`C`-reduced matrix. -/
theorem exists_reduced_GLZ (n : ℕ) :
    ∃ C : ℝ, 1 < C ∧ ∀ b : Matrix (Fin n) (Fin n) ℝ, b.PosDef →
      ∃ γ : GL (Fin n) ℤ, IsReduced C
        (((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b *
          ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
  obtain ⟨C, hC_gt, hC_red⟩ := exists_isReduced_of_cholesky_bound n (4 / 3)
  refine ⟨C, hC_gt, fun b hb ↦ ?_⟩
  obtain ⟨γ, N, d, hN_ut, hd_pos, hN_bound, hd_ratio, hγ_eq⟩ := exists_cholesky_reduced_GLZ n hb
  exact ⟨γ, hγ_eq ▸ (hC_red hN_ut hd_pos
    (fun i j hij ↦ (hN_bound i j hij).trans (by norm_num)) hd_ratio).2⟩

/-- Reversed-Cholesky right-Gram identity: reindexing a Cholesky congruence of
`(g * gᵀ).submatrix Fin.revPerm Fin.revPerm` back by `Fin.revPerm` gives `h * hᵀ = p * pᵀ` for
`h = γ⁻¹ * g` (where `γ = revPerm.reindexGL (η⁻ᵀ)`) and `p = V * diag(√(d ∘ rev))`. -/
private theorem revPerm_mul_transpose_eq {n : ℕ} (g : GL (Fin n) ℝ) (η : GL (Fin n) ℤ)
    {N : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ} (hd_pos : ∀ i, 0 < d i)
    (hV_ut : (Nᵀ.submatrix Fin.revPerm Fin.revPerm).IsUpperUnitriangular)
    (hη_eq : (η.map (Int.castRingHom ℝ)).valᵀ *
        ((g.val * g.valᵀ).submatrix Fin.revPerm Fin.revPerm) *
        (η.map (Int.castRingHom ℝ)).val = Nᵀ * Matrix.diagonal d * N) :
    let γ : GL (Fin n) ℤ := Fin.revPerm.reindexGL ℤ (Matrix.GeneralLinearGroup.inverseTranspose η)
    let h : GL (Fin n) ℝ := (γ⁻¹).map (Int.castRingHom ℝ) * g
    let a : Fin n → ℝ := fun i ↦ Real.sqrt (d (Fin.rev i))
    let p : GL (Fin n) ℝ :=
      hV_ut.toGL * diagGL (fun i ↦ Units.mk0 (a i) (Real.sqrt_pos.mpr (hd_pos (Fin.rev i))).ne')
    h.val * h.valᵀ = p.val * p.valᵀ := by
  intro γ h a p
  let ηR := (η.map (Int.castRingHom ℝ)).val
  let γiR := ((γ⁻¹).map (Int.castRingHom ℝ)).val
  have hγ_inv : ηR.submatrix Fin.revPerm Fin.revPerm = γiRᵀ := by
    ext i j
    simp [γiR, ηR, γ, ← map_inv, Matrix.GeneralLinearGroup.coe_inverseTranspose, Fin.revPerm_symm]
  have hsub := congrArg (fun M : Matrix _ _ ℝ ↦ M.submatrix Fin.revPerm Fin.revPerm) hη_eq
  have hrev_comp : (Fin.revPerm : Fin n ≃ Fin n) ∘ Fin.revPerm = id := by ext; simp
  have hlhs : (ηRᵀ * ((g.val * g.valᵀ).submatrix Fin.revPerm Fin.revPerm) * ηR).submatrix
      Fin.revPerm Fin.revPerm = h.val * h.valᵀ := by
    rw [Matrix.submatrix_transpose_mul_mul_equiv _ _ Fin.revPerm Fin.revPerm,
      Matrix.submatrix_submatrix, hrev_comp, Matrix.submatrix_id_id, hγ_inv,
      Matrix.transpose_transpose]
    simp only [h, γiR, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have hdiag_rev : (Matrix.diagonal d).submatrix Fin.revPerm Fin.revPerm =
      Matrix.diagonal a * (Matrix.diagonal a)ᵀ := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext i j; by_cases hij : i = j <;>
      simp [a, Matrix.diagonal, hij, Real.mul_self_sqrt (hd_pos (Fin.rev j)).le]
  have hrhs : (Nᵀ * Matrix.diagonal d * N).submatrix Fin.revPerm Fin.revPerm =
      p.val * p.valᵀ := by
    rw [Matrix.submatrix_transpose_mul_mul_equiv _ _ Fin.revPerm Fin.revPerm, hdiag_rev]
    simp only [p, hV_ut.coe_toGL, diagGL_coe, Units.val_mk0, Units.val_mul,
      Matrix.transpose_mul, Matrix.transpose_submatrix, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  exact hlhs.symm.trans (hsub.trans hrhs)

/-- **Classical Siegel reduction for `GL (Fin n) ℝ`:** every element of `GL (Fin n) ℝ` decomposes
as `γ * s` with `γ : GL (Fin n) ℤ` and `s ∈ siegelDomain n (1 / 2) (Real.sqrt 3 / 2)`. -/
theorem exists_mul_mem_siegelDomain_GLZ {n : ℕ} (g : GL (Fin n) ℝ) :
    ∃ γ : GL (Fin n) ℤ, ∃ s ∈ siegelDomain n (1 / 2) (Real.sqrt 3 / 2),
      g = γ.map (Int.castRingHom ℝ) * s := by
  -- Apply `exists_cholesky_reduced_GLZ` to the order-reversed right Gram matrix
  -- `B = (g * gᵀ).submatrix Fin.revPerm Fin.revPerm`: reversing indices turns the left-transpose
  -- factorization `ηᵀ * B * η = Nᵀ * diag(d) * N` into the `U A K` right-Gram identity
  -- `(γ⁻¹ * g) * (γ⁻¹ * g)ᵀ = p * pᵀ` with `V = Nᵀ.submatrix rev rev` upper unitriangular and
  -- `a i = √(d (rev i))` satisfying `a i / a (i + 1) ≥ √(3 / 4) = √3 / 2`.
  have hggT : (g.val * g.valᵀ).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_one] using
      (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := (1 : Matrix (Fin n) (Fin n) ℝ))
        g.isUnit).mpr Matrix.PosDef.one
  obtain ⟨η, N, d, hN_ut, hd_pos, hN_bound, hd_ratio, hη_eq⟩ :=
    exists_cholesky_reduced_GLZ n (hggT.submatrix Fin.revPerm.injective)
  have hV_ut : (Nᵀ.submatrix Fin.revPerm Fin.revPerm).IsUpperUnitriangular :=
    hN_ut.transpose_submatrix_of_strictAnti (fun _ _ h ↦ Fin.rev_lt_rev.mpr h)
  let γ : GL (Fin n) ℤ := Fin.revPerm.reindexGL ℤ (Matrix.GeneralLinearGroup.inverseTranspose η)
  let a : Fin n → ℝ := fun i ↦ Real.sqrt (d (Fin.rev i))
  have ha_pos : ∀ i, 0 < a i := fun i ↦ Real.sqrt_pos.mpr (hd_pos (Fin.rev i))
  let p : GL (Fin n) ℝ := hV_ut.toGL * diagGL (fun i ↦ Units.mk0 (a i) (ha_pos i).ne')
  let h : GL (Fin n) ℝ := (γ⁻¹).map (Int.castRingHom ℝ) * g
  refine ⟨γ, p * (p⁻¹ * h), mem_siegelDomain_iff.mpr
    ⟨hV_ut.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hV_ut, a, ha_pos,
      p⁻¹ * h, GLOrthogonal.inv_mul_mem_of_mul_transpose_eq
        (revPerm_mul_transpose_eq g η hd_pos hV_ut hη_eq),
      fun i j hij ↦ by
        simpa [hV_ut.coe_toGL] using
          hN_bound (Fin.rev j) (Fin.rev i) (Fin.rev_lt_iff.mpr (by simpa using hij)),
      fun i hi ↦ ?_, rfl⟩,
    by simp [h, map_inv, mul_inv_cancel_left]⟩
  let j : Fin n := Fin.rev ⟨i.val + 1, hi⟩
  have hj : j.val + 1 < n := by simp only [j, Fin.val_rev]; omega
  have hj_succ : (⟨j.val + 1, hj⟩ : Fin n) = Fin.rev i := by ext; simp only [j, Fin.val_rev]; omega
  have hsqrt : Real.sqrt (3 / 4) * Real.sqrt (d j) ≤ Real.sqrt (d (Fin.rev i)) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith [hj_succ ▸ hd_ratio j hj])
  have hsqrt_34 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
      (by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num)
  rw [le_div_iff₀ (ha_pos ⟨i.val + 1, hi⟩)]; exact hsqrt_34 ▸ hsqrt

end Reduction

end TauCeti.RealSiegel
