/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Isotropic
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Sectional
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Dimension
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Extension
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.LinearAlgebra.Multilinear.SectionalPolarization

/-!
# Berger's mixed-component estimate, strict quarter pinching, and Fubini–Study sharpness

For an algebraic curvature tensor `r : FourTensor V`, Berger's polarization estimate gives
`|r(f₀, f₁, f₂, f₃)| ≤ (2 / 3) (b - a)` whenever sectional curvatures in `span(f)` lie in `[a, b]`,
yielding `min a ((4 a - b) / 3) * (1 + l²) * (1 + m²) ≤ pic2Expression r f l m`. Weak quarter
pinching implies `IsPIC2FourFrame r`, strict quarter pinching places `r` in `interior {q |
IsPIC2FourFrame q.1}`, and `fubiniStudy J` witnesses sharpness on the boundary.

## Main definitions & statements

* `fubiniStudy`, `IsAlgebraicCurvature.abs_apply_orthonormal_le`,
  `IsAlgebraicCurvature.pic2Expression_pos_of_strict_quarterPinching`,
  `mem_interior_isPIC2FourFrame_of_quarterPinched`, `IsPIC2FourFrame.apply_self_nonneg`,
  `notMem_interior_isPIC2FourFrame_fubiniStudy`, `exists_isPIC2FourFrame_notMem_interior_fin_four`.

## References

* M. Berger, Bull. Soc. Math. France 88 (1960), 57–71.
* S. Brendle and R. Schoen, J. Amer. Math. Soc. 22 (2009), 287–307.
-/

public section

open Set
open scoped InnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

/-! ### Berger's mixed-component estimate and strict quarter pinching -/

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem apply_add_smul_self_mem_Icc_of_span {r : FourTensor V} {f : Fin 4 → V}
    (hf : Orthonormal ℝ f) {a b : ℝ}
    (hsec : ∀ u v : V, u ∈ Submodule.span ℝ (range f) → v ∈ Submodule.span ℝ (range f) →
      Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b)
    {i j k l : Fin 4} (hinj : Function.Injective ![i, j, k, l]) (c₁ c₂ : Bool) :
    let s₁ : ℝ := if c₁ then 1 else -1; let s₂ : ℝ := if c₂ then 1 else -1
    4 * a ≤ r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] ∧
      r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] ≤ 4 * b := by
  intro s₁ s₂
  have hcomp : f ∘ ![i, j, k, l] = ![f i, f j, f k, f l] := by funext t; fin_cases t <;> rfl
  have hf4 : Orthonormal ℝ ![f i, f j, f k, f l] := hcomp ▸ hf.comp ![i, j, k, l] hinj
  have hfs : Orthonormal ℝ ![f i, s₁ • f j, f k, s₂ • f l] :=
    hf4.orthonormal_of_forall_eq_or_eq_neg fun t ↦ by
      fin_cases t; exacts [.inl rfl, by cases c₁ <;> simp [s₁], .inl rfl, by cases c₂ <;> simp [s₂]]
  have hmem (p q : Fin 4) (s : ℝ) : (√2)⁻¹ • (f p + s • f q) ∈ Submodule.span ℝ (range f) :=
    Submodule.smul_mem _ _ <| Submodule.add_mem _ (Submodule.subset_span ⟨p, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩))
  have hbds := hsec _ _ (hmem i j s₁) (hmem k l s₂) hfs.inv_sqrt_two_add_pair
  have hpow : (√2)⁻¹ * (√2)⁻¹ * (√2)⁻¹ * (√2)⁻¹ = 1 / 4 := by
    rw [← mul_inv, mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [r.apply_smul_first, r.apply_smul_second, r.apply_smul_third, r.apply_smul_fourth,
    ← mul_assoc, ← mul_assoc, ← mul_assoc, hpow] at hbds
  exact ⟨by linarith, by linarith⟩

/-- **Berger's mixed-component estimate (localized to `span(f)`).** If `a ≤ r ![u, v, u, v] ≤ b` on
orthonormal pairs in `span(range f)`, then `|r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a)`. -/
theorem IsAlgebraicCurvature.abs_apply_orthonormal_le_of_span {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {f : Fin 4 → V} (hf : Orthonormal ℝ f) {a b : ℝ}
    (hsec : ∀ u v : V, u ∈ Submodule.span ℝ (range f) → v ∈ Submodule.span ℝ (range f) →
      Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    |r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a) := by
  have hpol := LinearMap.twentyFour_mul_apply_eq_of_cyclic_eq_zero (T := toLinearMap₄ r)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_first u v z w)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_last u v z w)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.cyclic_eq_zero u v z w)
    (f 0) (f 1) (f 2) (f 3)
  have hflip (x y : V) : r ![x, y, y, x] = -r ![x, y, x, y] := by
    linarith [hr.antisymm_last x y x y]
  simp only [toLinearMap₄_apply, hflip] at hpol
  have bp (c₁ c₂ : Bool) := And.intro
    (apply_add_smul_self_mem_Icc_of_span (i := 0) (j := 3) (k := 1) (l := 2) hf hsec (by decide)
      c₁ c₂)
    (apply_add_smul_self_mem_Icc_of_span (i := 1) (j := 3) (k := 0) (l := 2) hf hsec (by decide)
      c₁ c₂)
  obtain ⟨b1, b5⟩ := bp true true; obtain ⟨b2, b6⟩ := bp true false
  obtain ⟨b3, b7⟩ := bp false true; obtain ⟨b4, b8⟩ := bp false false
  simp only [↓reduceIte, Bool.false_eq_true, one_smul, neg_one_smul,
    ← sub_eq_add_neg] at b1 b2 b3 b4 b5 b6 b7 b8
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- **Berger's mixed-component estimate.** Sectional curvatures in `[a, b]` imply
`|r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a)` on orthonormal four-frames `f`. -/
theorem IsAlgebraicCurvature.abs_apply_orthonormal_le {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {f : Fin 4 → V} (hf : Orthonormal ℝ f) {a b : ℝ}
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    |r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a) :=
  hr.abs_apply_orthonormal_le_of_span hf fun u v _ _ huv ↦ hsec u v huv

/-- Berger's estimate in terms of `sectionalMin r` and `sectionalMax r`. -/
theorem IsAlgebraicCurvature.abs_apply_orthonormal_le_sectionalMax_sub_sectionalMin
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) {f : Fin 4 → V} (hf : Orthonormal ℝ f) :
    |r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (sectionalMax r - sectionalMin r) :=
  hr.abs_apply_orthonormal_le hf fun _ _ huv ↦
    ⟨sectionalMin_le_of_orthonormal r huv, le_sectionalMax_of_orthonormal r huv⟩

/-- **Quantitative lower bound on `pic2Expression` from sectional bounds.** Sectional curvatures in
`[a, b]` imply `min a ((4 * a - b) / 3) * (1 + l ^ 2) * (1 + m ^ 2) ≤ pic2Expression r f l m`. -/
theorem IsAlgebraicCurvature.le_pic2Expression_of_sectional_mem_Icc {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {a b : ℝ}
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b)
    {f : Fin 4 → V} (hf : Orthonormal ℝ f) (l m : ℝ) :
    min a ((4 * a - b) / 3) * (1 + l ^ 2) * (1 + m ^ 2) ≤ pic2Expression r f l m := by
  have hp : |l * m * r ![f 0, f 1, f 2, f 3]| ≤ |l * m| * ((2 / 3) * (b - a)) := by
    rw [abs_mul]; gcongr; exact hr.abs_apply_orthonormal_le hf hsec
  have h (i j : Fin 4) (hij : i ≠ j) := hsec (f i) (f j) (hf.pair hij)
  have h02 := h 0 2 (by decide)
  have hamgm : 4 * |l * m| ≤ (1 + l ^ 2) * (1 + m ^ 2) := by
    nlinarith [sq_abs l, sq_abs m, abs_mul l m, sq_nonneg (1 - |l * m|), sq_nonneg (|l| - |m|)]
  have hpen := mul_le_mul_of_nonneg_left hamgm (by linarith [h02.1, h02.2] : 0 ≤ (b - a) / 3)
  have hstep := mul_le_mul_of_nonneg_right (min_le_right a ((4 * a - b) / 3))
    (by positivity : 0 ≤ (1 + l ^ 2) * (1 + m ^ 2))
  rw [pic2Expression_def]
  nlinarith [(abs_le.1 hp).2, h02.1, sq_nonneg l, sq_nonneg m,
    mul_le_mul_of_nonneg_left (h 0 3 (by decide)).1 (sq_nonneg l),
    mul_le_mul_of_nonneg_left (h 1 2 (by decide)).1 (sq_nonneg m),
    mul_le_mul_of_nonneg_left (h 1 3 (by decide)).1 (mul_nonneg (sq_nonneg l) (sq_nonneg m))]

/-- **Weak quarter pinching gives `PIC2`.** Sectional curvatures in `[a, b]` with `0 ≤ a` and
`b ≤ 4 * a` imply `IsPIC2FourFrame r`. -/
theorem IsAlgebraicCurvature.isPIC2FourFrame_of_weak_quarterPinching {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {a b : ℝ} (ha : 0 ≤ a) (hab : b ≤ 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    IsPIC2FourFrame r := (isPIC2FourFrame_def r).2 fun f hf l _ m _ ↦
  (mul_nonneg (mul_nonneg (le_min ha (by linarith)) (by positivity)) (by positivity)).trans
    (hr.le_pic2Expression_of_sectional_mem_Icc hsec hf l m)

/-- **Strict quarter pinching gives strict `PIC2`** (Brendle–Schoen). Sectional curvatures in
`[a, b]` with `0 < a` and `b < 4 * a` imply `0 < pic2Expression r f l m`. -/
theorem IsAlgebraicCurvature.pic2Expression_pos_of_strict_quarterPinching {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {a b : ℝ} (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b)
    {f : Fin 4 → V} (hf : Orthonormal ℝ f) (l m : ℝ) : 0 < pic2Expression r f l m :=
  (mul_pos (mul_pos (lt_min ha (by linarith)) (by positivity)) (by positivity)).trans_le
    (hr.le_pic2Expression_of_sectional_mem_Icc hsec hf l m)

/-- Strict quarter pinching with `0 < a` and `b < 4 * a` places `r` in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}`. -/
theorem mem_interior_isPIC2FourFrame_of_sectional_mem_Icc (r : algebraicCurvatureSubmodule V)
    {a b : ℝ} (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r.val ![u, v, u, v] ∧ r.val ![u, v, u, v] ≤ b) :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.val} := by
  have hmin : 0 < min a ((4 * a - b) / 3) := lt_min ha (by linarith)
  refine mem_interior_isPIC2FourFrame_of_exists_pos_le hmin fun f hf l _ m _ ↦
    (le_mul_of_one_le_right hmin.le
      (by nlinarith [sq_nonneg l, sq_nonneg m] : 1 ≤ (1 + l ^ 2) * (1 + m ^ 2))).trans ?_
  simpa only [mul_assoc] using
    (mem_algebraicCurvatureSubmodule.1 r.property).le_pic2Expression_of_sectional_mem_Icc
      hsec hf l m

/-- When `4 ≤ finrank ℝ V`, every four-tensor in `IsPIC2FourFrame` has `0 ≤ sectionalMin r`. -/
theorem IsPIC2FourFrame.sectionalMin_nonneg {r : FourTensor V} (hpic : IsPIC2FourFrame r)
    (hn : 4 ≤ Module.finrank ℝ V) : 0 ≤ sectionalMin r := by
  rw [sectionalMin_def]; refine Real.sInf_nonneg ?_; rintro _ ⟨u, hu, rfl⟩
  obtain ⟨f, hf, h0, h2⟩ := (hu.pair zero_ne_one).exists_fin_four_extension hn
  simpa only [pic2Expression_zero_zero, h0, h2] using
    (isPIC2FourFrame_def r).1 hpic f hf 0 (by norm_num) 0 (by norm_num)

/-- When `4 ≤ finrank ℝ V`, every algebraic curvature tensor in `IsPIC2FourFrame` has
`0 ≤ r ![u, v, u, v]` on all pairs `(u, v)`. -/
theorem IsPIC2FourFrame.apply_self_nonneg {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hpic : IsPIC2FourFrame r) (hn : 4 ≤ Module.finrank ℝ V) (u v : V) :
    0 ≤ r ![u, v, u, v] := by
  by_cases h : LinearIndependent ℝ ![u, v]
  · exact (mul_nonneg (hpic.sectionalMin_nonneg hn)
      (Matrix.posDef_gram_of_linearIndependent h).det_pos.le).trans
      (hr.sectionalMin_mul_det_gram_le_and_le_sectionalMax u v).1
  · simp [hr.apply_self_eq_zero_of_not_linearIndependent h]

end InnerProductSpace

/-! ### Finite-dimensional quarter pinching and Fubini–Study sharpness -/

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- In dimension `≥ 2`, pointwise positivity of `r ![u, v, u, v] / det(Gram(u, v))` implies
`0 < sectionalMin r`. -/
theorem sectionalMin_pos_of_quarterPinched (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V)
    (hpos : ∀ u v : V, LinearIndependent ℝ ![u, v] →
      0 < r ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det) : 0 < sectionalMin r := by
  obtain ⟨u₀, v₀, h₀, hmin⟩ := exists_orthonormal_eq_sectionalMin hn r
  have hp₀ := hpos u₀ v₀ h₀.linearIndependent
  rwa [Matrix.gram_eq_one_iff_orthonormal.2 h₀, Matrix.det_one, div_one, hmin] at hp₀

/-- In dimension `≥ 2`, pointwise strict quarter pinching gives
`sectionalMax r < 4 * sectionalMin r`. -/
theorem sectionalMax_lt_four_mul_sectionalMin_of_quarterPinched
    (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V)
    (hpinch : ∀ u v u' v' : V, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
      r ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det <
        4 * (r ![u', v', u', v'] / (Matrix.gram ℝ ![u', v']).det)) :
    sectionalMax r < 4 * sectionalMin r := by
  obtain ⟨u₀, v₀, h₀, hmin⟩ := exists_orthonormal_eq_sectionalMin hn r
  obtain ⟨u₁, v₁, h₁, hmax⟩ := exists_orthonormal_eq_sectionalMax hn r
  have hp := hpinch u₁ v₁ u₀ v₀ h₁.linearIndependent h₀.linearIndependent
  rwa [Matrix.gram_eq_one_iff_orthonormal.2 h₀, Matrix.gram_eq_one_iff_orthonormal.2 h₁,
    Matrix.det_one, div_one, div_one, hmin, hmax] at hp

/-- Unquantified pointwise strict quarter pinching places `r` in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}`. -/
theorem mem_interior_isPIC2FourFrame_of_quarterPinched (r : algebraicCurvatureSubmodule V)
    (hpinch : ∀ u v u' v' : V, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
      0 < r.val ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det ∧
        r.val ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det <
          4 * (r.val ![u', v', u', v'] / (Matrix.gram ℝ ![u', v']).det)) :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.val} := by
  by_cases hn4 : 4 ≤ Module.finrank ℝ V
  · have hn2 : 2 ≤ Module.finrank ℝ V := by omega
    exact mem_interior_isPIC2FourFrame_of_sectional_mem_Icc r
      (sectionalMin_pos_of_quarterPinched hn2 r.val fun u v huv ↦ (hpinch u v u v huv huv).1)
      (sectionalMax_lt_four_mul_sectionalMin_of_quarterPinched hn2 r.val fun u v u' v' huv huv' ↦
        (hpinch u v u' v' huv huv').2)
      fun _ _ huv ↦
        ⟨sectionalMin_le_of_orthonormal r.val huv, le_sectionalMax_of_orthonormal r.val huv⟩
  · refine mem_interior_isPIC2FourFrame_iff_forall_pos.2 fun f hf ↦ ?_
    have := hf.linearIndependent.fintype_card_le_finrank; rw [Fintype.card_fin] at this; omega

/-! ### Constant holomorphic sectional curvature (Fubini–Study) and sharpness -/

/-- Fubini–Study four-tensor of `J`; for orthogonal `J`, it is an algebraic curvature tensor of
constant holomorphic sectional curvature `4`. -/
def fubiniStudy (J : AlmostComplexStructure V) : FourTensor V :=
  ofLinearMap₄ <| LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ
      (fun z w ↦ ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ +
        ⟪J u, z⟫_ℝ * ⟪J v, w⟫_ℝ - ⟪J u, w⟫_ℝ * ⟪J v, z⟫_ℝ + 2 * ⟪J u, v⟫_ℝ * ⟪J z, w⟫_ℝ)
      (fun _ _ _ ↦ by simp [inner_add_right, inner_add_left, map_add]; ring)
      (fun _ _ _ ↦ by simp [real_inner_smul_right, real_inner_smul_left, map_smul]; ring)
      (fun _ _ _ ↦ by simp [inner_add_right]; ring)
      (fun _ _ _ ↦ by simp [real_inner_smul_right]; ring))
    (fun _ _ _ ↦ by ext; simp [inner_add_left, map_add]; ring)
    (fun _ _ _ ↦ by ext; simp [real_inner_smul_left, map_smul]; ring)
    (fun _ _ _ ↦ by ext; simp [inner_add_left, inner_add_right, map_add]; ring)
    (fun _ _ _ ↦ by ext; simp [real_inner_smul_left, real_inner_smul_right, map_smul]; ring)

/-- Evaluation of the Fubini–Study four-tensor. -/
@[simp]
theorem fubiniStudy_apply (J : AlmostComplexStructure V) (u v z w : V) :
    fubiniStudy J ![u, v, z, w] = ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ +
      ⟪J u, z⟫_ℝ * ⟪J v, w⟫_ℝ - ⟪J u, w⟫_ℝ * ⟪J v, z⟫_ℝ + 2 * ⟪J u, v⟫_ℝ * ⟪J z, w⟫_ℝ := by
  simp [fubiniStudy]

/-- For orthogonal `J`, `fubiniStudy J` is an algebraic curvature tensor. -/
theorem isAlgebraicCurvature_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) : IsAlgebraicCurvature (fubiniStudy J) := by
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [fubiniStudy_apply]
  · rw [J.inner_apply_left_eq_neg_swap hJ v u]; ring
  · rw [J.inner_apply_left_eq_neg_swap hJ w z]; ring
  · rw [real_inner_comm u z, real_inner_comm v w, real_inner_comm v z, real_inner_comm u w,
      J.inner_apply_left_eq_neg_swap hJ z u, J.inner_apply_left_eq_neg_swap hJ w v,
      J.inner_apply_left_eq_neg_swap hJ z v, J.inner_apply_left_eq_neg_swap hJ w u]; ring
  · rw [real_inner_comm u z, real_inner_comm u v, real_inner_comm v z,
      J.inner_apply_left_eq_neg_swap hJ v u, J.inner_apply_left_eq_neg_swap hJ z u,
      J.inner_apply_left_eq_neg_swap hJ z v]; ring

/-- With orthogonal `J`, `fubiniStudy J ![u, v, u, v] = ‖u‖² ‖v‖² - ⟪u, v⟫² + 3 ⟪J u, v⟫²`. -/
theorem fubiniStudy_apply_self {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) (u v : V) :
    fubiniStudy J ![u, v, u, v] = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 + 3 * ⟪J u, v⟫_ℝ ^ 2 := by
  rw [fubiniStudy_apply, J.inner_apply_self hJ u, J.inner_apply_self hJ v,
    J.inner_apply_left_eq_neg_swap hJ v u, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm u v]; ring

/-- On an orthonormal pair `(u, v)`, `1 ≤ fubiniStudy J ![u, v, u, v] ≤ 4`. -/
theorem fubiniStudy_sectional_mem_Icc {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    1 ≤ fubiniStudy J ![u, v, u, v] ∧ fubiniStudy J ![u, v, u, v] ≤ 4 := by
  have hu : ‖u‖ = 1 := huv.1 0; have hv : ‖v‖ = 1 := huv.1 1
  have h0 : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  have hsq : ⟪J u, v⟫_ℝ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 <| by
    simpa only [J.norm_apply hJ, hu, hv, mul_one] using abs_real_inner_le_norm (J u) v
  rw [fubiniStudy_apply_self hJ, hu, hv, h0]
  exact ⟨by nlinarith [sq_nonneg ⟪J u, v⟫_ℝ], by linarith⟩

/-- On a holomorphic unit pair `(u, J u)`, `![u, J u]` is orthonormal with curvature `4`. -/
theorem fubiniStudy_apply_holomorphic {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) {u : V} (hu : ‖u‖ = 1) :
    Orthonormal ℝ ![u, J u] ∧ fubiniStudy J ![u, J u, u, J u] = 4 := by
  have h0 : ⟪u, J u⟫_ℝ = 0 := by rw [real_inner_comm, J.inner_apply_self hJ]
  refine ⟨by simp [hu, J.norm_apply hJ, h0], ?_⟩
  rw [fubiniStudy_apply_self hJ, hu, J.norm_apply hJ, h0, real_inner_self_eq_norm_sq,
    J.norm_apply hJ, hu]; norm_num

/-- **Sharpness of Berger's bound.** On a unitary orthonormal four-frame `![X, J X, Y, J Y]`,
`fubiniStudy J ![X, J X, Y, J Y] = 2` and `pic2Expression (fubiniStudy J) _ 1 1 = 0`. -/
theorem fubiniStudy_apply_unitary {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) {X Y : V} (hf : Orthonormal ℝ ![X, J X, Y, J Y]) :
    fubiniStudy J ![X, J X, Y, J Y] = 2 ∧
      pic2Expression (fubiniStudy J) ![X, J X, Y, J Y] 1 1 = 0 := by
  simp only [orthonormal_vecCons_iff, orthonormal_subsingleton_iff, Fin.forall_fin_succ,
    Fin.forall_fin_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, and_true] at hf
  rcases hf with ⟨hX, ⟨_, hXY, hXJY⟩, _, ⟨hJXY, hJXJY⟩, hY, _, _⟩
  have hmix : fubiniStudy J ![X, J X, Y, J Y] = 2 := by
    rw [fubiniStudy_apply]; simp only [J.apply_apply, hXY, hXJY, hJXY, hJXJY, inner_neg_left,
      real_inner_self_eq_norm_sq, J.norm_apply hJ, hX, hY]; ring
  refine ⟨hmix, ?_⟩
  simp only [pic2Expression_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hmix,
    fubiniStudy_apply_self hJ, J.apply_apply, J.norm_apply hJ, hX, hY, hXY, hXJY, hJXY, hJXJY,
    inner_neg_left]; ring

/-- `fubiniStudy J` lies in `IsPIC2FourFrame` for an orthogonal almost complex structure `J`. -/
theorem isPIC2FourFrame_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) : IsPIC2FourFrame (fubiniStudy J) :=
  (isAlgebraicCurvature_fubiniStudy hJ).isPIC2FourFrame_of_weak_quarterPinching
    zero_le_one (by norm_num) (fun _ _ huv ↦ fubiniStudy_sectional_mem_Icc hJ huv)

/-- **Weak quarter pinching does not imply `PIC2` interior.** In dimension `≥ 4`, `fubiniStudy J`
lies outside `interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}`. -/
theorem notMem_interior_isPIC2FourFrame_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) (hn : 4 ≤ Module.finrank ℝ V) :
    (⟨fubiniStudy J, mem_algebraicCurvatureSubmodule.2 (isAlgebraicCurvature_fubiniStudy hJ)⟩ :
       algebraicCurvatureSubmodule V) ∉
      interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.val} := by
  obtain ⟨k, hk⟩ := J.even_finrank_real
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) k (by omega)
  let idx : Fin 4 ↪ Fin (2 * k) := Fin.castLEEmb (by omega)
  have hf : Orthonormal ℝ ![b (idx 0), J (b (idx 0)), b (idx 2), J (b (idx 2))] := by
    convert b.orthonormal.comp idx idx.injective using 1
    funext i; fin_cases i; exacts [rfl, (hb ⟨0, by omega⟩).symm, rfl, (hb ⟨1, by omega⟩).symm]
  intro hint
  linarith [(mem_interior_isPIC2FourFrame_iff_forall_pos.1 hint) _ hf 1 (by norm_num) 1
    (by norm_num), (fubiniStudy_apply_unitary hJ hf).2]

/-- Four-dimensional boundary witness on `EuclideanSpace ℝ (Fin 4)`: an algebraic curvature tensor
with sectional curvatures in `[1, 4]` lying in `IsPIC2FourFrame` but not in its interior. -/
theorem exists_isPIC2FourFrame_notMem_interior_fin_four :
    ∃ r : algebraicCurvatureSubmodule (EuclideanSpace ℝ (Fin 4)),
      IsPIC2FourFrame r.val ∧ (∀ u v, Orthonormal ℝ ![u, v] →
          1 ≤ r.val ![u, v, u, v] ∧ r.val ![u, v, u, v] ≤ 4) ∧
        r ∉ interior
          {q : algebraicCurvatureSubmodule (EuclideanSpace ℝ (Fin 4)) | IsPIC2FourFrame q.val} := by
  obtain ⟨J, hJnorm⟩ := AlmostComplexStructure.exists_forall_norm_apply_eq
    (V := EuclideanSpace ℝ (Fin 4)) ⟨2, by simp⟩
  have hJ : ∀ u v : EuclideanSpace ℝ (Fin 4), ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ :=
    ({ J.toLinearMap with norm_map' := hJnorm } : _ →ₗᵢ[ℝ] _).inner_map_map
  exact ⟨⟨fubiniStudy J, mem_algebraicCurvatureSubmodule.2 (isAlgebraicCurvature_fubiniStudy hJ)⟩,
    isPIC2FourFrame_fubiniStudy hJ, fun _ _ huv ↦ fubiniStudy_sectional_mem_Icc hJ huv,
    notMem_interior_isPIC2FourFrame_fubiniStudy hJ (by simp)⟩

end FiniteDimensional

end TauCeti.FourTensor
