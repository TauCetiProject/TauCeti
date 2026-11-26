/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Positive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.PosDef.SiegelReduction.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fin.Rev
import TauCeti.Algebra.Module.Primitive
import TauCeti.LinearAlgebra.Matrix.CornerBlockSucc
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
import TauCeti.LinearAlgebra.Matrix.PosDef.Northcott

/-!
# Siegel reduction for positive-definite forms and `GL_n(ℝ)`

For `GL (Fin n) ℝ` with left `GL (Fin n) ℤ`-action, the standard real Siegel domain `Σ_n(u, t)` in
`U A K` coordinates consists of products `v * diag(a) * k` with `v` upper unitriangular satisfying
`|v i j| ≤ u` (`i < j`), positive diagonal `a` with `a i / a (i + 1) ≥ t`, and `k ∈ O(n)`. The Gram
map `gram g = (g⁻¹)ᵀ * g⁻¹` identifies right `O(n)`-cosets with positive-definite forms and
intertwines left multiplication by `γ` with congruence by `γ⁻¹`.

## Main definitions and results

* `TauCeti.RealSiegel.gram`, `TauCeti.RealSiegel.siegelDomain`,
  `TauCeti.RealSiegel.upperHalfPlaneGL`: the Gram map (`gram_def`, `posDef_gram`, `det_gram`,
  `gram_eq_iff_exists_mem_GLOrthogonal`), the standard Siegel domain `Σ_n(u, t)`, and the
  `SL_2(ℝ)` upper half-plane check (`upperHalfPlaneGL_mem_siegelDomain_iff`).
* `TauCeti.RealSiegel.exists_reducedSet_of_siegelDomain` and
  `TauCeti.RealSiegel.exists_siegelDomain_of_reducedSet`: two-sided cofinality between
  `siegelDomain n u t` (`t > 0`) and `reducedSet n C` (`C > 1`).
* `TauCeti.RealSiegel.exists_cholesky_reduced_GLZ`, `TauCeti.RealSiegel.exists_reduced_GLZ`, and
  `TauCeti.RealSiegel.exists_mul_mem_siegelDomain_GLZ`: Siegel-type Cholesky reduction over `ℤ`
  (size-reduced with pivot ratio `≤ 4 / 3`, constructed via an HKZ-style successive-minimum
  induction), `C`-reduced `GL (Fin n) ℤ`-equivalence, and
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

section Gram

/-- The positive-definite Gram matrix `(g⁻¹)ᵀ * g⁻¹` of the columns of `g⁻¹` for
`g : GL (Fin n) ℝ`. -/
def gram {n : ℕ} (g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
    ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)

/-- Unfolding characterization of `gram`. -/
theorem gram_def {n : ℕ} (g : GL (Fin n) ℝ) :
    gram g = ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := (rfl)

/-- Every invertible real matrix has positive-definite Gram matrix `gram g`. -/
theorem posDef_gram {n : ℕ} (g : GL (Fin n) ℝ) : (gram g).PosDef := by
  rw [gram_def]
  simpa only [Matrix.mul_one] using (Matrix.IsUnit.posDef_transpose_mul_mul_iff
    (B := (1 : Matrix (Fin n) (Fin n) ℝ)) g⁻¹.isUnit).mpr Matrix.PosDef.one

/-- The identity matrix has the identity Gram matrix. -/
@[simp] theorem gram_one {n : ℕ} : gram (1 : GL (Fin n) ℝ) = 1 := by simp [gram]

/-- Right multiplication by an orthogonal matrix leaves `gram` invariant. -/
theorem gram_mul_orthogonal {n : ℕ} (g : GL (Fin n) ℝ) {k : GL (Fin n) ℝ}
    (hk : k ∈ GLOrthogonal (Fin n) ℝ) : gram (g * k) = gram g := by
  have hkinv : k⁻¹.valᵀ * k⁻¹.val = 1 :=
    GLOrthogonal.mem_iff.mp ((GLOrthogonal (Fin n) ℝ).inv_mem hk)
  calc gram (g * k) = g⁻¹.valᵀ * (k⁻¹.valᵀ * k⁻¹.val) * g⁻¹.val := by
        simp only [gram_def, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = gram g := by rw [hkinv, Matrix.mul_one, ← gram_def]

/-- Two elements of `GL (Fin n) ℝ` have the same Gram matrix precisely when they differ on the
right by an orthogonal matrix. -/
theorem gram_eq_iff_exists_mem_GLOrthogonal {n : ℕ} {g h : GL (Fin n) ℝ} :
    gram h = gram g ↔ ∃ k ∈ GLOrthogonal (Fin n) ℝ, h = g * k := by
  refine ⟨fun hgram ↦ ⟨g⁻¹ * h, ?_, (mul_inv_cancel_left g h).symm⟩,
    fun ⟨_, hk, hk'⟩ ↦ hk' ▸ gram_mul_orthogonal g hk⟩
  have hmem : h⁻¹ * g ∈ GLOrthogonal (Fin n) ℝ := by
    rw [GLOrthogonal.mem_iff]
    calc (h⁻¹ * g).valᵀ * (h⁻¹ * g).val = g.valᵀ * gram h * g.val := by
          simp only [gram_def, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (g⁻¹ * g).valᵀ * (g⁻¹ * g).val := by
          rw [hgram]; simp only [gram_def, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by simp
  simpa only [mul_inv_rev, inv_inv] using (GLOrthogonal (Fin n) ℝ).inv_mem hmem

/-- Left multiplication by `γ` transforms `gram g` by congruence with `γ⁻¹`. -/
theorem gram_mul_left {n : ℕ} (γ g : GL (Fin n) ℝ) :
    gram (γ * g) = ((γ⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * gram g *
      ((γ⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  simp only [gram_def, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Congruence of `gram g` by `γ` equals `gram (γ⁻¹ * g)`. -/
theorem transpose_mul_gram_mul {n : ℕ} (γ g : GL (Fin n) ℝ) :
    (γ : Matrix (Fin n) (Fin n) ℝ)ᵀ * gram g * (γ : Matrix (Fin n) (Fin n) ℝ) =
      gram (γ⁻¹ * g) := by
  simpa only [inv_inv] using (gram_mul_left γ⁻¹ g).symm

/-- The determinant of `gram g` is `((det g)⁻¹) ^ 2`. -/
theorem det_gram {n : ℕ} (g : GL (Fin n) ℝ) :
    (gram g).det = ((g : Matrix (Fin n) (Fin n) ℝ).det)⁻¹ ^ 2 := by
  have hdet : g⁻¹.val.det = g.val.det⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one])
  rw [gram_def, Matrix.det_mul, Matrix.det_transpose, hdet, sq]

end Gram

section SiegelDomain

/-- The standard real Siegel domain `Σ_n(u, t)` in `GL (Fin n) ℝ` with respect to the upper
unitriangular subgroup, the positive diagonal torus, and the orthogonal group `O(n)`:
elements `v * diagGL a * k` with `|v i j| ≤ u` (`i < j`) and `t ≤ a i / a ⟨i + 1, _⟩`. -/
def siegelDomain (n : ℕ) (u t : ℝ) : Set (GL (Fin n) ℝ) :=
  {g | ∃ v ∈ upperUnitriangularGroup (Fin n) ℝ, ∃ a : Fin n → ℝ, ∃ ha : ∀ i, 0 < a i,
    ∃ k ∈ GLOrthogonal (Fin n) ℝ,
      (∀ i j : Fin n, i < j → |((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤ u) ∧
      (∀ (i : Fin n) (h : i.val + 1 < n), t ≤ a i / a ⟨i.val + 1, h⟩) ∧
      g = v * diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne') * k}

/-- Unfolding characterization of membership in `siegelDomain n u t`. -/
theorem mem_siegelDomain_iff {n : ℕ} {u t : ℝ} {g : GL (Fin n) ℝ} :
    g ∈ siegelDomain n u t ↔
      ∃ v ∈ upperUnitriangularGroup (Fin n) ℝ, ∃ a : Fin n → ℝ, ∃ ha : ∀ i, 0 < a i,
        ∃ k ∈ GLOrthogonal (Fin n) ℝ,
          (∀ i j : Fin n, i < j → |((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤ u) ∧
          (∀ (i : Fin n) (h : i.val + 1 < n), t ≤ a i / a ⟨i.val + 1, h⟩) ∧
          g = v * diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne') * k := Iff.rfl

/-- Increasing the off-diagonal bound `u` and decreasing the root-ratio bound `t` enlarges
`siegelDomain n u t`. -/
theorem siegelDomain_mono {n : ℕ} {u u' t t' : ℝ} (hu : u ≤ u') (ht : t' ≤ t) :
    siegelDomain n u t ⊆ siegelDomain n u' t' :=
  fun _ ⟨v, hv, a, ha, k, hk, hvb, har, hg⟩ ↦
    ⟨v, hv, a, ha, k, hk, fun i j hij ↦ (hvb i j hij).trans hu, fun i hi ↦ ht.trans (har i hi), hg⟩

/-- Right multiplication by an orthogonal matrix preserves `siegelDomain n u t`. -/
theorem mul_orthogonal_mem_siegelDomain {n : ℕ} {u t : ℝ} {g k' : GL (Fin n) ℝ}
    (hg : g ∈ siegelDomain n u t) (hk' : k' ∈ GLOrthogonal (Fin n) ℝ) :
    g * k' ∈ siegelDomain n u t :=
  let ⟨v, hv, a, ha, k, hk, hvb, har, heq⟩ := hg
  ⟨v, hv, a, ha, k * k', (GLOrthogonal (Fin n) ℝ).mul_mem hk hk', hvb, har,
    heq ▸ mul_assoc _ _ _⟩

/-- The identity lies in `siegelDomain n u t` whenever `0 ≤ u` and `t ≤ 1`. -/
theorem one_mem_siegelDomain {n : ℕ} {u t : ℝ} (hu : 0 ≤ u) (ht : t ≤ 1) :
    (1 : GL (Fin n) ℝ) ∈ siegelDomain n u t :=
  ⟨1, (upperUnitriangularGroup (Fin n) ℝ).one_mem, fun _ ↦ 1, fun _ ↦ one_pos, 1,
    (GLOrthogonal (Fin n) ℝ).one_mem, fun _ _ hij ↦ by simpa [Matrix.one_apply_ne hij.ne] using hu,
    fun _ _ ↦ by simpa using ht, Units.ext (by simp)⟩

/-- In rank zero, `siegelDomain 0 u t` is the entire singleton group `GL (Fin 0) ℝ`. -/
@[simp] theorem siegelDomain_fin_zero (u t : ℝ) : siegelDomain 0 u t = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ ⟨1, (upperUnitriangularGroup (Fin 0) ℝ).one_mem, Fin.elim0,
    fun i ↦ i.elim0, 1, (GLOrthogonal (Fin 0) ℝ).one_mem, fun i ↦ i.elim0, fun i ↦ i.elim0,
    Units.ext (Matrix.ext fun i ↦ i.elim0)⟩

/-- In rank one, `siegelDomain 1 u t` is all of `GL (Fin 1) ℝ`, including negative scalars via
`GLOrthogonal (Fin 1) ℝ = {±1}`. -/
@[simp] theorem siegelDomain_fin_one (u t : ℝ) : siegelDomain 1 u t = Set.univ := by
  refine Set.eq_univ_of_forall fun g ↦ ?_
  let x : ℝ := g.val 0 0
  have hx : x ≠ 0 := by
    simpa [Matrix.det_fin_one, x] using ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have habs : 0 < |x| := abs_pos.mpr hx
  let d : GL (Fin 1) ℝ := diagGL (fun _ ↦ Units.mk0 |x| habs.ne')
  refine ⟨1, (upperUnitriangularGroup (Fin 1) ℝ).one_mem, fun _ ↦ |x|, fun _ ↦ habs, d⁻¹ * g, ?_,
    fun _ _ hij ↦ by omega, fun _ hi ↦ by omega, by rw [one_mul, mul_inv_cancel_left]⟩
  rw [GLOrthogonal.mem_iff]; ext i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  have hd_inv : d⁻¹.val 0 0 = |x|⁻¹ := by simp [d]
  simp only [Units.val_mul, Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_unique,
    Fin.default_eq_zero, hd_inv, Matrix.one_apply_eq]
  have hsq : x * x = |x| * |x| := by rw [← sq, ← sq, sq_abs]
  calc |x|⁻¹ * x * (|x|⁻¹ * x) = (|x|⁻¹ * |x|) * (|x|⁻¹ * |x|) := by
        linear_combination |x|⁻¹ ^ 2 * hsq
    _ = 1 := by rw [inv_mul_cancel₀ habs.ne', mul_one]

private theorem isUpperUnitriangular_fin_two (x : ℝ) :
    (!![(1 : ℝ), x; 0, 1]).IsUpperUnitriangular :=
  (Matrix.isUpperUnitriangular_def _).mpr
    ⟨fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij ⊢,
      fun i ↦ by fin_cases i <;> simp⟩

/-- The standard `SL_2(ℝ)` representative `!![√y, x / √y; 0, (√y)⁻¹]` of `x + i y` in the upper
half-plane (`y > 0`). -/
def upperHalfPlaneGL (x y : ℝ) (hy : 0 < y) : GL (Fin 2) ℝ :=
  (isUpperUnitriangular_fin_two x).toGL *
    diagGL ![Units.mk0 (Real.sqrt y) (Real.sqrt_pos.mpr hy).ne',
      Units.mk0 (Real.sqrt y)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hy).ne')]

/-- Matrix entries of `upperHalfPlaneGL x y hy`. -/
@[simp] theorem coe_upperHalfPlaneGL (x y : ℝ) (hy : 0 < y) :
    (upperHalfPlaneGL x y hy : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.sqrt y, x / Real.sqrt y; 0, (Real.sqrt y)⁻¹] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperHalfPlaneGL, diagGL_coe, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]

/-- `upperHalfPlaneGL x y hy` has determinant `1`. -/
theorem det_upperHalfPlaneGL (x y : ℝ) (hy : 0 < y) :
    (upperHalfPlaneGL x y hy : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [coe_upperHalfPlaneGL, Matrix.det_fin_two]; simp [(Real.sqrt_pos.mpr hy).ne']

/-- Uniqueness of the `2 × 2` Iwasawa parameters for `upperHalfPlaneGL x y hy`: any decomposition
`upperHalfPlaneGL x y hy = v * diagGL a * k` with `v` upper unitriangular, `0 < a i`, and
`k ∈ O(2)` satisfies `v 0 1 = x`, `a 0 = √y`, and `a 1 = (√y)⁻¹`. -/
private theorem upperHalfPlaneGL_iwasawa_eq {x y : ℝ} (hy : 0 < y) {v k : GL (Fin 2) ℝ}
    {a : Fin 2 → ℝ} (ha : ∀ i, 0 < a i) (hv : v ∈ upperUnitriangularGroup (Fin 2) ℝ)
    (hk : k ∈ GLOrthogonal (Fin 2) ℝ)
    (hg_eq : upperHalfPlaneGL x y hy = v * diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne') * k) :
    v.val 0 1 = x ∧ a 0 = Real.sqrt y ∧ a 1 = (Real.sqrt y)⁻¹ := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  let U : Matrix (Fin 2) (Fin 2) ℝ := upperHalfPlaneGL x y hy
  have hv_ut : v.val.IsUpperUnitriangular := UpperUnitriangularGroup.mem_iff.mp hv
  let da : GL (Fin 2) ℝ := diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne')
  have hda : da.val * da.valᵀ = Matrix.diagonal (fun i ↦ a i ^ 2) := by
    simp [da, diagGL_coe, Matrix.diagonal_mul_diagonal, sq]
  -- Eliminate `k` via `U * Uᵀ = v * diag(a²) * vᵀ`, then read off `a 1`, `v 0 1`, and `a 0`.
  have hprod : U * Uᵀ = v.val * Matrix.diagonal (fun i ↦ a i ^ 2) * v.valᵀ := by
    calc U * Uᵀ = v.val * da.val * (k.val * k.valᵀ) * da.valᵀ * v.valᵀ := by
          simp only [U, hg_eq, da, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = v.val * Matrix.diagonal (fun i ↦ a i ^ 2) * v.valᵀ := by
          rw [GLOrthogonal.mem_iff'.mp hk, Matrix.mul_one, Matrix.mul_assoc v.val, hda]
  have hv10 : v.val 1 0 = 0 := hv_ut.isUpperTriangular (by decide)
  have h11 := congrFun (congrFun hprod 1) 1
  simp only [U, coe_upperHalfPlaneGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hv10, hv_ut.apply_diag 1,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, ne_eq, one_ne_zero, not_false_eq_true,
    mul_zero, zero_mul, zero_add, one_mul, mul_one] at h11
  have ha1 : a 1 = (Real.sqrt y)⁻¹ :=
    (sq_eq_sq₀ (ha 1).le (inv_pos.mpr hsy).le).mp (by rw [← sq] at h11; exact h11.symm)
  have h01 := congrFun (congrFun hprod 0) 1
  simp only [U, coe_upperHalfPlaneGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hv10, hv_ut.apply_diag 0,
    hv_ut.apply_diag 1, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, ne_eq, one_ne_zero,
    zero_ne_one, not_false_eq_true, mul_zero, zero_add, add_zero, one_mul, mul_one] at h01
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_transpose, det_upperHalfPlaneGL, mul_one, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, hv_ut.det_eq_one, one_mul, mul_one,
    Matrix.det_diagonal, Fin.prod_univ_two] at hdet
  have ha01 : a 0 * a 1 = 1 := (sq_eq_sq₀ (mul_pos (ha 0) (ha 1)).le zero_le_one).mp
    (by rw [mul_pow, one_pow]; exact hdet.symm)
  exact ⟨mul_right_cancel₀ (pow_ne_zero 2 (inv_ne_zero hsy.ne'))
    (by rw [ha1, div_eq_mul_inv] at h01; linarith), eq_of_mul_inv_eq_one (ha1 ▸ ha01), ha1⟩

/-- **Upper half-plane Siegel check for `SL_2(ℝ)`.** For `y > 0`, the matrix
`!![√y, x / √y; 0, (√y)⁻¹]` lies in `siegelDomain 2 u t` precisely when `|x| ≤ u` and `t ≤ y`. -/
theorem upperHalfPlaneGL_mem_siegelDomain_iff (x : ℝ) {y : ℝ} (hy : 0 < y) (u t : ℝ) :
    upperHalfPlaneGL x y hy ∈ siegelDomain 2 u t ↔ |x| ≤ u ∧ t ≤ y := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  constructor
  · rintro ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, hg_eq⟩
    obtain ⟨hv01_eq, ha0, ha1⟩ := upperHalfPlaneGL_iwasawa_eq hy ha hv hk hg_eq
    refine ⟨hv01_eq ▸ hv_bound 0 1 (by decide), ?_⟩
    have hrat := ha_ratio 0 (by decide)
    rwa [show (⟨(0 : Fin 2).val + 1, by decide⟩ : Fin 2) = 1 from rfl,
      ha0, ha1, div_inv_eq_mul, Real.mul_self_sqrt hy.le] at hrat
  · rintro ⟨hx, hty⟩
    let hU := isUpperUnitriangular_fin_two x
    let a : Fin 2 → ℝ := ![Real.sqrt y, (Real.sqrt y)⁻¹]
    refine ⟨hU.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hU, a,
      fun i ↦ by fin_cases i <;> simp [a, hsy], 1, (GLOrthogonal (Fin 2) ℝ).one_mem,
      fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij; simpa [hU.coe_toGL] using hx,
      fun i hi ↦ by
        fin_cases i
        · simp [a, div_inv_eq_mul, Real.mul_self_sqrt hy.le, hty]
        · simp at hi,
      by rw [mul_one, upperHalfPlaneGL]; congr 1; apply congrArg diagGL
         ext i; fin_cases i <;> simp [a]⟩

end SiegelDomain

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
  obtain ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, rfl⟩ := hg
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
    exists_isUpperUnitriangular_transpose_mul_diagonal_mul_eq hb_pos
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
  refine ⟨g₀, ⟨v, hv_mem, a, ha_pos, 1, (GLOrthogonal (Fin n) ℝ).one_mem,
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
    rw [← hγ_col0, hquad 0, hb₃_form]; rfl
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

/-- Single-step Schur complement factorization for a positive-definite `(n + 1) × (n + 1)` matrix
`b₁`: writing `d₀ = b₁ 0 0`, there exist a shear row `u₀ : Fin n → ℝ` and a positive-definite
`n × n` Schur complement `b_sub` with
`b₁ = (upperBorder u₀ 1)ᵀ * cornerBlockSucc d₀ b_sub * upperBorder u₀ 1`. -/
private theorem exists_schur_upperBorder_posDef {n : ℕ}
    {b₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hb₁ : b₁.PosDef) :
    ∃ (u₀ : Fin n → ℝ) (b_sub : Matrix (Fin n) (Fin n) ℝ), b_sub.PosDef ∧
      b₁ = (Matrix.upperBorder u₀ 1)ᵀ * Matrix.cornerBlockSucc (b₁ 0 0) b_sub *
        Matrix.upperBorder u₀ 1 := by
  let d₀ : ℝ := b₁ 0 0; have hd₀_pos : 0 < d₀ := hb₁.diag_pos
  let u₀ : Fin n → ℝ := fun j ↦ b₁ 0 j.succ / d₀
  let b_sub : Matrix _ _ ℝ := Matrix.of fun i j ↦ b₁ i.succ j.succ - d₀ * u₀ i * u₀ j
  have hb₁_schur : b₁ = (Matrix.upperBorder u₀ 1)ᵀ * Matrix.cornerBlockSucc d₀ b_sub *
      Matrix.upperBorder u₀ 1 := by
    rw [Matrix.transpose_upperBorder_mul_cornerBlockSucc_mul]
    exact Matrix.ext_fin_succ rfl (fun j ↦ (mul_div_cancel₀ _ hd₀_pos.ne').symm)
      (fun i ↦ by simpa [u₀, div_mul_cancel₀ _ hd₀_pos.ne'] using hb₁.1.apply 0 i.succ)
      fun i j ↦ by simp [b_sub]
  have hcorner : (Matrix.cornerBlockSucc d₀ b_sub).PosDef :=
    (Matrix.IsUnit.posDef_transpose_mul_mul_iff (Matrix.upperBorderUnit u₀ 1).isUnit).mp
      (by rw [Matrix.coe_upperBorderUnit, Units.val_one, ← hb₁_schur]; exact hb₁)
  exact ⟨u₀, b_sub, (by ext i j; simp : (Matrix.cornerBlockSucc d₀ b_sub).submatrix Fin.succ
    Fin.succ = b_sub) ▸ hcorner.submatrix (Fin.succ_injective n), hb₁_schur⟩

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
the Siegel pivot bound `d i ≤ (4 / 3) * d ⟨i + 1, _⟩`. The unimodular matrix `γ` is constructed
by an HKZ-style successive-minimum induction on `n`. -/
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
      have hb₁ : b₁.PosDef := (Matrix.IsUnit.posDef_transpose_mul_mul_iff γ₁R.isUnit).mpr hb
      obtain ⟨u₀, b_sub, hb_sub, hb₁_schur⟩ := exists_schur_upperBorder_posDef hb₁
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
        fun i hi ↦ Fin.cases (fun h01 ↦ ?_) (fun i' hi' ↦ ?_) i hi, hγ_eq⟩
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
  have hγ_inv : γiR = ηRᵀ.submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [γiR, ηR, γ, ← map_inv, Matrix.GeneralLinearGroup.coe_inverseTranspose, Fin.revPerm_symm]
  have hsub := congrArg (fun M : Matrix _ _ ℝ ↦ M.submatrix Fin.revPerm Fin.revPerm) hη_eq
  have hlhs : (ηRᵀ * ((g.val * g.valᵀ).submatrix Fin.revPerm Fin.revPerm) * ηR).submatrix
      Fin.revPerm Fin.revPerm = h.val * h.valᵀ := by
    rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
      ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
      show ((g.val * g.valᵀ).submatrix Fin.revPerm Fin.revPerm).submatrix
        Fin.revPerm Fin.revPerm = g.val * g.valᵀ from by ext i j; simp,
      ← hγ_inv, ← Matrix.transpose_transpose ηR, ← Matrix.transpose_submatrix, ← hγ_inv]
    simp only [h, γiR, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have hdiag_rev : (Matrix.diagonal d).submatrix Fin.revPerm Fin.revPerm =
      Matrix.diagonal a * (Matrix.diagonal a)ᵀ := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext i j; by_cases hij : i = j <;>
      simp [a, Matrix.diagonal, hij, Real.mul_self_sqrt (hd_pos (Fin.rev j)).le]
  have hrhs : (Nᵀ * Matrix.diagonal d * N).submatrix Fin.revPerm Fin.revPerm =
      p.val * p.valᵀ := by
    rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
      ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, hdiag_rev]
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
    simpa only [Matrix.mul_one] using
      (Matrix.IsUnit.posDef_mul_mul_transpose_iff (B := (1 : Matrix (Fin n) (Fin n) ℝ))
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
  refine ⟨γ, p * (p⁻¹ * h),
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
