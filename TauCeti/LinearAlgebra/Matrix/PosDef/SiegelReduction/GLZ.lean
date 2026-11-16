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
import TauCeti.LinearAlgebra.Matrix.CornerBlockSucc
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
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
  `TauCeti.RealSiegel.upperHalfPlaneGL`: the Gram map (`gram_eq_iff_exists_mem_GLOrthogonal`), the
  standard Siegel domain `Σ_n(u, t)`, and the `SL_2(ℝ)` upper half-plane check
  (`upperHalfPlaneGL_mem_siegelDomain_iff`).
* `TauCeti.RealSiegel.exists_reducedSet_of_siegelDomain` and
  `TauCeti.RealSiegel.exists_siegelDomain_of_reducedSet`: two-sided cofinality between
  `siegelDomain n u t` (`t > 0`) and `reducedSet n C` (`C > 1`).
* `TauCeti.RealSiegel.exists_cholesky_reduced_GLZ`, `TauCeti.RealSiegel.exists_reduced_GLZ`, and
  `TauCeti.RealSiegel.exists_mul_mem_siegelDomain_GLZ`: Hermite–Korkine–Zolotarev Cholesky
  reduction, `C`-reduced `GL (Fin n) ℤ`-equivalence, and `GL_n(ℝ) = GL_n(ℤ) · Σ_n(1 / 2, √3 / 2)`.

## References

* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, second
  edition, Vol. 1, Cambridge University Press, 2023, §4.2 (Theorems 4.12 and 4.20).
* B. Bakker, B. Klingler, and J. Tsimerman, *Tame topology of arithmetic quotients and
  algebraicity of Hodge loci*, J. Amer. Math. Soc. **33** (2020), §4.5, pp. 17–18.
* M. Orr, *Height bounds and the Siegel property*, Algebra Number Theory **12** (2018), §2.A.
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

/-- Every invertible real matrix has positive-definite Gram matrix `gram g`. -/
theorem gram_posDef {n : ℕ} (g : GL (Fin n) ℝ) : (gram g).PosDef := by
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
      (Matrix.mulVec_injective_of_isUnit g⁻¹.isUnit)

/-- The identity matrix has the identity Gram matrix. -/
@[simp]
theorem gram_one {n : ℕ} : gram (1 : GL (Fin n) ℝ) = 1 := by
  simp [gram]

/-- Right multiplication by an orthogonal matrix leaves `gram` invariant. -/
theorem gram_mul_orthogonal {n : ℕ} (g : GL (Fin n) ℝ) {k : GL (Fin n) ℝ}
    (hk : k ∈ GLOrthogonal (Fin n) ℝ) : gram (g * k) = gram g := by
  let gi : Matrix (Fin n) (Fin n) ℝ := (g⁻¹ : GL (Fin n) ℝ)
  let ki : Matrix (Fin n) (Fin n) ℝ := (k⁻¹ : GL (Fin n) ℝ)
  have hkinv : kiᵀ * ki = 1 := GLOrthogonal.mem_iff.mp ((GLOrthogonal (Fin n) ℝ).inv_mem hk)
  calc gram (g * k) = giᵀ * (kiᵀ * ki) * gi := by
        simp only [gram, gi, ki, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = gram g := by rw [hkinv, Matrix.mul_one]; rfl

/-- Two elements of `GL (Fin n) ℝ` have the same Gram matrix precisely when they differ on the
right by an orthogonal matrix. -/
theorem gram_eq_iff_exists_mem_GLOrthogonal {n : ℕ} {g h : GL (Fin n) ℝ} :
    gram h = gram g ↔ ∃ k ∈ GLOrthogonal (Fin n) ℝ, h = g * k := by
  refine ⟨fun hgram ↦ ⟨g⁻¹ * h, ?_, (mul_inv_cancel_left g h).symm⟩, ?_⟩
  · have hmem : h⁻¹ * g ∈ GLOrthogonal (Fin n) ℝ := by
      rw [GLOrthogonal.mem_iff]
      let G : Matrix (Fin n) (Fin n) ℝ := g
      calc ((h⁻¹ * g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            ((h⁻¹ * g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
          = Gᵀ * gram h * G := by
            simp only [gram, G, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = ((g⁻¹ * g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              ((g⁻¹ * g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
            rw [hgram]; simp only [gram, G, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 1 := by simp
    simpa only [mul_inv_rev, inv_inv] using (GLOrthogonal (Fin n) ℝ).inv_mem hmem
  · rintro ⟨k, hk, rfl⟩
    exact gram_mul_orthogonal g hk

/-- Left multiplication by `γ` transforms `gram g` by congruence with `γ⁻¹`. -/
theorem gram_mul_left {n : ℕ} (γ g : GL (Fin n) ℝ) :
    gram (γ * g) =
      ((γ⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * gram g *
        ((γ⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  simp only [gram, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Congruence of `gram g` by `γ` equals `gram (γ⁻¹ * g)`. -/
theorem transpose_mul_gram_mul {n : ℕ} (γ g : GL (Fin n) ℝ) :
    (γ : Matrix (Fin n) (Fin n) ℝ)ᵀ * gram g * (γ : Matrix (Fin n) (Fin n) ℝ) =
      gram (γ⁻¹ * g) := by
  simpa only [inv_inv] using (gram_mul_left γ⁻¹ g).symm

/-- The determinant of `gram g` is `((det g)⁻¹) ^ 2`. -/
theorem gram_det {n : ℕ} (g : GL (Fin n) ℝ) :
    (gram g).det = ((g : Matrix (Fin n) (Fin n) ℝ).det)⁻¹ ^ 2 := by
  have hdet : ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ).det =
      ((g : Matrix (Fin n) (Fin n) ℝ).det)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one])
  rw [gram, Matrix.det_mul, Matrix.det_transpose, hdet, sq]

/-- Concrete `2 × 2` Gram check: when `g⁻¹ = !![1, 1; 0, 2]`, `gram g = !![1, 1; 1, 5]`. -/
theorem gram_of_coe_inv_eq_two {g : GL (Fin 2) ℝ}
    (hg : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 1; 0, 2]) :
    gram g = !![(1 : ℝ), 1; 1, 5] := by
  rw [gram, hg]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete `2 × 2` diagonal Gram check: `gram (diagGL ![a, a⁻¹]) = diagonal ![a⁻², a²]`. -/
theorem gram_diagGL_two_inv (a : ℝˣ) :
    gram (diagGL ![a, a⁻¹]) = Matrix.diagonal ![(a : ℝ)⁻¹ ^ 2, (a : ℝ) ^ 2] := by
  have hinv : (((diagGL ![a, a⁻¹])⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal ![(a : ℝ)⁻¹, (a : ℝ)] := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [diagGL_coe, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one (n := Fin 2) (α := ℝ) using 2
    ext i; fin_cases i <;> simp [a.ne_zero]
  rw [gram, hinv, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1; ext i; fin_cases i <;> simp [sq]

end Gram

section SiegelDomain

/-- The standard real Siegel domain `Σ_n(u, t)` in `GL (Fin n) ℝ` with respect to the upper
unitriangular subgroup, the positive diagonal torus, and the orthogonal group `O(n)`:
elements `v * diagGL a * k` with `|v i j| ≤ u` (`i < j`) and `t ≤ a i / a ⟨i + 1, _⟩`. -/
def siegelDomain (n : ℕ) (u t : ℝ) : Set (GL (Fin n) ℝ) :=
  {g | ∃ v ∈ upperUnitriangularGroup (Fin n) ℝ, ∃ a : Fin n → ℝ, ∃ ha : ∀ i, 0 < a i,
    ∃ k ∈ GLOrthogonal (Fin n) ℝ,
      (∀ i j : Fin n, i < j → |((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤ u) ∧
      (∀ (i : Fin n) (h : i.1 + 1 < n), t ≤ a i / a ⟨i.1 + 1, h⟩) ∧
      g = v * diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne') * k}

/-- Unfolding characterization of membership in `siegelDomain n u t`. -/
theorem mem_siegelDomain_iff {n : ℕ} {u t : ℝ} {g : GL (Fin n) ℝ} :
    g ∈ siegelDomain n u t ↔
      ∃ v ∈ upperUnitriangularGroup (Fin n) ℝ, ∃ a : Fin n → ℝ, ∃ ha : ∀ i, 0 < a i,
        ∃ k ∈ GLOrthogonal (Fin n) ℝ,
          (∀ i j : Fin n, i < j → |((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤ u) ∧
          (∀ (i : Fin n) (h : i.1 + 1 < n), t ≤ a i / a ⟨i.1 + 1, h⟩) ∧
          g = v * diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne') * k :=
  Iff.rfl

/-- Increasing the off-diagonal bound `u` and decreasing the root-ratio bound `t` enlarges
`siegelDomain n u t`. -/
theorem siegelDomain_mono {n : ℕ} {u u' t t' : ℝ} (hu : u ≤ u') (ht : t' ≤ t) :
    siegelDomain n u t ⊆ siegelDomain n u' t' := by
  rintro g ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, rfl⟩
  exact ⟨v, hv, a, ha, k, hk, fun i j hij ↦ (hv_bound i j hij).trans hu,
    fun i hi ↦ ht.trans (ha_ratio i hi), rfl⟩

/-- Right multiplication by an orthogonal matrix preserves `siegelDomain n u t`. -/
theorem mul_orthogonal_mem_siegelDomain {n : ℕ} {u t : ℝ} {g k' : GL (Fin n) ℝ}
    (hg : g ∈ siegelDomain n u t) (hk' : k' ∈ GLOrthogonal (Fin n) ℝ) :
    g * k' ∈ siegelDomain n u t := by
  obtain ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, rfl⟩ := hg
  exact ⟨v, hv, a, ha, k * k', (GLOrthogonal (Fin n) ℝ).mul_mem hk hk', hv_bound, ha_ratio,
    mul_assoc _ _ _⟩

/-- The identity lies in `siegelDomain n u t` whenever `0 ≤ u` and `t ≤ 1`. -/
theorem one_mem_siegelDomain {n : ℕ} {u t : ℝ} (hu : 0 ≤ u) (ht : t ≤ 1) :
    (1 : GL (Fin n) ℝ) ∈ siegelDomain n u t :=
  ⟨1, (upperUnitriangularGroup (Fin n) ℝ).one_mem, fun _ ↦ 1, fun _ ↦ one_pos, 1,
    (GLOrthogonal (Fin n) ℝ).one_mem, fun _ _ hij ↦ by simpa [Matrix.one_apply_ne hij.ne] using hu,
    fun _ _ ↦ by simpa using ht, Units.ext (by simp)⟩

/-- In rank zero, `siegelDomain 0 u t` is the entire singleton group `GL (Fin 0) ℝ`. -/
@[simp]
theorem siegelDomain_fin_zero (u t : ℝ) : siegelDomain 0 u t = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ ⟨1, (upperUnitriangularGroup (Fin 0) ℝ).one_mem, Fin.elim0,
    fun i ↦ i.elim0, 1, (GLOrthogonal (Fin 0) ℝ).one_mem, fun i ↦ i.elim0, fun i ↦ i.elim0,
    Units.ext (Matrix.ext fun i ↦ i.elim0)⟩

/-- In rank one, `siegelDomain 1 u t` is all of `GL (Fin 1) ℝ`, including negative scalars via
`GLOrthogonal (Fin 1) ℝ = {±1}`. -/
@[simp]
theorem siegelDomain_fin_one (u t : ℝ) : siegelDomain 1 u t = Set.univ := by
  refine Set.eq_univ_of_forall fun g ↦ ?_
  let x : ℝ := (g : Matrix (Fin 1) (Fin 1) ℝ) 0 0
  have hx : x ≠ 0 := by
    simpa [Matrix.det_fin_one, x] using ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have habs : 0 < |x| := abs_pos.mpr hx
  let d : GL (Fin 1) ℝ := diagGL (fun _ ↦ Units.mk0 |x| habs.ne')
  refine ⟨1, (upperUnitriangularGroup (Fin 1) ℝ).one_mem, fun _ ↦ |x|, fun _ ↦ habs, d⁻¹ * g, ?_,
    fun _ _ hij ↦ by omega, fun _ hi ↦ by omega, by rw [one_mul, mul_inv_cancel_left]⟩
  rw [GLOrthogonal.mem_iff]
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  have hd_inv : ((d⁻¹ : GL (Fin 1) ℝ) : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = |x|⁻¹ := by simp [d]
  simp only [Units.val_mul, Matrix.transpose_apply, Matrix.mul_apply, Fintype.sum_unique,
    Fin.default_eq_zero, hd_inv, Matrix.one_apply_eq]
  have hsq : x * x = |x| * |x| := by rw [← sq, ← sq, sq_abs]
  calc |x|⁻¹ * x * (|x|⁻¹ * x)
      = (|x|⁻¹ * |x|) * (|x|⁻¹ * |x|) := by linear_combination |x|⁻¹ ^ 2 * hsq
    _ = 1 := by rw [inv_mul_cancel₀ habs.ne', mul_one]

private theorem isUpperUnitriangular_fin_two (x : ℝ) :
    (!![(1 : ℝ), x; 0, 1]).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  exact ⟨fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij ⊢,
    fun i ↦ by fin_cases i <;> simp⟩

/-- The standard `SL_2(ℝ)` representative `!![√y, x / √y; 0, (√y)⁻¹]` of `x + i y` in the upper
half-plane (`y > 0`). -/
def upperHalfPlaneGL (x y : ℝ) (hy : 0 < y) : GL (Fin 2) ℝ :=
  (isUpperUnitriangular_fin_two x).toGL *
    diagGL ![Units.mk0 (Real.sqrt y) (Real.sqrt_pos.mpr hy).ne',
      Units.mk0 (Real.sqrt y)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hy).ne')]

/-- Matrix entries of `upperHalfPlaneGL x y hy`. -/
@[simp]
theorem coe_upperHalfPlaneGL (x y : ℝ) (hy : 0 < y) :
    (upperHalfPlaneGL x y hy : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.sqrt y, x / Real.sqrt y; 0, (Real.sqrt y)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperHalfPlaneGL, diagGL_coe, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]

/-- `upperHalfPlaneGL x y hy` has determinant `1`. -/
theorem det_upperHalfPlaneGL (x y : ℝ) (hy : 0 < y) :
    (upperHalfPlaneGL x y hy : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [coe_upperHalfPlaneGL, Matrix.det_fin_two]
  simp [(Real.sqrt_pos.mpr hy).ne']

/-- **Upper half-plane Siegel check for `SL_2(ℝ)`.** For `y > 0`, the matrix
`!![√y, x / √y; 0, (√y)⁻¹]` lies in `siegelDomain 2 u t` precisely when `|x| ≤ u` and `t ≤ y`. -/
theorem upperHalfPlaneGL_mem_siegelDomain_iff (x : ℝ) {y : ℝ} (hy : 0 < y) (u t : ℝ) :
    upperHalfPlaneGL x y hy ∈ siegelDomain 2 u t ↔ |x| ≤ u ∧ t ≤ y := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  constructor
  · rintro ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, hg_eq⟩
    let V : Matrix (Fin 2) (Fin 2) ℝ := v
    let K : Matrix (Fin 2) (Fin 2) ℝ := k
    let U : Matrix (Fin 2) (Fin 2) ℝ := upperHalfPlaneGL x y hy
    have hv_ut : V.IsUpperUnitriangular := UpperUnitriangularGroup.mem_iff.mp hv
    have hk_orth : K * Kᵀ = 1 := GLOrthogonal.mem_iff'.mp hk
    let da : GL (Fin 2) ℝ := diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne')
    have hda : (da : Matrix (Fin 2) (Fin 2) ℝ) * (da : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
        Matrix.diagonal (fun i ↦ a i ^ 2) := by
      simp [da, diagGL_coe, Matrix.diagonal_mul_diagonal, sq]
    have hprod : U * Uᵀ = V * Matrix.diagonal (fun i ↦ a i ^ 2) * Vᵀ := by
      calc U * Uᵀ = V * (da : Matrix (Fin 2) (Fin 2) ℝ) * (K * Kᵀ) *
              (da : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * Vᵀ := by
            simp only [U, hg_eq, V, K, da, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = V * Matrix.diagonal (fun i ↦ a i ^ 2) * Vᵀ := by
            rw [hk_orth, Matrix.mul_one, Matrix.mul_assoc V, hda]
    have hv10 : V 1 0 = 0 := hv_ut.isUpperTriangular (by decide)
    have hv00 : V 0 0 = 1 := hv_ut.apply_diag 0
    have hv11 : V 1 1 = 1 := hv_ut.apply_diag 1
    have h11 := congrFun (congrFun hprod 1) 1
    simp only [U, coe_upperHalfPlaneGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hv10, hv11,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, ne_eq, one_ne_zero, not_false_eq_true,
      mul_zero, zero_mul, zero_add, mul_one] at h11
    have ha1 : a 1 = (Real.sqrt y)⁻¹ := by nlinarith [ha 1, inv_pos.mpr hsy]
    have h01 := congrFun (congrFun hprod 0) 1
    simp only [U, coe_upperHalfPlaneGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hv10, hv00, hv11,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, ne_eq, one_ne_zero, zero_ne_one,
      not_false_eq_true, mul_zero, zero_add, add_zero, one_mul, mul_one] at h01
    have hv01_eq : V 0 1 = x := mul_right_cancel₀ (pow_ne_zero 2 (inv_ne_zero hsy.ne'))
      (by rw [ha1, div_eq_mul_inv] at h01; linarith)
    have hdet := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_transpose, det_upperHalfPlaneGL, mul_one, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, hv_ut.det_eq_one, one_mul, mul_one,
      Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    have ha01_one : a 0 * a 1 = 1 := by nlinarith [mul_pos (ha 0) (ha 1), hdet]
    have ha0 : a 0 = Real.sqrt y := eq_of_mul_inv_eq_one (ha1 ▸ ha01_one)
    refine ⟨hv01_eq ▸ hv_bound 0 1 (by decide), ?_⟩
    have hrat := ha_ratio 0 (by decide)
    have hidx : (⟨(0 : Fin 2).1 + 1, by decide⟩ : Fin 2) = 1 := rfl
    rwa [hidx, ha0, ha1, div_inv_eq_mul, Real.mul_self_sqrt hy.le] at hrat
  · rintro ⟨hx, hty⟩
    let hU := isUpperUnitriangular_fin_two x
    let a : Fin 2 → ℝ := ![Real.sqrt y, (Real.sqrt y)⁻¹]
    have ha : ∀ i, 0 < a i := fun i ↦ by fin_cases i <;> simp [a, hsy]
    refine ⟨hU.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hU, a, ha, 1,
      (GLOrthogonal (Fin 2) ℝ).one_mem,
      fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij; simpa [hU.coe_toGL] using hx,
      fun i hi ↦ by
        fin_cases i
        · simp [a, div_inv_eq_mul, Real.mul_self_sqrt hy.le, hty]
        · simp at hi,
      ?_⟩
    rw [mul_one, upperHalfPlaneGL]
    congr 1; apply congrArg diagGL; ext i; fin_cases i <;> simp [a]

end SiegelDomain

section Cofinality

private theorem abs_pow_apply_le {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ i j, |X i j| ≤ B) (m : ℕ) (i j : Fin n) :
    |(X ^ m) i j| ≤ ((n : ℝ) * B) ^ m := by
  induction m generalizing i j with
  | zero => rw [pow_zero, pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k : Fin n, |(X ^ m) i k * X k j|
          ≤ ∑ _k : Fin n, ((n : ℝ) * B) ^ m * B := Finset.sum_le_sum fun k _ ↦ by
            rw [abs_mul]; exact mul_le_mul (ih i k) (hX k j) (abs_nonneg _) (by positivity)
        _ = ((n : ℝ) * B) ^ (m + 1) := by simp [Finset.sum_const, nsmul_eq_mul]; ring

private theorem abs_inv_toGL_apply_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsUpperUnitriangular) {B : ℝ} (hB : 0 ≤ B) (hM_bound : ∀ i j, i < j → |M i j| ≤ B)
    (i j : Fin n) :
    |((hM.toGL⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤
      ∑ m ∈ Finset.range n, ((n : ℝ) * B) ^ m := by
  let X : Matrix (Fin n) (Fin n) ℝ := -(M - 1)
  have hX_diag (k : Fin n) : X k k = 0 := by simp [X, hM.apply_diag k]
  have hX_pow : X ^ n = 0 := by
    simpa only [Fintype.card_fin] using
      Matrix.pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero
        hM.isUpperTriangular_sub_one.neg hX_diag
  let S : Matrix (Fin n) (Fin n) ℝ := ∑ m ∈ Finset.range n, X ^ m
  have hMX : M = 1 - X := by simp [X]
  have hMS : M * S = 1 := by rw [hMX, mul_neg_geom_sum, hX_pow, sub_zero]
  have hinv_eq : ((hM.toGL⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = S :=
    Units.inv_eq_of_mul_eq_one_right (hM.coe_toGL.symm ▸ hMS)
  have hX_bound (a b : Fin n) : |X a b| ≤ B := by
    rcases lt_trichotomy a b with hab | rfl | hba
    · simpa [X, Matrix.one_apply_ne hab.ne] using hM_bound a b hab
    · simpa [hX_diag a] using hB
    · simpa [X, hM.isUpperTriangular hba, Matrix.one_apply_ne hba.ne'] using hB
  rw [hinv_eq]
  simp only [S, Matrix.sum_apply]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun m _ ↦ abs_pow_apply_le hB hX_bound m i j)

private theorem gram_mul_diagGL {n : ℕ} (v : GL (Fin n) ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    gram (v * diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne')) =
      ((v⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        Matrix.diagonal (fun i ↦ (a i)⁻¹ ^ 2) *
        ((v⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  let da : GL (Fin n) ℝ := diagGL (fun i ↦ Units.mk0 (a i) (ha i).ne')
  let N : Matrix (Fin n) (Fin n) ℝ := (v⁻¹ : GL (Fin n) ℝ)
  have hda_mem : da ∈ posDiagonalSubgroup (Fin n) ℝ :=
    diagGL_mem_posDiagonalSubgroup_iff.mpr fun i ↦ by simpa using ha i
  have hda_inv : ((da⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.diagonal (fun i ↦ (a i)⁻¹) := by
    simpa [da, diagGL_coe] using coe_inv_of_mem_posDiagonalSubgroup hda_mem
  calc gram (v * da)
      = Nᵀ * (((da⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          ((da⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) * N := by
        simp only [gram, N, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Nᵀ * Matrix.diagonal (fun i ↦ (a i)⁻¹ ^ 2) * N := by
        rw [hda_inv, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
        congr 2; ext i; simp [sq]

/-- **Siegel domains map into reduced-form sets.** For every `u` and every `t > 0`, there is
`C > 1` depending only on `n`, `u`, and `t` such that `gram g ∈ reducedSet n C` for every
`g ∈ siegelDomain n u t`. -/
theorem exists_reducedSet_of_siegelDomain (n : ℕ) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 1 < C ∧ ∀ g ∈ siegelDomain n u t, gram g ∈ reducedSet n C := by
  let u₀ : ℝ := max u 0
  let u_inv : ℝ := ∑ m ∈ Finset.range n, ((n : ℝ) * u₀) ^ m
  let B : ℝ := max (u_inv + 1) (t⁻¹ ^ 2)
  obtain ⟨C, hC_gt, hC_red⟩ := exists_isReduced_of_cholesky_bound n B
  refine ⟨C, hC_gt, fun g hg ↦ mem_reducedSet_iff.mpr ⟨gram_posDef g, ?_⟩⟩
  obtain ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, rfl⟩ := hg
  rw [gram_mul_orthogonal _ hk, gram_mul_diagGL v a ha]
  have hv_ut : ((v : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ).IsUpperUnitriangular :=
    UpperUnitriangularGroup.mem_iff.mp hv
  have hN_ut : ((v⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ).IsUpperUnitriangular :=
    UpperUnitriangularGroup.mem_iff.mp ((upperUnitriangularGroup (Fin n) ℝ).inv_mem hv)
  let d : Fin n → ℝ := fun i ↦ (a i)⁻¹ ^ 2
  have hd_pos : ∀ i, 0 < d i := fun i ↦ sq_pos_of_pos (inv_pos.mpr (ha i))
  refine (hC_red hN_ut hd_pos (fun i j _ ↦ ?_) (fun i hi ↦ ?_)).2
  · have hv_toGL : hv_ut.toGL = v := Units.ext hv_ut.coe_toGL
    have hN_le : |((v⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j| ≤ u_inv := by
      simpa only [hv_toGL] using abs_inv_toGL_apply_le hv_ut (le_max_right u 0)
        (fun p q hpq ↦ (hv_bound p q hpq).trans (le_max_left u 0)) i j
    exact hN_le.trans ((lt_add_one u_inv).le.trans (le_max_left _ _))
  · have hrat : t * a ⟨i.1 + 1, hi⟩ ≤ a i := (le_div_iff₀ (ha ⟨i.1 + 1, hi⟩)).mp (ha_ratio i hi)
    have hinv_le : (a i)⁻¹ ≤ t⁻¹ * (a ⟨i.1 + 1, hi⟩)⁻¹ := by
      rw [← mul_inv, inv_le_inv₀ (ha i) (mul_pos ht (ha ⟨i.1 + 1, hi⟩))]; exact hrat
    have hsq_le : d i ≤ t⁻¹ ^ 2 * d ⟨i.1 + 1, hi⟩ := by
      have hmul := mul_le_mul hinv_le hinv_le (inv_nonneg.mpr (ha i).le)
        (mul_nonneg (inv_nonneg.mpr ht.le) (inv_nonneg.mpr (ha ⟨i.1 + 1, hi⟩).le))
      simpa only [d, sq, mul_mul_mul_comm] using hmul
    exact hsq_le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hd_pos _).le)

private theorem exists_mem_siegelDomain_gram_eq {n : ℕ} {C B₁ : ℝ} (hB₁ : 0 < B₁)
    (hCh : ∀ {b N : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ},
      b.PosDef → IsReduced C b → N.IsUpperUnitriangular → (∀ i, 0 < d i) →
        b = Nᵀ * Matrix.diagonal d * N →
        (∀ i j, i < j → |N i j| ≤ B₁) ∧ (∀ i j, i < j → d i ≤ B₁ * d j))
    {b : Matrix (Fin n) (Fin n) ℝ} (hb : b ∈ reducedSet n C) :
    ∃ g ∈ siegelDomain n ((∑ m ∈ Finset.range n, ((n : ℝ) * B₁) ^ m) + 1) (Real.sqrt B₁)⁻¹,
      gram g = b ∧ (b.det = 1 → (g : Matrix (Fin n) (Fin n) ℝ).det = 1) := by
  obtain ⟨hb_pos, hb_red⟩ := mem_reducedSet_iff.mp hb
  obtain ⟨N, d, hN_ut, hd_pos, hb_eq⟩ :=
    exists_isUpperUnitriangular_transpose_mul_diagonal_mul_eq hb_pos
  obtain ⟨hN_bound, hd_ratio⟩ := hCh hb_pos hb_red hN_ut hd_pos hb_eq
  let v : GL (Fin n) ℝ := hN_ut.toGL⁻¹
  have hv_mem : v ∈ upperUnitriangularGroup (Fin n) ℝ :=
    (upperUnitriangularGroup (Fin n) ℝ).inv_mem
      (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hN_ut)
  let a : Fin n → ℝ := fun i ↦ (Real.sqrt (d i))⁻¹
  have ha_pos : ∀ i, 0 < a i := fun i ↦ inv_pos.mpr (Real.sqrt_pos.mpr (hd_pos i))
  let g₀ : GL (Fin n) ℝ := v * diagGL (fun i ↦ Units.mk0 (a i) (ha_pos i).ne')
  have hg₀_mem : g₀ ∈
      siegelDomain n ((∑ m ∈ Finset.range n, ((n : ℝ) * B₁) ^ m) + 1) (Real.sqrt B₁)⁻¹ := by
    refine ⟨v, hv_mem, a, ha_pos, 1, (GLOrthogonal (Fin n) ℝ).one_mem,
      fun i j _ ↦ (abs_inv_toGL_apply_le hN_ut hB₁.le hN_bound i j).trans (lt_add_one _).le,
      fun i hi ↦ ?_, (mul_one g₀).symm⟩
    have hsqrt_le : Real.sqrt (d i) ≤ Real.sqrt B₁ * Real.sqrt (d ⟨i.1 + 1, hi⟩) := by
      rw [← Real.sqrt_mul hB₁.le]
      exact Real.sqrt_le_sqrt (hd_ratio i ⟨i.1 + 1, hi⟩ (Fin.lt_def.mpr (Nat.lt_succ_self i.1)))
    rw [le_div_iff₀ (ha_pos ⟨i.1 + 1, hi⟩)]
    simpa only [a, ← mul_inv] using
      (inv_le_inv₀ (mul_pos (Real.sqrt_pos.mpr hB₁) (Real.sqrt_pos.mpr (hd_pos _)))
        (Real.sqrt_pos.mpr (hd_pos i))).mpr hsqrt_le
  have hgram_g₀ : gram g₀ = b := by
    rw [gram_mul_diagGL v a ha_pos, hb_eq]
    have hv_inv : ((v⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = N := by simp [v]
    rw [hv_inv]
    congr 2; ext i j
    by_cases hij : i = j <;> simp [a, Matrix.diagonal, hij, Real.sq_sqrt (hd_pos _).le]
  refine ⟨g₀, hg₀_mem, hgram_g₀, fun hb_det ↦ ?_⟩
  have hg₀_det_pos : 0 < (g₀ : Matrix (Fin n) (Fin n) ℝ).det := by
    rw [Units.val_mul, Matrix.det_mul, (UpperUnitriangularGroup.mem_iff.mp hv_mem).det_eq_one,
      one_mul]
    exact det_pos_of_mem_posDiagonalSubgroup
      (diagGL_mem_posDiagonalSubgroup_iff.mpr fun i ↦ by simpa using ha_pos i)
  have hsq : ((g₀ : Matrix (Fin n) (Fin n) ℝ).det)⁻¹ ^ 2 = 1 := by
    rw [← gram_det g₀, hgram_g₀, hb_det]
  exact inv_eq_one.mp (by nlinarith [inv_pos.mpr hg₀_det_pos])

/-- **Reduced-form sets lift into Siegel domains.** For every `C`, there are `u > 0` and `t > 0`
depending only on `n` and `C` such that every `g : GL (Fin n) ℝ` with `gram g ∈ reducedSet n C`
lies in `siegelDomain n u t`, and every `b ∈ reducedSet n C` has the form `b = gram g` for some
`g ∈ siegelDomain n u t` (with `det g = 1` whenever `det b = 1`). -/
theorem exists_siegelDomain_of_reducedSet (n : ℕ) (C : ℝ) :
    ∃ u > 0, ∃ t > 0,
      (∀ g : GL (Fin n) ℝ, gram g ∈ reducedSet n C → g ∈ siegelDomain n u t) ∧
      (∀ b ∈ reducedSet n C, ∃ g ∈ siegelDomain n u t,
        gram g = b ∧ (b.det = 1 → (g : Matrix (Fin n) (Fin n) ℝ).det = 1)) := by
  obtain ⟨B, _, hCh⟩ := exists_cholesky_bound_of_isReduced n C
  let B₁ : ℝ := max B 1
  have hB₁_pos : 0 < B₁ := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hCh₁ : ∀ {b N : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ},
      b.PosDef → IsReduced C b → N.IsUpperUnitriangular → (∀ i, 0 < d i) →
        b = Nᵀ * Matrix.diagonal d * N →
        (∀ i j, i < j → |N i j| ≤ B₁) ∧ (∀ i j, i < j → d i ≤ B₁ * d j) := by
    intro b N d hb hred hN hd hfac
    obtain ⟨h1, h2⟩ := hCh hb hred hN hd hfac
    exact ⟨fun i j hij ↦ (h1 i j hij).trans (le_max_left B 1),
      fun i j hij ↦ (h2 i j hij).trans (mul_le_mul_of_nonneg_right (le_max_left B 1) (hd j).le)⟩
  have hu_pos : 0 < (∑ m ∈ Finset.range n, ((n : ℝ) * B₁) ^ m) + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ ↦ by positivity) zero_lt_one
  refine ⟨_, hu_pos, (Real.sqrt B₁)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hB₁_pos),
    fun g hg ↦ ?_, fun b hb ↦ exists_mem_siegelDomain_gram_eq hB₁_pos hCh₁ hb⟩
  obtain ⟨g₀, hg₀_mem, hgram_eq, -⟩ := exists_mem_siegelDomain_gram_eq hB₁_pos hCh₁ hg
  obtain ⟨k, hk, rfl⟩ := gram_eq_iff_exists_mem_GLOrthogonal.mp hgram_eq.symm
  exact mul_orthogonal_mem_siegelDomain hg₀_mem hk

end Cofinality

section Reduction

private def upperBorder {R : Type*} [Zero R] [One R] {m : ℕ} (w : Fin m → R)
    (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 w) fun i ↦ Fin.cons 0 (M i))

@[simp]
private theorem upperBorder_zero_zero {R : Type*} [Zero R] [One R] {m : ℕ} (w : Fin m → R)
    (M : Matrix (Fin m) (Fin m) R) : upperBorder w M 0 0 = 1 := rfl

@[simp]
private theorem upperBorder_zero_succ {R : Type*} [Zero R] [One R] {m : ℕ} (w : Fin m → R)
    (M : Matrix (Fin m) (Fin m) R) (j : Fin m) : upperBorder w M 0 j.succ = w j := rfl

@[simp]
private theorem upperBorder_succ_zero {R : Type*} [Zero R] [One R] {m : ℕ} (w : Fin m → R)
    (M : Matrix (Fin m) (Fin m) R) (i : Fin m) : upperBorder w M i.succ 0 = 0 := rfl

@[simp]
private theorem upperBorder_succ_succ {R : Type*} [Zero R] [One R] {m : ℕ} (w : Fin m → R)
    (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) : upperBorder w M i.succ j.succ = M i j := rfl

private theorem upperBorder_zero_one {R : Type*} [Zero R] [One R] {m : ℕ} :
    upperBorder (0 : Fin m → R) (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  refine Matrix.ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

private theorem upperBorder_mul_upperBorder {R : Type*} [Semiring R] {m : ℕ} (w₁ w₂ : Fin m → R)
    (M₁ M₂ : Matrix (Fin m) (Fin m) R) :
    upperBorder w₁ M₁ * upperBorder w₂ M₂ = upperBorder (w₂ + w₁ ᵥ* M₂) (M₁ * M₂) := by
  refine Matrix.ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct]

private theorem upperBorder_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) {m : ℕ}
    (w : Fin m → R) (M : Matrix (Fin m) (Fin m) R) :
    (upperBorder w M).map f = upperBorder (f ∘ w) (M.map f) := by
  refine Matrix.ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;> simp

private theorem upperBorder_mulVec_single_zero {R : Type*} [Semiring R] {m : ℕ} (w : Fin m → R)
    (M : Matrix (Fin m) (Fin m) R) :
    upperBorder w M *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  ext p
  refine Fin.cases ?_ (fun _ ↦ ?_) p <;>
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Fin.succ_ne_zero]

private theorem isUpperUnitriangular_upperBorder {R : Type*} [Zero R] [One R] {m : ℕ}
    (w : Fin m → R) {M : Matrix (Fin m) (Fin m) R} (hM : M.IsUpperUnitriangular) :
    (upperBorder w M).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  refine ⟨fun i j hji ↦ ?_, Fin.cases rfl hM.apply_diag⟩
  refine Fin.cases (fun h : j < 0 ↦ (Fin.not_lt_zero j h).elim) (fun i' hji' ↦ ?_) i hji
  exact Fin.cases (fun _ ↦ rfl)
    (fun j' h ↦ hM.isUpperTriangular (Fin.succ_lt_succ_iff.mp h)) j hji'

private theorem transpose_upperBorder_mul_cornerBlockSucc_mul {m : ℕ} (d₀ : ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (w : Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    (upperBorder w M)ᵀ * Matrix.cornerBlockSucc d₀ B * upperBorder w M =
      Matrix.of (Fin.cons (Fin.cons d₀ (fun j ↦ d₀ * w j))
        fun i ↦ Fin.cons (w i * d₀)
          (fun j ↦ d₀ * w i * w j + (Mᵀ * B * M) i j)) := by
  refine Matrix.ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun i j ↦ ?_)
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · simp only [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, upperBorder_zero_succ,
      upperBorder_succ_succ, Matrix.cornerBlockSucc_zero_zero, Matrix.cornerBlockSucc_zero_succ,
      Matrix.cornerBlockSucc_succ_zero, Matrix.cornerBlockSucc_succ_succ, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, Matrix.of_apply, Fin.cons_succ]
    ring

private theorem cornerBlockSucc_diagonal {m : ℕ} (d₀ : ℝ) (d' : Fin m → ℝ) :
    Matrix.cornerBlockSucc d₀ (Matrix.diagonal d') = Matrix.diagonal (Fin.cons d₀ d') := by
  refine Matrix.ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;>
    simp [Matrix.diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

private def upperBorderShearGL {R : Type*} [Ring R] {m : ℕ} (w : Fin m → R) :
    GL (Fin (m + 1)) R :=
  ⟨upperBorder w 1, upperBorder (-w) 1,
    by simp [upperBorder_mul_upperBorder, upperBorder_zero_one],
    by simp [upperBorder_mul_upperBorder, upperBorder_zero_one]⟩

private def upperBorderBlockGL {R : Type*} [Ring R] {m : ℕ} (g : GL (Fin m) R) :
    GL (Fin (m + 1)) R :=
  ⟨upperBorder 0 g.1, upperBorder 0 (g⁻¹).1,
    by simp [upperBorder_mul_upperBorder, upperBorder_zero_one],
    by simp [upperBorder_mul_upperBorder, upperBorder_zero_one]⟩

private theorem first_pivot_le_four_thirds {n : ℕ} {b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {v₀ : Fin (n + 1) → ℤ}
    (hv₀_min : ∀ x : Fin (n + 1) → ℤ, x ≠ 0 →
      (fun i ↦ (v₀ i : ℝ)) ⬝ᵥ b *ᵥ (fun i ↦ (v₀ i : ℝ)) ≤
        (fun i ↦ (x i : ℝ)) ⬝ᵥ b *ᵥ (fun i ↦ (x i : ℝ)))
    {γ : GL (Fin (n + 1)) ℤ} (hγ_col0 : (γ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ
      Pi.single 0 1 = v₀)
    {d₀ : ℝ} (hd₀_pos : 0 < d₀) {d' : Fin n → ℝ} {w' : Fin n → ℝ}
    (hw'_bound : ∀ j, |w' j| ≤ 1 / 2)
    {N' : Matrix (Fin n) (Fin n) ℝ} (hN'_ut : N'.IsUpperUnitriangular)
    (hγ_eq : ((γ.map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * b *
      ((γ.map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
      (upperBorder w' N')ᵀ * Matrix.diagonal (Fin.cons d₀ d') * upperBorder w' N')
    (i₀ : Fin n) (hi₀ : i₀.1 = 0) :
    d₀ ≤ (4 / 3) * d' i₀ := by
  let b₃ := (upperBorder w' N')ᵀ * Matrix.diagonal (Fin.cons d₀ d') * upperBorder w' N'
  have hquad_single (p : Fin (n + 1)) :
      (fun i ↦ (((γ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ Pi.single p 1) i : ℝ)) ⬝ᵥ
        b *ᵥ (fun i ↦ (((γ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ Pi.single p 1) i : ℝ)) =
        b₃ p p := by
    have hvec : (fun i ↦ (((γ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ Pi.single p 1) i : ℝ)) =
        ((γ.map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ Pi.single p 1 := by
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
    rw [← cornerBlockSucc_diagonal, transpose_upperBorder_mul_cornerBlockSucc_mul]
  have hd₀_eq : (fun i ↦ (v₀ i : ℝ)) ⬝ᵥ b *ᵥ (fun i ↦ (v₀ i : ℝ)) = d₀ := by
    rw [← hγ_col0, hquad_single 0, hb₃_form]; rfl
  let y₁ : Fin (n + 1) → ℤ := (γ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ Pi.single i₀.succ 1
  have hy₁_ne : y₁ ≠ 0 := fun hy0 ↦ by
    have he0 := Matrix.mulVec_injective_of_isUnit γ.isUnit (hy0.trans (Matrix.mulVec_zero _).symm)
    simpa using congrFun he0 i₀.succ
  have hsub00 : (N'ᵀ * Matrix.diagonal d' * N') i₀ i₀ = d' i₀ := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i₀]
    · simp [hN'_ut.apply_diag i₀]
    · intro k _ hk
      have hi₀k : i₀ < k := Fin.lt_def.mpr
        (hi₀ ▸ Nat.pos_of_ne_zero fun hk0 ↦ hk (Fin.ext (hi₀.trans hk0.symm).symm))
      simp [hN'_ut.isUpperTriangular hi₀k]
    · exact fun h ↦ absurd (Finset.mem_univ i₀) h
  have hb₃_11 : b₃ i₀.succ i₀.succ = d₀ * w' i₀ ^ 2 + d' i₀ := by
    rw [hb₃_form]; simp only [Matrix.of_apply, Fin.cons_succ, hsub00]; ring
  have hmin := hv₀_min y₁ hy₁_ne
  rw [hd₀_eq, hquad_single i₀.succ, hb₃_11] at hmin
  have hw := abs_le.mp (hw'_bound i₀)
  have hw_sq : w' i₀ ^ 2 ≤ 1 / 4 := by nlinarith [hw.1, hw.2]
  nlinarith [mul_le_mul_of_nonneg_left hw_sq hd₀_pos.le]

/-- **Hermite–Korkine–Zolotarev Cholesky reduction over `ℤ`.** Every positive-definite real
`n × n` matrix `b` is `GL (Fin n) ℤ`-congruent to `Nᵀ * diagonal d * N` for an upper-unitriangular
matrix `N` with `|N i j| ≤ 1 / 2` above the diagonal and positive diagonal `d` satisfying
`d i ≤ (4 / 3) * d ⟨i + 1, _⟩`. -/
theorem exists_cholesky_reduced_GLZ (n : ℕ) {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.PosDef) :
    ∃ (γ : GL (Fin n) ℤ) (N : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      N.IsUpperUnitriangular ∧
      (∀ i, 0 < d i) ∧
      (∀ i j, i < j → |N i j| ≤ 1 / 2) ∧
      (∀ (i : Fin n) (h : i.1 + 1 < n), d i ≤ (4 / 3) * d ⟨i.1 + 1, h⟩) ∧
      ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b *
        ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
          Nᵀ * Matrix.diagonal d * N := by
  induction n with
  | zero =>
      exact ⟨1, 1, Fin.elim0, Matrix.isUpperUnitriangular_one, fun i ↦ i.elim0,
        fun i ↦ i.elim0, fun i ↦ i.elim0, Matrix.ext fun i ↦ i.elim0⟩
  | succ n ih =>
      obtain ⟨v₀, hv₀_prim, hv₀_min⟩ := hb.exists_isPrimitive_forall_dotProduct_mulVec_le
      let std := Pi.basisFun ℤ (Fin (n + 1))
      obtain ⟨f, hf⟩ := isPrimitive_def.mp hv₀_prim
      obtain ⟨e, -, he0⟩ :=
        (std.exists_basis_eq_iff 0 v₀).mpr ⟨f, fun j hj ↦ (Fin.not_lt_zero j hj).elim, hf⟩
      let γ₁ : GL (Fin (n + 1)) ℤ :=
        ⟨std.toMatrix e, e.toMatrix std, std.toMatrix_mul_toMatrix_flip e,
          e.toMatrix_mul_toMatrix_flip std⟩
      have hγ₁_col0 : (γ₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ Pi.single 0 1 = v₀ := by
        ext i; simpa [γ₁, std, Module.Basis.toMatrix_apply, Matrix.mulVec_single_one,
          Matrix.col_apply] using congrFun he0 i
      let γ₁R : GL (Fin (n + 1)) ℝ := γ₁.map (Int.castRingHom ℝ)
      let b₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
        (γ₁R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * b *
          (γ₁R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      have hb₁ : b₁.PosDef := by
        simpa only [b₁, Matrix.conjTranspose_eq_transpose_of_trivial] using
          hb.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit γ₁R.isUnit)
      let d₀ : ℝ := b₁ 0 0
      have hd₀_pos : 0 < d₀ := hb₁.diag_pos
      let u₀ : Fin n → ℝ := fun j ↦ b₁ 0 j.succ / d₀
      let b_sub : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.of fun i j ↦ b₁ i.succ j.succ - d₀ * u₀ i * u₀ j
      let U₁ : GL (Fin (n + 1)) ℝ := upperBorderShearGL u₀
      have hb₁_schur : b₁ = (U₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ *
          Matrix.cornerBlockSucc d₀ b_sub * (U₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
        dsimp only [U₁, upperBorderShearGL]
        rw [transpose_upperBorder_mul_cornerBlockSucc_mul]
        refine Matrix.ext_fin_succ rfl (fun j ↦ (mul_div_cancel₀ _ hd₀_pos.ne').symm) (fun i ↦ ?_)
          fun i j ↦ ?_
        · simpa [u₀, div_mul_cancel₀ _ hd₀_pos.ne'] using hb₁.1.apply 0 i.succ
        · simp [b_sub]
      have hb_sub : b_sub.PosDef := by
        have hcorner : (Matrix.cornerBlockSucc d₀ b_sub).PosDef := by
          have hconj : Matrix.cornerBlockSucc d₀ b_sub =
              ((U₁⁻¹ : GL (Fin (n + 1)) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * b₁ *
                ((U₁⁻¹ : GL (Fin (n + 1)) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
            rw [hb₁_schur]
            simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv,
              Matrix.transpose_one, Matrix.one_mul]
            simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
          rw [hconj]
          simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
            hb₁.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit U₁⁻¹.isUnit)
        have hsub : (Matrix.cornerBlockSucc d₀ b_sub).submatrix Fin.succ Fin.succ = b_sub := by
          ext i j; simp
        exact hsub ▸ hcorner.submatrix (Fin.succ_injective n)
      obtain ⟨γ', N', d', hN'_ut, hd'_pos, hN'_bound, hd'_ratio, hγ'_eq⟩ := ih hb_sub
      let γ'R : Matrix (Fin n) (Fin n) ℝ := (γ'.map (Int.castRingHom ℝ) : GL (Fin n) ℝ)
      let w : Fin n → ℝ := u₀ ᵥ* γ'R
      let z : Fin n → ℤ := fun j ↦ -⌊w j + 1 / 2⌋
      let w' : Fin n → ℝ := (Int.cast ∘ z) + w
      have hw'_bound (j : Fin n) : |w' j| ≤ 1 / 2 := abs_le.mpr
        ⟨by dsimp [w', z]; push_cast; linarith [Int.floor_le (w j + 1 / 2)],
          by dsimp [w', z]; push_cast; linarith [Int.lt_floor_add_one (w j + 1 / 2)]⟩
      let γ : GL (Fin (n + 1)) ℤ := γ₁ * upperBorderBlockGL γ' * upperBorderShearGL z
      let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := upperBorder w' N'
      let d : Fin (n + 1) → ℝ := Fin.cons d₀ d'
      have hN_bound (i j : Fin (n + 1)) (hij : i < j) : |N i j| ≤ 1 / 2 := by
        refine Fin.cases (fun hij0 ↦ ?_) (fun i' hij' ↦ ?_) i hij
        · exact Fin.cases (fun h ↦ (lt_irrefl 0 h).elim) (fun j' _ ↦ hw'_bound j') j hij0
        · exact Fin.cases (fun h ↦ (Fin.not_lt_zero _ h).elim)
            (fun j' h ↦ hN'_bound i' j' (Fin.succ_lt_succ_iff.mp h)) j hij'
      have hγ_eq : ((γ.map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * b *
          ((γ.map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = Nᵀ * Matrix.diagonal d * N := by
        have hγ₂R : (((upperBorderBlockGL γ').map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = upperBorder 0 γ'R := by
          simpa [upperBorderBlockGL, γ'R, Matrix.GeneralLinearGroup.map] using
            upperBorder_map (Int.castRingHom ℝ) (0 : Fin n → ℤ) γ'.1
        have hγ₃R : (((upperBorderShearGL z).map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = upperBorder (Int.cast ∘ z) 1 := by
          simpa [upperBorderShearGL, Matrix.map_one, Matrix.GeneralLinearGroup.map] using
            upperBorder_map (Int.castRingHom ℝ) z (1 : Matrix (Fin n) (Fin n) ℤ)
        have hUγ₂ : (U₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) * upperBorder 0 γ'R =
            upperBorder w γ'R := by
          simp [U₁, upperBorderShearGL, w, upperBorder_mul_upperBorder]
        have hb₂_eq : (upperBorder 0 γ'R)ᵀ * b₁ * upperBorder 0 γ'R =
            (upperBorder w N')ᵀ * Matrix.diagonal d * upperBorder w N' := by
          calc (upperBorder 0 γ'R)ᵀ * b₁ * upperBorder 0 γ'R
              = (upperBorder w γ'R)ᵀ * Matrix.cornerBlockSucc d₀ b_sub * upperBorder w γ'R := by
                rw [hb₁_schur, ← hUγ₂]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
            _ = (upperBorder w N')ᵀ * Matrix.diagonal d * upperBorder w N' := by
                rw [transpose_upperBorder_mul_cornerBlockSucc_mul, hγ'_eq,
                  ← cornerBlockSucc_diagonal, transpose_upperBorder_mul_cornerBlockSucc_mul]
        have hN_mul : upperBorder w N' * upperBorder (Int.cast ∘ z) 1 = N := by
          simp [N, w', upperBorder_mul_upperBorder]
        calc ((γ.map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * b *
              ((γ.map (Int.castRingHom ℝ) : GL (Fin (n + 1)) ℝ) :
                Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            = (upperBorder (Int.cast ∘ z) 1)ᵀ * ((upperBorder 0 γ'R)ᵀ * b₁ * upperBorder 0 γ'R) *
                upperBorder (Int.cast ∘ z) 1 := by
              simp only [γ, b₁, γ₁R, map_mul, Units.val_mul, hγ₂R, hγ₃R, Matrix.transpose_mul,
                Matrix.mul_assoc]
          _ = Nᵀ * Matrix.diagonal d * N := by
              rw [hb₂_eq, ← hN_mul]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      have hγ_col0 : (γ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ Pi.single 0 1 = v₀ := by
        simp only [γ, upperBorderBlockGL, upperBorderShearGL, Units.val_mul, ← Matrix.mulVec_mulVec,
          upperBorder_mulVec_single_zero, hγ₁_col0]
      refine ⟨γ, N, d, isUpperUnitriangular_upperBorder w' hN'_ut, Fin.cases hd₀_pos hd'_pos,
        hN_bound, fun i hi ↦ Fin.cases (fun h01 ↦ ?_) (fun i' hi' ↦ ?_) i hi, hγ_eq⟩
      · let i₀ : Fin n := ⟨0, by omega⟩
        have hidx : (⟨(0 : Fin (n + 1)).1 + 1, h01⟩ : Fin (n + 1)) = i₀.succ := rfl
        rw [hidx]
        exact first_pivot_le_four_thirds hv₀_min hγ_col0 hd₀_pos hw'_bound hN'_ut hγ_eq i₀ rfl
      · have hi'_lt : i'.1 + 1 < n := by simp only [Fin.val_succ] at hi'; omega
        have hidx : (⟨i'.succ.1 + 1, hi'⟩ : Fin (n + 1)) = (⟨i'.1 + 1, hi'_lt⟩ : Fin n).succ := by
          ext; simp
        rw [hidx]; exact hd'_ratio i' hi'_lt

/-- **Siegel reduction for positive-definite forms over `ℤ`.** There exists `C > 0` depending only
on `n` such that every positive-definite real `n × n` matrix is `GL (Fin n) ℤ`-congruent to a
`C`-reduced matrix. -/
theorem exists_reduced_GLZ {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ b : Matrix (Fin n) (Fin n) ℝ, b.PosDef →
      ∃ γ : GL (Fin n) ℤ, IsReduced C
        (((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b *
          ((γ.map (Int.castRingHom ℝ) : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
  obtain ⟨C, hC_gt, hC_red⟩ := exists_isReduced_of_cholesky_bound n (4 / 3)
  refine ⟨C, zero_lt_one.trans hC_gt, fun b hb ↦ ?_⟩
  obtain ⟨γ, N, d, hN_ut, hd_pos, hN_bound, hd_ratio, hγ_eq⟩ := exists_cholesky_reduced_GLZ n hb
  exact ⟨γ, hγ_eq ▸ (hC_red hN_ut hd_pos
    (fun i j hij ↦ (hN_bound i j hij).trans (by norm_num)) hd_ratio).2⟩

/-- **Classical Siegel reduction for `GL (Fin n) ℝ`:** every element of `GL (Fin n) ℝ` decomposes
as `γ * s` with `γ : GL (Fin n) ℤ` and `s ∈ siegelDomain n (1 / 2) (Real.sqrt 3 / 2)`. -/
theorem exists_mul_mem_siegelDomain_GLZ {n : ℕ} (g : GL (Fin n) ℝ) :
    ∃ γ : GL (Fin n) ℤ, ∃ s ∈ siegelDomain n (1 / 2) (Real.sqrt 3 / 2),
      g = γ.map (Int.castRingHom ℝ) * s := by
  let ggT : Matrix (Fin n) (Fin n) ℝ :=
    (g : Matrix (Fin n) (Fin n) ℝ) * (g : Matrix (Fin n) (Fin n) ℝ)ᵀ
  have hggT : ggT.PosDef := by
    simpa only [ggT, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self (g : Matrix (Fin n) (Fin n) ℝ)
        (Matrix.vecMul_injective_of_isUnit g.isUnit)
  let B : Matrix (Fin n) (Fin n) ℝ := ggT.submatrix Fin.revPerm Fin.revPerm
  obtain ⟨η, N, d, hN_ut, hd_pos, hN_bound, hd_ratio, hη_eq⟩ :=
    exists_cholesky_reduced_GLZ n (hggT.submatrix Fin.revPerm.injective)
  let γ : GL (Fin n) ℤ := Fin.revPerm.reindexGL ℤ (Matrix.GeneralLinearGroup.inverseTranspose η)
  let ηR : Matrix (Fin n) (Fin n) ℝ := (η.map (Int.castRingHom ℝ) : GL (Fin n) ℝ)
  let γiR : Matrix (Fin n) (Fin n) ℝ :=
    ((γ⁻¹ : GL (Fin n) ℤ).map (Int.castRingHom ℝ) : GL (Fin n) ℝ)
  have hγ_inv_coe : γiR = ηRᵀ.submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [γiR, ηR, γ, ← map_inv, Matrix.GeneralLinearGroup.coe_inverseTranspose, Fin.revPerm_symm]
  let V : Matrix (Fin n) (Fin n) ℝ := Nᵀ.submatrix Fin.revPerm Fin.revPerm
  have hV_ut : V.IsUpperUnitriangular := (Matrix.isUpperUnitriangular_def _).mpr
    ⟨fun i j (hji : j < i) ↦ hN_ut.isUpperTriangular (Fin.rev_lt_iff.mpr (by simpa using hji)),
      fun i ↦ hN_ut.apply_diag (Fin.rev i)⟩
  let a : Fin n → ℝ := fun i ↦ Real.sqrt (d (Fin.rev i))
  have ha_pos : ∀ i, 0 < a i := fun i ↦ Real.sqrt_pos.mpr (hd_pos (Fin.rev i))
  let v : GL (Fin n) ℝ := hV_ut.toGL
  let p : GL (Fin n) ℝ := v * diagGL (fun i ↦ Units.mk0 (a i) (ha_pos i).ne')
  let h : GL (Fin n) ℝ := (γ⁻¹).map (Int.castRingHom ℝ) * g
  have hh_prod : (h : Matrix (Fin n) (Fin n) ℝ) * (h : Matrix (Fin n) (Fin n) ℝ)ᵀ =
      (p : Matrix (Fin n) (Fin n) ℝ) * (p : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
    have hsub := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M.submatrix Fin.revPerm Fin.revPerm)
      hη_eq
    have hB_rev : B.submatrix Fin.revPerm Fin.revPerm = ggT := by ext i j; simp [B]
    have hlhs : (ηRᵀ * B * ηR).submatrix Fin.revPerm Fin.revPerm =
        (h : Matrix (Fin n) (Fin n) ℝ) * (h : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
      rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
        ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, hB_rev, ← hγ_inv_coe,
        ← Matrix.transpose_transpose ηR, ← Matrix.transpose_submatrix, ← hγ_inv_coe]
      simp only [h, ggT, γiR, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    have hdiag_rev : (Matrix.diagonal d).submatrix Fin.revPerm Fin.revPerm =
        Matrix.diagonal a * (Matrix.diagonal a)ᵀ := by
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [a, Matrix.diagonal, Real.mul_self_sqrt (hd_pos (Fin.rev i)).le]
      · simp [Matrix.diagonal, hij]
    have hrhs : (Nᵀ * Matrix.diagonal d * N).submatrix Fin.revPerm Fin.revPerm =
        (p : Matrix (Fin n) (Fin n) ℝ) * (p : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
      rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
        ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, hdiag_rev]
      simp only [p, v, V, hV_ut.coe_toGL, diagGL_coe, Units.val_mk0, Units.val_mul,
        Matrix.transpose_mul, Matrix.transpose_submatrix, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    exact hlhs.symm.trans (hsub.trans hrhs)
  let k : GL (Fin n) ℝ := p⁻¹ * h
  have hk_orth : k ∈ GLOrthogonal (Fin n) ℝ := by
    rw [GLOrthogonal.mem_iff']
    calc (k : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ)ᵀ
        = ((p⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
            ((h : Matrix (Fin n) (Fin n) ℝ) * (h : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
            ((p⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
          simp only [k, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((p⁻¹ * p : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
            ((p⁻¹ * p : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
          rw [hh_prod]; simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by simp
  refine ⟨γ, p * k, ⟨v, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hV_ut, a, ha_pos,
    k, hk_orth, fun i j hij ↦ ?_, fun i hi ↦ ?_, rfl⟩, by simp [k, h, map_inv, mul_inv_cancel_left]⟩
  · simpa [v, hV_ut.coe_toGL, V] using
      hN_bound (Fin.rev j) (Fin.rev i) (Fin.rev_lt_iff.mpr (by simpa using hij))
  · let j : Fin n := Fin.rev ⟨i.1 + 1, hi⟩
    have hj : j.1 + 1 < n := by simp only [j, Fin.val_rev]; omega
    have hj_succ : (⟨j.1 + 1, hj⟩ : Fin n) = Fin.rev i := by ext; simp only [j, Fin.val_rev]; omega
    have hd_le' : (3 / 4) * d j ≤ d (Fin.rev i) := by linarith [hj_succ ▸ hd_ratio j hj]
    have hsqrt : Real.sqrt (3 / 4) * Real.sqrt (d j) ≤ Real.sqrt (d (Fin.rev i)) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hd_le'
    have hsqrt_34 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).mpr
        (by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num)
    rw [le_div_iff₀ (ha_pos ⟨i.1 + 1, hi⟩)]
    exact hsqrt_34 ▸ hsqrt

end Reduction

end TauCeti.RealSiegel
