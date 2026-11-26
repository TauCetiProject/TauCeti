/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Positive
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
import Mathlib.Algebra.Order.Star.Real
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Iwasawa

/-!
# The Gram map and standard real Siegel domains in `GL_n(ℝ)`

For `g : GL (Fin n) ℝ`, the left Gram matrix `TauCeti.RealSiegel.gram g = (g⁻¹)ᵀ * g⁻¹` is
positive definite, identifies right `O(n)`-cosets in `GL (Fin n) ℝ`
(`TauCeti.RealSiegel.gram_eq_iff_exists_mem_GLOrthogonal`), and intertwines left multiplication by
`γ` with congruence by `γ⁻¹` (`TauCeti.RealSiegel.gram_mul_left`).

In `U A K` Iwasawa coordinates, the standard real Siegel domain
`TauCeti.RealSiegel.siegelDomain n u t` (`Σ_n(u, t) ⊆ GL (Fin n) ℝ`) consists of products
`v * diagGL a * k` with `v` upper unitriangular satisfying `|v i j| ≤ u` (`i < j`), positive
diagonal `a` with `t ≤ a i / a (i + 1)`, and `k ∈ O(n)`. For `z : UpperHalfPlane`, Iwasawa
uniqueness (`Matrix.GeneralLinearGroup.existsUnique_iwasawa`) identifies membership of
`z.toSL2R.toGL` in `siegelDomain 2 u t` with the classical strip-and-height condition
`|z.re| ≤ u ∧ t ≤ z.im` (`TauCeti.RealSiegel.toSL2R_toGL_mem_siegelDomain_iff`).

## Main definitions and results

* `TauCeti.RealSiegel.gram`: the positive-definite Gram map `g ↦ (g⁻¹)ᵀ * g⁻¹` on `GL (Fin n) ℝ`,
  with `posDef_gram`, `gram_mul_orthogonal`, `gram_eq_iff_exists_mem_GLOrthogonal`,
  `gram_mul_left`, `transpose_mul_gram_mul`, and `det_gram`.
* `TauCeti.RealSiegel.siegelDomain`: the standard real Siegel domain `Σ_n(u, t)` in `GL (Fin n) ℝ`,
  with `siegelDomain_mono`, `mul_orthogonal_mem_siegelDomain`, `one_mem_siegelDomain`,
  `siegelDomain_fin_zero`, and `siegelDomain_fin_one`.
* `TauCeti.RealSiegel.toSL2R_toGL_mem_siegelDomain_iff`: `z.toSL2R.toGL ∈ siegelDomain 2 u t`
  if and only if `|z.re| ≤ u ∧ t ≤ z.im`.

## References

* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, second
  edition, Vol. 1, Cambridge University Press, 2023, §4.2.
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
  simpa only [gram_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_one] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := (1 : Matrix (Fin n) (Fin n) ℝ))
      g⁻¹.isUnit).mpr Matrix.PosDef.one

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
  simpa only [inv_inv] using
    GLOrthogonal.mul_inv_mem_of_transpose_mul_eq (p := h⁻¹) (h := g⁻¹) hgram.symm

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

/-- **Upper half-plane Siegel check for `SL(2, ℝ)`.** For `z : UpperHalfPlane`, the standard
section `z.toSL2R.toGL` lies in `siegelDomain 2 u t` precisely when `|z.re| ≤ u` and
`t ≤ z.im`. -/
@[simp]
theorem toSL2R_toGL_mem_siegelDomain_iff {z : UpperHalfPlane} {u t : ℝ} :
    z.toSL2R.toGL ∈ siegelDomain 2 u t ↔ |z.re| ≤ u ∧ t ≤ z.im := by
  have hsy : 0 < Real.sqrt z.im := Real.sqrt_pos.mpr z.im_pos
  let hU := isUpperUnitriangular_fin_two z.re
  let a₀ : Fin 2 → ℝ := ![Real.sqrt z.im, (Real.sqrt z.im)⁻¹]
  have ha₀ (i : Fin 2) : 0 < a₀ i := by fin_cases i <;> simp [a₀, hsy]
  let d₀ : GL (Fin 2) ℝ := diagGL fun i ↦ Units.mk0 (a₀ i) (ha₀ i).ne'
  have hz_eq : z.toSL2R.toGL = hU.toGL * d₀ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [d₀, a₀, UpperHalfPlane.coe_toSL2R, diagGL_coe, Matrix.mul_apply, Fin.sum_univ_two,
        div_eq_mul_inv]
  constructor
  · rintro ⟨v, hv, a, ha, k, hk, hv_bound, ha_ratio, hg_eq⟩
    let da : GL (Fin 2) ℝ := diagGL fun i ↦ Units.mk0 (a i) (ha i).ne'
    have hmap (x : GL (Fin 2) ℝ) : Matrix.GeneralLinearGroup.map (algebraMap ℝ ℝ) x = x :=
      Units.ext (by simp)
    have hk_mem : k⁻¹ ∈ unitarySubgroup (GL (Fin 2) ℝ) :=
      GLOrthogonal.eq_unitarySubgroup (n := Fin 2) (R := ℝ) ▸ (GLOrthogonal (Fin 2) ℝ).inv_mem hk
    have hda_mem : da⁻¹ ∈ posDiagonalSubgroup (Fin 2) ℝ :=
      (posDiagonalSubgroup (Fin 2) ℝ).inv_mem
        (diagGL_mem_posDiagonalSubgroup_iff.mpr fun i ↦ by simpa using ha i)
    have hd₀_mem : d₀⁻¹ ∈ posDiagonalSubgroup (Fin 2) ℝ :=
      (posDiagonalSubgroup (Fin 2) ℝ).inv_mem
        (diagGL_mem_posDiagonalSubgroup_iff.mpr fun i ↦ by simpa using ha₀ i)
    have hv_mem : v⁻¹ ∈ upperUnitriangularGroup (Fin 2) ℝ :=
      (upperUnitriangularGroup (Fin 2) ℝ).inv_mem hv
    have hv₀_mem : hU.toGL⁻¹ ∈ upperUnitriangularGroup (Fin 2) ℝ :=
      (upperUnitriangularGroup (Fin 2) ℝ).inv_mem
        (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hU)
    have huniq := (Matrix.GeneralLinearGroup.existsUnique_iwasawa (z.toSL2R.toGL)⁻¹).unique
      (y₁ := (⟨k⁻¹, hk_mem⟩, ⟨da⁻¹, hda_mem⟩, ⟨v⁻¹, hv_mem⟩))
      (y₂ := (1, ⟨d₀⁻¹, hd₀_mem⟩, ⟨hU.toGL⁻¹, hv₀_mem⟩))
      (by simp only [hmap, hg_eq, da, mul_inv_rev, mul_assoc])
      (by simp only [OneMemClass.coe_one, one_mul, hmap, hz_eq, mul_inv_rev])
    have hda_eq : da = d₀ := inv_inj.mp (congrArg (fun x ↦ (x.2.1 : GL (Fin 2) ℝ)) huniq)
    have hv_eq : v = hU.toGL := inv_inj.mp (congrArg (fun x ↦ (x.2.2 : GL (Fin 2) ℝ)) huniq)
    have hv01 : v.val 0 1 = z.re := by
      simpa using congrArg (fun g : GL (Fin 2) ℝ ↦ g.val 0 1) hv_eq
    have ha0 : a 0 = Real.sqrt z.im := by
      simpa [da, d₀, a₀, diagGL_coe] using congrArg (fun g : GL (Fin 2) ℝ ↦ g.val 0 0) hda_eq
    have ha1 : a 1 = (Real.sqrt z.im)⁻¹ := by
      simpa [da, d₀, a₀, diagGL_coe] using congrArg (fun g : GL (Fin 2) ℝ ↦ g.val 1 1) hda_eq
    refine ⟨hv01 ▸ hv_bound 0 1 (by decide), ?_⟩
    have hrat := ha_ratio 0 (by decide)
    rwa [show (⟨(0 : Fin 2).val + 1, by decide⟩ : Fin 2) = 1 by ext; simp,
      ha0, ha1, div_inv_eq_mul, Real.mul_self_sqrt z.im_pos.le] at hrat
  · rintro ⟨hx, hty⟩
    refine ⟨hU.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hU, a₀, ha₀,
      1, (GLOrthogonal (Fin 2) ℝ).one_mem,
      fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij; simpa using hx,
      fun i hi ↦ ?_, by rw [mul_one, ← hz_eq]⟩
    fin_cases i
    · simp [a₀, div_inv_eq_mul, Real.mul_self_sqrt z.im_pos.le, hty]
    · simp at hi

end SiegelDomain

end TauCeti.RealSiegel
