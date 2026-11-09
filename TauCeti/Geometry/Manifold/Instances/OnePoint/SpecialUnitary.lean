/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic

/-!
# `PSU(2)` preserves the Fubini–Study form

The Möbius transformation `z ↦ (α z + β) / (γ z + δ)` of a matrix `M = !![α, β; γ, δ]` of
`GL(2, ℂ)` is a smooth self-map of the Riemann sphere `OnePoint ℂ`, regarded as a real surface
through its holomorphic charts (`Matrix.GeneralLinearGroup.contMDiff_smul_real`). This file
determines which of them preserve the Fubini–Study form `ω_FS = ρ(z) dx ∧ dy`,
`ρ(z) = 1 / (π (1 + |z|²)²)` (`OnePoint.fubiniStudyForm`): the transformation of `M` pulls
`ω_FS` back to itself exactly when `Mᴴ M` is a real scalar matrix, that is, when `M` is a nonzero
multiple of a unitary matrix
(`Matrix.GeneralLinearGroup.mpullback_smul_fubiniStudyForm_eq_self_iff`).
In `PSL(2, ℂ)` these are exactly the classes of special unitary matrices: `PSU(2)`, the range of
`Matrix.specialUnitaryGroup.toPSL`, is the stabilizer of `ω_FS`
(`Matrix.ProjectiveSpecialLinearGroup.mem_range_toPSL_iff_mpullback_smul_fubiniStudyForm_eq_self`).
This complements the characterization of `PSU(2)` as the Möbius transformations commuting with
the antipodal map, `Matrix.ProjectiveSpecialLinearGroup.mem_range_toPSL_iff_forall_smul_antipode`.

The computation is made in the preferred charts. Read in the charts at `x` and at `M • x`, the
transformation is again a Möbius transformation, of the matrix `N = τ M σ⁻¹`, where `σ` and `τ`
are the identity or the matrix `!![0, 1; 1, 0]` of `z ↦ 1 / z` according to whether the point is
finite or `∞`. At the coordinate `c` of `x` its derivative is multiplication by
`det N / (γ c + δ) ^ 2`, so it pulls `ω_FS` back to

`ρ ((α c + β) / (γ c + δ)) ‖det N / (γ c + δ) ^ 2‖ ^ 2 dx ∧ dy =`
`‖det N‖ ^ 2 / (π (‖α c + β‖ ^ 2 + ‖γ c + δ‖ ^ 2) ^ 2) dx ∧ dy`,

for the entries `α, β, γ, δ` of `N`. The sum `‖α c + β‖ ^ 2 + ‖γ c + δ‖ ^ 2` is the squared norm of
`N (c, 1)`. If `Nᴴ N = r`, it is `r (1 + ‖c‖ ^ 2)` and `‖det N‖ ^ 2 = r ^ 2`, so the pullback is
`ρ(c) dx ∧ dy`; `σ` and `τ` are unitary, so this holds as soon as `Mᴴ M` is scalar. Conversely, if
the pullback is `ω_FS`, comparing the two forms at every finite point gives
`‖α z + β‖ ^ 2 + ‖γ z + δ‖ ^ 2 = ‖det M‖ (1 + ‖z‖ ^ 2)` for the entries of `M` and every `z ∈ ℂ`,
and the values at `z = 0, 1, -1, i` determine the four entries of `Mᴴ M = ‖det M‖`.

Since a Möbius transformation is holomorphic, preserving `ω_FS` amounts classically to being an
isometry of the Fubini–Study metric `g_FS(v, w) = ω_FS(v, i w)`; that reformulation is not stated
here.

## Main results

* `Matrix.GeneralLinearGroup.mpullback_smul_fubiniStudyForm_eq_self_iff`: the Möbius
  transformation of `M ∈ GL(2, ℂ)` preserves `ω_FS` exactly when `Mᴴ M` is a real scalar matrix.
* `Matrix.ProjectiveSpecialLinearGroup.mem_range_toPSL_iff_mpullback_smul_fubiniStudyForm_eq_self`:
  an element of `PSL(2, ℂ)` lies in `PSU(2)` exactly when it preserves `ω_FS`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapters 2 and 4 (unitary matrices and the rotations of the Riemann sphere).
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric and its invariance under the unitary group).
-/

public section

open scoped Manifold ContDiff MatrixGroups TauCeti.ComplexManifold ComplexConjugate

open Matrix TauCeti

noncomputable section

namespace OnePoint

/-- The matrix `!![0, 1; 1, 0]` of the Möbius transformation `z ↦ 1 / z`. -/
private def swapGL : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp)

private theorem swapGL_apply (i j : Fin 2) : (swapGL : Matrix (Fin 2) (Fin 2) ℂ) i j =
    !![0, 1; 1, 0] i j :=
  rfl

private theorem swapGL_inv : swapGL⁻¹ = swapGL := by
  refine inv_eq_of_mul_eq_one_left (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, swapGL_apply]

/-- The inverted chart is the affine chart after the Möbius transformation `z ↦ 1 / z`. -/
private theorem invChart_eq_affineChart_swapGL_smul (y : OnePoint ℂ) :
    invChart y = affineChart (swapGL • y) := by
  induction y using OnePoint.rec with
  | infty => simp [smul_infty_eq_ite, swapGL_apply]
  | coe z => by_cases hz : z = 0 <;> simp [hz, smul_some_eq_ite, swapGL_apply]

/-- The Möbius transformation which, followed by the affine chart, gives the preferred chart at
`x`: the identity at a finite point and `z ↦ 1 / z` at `∞`. -/
private def chartGL (x : OnePoint ℂ) : GL (Fin 2) ℂ :=
  x.elim swapGL fun _ ↦ 1

private theorem chartAt_apply (x y : OnePoint ℂ) :
    chartAt ℂ x y = affineChart (chartGL x • y) := by
  induction x using OnePoint.rec with
  | infty => simp [chartGL, invChart_eq_affineChart_swapGL_smul]
  | coe z => simp [chartGL]

private theorem chartAt_symm_apply (x : OnePoint ℂ) (w : ℂ) :
    (chartAt ℂ x).symm w = (chartGL x)⁻¹ • (w : OnePoint ℂ) := by
  induction x using OnePoint.rec with
  | infty =>
    -- `swapGL` is the matrix of `invChart_symm_eq_smul`.
    rw [chartAt_infty, invChart_symm_eq_smul, chartGL, elim_infty, swapGL_inv]
    rfl
  | coe z => simp [chartGL]

private theorem chartGL_smul_ne_infty (y : OnePoint ℂ) : chartGL y • y ≠ (∞ : OnePoint ℂ) := by
  induction y using OnePoint.rec with
  | infty => simp [chartGL, smul_infty_eq_ite, swapGL_apply]
  | coe z => simp [chartGL]

end OnePoint

open Matrix.GeneralLinearGroup

namespace OnePoint

/-- The matrix of a Möbius transformation read in the preferred charts at `x` and at its image. -/
private def chartMatrix (M : GL (Fin 2) ℂ) (x : OnePoint ℂ) : GL (Fin 2) ℂ :=
  chartGL (M • x) * M * (chartGL x)⁻¹

private theorem chartAt_smul_chartAt_symm (M : GL (Fin 2) ℂ) (x : OnePoint ℂ) (w : ℂ) :
    chartAt ℂ (M • x) (M • (chartAt ℂ x).symm w) =
      affineChart (chartMatrix M x • (w : OnePoint ℂ)) := by
  rw [chartAt_apply, chartAt_symm_apply, chartMatrix, mul_smul, mul_smul]

private theorem chartMatrix_denom_ne_zero (M : GL (Fin 2) ℂ) (x : OnePoint ℂ) :
    chartMatrix M x 1 0 * chartAt ℂ x x + chartMatrix M x 1 1 ≠ 0 := by
  intro h
  have hx : (chartGL x)⁻¹ • ((chartAt ℂ x x : ℂ) : OnePoint ℂ) = x := by
    rw [← chartAt_symm_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  apply chartGL_smul_ne_infty (M • x)
  have := smul_some_eq_ite (g := chartMatrix M x) (k := chartAt ℂ x x)
  simp only [h, ↓reduceIte] at this
  rwa [chartMatrix, mul_smul, mul_smul, hx] at this

/-- In the preferred charts, a Möbius transformation has derivative `det N / (γ c + δ) ^ 2` at the
coordinate `c` of `x`, where `N = !![α, β; γ, δ]` is its matrix in these charts. -/
private theorem mfderiv_smul_apply (M : GL (Fin 2) ℂ) (x : OnePoint ℂ) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : OnePoint ℂ ↦ M • y) x v =
      (chartMatrix M x : Matrix (Fin 2) (Fin 2) ℂ).det /
        (chartMatrix M x 1 0 * chartAt ℂ x x + chartMatrix M x 1 1) ^ 2 * v := by
  set N := chartMatrix M x
  set c := chartAt ℂ x x
  have hd := (contMDiff_smul_real M (n := 1) x).mdifferentiableAt one_ne_zero
  have hq := chartMatrix_denom_ne_zero M x
  have hquot : HasDerivAt (fun w : ℂ ↦ (N 0 0 * w + N 0 1) / (N 1 0 * w + N 1 1))
      ((N : Matrix (Fin 2) (Fin 2) ℂ).det / (N 1 0 * c + N 1 1) ^ 2) c := by
    have h := (((hasDerivAt_id c).const_mul (N 0 0)).add_const (N 0 1)).div
      (((hasDerivAt_id c).const_mul (N 1 0)).add_const (N 1 1)) hq
    refine h.congr_deriv ?_
    rw [det_fin_two]
    simp
    ring
  have hev : (fun w : ℂ ↦ chartAt ℂ (M • x) (M • (chartAt ℂ x).symm w)) =ᶠ[nhds c]
      fun w : ℂ ↦ (N 0 0 * w + N 0 1) / (N 1 0 * w + N 1 1) := by
    have hcont : Continuous fun w : ℂ ↦ N 1 0 * w + N 1 1 := by fun_prop
    filter_upwards [hcont.continuousAt.eventually_ne hq] with w hw
    rw [chartAt_smul_chartAt_symm, smul_some_eq_ite]
    split_ifs with h
    · exact absurd h hw
    · exact affineChart_coe _
  have key : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : OnePoint ℂ ↦ M • y) x =
      fderiv ℝ (fun w : ℂ ↦ (N 0 0 * w + N 0 1) / (N 1 0 * w + N 1 1)) c := by
    rw [hd.mfderiv_abuse]
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Set.range_id, fderivWithin_univ, Function.comp_def, id_eq]
    exact hev.fderiv_eq
  rw [key, (hquot.hasFDerivAt.restrictScalars ℝ).fderiv]
  -- The real restriction of multiplication by a complex number, applied to `v`.
  exact mul_comm v _

/-! ### The Fubini–Study density under a Möbius transformation -/

/-- If `p / q` is the image of a point under a Möbius transformation of determinant `δ` with
denominator `q`, the density `ρ (p / q)` times the squared modulus `‖δ / q ^ 2‖ ^ 2` of its
derivative is `‖δ‖ ^ 2 / (π (‖p‖ ^ 2 + ‖q‖ ^ 2) ^ 2)`. -/
private theorem fubiniStudyDensity_div_mul_norm_sq (p q δ : ℂ) (hq : q ≠ 0) :
    fubiniStudyDensity (p / q) * ‖δ / q ^ 2‖ ^ 2 =
      ‖δ‖ ^ 2 / (Real.pi * (‖p‖ ^ 2 + ‖q‖ ^ 2) ^ 2) := by
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hs : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by positivity
  simp only [fubiniStudyDensity_def, norm_div, norm_pow]
  field_simp
  ring

/-- **The density is invariant when `Nᴴ N` is scalar.** If `Nᴴ N = r` for an invertible matrix
`N = !![α, β; γ, δ]`, the Möbius transformation of `N` pulls the Fubini–Study density back to
itself at every `c` with `γ c + δ ≠ 0`: `ρ ((α c + β) / (γ c + δ)) ‖det N / (γ c + δ) ^ 2‖ ^ 2`
is `ρ c`. Indeed `‖α c + β‖ ^ 2 + ‖γ c + δ‖ ^ 2 = r (1 + ‖c‖ ^ 2)` and `‖det N‖ ^ 2 = r ^ 2`. -/
private theorem fubiniStudyDensity_div_mul_norm_sq_of_star_mul_self
    {N : Matrix (Fin 2) (Fin 2) ℂ} {r : ℝ} (h : star N * N = scalar (Fin 2) (r : ℂ))
    (hdet : N.det ≠ 0) {c : ℂ} (hq : N 1 0 * c + N 1 1 ≠ 0) :
    fubiniStudyDensity ((N 0 0 * c + N 0 1) / (N 1 0 * c + N 1 1)) *
      ‖N.det / (N 1 0 * c + N 1 1) ^ 2‖ ^ 2 = fubiniStudyDensity c := by
  -- The squared norm of `N (c, 1)` is `r` times that of `(c, 1)`.
  have hnorm : ‖N 0 0 * c + N 0 1‖ ^ 2 + ‖N 1 0 * c + N 1 1‖ ^ 2 = r * (1 + ‖c‖ ^ 2) := by
    have e := fun i j ↦ congrFun (congrFun h i) j
    have e00 := e 0 0
    have e01 := e 0 1
    have e11 := e 1 1
    simp only [Fin.isValue, Matrix.mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_two,
      scalar_apply, diagonal_apply_eq, ne_eq, zero_ne_one, not_false_eq_true, diagonal_apply_ne]
      at e00 e01 e11
    have e10 := congrArg conj e01
    simp only [map_add, map_mul, Complex.conj_conj, map_zero] at e10
    apply Complex.ofReal_injective
    push_cast
    rw [← Complex.mul_conj', ← Complex.mul_conj', ← Complex.mul_conj']
    simp only [map_add, map_mul]
    linear_combination (c * conj c) * e00 + conj c * e01 + c * e10 + e11
  -- Taking determinants in `Nᴴ N = r`, `‖det N‖ ^ 2 = r ^ 2`.
  have hdet' : ‖N.det‖ ^ 2 = r ^ 2 := by
    have hd := congrArg Matrix.det h
    rw [det_mul, star_eq_conjTranspose, det_conjTranspose, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
    apply Complex.ofReal_injective
    push_cast
    rw [← Complex.mul_conj', mul_comm]
    simpa using hd
  have hr : r ≠ 0 := by
    rintro rfl
    exact hdet (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by simpa using hdet')))
  rw [fubiniStudyDensity_div_mul_norm_sq _ _ _ hq, hnorm, hdet', fubiniStudyDensity_def]
  field_simp

/-! ### The pullback of the Fubini–Study form -/

private theorem star_chartGL_mul_self (y : OnePoint ℂ) :
    star (chartGL y : Matrix (Fin 2) (Fin 2) ℂ) * chartGL y = 1 := by
  induction y using OnePoint.rec <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chartGL, swapGL_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem coe_chartGL_inv (y : OnePoint ℂ) :
    ((chartGL y)⁻¹ : GL (Fin 2) ℂ) = star (chartGL y : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [coe_units_inv]
  exact inv_eq_left_inv (star_chartGL_mul_self y)

/-- If `Mᴴ M` is scalar, so is `Nᴴ N` for the matrix `N` of `M` in the preferred charts, since the
chart matrices are unitary. -/
private theorem star_chartMatrix_mul_self {M : GL (Fin 2) ℂ} {r : ℝ}
    (h : star (M : Matrix (Fin 2) (Fin 2) ℂ) * M = scalar (Fin 2) (r : ℂ)) (x : OnePoint ℂ) :
    star (chartMatrix M x : Matrix (Fin 2) (Fin 2) ℂ) * chartMatrix M x =
      scalar (Fin 2) (r : ℂ) := by
  have key (A B X : Matrix (Fin 2) (Fin 2) ℂ) (hA : star A * A = 1) (hB : B * star B = 1)
      (hX : star X * X = scalar (Fin 2) (r : ℂ)) :
      B * (star X * (star A * (A * (X * star B)))) = scalar (Fin 2) (r : ℂ) := by
    rw [← Matrix.mul_assoc (star A) A, hA, Matrix.one_mul, ← Matrix.mul_assoc (star X), hX,
      ← Matrix.mul_assoc, ← (scalar_commute (r : ℂ) (fun _ ↦ Commute.all _ _) B).eq,
      Matrix.mul_assoc, hB, Matrix.mul_one]
  simp only [chartMatrix, Units.val_mul, coe_chartGL_inv, star_mul, star_star, Matrix.mul_assoc]
  exact key _ _ _ (star_chartGL_mul_self _) (mul_eq_one_comm.mp (star_chartGL_mul_self x)) h

/-- The chart matrix of `M` at a finite point is `M`, followed by `z ↦ 1 / z` if the image is `∞`;
so it has the same row norms and the same determinant up to sign. -/
private theorem norm_sq_add_chartMatrix_coe (M : GL (Fin 2) ℂ) (z : ℂ) :
    ‖chartMatrix M z 0 0 * z + chartMatrix M z 0 1‖ ^ 2 +
        ‖chartMatrix M z 1 0 * z + chartMatrix M z 1 1‖ ^ 2 =
      ‖M 0 0 * z + M 0 1‖ ^ 2 + ‖M 1 0 * z + M 1 1‖ ^ 2 ∧
    ‖(chartMatrix M z : Matrix (Fin 2) (Fin 2) ℂ).det‖ = ‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
  simp only [chartMatrix, chartGL, elim_some, inv_one, mul_one]
  induction (M • (z : OnePoint ℂ)) using OnePoint.rec with
  | infty =>
    simp only [elim_infty, Fin.isValue, Units.val_mul, Matrix.mul_apply, swapGL_apply, of_apply,
      cons_val', cons_val_fin_one, cons_val_zero, Fin.sum_univ_two, zero_mul, cons_val_one,
      one_mul, zero_add, add_comm, det_mul, det_fin_two, mul_zero, mul_one, zero_sub, neg_mul,
      neg_sub, true_and]
    -- Exchanging the two rows negates the determinant.
    rw [← norm_neg]
    ring_nf
  | coe w => simp

/-- **The Fubini–Study form under a Möbius transformation.** At a point `x` with coordinate `c`, a
Möbius transformation whose matrix in the preferred charts is `N = !![α, β; γ, δ]` pulls the
Fubini–Study form back to `ρ ((α c + β) / (γ c + δ)) ‖det N / (γ c + δ) ^ 2‖ ^ 2 dx ∧ dy`. -/
private theorem eval₂_fubiniStudyForm_mfderiv_smul (M : GL (Fin 2) ℂ) (x : OnePoint ℂ)
    (v w : ℂ) :
    SmoothBundleForm.eval₂ fubiniStudyForm (M • x)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : OnePoint ℂ ↦ M • y) x v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : OnePoint ℂ ↦ M • y) x w) =
      fubiniStudyDensity ((chartMatrix M x 0 0 * chartAt ℂ x x + chartMatrix M x 0 1) /
          (chartMatrix M x 1 0 * chartAt ℂ x x + chartMatrix M x 1 1)) *
        ‖(chartMatrix M x : Matrix (Fin 2) (Fin 2) ℂ).det /
          (chartMatrix M x 1 0 * chartAt ℂ x x + chartMatrix M x 1 1) ^ 2‖ ^ 2 *
        (conj v * w).im := by
  have hq := chartMatrix_denom_ne_zero M x
  have hchart := chartAt_smul_chartAt_symm M x (chartAt ℂ x x)
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at hchart
  simp only [smul_some_eq_ite, hq, ↓reduceIte, affineChart_coe] at hchart
  refine (eval₂_fubiniStudyForm _ _ _).trans ?_
  rw [mfderiv_smul_apply, mfderiv_smul_apply, hchart, mul_assoc]
  congr 1
  -- Multiplying both vectors by `k` scales their area `Im (conj v * w)` by `‖k‖ ^ 2`.
  generalize (chartMatrix M x : Matrix (Fin 2) (Fin 2) ℂ).det /
    (chartMatrix M x 1 0 * chartAt ℂ x x + chartMatrix M x 1 1) ^ 2 = k
  rw [map_mul, show conj k * conj v * (k * w) = (conj k * k) * (conj v * w) by ring,
    Complex.conj_mul', ← Complex.ofReal_pow, Complex.im_ofReal_mul]

end OnePoint

open OnePoint

namespace Matrix.GeneralLinearGroup

/-- **The Möbius transformations preserving the Fubini–Study form.** The Möbius transformation
`z ↦ (α z + β) / (γ z + δ)` of `M = !![α, β; γ, δ] ∈ GL(2, ℂ)` pulls the Fubini–Study form of the
Riemann sphere back to itself exactly when `Mᴴ M` is a real scalar matrix, that is, when `M` is a
nonzero multiple of a unitary matrix. -/
theorem mpullback_smul_fubiniStudyForm_eq_self_iff (M : GL (Fin 2) ℂ) :
    SmoothForm.mpullback (fun x : OnePoint ℂ ↦ M • x) (contMDiff_smul_real M) fubiniStudyForm =
        fubiniStudyForm ↔
      ∃ r : ℝ, star (M : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ) =
        Matrix.scalar (Fin 2) (r : ℂ) := by
  rw [SmoothBundleForm.ext_eval₂_iff]
  simp only [SmoothForm.eval₂_mpullback]
  constructor
  · intro h
    refine ⟨‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖,
      Matrix.star_mul_self_eq_scalar_of_forall_norm_sq_add _ _ fun z ↦ ?_⟩
    -- Compare the two forms at `z` on the vectors `1` and `i`, on which `dx ∧ dy` is `1`.
    have hz := (eval₂_fubiniStudyForm_mfderiv_smul M z 1 Complex.I).symm.trans
      ((h z (1 : ℂ) Complex.I).trans (eval₂_fubiniStudyForm_coe z 1 Complex.I))
    have hq := chartMatrix_denom_ne_zero M z
    simp only [chartAt_coe, affineChart_coe] at hz hq
    obtain ⟨hS, hdet⟩ := norm_sq_add_chartMatrix_coe M z
    simp only [map_one, one_mul, Complex.I_im, mul_one] at hz
    rw [fubiniStudyDensity_div_mul_norm_sq _ _ _ hq, hS, hdet, fubiniStudyDensity_def] at hz
    have hd : 0 < ‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ := norm_pos_iff.2 M.det_ne_zero
    have hT : 0 < 1 + ‖z‖ ^ 2 := by positivity
    set S := ‖M 0 0 * z + M 0 1‖ ^ 2 + ‖M 1 0 * z + M 1 1‖ ^ 2
    have hS0 : S ≠ 0 := by
      rintro h0
      rw [h0] at hz
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero]
        at hz
      exact (inv_pos.2 (by positivity : 0 < Real.pi * (1 + ‖z‖ ^ 2) ^ 2)).ne hz
    have hsq : S ^ 2 = (‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ * (1 + ‖z‖ ^ 2)) ^ 2 := by
      field_simp at hz
      linear_combination -hz
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  · rintro ⟨r, hr⟩ x v w
    refine (eval₂_fubiniStudyForm_mfderiv_smul M x v w).trans ?_
    rw [fubiniStudyDensity_div_mul_norm_sq_of_star_mul_self
      (star_chartMatrix_mul_self hr x) (chartMatrix M x).det_ne_zero
      (chartMatrix_denom_ne_zero M x)]
    exact (eval₂_fubiniStudyForm x v w).symm

end Matrix.GeneralLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- **`PSU(2)` is the group of Möbius transformations preserving the Fubini–Study form.** An
element of `PSL(2, ℂ)` lies in the range of `SU(2)` exactly when its Möbius transformation of the
Riemann sphere pulls the Fubini–Study form back to itself. So the rotation `z ↦ e^{iθ} z`, the
class of the unitary matrix `diag (e^{iθ/2}, e^{-iθ/2})`, preserves the form, while the dilation
`z ↦ 2 z`, which also fixes `0` and `∞` but is the class of `diag (√2, 1 / √2)`, does not. -/
theorem mem_range_toPSL_iff_mpullback_smul_fubiniStudyForm_eq_self (g : PSL(2, ℂ)) :
    g ∈ (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* _).range ↔
      SmoothForm.mpullback (fun x : OnePoint ℂ ↦ g • x) (contMDiff_smul_real g)
        fubiniStudyForm = fubiniStudyForm := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  rw [specialUnitaryGroup.mk_mem_range_toPSL_iff]
  -- The class of `A` acts as `A` does (`OnePoint.pslMk_smul`).
  refine Iff.trans ?_ (GeneralLinearGroup.mpullback_smul_fubiniStudyForm_eq_self_iff
    (SpecialLinearGroup.toGL A)).symm
  simp only [SpecialLinearGroup.coe_GL_coe_matrix]
  refine ⟨fun h ↦ ⟨1, by simpa using mem_unitaryGroup_iff'.1 h⟩, fun ⟨r, hr⟩ ↦ ?_⟩
  exact mem_unitaryGroup_of_star_mul_self_eq_scalar (by simp [A.2]) hr

end Matrix.ProjectiveSpecialLinearGroup
