/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjJ

/-!
# The Möbius-action conjugation at a positive determinant

Mathlib's `UpperHalfPlane.σ` sends a matrix `g : GL(2, ℝ)` to the automorphism of `ℂ` which is
the identity when `det g` is positive and complex conjugation otherwise. It is the twist that
makes the Möbius action of a negative-determinant matrix antiholomorphic, and it is carried
through the weight-`k` slash action of a general real matrix.

Positive determinant is the case everything in this project works in — congruence subgroups,
the semigroups `Δ₀(N)` of the Hecke theory, and the scaling matrices `diag(d, 1)` all consist
of matrices of positive determinant — so the conjugation is invariably trivial and every
computation begins by discharging it. This file names that branch, so `σ` need never be
unfolded by hand.

## Main results

* `UpperHalfPlane.σ_eq_refl_of_det_pos`: `σ g = ContinuousAlgEquiv.refl ℝ ℂ` for `0 < det g`.
* `UpperHalfPlane.smul_eq_smul_of_coe_eq_smul`: matrices in `GL(2, ℝ)` differing by a nonzero
  scalar act identically on `ℍ`.
* `UpperHalfPlane.ofReal_mul_add_eq_zero_iff`: `m z + n = 0` for real `m`, `n` and `z ∈ ℍ` only
  when `m = n = 0`, the `iff` form of Mathlib's `UpperHalfPlane.linear_ne_zero`.
* `UpperHalfPlane.num_sub_smul_mul_denom`: the difference formula
  `g • z - g • τ = det g · (z - τ) / ((cz + d)(cτ + d))` for `det g > 0`, with the denominator of
  `g • z` cleared.
* `UpperHalfPlane.J_smul_re`, `UpperHalfPlane.J_smul_im`: the involution `J : z ↦ -conj z`
  negates the real part and preserves the imaginary part.
* `Matrix.SpecialLinearGroup.J_mul_mapGL_mul_J`, `Matrix.SpecialLinearGroup.J_mul_mapGL`:
  conjugation by `J` realizes `conjJ` on the image of `SL(2, R)` in `GL(2, ℝ)`.
* `ModularGroup.sl_smul_set`: the `SL(2, ℤ)`-action on subsets of `ℍ` is the `GL(2, ℝ)`-action
  along the coercion, the pointwise-image counterpart of Mathlib's `ModularGroup.sl_moeb`.
* `ModularGroup.smul_eq_smul_of_eq_or_eq_neg`: elements of `SL(2, ℤ)` that agree up to sign act
  alike on `ℍ`.
* `Matrix.SpecialLinearGroup.toGL_smul`, `Matrix.SpecialLinearGroup.mapGL_smul`: the
  `SL(2, ℝ)`-action on `ℍ` is the `GL(2, ℝ)`-action of the underlying matrix, the `SL(2, ℝ)`
  counterpart of Mathlib's `ModularGroup.sl_moeb`.
* `Matrix.SpecialLinearGroup.denom_mapGL_mul`: the automorphy factor is a cocycle for the
  `SL(2, ℝ)`-action.
* `TauCeti.bijOn_sub_div_sub_upperHalfPlaneSet`: an ordered pair of real prevertices gives
  a fractional-linear bijection of the upper half-plane.
* `TauCeti.im_neg_one_div_pos`: the inversion `S : τ ↦ -1/τ` maps a complex number with positive
  imaginary part to one with positive imaginary part.
* `ModularGroup.re_S_smul`, `ModularGroup.S_smul_S_smul`: the inversion `S` negates the real
  part up to a `normSq` factor, and is an involution of `ℍ`.
* `ModularGroup.coe_S_smul`, `ModularGroup.coe_T_smul`: `S` and `T` act on `ℍ ⊆ ℂ` by
  `τ ↦ -1 / τ` and `τ ↦ τ + 1`.
* `ModularGroup.sq_smul_smul_eq_vadd_S_smul_vadd`: for `g = !![a, b; c, d] ∈ SL(2, ℤ)` with
  `c ≠ 0`, `c² (g • τ) = a c - 1 / (τ + d / c)`.

## Provenance

The statement and its role follow AINTLIB's `sigma_eq_id_of_pos_det` in the `LeanModularForms`
project
([`LeanModularForms/HeckeRIngs/GL2/HeckeAction.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck), where it
discharges the `σ` branch for the Hecke slash action. The proof is written against the current
pin — `if_pos` is deprecated here in favour of `ite_eq_left`.
-/

public section

open UpperHalfPlane

open scoped MatrixGroups Pointwise

namespace UpperHalfPlane

/-- The Möbius-action conjugation `σ` is the identity on matrices of positive determinant:
that is the branch its definition picks. On the other branch `σ` is complex conjugation, which
is where the antiholomorphic behaviour of a negative-determinant Möbius transformation comes
from.

The hypothesis is stated with `Matrix.det` of the underlying matrix rather than with the
`ℝˣ`-valued `GeneralLinearGroup.det`: the two agree by
`Matrix.GeneralLinearGroup.val_det_apply`, which is `simp`, so only this form is in simp-normal
form and only this form makes the lemma usable as a conditional `simp` rule. -/
@[simp]
lemma σ_eq_refl_of_det_pos {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) : σ g = ContinuousAlgEquiv.refl ℝ ℂ :=
  ite_eq_left (by rwa [Matrix.GeneralLinearGroup.val_det_apply])

/-- The `SL(2, ℝ)`-action on `ℍ` is the `GL(2, ℝ)`-action of the underlying matrix. -/
@[simp]
theorem _root_.Matrix.SpecialLinearGroup.toGL_smul (g : SL(2, ℝ)) (τ : ℍ) :
    Matrix.SpecialLinearGroup.toGL g • τ = g • τ := by
  -- the action is `MulAction.compHom` along `mapGL ℝ`, and `algebraMap ℝ ℝ` is the identity
  have h : Matrix.SpecialLinearGroup.mapGL ℝ g = Matrix.SpecialLinearGroup.toGL g := by
    ext i j
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  rw [MulAction.compHom_smul_def, h]

/-- The `SL(2, ℝ)`-action on `ℍ` is the `GL(2, ℝ)`-action of its image under
`Matrix.SpecialLinearGroup.mapGL`. -/
theorem _root_.Matrix.SpecialLinearGroup.mapGL_smul (g : SL(2, ℝ)) (τ : ℍ) :
    Matrix.SpecialLinearGroup.mapGL ℝ g • τ = g • τ :=
  (MulAction.compHom_smul_def _ _ _).symm

/-- The automorphy factor is a cocycle for the `SL(2, ℝ)`-action on `ℍ`:
`denom (a * b) τ = denom a (b • τ) * denom b τ`. -/
theorem _root_.Matrix.SpecialLinearGroup.denom_mapGL_mul (a b : SL(2, ℝ)) (τ : ℍ) :
    denom (Matrix.SpecialLinearGroup.mapGL ℝ (a * b)) τ =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ a) ((b • τ : ℍ) : ℂ) *
        denom (Matrix.SpecialLinearGroup.mapGL ℝ b) τ := by
  rw [map_mul, denom_cocycle_σ, σ_eq_refl_of_det_pos (by simp), ContinuousAlgEquiv.refl_apply,
    Matrix.SpecialLinearGroup.mapGL_smul]

/-- The orientation-reversing involution `J : z ↦ -conj z` negates the real part. -/
@[simp]
theorem J_smul_re (τ : ℍ) : (J • τ).re = -τ.re := by
  rw [← coe_re, coe_J_smul, Complex.neg_re, Complex.conj_re, coe_re]

/-- The orientation-reversing involution `J : z ↦ -conj z` preserves the imaginary part. -/
@[simp]
theorem J_smul_im (τ : ℍ) : (J • τ).im = τ.im := by
  rw [← coe_im, coe_J_smul, Complex.neg_im, Complex.conj_im, neg_neg, coe_im]

/-- Conjugation by `J` realizes `conjJ` on the image of `SL(2, R)` in `GL(2, ℝ)`. -/
theorem _root_.Matrix.SpecialLinearGroup.J_mul_mapGL_mul_J {R : Type*} [CommRing R]
    [Algebra R ℝ] (γ : SL(2, R)) :
    J * Matrix.SpecialLinearGroup.mapGL ℝ γ * J =
      Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.conjJ γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct]

/-- `J` intertwines the image of `γ ∈ SL(2, R)` in `GL(2, ℝ)` with that of `conjJ γ`. -/
theorem _root_.Matrix.SpecialLinearGroup.J_mul_mapGL {R : Type*} [CommRing R] [Algebra R ℝ]
    (γ : SL(2, R)) :
    J * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.conjJ γ) * J := by
  rw [← Matrix.SpecialLinearGroup.J_mul_mapGL_mul_J, mul_assoc, ← sq, J_sq, mul_one]

/-- A real linear combination `m z + n` of a point `z` of the upper half-plane and `1` vanishes only
when both coefficients do, as `z` is not real: the `iff` form of `UpperHalfPlane.linear_ne_zero`. -/
theorem ofReal_mul_add_eq_zero_iff (z : ℍ) {m n : ℝ} : (m : ℂ) * z + n = 0 ↔ m = 0 ∧ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  -- the imaginary part `m (im z)` of `m z + n` vanishes only for `m = 0`
  obtain rfl : m = 0 := by simpa [z.im_ne_zero] using congrArg Complex.im h
  simpa using h

/-- For `g = !![a, b; c, d]` of positive determinant,
`(az + b) - (g • τ)(cz + d) = det g · (z - τ) / (cτ + d)`: dividing by `cz + d` gives the
difference formula `g • z - g • τ = det g · (z - τ) / ((cz + d)(cτ + d))`, in the form that
clears the denominator of `g • z`. -/
theorem num_sub_smul_mul_denom {g : GL (Fin 2) ℝ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (τ z : ℍ) :
    num g z - (g • τ : ℍ) * denom g z =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) * ((z : ℂ) - τ) / denom g τ := by
  rw [coe_smul_of_det_pos (by rwa [Matrix.GeneralLinearGroup.val_det_apply]),
    eq_div_iff (denom_ne_zero g τ)]
  field_simp [denom_ne_zero g τ]
  simp only [num, denom, Matrix.det_fin_two, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

/-- Scalar action invariance for `GL (Fin 2) ℝ`: a matrix that is a scalar multiple of another
acts identically on `ℍ`, through Mathlib's scalar-matrix action `glScalar_smul`. The scalar is
necessarily nonzero, since an invertible matrix is not zero. -/
lemma smul_eq_smul_of_coe_eq_smul {g h : GL (Fin 2) ℝ} {c : ℝ}
    (h_eq : ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      c • ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    h • τ = g • τ := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h_eq
    exact h.ne_zero h_eq
  have h_mul : h = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) * g := by
    refine Units.ext ?_
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, h_eq]
    ext i j
    simp [Matrix.scalar, Matrix.diagonal_mul]
  rw [h_mul, mul_smul, glScalar_smul]

end UpperHalfPlane

namespace ModularGroup

/-- **The `SL(2, ℤ)`-action on subsets of `ℍ` is the `GL(2, ℝ)`-action along the coercion**, the
pointwise-image counterpart of `ModularGroup.sl_moeb`. This is useful as a rewrite even though
the two actions are definitionally equal. -/
@[simp]
theorem sl_smul_set (γ : SL(2, ℤ)) (S : Set ℍ) : γ • S = (γ : GL (Fin 2) ℝ) • S := (rfl)

/-- Elements of `SL(2, ℤ)` that agree up to sign act alike on `ℍ`, since `-1` acts trivially
(`ModularGroup.SL_neg_smul`). This absorbs the sign ambiguity `g = k ∨ g = -k` in the cases of
Mathlib's classification `ModularGroup.cases_of_mem_fd_smul_mem_fd`. -/
theorem smul_eq_smul_of_eq_or_eq_neg {g k : SL(2, ℤ)} {z : ℍ} (hg : g = k ∨ g = -k) :
    g • z = k • z :=
  hg.elim (· ▸ rfl) (· ▸ SL_neg_smul _ _)

-- Not `@[simp]`: the simpNF linter rewrites the stated LHS through the unconditional simp lemma
-- `ModularGroup.sl_moeb` to the `GL (Fin 2) ℝ`-lifted action, which is not how call sites state
-- the `S`-action.
/-- The inversion `S` negates the real part of every point and divides by its norm-square. -/
lemma re_S_smul (p : ℍ) : (S • p).re = -p.re / Complex.normSq (p : ℂ) := by
  rw [modular_S_smul]
  simp [Complex.inv_re]
  ring

-- Not `@[simp]`: the simpNF linter rewrites the stated LHS through the unconditional simp
-- lemma `ModularGroup.sl_moeb` to the `GL (Fin 2) ℝ`-lifted double action, the same reason
-- `re_S_smul` above is not tagged.
/-- The inversion `S` is an involution of `ℍ`. -/
lemma S_smul_S_smul (p : ℍ) : S • (S • p) = p := by
  rw [← SL_neg_smul, ← S_inv, inv_smul_smul]

-- Not `@[simp]`, for the same reason as `re_S_smul` above.
/-- The inversion `S` acts on `ℍ ⊆ ℂ` by `τ ↦ -1 / τ`. -/
lemma coe_S_smul (τ : ℍ) : ((S • τ : ℍ) : ℂ) = -1 / τ := by
  rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]

-- Not `@[simp]`, for the same reason as `re_S_smul` above.
/-- The translation `T` acts on `ℍ ⊆ ℂ` by `τ ↦ τ + 1`. -/
lemma coe_T_smul (τ : ℍ) : ((T • τ : ℍ) : ℂ) = τ + 1 := by
  rw [modular_T_smul, coe_vadd, add_comm, Complex.ofReal_one]

/-- For `g = !![a, b; c, d] ∈ SL(2, ℤ)` with `c ≠ 0`, scaling `g • τ` by `c²` gives
`a c - 1 / (τ + d / c)`: in terms of the actions on `ℍ`,
`c² • (g • τ) = a c +ᵥ S • (d / c +ᵥ τ)`. This is an explicit form of Mathlib's
`UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_ne_zero`, adapted to reading `g • τ` near
the cusp `a / c` at the scale `c²`. -/
theorem sq_smul_smul_eq_vadd_S_smul_vadd (g : SL(2, ℤ)) (hc : g 1 0 ≠ 0) (τ : ℍ) :
    (⟨(g 1 0 : ℝ) ^ 2, sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hc)⟩ : {r : ℝ // 0 < r}) •
        (g • τ) =
      ((g 0 0 * g 1 0 : ℤ) : ℝ) +ᵥ S • (((g 1 1 : ℝ) / g 1 0) +ᵥ τ) := by
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hc' : (g 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hden : (g 1 0 : ℂ) * τ + g 1 1 ≠ 0 := by
    simpa [denom_apply] using denom_ne_zero g τ
  have hden' : (τ : ℂ) + (g 1 1 : ℂ) / g 1 0 ≠ 0 := by
    rw [show (τ : ℂ) + (g 1 1 : ℂ) / g 1 0 = (g 1 0 * τ + g 1 1) / g 1 0 by field_simp]
    exact div_ne_zero hden hc'
  have hS : ((S • (((g 1 1 : ℝ) / g 1 0) +ᵥ τ) : ℍ) : ℂ) = -((τ : ℂ) + (g 1 1 : ℂ) / g 1 0)⁻¹ := by
    rw [modular_S_smul, coe_mk, coe_vadd, inv_neg]
    push_cast
    ring
  rw [UpperHalfPlane.ext_iff, coe_pos_real_smul, coe_vadd, coe_specialLinearGroup_apply, hS]
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast, Complex.real_smul,
    Complex.ofReal_pow]
  push_cast
  field_simp
  linear_combination -hdet

open Matrix.SpecialLinearGroup in
/-- The bottom row of `(S * T * S⁻¹) ^ r` in `SL₂(ℤ)` has entries `-r` and `1`, so its automorphy
factor at `z` is `-r z + 1`. -/
theorem denom_mapGL_STS_inv_pow (r : ℕ) (z : ℍ) :
    denom (mapGL ℝ ((S * T * S⁻¹ : SL(2, ℤ)) ^ r)) z = -(r : ℂ) * z + 1 := by
  let g : SL(2, ℤ) := (S * T * S⁻¹ : SL(2, ℤ)) ^ r
  have hg : (S * T * S⁻¹ : SL(2, ℤ)) ^ r = g := rfl
  have hp : g = S * T ^ r * S⁻¹ := by simp [g, conj_pow]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(r : ℤ) := by
    rw [hp, ← zpow_natCast]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S_inv,
      Matrix.SpecialLinearGroup.coe_neg, coe_S, coe_T_zpow]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    rw [hp, ← zpow_natCast]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S_inv,
      Matrix.SpecialLinearGroup.coe_neg, coe_S, coe_T_zpow]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hg, denom, mapGL_coe_matrix, map_apply_coe]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, h10, h11]
  simp [algebraMap_int_eq]

open Matrix.SpecialLinearGroup in
/-- The denominators of `(S T S⁻¹) ^ (n * m)` at a point `z` are pairwise distinct as `m` varies,
for `n > 0`. -/
theorem denom_mapGL_STS_inv_pow_injective {n : ℕ} (hn : 0 < n) (z : ℍ) :
    Function.Injective fun m : ℕ ↦ denom (mapGL ℝ ((S * T * S⁻¹ : SL(2, ℤ)) ^ (n * m))) z :=
  fun m₁ m₂ hm ↦ by
    have him := congrArg Complex.im hm
    simp only [denom_mapGL_STS_inv_pow, Complex.add_im, Complex.one_im, add_zero,
      Complex.neg_im, Complex.mul_im, Complex.natCast_im] at him
    have hmul : ((n * m₁ : ℕ) : ℝ) = ((n * m₂ : ℕ) : ℝ) :=
      mul_right_cancel₀ z.im_ne_zero (by simpa using him)
    exact Nat.eq_of_mul_eq_mul_left hn (Nat.cast_injective hmul)

end ModularGroup

namespace TauCeti

open Complex Function Set

/-- For `p < q`, the real fractional-linear transformation sending `p` to infinity
and `q` to zero preserves the upper half-plane bijectively. -/
theorem bijOn_sub_div_sub_upperHalfPlaneSet {p q : ℝ} (hpq : p < q) :
    BijOn (fun z : ℂ => (z - (q : ℂ)) / (z - (p : ℂ)))
      upperHalfPlaneSet upperHalfPlaneSet := by
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, -q; 1, -p] (by simpa [Matrix.det_fin_two, sub_eq_add_neg, add_comm] using
      (sub_pos.mpr hpq).ne')
  have hg : 0 < g.det.val := by
    simpa [g, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using sub_pos.mpr hpq
  have hsemi : Semiconj ((↑) : ℍ → ℂ) (fun z => g • z)
      (fun z : ℂ => (z - (q : ℂ)) / (z - (p : ℂ))) := by
    intro z
    rw [UpperHalfPlane.coe_smul_of_det_pos hg]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, g,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, sub_eq_add_neg]
  simpa only [UpperHalfPlane.range_coe] using
    hsemi.bijOn_range (MulAction.toPerm g).bijective UpperHalfPlane.coe_injective

/-- `S : τ ↦ -1/τ` preserves the upper half-plane: `0 < (-1/τ).im` whenever `0 < τ.im`. -/
theorem im_neg_one_div_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  simpa [neg_div, inv_neg] using UpperHalfPlane.im_inv_neg_coe_pos ⟨τ, hτ⟩

end TauCeti
