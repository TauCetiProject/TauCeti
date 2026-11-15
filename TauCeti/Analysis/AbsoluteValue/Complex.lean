/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The standard absolute value on `ℂ` and isometric Gelfand–Mazur over `ℝ`

An absolute value on `ℂ` that agrees with `|·|` on `ℝ` is the standard complex norm `‖·‖`
(`AbsoluteValue.eq_norm_of_apply_ofReal`). Together with Mathlib's algebraic Gelfand–Mazur theorem
over `ℝ` (`NormedAlgebra.Real.nonempty_algEquiv_or`), this upgrades every `ℝ`-algebra equivalence
from a normed `ℝ`-algebra field `F` onto `ℝ` or `ℂ` to an isometry, and produces an isometric
embedding `F →ₐ[ℝ] ℂ` (`NormedAlgebra.Real.exists_algHom_complex_isometry`).

## Proof outline

Every absolute value `v` on `ℂ` satisfies `v I = 1`, since `I ^ 2 = -1`. If `v` agrees with `|·|`
on `ℝ`, writing `z = z.re + z.im * I` gives the coarse bound `v z ≤ 2 * ‖z‖`. Applying this to
`z ^ n` yields `(v z) ^ n ≤ 2 * ‖z‖ ^ n` for all `n : ℕ`, which forces `v z ≤ ‖z‖` as `n → ∞`.
On a division ring, one absolute value dominated pointwise by another must equal it
(`AbsoluteValue.eq_of_forall_le`), since inversion reverses the inequality on nonzero elements.

For a normed field `F` that is a normed `ℝ`-algebra, any `e : F ≃ₐ[ℝ] ℝ` satisfies
`x = algebraMap ℝ F (e x)` and is therefore isometric, while any `e : F ≃ₐ[ℝ] ℂ` pulls the norm of
`F` back to an absolute value on `ℂ` restricting to `|·|` on `ℝ`, which must be `‖·‖`.

## Main results

* `AbsoluteValue.eq_of_forall_le`: if `v x ≤ w x` for all `x` in a division ring, then `v = w`.
* `AbsoluteValue.apply_I`: every absolute value on `ℂ` sends `Complex.I` to `1`.
* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value on `ℂ` restricting to `|·|` on `ℝ`
  is `‖·‖`.
* `NormedAlgebra.Real.norm_algEquiv_real` and `NormedAlgebra.Real.norm_algEquiv_complex`: every
  `ℝ`-algebra equivalence from a normed field `F` to `ℝ` or `ℂ` preserves norms.
* `NormedAlgebra.Real.exists_algHom_complex_isometry` and
  `NormedAlgebra.Real.exists_ringHom_complex_isometry`: every normed field over `ℝ` admits an
  isometric embedding into `ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2–1.3.
-/

public section

namespace AbsoluteValue

/-- On a division ring, an absolute value dominated pointwise by another absolute value is equal to
it: evaluating at `x⁻¹` reverses the inequality on nonzero elements. -/
theorem eq_of_forall_le {R S : Type*} [DivisionRing R] [Semiring S] [LinearOrder S]
    [IsStrictOrderedRing S] {v w : AbsoluteValue R S} (h : ∀ x : R, v x ≤ w x) : v = w := by
  ext x
  rcases subsingleton_or_nontrivial S with _ | hS
  · exact Subsingleton.elim _ _
  have : Nontrivial S := hS
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  refine le_antisymm (h x) (le_of_mul_le_mul_right ?_ (v.pos (inv_ne_zero hx)))
  calc
    w x * v x⁻¹ ≤ w x * w x⁻¹ := mul_le_mul_of_nonneg_left (h x⁻¹) (w.nonneg x)
    _ = w 1 := by rw [← w.map_mul, mul_inv_cancel₀ hx]
    _ = 1 := w.map_one_of_isLeftRegular <|
      StrictMono.injective fun _ _ hlt ↦ mul_lt_mul_of_pos_left hlt (w.pos one_ne_zero)
    _ = v 1 := (v.map_one_of_isLeftRegular <|
      StrictMono.injective fun _ _ hlt ↦ mul_lt_mul_of_pos_left hlt (v.pos one_ne_zero)).symm
    _ = v x * v x⁻¹ := by rw [← v.map_mul, mul_inv_cancel₀ hx]

/-- Every absolute value on `ℂ` takes the value `1` at `Complex.I`, since `I ^ 2 = -1`. -/
@[simp]
theorem apply_I {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (v : AbsoluteValue ℂ S) : v Complex.I = 1 := by
  rcases subsingleton_or_nontrivial S with _ | hS
  · exact Subsingleton.elim _ _
  have : Nontrivial S := hS
  have hsq : v Complex.I ^ 2 = 1 := by
    rw [← map_pow, Complex.I_sq, map_neg_eq_map, v.map_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · exfalso
    linarith [v.nonneg Complex.I]

/-- **Uniqueness of the archimedean absolute value on `ℂ` over `ℝ`.** An absolute value on `ℂ`
that agrees with `|·|` on `ℝ` is the standard complex norm `‖·‖`. -/
theorem eq_norm_of_apply_ofReal (v : AbsoluteValue ℂ ℝ) (hv : ∀ r : ℝ, v r = |r|) (z : ℂ) :
    v z = ‖z‖ := by
  have hcoarse (w : ℂ) : v w ≤ 2 * ‖w‖ := by
    calc
      v w = v ((w.re : ℂ) + (w.im : ℂ) * Complex.I) := by rw [Complex.re_add_im]
      _ ≤ v (w.re : ℂ) + v ((w.im : ℂ) * Complex.I) := v.add_le _ _
      _ = |w.re| + |w.im| := by rw [v.map_mul, hv, hv, v.apply_I, mul_one]
      _ ≤ ‖w‖ + ‖w‖ := add_le_add (Complex.abs_re_le_norm w) (Complex.abs_im_le_norm w)
      _ = 2 * ‖w‖ := (two_mul ‖w‖).symm
  have hle (w : ℂ) : v w ≤ ‖w‖ := by
    by_contra! hlt
    have hw : 0 < ‖w‖ := (norm_nonneg w).trans_lt hlt |> fun h ↦
      norm_pos_iff.mpr (v.ne_zero_iff.mp h.ne')
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 ((one_lt_div hw).mpr hlt)
    have hpow : 2 * ‖w‖ ^ n < v (w ^ n) := by
      rwa [div_pow, lt_div_iff₀ (pow_pos hw n), ← map_pow] at hn
    linarith [hcoarse (w ^ n), norm_pow w n]
  exact DFunLike.congr_fun (eq_of_forall_le (w := NormedField.toAbsoluteValue ℂ) hle) z

/-- Bundled form of `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value on `ℂ` agreeing with
`|·|` on `ℝ` equals `NormedField.toAbsoluteValue ℂ`. -/
theorem eq_toAbsoluteValue_of_apply_ofReal (v : AbsoluteValue ℂ ℝ) (hv : ∀ r : ℝ, v r = |r|) :
    v = NormedField.toAbsoluteValue ℂ :=
  ext (eq_norm_of_apply_ofReal v hv)

/-- An absolute value on `ℂ` equals `NormedField.toAbsoluteValue ℂ` if and only if it restricts to
`|·|` on `ℝ`. -/
theorem eq_toAbsoluteValue_complex_iff {v : AbsoluteValue ℂ ℝ} :
    v = NormedField.toAbsoluteValue ℂ ↔ ∀ r : ℝ, v r = |r| :=
  ⟨fun h r ↦ by simp [h], eq_toAbsoluteValue_of_apply_ofReal v⟩

end AbsoluteValue

namespace NormedAlgebra.Real

/-- Every `ℝ`-algebra equivalence from a seminormed `ℝ`-algebra with `‖1‖ = 1` onto `ℝ` preserves
norms. -/
theorem norm_algEquiv_real {F : Type*} [SeminormedRing F] [NormedAlgebra ℝ F] [NormOneClass F]
    (e : F ≃ₐ[ℝ] ℝ) (x : F) : ‖e x‖ = ‖x‖ := by
  have hx : algebraMap ℝ F (e x) = x := e.injective (by simp)
  nth_rw 2 [← hx]
  rw [norm_algebraMap']

/-- `simp`-normal form of `NormedAlgebra.Real.norm_algEquiv_real`, since `‖r‖` simplifies to `|r|`
on `ℝ`. -/
@[simp]
theorem abs_algEquiv_real {F : Type*} [SeminormedRing F] [NormedAlgebra ℝ F] [NormOneClass F]
    (e : F ≃ₐ[ℝ] ℝ) (x : F) : |e x| = ‖x‖ := by
  simpa only [Real.norm_eq_abs] using norm_algEquiv_real e x

/-- Every `ℝ`-algebra equivalence from a seminormed `ℝ`-algebra with `‖1‖ = 1` onto `ℝ` is an
isometry. -/
theorem isometry_algEquiv_real {F : Type*} [SeminormedRing F] [NormedAlgebra ℝ F] [NormOneClass F]
    (e : F ≃ₐ[ℝ] ℝ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e (norm_algEquiv_real e)

/-- Every `ℝ`-algebra equivalence from a normed field over `ℝ` onto `ℂ` preserves norms. -/
@[simp]
theorem norm_algEquiv_complex {F : Type*} [NormedField F] [NormedAlgebra ℝ F]
    (e : F ≃ₐ[ℝ] ℂ) (x : F) : ‖e x‖ = ‖x‖ := by
  let v : AbsoluteValue ℂ ℝ :=
    (NormedField.toAbsoluteValue F).comp (f := e.symm.toRingHom) e.symm.injective
  have hv (r : ℝ) : v r = |r| := by
    -- Unfold `v r` to the norm in `F` of `e.symm` on the real scalar `r`.
    change ‖e.symm (algebraMap ℝ ℂ r)‖ = |r|
    rw [e.symm.commutes, norm_algebraMap', Real.norm_eq_abs]
  simpa [v] using (v.eq_norm_of_apply_ofReal hv (e x)).symm

/-- Every `ℝ`-algebra equivalence from a normed field over `ℝ` onto `ℂ` is an isometry. -/
theorem isometry_algEquiv_complex {F : Type*} [NormedField F] [NormedAlgebra ℝ F]
    (e : F ≃ₐ[ℝ] ℂ) : Isometry e :=
  AddMonoidHomClass.isometry_of_norm e (norm_algEquiv_complex e)

/-- **Isometric Gelfand–Mazur theorem over `ℝ`.** Every normed field that is a normed `ℝ`-algebra
admits an isometric `ℝ`-algebra embedding into `ℂ`. -/
theorem exists_algHom_complex_isometry (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    ∃ φ : F →ₐ[ℝ] ℂ, Isometry φ := by
  rcases nonempty_algEquiv_or F with h | h
  · obtain ⟨e⟩ := h
    exact ⟨(Algebra.ofId ℝ ℂ).comp e.toAlgHom,
      Complex.isometry_ofReal.comp (isometry_algEquiv_real e)⟩
  · obtain ⟨e⟩ := h
    exact ⟨e.toAlgHom, isometry_algEquiv_complex e⟩

/-- If a normed field `F` receives an isometric ring homomorphism `f : ℝ →+* F`, then `f` extends
to an isometric ring homomorphism `φ : F →+* ℂ` over `ℝ`. -/
theorem exists_ringHom_complex_isometry {F : Type*} [NormedField F] (f : ℝ →+* F)
    (hf : Isometry f) : ∃ φ : F →+* ℂ, φ.comp f = Complex.ofRealHom ∧ Isometry φ := by
  let _ : Algebra ℝ F := f.toAlgebra
  have hnorm (r : ℝ) : ‖f r‖ = ‖r‖ := hf.norm_map_of_map_zero (map_zero f) r
  let _ : NormedAlgebra ℝ F :=
    { norm_smul_le := fun r x ↦ by
        -- Scalar multiplication in `f.toAlgebra` is left multiplication by `f r`.
        change ‖f r * x‖ ≤ ‖r‖ * ‖x‖
        rw [norm_mul, hnorm] }
  obtain ⟨φ, hg⟩ := exists_algHom_complex_isometry F
  exact ⟨φ.toRingHom, RingHom.ext φ.commutes, hg⟩

end NormedAlgebra.Real

/-! ### Sharpness checks -/

section Examples

-- `AbsoluteValue.eq_of_forall_le` needs `DivisionRing`: on `ℤ`, the trivial absolute value is
-- bounded pointwise by `|·|` without equaling it.
example : ∃ v w : AbsoluteValue ℤ ℤ, (∀ n : ℤ, v n ≤ w n) ∧ v ≠ w := by
  classical
  refine ⟨AbsoluteValue.trivial, AbsoluteValue.abs, fun n ↦ ?_, fun h ↦ ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simpa [AbsoluteValue.trivial_apply, hn] using Int.one_le_abs hn
  · have := DFunLike.congr_fun h 2
    norm_num [AbsoluteValue.trivial_apply] at this

-- `AbsoluteValue.eq_norm_of_apply_ofReal` needs the restriction hypothesis `∀ r : ℝ, v r = |r|`:
-- `z ↦ ‖z‖ ^ (1 / 2)` is an absolute value on `ℂ` distinct from `‖·‖`.
example : ∃ v : AbsoluteValue ℂ ℝ, v ≠ NormedField.toAbsoluteValue ℂ := by
  refine ⟨{
    toFun := fun z ↦ ‖z‖ ^ (1 / 2 : ℝ)
    map_mul' := fun x y ↦ by rw [norm_mul, Real.mul_rpow (norm_nonneg x) (norm_nonneg y)]
    nonneg' := fun x ↦ by positivity
    eq_zero' := fun x ↦ by simp
    add_le' := fun x y ↦ (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le x y) (by norm_num)).trans
      (Real.rpow_add_le_add_rpow (norm_nonneg x) (norm_nonneg y) (by norm_num) (by norm_num))
  }, fun h ↦ ?_⟩
  have h4 := DFunLike.congr_fun h 4
  simp only [AbsoluteValue.coe_mk, MulHom.coe_mk, NormedField.toAbsoluteValue_apply] at h4
  have h4' : (4 : ℝ) ^ (1 / 2 : ℝ) = 4 := by simpa using h4
  have : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by positivity)]
    norm_num
  linarith

end Examples
