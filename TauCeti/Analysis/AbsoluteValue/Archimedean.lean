/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs

import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Instances.Rat
import TauCeti.Analysis.AbsoluteValue.FiniteOrder

/-!
# Archimedean absolute values come from complex embeddings

An absolute value `w` on a field `F` that agrees with the usual absolute value on the natural
numbers is the pullback of the norm of `ℂ` along a ring homomorphism `F →+* ℂ`. This is the
archimedean half of Ostrowski's theorem for an arbitrary field, in the normalisation where `w`
restricts to `|·|` on `ℚ` on the nose, and it is what identifies the absolute values of a field
extension lying over an infinite place of a number field with infinite places of the extension.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value on `ℂ` restricting to `|·|` on `ℝ`
  is the norm of `ℂ`. Gelfand–Mazur produces only an `ℝ`-algebra isomorphism with `ℂ`, so this
  is what makes it an isometry.
* `AbsoluteValue.apply_ratCast_eq_abs`: an absolute value on a field which is `n` at every natural
  number `n` is `|·|` on `ℚ`.
* `AbsoluteValue.exists_ringHom_complex_apply_eq_norm`: an absolute value on a field which is
  `n` at every natural number `n` is `x ↦ ‖φ x‖` for some `φ : F →+* ℂ`.

## Implementation notes

For `eq_norm_of_apply_ofReal`, `N i = 1` because `i` has finite order, so `N z ≤ 2 ‖z‖` by the
triangle inequality on `z = re z + im z * i`. Applied to the powers of `z` this gives
`N z ≤ ‖z‖`, and then `N z * N (conj z) = ‖z‖ ^ 2` forces equality.

For `exists_ringHom_complex_apply_eq_norm`, let `E` be the completion of `F` at `w`. The
hypothesis makes `ℚ → E` an isometry for `|·|`, so it extends to an isometric ring homomorphism
`ℝ →+* E` (`IsDenseInducing.extendRingHom`), and `E` is a normed `ℝ`-algebra. By the real
Gelfand–Mazur theorem, `NormedAlgebra.Real.nonempty_algEquiv_or`, which needs neither
completeness nor finite dimension, `E` is `ℝ` or `ℂ` as an `ℝ`-algebra; in either case the norm
of `E` transported to `ℂ` restricts to `|·|` on `ℝ`, hence is the norm of `ℂ`.

## References

* A. Ostrowski, *Über einige Lösungen der Funktionalgleichung φ(x)⋅φ(y) = φ(xy)*, Acta Math. 41
  (1916), 271–284.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2 and §1.3.
-/

public section

open ComplexConjugate

namespace AbsoluteValue

/-- An absolute value on `ℂ` that restricts to the usual absolute value on `ℝ` is the norm of
`ℂ`. -/
theorem eq_norm_of_apply_ofReal (N : AbsoluteValue ℂ ℝ) (h : ∀ r : ℝ, N r = |r|) (z : ℂ) :
    N z = ‖z‖ := by
  have hI : N Complex.I = 1 :=
    N.map_eq_one_of_isOfFinOrder (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, by simp⟩)
  -- `N` is bounded by twice the norm.
  have hle₂ (z : ℂ) : N z ≤ 2 * ‖z‖ := by
    calc N z = N (z.re + z.im * Complex.I) := by rw [Complex.re_add_im]
      _ ≤ |z.re| + |z.im| := by
        simpa [h, hI] using N.add_le (z.re : ℂ) (z.im * Complex.I)
      _ ≤ 2 * ‖z‖ := by linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]
  -- Applying this to the powers of `z` removes the factor `2`.
  have hle (z : ℂ) : N z ≤ ‖z‖ := by
    by_contra! hz
    have hz₀ : 0 < ‖z‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hz
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 ((one_lt_div hz₀).mpr hz)
    have := hle₂ (z ^ n)
    rw [map_pow, norm_pow] at this
    rw [div_pow, lt_div_iff₀ (by positivity)] at hn
    linarith
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  -- The product of the values at `z` and at `conj z` is `‖z‖ ^ 2`.
  have hmul : N z * N (conj z) = ‖z‖ ^ 2 := by
    rw [← map_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq, h,
      abs_of_nonneg (by positivity)]
  have h₁ := hle (conj z)
  rw [Complex.norm_conj] at h₁
  nlinarith [N.nonneg z, N.nonneg (conj z), hle z, norm_pos_iff.mpr hz]

variable {F : Type*} [Field F] {w : AbsoluteValue F ℝ}

/-- An absolute value on a field which is `n` at every natural number `n` is the usual absolute
value on the rational numbers. -/
theorem apply_ratCast_eq_abs (hw : ∀ n : ℕ, w n = n) (q : ℚ) :
    w q = |(q : ℝ)| := by
  have hint (m : ℤ) : w m = |(m : ℝ)| := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m <;> simp [hw]
  rw [Rat.cast_def, map_div₀, hint, hw, Rat.cast_def, abs_div, Nat.abs_cast]

open UniformSpace.Completion in
/-- An absolute value on a field which is `n` at every natural number `n` is the pullback of the
norm of `ℂ` along a ring homomorphism. -/
theorem exists_ringHom_complex_apply_eq_norm (hw : ∀ n : ℕ, w n = n) :
    ∃ φ : F →+* ℂ, ∀ x, w x = ‖φ x‖ := by
  let E := w.Completion
  -- The completion of `F` at `w` receives `ℚ` isometrically, hence `ℝ`.
  let ι : F →+* E := (coeRingHom : WithAbs w →+* E).comp (WithAbs.equiv w).symm.toRingHom
  -- `coeRingHom` is the coercion into the completion, which has no `simp` lemma of its own.
  have hι (x : F) : ‖ι x‖ = w x :=
    (norm_coe (WithAbs.toAbs w x)).trans (WithAbs.norm_toAbs_eq w x)
  have hq (q : ℚ) : ‖(q : E)‖ = |(q : ℝ)| := by
    rw [← map_ratCast ι, hι, apply_ratCast_eq_abs hw]
  have : CharZero E := ⟨fun m n hmn ↦ by
    have := congrArg norm hmn
    rwa [← map_natCast ι, ← map_natCast ι, hι, hι, hw, hw, Nat.cast_inj] at this⟩
  have hqc : UniformContinuous (Rat.castHom E) := by
    refine Isometry.uniformContinuous (AddMonoidHomClass.isometry_of_norm _ fun q ↦ ?_)
    exact (hq q).trans (by rw [← Rat.norm_cast_real, Real.norm_eq_abs])
  let g : ℝ →+* E := IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast hqc
  have hg (q : ℚ) : g q = q :=
    (Rat.isUniformEmbedding_coe_real.isUniformInducing.isDenseInducing
      Rat.denseRange_cast).extend_eq hqc.continuous q
  have hgc : Continuous g := (uniformContinuous_uniformly_extend
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast hqc).continuous
  have hgn (r : ℝ) : ‖g r‖ = |r| := by
    refine congrFun (Rat.isDenseEmbedding_coe_real.dense.equalizer
      (g := fun r ↦ ‖g r‖) (h := fun r ↦ |r|) (by fun_prop) continuous_abs (funext fun q ↦ ?_)) r
    simp [hg, hq]
  -- So `E` is a normed `ℝ`-algebra, and Gelfand–Mazur applies.
  let : NormedAlgebra ℝ E :=
    { g.toAlgebra with norm_smul_le r x := by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        hgn] }
  -- The algebra map of this instance is `g` by construction.
  have hE (r : ℝ) : ‖algebraMap ℝ E r‖ = |r| := hgn r
  -- An `ℝ`-algebra isomorphism `E ≃ₐ[ℝ] ℂ` is an isometry.
  have key (e : E ≃ₐ[ℝ] ℂ) (y : E) : ‖e y‖ = ‖y‖ := by
    let N : AbsoluteValue ℂ ℝ :=
      (NormedField.toAbsoluteValue E).comp (e.symm : ℂ →+* E).injective
    have hN (z : ℂ) : N z = ‖e.symm z‖ := by simp [N]
    have := eq_norm_of_apply_ofReal N (fun r ↦ by
      rw [hN, ← Complex.coe_algebraMap, AlgEquiv.commutes, hE]) (e y)
    rw [hN, AlgEquiv.symm_apply_apply] at this
    exact this.symm
  rcases NormedAlgebra.Real.nonempty_algEquiv_or E with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine ⟨(Complex.ofRealHom.comp (e : E →+* ℝ)).comp ι, fun x ↦ ?_⟩
    have : algebraMap ℝ E (e (ι x)) = ι x := by
      simpa using (e.symm.commutes (e (ι x))).symm
    simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real,
      Real.norm_eq_abs, RingHom.coe_coe]
    rw [← hE, this, hι]
  · exact ⟨(e : E →+* ℂ).comp ι, fun x ↦ by simp [key, hι]⟩

end AbsoluteValue
