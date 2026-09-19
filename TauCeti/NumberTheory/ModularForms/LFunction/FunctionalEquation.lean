/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Fricke.Normalized
public import TauCeti.NumberTheory.ModularForms.LFunction.Basic
public import TauCeti.NumberTheory.ModularForms.ResToImagAxis

/-!
# The Fricke functional equation of a cusp form

For a cusp form `f` of positive integral weight, the level-`N` completion is the Mellin
transform of the restriction of `f` to the rescaled imaginary axis,

`Λ_N(s, f) = Mellin (t ↦ f(i t / √N)) s`.

If `g` is the Petersson-normalized Fricke companion
`g = (√N)^(2-k) • (f ∣[k] W_N)`, then

`Λ_N(k - s, f) = i^k Λ_N(s, g)`.

The rescaling identity for Mellin transforms identifies `Λ_N` with `(√N)^s` times Mathlib's
entire `ModularForm.Λ`, so the completed function is entire.  On `Γ₁(N)`, Tau Ceti's bundled
`normalizedFrickeOperatorCusp` supplies the companion without an additional hypothesis.

## Main results

* `UpperHalfPlane.resToImagAxis_slash_frickeGL`: the Fricke slash on the rescaled imaginary axis.
* `CuspForm.frickeCompletedL`: the level-`N` completed L-function.
* `CuspForm.frickeCompletedL_eq_cpow_mul_Λ`: its expression as `N^(s/2) · ModularForm.Λ`.
* `CuspForm.frickeCompletedL_sub_eq_I_zpow_mul`: `Λ_N(k - s, f) = i^k Λ_N(s, g)` for any
  Fricke companion `g`, without weight or width hypotheses.
* `CuspForm.frickeCompletedL_functional_equation`: the two-form Fricke functional equation.
* `CuspForm.frickeCompletedL_functional_equation_Gamma1`: the functional equation on `Γ₁(N)`
  with the bundled normalized Fricke companion.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Apache-2.0, commit `112d12d95`),
`LeanModularForms/Modularforms/LFunctionFEqN.lean`.  This version reuses Mathlib's completed
L-function and Mellin change-of-variables API instead of rebuilding the analytic-continuation
argument.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Theorem 5.10.2.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Section 3.6.
* T. Miyake, *Modular Forms*, Theorem 4.3.5.
-/

public section

noncomputable section

open Complex MeasureTheory UpperHalfPlane
open scoped MatrixGroups ModularForm Real

namespace UpperHalfPlane

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The point `i t / √N` in the upper half-plane, for `t > 0`. -/
private noncomputable def scaledImLift {t : ℝ} (ht : 0 < t) : ℍ :=
  ⟨Complex.I * (t / Real.sqrt N : ℝ), by
    have hN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)
    simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul]
    positivity⟩

private lemma scaledImLift_coe {t : ℝ} (ht : 0 < t) :
    ((scaledImLift (N := N) ht : ℍ) : ℂ) = Complex.I * (t / Real.sqrt N : ℝ) :=
  (rfl)

private lemma resToImagAxis_scaled_eq (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis F (t / Real.sqrt N) = F (scaledImLift (N := N) ht) := by
  have hN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)
  have htN : 0 < t / Real.sqrt N := by positivity
  rw [resToImagAxis_of_pos F htN]
  congr 1

private lemma frickeGL_smul_scaledImLift {t : ℝ} (ht : 0 < t) :
    TauCeti.frickeGL ℝ N • scaledImLift (N := N) ht =
      scaledImLift (N := N) (one_div_pos.mpr ht) := by
  have hN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)
  have hNc : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsqN : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_cast
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos TauCeti.val_det_frickeGL_pos]
  rw [UpperHalfPlane.num, UpperHalfPlane.denom, TauCeti.coe_frickeGL,
    scaledImLift_coe, scaledImLift_coe]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [div_eq_iff (by
    have : (N : ℂ) * (Complex.I * (↑t / ↑(Real.sqrt N))) ≠ 0 := by
      refine mul_ne_zero (by exact_mod_cast NeZero.ne N) (mul_ne_zero Complex.I_ne_zero ?_)
      exact div_ne_zero htc hNc
    simpa using this)]
  rw [← hsqN]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Fricke slash on the rescaled imaginary axis.  For `t > 0`,

`(F ∣[k] W_N)(i t / √N) = (√N)^(k-2) i^(-k) t^(-k) F(i / (t√N))`.

The power of `√N` is exactly cancelled by the Petersson normalization of the Fricke operator. -/
theorem resToImagAxis_slash_frickeGL (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis (F ∣[k] TauCeti.frickeGL ℝ N) (t / Real.sqrt N) =
      (Real.sqrt N : ℂ) ^ (k - 2) * Complex.I ^ (-k) * (t : ℂ) ^ (-k) *
        resToImagAxis F (1 / t / Real.sqrt N) := by
  have hN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)
  have hNc : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsqN : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_cast
  rw [resToImagAxis_scaled_eq (F ∣[k] TauCeti.frickeGL ℝ N) ht,
    resToImagAxis_scaled_eq F (one_div_pos.mpr ht), ModularForm.slash_apply,
    frickeGL_smul_scaledImLift ht]
  have hσ : ∀ w : ℂ, UpperHalfPlane.σ (TauCeti.frickeGL ℝ N) w = w := fun w ↦ by
    have hdet : (0 : ℝ) < ((TauCeti.frickeGL ℝ N).det : ℝ) :=
      TauCeti.val_det_frickeGL_pos
    simp only [UpperHalfPlane.σ]
    split
    · rfl
    · rename_i h
      exact (h hdet).elim
  rw [hσ]
  have hdet : |((TauCeti.frickeGL ℝ N).det : ℝ)| = (N : ℝ) := by
    rw [TauCeti.val_det_frickeGL]
    exact abs_of_nonneg (Nat.cast_nonneg N)
  rw [hdet]
  have hdenom : UpperHalfPlane.denom (TauCeti.frickeGL ℝ N) (scaledImLift (N := N) ht) =
      (Real.sqrt N : ℂ) * Complex.I * (t : ℂ) := by
    rw [UpperHalfPlane.denom, TauCeti.coe_frickeGL, scaledImLift_coe]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    -- `denom` leaves `N` as a complex cast; expose its square-root factorization for `field_simp`.
    rw [show (N : ℂ) = (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) from hsqN.symm]
    field_simp
    ring
  rw [hdenom]
  have hN2 : ((N : ℝ) : ℂ) ^ (k - 1) = (Real.sqrt N : ℂ) ^ (2 * (k - 1)) := by
    -- `zpow_mul` needs both the real/natural cast and the numeral exponent made syntactic.
    rw [show ((N : ℝ) : ℂ) = (Real.sqrt N : ℂ) ^ (2 : ℤ) by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq]
      exact hsqN.symm, ← zpow_mul]
  have hsplit : ((Real.sqrt N : ℂ) * Complex.I * (t : ℂ)) ^ (-k) =
      (Real.sqrt N : ℂ) ^ (-k) * Complex.I ^ (-k) * (t : ℂ) ^ (-k) := by
    rw [mul_zpow, mul_zpow]
  rw [mul_assoc, hN2, hsplit]
  -- Reassociate the product and normalize its integer exponent so `zpow_add₀` sees the
  -- cancellable square-root powers.
  rw [show (Real.sqrt N : ℂ) ^ (2 * (k - 1)) *
        ((Real.sqrt N : ℂ) ^ (-k) * Complex.I ^ (-k) * (t : ℂ) ^ (-k)) =
      ((Real.sqrt N : ℂ) ^ (2 * (k - 1)) * (Real.sqrt N : ℂ) ^ (-k)) *
        (Complex.I ^ (-k) * (t : ℂ) ^ (-k)) by ring,
    ← zpow_add₀ hNc, show 2 * (k - 1) + -k = k - 2 by ring]
  ring

end UpperHalfPlane

namespace CuspForm

variable {N : ℕ} [NeZero N] {k : ℤ}
variable {Γ : Subgroup (GL (Fin 2) ℝ)}

/-- The level-`N` completed L-function of a cusp form, for a positive level `N`, defined as the
Mellin transform of its restriction to the rescaled imaginary axis `t ↦ i t / √N`. -/
noncomputable def frickeCompletedL (f : CuspForm Γ k) (N : ℕ+) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ ↦ resToImagAxis (f : ℍ → ℂ) (t / Real.sqrt (N : ℕ))) s

/-- The defining equation for the level-`N` completed L-function. -/
@[simp] lemma frickeCompletedL_apply (f : CuspForm Γ k) (N : ℕ+) (s : ℂ) :
    frickeCompletedL f N s =
      mellin (fun t : ℝ ↦ resToImagAxis (f : ℍ → ℂ) (t / Real.sqrt (N : ℕ))) s :=
  (rfl)

private theorem frickeCompletedL_eq_sqrt_cpow_mul_Λ [Γ.IsArithmetic]
    (f : CuspForm Γ k) (N : ℕ+) (hk : 0 < k) (s : ℂ) :
    frickeCompletedL f N s =
      (Real.sqrt (N : ℕ) : ℂ) ^ s * ModularForm.Λ hk f s := by
  have hN : 0 < Real.sqrt (N : ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast N.pos)
  have hNinv : 0 < (Real.sqrt N)⁻¹ := inv_pos.mpr hN
  have heq : (fun t : ℝ ↦ resToImagAxis (f : ℍ → ℂ) (t / Real.sqrt N)) =
      (fun t : ℝ ↦ resToImagAxis (f : ℍ → ℂ) (t * (Real.sqrt N)⁻¹)) := by
    funext t
    rw [div_eq_mul_inv]
  simp only [frickeCompletedL]
  rw [heq, mellin_comp_mul_right _ s hNinv, smul_eq_mul,
    CuspForm.Λ_eq_mellin]
  have harg : (Real.sqrt N : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have ht' : 0 < t := ht
  rw [resToImagAxis_of_pos _ ht']
  congr 2
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos (by simpa using ht')]

/-- The level-`N` completed L-function is `N^(s/2)` times Mathlib's completed L-function
`ModularForm.Λ`.  Thus this definition has the classical completion
`N^(s/2) (2π)^(-s) Γ(s) L(s, f)` on the Dirichlet-series half-plane. -/
theorem frickeCompletedL_eq_cpow_mul_Λ [Γ.IsArithmetic]
    (f : CuspForm Γ k) (N : ℕ+) (hk : 0 < k) (s : ℂ) :
    frickeCompletedL f N s =
      ((N : ℕ) : ℂ) ^ (s / 2) * ModularForm.Λ hk f s := by
  rw [frickeCompletedL_eq_sqrt_cpow_mul_Λ f N hk s]
  -- `cpow_mul_ofReal_nonneg` expects a real base and its exponent as an explicit product.
  rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by norm_cast,
    show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring,
    Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]

/-- The level-`N` completed L-function of a positive-weight cusp form is entire. -/
theorem differentiable_frickeCompletedL [Γ.IsArithmetic]
    (f : CuspForm Γ k) (N : ℕ+) (hk : 0 < k) :
    Differentiable ℂ (frickeCompletedL f N) := by
  rw [funext fun s ↦ frickeCompletedL_eq_sqrt_cpow_mul_Λ f N hk s]
  let _ : NeZero (Real.sqrt (N : ℕ) : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast N.pos)).ne'⟩
  exact (differentiable_const_cpow_of_neZero (Real.sqrt (N : ℕ) : ℂ)).mul
    (CuspForm.differentiable_Λ hk f)

private lemma scaled_fricke_relation (H G : ℍ → ℂ)
    (hG : G = (Real.sqrt N : ℂ) ^ (2 - k) • (H ∣[k] TauCeti.frickeGL ℝ N))
    {t : ℝ} (ht : 0 < t) :
    resToImagAxis H (1 / t / Real.sqrt N) =
      (Complex.I ^ k * ((t ^ (k : ℝ) : ℝ) : ℂ)) •
        resToImagAxis G (t / Real.sqrt N) := by
  have hN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)
  have hNc : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [hG, congrFun (resToImagAxis_smul _ _) _]
  simp only [Pi.smul_apply]
  rw [UpperHalfPlane.resToImagAxis_slash_frickeGL H ht]
  -- Bridge the real `rpow` used by the FE convention to the corresponding complex `zpow`.
  rw [smul_eq_mul, smul_eq_mul,
    show ((t ^ (k : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ k by
      rw [← Complex.ofReal_zpow, Real.rpow_intCast]]
  -- Reassociation exposes the inverse `√N`, `I`, and `t` powers to the `zpow_add₀` rewrites.
  rw [show (Real.sqrt N : ℂ) ^ (2 - k) *
        ((Real.sqrt N : ℂ) ^ (k - 2) * Complex.I ^ (-k) * (t : ℂ) ^ (-k) *
          resToImagAxis H (1 / t / Real.sqrt N)) =
      ((Real.sqrt N : ℂ) ^ (2 - k) * (Real.sqrt N : ℂ) ^ (k - 2)) *
        (Complex.I ^ (-k) * (t : ℂ) ^ (-k)) *
          resToImagAxis H (1 / t / Real.sqrt N) by ring,
    ← zpow_add₀ hNc, show (2 - k) + (k - 2) = 0 by ring, zpow_zero, one_mul]
  rw [show Complex.I ^ k * (t : ℂ) ^ k *
        (Complex.I ^ (-k) * (t : ℂ) ^ (-k) *
          resToImagAxis H (1 / t / Real.sqrt N)) =
      (Complex.I ^ k * Complex.I ^ (-k)) * ((t : ℂ) ^ k * (t : ℂ) ^ (-k)) *
        resToImagAxis H (1 / t / Real.sqrt N) by ring,
    ← zpow_add₀ Complex.I_ne_zero, ← zpow_add₀ htc, add_neg_cancel, zpow_zero,
    zpow_zero, one_mul, one_mul]

/-- The identity underlying Hecke's two-form functional equation.  If `g` is the
Petersson-normalized Fricke companion of `f`, then `Λ_N(k - s, f) = i^k Λ_N(s, g)`, without
additional weight or width hypotheses; this follows from Mellin change of variables alone. -/
theorem frickeCompletedL_sub_eq_I_zpow_mul
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)}
    (f : CuspForm Γ₁ k) (g : CuspForm Γ₂ k) (N : ℕ) [NeZero N]
    (hg : (g : ℍ → ℂ) =
      (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] TauCeti.frickeGL ℝ N))
    (s : ℂ) :
    frickeCompletedL f (N.toPNat (NeZero.pos N)) ((k : ℂ) - s) =
      Complex.I ^ k * frickeCompletedL g (N.toPNat (NeZero.pos N)) s := by
  let A : ℝ → ℂ := fun t ↦ resToImagAxis (f : ℍ → ℂ) (t / Real.sqrt N)
  let B : ℝ → ℂ := fun t ↦ resToImagAxis (g : ℍ → ℂ) (t / Real.sqrt N)
  have hAB {t : ℝ} (ht : 0 < t) :
      A t = (Complex.I ^ k * (t : ℂ) ^ (-(k : ℂ))) • B (1 / t) := by
    have h := scaled_fricke_relation (N := N) (k := k) (f : ℍ → ℂ) (g : ℍ → ℂ) hg
      (one_div_pos.mpr ht)
    rw [one_div_div] at h
    norm_num at h
    dsimp only [A, B]
    simp only [one_div]
    rw [h]
    congr 2
    rw [← zpow_neg, ← Complex.cpow_intCast]
    norm_cast
  simp only [frickeCompletedL, Nat.toPNat, PNat.val]
  have hcongr : mellin A ((k : ℂ) - s) =
      mellin (fun t ↦ (Complex.I ^ k) • ((t : ℂ) ^ (-(k : ℂ)) • B (1 / t)))
        ((k : ℂ) - s) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [hAB ht]
    simp only [smul_eq_mul]
    ring
  -- The local names prevent repeated large terms above; unfold them explicitly for the final
  -- Mellin rewrites, whose left-hand sides do not unfold `let` bindings during matching.
  rw [show (fun t : ℝ ↦ resToImagAxis (f : ℍ → ℂ) (t / Real.sqrt N)) = A from rfl,
    show (fun t : ℝ ↦ resToImagAxis (g : ℍ → ℂ) (t / Real.sqrt N)) = B from rfl,
    hcongr, mellin_const_smul, mellin_cpow_smul]
  -- Put the exponent and reciprocal function into the exact normal forms expected by the two
  -- Mellin change-of-variables lemmas.
  rw [show ((k : ℂ) - s) + -(k : ℂ) = -s by ring,
    show (fun t ↦ B (1 / t)) = (fun t ↦ B t⁻¹) by simp [one_div],
    mellin_comp_inv, neg_neg, smul_eq_mul]

/-- Hecke's two-form functional equation.  If `f` and `g` are positive-weight, width-one cusp
forms and `g` is the Petersson-normalized Fricke companion of `f`, then
`Λ_N(k - s, f) = i^k Λ_N(s, g)`.  The two forms may live on different carriers, but both have
weight `k`. -/
theorem frickeCompletedL_functional_equation
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)}
    (f : CuspForm Γ₁ k) (g : CuspForm Γ₂ k) (N : ℕ) [NeZero N]
    (_hw₁ : Γ₁.strictWidthInfty = 1) (_hw₂ : Γ₂.strictWidthInfty = 1) (_hk : 0 < k)
    (hg : (g : ℍ → ℂ) =
      (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] TauCeti.frickeGL ℝ N))
    (s : ℂ) :
    frickeCompletedL f (N.toPNat (NeZero.pos N)) ((k : ℂ) - s) =
      Complex.I ^ k * frickeCompletedL g (N.toPNat (NeZero.pos N)) s :=
  frickeCompletedL_sub_eq_I_zpow_mul f g N hg s

open Matrix.SpecialLinearGroup CongruenceSubgroup
open TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- Hecke's functional equation for a positive-weight cusp form on `Γ₁(N)`, with the normalized
Fricke operator providing the companion cusp form. -/
theorem frickeCompletedL_functional_equation_Gamma1
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 0 < k) (s : ℂ) :
    frickeCompletedL f (N.toPNat (NeZero.pos N)) ((k : ℂ) - s) =
      Complex.I ^ k *
        frickeCompletedL (normalizedFrickeOperatorCusp k f) (N.toPNat (NeZero.pos N)) s := by
  apply frickeCompletedL_functional_equation f (normalizedFrickeOperatorCusp k f) N
      (by simp) (by simp) hk
  simp only [coe_normalizedFrickeOperatorCusp, atkinLehnerNormalizer_def]

end CuspForm
