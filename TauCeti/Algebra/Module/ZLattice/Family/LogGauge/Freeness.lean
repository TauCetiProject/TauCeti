/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Basic
import Mathlib.Algebra.Module.Torsion.Free
import TauCeti.Algebra.Module.ZLattice.Family.RotatedDisc

/-!
# Freeness criterion for the normalized translation action

Over a disc of positive radius whose central periods `P 0` are injective, the normalized pure
translation action `TauCeti.logTranslationMulAction` for `l : Λ` on the pulled-back family of tori
is free exactly when the class of `l` in `Λ ⧸ mΛ` has exact additive order `m`
(`TauCeti.isCancelSMul_logTranslationMulAction_iff`).

This criterion is separated from `TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Basic` so basic
gauge consumers need not import the rotated-disc analytic-order and torsion theory.

## Main results

* `TauCeti.isCancelSMul_logTranslationMulAction_iff`: exact-order freeness criterion for
  `TauCeti.logTranslationMulAction`.
-/

public section

open MulAction Set Complex
open scoped Real

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)

/-- **Freeness of the normalized action.** Over a disc of positive radius whose central periods
`P 0` are injective, the normalized pure translation action for `l : Λ` is free exactly when the
class of `l` in `Λ ⧸ mΛ` has exact additive order `m`. -/
theorem isCancelSMul_logTranslationMulAction_iff (hr : 0 < r)
    (hinj : Function.Injective (P ⟨0, mem_ball_zero_iff.2 (by simpa using pow_pos hr m)⟩))
    (l : Λ) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) ↔
      addOrderOf (Submodule.Quotient.mk l : QuotSMulTop (m : ℤ) Λ) = m := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  let u₀ : rootsOfUnityBall m r := ⟨0, mem_rootsOfUnityBall.2 (by simpa using hr)⟩
  have hu₀ : (u₀ : ℂ) = 0 := rfl
  have hpow₀ : rootsOfUnityBall.powMap m r u₀ =
      ⟨0, mem_ball_zero_iff.2 (by simpa using pow_pos hr m)⟩ :=
    Subtype.ext (by simp [u₀, zero_pow (NeZero.ne m)])
  have hprimℂ : IsPrimitiveRoot (exp (2 * π * I / m)) m :=
    Complex.isPrimitiveRoot_exp m (NeZero.ne m)
  let ζ : rootsOfUnity m ℂ := hprimℂ.toRootsOfUnity
  have hζval : exp (2 * π * I / m) = ((ζ : ℂˣ) : ℂ) := hprimℂ.val_toRootsOfUnity_coe.symm
  have hζprim : IsPrimitiveRoot ζ m :=
    IsPrimitiveRoot.coe_submonoidClass_iff.1 (IsPrimitiveRoot.coe_units_iff.1 (hζval ▸ hprimℂ))
  have hmE : Function.Injective fun v : E ↦ m • v := by
    have : HasUniqueDiv E := .of_isTorsionFree ℂ E
    exact nsmul_right_injective (NeZero.ne m)
  have hβ : logTranslationSection P l ζ u₀ =
      Quotient.mk _ (u₀, (m : ℂ)⁻¹ • powPullbackPeriod m r P u₀ l) := by
    rw [logTranslationSection_eq_mk_of_exp_eq P l hζval,
      smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ, div_div_cancel_left₀ two_pi_I_ne_zero]
  have hl : powPullbackPeriod m r P u₀ l =
      m • ((m : ℂ)⁻¹ • powPullbackPeriod m r P u₀ l) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (NeZero.ne m))]
  exact isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_mk_eq
    (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
    (powPullbackPeriod m r P) (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ)
    (powPullbackPeriod_smul_apply P) (logTranslationSection P l)
    (torusFamilyProjection_logTranslationSection P l) (logTranslationSection_mul P l)
    hu₀ hζprim (fun _ ↦ rfl) (by simpa only [powPullbackPeriod_apply, hpow₀] using hinj)
    hmE hβ hl

end TauCeti
