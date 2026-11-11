/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.Basic
public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The winding number of a zero-free loop on the circle

A zero-free continuous function `g` on the circle `AddCircle T` winds some integral number `d` of
times around the origin. This file states that through continuous logarithms
(`TauCeti.HasContinuousLogOn`): `g` divided by the Fourier monomial `fourier d`, the loop
`x ↦ e^{2πidx/T}`, has a continuous logarithm, and the integer `d` with this property is unique
when `T ≠ 0`. In other words every zero-free loop is `fourier d * exp L` for a continuous `L`, and
`d` is its winding number.

Existence (`TauCeti.exists_hasContinuousLogOn_div_fourier`) lifts `g`, read as a periodic function
on `ℝ`, through the exponential (Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp`). The lift
`ℓ` satisfies `ℓ(t + T) = ℓ(t) + 2πid` for an integer `d`, because both sides are continuous
logarithms of the same function (`TauCeti.exists_int_forall_eq_add_of_exp_eq`), and then
`ℓ(t) - 2πidt/T` is periodic and descends to the circle. Uniqueness comes from the fact that a
monomial `fourier n` with `n ≠ 0` has no continuous logarithm
(`TauCeti.not_hasContinuousLogOn_fourier`): a logarithm `L` would make `L(t) - 2πint/T` a continuous
logarithm of `1` on `ℝ`, hence constant, while going once around the circle changes it by `-2πin`.

## Main statements

* `TauCeti.not_hasContinuousLogOn_fourier`: for `T ≠ 0` and `n ≠ 0`, the monomial `fourier n` has
  no continuous logarithm on the circle.
* `TauCeti.exists_hasContinuousLogOn_div_fourier`: a zero-free continuous function on the circle
  has a continuous logarithm after division by some monomial `fourier d`.
* `TauCeti.eq_of_hasContinuousLogOn_div_fourier`: for `T ≠ 0` this integer `d` is unique.
-/

public section

noncomputable section

open Complex Set

open scoped Real

namespace TauCeti

variable {T : ℝ}

/-- **The monomials of nonzero degree have no continuous logarithm.** For `T ≠ 0` and `n ≠ 0`, no
continuous `L` on `AddCircle T` satisfies `exp (L x) = fourier n x`: going once around the circle,
`L` would have to increase by `2πin`. -/
theorem not_hasContinuousLogOn_fourier (hT : T ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    ¬HasContinuousLogOn (fourier (T := T) n) univ := by
  intro h
  obtain ⟨L, hL, hLe⟩ := hasContinuousLogOn_iff.1 h
  rw [continuousOn_univ] at hL
  -- On `ℝ`, `t ↦ L t - 2πint/T` is a continuous logarithm of `1`, so it is constant.
  obtain ⟨k, hk⟩ := exists_int_forall_eq_add_of_exp_eq (u := fun _ : ℝ ↦ (0 : ℂ))
    (v := fun t : ℝ ↦ L t - 2 * π * I * n * t / T) continuous_const (by fun_prop) fun t ↦ by
      rw [exp_zero, exp_sub, hLe _ (mem_univ _), fourier_coe_apply, div_self (exp_ne_zero _)]
  have h := (hk T).trans (hk 0).symm
  have hT' : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT
  simp only [AddCircle.coe_period, QuotientAddGroup.mk_zero, ofReal_zero, mul_zero, zero_div,
    sub_zero, mul_div_assoc, div_self hT', mul_one, sub_eq_self] at h
  simp [Real.pi_ne_zero, I_ne_zero, hn] at h

/-- **Every zero-free loop has a winding number.** A zero-free continuous function `g` on the circle
has a continuous logarithm after division by the monomial `fourier d`, for some integer `d`. -/
theorem exists_hasContinuousLogOn_div_fourier {g : AddCircle T → ℂ} (hg : Continuous g)
    (hg₀ : ∀ x, g x ≠ 0) : ∃ d : ℤ, HasContinuousLogOn (fun x ↦ g x / fourier d x) univ := by
  -- Lift `g`, read as a function on `ℝ`, through the exponential.
  have hsimply : IsSimplyConnected (univ : Set ℝ) :=
    (Homeomorph.Set.univ ℝ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨ℓ, hℓ, hℓe⟩ := exists_continuousOn_eqOn_exp_comp hsimply isOpen_univ
    (hg.comp continuous_quotient_mk').continuousOn (by simp [hg₀])
  rw [continuousOn_univ] at hℓ
  have hℓe' (t : ℝ) : exp (ℓ t) = g t := hℓe (mem_univ t)
  -- Going once around the circle changes the lift by `2πid`.
  obtain ⟨d, hd⟩ := exists_int_forall_eq_add_of_exp_eq (v := fun t ↦ ℓ (t + T)) hℓ
    (hℓ.comp (continuous_id.add continuous_const)) fun t ↦ by
      rw [hℓe', hℓe', AddCircle.coe_add_period]
  -- So `t ↦ ℓ t - 2πidt/T` is periodic and descends to the circle.
  have hper : Function.Periodic (fun t : ℝ ↦ ℓ t - 2 * π * I * d * t / T) T := fun t ↦ by
    rcases eq_or_ne T 0 with rfl | hT
    · simp
    have hT' : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT
    simp only [hd t]
    push_cast
    field_simp
    ring
  refine ⟨d, hasContinuousLogOn_iff.2 ⟨hper.lift, ?_, fun x _ ↦ ?_⟩⟩
  · rw [continuousOn_univ]
    refine (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples T)).continuous_iff.2 ?_
    have : hper.lift ∘ ((↑) : ℝ → AddCircle T) = fun t ↦ ℓ t - 2 * π * I * d * t / T :=
      funext fun t ↦ hper.lift_coe t
    rw [this]
    fun_prop
  · induction x using QuotientAddGroup.induction_on with | H t => ?_
    rw [Function.Periodic.lift_coe, exp_sub, hℓe', fourier_coe_apply]

/-- **The winding number is unique.** For `T ≠ 0`, if `g / fourier d` and `g / fourier d'` both
have continuous logarithms on the circle, then `d = d'`. -/
theorem eq_of_hasContinuousLogOn_div_fourier (hT : T ≠ 0) {g : AddCircle T → ℂ} {d d' : ℤ}
    (h : HasContinuousLogOn (fun x ↦ g x / fourier d x) univ)
    (h' : HasContinuousLogOn (fun x ↦ g x / fourier d' x) univ) : d = d' := by
  by_contra hne
  refine not_hasContinuousLogOn_fourier hT (sub_ne_zero.2 hne) <| (h'.div h).congr fun x _ ↦ ?_
  have hg : g x ≠ 0 := fun h0 ↦ h.ne_zero (mem_univ x) (by simp [h0])
  have hadd : (fourier d x : ℂ) = fourier (d - d') x * fourier d' x := by
    rw [← fourier_add, sub_add_cancel]
  simp only
  rw [hadd]
  field_simp [hg, fourier_apply_ne_zero]

end TauCeti
