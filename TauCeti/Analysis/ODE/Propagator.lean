/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Caratheodory
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousSubstitution.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The propagator of a linear equation with an integrable coefficient

Let `E` be a Banach space over `𝕜` and let `P : ℝ → E →L[𝕜] E` be integrable on `[a, b]`, not
necessarily continuous or essentially bounded. For `s, t ∈ [a, b]` the propagator
`N_P(t, s) ∈ E →L[𝕜] E` is the value at `t` of the solution of the operator equation

`N(t) = 1 + ∫ r in s..t, P r ∘L N r`,

so that `N_P(t, s) y` is the value at `t` of the Carathéodory solution of `x' = P(t) x` with
`x(s) = y` (`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard`).

## Main definitions and results

* `TauCeti.propagator P t s`: the propagator `N_P(t, s)`. It is defined from the values of `P` on
  the interval between `s` and `t` only.
* `TauCeti.propagator_eq_of_forall_mem_Icc`: the propagator is the solution of the operator
  equation on any compact interval on which `P` is integrable;
  `TauCeti.propagator_eq_of_hasDerivAt` is the same for differentiable solutions.
* `TauCeti.propagator_eq_one_add_integral`: the integral equation.
* `TauCeti.propagator_apply_eq_add_integral`, `TauCeti.eq_propagator_apply`: `t ↦ N_P(t, s) y`
  solves `x t = y + ∫ r in s..t, P r (x r)`, and every continuous solution is of this form.
* `TauCeti.propagator_self`, `TauCeti.propagator_comp_propagator`: `N_P(t, t) = 1` and the cocycle
  identity `N_P(t, r) N_P(r, s) = N_P(t, s)`, so that `N_P(t, s)` is invertible with inverse
  `N_P(s, t)` (`TauCeti.isUnit_propagator`, `TauCeti.ringInverse_propagator`).
* `TauCeti.norm_propagator_le`, `TauCeti.norm_propagator_sub_one_le`:
  `‖N_P(t, s)‖ ≤ exp |∫ r in s..t, ‖P r‖|` and `‖N_P(t, s) - 1‖ ≤ exp |∫ r in s..t, ‖P r‖| - 1`.
* `TauCeti.norm_propagator_le_of_norm_le`: a domination `‖P r‖ ≤ m r` between `s` and `t` gives
  `‖N_P(t, s)‖ ≤ exp |∫ r in s..t, m r|`.
* `TauCeti.continuousOn_propagator`: `(t, s) ↦ N_P(t, s)` is continuous on `[a, b]²` in the
  operator norm.
* `TauCeti.absolutelyContinuousOnInterval_propagator_left`,
  `TauCeti.ae_hasDerivAt_propagator_left`: `t ↦ N_P(t, s)` is absolutely continuous, with
  derivative `P(t) N_P(t, s)` at almost every `t`.
* `TauCeti.ae_hasDerivAt_propagator_right`: `s ↦ N_P(t, s)` has derivative `-N_P(t, s) P(s)` at
  almost every `s`.
* `TauCeti.propagator_congr_ae`: the propagator depends only on `P` almost everywhere on the
  interval between `s` and `t`.
* `TauCeti.norm_propagator_sub_propagator_le`, `TauCeti.tendstoUniformlyOn_propagator`:
  `‖N_{P'}(t, s) - N_P(t, s)‖ ≤ ‖P' - P‖₁ exp (‖P'‖₁ + ‖P‖₁)` with `L¹` norms over the interval
  between `s` and `t`, so `L¹` convergence of coefficients gives uniform convergence of
  propagators on `[a, b]²`.
* `TauCeti.propagator_const`, `TauCeti.propagator_zero`: for a constant coefficient `A`,
  `N_P(t, s) = exp ((t - s) • A)`; for `P = 0`, `N_P(t, s) = 1`.
* `TauCeti.propagator_const_eq_cosh_add_sinh`: for a constant coefficient `A` with `A² = a²`,
  `a ≠ 0` real, `N_P(t, s) = cosh((t - s) a) + (sinh((t - s) a) / a) A`.

## Implementation notes

Existence and uniqueness for the operator equation are the linear Carathéodory theorem in the
Banach space `E →L[𝕜] E`, with the real-linear coefficient `X ↦ P r ∘L X`, that is
`ContinuousLinearMap.mul ℝ (E →L[𝕜] E) (P r)`. The scalars `𝕜` enter
only through `P`: the integrals are over `ℝ`, so `E` carries compatible real and `𝕜` structures.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
* R. Romanov, *Canonical systems and de Branges spaces*, §1.
-/

public section

open MeasureTheory Set intervalIntegral Real

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

open scoped Classical in
/-- The propagator `N_P(t, s)` of the linear equation `x' = P(t) x`: the value at `t` of the
continuous solution on the interval between `s` and `t` of the operator equation
`N r = 1 + ∫ u in s..r, P u ∘L N u`. When `E` is complete and `P` is integrable on that interval,
the solution exists (`TauCeti.propagator_eq_one_add_integral`,
`TauCeti.continuousOn_propagator_left`) and is unique (`TauCeti.propagator_eq_of_forall_mem_Icc`).
When no such solution exists, the value is `1`. -/
noncomputable def propagator (P : ℝ → E →L[𝕜] E) (t s : ℝ) : E →L[𝕜] E :=
  if h : ∃ N : ℝ → E →L[𝕜] E, ContinuousOn N (uIcc s t) ∧
      ∀ r ∈ uIcc s t, N r = 1 + ∫ u in s..r, P u ∘L N u then h.choose t else 1

namespace Propagator

private theorem picard_mul (P : ℝ → E →L[𝕜] E) (N : ℝ → E →L[𝕜] E) (s r : ℝ) :
    ODE.picard (fun u Y ↦ ContinuousLinearMap.mul ℝ (E →L[𝕜] E) (P u) Y +
      (fun _ ↦ (0 : E →L[𝕜] E)) u) s 1 N r = 1 + ∫ u in s..r, P u ∘L N u := by
  simp [ODE.picard_apply, ContinuousLinearMap.mul_def]

private theorem picard_restrictScalars (P : ℝ → E →L[𝕜] E) (x : ℝ → E) (y : E) (s r : ℝ) :
    ODE.picard (fun u z ↦ (P u).restrictScalars ℝ z + (fun _ ↦ (0 : E)) u) s y x r =
      y + ∫ u in s..r, P u (x u) := by
  simp [ODE.picard_apply]

variable {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

/-- The real-linear coefficient `X ↦ P u ∘L X` is integrable. Stated once because
`(ContinuousLinearMap.mul ℝ (E →L[𝕜] E)).integrable_comp hP` elaborates only with its implicit
arguments spelled out: the additive structures on `E →L[𝕜] E` reached through `NonUnitalNormedRing`
and through `ContinuousLinearMap.toNormedAddCommGroup` are not unified otherwise. -/
private theorem integrableOn_mul {S : Set ℝ} (hP : IntegrableOn P S) :
    IntegrableOn (fun u ↦ ContinuousLinearMap.mul ℝ (E →L[𝕜] E) (P u)) S := by
  have := ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ)
    (H := E →L[𝕜] E) (E := (E →L[𝕜] E) →L[ℝ] E →L[𝕜] E) (ContinuousLinearMap.mul ℝ _) hP
  exact this

private theorem exists_sol [CompleteSpace E] (hP : IntegrableOn P (Icc a b))
    (hs : s ∈ Icc a b) :
    ∃ N : ℝ → E →L[𝕜] E, ContinuousOn N (Icc a b) ∧
      ∀ r ∈ Icc a b, N r = 1 + ∫ u in s..r, P u ∘L N u := by
  obtain ⟨N, hN, h⟩ := exists_continuousOn_forall_mem_Icc_eq_picard hs
    (integrableOn_mul hP) integrableOn_zero 1
  exact ⟨N, hN, fun r hr ↦ (h r hr).trans (picard_mul P N s r)⟩

private theorem eqOn_sol (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    {N₁ N₂ : ℝ → E →L[𝕜] E} (hN₁ : ContinuousOn N₁ (Icc a b)) (hN₂ : ContinuousOn N₂ (Icc a b))
    (h₁ : ∀ r ∈ Icc a b, N₁ r = 1 + ∫ u in s..r, P u ∘L N₁ u)
    (h₂ : ∀ r ∈ Icc a b, N₂ r = 1 + ∫ u in s..r, P u ∘L N₂ u) :
    EqOn N₁ N₂ (Icc a b) := by
  have hM := integrableOn_mul hP
  exact eqOn_of_forall_mem_Icc_eq_picard (M := fun u ↦ ContinuousLinearMap.mul ℝ _ (P u))
    (F := fun _ ↦ (0 : E →L[𝕜] E)) (x₀ := 1) hs hM integrableOn_zero hN₁ hN₂
    (fun r hr ↦ (h₁ r hr).trans (picard_mul P N₁ s r).symm)
    (fun r hr ↦ (h₂ r hr).trans (picard_mul P N₂ s r).symm)

end Propagator

open Propagator

variable {P : ℝ → E →L[𝕜] E} {a b r s t : ℝ}

/-- The propagator `N_P(t, t)` is the identity. -/
@[simp]
theorem propagator_self (P : ℝ → E →L[𝕜] E) (t : ℝ) : propagator P t t = 1 := by
  have hex : ∃ N : ℝ → E →L[𝕜] E, ContinuousOn N (uIcc t t) ∧
      ∀ r ∈ uIcc t t, N r = 1 + ∫ u in t..r, P u ∘L N u :=
    ⟨fun _ ↦ 1, continuousOn_const, fun r hr ↦ by
      rw [uIcc_self, mem_singleton_iff] at hr
      simp [hr]⟩
  rw [propagator, dite_eq_left hex]
  simpa using hex.choose_spec.2 t (by simp)

/-- **Locality of the propagator.** `N_P(t, s)` depends only on the values of `P` almost
everywhere on the interval between `s` and `t`. -/
theorem propagator_congr_ae {P Q : ℝ → E →L[𝕜] E} (h : ∀ᵐ u, u ∈ uIoc s t → P u = Q u) :
    propagator P t s = propagator Q t s := by
  have key : ∀ N : ℝ → E →L[𝕜] E, ∀ r ∈ uIcc s t,
      ∫ u in s..r, P u ∘L N u = ∫ u in s..r, Q u ∘L N u := fun N r hr ↦
    integral_congr_ae (by
      filter_upwards [h] with u hu hur
      rw [hu (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hr) hur)])
  have hF : (fun N : ℝ → E →L[𝕜] E ↦ ContinuousOn N (uIcc s t) ∧
      ∀ r ∈ uIcc s t, N r = 1 + ∫ u in s..r, P u ∘L N u) =
      fun N ↦ ContinuousOn N (uIcc s t) ∧ ∀ r ∈ uIcc s t, N r = 1 + ∫ u in s..r, Q u ∘L N u :=
    funext fun N ↦ propext (and_congr_right fun _ ↦ forall₂_congr fun r hr ↦ by rw [key N r hr])
  classical
  simp only [propagator]
  exact congrArg (fun p : (ℝ → E →L[𝕜] E) → Prop ↦ if h : ∃ N, p N then h.choose t else 1) hF

/-- **Characterisation of the propagator.** If `P` is integrable on `[a, b]` and `N` is a solution
continuous on `[a, b]` of `N r = 1 + ∫ u in s..r, P u ∘L N u`, then `N_P(t, s) = N t` for every
`t ∈ [a, b]`. -/
theorem propagator_eq_of_forall_mem_Icc (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {N : ℝ → E →L[𝕜] E} (hN : ContinuousOn N (Icc a b))
    (h : ∀ r ∈ Icc a b, N r = 1 + ∫ u in s..r, P u ∘L N u) : propagator P t s = N t := by
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  have hex : ∃ N : ℝ → E →L[𝕜] E, ContinuousOn N (uIcc s t) ∧
      ∀ r ∈ uIcc s t, N r = 1 + ∫ u in s..r, P u ∘L N u :=
    ⟨N, hN.mono hsub, fun r hr ↦ h r (hsub hr)⟩
  rw [propagator, dite_eq_left hex]
  exact eqOn_sol (hP.mono_set hsub) left_mem_uIcc hex.choose_spec.1 (hN.mono hsub)
    hex.choose_spec.2 (fun r hr ↦ h r (hsub hr)) right_mem_uIcc

/-- **Degenerate coefficient.** For `P = 0`, `N_P(t, s) = 1`. -/
@[simp]
theorem propagator_zero (t s : ℝ) : propagator (0 : ℝ → E →L[𝕜] E) t s = 1 :=
  propagator_eq_of_forall_mem_Icc (P := fun _ ↦ 0) (a := min s t) (b := max s t)
    continuousOn_const.integrableOn_Icc ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨min_le_right _ _, le_max_right _ _⟩ continuousOn_const fun r _ ↦ by simp

variable [CompleteSpace E]

/-- The propagator `N_P(t, s)` is continuous in `t ∈ [a, b]` in the operator norm. -/
theorem continuousOn_propagator_left (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b) :
    ContinuousOn (fun t ↦ propagator P t s) (Icc a b) := by
  obtain ⟨N, hN, h⟩ := exists_sol hP hs
  exact hN.congr fun t ht ↦ propagator_eq_of_forall_mem_Icc hP hs ht hN h

/-- **The integral equation of the propagator.**
`N_P(t, s) = 1 + ∫ u in s..t, P u ∘L N_P(u, s)` for `s, t ∈ [a, b]`. -/
theorem propagator_eq_one_add_integral (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : propagator P t s = 1 + ∫ u in s..t, P u ∘L propagator P u s := by
  obtain ⟨N, hN, h⟩ := exists_sol hP hs
  rw [propagator_eq_of_forall_mem_Icc hP hs ht hN h, h t ht]
  congr 1
  refine integral_congr fun u hu ↦ ?_
  rw [propagator_eq_of_forall_mem_Icc hP hs (uIcc_subset_Icc hs ht hu) hN h]

/-- `t ↦ N_P(t, s) y` solves the linear equation `x t = y + ∫ u in s..t, P u (x u)` on `[a, b]`.
-/
theorem propagator_apply_eq_add_integral (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (y : E) :
    propagator P t s y = y + ∫ u in s..t, P u (propagator P u s y) := by
  have hI : IntervalIntegrable (fun u ↦ P u ∘L propagator P u s) volume s t :=
    hP.intervalIntegrable_clm_comp (continuousOn_propagator_left hP hs) hs ht
  conv_lhs => rw [propagator_eq_one_add_integral hP hs ht]
  rw [add_apply, one_apply_eq_self,
    ContinuousLinearMap.intervalIntegral_apply hI]
  simp only [ContinuousLinearMap.comp_apply]

/-- **Solutions are given by the propagator.** A curve `x` continuous on `[a, b]` with
`x r = x s + ∫ u in s..r, P u (x u)` for `r ∈ [a, b]` satisfies `x t = N_P(t, s) (x s)`. -/
theorem eq_propagator_apply (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ r ∈ Icc a b, x r = x s + ∫ u in s..r, P u (x u)) : x t = propagator P t s (x s) :=
  eqOn_of_forall_mem_Icc_eq_picard (M := fun u ↦ (P u).restrictScalars ℝ)
    (F := fun _ ↦ (0 : E)) (x₀ := x s) hs
    ((ContinuousLinearMap.restrictScalarsL 𝕜 E E ℝ ℝ).integrable_comp hP) integrableOn_zero hx
    ((continuousOn_propagator_left hP hs).clm_apply continuousOn_const)
    (fun r hr ↦ (h r hr).trans (picard_restrictScalars P x _ s r).symm)
    (fun r hr ↦ (propagator_apply_eq_add_integral hP hs hr _).trans
      (picard_restrictScalars P _ _ s r).symm) ht

/-- **The cocycle identity.** `N_P(t, r) N_P(r, s) = N_P(t, s)` for `r, s, t ∈ [a, b]`. -/
theorem propagator_comp_propagator (hP : IntegrableOn P (Icc a b)) (hr : r ∈ Icc a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    propagator P t r ∘L propagator P r s = propagator P t s := by
  ext y
  have hx : ContinuousOn (fun u ↦ propagator P u s y) (Icc a b) :=
    (continuousOn_propagator_left hP hs).clm_apply continuousOn_const
  have hI := hP.clm_apply_continuousOn hx isCompact_Icc
  -- Rebase the vector equation of `u ↦ N_P(u, s) y` from `s` to `r`.
  have h (u : ℝ) (hu : u ∈ Icc a b) : propagator P u s y =
      propagator P r s y + ∫ v in r..u, P v (propagator P v s y) := by
    rw [propagator_apply_eq_add_integral hP hs hu y, propagator_apply_eq_add_integral hP hs hr y,
      add_assoc, integral_add_adjacent_intervals
        ((hI.mono_set (uIcc_subset_Icc hs hr)).intervalIntegrable)
        ((hI.mono_set (uIcc_subset_Icc hr hu)).intervalIntegrable)]
  exact (eq_propagator_apply hP hr ht hx h).symm

/-- `N_P(s, t)` is a left inverse of `N_P(t, s)`. -/
theorem propagator_comp_propagator_swap (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : propagator P s t ∘L propagator P t s = 1 := by
  rw [propagator_comp_propagator hP ht hs hs, propagator_self]

/-- The propagator `N_P(t, s)` as a unit, with inverse `N_P(s, t)`. -/
private noncomputable def propagatorUnit (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : (E →L[𝕜] E)ˣ :=
  ⟨propagator P t s, propagator P s t, propagator_comp_propagator_swap hP ht hs,
    propagator_comp_propagator_swap hP hs ht⟩

private theorem coe_inv_propagatorUnit (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : ((propagatorUnit hP hs ht)⁻¹ : (E →L[𝕜] E)ˣ) = propagator P s t :=
  rfl

/-- The propagator `N_P(t, s)` is invertible, with inverse `N_P(s, t)`
(`TauCeti.ringInverse_propagator`). -/
theorem isUnit_propagator (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : IsUnit (propagator P t s) :=
  (propagatorUnit hP hs ht).isUnit

/-- The inverse of the propagator `N_P(t, s)` is `N_P(s, t)`. -/
theorem ringInverse_propagator (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : Ring.inverse (propagator P t s) = propagator P s t :=
  Ring.inverse_unit (propagatorUnit hP hs ht)

/-- **The norm bound.** `‖N_P(t, s)‖ ≤ exp |∫ u in s..t, ‖P u‖|` for `s, t ∈ [a, b]`. -/
theorem norm_propagator_le (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : ‖propagator P t s‖ ≤ exp |∫ u in s..t, ‖P u‖| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (exp_pos _).le fun y ↦ ?_
  have := norm_le_mul_exp_of_forall_mem_Icc_eq_picard (M := fun u ↦ (P u).restrictScalars ℝ)
    (F := fun _ ↦ (0 : E)) (x₀ := y) hs
    ((ContinuousLinearMap.restrictScalarsL 𝕜 E E ℝ ℝ).integrable_comp hP) integrableOn_zero
    ((continuousOn_propagator_left hP hs).clm_apply continuousOn_const)
    (fun r hr ↦ (propagator_apply_eq_add_integral hP hs hr y).trans
      (picard_restrictScalars P _ y s r).symm) ht
  simpa [mul_comm] using this

open scoped Interval in
/-- **The norm bound under a domination.** If `P` and `m` are integrable between `s` and `t` and
`‖P r‖ ≤ m r` for almost every `r` there, then `‖N_P(t, s)‖ ≤ exp |∫ r in s..t, m r|`. Applied
to a family of coefficients dominated by one function `m` for all parameters in a set, the
bound is uniform in the parameter. -/
theorem norm_propagator_le_of_norm_le {m : ℝ → ℝ} (hP : IntervalIntegrable P volume s t)
    (hm : IntervalIntegrable m volume s t) (hPm : ∀ᵐ r, r ∈ Ι s t → ‖P r‖ ≤ m r) :
    ‖propagator P t s‖ ≤ exp |∫ r in s..t, m r| := by
  have hP' : IntegrableOn P (Icc (min s t) (max s t)) :=
    Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc (by simpa only [uIoc] using hP.def')
  refine (norm_propagator_le hP'
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩).trans
    (exp_le_exp.2 (intervalIntegral.abs_integral_norm_le_abs_integral_of_norm_le hm hPm))

/-- The propagator `N_P(t, s)` is continuous in `s ∈ [a, b]` in the operator norm. -/
theorem continuousOn_propagator_right (hP : IntegrableOn P (Icc a b)) (ht : t ∈ Icc a b) :
    ContinuousOn (fun s ↦ propagator P t s) (Icc a b) := by
  -- On `[a, b]`, `N_P(t, s) = N_P(t, a) N_P(s, a)⁻¹`, and inversion is continuous on the units.
  intro s₀ hs₀
  have ha : a ∈ Icc a b := ⟨le_rfl, hs₀.1.trans hs₀.2⟩
  have hinv : ContinuousWithinAt (fun s ↦ Ring.inverse (propagator P s a)) (Icc a b) s₀ :=
    ContinuousAt.comp_continuousWithinAt (g := Ring.inverse) (f := fun s ↦ propagator P s a)
      -- The coercion of `propagatorUnit hP ha hs₀` is `propagator P s₀ a` by construction.
      (NormedRing.inverse_continuousAt (propagatorUnit hP ha hs₀))
      (continuousOn_propagator_left hP ha s₀ hs₀)
  have heq {s : ℝ} (hs : s ∈ Icc a b) :
      propagator P t s = propagator P t a ∘L Ring.inverse (propagator P s a) := by
    rw [ringInverse_propagator hP ha hs, propagator_comp_propagator hP ha hs ht]
  exact (continuousWithinAt_const.clm_comp hinv).congr (fun s hs ↦ heq hs) (heq hs₀)

/-- **Joint continuity of the propagator.** `(t, s) ↦ N_P(t, s)` is continuous on `[a, b]²` in
the operator norm. -/
theorem continuousOn_propagator (hP : IntegrableOn P (Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ ↦ propagator P p.1 p.2) (Icc a b ×ˢ Icc a b) := by
  intro p hp
  have ha : a ∈ Icc a b := ⟨le_rfl, hp.1.1.trans hp.1.2⟩
  refine ContinuousWithinAt.congr (f := fun p : ℝ × ℝ ↦ propagator P p.1 a ∘L propagator P a p.2)
    ?_ (fun q (hq : q ∈ Icc a b ×ˢ Icc a b) ↦ (propagator_comp_propagator hP ha hq.2 hq.1).symm)
    (propagator_comp_propagator hP ha hp.2 hp.1).symm
  exact ((continuousOn_propagator_left hP ha).comp continuousOn_fst
    (fun q (hq : q ∈ Icc a b ×ˢ Icc a b) ↦ hq.1) p hp).clm_comp
    ((continuousOn_propagator_right hP ha).comp continuousOn_snd
      (fun q (hq : q ∈ Icc a b ×ˢ Icc a b) ↦ hq.2) p hp)

/-- **Differentiable solutions.** If `P` is integrable on `[a, b]`, `X s = 1` and `X` has
derivative `P r ∘L X r` at every `r ∈ [a, b]`, then `N_P(t, s) = X t` for `s, t ∈ [a, b]`. -/
theorem propagator_eq_of_hasDerivAt (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {X : ℝ → E →L[𝕜] E} (hX : ∀ r ∈ Icc a b, HasDerivAt X (P r ∘L X r) r)
    (hXs : X s = 1) : propagator P t s = X t := by
  have hc : ContinuousOn X (Icc a b) := fun r hr ↦ (hX r hr).continuousAt.continuousWithinAt
  refine propagator_eq_of_forall_mem_Icc hP hs ht hc fun r hr ↦ ?_
  rw [integral_eq_sub_of_hasDerivAt (fun u hu ↦ hX u (uIcc_subset_Icc hs hr hu))
    (hP.intervalIntegrable_clm_comp hc hs hr), hXs, add_sub_cancel]

/-- **Constant coefficients.** For a constant coefficient `A`,
`N_P(t, s) = exp ((t - s) A)`. -/
@[simp]
theorem propagator_const (A : E →L[𝕜] E) (t s : ℝ) :
    propagator (fun _ ↦ A) t s = NormedSpace.exp (((t - s : ℝ) : 𝕜) • A) := by
  refine propagator_eq_of_hasDerivAt (a := min s t) (b := max s t)
    (X := fun r ↦ NormedSpace.exp (((r - s : ℝ) : 𝕜) • A))
    continuousOn_const.integrableOn_Icc ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨min_le_right _ _, le_max_right _ _⟩ (fun r _ ↦ ?_) (by simp)
  have hg : HasDerivAt (fun r : ℝ ↦ ((r - s : ℝ) : 𝕜)) 1 r :=
    ((RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).sub_const s)).congr_deriv (by simp)
  have h := ((hasDerivAt_exp_smul_const' (𝕂 := 𝕜) A ((r - s : ℝ) : 𝕜)).hasFDerivAt.restrictScalars
    ℝ).comp_hasDerivAt r hg
  simpa [Function.comp_def, ContinuousLinearMap.mul_def] using h

/-- **Constant coefficients squaring to a positive scalar.** If `A² = a²` with `a ≠ 0` real,
then `N_P(t, s) = cosh((t - s) a) + (sinh((t - s) a) / a) A` for the constant coefficient `A`. -/
theorem propagator_const_eq_cosh_add_sinh {A : E →L[𝕜] E} {a : ℝ} (ha : a ≠ 0)
    (hA : A * A = (a : 𝕜) ^ 2 • 1) (t s : ℝ) :
    propagator (fun _ ↦ A) t s =
      (Real.cosh ((t - s) * a) : 𝕜) • 1 + (Real.sinh ((t - s) * a) / a : 𝕜) • A := by
  refine propagator_eq_of_hasDerivAt (a := min s t) (b := max s t)
    (X := fun r ↦ (Real.cosh ((r - s) * a) : 𝕜) • 1 + (Real.sinh ((r - s) * a) / a : 𝕜) • A)
    continuousOn_const.integrableOn_Icc ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨min_le_right _ _, le_max_right _ _⟩ (fun r _ ↦ ?_) (by simp)
  -- `X' = a sinh((r - s) a) + cosh((r - s) a) A = A X`, since `A² = a²`.
  have ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u r) :
      HasDerivAt (fun y ↦ (f y : 𝕜)) (u : 𝕜) r := by
    simpa [Function.comp_def] using!
      (RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt r hf
  have hlin : HasDerivAt (fun r : ℝ ↦ (r - s) * a) a r := by
    simpa using ((hasDerivAt_id r).sub_const s).mul_const a
  have hc : HasDerivAt (fun r : ℝ ↦ (Real.cosh ((r - s) * a) : 𝕜))
      (Real.sinh ((r - s) * a) * a : 𝕜) r := by
    simpa using ofReal_comp hlin.cosh
  have hs : HasDerivAt (fun r : ℝ ↦ (Real.sinh ((r - s) * a) / a : 𝕜))
      (Real.cosh ((r - s) * a) : 𝕜) r := by
    simpa [ha] using ofReal_comp (hlin.sinh.div_const a)
  refine ((hc.smul_const _).add (hs.smul_const _)).congr_deriv ?_
  simp only [← ContinuousLinearMap.mul_def, mul_add, mul_smul_comm, mul_one, hA, smul_smul]
  match_scalars <;> field_simp

/-- **The norm bound on `N_P(t, s) - 1`.**
`‖N_P(t, s) - 1‖ ≤ exp |∫ u in s..t, ‖P u‖| - 1` for `s, t ∈ [a, b]`. -/
theorem norm_propagator_sub_one_le (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : ‖propagator P t s - 1‖ ≤ exp |∫ u in s..t, ‖P u‖| - 1 := by
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  have hPi : IntervalIntegrable (fun u ↦ ‖P u‖) volume s t :=
    IntegrableOn.intervalIntegrable (hP.mono_set hsub).norm
  have hg : IntervalIntegrable (fun u ↦ ‖P u‖ * exp |∫ v in s..u, ‖P v‖|) volume s t :=
    hPi.mul_continuousOn
      (continuousOn_primitive_interval (hP.mono_set hsub).norm).abs.rexp
  rw [propagator_eq_one_add_integral hP hs ht, add_sub_cancel_left,
    ← hPi.abs_integral_mul_exp_abs_integral]
  refine norm_integral_le_abs_of_norm_le ((ae_restrict_mem measurableSet_uIoc).mono
    fun u hu ↦ ?_) hg
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
    (norm_propagator_le hP hs (hsub (uIoc_subset_uIcc hu))) (norm_nonneg _))

/-- The propagator `N_P(t, s)` is absolutely continuous in `t` on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_propagator_left (hP : IntegrableOn P (Icc a b))
    (hs : s ∈ Icc a b) : AbsolutelyContinuousOnInterval (fun t ↦ propagator P t s) a b := by
  have hM := integrableOn_mul hP
  exact absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard
    (M := fun u ↦ ContinuousLinearMap.mul ℝ _ (P u)) (F := fun _ ↦ (0 : E →L[𝕜] E)) (x₀ := 1) hs
    hM integrableOn_zero (continuousOn_propagator_left hP hs) fun r hr ↦
      (propagator_eq_one_add_integral hP hs hr).trans (picard_mul P _ s r).symm

/-- **The derivative in the final time.** `t ↦ N_P(t, s)` has derivative `P(t) N_P(t, s)` at
almost every `t ∈ (a, b)`. -/
theorem ae_hasDerivAt_propagator_left (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt (fun t ↦ propagator P t s) (P t ∘L propagator P t s) t := by
  have hM := integrableOn_mul hP
  filter_upwards [ae_hasDerivAt_of_forall_mem_Icc_eq_picard
    (M := fun u ↦ ContinuousLinearMap.mul ℝ _ (P u)) (F := fun _ ↦ (0 : E →L[𝕜] E)) (x₀ := 1) hs
    hM integrableOn_zero (continuousOn_propagator_left hP hs) fun r hr ↦
      (propagator_eq_one_add_integral hP hs hr).trans (picard_mul P _ s r).symm] with t hd ht
  simpa [ContinuousLinearMap.mul_def] using hd ht

/-- **The derivative in the initial time.** `s ↦ N_P(t, s)` has derivative `-N_P(t, s) P(s)` at
almost every `s ∈ (a, b)`. -/
theorem ae_hasDerivAt_propagator_right (hP : IntegrableOn P (Icc a b)) (ht : t ∈ Icc a b) :
    ∀ᵐ s, s ∈ Ioo a b → HasDerivAt (fun s ↦ propagator P t s) (-(propagator P t s ∘L P s)) s := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  filter_upwards [ae_hasDerivAt_propagator_left hP ha] with s hds hs
  have hs' : s ∈ Icc a b := Ioo_subset_Icc_self hs
  replace hds := hds hs
  -- Differentiate `N_P(t, a) N_P(s, a)⁻¹`; the coercion of `propagatorUnit hP ha hs'` is
  -- `propagator P s a` by construction.
  have h := (((ContinuousLinearMap.compL 𝕜 E E E (propagator P t a)).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt s <| ((hasFDerivAt_ringInverse (𝕜 := 𝕜)
      (propagatorUnit hP ha hs')).restrictScalars ℝ).comp_hasDerivAt s hds)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · have h₁ : propagator P s a * propagator P a s = 1 := propagator_comp_propagator_swap hP hs' ha
    have h₂ : propagator P t a * propagator P a s = propagator P t s :=
      propagator_comp_propagator hP ha hs' ht
    simp only [ContinuousLinearMap.coe_restrictScalars', neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.compL_apply,
      coe_inv_propagatorUnit, ← ContinuousLinearMap.mul_def]
    rw [show propagator P t a * -(propagator P a s * (P s * propagator P s a) * propagator P a s) =
      -(propagator P t a * propagator P a s * P s * (propagator P s a * propagator P a s)) by
        noncomm_ring, h₁, h₂, mul_one]
  · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.compL_apply]
    rw [ringInverse_propagator hP ha (Ioo_subset_Icc_self hr),
      propagator_comp_propagator hP ha (Ioo_subset_Icc_self hr) ht]

/-- The difference `D(r) = N_{P'}(r, s) - N_P(r, s)` of two propagators solves
`D(r) = ∫ u in s..r, (P u ∘L D u + (P' u - P u) ∘L N_{P'}(u, s))` on `[a, b]`. -/
private theorem propagator_sub_propagator_eq_picard {P' : ℝ → E →L[𝕜] E}
    (hP : IntegrableOn P (Icc a b)) (hP' : IntegrableOn P' (Icc a b)) (hs : s ∈ Icc a b) :
    ∀ r ∈ Icc a b, propagator P' r s - propagator P r s =
      ODE.picard (fun u Y ↦ ContinuousLinearMap.mul ℝ (E →L[𝕜] E) (P u) Y +
        (P' u - P u) ∘L propagator P' u s) s 0
        (fun u ↦ propagator P' u s - propagator P u s) r := by
  have hN' := continuousOn_propagator_left hP' hs
  have hN := continuousOn_propagator_left hP hs
  intro r hr
  have h₁ := hP'.intervalIntegrable_clm_comp hN' hs hr
  have h₂ := hP.intervalIntegrable_clm_comp hN hs hr
  rw [ODE.picard_apply, propagator_eq_one_add_integral hP' hs hr,
    propagator_eq_one_add_integral hP hs hr, add_sub_add_left_eq_sub, zero_add,
    ← intervalIntegral.integral_sub h₁ h₂]
  refine integral_congr fun u _ ↦ ?_
  simp only [ContinuousLinearMap.mul_apply', ← ContinuousLinearMap.mul_def]
  noncomm_ring

/-- **Continuous dependence on the coefficient.** For `P` and `P'` integrable on `[a, b]` and
`s, t ∈ [a, b]`,
`‖N_{P'}(t, s) - N_P(t, s)‖ ≤ ‖P' - P‖₁ exp (‖P'‖₁ + ‖P‖₁)`, all `L¹` norms over the interval
between `s` and `t`. -/
theorem norm_propagator_sub_propagator_le {P' : ℝ → E →L[𝕜] E} (hP : IntegrableOn P (Icc a b))
    (hP' : IntegrableOn P' (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖propagator P' t s - propagator P t s‖ ≤
      |∫ u in s..t, ‖P' u - P u‖| * exp (|∫ u in s..t, ‖P' u‖| + |∫ u in s..t, ‖P u‖|) := by
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  set A' := |∫ u in s..t, ‖P' u‖|
  have hN' := continuousOn_propagator_left hP' hs
  have hN := continuousOn_propagator_left hP hs
  -- The inhomogeneous term `(P' - P) N_{P'}` and its pointwise bound.
  have hF : IntegrableOn (fun u ↦ (P' u - P u) ∘L propagator P' u s) (Icc a b) := by
    simpa [ContinuousLinearMap.mul_def] using (hP'.sub hP).mul_continuousOn hN' isCompact_Icc
  -- Apply the a priori bound to the integral equation of `N_{P'}(·, s) - N_P(·, s)`.
  have hD := propagator_sub_propagator_eq_picard hP hP' hs
  have key := norm_le_mul_exp_of_forall_mem_Icc_eq_picard hs (integrableOn_mul hP) hF
    (hN'.sub hN) hD ht
  have hPi : IntervalIntegrable (fun u ↦ ‖P u‖) volume s t :=
    IntegrableOn.intervalIntegrable (hP.mono_set hsub).norm
  have hdi : IntervalIntegrable (fun u ↦ ‖P' u - P u‖ * exp A') volume s t :=
    (IntegrableOn.intervalIntegrable ((hP'.sub hP).mono_set hsub).norm).mul_const _
  -- `‖N_{P'}(u, s)‖ ≤ exp ‖P'‖₁` for `u` between `s` and `t`.
  have hFle : |∫ u in s..t, ‖(P' u - P u) ∘L propagator P' u s‖| ≤
      |∫ u in s..t, ‖P' u - P u‖ * exp A'| := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_abs_of_norm_le ((ae_restrict_mem measurableSet_uIoc).mono
      fun u hu ↦ ?_) hdi
    have hu : u ∈ uIcc s t := uIoc_subset_uIcc hu
    rw [norm_norm]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
      ((norm_propagator_le hP' hs (hsub hu)).trans (exp_le_exp.2 ?_)) (norm_nonneg _))
    exact abs_integral_mono_interval (uIoc_subset_uIoc_of_uIcc_subset_uIcc
      (uIcc_subset_uIcc left_mem_uIcc hu)) (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (IntegrableOn.intervalIntegrable (hP'.mono_set hsub).norm)
  have hMle : |∫ u in s..t, ‖ContinuousLinearMap.mul ℝ (E →L[𝕜] E) (P u)‖| ≤
      |∫ u in s..t, ‖P u‖| := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_abs_of_norm_le (Filter.Eventually.of_forall fun u ↦ by
      rw [norm_norm]; exact ContinuousLinearMap.opNorm_mul_apply_le _ _ _) hPi
  rw [norm_zero, zero_add] at key
  refine key.trans ?_
  rw [intervalIntegral.integral_mul_const, abs_mul, abs_of_pos (exp_pos _)] at hFle
  rw [exp_add, ← mul_assoc]
  exact mul_le_mul hFle (exp_le_exp.2 hMle) (exp_pos _).le
    (mul_nonneg (abs_nonneg _) (exp_pos _).le)

/-- **Convergence of propagators under `L¹` convergence of coefficients.** If `P_n → P` in
`L¹([a, b])`, then `N_{P_n} → N_P` uniformly on `[a, b]²` in the operator norm. -/
theorem tendstoUniformlyOn_propagator {ι : Type*} {l : Filter ι} {Q : ι → ℝ → E →L[𝕜] E}
    (hP : IntegrableOn P (Icc a b)) (hQ : ∀ᶠ n in l, IntegrableOn (Q n) (Icc a b))
    (hlim : Filter.Tendsto (fun n ↦ ∫ u in a..b, ‖Q n u - P u‖) l (nhds 0)) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) ↦ propagator (Q n) p.1 p.2)
      (fun p ↦ propagator P p.1 p.2) l (Icc a b ×ˢ Icc a b) := by
  set I := ∫ u in a..b, ‖P u‖
  -- The bound `‖N_{Q n} - N_P‖ ≤ δ (exp (δ + 2 I))`, with `δ` the `L¹` distance, tends to `0`.
  have hg : Filter.Tendsto (fun n ↦ (∫ u in a..b, ‖Q n u - P u‖) *
      exp ((∫ u in a..b, ‖Q n u - P u‖) + I + I)) l (nhds 0) := by
    simpa using hlim.mul (((hlim.add_const I).add_const I).rexp)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hQ, hg.eventually (gt_mem_nhds hε)] with n hQn hn p hp
  have hab : a ≤ b := hp.1.1.trans hp.1.2
  have hn₀ : 0 ≤ ∫ u in a..b, ‖Q n u - P u‖ := integral_nonneg hab fun _ _ ↦ norm_nonneg _
  -- `L¹` norms over the interval between `p.2` and `p.1` are at most those over `[a, b]`.
  have hle {R : ℝ → E →L[𝕜] E} (hR : IntegrableOn R (Icc a b)) :
      |∫ u in p.2..p.1, ‖R u‖| ≤ ∫ u in a..b, ‖R u‖ := by
    simpa [integral_of_le hab, integral_Ioc_eq_integral_Ioo] using
      intervalIntegral.norm_integral_le_setIntegral_norm (f := fun u ↦ ‖R u‖)
        ((hR.mono_set Ioo_subset_Icc_self).norm) hp.2 hp.1
  have hd := hle (hQn.sub hP)
  have hI := hle hP
  have hsub : uIcc p.2 p.1 ⊆ Icc a b := uIcc_subset_Icc hp.2 hp.1
  have hQI : |∫ u in p.2..p.1, ‖Q n u‖| ≤ (∫ u in a..b, ‖Q n u - P u‖) + I := by
    have hi₁ := IntegrableOn.intervalIntegrable ((hQn.sub hP).mono_set hsub).norm
    have hi₂ := IntegrableOn.intervalIntegrable (hP.mono_set hsub).norm
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_abs_of_norm_le (Filter.Eventually.of_forall fun u ↦ ?_)
      (hi₁.add hi₂)).trans ?_
    · rw [norm_norm]
      exact norm_le_insert' _ _ |>.trans_eq (add_comm _ _)
    · rw [intervalIntegral.integral_add hi₁ hi₂]
      exact (abs_add_le _ _).trans (add_le_add hd hI)
  rw [dist_eq_norm, norm_sub_rev]
  refine ((norm_propagator_sub_propagator_le hP hQn hp.2 hp.1).trans ?_).trans_lt hn
  exact mul_le_mul hd (exp_le_exp.2 (add_le_add hQI hI)) (exp_pos _).le hn₀

end TauCeti
