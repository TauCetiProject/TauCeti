/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Caratheodory
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

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
  `N_P(s, t)` (`TauCeti.isUnit_propagator`).
* `TauCeti.norm_propagator_le`, `TauCeti.norm_propagator_sub_one_le`:
  `‖N_P(t, s)‖ ≤ exp |∫ r in s..t, ‖P r‖|` and `‖N_P(t, s) - 1‖ ≤ exp |∫ r in s..t, ‖P r‖| - 1`.
* `TauCeti.continuousOn_propagator`: `(t, s) ↦ N_P(t, s)` is continuous on `[a, b]²` in the
  operator norm.
* `TauCeti.ae_hasDerivAt_propagator_right`: `s ↦ N_P(t, s)` has derivative `-N_P(t, s) P(s)` at
  almost every `s`.
* `TauCeti.propagator_congr_ae`: the propagator depends only on `P` almost everywhere on the
  interval between `s` and `t`.
* `TauCeti.propagator_const`: for a constant coefficient `A`, `N_P(t, s) = exp ((t - s) • A)`.

## Implementation notes

Existence and uniqueness for the operator equation are the linear Carathéodory theorem in the
Banach space `E →L[𝕜] E`, with the real-linear coefficient `X ↦ P r ∘L X`. The scalars `𝕜` enter
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
`N r = 1 + ∫ u in s..r, P u ∘L N u`. When `P` is integrable on that interval the solution exists
and is unique (`TauCeti.propagator_eq_of_forall_mem_Icc`); otherwise the value is unspecified. -/
noncomputable def propagator (P : ℝ → E →L[𝕜] E) (t s : ℝ) : E →L[𝕜] E :=
  if h : ∃ N : ℝ → E →L[𝕜] E, ContinuousOn N (uIcc s t) ∧
      ∀ r ∈ uIcc s t, N r = 1 + ∫ u in s..r, P u ∘L N u then h.choose t else 1

namespace Propagator

/-- Left composition `A ↦ (X ↦ A ∘L X)`, as a real-linear map. -/
private noncomputable def compLeft : (E →L[𝕜] E) →L[ℝ] (E →L[𝕜] E) →L[ℝ] E →L[𝕜] E :=
  (ContinuousLinearMap.restrictScalarsL 𝕜 (E →L[𝕜] E) (E →L[𝕜] E) ℝ ℝ).comp
    ((ContinuousLinearMap.compL 𝕜 E E E).restrictScalars ℝ)

private theorem compLeft_apply (A X : E →L[𝕜] E) : compLeft A X = A ∘L X := rfl

private theorem picard_compLeft (P : ℝ → E →L[𝕜] E) (N : ℝ → E →L[𝕜] E) (s r : ℝ) :
    ODE.picard (fun u Y ↦ compLeft (P u) Y + (fun _ ↦ (0 : E →L[𝕜] E)) u) s 1 N r =
      1 + ∫ u in s..r, P u ∘L N u := by
  simp [ODE.picard_apply, compLeft_apply]

private theorem picard_restrictScalars (P : ℝ → E →L[𝕜] E) (x : ℝ → E) (y : E) (s r : ℝ) :
    ODE.picard (fun u z ↦ (P u).restrictScalars ℝ z + (fun _ ↦ (0 : E)) u) s y x r =
      y + ∫ u in s..r, P u (x u) := by
  simp [ODE.picard_apply]

variable {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

private theorem integrableOn_restrictScalars {S : Set ℝ} (hP : IntegrableOn P S) :
    IntegrableOn (fun u ↦ (P u).restrictScalars ℝ) S :=
  (ContinuousLinearMap.restrictScalarsL 𝕜 E E ℝ ℝ).integrable_comp hP

private theorem exists_sol [CompleteSpace E] (hP : IntegrableOn P (Icc a b))
    (hs : s ∈ Icc a b) :
    ∃ N : ℝ → E →L[𝕜] E, ContinuousOn N (Icc a b) ∧
      ∀ r ∈ Icc a b, N r = 1 + ∫ u in s..r, P u ∘L N u := by
  obtain ⟨N, hN, h⟩ := exists_continuousOn_forall_mem_Icc_eq_picard hs
    (ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ) (H := E →L[𝕜] E)
      (E := (E →L[𝕜] E) →L[ℝ] E →L[𝕜] E) compLeft hP) integrableOn_zero 1
  exact ⟨N, hN, fun r hr ↦ (h r hr).trans (picard_compLeft P N s r)⟩

private theorem eqOn_sol (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    {N₁ N₂ : ℝ → E →L[𝕜] E} (hN₁ : ContinuousOn N₁ (Icc a b)) (hN₂ : ContinuousOn N₂ (Icc a b))
    (h₁ : ∀ r ∈ Icc a b, N₁ r = 1 + ∫ u in s..r, P u ∘L N₁ u)
    (h₂ : ∀ r ∈ Icc a b, N₂ r = 1 + ∫ u in s..r, P u ∘L N₂ u) :
    EqOn N₁ N₂ (Icc a b) := by
  have hM := ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ)
    (H := E →L[𝕜] E) (E := (E →L[𝕜] E) →L[ℝ] E →L[𝕜] E) compLeft hP
  exact eqOn_of_forall_mem_Icc_eq_picard (M := fun u ↦ compLeft (P u))
    (F := fun _ ↦ (0 : E →L[𝕜] E)) (x₀ := 1) hs hM integrableOn_zero hN₁ hN₂
    (fun r hr ↦ (h₁ r hr).trans (picard_compLeft P N₁ s r).symm)
    (fun r hr ↦ (h₂ r hr).trans (picard_compLeft P N₂ s r).symm)

private theorem intervalIntegrable_comp (hP : IntegrableOn P (Icc a b)) (hab : a ≤ b)
    {N : ℝ → E →L[𝕜] E} (hN : ContinuousOn N (Icc a b)) :
    IntervalIntegrable (fun u ↦ P u ∘L N u) volume a b := by
  have hM := ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ)
    (H := E →L[𝕜] E) (E := (E →L[𝕜] E) →L[ℝ] E →L[𝕜] E) compLeft hP
  simpa [compLeft_apply] using intervalIntegrable_clm_apply_add (M := fun u ↦ compLeft (P u))
    (F := fun _ ↦ (0 : E →L[𝕜] E)) hab hM integrableOn_zero hN

private theorem intervalIntegrable_apply (hP : IntegrableOn P (Icc a b)) (hab : a ≤ b)
    {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntervalIntegrable (fun u ↦ P u (x u)) volume a b := by
  simpa using intervalIntegrable_clm_apply_add (M := fun u ↦ (P u).restrictScalars ℝ)
    (F := fun _ ↦ (0 : E)) hab (integrableOn_restrictScalars hP) integrableOn_zero hx

/-- A solution of an integral equation from `s` also solves it from any other time `r`. -/
private theorem eq_add_integral_of_mem {f x : ℝ → E} {c : E} {r : ℝ}
    (hf : IntervalIntegrable f volume a b) (h : ∀ u ∈ Icc a b, x u = c + ∫ v in s..u, f v)
    (hs : s ∈ Icc a b) (hr : r ∈ Icc a b) (ht : t ∈ Icc a b) :
    x t = x r + ∫ v in r..t, f v := by
  rw [h t ht, h r hr, add_assoc, integral_add_adjacent_intervals
    (hf.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hs) (Icc_subset_uIcc hr)))
    (hf.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hr) (Icc_subset_uIcc ht)))]

/-- For `g ≥ 0` integrable between `s` and `t`, with primitive `G u = ∫ v in s..u, g v`,
`|∫ u in s..t, g u * exp |G u|| = exp |G t| - 1`, whatever the order of `s` and `t`. -/
private theorem abs_integral_mul_exp_abs_integral {g : ℝ → ℝ} {s t : ℝ}
    (hg : IntervalIntegrable g volume s t) (hg₀ : ∀ u, 0 ≤ g u) :
    |∫ u in s..t, g u * exp (|∫ v in s..u, g v|)| = exp |∫ v in s..t, g v| - 1 := by
  set G : ℝ → ℝ := fun u ↦ ∫ v in s..u, g v
  -- `G` has a constant sign `σ` between `s` and `t`.
  obtain ⟨σ, hσ, hG⟩ : ∃ σ : ℝ, σ * σ = 1 ∧ ∀ u ∈ uIcc s t, |G u| = σ * G u := by
    rcases le_total s t with h | h
    · refine ⟨1, one_mul 1, fun u hu ↦ ?_⟩
      rw [uIcc_of_le h] at hu
      rw [one_mul, abs_of_nonneg (integral_nonneg hu.1 fun v _ ↦ hg₀ v)]
    · refine ⟨-1, by norm_num, fun u hu ↦ ?_⟩
      rw [uIcc_of_ge h] at hu
      rw [neg_one_mul, abs_of_nonpos]
      simp only [G]
      rw [integral_symm, neg_nonpos]
      exact integral_nonneg hu.2 fun v _ ↦ hg₀ v
  have hφ : AbsolutelyContinuousOnInterval (fun u ↦ exp (σ * G u)) s t :=
    (hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).comp_of_contDiffAt
      (φ := fun x : ℝ ↦ exp (σ * x)) fun _ _ ↦ (contDiff_const.mul contDiff_id).exp.contDiffAt
  have hderiv : ∀ᵐ u, u ∈ uIoc s t →
      deriv (fun u ↦ exp (σ * G u)) u = σ * (g u * exp (σ * G u)) := by
    filter_upwards [hg.ae_hasDerivAt_integral] with u hu huI
    rw [(((hu (uIoc_subset_uIcc huI) s left_mem_uIcc).const_mul σ).exp).deriv]
    ring
  have h := hφ.integral_deriv_eq_sub
  rw [integral_congr_ae hderiv, intervalIntegral.integral_const_mul] at h
  have h' : ∫ u in s..t, g u * exp |G u| = σ * (exp (σ * G t) - 1) := by
    have hGs : G s = 0 := integral_same
    rw [hGs, mul_zero, exp_zero] at h
    rw [integral_congr (g := fun u ↦ g u * exp (σ * G u)) fun u hu ↦ by simp only [hG u hu]]
    linear_combination σ * h - (∫ u in s..t, g u * exp (σ * G u)) * hσ
  rw [h', ← hG t right_mem_uIcc, abs_mul, show |σ| = 1 by
    nlinarith [abs_mul_abs_self σ, abs_nonneg σ], one_mul,
    abs_of_nonneg (sub_nonneg.2 (one_le_exp (abs_nonneg _)))]

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
    (intervalIntegrable_comp hP (hs.1.trans hs.2) (continuousOn_propagator_left hP hs)).mono_set
      (uIcc_subset_uIcc (Icc_subset_uIcc hs) (Icc_subset_uIcc ht))
  conv_lhs => rw [propagator_eq_one_add_integral hP hs ht]
  rw [add_apply, one_apply_eq_self,
    ContinuousLinearMap.intervalIntegral_apply hI]
  rfl

/-- **Solutions are given by the propagator.** A curve `x` continuous on `[a, b]` with
`x r = x s + ∫ u in s..r, P u (x u)` for `r ∈ [a, b]` satisfies `x t = N_P(t, s) (x s)`. -/
theorem eq_propagator_apply (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ r ∈ Icc a b, x r = x s + ∫ u in s..r, P u (x u)) : x t = propagator P t s (x s) :=
  eqOn_of_forall_mem_Icc_eq_picard (M := fun u ↦ (P u).restrictScalars ℝ)
    (F := fun _ ↦ (0 : E)) (x₀ := x s) hs (integrableOn_restrictScalars hP) integrableOn_zero hx
    ((continuousOn_propagator_left hP hs).clm_apply continuousOn_const)
    (fun r hr ↦ (h r hr).trans (picard_restrictScalars P x _ s r).symm)
    (fun r hr ↦ (propagator_apply_eq_add_integral hP hs hr _).trans
      (picard_restrictScalars P _ _ s r).symm) ht

/-- **The cocycle identity.** `N_P(t, r) N_P(r, s) = N_P(t, s)` for `r, s, t ∈ [a, b]`. -/
theorem propagator_comp_propagator (hP : IntegrableOn P (Icc a b)) (hr : r ∈ Icc a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    propagator P t r ∘L propagator P r s = propagator P t s := by
  ext y
  set x : ℝ → E := fun u ↦ propagator P u s y
  have hx : ContinuousOn x (Icc a b) :=
    (continuousOn_propagator_left hP hs).clm_apply continuousOn_const
  have h (u : ℝ) (hu : u ∈ Icc a b) : x u = x r + ∫ v in r..u, P v (x v) :=
    eq_add_integral_of_mem (intervalIntegrable_apply hP (hs.1.trans hs.2) hx)
      (fun v hv ↦ propagator_apply_eq_add_integral hP hs hv y) hs hr hu
  exact (eq_propagator_apply hP hr ht hx h).symm

/-- `N_P(s, t)` is a left inverse of `N_P(t, s)`. -/
theorem propagator_comp_propagator_swap (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : propagator P s t ∘L propagator P t s = 1 := by
  rw [propagator_comp_propagator hP ht hs hs, propagator_self]

/-- The propagator `N_P(t, s)` is invertible, with inverse `N_P(s, t)`. -/
theorem isUnit_propagator (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : IsUnit (propagator P t s) :=
  isUnit_iff_exists.2 ⟨propagator P s t, propagator_comp_propagator_swap hP ht hs,
    propagator_comp_propagator_swap hP hs ht⟩

/-- **The norm bound.** `‖N_P(t, s)‖ ≤ exp |∫ u in s..t, ‖P u‖|` for `s, t ∈ [a, b]`. -/
theorem norm_propagator_le (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : ‖propagator P t s‖ ≤ exp |∫ u in s..t, ‖P u‖| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (exp_pos _).le fun y ↦ ?_
  have := norm_le_mul_exp_of_forall_mem_Icc_eq_picard (M := fun u ↦ (P u).restrictScalars ℝ)
    (F := fun _ ↦ (0 : E)) (x₀ := y) hs (integrableOn_restrictScalars hP) integrableOn_zero
    ((continuousOn_propagator_left hP hs).clm_apply continuousOn_const)
    (fun r hr ↦ (propagator_apply_eq_add_integral hP hs hr y).trans
      (picard_restrictScalars P _ y s r).symm) ht
  simpa [mul_comm] using this

/-- The propagator `N_P(t, s)` as a unit, with inverse `N_P(s, t)`. -/
private noncomputable def propagatorUnit (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : (E →L[𝕜] E)ˣ :=
  ⟨propagator P t s, propagator P s t, propagator_comp_propagator_swap hP ht hs,
    propagator_comp_propagator_swap hP hs ht⟩

private theorem ring_inverse_propagator (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : Ring.inverse (propagator P t s) = propagator P s t :=
  Ring.inverse_unit (propagatorUnit hP hs ht)

/-- The propagator `N_P(t, s)` is continuous in `s ∈ [a, b]` in the operator norm: on `[a, b]`,
`N_P(t, s) = N_P(t, a) N_P(s, a)⁻¹`, and inversion is continuous on the units. -/
theorem continuousOn_propagator_right (hP : IntegrableOn P (Icc a b)) (ht : t ∈ Icc a b) :
    ContinuousOn (fun s ↦ propagator P t s) (Icc a b) := by
  intro s₀ hs₀
  have ha : a ∈ Icc a b := ⟨le_rfl, hs₀.1.trans hs₀.2⟩
  have hinv : ContinuousWithinAt (fun s ↦ Ring.inverse (propagator P s a)) (Icc a b) s₀ :=
    ContinuousAt.comp_continuousWithinAt (g := Ring.inverse) (f := fun s ↦ propagator P s a)
      (NormedRing.inverse_continuousAt (propagatorUnit hP ha hs₀))
      (continuousOn_propagator_left hP ha s₀ hs₀)
  have heq {s : ℝ} (hs : s ∈ Icc a b) :
      propagator P t s = propagator P t a ∘L Ring.inverse (propagator P s a) := by
    rw [ring_inverse_propagator hP ha hs, propagator_comp_propagator hP ha hs ht]
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
  have hI := intervalIntegrable_comp hP (hs.1.trans hs.2) hc
  refine propagator_eq_of_forall_mem_Icc hP hs ht hc fun r hr ↦ ?_
  have hsub := uIcc_subset_uIcc (Icc_subset_uIcc hs) (Icc_subset_uIcc hr)
  rw [integral_eq_sub_of_hasDerivAt (fun u hu ↦ hX u (uIcc_subset_Icc hs hr hu))
    (hI.mono_set hsub), hXs, add_sub_cancel]

/-- **Constant coefficients.** For a constant coefficient `A`,
`N_P(t, s) = exp ((t - s) A)`. -/
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

/-- **The norm bound on `N_P(t, s) - 1`.**
`‖N_P(t, s) - 1‖ ≤ exp |∫ u in s..t, ‖P u‖| - 1` for `s, t ∈ [a, b]`. -/
theorem norm_propagator_sub_one_le (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : ‖propagator P t s - 1‖ ≤ exp |∫ u in s..t, ‖P u‖| - 1 := by
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  have hPi : IntervalIntegrable (fun u ↦ ‖P u‖) volume s t :=
    IntegrableOn.intervalIntegrable (hP.mono_set hsub).norm
  have hf : IntervalIntegrable (fun u ↦ ‖P u ∘L propagator P u s‖) volume s t :=
    ((intervalIntegrable_comp hP (hs.1.trans hs.2) (continuousOn_propagator_left hP hs)).mono_set
      (uIcc_subset_uIcc (Icc_subset_uIcc hs) (Icc_subset_uIcc ht))).norm
  have hg : IntervalIntegrable (fun u ↦ ‖P u‖ * exp |∫ v in s..u, ‖P v‖|) volume s t :=
    hPi.mul_continuousOn
      (continuousOn_primitive_interval (hP.mono_set hsub).norm).abs.rexp
  rw [propagator_eq_one_add_integral hP hs ht, add_sub_cancel_left,
    ← abs_integral_mul_exp_abs_integral hPi fun _ ↦ norm_nonneg _]
  refine norm_integral_le_abs_integral_norm.trans ?_
  rw [abs_integral_eq_abs_integral_uIoc, abs_integral_eq_abs_integral_uIoc,
    abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun _ _ ↦ norm_nonneg _),
    abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun _ _ ↦
      mul_nonneg (norm_nonneg _) (exp_pos _).le)]
  refine setIntegral_mono_on hf.def' hg.def' measurableSet_uIoc fun u hu ↦ ?_
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
    (norm_propagator_le hP hs (hsub (uIoc_subset_uIcc hu))) (norm_nonneg _))

/-- **The derivative in the initial time.** `s ↦ N_P(t, s)` has derivative `-N_P(t, s) P(s)` at
almost every `s ∈ (a, b)`. -/
theorem ae_hasDerivAt_propagator_right (hP : IntegrableOn P (Icc a b)) (ht : t ∈ Icc a b) :
    ∀ᵐ s, s ∈ Ioo a b → HasDerivAt (fun s ↦ propagator P t s) (-(propagator P t s ∘L P s)) s := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hM := ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ)
    (H := E →L[𝕜] E) (E := (E →L[𝕜] E) →L[ℝ] E →L[𝕜] E) compLeft hP
  have hd := ae_hasDerivAt_of_forall_mem_Icc_eq_picard (M := fun u ↦ compLeft (P u))
    (F := fun _ ↦ (0 : E →L[𝕜] E)) (x₀ := 1) ha hM integrableOn_zero
    (continuousOn_propagator_left hP ha) fun r hr ↦
      (propagator_eq_one_add_integral hP ha hr).trans (picard_compLeft P _ a r).symm
  filter_upwards [hd] with s hds hs
  have hs' : s ∈ Icc a b := Ioo_subset_Icc_self hs
  have hds : HasDerivAt (fun r ↦ propagator P r a) (P s ∘L propagator P s a) s := by
    simpa [compLeft_apply] using hds hs
  -- Differentiate `N_P(t, a) N_P(s, a)⁻¹`.
  have h := (((ContinuousLinearMap.compL 𝕜 E E E (propagator P t a)).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt s <| ((hasFDerivAt_ringInverse (𝕜 := 𝕜)
      (propagatorUnit hP ha hs')).restrictScalars ℝ).comp_hasDerivAt s hds)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · have h₁ : propagator P s a * propagator P a s = 1 := propagator_comp_propagator_swap hP hs' ha
    have h₂ : propagator P t a * propagator P a s = propagator P t s :=
      propagator_comp_propagator hP ha hs' ht
    simp only [ContinuousLinearMap.coe_restrictScalars', neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.compL_apply,
      ← ContinuousLinearMap.mul_def]
    change propagator P t a * -(propagator P a s * (P s * propagator P s a) * propagator P a s) = _
    rw [show propagator P t a * -(propagator P a s * (P s * propagator P s a) * propagator P a s) =
      -(propagator P t a * propagator P a s * P s * (propagator P s a * propagator P a s)) by
        noncomm_ring, h₁, h₂, mul_one]
  · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.compL_apply]
    rw [ring_inverse_propagator hP ha (Ioo_subset_Icc_self hr),
      propagator_comp_propagator hP ha (Ioo_subset_Icc_self hr) ht]

end TauCeti
