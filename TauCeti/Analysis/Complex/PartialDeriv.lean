/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Partial derivatives of entire functions on `ℂⁿ`

This file defines the partial derivative `∂ᵢ f (z) = Df(z) eᵢ` (`TauCeti.partialDeriv`) of a
function `f : ℂⁿ → ℂ` in the direction of the `i`-th coordinate vector, and develops its calculus
on entire functions.

## Main results

* `TauCeti.partialDeriv_eq_deriv_update`: `∂ᵢ f (z)` is the derivative of `f` along the line
  through `z` parallel to the `i`-th coordinate axis.
* `TauCeti.differentiable_partialDeriv`: a partial derivative of an entire function is entire.
* `TauCeti.partialDeriv_comm`: partial derivatives of an entire function commute.
* `TauCeti.partialDeriv_add`, `TauCeti.partialDeriv_const_mul`: `∂ᵢ` is linear.
* `TauCeti.partialDeriv_prod`, `TauCeti.iterate_partialDeriv_prod`: for a separated product
  `z ↦ ∏ⱼ gⱼ(zⱼ)` of entire functions of one variable, `∂ᵢ^k` differentiates the `i`-th factor
  `k` times.
-/

public section

open Function

namespace TauCeti

variable {n : ℕ}

/-- The partial derivative `∂ᵢ f (z) = Df(z) eᵢ` of a function `f : ℂⁿ → ℂ` in the direction of
the `i`-th coordinate vector. -/
noncomputable def partialDeriv (i : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z ↦ fderiv ℂ f z (Pi.single i 1)

theorem partialDeriv_def (i : Fin n) (f : (Fin n → ℂ) → ℂ) :
    partialDeriv i f = fun z ↦ fderiv ℂ f z (Pi.single i 1) := (rfl)

theorem partialDeriv_apply (i : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    partialDeriv i f z = fderiv ℂ f z (Pi.single i 1) := (rfl)

/-- The partial derivative `∂ᵢ f (z)` is the derivative of `f` restricted to the line through `z`
parallel to the `i`-th coordinate axis. -/
theorem partialDeriv_eq_deriv_update {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : Fin n) :
    partialDeriv i f z = deriv (fun s ↦ f (update z i s)) (z i) := by
  have hf' : HasFDerivAt f (fderiv ℂ f z) (update z i (z i)) := by
    rw [update_eq_self]
    exact hf.hasFDerivAt
  have hline := (hf'.comp (z i) (hasFDerivAt_update z (i := i) (z i))).hasDerivAt
  refine (hline.deriv.trans ?_).symm
  simp only [partialDeriv_apply, ContinuousLinearMap.comp_apply]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- A partial derivative of the zero function is zero. -/
@[simp]
theorem partialDeriv_zero_fun (i : Fin n) : partialDeriv i (0 : (Fin n → ℂ) → ℂ) = 0 := by
  ext z
  simp [partialDeriv_apply, fderiv_zero]

variable {f g : (Fin n → ℂ) → ℂ}

/-- A partial derivative of an entire function is entire. -/
theorem differentiable_partialDeriv (hf : Differentiable ℂ f) (i : Fin n) :
    Differentiable ℂ (partialDeriv i f) :=
  hf.fderiv_of_finiteDimensional.clm_apply (differentiable_const _)

/-- **Partial derivatives of an entire function commute.** -/
theorem partialDeriv_comm (hf : Differentiable ℂ f) (i j : Fin n) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  have key (k l : Fin n) (z : Fin n → ℂ) : partialDeriv k (partialDeriv l f) z =
      fderiv ℂ (fderiv ℂ f) z (Pi.single k 1) (Pi.single l 1) := by
    rw [partialDeriv_apply, partialDeriv_def l f,
      fderiv_clm_apply (hf.fderiv_of_finiteDimensional z) (differentiableAt_const _)]
    simp
  ext z
  rw [key, key]
  exact (hf.contDiff_of_finiteDimensional (n := 2)).contDiffAt.isSymmSndFDerivAt (by simp) _ _

/-- `∂ᵢ` is additive on entire functions. -/
theorem partialDeriv_add (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (i : Fin n) :
    partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := by
  ext z
  simp [partialDeriv_apply, fderiv_add (hf z) (hg z)]

/-- `∂ᵢ` commutes with multiplication by a constant. -/
theorem partialDeriv_const_mul (c : ℂ) (i : Fin n) :
    partialDeriv i (fun z ↦ c * f z) = fun z ↦ c * partialDeriv i f z := by
  ext z
  simp_rw [← smul_eq_mul]
  rw [← Pi.smul_def, partialDeriv_apply, partialDeriv_apply, fderiv_const_smul_field]
  simp

/-! ### Iterated partial derivatives in one direction -/

/-- An iterated partial derivative of an entire function is entire. -/
theorem differentiable_iterate_partialDeriv (hf : Differentiable ℂ f) (i : Fin n) (k : ℕ) :
    Differentiable ℂ ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [iterate_succ_apply']; exact differentiable_partialDeriv ih i

/-- `∂ᵢ^k` commutes with `∂ⱼ` on entire functions. -/
theorem iterate_partialDeriv_comm (hf : Differentiable ℂ f) (i j : Fin n) (k : ℕ) :
    (partialDeriv i)^[k] (partialDeriv j f) = partialDeriv j ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_comm (differentiable_iterate_partialDeriv hf i k)]

/-- `∂ᵢ^k` is additive on entire functions. -/
theorem iterate_partialDeriv_add (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (i : Fin n)
    (k : ℕ) : (partialDeriv i)^[k] (f + g) = (partialDeriv i)^[k] f + (partialDeriv i)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_add (differentiable_iterate_partialDeriv hf i k)
        (differentiable_iterate_partialDeriv hg i k)]

/-- `∂ᵢ^k` commutes with multiplication by a constant. -/
theorem iterate_partialDeriv_const_mul (c : ℂ) (i : Fin n) (k : ℕ) :
    (partialDeriv i)^[k] (fun z ↦ c * f z) = fun z ↦ c * (partialDeriv i)^[k] f z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', iterate_succ_apply', ih, partialDeriv_const_mul]

/-! ### Separated products -/

section Product

variable {g : Fin n → ℂ → ℂ}

/-- An iterated derivative of a complex differentiable function `f : ℂ → E` is complex
differentiable. -/
theorem _root_.Differentiable.iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k f) :=
  (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)

/-- The partial derivative `∂ⱼ` of a separated product `z ↦ ∏ᵢ gᵢ(zᵢ)` of entire functions of one
variable replaces the factor `gⱼ` by its derivative. -/
theorem partialDeriv_prod (hg : ∀ i, Differentiable ℂ (g i)) (j : Fin n) :
    partialDeriv j (fun z ↦ ∏ i, g i (z i)) = fun z ↦ ∏ i, update g j (deriv (g j)) i (z i) := by
  ext z
  have hd : DifferentiableAt ℂ (fun z : Fin n → ℂ ↦ ∏ i, g i (z i)) z :=
    (HasFDerivAt.finsetProd fun i _ ↦
      ((hg i) (z i)).hasFDerivAt.comp z (hasFDerivAt_apply i z)).differentiableAt
  rw [partialDeriv_eq_deriv_update hd]
  have hsplit (h : ℂ → ℂ) (s : ℂ) : ∏ i, update g j h i (update z j s i) =
      h s * ∏ i ∈ Finset.univ \ {j}, g i (z i) := by
    rw [← Finset.prod_update_of_mem (Finset.mem_univ j) (fun i ↦ g i (z i)) (h s)]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hfun : (fun s ↦ ∏ i, g i (update z j s i)) =
      fun s ↦ g j s * ∏ i ∈ Finset.univ \ {j}, g i (z i) :=
    funext fun s ↦ by simpa using hsplit (g j) s
  have hR := hsplit (deriv (g j)) (z j)
  rw [update_eq_self] at hR
  rw [hfun, hR, deriv_mul_const ((hg j) _)]

/-- The iterated partial derivative `∂ⱼ^k` of a separated product `z ↦ ∏ᵢ gᵢ(zᵢ)` of entire
functions of one variable replaces the factor `gⱼ` by its `k`-th derivative. -/
theorem iterate_partialDeriv_prod (hg : ∀ i, Differentiable ℂ (g i)) (j : Fin n) (k : ℕ) :
    (partialDeriv j)^[k] (fun z ↦ ∏ i, g i (z i)) =
      fun z ↦ ∏ i, update g j (iteratedDeriv k (g j)) i (z i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hgk : ∀ i, Differentiable ℂ (update g j (iteratedDeriv k (g j)) i) := by
      intro i
      by_cases hij : i = j
      · subst hij
        simpa using (hg i).iteratedDeriv k
      · simpa [hij] using hg i
    rw [iterate_succ_apply', ih, partialDeriv_prod hgk, update_idem, update_self,
      iteratedDeriv_succ]

end Product

end TauCeti
