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
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Partial derivatives of entire functions on `ℂⁿ`

This file defines the partial derivative `∂ᵢ f (z) = Df(z) eᵢ` (`TauCeti.partialDeriv`) of a
function `f : (ι → ℂ) → E` in the direction of the `i`-th coordinate vector, and develops its
calculus on entire functions.

## Main results

* `TauCeti.partialDeriv_eq_deriv_update`: `∂ᵢ f (z)` is the derivative of `f` along the line
  through `z` parallel to the `i`-th coordinate axis.
* `TauCeti.differentiable_partialDeriv`: a partial derivative of an entire function is entire.
* `TauCeti.partialDeriv_comm`: partial derivatives of an entire function commute.
* `TauCeti.partialDeriv_add`, `TauCeti.partialDeriv_const_smul`: `∂ᵢ` is linear.
* `TauCeti.partialDeriv_prod`, `TauCeti.iterate_partialDeriv_prod`: for a separated product
  `z ↦ ∏ⱼ gⱼ(zⱼ)` of entire functions of one variable, `∂ᵢ^k` differentiates the `i`-th factor
  `k` times.
-/

public section

open Function

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The partial derivative `∂ᵢ f (z) = Df(z) eᵢ` of a function `f : (ι → ℂ) → E` in the direction
of the `i`-th coordinate vector. -/
noncomputable def partialDeriv (i : ι) (f : (ι → ℂ) → E) : (ι → ℂ) → E :=
  fun z ↦ fderiv ℂ f z (Pi.single i 1)

theorem partialDeriv_def (i : ι) (f : (ι → ℂ) → E) :
    partialDeriv i f = fun z ↦ fderiv ℂ f z (Pi.single i 1) := (rfl)

theorem partialDeriv_apply (i : ι) (f : (ι → ℂ) → E) (z : ι → ℂ) :
    partialDeriv i f z = fderiv ℂ f z (Pi.single i 1) := (rfl)

/-- The partial derivative `∂ᵢ f (z)` is the derivative of `f` restricted to the line through `z`
parallel to the `i`-th coordinate axis. -/
theorem partialDeriv_eq_deriv_update [Finite ι] {f : (ι → ℂ) → E} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : ι) :
    partialDeriv i f z = deriv (fun s ↦ f (update z i s)) (z i) := by
  have := Fintype.ofFinite ι
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
theorem partialDeriv_zero_fun [Finite ι] (i : ι) : partialDeriv i (0 : (ι → ℂ) → E) = 0 := by
  have := Fintype.ofFinite ι
  ext z
  simp [partialDeriv_apply, fderiv_zero]

variable {f g : (ι → ℂ) → E}

/-- `∂ᵢ` is additive on entire functions. -/
theorem partialDeriv_add [Finite ι] (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (i : ι) :
    partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := by
  have := Fintype.ofFinite ι
  ext z
  simp [partialDeriv_apply, fderiv_add (hf z) (hg z)]

/-- `∂ᵢ` commutes with scalar multiplication by a constant. -/
@[simp]
theorem partialDeriv_const_smul [Finite ι] (c : ℂ) (i : ι) :
    partialDeriv i (c • f) = c • partialDeriv i f := by
  have := Fintype.ofFinite ι
  ext z
  simp [partialDeriv_apply, fderiv_const_smul_field]

/-- `∂ᵢ` commutes with multiplication by a constant. -/
@[simp]
theorem partialDeriv_const_mul [Finite ι] {f : (ι → ℂ) → ℂ} (c : ℂ) (i : ι) :
    partialDeriv i (fun z ↦ c * f z) = fun z ↦ c * partialDeriv i f z := by
  simp_rw [← smul_eq_mul]
  rw [← Pi.smul_def, partialDeriv_const_smul, Pi.smul_def]

/-- `∂ᵢ^k` commutes with scalar multiplication by a constant. -/
@[simp]
theorem iterate_partialDeriv_const_smul [Finite ι] (c : ℂ) (i : ι) (k : ℕ) :
    (partialDeriv i)^[k] (c • f) = c • (partialDeriv i)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', iterate_succ_apply', ih, partialDeriv_const_smul]

/-- `∂ᵢ^k` commutes with multiplication by a constant. -/
@[simp]
theorem iterate_partialDeriv_const_mul [Finite ι] {f : (ι → ℂ) → ℂ} (c : ℂ) (i : ι) (k : ℕ) :
    (partialDeriv i)^[k] (fun z ↦ c * f z) = fun z ↦ c * (partialDeriv i)^[k] f z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', iterate_succ_apply', ih, partialDeriv_const_mul]

/-! ### Entire functions -/

section Entire

variable [Finite ι] [CompleteSpace E]

/-- A partial derivative of an entire function is entire. -/
theorem differentiable_partialDeriv (hf : Differentiable ℂ f) (i : ι) :
    Differentiable ℂ (partialDeriv i f) := by
  have := Fintype.ofFinite ι
  exact hf.fderiv_of_finiteDimensional.clm_apply (differentiable_const _)

/-- **Partial derivatives of an entire function commute.** -/
theorem partialDeriv_comm (hf : Differentiable ℂ f) (i j : ι) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  have := Fintype.ofFinite ι
  have key (k l : ι) (z : ι → ℂ) : partialDeriv k (partialDeriv l f) z =
      fderiv ℂ (fderiv ℂ f) z (Pi.single k 1) (Pi.single l 1) := by
    rw [partialDeriv_apply, partialDeriv_def l f,
      fderiv_clm_apply (hf.fderiv_of_finiteDimensional z) (differentiableAt_const _)]
    simp
  ext z
  rw [key, key]
  exact (hf.contDiff_of_finiteDimensional (n := 2)).contDiffAt.isSymmSndFDerivAt (by simp) _ _

/-! ### Iterated partial derivatives in one direction -/

/-- An iterated partial derivative of an entire function is entire. -/
theorem differentiable_iterate_partialDeriv (hf : Differentiable ℂ f) (i : ι) (k : ℕ) :
    Differentiable ℂ ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [iterate_succ_apply']; exact differentiable_partialDeriv ih i

/-- `∂ᵢ^k` commutes with `∂ⱼ` on entire functions. -/
theorem iterate_partialDeriv_comm (hf : Differentiable ℂ f) (i j : ι) (k : ℕ) :
    (partialDeriv i)^[k] (partialDeriv j f) = partialDeriv j ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_comm (differentiable_iterate_partialDeriv hf i k)]

/-- `∂ᵢ^k` is additive on entire functions. -/
theorem iterate_partialDeriv_add (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (i : ι)
    (k : ℕ) : (partialDeriv i)^[k] (f + g) = (partialDeriv i)^[k] f + (partialDeriv i)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_add (differentiable_iterate_partialDeriv hf i k)
        (differentiable_iterate_partialDeriv hg i k)]

end Entire

/-! ### Separated products -/

section Product

variable [Fintype ι] {g : ι → ℂ → ℂ}

/-- The partial derivative `∂ⱼ` of a separated product `z ↦ ∏ᵢ gᵢ(zᵢ)` of entire functions of one
variable replaces the factor `gⱼ` by its derivative. -/
theorem partialDeriv_prod (hg : ∀ i, Differentiable ℂ (g i)) (j : ι) :
    partialDeriv j (fun z ↦ ∏ i, g i (z i)) = fun z ↦ ∏ i, update g j (deriv (g j)) i (z i) := by
  ext z
  have hd : DifferentiableAt ℂ (fun z : ι → ℂ ↦ ∏ i, g i (z i)) z :=
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
theorem iterate_partialDeriv_prod (hg : ∀ i, Differentiable ℂ (g i)) (j : ι) (k : ℕ) :
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
