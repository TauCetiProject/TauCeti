/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# A root bound and smooth coefficients in monic coefficient coordinates

A root of `TauCeti.Polynomial.monicOfCoeff c` has norm strictly less than
`‖c‖ + 1`. Thus locally bounded coefficient tuples give locally bounded roots,
without choosing or continuously labelling them. This is the bound used to remove
singularities of analytic root branches.

The estimate specializes Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound`
(Daniel Weber's formalization of Cauchy's root bound) to the finite coefficient tuple.

Over a nontrivially normed field, every coefficient of `monicOfCoeff c` and of its derivative is
a smooth function of `c` (`TauCeti.Polynomial.contDiff_coeff_monicOfCoeff`,
`TauCeti.Polynomial.contDiff_coeff_derivative_monicOfCoeff`): it is a coordinate of `c`, the
constant `1` or `0`, or such a coordinate times a constant. So the value of `monicOfCoeff c` at a
point is smooth jointly in `c` and the point (`TauCeti.Polynomial.contDiff_eval_monicOfCoeff`).
That value is affine in `c`: its derivative in the direction `v` is the value of the polynomial of
degree less than `d` with coefficients `v` (`TauCeti.Polynomial.fderiv_eval_monicOfCoeff_apply`),
the tangent vector of the coefficient chart of `Sym^d`.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

/-- Every root of the monic polynomial with lower coefficients `c` has norm
strictly less than `‖c‖ + 1`. -/
theorem norm_lt_of_isRoot_monicOfCoeff {K : Type*} [NormedField K] {d : ℕ}
    (c : Fin d → K) {z : K} (hz : (monicOfCoeff c).IsRoot z) : ‖z‖ < ‖c‖ + 1 := by
  have hsup : (Finset.range d).sup (fun i => ‖(monicOfCoeff c).coeff i‖₊) ≤ ‖c‖₊ := by
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [coeff_monicOfCoeff c ⟨i, hi⟩]
    exact nnNorm_le_pi_nnNorm c ⟨i, hi⟩
  have hb : (monicOfCoeff c).cauchyBound ≤ ‖c‖₊ + 1 := by
    rw [cauchyBound, (monic_monicOfCoeff c).leadingCoeff, nnNorm_one, div_one,
      natDegree_monicOfCoeff]
    exact add_le_add hsup le_rfl
  exact_mod_cast (hz.norm_lt_cauchyBound (monic_monicOfCoeff c).ne_zero).trans_le hb

/-- Evaluating a monic coefficient family at a continuous function is continuous. -/
@[fun_prop]
theorem continuousOn_eval_monicOfCoeff {R B : Type*} [CommSemiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [TopologicalSpace B] {d : ℕ}
    (c : B → Fin d → R) {r : B → R} {t : Set B}
    (hc : ContinuousOn c t) (hr : ContinuousOn r t) :
    ContinuousOn (fun x => (monicOfCoeff (c x)).eval (r x)) t := by
  simp_rw [eval_monicOfCoeff]
  exact (hr.pow d).add (continuousOn_finsetSum _ fun i _ =>
    (continuousOn_pi.1 hc i).mul (hr.pow i.val))

section ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {d : ℕ} {n : WithTop ℕ∞}

/-- Each coefficient of the monic polynomial with lower coefficients `c` depends smoothly on `c`. -/
theorem contDiff_coeff_monicOfCoeff (k : ℕ) :
    ContDiff 𝕜 n fun c : Fin d → 𝕜 ↦ (monicOfCoeff c).coeff k := by
  rcases lt_trichotomy k d with hk | rfl | hk
  · have h (c : Fin d → 𝕜) : (monicOfCoeff c).coeff k = c ⟨k, hk⟩ :=
      coeff_monicOfCoeff c ⟨k, hk⟩
    simp_rw [h]
    exact contDiff_apply 𝕜 (fun _ : Fin d ↦ 𝕜) ⟨k, hk⟩
  · simp_rw [coeff_monicOfCoeff_self]
    exact contDiff_const
  · have h (c : Fin d → 𝕜) : (monicOfCoeff c).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_monicOfCoeff])
    simp_rw [h]
    exact contDiff_const

/-- Each coefficient of the derivative of the monic polynomial with lower coefficients `c`
depends smoothly on `c`. -/
theorem contDiff_coeff_derivative_monicOfCoeff (k : ℕ) :
    ContDiff 𝕜 n fun c : Fin d → 𝕜 ↦ (monicOfCoeff c).derivative.coeff k := by
  simp_rw [coeff_derivative]
  exact (contDiff_coeff_monicOfCoeff (k + 1)).mul contDiff_const

/-- Evaluating the monic polynomial with smoothly varying lower coefficients at a smoothly varying
point is smooth. -/
@[fun_prop]
theorem contDiff_eval_monicOfCoeff {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {c : E → Fin d → 𝕜} {r : E → 𝕜} (hc : ContDiff 𝕜 n c) (hr : ContDiff 𝕜 n r) :
    ContDiff 𝕜 n fun x ↦ (monicOfCoeff (c x)).eval (r x) := by
  simp_rw [eval_monicOfCoeff]
  exact (hr.pow d).add (ContDiff.sum fun i _ ↦ (contDiff_pi.1 hc i).mul (hr.pow _))

end ContDiff

section FDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {d : ℕ}

/-- The value at `z` of the monic polynomial with lower coefficients `c` is affine in `c`, with
linear part `v ↦ ∑ᵢ vᵢ zⁱ`. -/
theorem hasFDerivAt_eval_monicOfCoeff (c : Fin d → 𝕜) (z : 𝕜) :
    HasFDerivAt (fun c' : Fin d → 𝕜 ↦ (monicOfCoeff c').eval z)
      (∑ i : Fin d, (ContinuousLinearMap.proj i : (Fin d → 𝕜) →L[𝕜] 𝕜).smulRight (z ^ (i : ℕ)))
      c := by
  set L : (Fin d → 𝕜) →L[𝕜] 𝕜 :=
    ∑ i : Fin d, (ContinuousLinearMap.proj i : (Fin d → 𝕜) →L[𝕜] 𝕜).smulRight (z ^ (i : ℕ))
  have h : (fun c' : Fin d → 𝕜 ↦ (monicOfCoeff c').eval z) = fun c' ↦ z ^ d + L c' := by
    ext c'
    simp [L, eval_monicOfCoeff]
  rw [h]
  exact ((hasFDerivAt_const (z ^ d) c).add L.hasFDerivAt).congr_fderiv (zero_add L)

/-- **The coefficient derivative of `monicOfCoeff`.** The derivative in `c`, in the direction `v`,
of the value at `z` of the monic polynomial with lower coefficients `c` is the value at `z` of the
polynomial of degree less than `d` with coefficients `v`. -/
theorem fderiv_eval_monicOfCoeff_apply (c v : Fin d → 𝕜) (z : 𝕜) :
    fderiv 𝕜 (fun c' : Fin d → 𝕜 ↦ (monicOfCoeff c').eval z) c v =
      ((degreeLTEquiv 𝕜 d).symm v : 𝕜[X]).eval z := by
  rw [(hasFDerivAt_eval_monicOfCoeff c z).fderiv, eval_eq_sum_degreeLTEquiv (Subtype.prop _),
    Subtype.coe_eta, LinearEquiv.apply_symm_apply]
  simp

end FDeriv

end TauCeti.Polynomial
