/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential
import TauCeti.Analysis.Meromorphic.PrincipalPart
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Principal parts at an isolated singularity with smooth `∂bar`

For coefficients `c : Fin n → ℂ` and a point `z`, the **principal part sum**
(`TauCeti.principalPartSum c z`) is the function

`w ↦ ∑_{j < n} c_j / (w - z)^(j + 1)`.

A function `f` **has principal part `c` at `z`** (`TauCeti.HasPrincipalPart f z c`) if
`f - principalPartSum c z` is bounded on a punctured neighbourhood of `z`. A principal part sum
is the polynomial `∑_{j < n} c_j X^(j + 1)` evaluated at `(w - z)⁻¹`
(`TauCeti.principalPartSum_eq_eval_inv_sub`), so the theory of principal parts of meromorphic germs
in `TauCeti.Analysis.Meromorphic.PrincipalPart` applies to it. In particular a principal part sum
that is bounded near `z` has zero coefficients (`TauCeti.eq_zero_of_isBigO_principalPartSum`), so
a function has at most one principal part of each order (`TauCeti.HasPrincipalPart.unique`), and
principal parts are additive and homogeneous. `TauCeti.principalPart f z n` selects it when it
exists, and is `0` otherwise.

The main result is a removable-singularity theorem for the inhomogeneous Cauchy–Riemann
equation. Let `η` be real differentiable on a punctured neighbourhood of `z`, with
`∂bar η = β` there for a function `β` of class `Cᵏ`, `k ≥ 1`, on a full neighbourhood of `z`,
and suppose that `(w - z)ⁿ η(w)` is bounded near `z`. Then

`η = g + principalPartSum c z`  on a punctured neighbourhood of `z`,

for some coefficients `c : Fin n → ℂ` and a function `g` of class `Cᵏ` at `z`
(`TauCeti.exists_contDiffAt_eventuallyEq_add_principalPartSum`). Indeed, subtracting a local
solution `G` of `∂bar G = β` leaves a function `h` holomorphic on the punctured neighbourhood with
a pole of order at most `n`. Then `(w - z)ⁿ h` has a removable singularity, and Taylor's formula
for its extension splits `h` into a principal part sum and a function analytic at `z`
(`TauCeti.exists_analyticAt_eventuallyEq_add_principalPartSum`). For `n = 0` this says that a
bounded solution of `∂bar η = β` extends across `z` with the regularity of `β`.

This is the local structure of the quotient `δα / α` of a variation of a plane vortex by its
section near a zero of the section. Under the hypotheses of the vortex application, these
principal parts determine the elements of the kernel of the linearized vortex equations.

## Main definitions

* `TauCeti.principalPartSum c z`: the function `w ↦ ∑_{j < n} c_j / (w - z)^(j + 1)`.
* `TauCeti.HasPrincipalPart f z c`: `f - principalPartSum c z` is bounded near `z`.
* `TauCeti.principalPart f z n`: the principal part of order `n` of `f` at `z`, or `0`.

## Main results

* `TauCeti.principalPartSum_eq_eval_inv_sub`: a principal part sum as a polynomial in
  `(w - z)⁻¹`.
* `TauCeti.eq_zero_of_isBigO_principalPartSum`: a bounded principal part sum vanishes.
* `TauCeti.HasPrincipalPart.unique`, `TauCeti.HasPrincipalPart.add`,
  `TauCeti.HasPrincipalPart.const_mul`: uniqueness and linearity of principal parts.
* `TauCeti.hasPrincipalPart_of_eventuallyEq_add`: a principal part sum plus a function
  continuous at `z` has that principal part.
* `TauCeti.exists_analyticAt_eventuallyEq_add_principalPartSum`,
  `TauCeti.exists_hasPrincipalPart_of_differentiableAt`: a function holomorphic on a punctured
  neighbourhood of `z` with a pole of order at most `n` is a principal part sum plus a function
  analytic at `z`; in particular it has a principal part of order `n` there.
* `TauCeti.exists_contDiffAt_eventuallyEq_add_principalPartSum`: a function with `Cᵏ`
  `∂bar` near `z` and a pole of order at most `n` is a principal part sum plus a function of
  class `Cᵏ` at `z`; in particular it has a principal part of order `n` there.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I.
-/

public section

noncomputable section

open Asymptotics Complex Filter Function Polynomial Set Topology

namespace TauCeti

/-! ### Principal part sums -/

section Sum

variable {n : ℕ}

/-- The **principal part sum** with coefficients `c` at `z`: the function
`w ↦ ∑_{j < n} c_j / (w - z)^(j + 1)`. -/
def principalPartSum (c : Fin n → ℂ) (z w : ℂ) : ℂ :=
  ∑ j, c j / (w - z) ^ (j.val + 1)

theorem principalPartSum_def (c : Fin n → ℂ) (z w : ℂ) :
    principalPartSum c z w = ∑ j, c j / (w - z) ^ (j.val + 1) :=
  (rfl)

/-- The principal part sum with zero coefficients vanishes. -/
@[simp]
theorem principalPartSum_zero (z : ℂ) : principalPartSum (0 : Fin n → ℂ) z = 0 := by
  funext w
  simp [principalPartSum]

theorem principalPartSum_add (c d : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (c + d) z w = principalPartSum c z w + principalPartSum d z w := by
  simp only [principalPartSum, Pi.add_apply, add_div, Finset.sum_add_distrib]

theorem principalPartSum_smul (a : ℂ) (c : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (a • c) z w = a * principalPartSum c z w := by
  simp only [principalPartSum, Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

theorem principalPartSum_sub (c d : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (c - d) z w = principalPartSum c z w - principalPartSum d z w := by
  simp only [principalPartSum, Pi.sub_apply, sub_div, Finset.sum_sub_distrib]

/-- Prepending a coefficient:
`principalPartSum (a, c) z w = (a + principalPartSum c z w) / (w - z)`. -/
theorem principalPartSum_cons (a : ℂ) (c : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (Fin.cons a c : Fin (n + 1) → ℂ) z w =
      (a + principalPartSum c z w) / (w - z) := by
  simp only [principalPartSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, pow_zero, one_mul, add_div, Finset.sum_div, div_div, pow_succ]

/-- A principal part sum is holomorphic off its pole. -/
theorem differentiableAt_principalPartSum (c : Fin n → ℂ) {z w : ℂ} (hw : w ≠ z) :
    DifferentiableAt ℂ (principalPartSum c z) w := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
  unfold principalPartSum
  fun_prop (disch := exact pow_ne_zero _ hwz)

/-- A principal part sum is the polynomial `∑_{j < n} c_j X^(j + 1)`, which has no constant term,
evaluated at `(w - z)⁻¹`. -/
theorem principalPartSum_eq_eval_inv_sub (c : Fin n → ℂ) (z w : ℂ) :
    principalPartSum c z w = (∑ j, C (c j) * X ^ (j.val + 1)).eval (w - z)⁻¹ := by
  simp [principalPartSum, eval_finsetSum, div_eq_mul_inv, inv_pow]

/-- **A bounded principal part sum vanishes.** If `∑_{j < n} c_j / (w - z)^(j + 1)` is bounded on
a punctured neighbourhood of `z`, then all the coefficients `c_j` are zero. -/
theorem eq_zero_of_isBigO_principalPartSum {c : Fin n → ℂ} {z : ℂ}
    (h : principalPartSum c z =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) : c = 0 := by
  -- The sum extends analytically across `z`, so as a polynomial without constant term in
  -- `(w - z)⁻¹` it is zero.
  obtain ⟨H, hH, hcH⟩ := exists_analyticAt_eventuallyEq_of_isBigO
    (eventually_mem_nhdsWithin.mono fun w hw ↦ differentiableAt_principalPartSum c hw) h
  have hP := eq_zero_of_eval_inv_sub_eventuallyEq (P := ∑ j, C (c j) * X ^ (j.val + 1))
    (by simp [finsetSum_coeff]) hH
    (hcH.mono fun w hw ↦ (principalPartSum_eq_eval_inv_sub c z w).symm.trans hw)
  funext j
  simpa [finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using congrArg (coeff · (j.val + 1)) hP

end Sum

/-! ### Principal parts -/

section PrincipalPart

variable {f g : ℂ → ℂ} {z : ℂ} {n : ℕ} {c d : Fin n → ℂ}

/-- `c` is the **principal part** of order `n` of `f` at `z`: the difference
`f - principalPartSum c z` is bounded on a punctured neighbourhood of `z`. The value of `f` at
`z` plays no role. -/
def HasPrincipalPart (f : ℂ → ℂ) (z : ℂ) (c : Fin n → ℂ) : Prop :=
  (fun w ↦ f w - principalPartSum c z w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))

theorem hasPrincipalPart_iff :
    HasPrincipalPart f z c ↔
      (fun w ↦ f w - principalPartSum c z w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ)) :=
  Iff.rfl

/-- The principal part is zero exactly when the function is bounded near the point. -/
@[simp]
theorem hasPrincipalPart_zero_iff :
    HasPrincipalPart f z (0 : Fin n → ℂ) ↔ f =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ)) := by
  simp [HasPrincipalPart]

/-- **Uniqueness of principal parts.** -/
theorem HasPrincipalPart.unique (h : HasPrincipalPart f z c) (h' : HasPrincipalPart f z d) :
    c = d := by
  refine sub_eq_zero.mp (eq_zero_of_isBigO_principalPartSum (z := z) ?_)
  refine (IsBigO.sub h' h).congr_left fun w ↦ ?_
  rw [principalPartSum_sub]
  ring

theorem HasPrincipalPart.add (hf : HasPrincipalPart f z c) (hg : HasPrincipalPart g z d) :
    HasPrincipalPart (fun w ↦ f w + g w) z (c + d) := by
  refine (IsBigO.add hf hg).congr_left fun w ↦ ?_
  rw [principalPartSum_add]
  ring

theorem HasPrincipalPart.const_mul (hf : HasPrincipalPart f z c) (a : ℂ) :
    HasPrincipalPart (fun w ↦ a * f w) z (a • c) := by
  refine (IsBigO.const_mul_left hf a).congr_left fun w ↦ ?_
  rw [principalPartSum_smul]
  ring

/-- A function that is a principal part sum plus a function continuous at `z`, on a punctured
neighbourhood of `z`, has that principal part. -/
theorem hasPrincipalPart_of_eventuallyEq_add (hg : ContinuousAt g z)
    (hfg : ∀ᶠ w in 𝓝[≠] z, f w = g w + principalPartSum c z w) : HasPrincipalPart f z c :=
  IsBigO.congr' (hg.tendsto.isBigO_one ℝ |>.mono nhdsWithin_le_nhds)
    (hfg.mono fun w hw ↦ by simp only [hw]; ring) EventuallyEq.rfl

/-- Functions that agree on a punctured neighbourhood of `z` have the same principal part
there. -/
theorem HasPrincipalPart.congr (hf : HasPrincipalPart f z c) (hfg : f =ᶠ[𝓝[≠] z] g) :
    HasPrincipalPart g z c :=
  IsBigO.congr' hf (hfg.mono fun w hw ↦ by simp only [hw]) EventuallyEq.rfl

open scoped Classical in
/-- The **principal part** of order `n` of `f` at `z`: the coefficients `c` with
`HasPrincipalPart f z c` when they exist (they are then unique), and `0` otherwise. -/
def principalPart (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : Fin n → ℂ :=
  if h : ∃ c : Fin n → ℂ, HasPrincipalPart f z c then h.choose else 0

theorem hasPrincipalPart_principalPart (h : ∃ c : Fin n → ℂ, HasPrincipalPart f z c) :
    HasPrincipalPart f z (principalPart f z n) := by
  simp only [principalPart, h, ↓reduceDIte]
  exact h.choose_spec

theorem HasPrincipalPart.principalPart_eq (h : HasPrincipalPart f z c) :
    principalPart f z n = c :=
  (hasPrincipalPart_principalPart ⟨c, h⟩).unique h

end PrincipalPart

/-! ### Existence of principal parts -/

section Existence

variable {z : ℂ}

/-- **Principal parts of a pole.** A function holomorphic on a punctured neighbourhood of `z`,
with a pole of order at most `n` there, is a principal part sum of order `n` plus a function
analytic at `z`, on a punctured neighbourhood of `z`. -/
theorem exists_analyticAt_eventuallyEq_add_principalPartSum {n : ℕ} {h : ℂ → ℂ}
    (hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ h w)
    (hb : (fun w ↦ (w - z) ^ n * h w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) :
    ∃ (c : Fin n → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝[≠] z, h w = g w + principalPartSum c z w := by
  -- `(w - z)ⁿ h` extends to a function `F` analytic at `z`, and Taylor's formula for `F` splits
  -- `h = (w - z)⁻ⁿ F` into a polynomial without constant term in `(w - z)⁻¹` of degree at most
  -- `n` and an analytic remainder.
  obtain ⟨F, hF, hhF⟩ := exists_analyticAt_eventuallyEq_of_isBigO (by
    filter_upwards [hd] with w hw
    exact ((differentiableAt_id.sub_const z).pow n).mul hw) hb
  set P := ∑ j ∈ Finset.range n, C ((swap dslope z)^[j] F z) * X ^ (n - j)
  have hP : ∑ j : Fin n, C (P.coeff (j.val + 1)) * X ^ (j.val + 1) = P := by
    have hdeg : P.natDegree < n + 1 := Nat.lt_succ_of_le <| natDegree_sum_le_of_forall_le _ _
      fun j _ ↦ natDegree_C_mul_X_pow_le _ _ |>.trans (Nat.sub_le n j)
    conv_rhs => rw [as_sum_range_C_mul_X_pow' P hdeg, Finset.sum_range_succ']
    rw [coeff_zero_sum_C_mul_X_pow_sub, C_0, zero_mul, add_zero,
      Fin.sum_univ_eq_sum_range (fun j ↦ C (P.coeff (j + 1)) * X ^ (j + 1))]
  refine ⟨fun j ↦ P.coeff (j.val + 1), (swap dslope z)^[n] F, hF.iterate_dslope n, ?_⟩
  filter_upwards [hhF, self_mem_nhdsWithin] with w hw hwz
  rw [principalPartSum_eq_eval_inv_sub, hP, add_comm, ← inv_pow_sub_mul_eq_eval_inv_sub_add F n hwz,
    ← hw, inv_mul_cancel_left₀ (pow_ne_zero n (sub_ne_zero.mpr hwz))]

/-- A function holomorphic on a punctured neighbourhood of `z` with a pole of order at most `n`
has a principal part of order `n` there. -/
theorem exists_hasPrincipalPart_of_differentiableAt {n : ℕ} {h : ℂ → ℂ}
    (hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ h w)
    (hb : (fun w ↦ (w - z) ^ n * h w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) :
    ∃ c : Fin n → ℂ, HasPrincipalPart h z c :=
  let ⟨c, _, hg, hhg⟩ := exists_analyticAt_eventuallyEq_add_principalPartSum hd hb
  ⟨c, hasPrincipalPart_of_eventuallyEq_add hg.continuousAt hhg⟩

/-- **Principal parts at a singularity with smooth `∂bar`.** Let `η` be real differentiable on a
punctured neighbourhood of `z`, with `∂bar η = β` there, where `β` is of class `Cᵏ`, `k ≥ 1`, on a
neighbourhood of `z`. If `(w - z)ⁿ η(w)` is bounded near `z`, then on a punctured neighbourhood of
`z`, `η = g + principalPartSum c z` for some coefficients `c : Fin n → ℂ` and a function `g` of
class `Cᵏ` at `z`. -/
theorem exists_contDiffAt_eventuallyEq_add_principalPartSum {η β : ℂ → ℂ} {U : Set ℂ}
    {k : ℕ∞} {n : ℕ} (hk : 1 ≤ k) (hU : U ∈ 𝓝 z) (hβ : ContDiffOn ℝ k β U)
    (hη : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℝ η w ∧ conjWirtingerDeriv η w 1 = β w)
    (hb : (fun w ↦ (w - z) ^ n * η w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) :
    ∃ (c : Fin n → ℂ) (g : ℂ → ℂ), ContDiffAt ℝ k g z ∧
      ∀ᶠ w in 𝓝[≠] z, η w = g w + principalPartSum c z w := by
  -- Subtract a local solution `G` of `∂bar G = β`; the difference is holomorphic off `z`.
  obtain ⟨G, hG, hGβ⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq hk
    isOpen_interior (hβ.mono interior_subset) (mem_interior_iff_mem_nhds.mpr hU)
  have hGd : Differentiable ℝ G :=
    hG.differentiable (by exact_mod_cast (zero_lt_one.trans_le hk).ne')
  have hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ (η - G) w := by
    filter_upwards [hη, nhdsWithin_le_nhds hGβ] with w hw hGw
    rw [differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hw.1.sub (hGd w)),
      conjWirtingerDeriv_sub hw.1 (hGd w), sub_apply, hw.2, hGw, sub_self]
  have hbG : (fun w ↦ (w - z) ^ n * G w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ)) :=
    (((continuous_id.sub continuous_const).pow n).mul hG.continuous).continuousAt.tendsto
      |>.isBigO_one ℝ |>.mono nhdsWithin_le_nhds
  obtain ⟨c, H, hH, hhH⟩ := exists_analyticAt_eventuallyEq_add_principalPartSum hd
    ((hb.sub hbG).congr_left fun w ↦ by simp only [Pi.sub_apply]; ring)
  refine ⟨c, fun w ↦ G w + H w, hG.contDiffAt.add (hH.contDiffAt.restrict_scalars ℝ), ?_⟩
  filter_upwards [hhH] with w hw
  rw [Pi.sub_apply] at hw
  linear_combination hw

end Existence

end TauCeti
