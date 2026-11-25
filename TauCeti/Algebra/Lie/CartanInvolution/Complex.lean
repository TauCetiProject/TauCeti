/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Algebra.Lie.Killing.RestrictScalars

/-!
# Cartan involutions of complex Lie algebras viewed as real

Let `L` be a complex Lie algebra, viewed as a real Lie algebra `L_ℝ`. Its real Killing form is
`B_ℝ = 2 Re B_ℂ` (`TauCeti.killingForm_real_eq_two_mul_re`). Hence an involutive automorphism `τ`
of `L_ℝ` with `Re B_ℂ(x, τ x) < 0` for every `x ≠ 0` is a Cartan involution of `L_ℝ`.

When `τ` is moreover conjugate-linear, its `-1`-eigenspace is `i` times its fixed subalgebra:
`𝔭 = i 𝔨`. If the fixed subalgebra `𝔲 = 𝔨` of a conjugate-linear involutive automorphism has
negative definite `Re B_ℂ`, as for a compact real form, then `τ` is a Cartan involution of `L_ℝ`
with `𝔨 = 𝔲` and `𝔭 = i 𝔲`: writing `a = x + τ x ∈ 𝔲` and `c = i (x - τ x) ∈ 𝔲`, one has
`4 B_ℂ(x, τ x) = B_ℂ(a, a) + B_ℂ(c, c)`.

## Main results

* `LieEquiv.isCartanInvolution_of_re_killingForm_neg`: an involution with
  `Re B_ℂ(x, τ x) < 0` for `x ≠ 0` is a Cartan involution of `L_ℝ`.
* `LieEquiv.I_smul_mem_cartanP_iff`, `LieEquiv.mem_cartanP_iff_I_smul_mem_fixedSubalgebra`: for
  conjugate-linear `τ`, `𝔭 = i 𝔨`.
* `LieEquiv.isCartanInvolution_of_re_killingForm_fixedSubalgebra_neg`: a conjugate-linear
  involutive automorphism whose fixed subalgebra has negative definite `Re B_ℂ` is a Cartan
  involution of `L_ℝ`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §1, Proposition 6.3,
  and §2, Example 1 after Corollary 6.18.
-/

public section

open LieAlgebra Complex

namespace LieEquiv

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℝ L] [IsScalarTower ℝ ℂ L]
  {τ : L ≃ₗ⁅ℝ⁆ L}

/-- An involutive automorphism `τ` of a complex Lie algebra viewed as real, with
`Re B_ℂ(x, τ x) < 0` for every `x ≠ 0`, is a Cartan involution of the real Lie algebra. -/
theorem isCartanInvolution_of_re_killingForm_neg (hinv : Function.Involutive τ)
    (h : ∀ x : L, x ≠ 0 → (killingForm ℂ L x (τ x)).re < 0) : τ.IsCartanInvolution :=
  isCartanInvolution_iff.2 ⟨hinv, fun x hx ↦ by
    rw [TauCeti.killingForm_real_eq_two_mul_re]
    linarith [h x hx]⟩

omit [IsScalarTower ℝ ℂ L] in
/-- For a conjugate-linear `τ`, `i x` lies in the `-1`-eigenspace `𝔭` exactly when `x` lies in
the fixed subalgebra `𝔨`. -/
theorem I_smul_mem_cartanP_iff (hτ : ∀ (c : ℂ) (x : L), τ (c • x) = (starRingEnd ℂ) c • τ x)
    {x : L} : I • x ∈ τ.cartanP ↔ x ∈ τ.toLieHom.fixedSubalgebra := by
  rw [mem_cartanP, LieHom.mem_fixedSubalgebra, coe_toLieHom, hτ, conj_I, neg_smul, neg_inj,
    smul_right_inj I_ne_zero]

omit [IsScalarTower ℝ ℂ L] in
/-- For a conjugate-linear `τ`, `x` lies in the `-1`-eigenspace `𝔭` exactly when `i x` lies in
the fixed subalgebra `𝔨`: `𝔭 = i 𝔨`. -/
theorem mem_cartanP_iff_I_smul_mem_fixedSubalgebra
    (hτ : ∀ (c : ℂ) (x : L), τ (c • x) = (starRingEnd ℂ) c • τ x) {x : L} :
    x ∈ τ.cartanP ↔ I • x ∈ τ.toLieHom.fixedSubalgebra := by
  rw [mem_cartanP, LieHom.mem_fixedSubalgebra, coe_toLieHom, hτ, conj_I, neg_smul, ← smul_neg,
    smul_right_inj I_ne_zero, neg_eq_iff_eq_neg]

/-- **A compact real form gives a Cartan involution.** A conjugate-linear involutive automorphism
`τ` of a complex Lie algebra viewed as real, whose fixed subalgebra `𝔲` has negative definite
`Re B_ℂ`, is a Cartan involution of the real Lie algebra, with `𝔨 = 𝔲` and `𝔭 = i 𝔲`. -/
theorem isCartanInvolution_of_re_killingForm_fixedSubalgebra_neg (hinv : Function.Involutive τ)
    (hτ : ∀ (c : ℂ) (x : L), τ (c • x) = (starRingEnd ℂ) c • τ x)
    (h : ∀ u ∈ τ.toLieHom.fixedSubalgebra, u ≠ 0 → (killingForm ℂ L u u).re < 0) :
    τ.IsCartanInvolution := by
  have hle (u : L) (hu : u ∈ τ.toLieHom.fixedSubalgebra) : (killingForm ℂ L u u).re ≤ 0 := by
    rcases eq_or_ne u 0 with rfl | hu₀
    · simp
    · exact (h u hu hu₀).le
  refine isCartanInvolution_of_re_killingForm_neg hinv fun x hx ↦ ?_
  have ha : x + τ x ∈ τ.toLieHom.fixedSubalgebra := by
    rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_add, hinv x, add_comm]
  have hc : I • (x - τ x) ∈ τ.toLieHom.fixedSubalgebra := by
    rw [← mem_cartanP_iff_I_smul_mem_fixedSubalgebra hτ, mem_cartanP, map_sub, hinv x, neg_sub]
  have key : 4 * killingForm ℂ L x (τ x) = killingForm ℂ L (x + τ x) (x + τ x) +
      killingForm ℂ L (I • (x - τ x)) (I • (x - τ x)) := by
    have hsymm := LieModule.traceForm_comm ℂ L L (τ x) x
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [killingForm, hsymm]
    linear_combination (-(LieModule.traceForm ℂ L L x x - LieModule.traceForm ℂ L L x (τ x) -
      LieModule.traceForm ℂ L L x (τ x) + LieModule.traceForm ℂ L L (τ x) (τ x))) * I_sq
  have hre := congrArg re key
  rw [add_re, show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, re_ofReal_mul] at hre
  have hne : x + τ x ≠ 0 ∨ I • (x - τ x) ≠ 0 := by
    by_contra! h₀
    rw [smul_eq_zero, sub_eq_zero] at h₀
    have h₁ := h₀.1
    rw [← h₀.2.resolve_left I_ne_zero, ← two_smul ℂ x, smul_eq_zero] at h₁
    exact hx (h₁.resolve_left two_ne_zero)
  rcases hne with hne | hne
  · linarith [h _ ha hne, hle _ hc]
  · linarith [hle _ ha, h _ hc hne]

end LieEquiv
