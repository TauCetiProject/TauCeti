/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import TauCeti.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Meromorphic continuation and exact poles of Mellin pairs

Mathlib constructs the continued Mellin transform `WeakFEPair.Λ` as an entire function minus
two explicit simple-pole terms. This file gives its meromorphicity and characterizes its
regular points: the possible poles at zero and at the weight are present exactly when the
corresponding constant terms are nonzero. These statements apply to Mellin transforms valued
in any complex Banach space, as well as scalar-valued ones.

In particular, the residue formulas determine exact pole orders, not merely upper bounds.
This is useful for theta kernels whose nonzero constant terms produce the poles of completed
zeta functions; vanishing constant terms instead give an entire completion.

The construction and residue formulas are David Loeffler's `WeakFEPair.Λ`,
`WeakFEPair.differentiable_Λ₀`, `WeakFEPair.Λ_residue_zero` and `WeakFEPair.Λ_residue_k`
in Mathlib. The Mellin principle follows Neukirch, *Algebraic Number Theory*, VII §1.
-/

public section

open Filter Topology

namespace WeakFEPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (P : WeakFEPair E)

/-- The continued Mellin transform of a weak functional-equation pair is meromorphic. -/
theorem meromorphic_Λ : Meromorphic P.Λ := by
  intro s
  have h := P.differentiable_Λ₀.analyticAt s
  unfold Λ
  fun_prop

/-- A nonzero constant term at infinity gives an exact simple pole at zero. -/
theorem meromorphicOrderAt_Λ_zero (hf : P.f₀ ≠ 0) :
    meromorphicOrderAt P.Λ 0 = (-1 : ℤ) := by
  exact (P.meromorphic_Λ 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (neg_ne_zero.mpr hf) (by simpa only [sub_zero] using P.Λ_residue_zero)

/-- A nonzero dual constant term gives an exact simple pole at the weight. -/
theorem meromorphicOrderAt_Λ_k (hg : P.g₀ ≠ 0) :
    meromorphicOrderAt P.Λ P.k = (-1 : ℤ) := by
  exact (P.meromorphic_Λ P.k).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (smul_ne_zero P.hε hg) P.Λ_residue_k

/-- The only singularities of the continued Mellin transform are the poles detected by the
constant terms. This asserts analyticity of the actual representative, not just of its germ. -/
@[simp]
theorem analyticAt_Λ_iff (s : ℂ) : AnalyticAt ℂ P.Λ s ↔
    (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.g₀ = 0) := by
  constructor
  · intro h
    have hnot (a : ℂ) (ha : meromorphicOrderAt P.Λ a = (-1 : ℤ)) :
        ¬ AnalyticAt ℂ P.Λ a := by
      intro han
      have hn := han.meromorphicOrderAt_nonneg
      rw [ha] at hn
      have : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hn
      omega
    constructor
    · by_cases hs : s = 0
      · right
        by_contra hf
        exact hnot 0 (P.meromorphicOrderAt_Λ_zero hf) (hs ▸ h)
      · exact Or.inl hs
    · by_cases hs : s = P.k
      · right
        by_contra hg
        exact hnot P.k (P.meromorphicOrderAt_Λ_k hg) (hs ▸ h)
      · exact Or.inl hs
  · rintro ⟨h0, hk⟩
    have h := P.differentiable_Λ₀.analyticAt s
    unfold Λ
    refine (h.sub ?_).sub ?_
    · rcases h0 with h0 | h0
      · fun_prop (disch := assumption)
      · simp only [h0, smul_zero]; exact analyticAt_const
    · rcases hk with hk | hk
      · have hks : (P.k : ℂ) - s ≠ 0 := sub_ne_zero.mpr hk.symm
        fun_prop (disch := assumption)
      · simp only [hk, smul_zero]; exact analyticAt_const

/-- The continued Mellin transform is entire exactly for strong functional-equation pairs. -/
@[simp]
theorem differentiable_Λ_iff : Differentiable ℂ P.Λ ↔ IsStrongFEPair P := by
  constructor
  · intro h
    exact ⟨((P.analyticAt_Λ_iff 0).mp (h.analyticAt 0)).1.resolve_left (by simp),
      ((P.analyticAt_Λ_iff P.k).mp (h.analyticAt P.k)).2.resolve_left (by simp)⟩
  · exact IsStrongFEPair.differentiable_Λ

end WeakFEPair
