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
zeta functions; vanishing constant terms instead give an entire completion
(`IsStrongFEPair.Λ_eq_Λ₀`). Clearing the two simple poles defines an explicit entire function
`WeakFEPair.entireΛ` that agrees with `(s * (s - k)) • Λ s` off `{0, k}`, takes the removable
residue values `k • f₀` at `0` and `k • (ε • g₀)` at `k`, and satisfies
`entireΛ (k - s) = ε • symm.entireΛ s` on all of `ℂ`.

The construction and residue formulas are David Loeffler's `WeakFEPair.Λ`,
`WeakFEPair.differentiable_Λ₀`, `WeakFEPair.Λ_residue_zero` and `WeakFEPair.Λ_residue_k`
in Mathlib. The Mellin principle follows Neukirch, *Algebraic Number Theory*, VII §1.
-/

public section

open Filter Topology

namespace IsStrongFEPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For a strong functional-equation pair, the completed function equals the entire part `Λ₀`
pointwise on `ℂ`, including at `0` and `k`. -/
theorem Λ_eq_Λ₀ {P : WeakFEPair E} (hP : IsStrongFEPair P) : P.Λ = P.Λ₀ := by
  funext s
  simp [WeakFEPair.Λ, hP.hf₀, hP.hg₀]

end IsStrongFEPair

namespace WeakFEPair

section Meromorphic

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

end Meromorphic

section Entire

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (P : WeakFEPair E)

/-- The continued Mellin transform is entire exactly for strong functional-equation pairs. -/
@[simp]
theorem differentiable_Λ_iff : Differentiable ℂ P.Λ ↔ IsStrongFEPair P := by
  constructor
  · intro h
    have hzero (a : ℂ) :
        Tendsto (fun s ↦ (s - a) • P.Λ s) (𝓝[≠] a) (𝓝 0) := by
      have hc : Continuous (fun s : ℂ ↦ (s - a) • P.Λ s) :=
        (continuous_id.sub continuous_const).smul h.continuous
      simpa only [sub_self, zero_smul] using (hc.tendsto a).mono_left nhdsWithin_le_nhds
    constructor
    · have hf := tendsto_nhds_unique P.Λ_residue_zero
        (by simpa only [sub_zero] using hzero 0)
      exact neg_injective (hf.trans neg_zero.symm)
    · exact (smul_eq_zero_iff_right P.hε).mp
        (tendsto_nhds_unique P.Λ_residue_k (hzero P.k))
  · exact IsStrongFEPair.differentiable_Λ

/-- The entire part `Λ₀` depends only on `f` on `(0, ∞)` and the constants of the pair. -/
theorem Λ₀_congr {P P' : WeakFEPair E} (hf : Set.EqOn P.f P'.f (Set.Ioi 0)) (hk : P.k = P'.k)
    (hε : P.ε = P'.ε) (hf₀ : P.f₀ = P'.f₀) (hg₀ : P.g₀ = P'.g₀) : P.Λ₀ = P'.Λ₀ := by
  have hmod : Set.EqOn P.f_modif P'.f_modif (Set.Ioi 0) := fun t ht ↦ by
    simp only [f_modif, Pi.add_apply, Set.indicator_apply, hf ht, hk, hε, hf₀, hg₀]
  funext s
  simp only [Λ₀, mellin]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by rw [hmod ht]

/-- Two weak pairs whose functions `f` agree on `(0, ∞)`, with the same weight, root number and
constants, have the same completed function: `Λ` sees `f` only through a Mellin transform. -/
theorem Λ_congr {P P' : WeakFEPair E} (hf : Set.EqOn P.f P'.f (Set.Ioi 0)) (hk : P.k = P'.k)
    (hε : P.ε = P'.ε) (hf₀ : P.f₀ = P'.f₀) (hg₀ : P.g₀ = P'.g₀) : P.Λ = P'.Λ := by
  funext s
  simp only [Λ, Λ₀_congr hf hk hε hf₀ hg₀, hk, hε, hf₀, hg₀]

/-- **Pole-cleared entire completion** of a weak functional-equation pair. Away from `0` and `k`
it equals `(s * (s - k)) • Λ s`, while at `0` and `k` the spurious values of the raw product are
replaced by the removable values `k • f₀` and `k • (ε • g₀)`. -/
noncomputable def entireΛ (s : ℂ) : E :=
  (s * (s - P.k)) • P.Λ₀ s - (s - P.k) • P.f₀ + s • (P.ε • P.g₀)

theorem entireΛ_def (s : ℂ) :
    P.entireΛ s = (s * (s - P.k)) • P.Λ₀ s - (s - P.k) • P.f₀ + s • (P.ε • P.g₀) := (rfl)

/-- The pole-cleared completion `entireΛ` is entire on `ℂ`. -/
theorem differentiable_entireΛ : Differentiable ℂ P.entireΛ :=
  (((differentiable_id.mul (differentiable_id.sub_const _)).smul P.differentiable_Λ₀).sub
    ((differentiable_id.sub_const _).smul_const P.f₀)).add
    (differentiable_id.smul_const (P.ε • P.g₀))

@[simp]
theorem entireΛ_zero : P.entireΛ 0 = (P.k : ℂ) • P.f₀ := by
  simp [entireΛ_def]

@[simp]
theorem entireΛ_k : P.entireΛ P.k = (P.k : ℂ) • (P.ε • P.g₀) := by
  simp [entireΛ_def]

theorem entireΛ_zero_eq_zero_iff : P.entireΛ 0 = 0 ↔ P.f₀ = 0 := by
  rw [entireΛ_zero, smul_eq_zero_iff_right (Complex.ofReal_ne_zero.mpr P.hk.ne')]

theorem entireΛ_k_eq_zero_iff : P.entireΛ P.k = 0 ↔ P.g₀ = 0 := by
  rw [entireΛ_k, smul_eq_zero_iff_right (Complex.ofReal_ne_zero.mpr P.hk.ne'),
    smul_eq_zero_iff_right P.hε]

/-- Away from the poles of `Λ` (at `s` unless `s = 0` with `f₀ ≠ 0` or `s = k` with `g₀ ≠ 0`),
`entireΛ s` equals `(s * (s - k)) • Λ s`. -/
theorem entireΛ_eq_smul_Λ {s : ℂ} (h0 : s ≠ 0 ∨ P.f₀ = 0) (hk : s ≠ P.k ∨ P.g₀ = 0) :
    P.entireΛ s = (s * (s - P.k)) • P.Λ s := by
  have h1 : (s * (s - P.k)) • ((1 / s) • P.f₀) = (s - P.k) • P.f₀ := by
    rcases h0 with h0 | hf₀
    · rw [smul_smul]; congr 1; field_simp
    · simp [hf₀]
  have h2 : (s * (s - P.k)) • ((P.ε / ((P.k : ℂ) - s)) • P.g₀) = -(s • (P.ε • P.g₀)) := by
    rcases hk with hk | hg₀
    · have hks : (P.k : ℂ) - s ≠ 0 := sub_ne_zero.mpr hk.symm
      rw [smul_smul, ← neg_smul, ← mul_smul]; congr 1; field_simp; ring
    · simp [hg₀]
  rw [Λ, smul_sub, smul_sub, h1, h2, sub_neg_eq_add, entireΛ_def]

/-- `entireΛ` agrees with `(z * (z - k)) • Λ z` as a punctured germ at every point. -/
theorem entireΛ_eventuallyEq (s : ℂ) :
    P.entireΛ =ᶠ[𝓝[≠] s] fun z ↦ (z * (z - P.k)) • P.Λ z := by
  filter_upwards [(eventually_cofinite_ne 0).filter_mono (nhdsNE_le_cofinite s),
    (eventually_cofinite_ne (P.k : ℂ)).filter_mono (nhdsNE_le_cofinite s)] with z hz0 hzk
  exact P.entireΛ_eq_smul_Λ (.inl hz0) (.inl hzk)

/-- For a strong pair, `entireΛ` equals `(s * (s - k)) • Λ s` everywhere on `ℂ`. -/
theorem _root_.IsStrongFEPair.entireΛ_eq_smul_Λ {P : WeakFEPair E} (hP : IsStrongFEPair P)
    (s : ℂ) : P.entireΛ s = (s * (s - P.k)) • P.Λ s :=
  P.entireΛ_eq_smul_Λ (.inr hP.hf₀) (.inr hP.hg₀)

/-- **Functional equation of the pole-cleared completion**, valid on all of `ℂ` including `0`
and `k`. -/
theorem entireΛ_k_sub (s : ℂ) : P.entireΛ (P.k - s) = P.ε • P.symm.entireΛ s := by
  have hmul : ((P.k : ℂ) - s) * (((P.k : ℂ) - s) - P.k) = s * (s - P.k) := by ring
  have hlin : ((P.k : ℂ) - s) - P.k = -s := by ring
  have hlin' : (P.k : ℂ) - s = -(s - P.k) := by ring
  rw [entireΛ_def, P.symm.entireΛ_def, hmul, hlin, P.functional_equation₀ s, neg_smul,
    sub_neg_eq_add]
  simp only [symm_k, symm_f₀, symm_g₀, symm_ε, smul_add, smul_sub]
  rw [smul_comm P.ε (s * (s - (P.k : ℂ))), smul_comm P.ε (s - (P.k : ℂ)), smul_comm P.ε s,
    smul_smul P.ε P.ε⁻¹, mul_inv_cancel₀ P.hε, one_smul, hlin', neg_smul]
  abel

/-- `entireΛ` depends only on `f` on `(0, ∞)` and the constants of the pair. -/
theorem entireΛ_congr {P P' : WeakFEPair E} (hf : Set.EqOn P.f P'.f (Set.Ioi 0))
    (hk : P.k = P'.k) (hε : P.ε = P'.ε) (hf₀ : P.f₀ = P'.f₀) (hg₀ : P.g₀ = P'.g₀) :
    P.entireΛ = P'.entireΛ := by
  funext s
  simp only [entireΛ_def, Λ₀_congr hf hk hε hf₀ hg₀, hk, hε, hf₀, hg₀]

end Entire

end WeakFEPair
