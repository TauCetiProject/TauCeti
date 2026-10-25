/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MoreauYosida.Derivative

/-!
# De Giorgi's variational interpolation

Let `U` be a minimizing movement sequence for an energy `φ : X → EReal` with time step `τ > 0`, so
that each `U (n + 1)` is a resolvent step `U (n + 1) ∈ J_τ (U n)`. Besides the piecewise constant
interpolant `t ↦ U ⌈t / τ⌉₊`, De Giorgi's *variational interpolant* fills each time interval
`(n τ, (n + 1) τ]` with resolvent steps of intermediate size from `U n`: at time `t = n τ + r` with
`r ∈ (0, τ]` it takes a value `V n r ∈ J_r (U n)`. The family `V` is an arbitrary selection,
usually with `V n τ = U (n + 1)`, so that the two interpolants agree at the nodes.

Along this interpolant the descending slope `|∂φ|` is controlled, and summing the one-step
energy–dissipation inequality `TauCeti.apply_add_add_lintegral_descendingSlope_le` over the steps
gives the discrete energy–dissipation inequality

`φ (U N) + ∑_{n < N} d(U n, U (n + 1))² / (2τ) + ∫₀^{Nτ} |∂φ|²(W t) / 2 dt ≤ φ (U 0)`,

with `W = deGiorgiInterpolant τ V` the variational interpolant. The sum is half the discrete
`2`-action of the scheme and the integral is the discrete counterpart of
`(1/2) ∫ |∂φ|²(u t) dt`, so this is the discrete form of the energy–dissipation inequality
defining curves of maximal slope. Passing to the limit as `τ → 0` in it is how
Ambrosio–Gigli–Savaré show that generalized minimizing movements are curves of maximal slope.
For that limit the variational interpolant has to stay close to the piecewise constant one, which
is the distance estimate `d(U n, W t) ≤ d(U n, U (n + 1))` on `(n τ, (n + 1) τ]`, valid when
`V n τ = U (n + 1)`, `φ (U n) ≠ ⊤` and `φ (U (n + 1)) ≠ ⊥`.

## Main definitions

* `TauCeti.deGiorgiInterpolant τ V`: the variational interpolant `t ↦ V n (t - n τ)` on
  `(n τ, (n + 1) τ]`, defined through `n = ⌈t / τ⌉₊ - 1`.

## Main results

* `TauCeti.deGiorgiInterpolant_of_mem_Ioc`: the value of the interpolant on `(n τ, (n + 1) τ]`.
* `TauCeti.exists_forall_mem_moreauYosidaResolvent_and_eq`: a selection `V` with
  `V n τ = U (n + 1)` exists as soon as the intermediate resolvents are nonempty.
* `TauCeti.apply_deGiorgiInterpolant_le` and `TauCeti.edist_deGiorgiInterpolant_le`: on
  `(n τ, (n + 1) τ]` the interpolant has energy at most `φ (U n)`, and, when `V n τ = U (n + 1)`,
  `φ (U n) ≠ ⊤` and `φ (U (n + 1)) ≠ ⊥`, distance at most `d(U n, U (n + 1))` from `U n`.
* `TauCeti.apply_add_sum_add_lintegral_descendingSlope_le_of_forall_mem_moreauYosidaResolvent`:
  the discrete energy–dissipation inequality along a minimizing movement sequence.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 3, Sections 3.1 and 3.2.
* E. De Giorgi, *New problems on minimizing movements*, in *Boundary Value Problems for Partial
  Differential Equations and Applications*, RMA Res. Notes Appl. Math. 29, Masson 1993, 81–98.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

section Interpolant

variable {X : Type*} {τ : ℝ≥0} {V : ℕ → ℝ → X}

/-- *De Giorgi's variational interpolant* of the family `V` with time step `τ`: on the time interval
`(n τ, (n + 1) τ]` it is `t ↦ V n (t - n τ)`, where `V n r` is meant to be a resolvent step
`V n r ∈ J_r (U n)` from the `n`-th point of a minimizing movement sequence. The index
`n = ⌈t / τ⌉₊ - 1` is that of the interval containing `t`; the values at times `t ≤ 0` play no
role. -/
def deGiorgiInterpolant (τ : ℝ≥0) (V : ℕ → ℝ → X) (t : ℝ) : X :=
  V (⌈t / τ⌉₊ - 1) (t - (⌈t / τ⌉₊ - 1 : ℕ) * τ)

/-- On the time interval `(n τ, (n + 1) τ]`, the variational interpolant is `V n (t - n τ)`. -/
theorem deGiorgiInterpolant_of_mem_Ioc (hτ : 0 < τ) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ioc (n * τ : ℝ) ((n + 1) * τ)) :
    deGiorgiInterpolant τ V t = V n (t - n * τ) := by
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hceil : ⌈t / τ⌉₊ = n + 1 := (Nat.ceil_eq_iff n.succ_ne_zero).2
    ⟨by simpa [lt_div_iff₀ hτ'] using ht.1, by simpa [div_le_iff₀ hτ'] using ht.2⟩
  rw [deGiorgiInterpolant, hceil, Nat.add_sub_cancel]

/-- The integral of a function of the variational interpolant over the time interval
`(n τ, (n + 1) τ]` is the integral of the same function of `V n` over `(0, τ]`. -/
theorem setLIntegral_deGiorgiInterpolant (hτ : 0 < τ) (f : X → ℝ≥0∞) (n : ℕ) :
    ∫⁻ t in Ioc (n * τ : ℝ) ((n + 1) * τ), f (deGiorgiInterpolant τ V t) =
      ∫⁻ r in Ioc 0 (τ : ℝ), f (V n r) := by
  rw [setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ by
    rw [deGiorgiInterpolant_of_mem_Ioc hτ ht]]
  have h := (measurePreserving_add_right volume (n * τ : ℝ)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (n * τ : ℝ)) (fun t ↦ f (V n (t - n * τ)))
    (Ioc (n * τ : ℝ) ((n + 1) * τ))
  rw [← h, preimage_add_const_Ioc]
  simp only [add_sub_cancel_right, sub_self]
  rw [show ((n : ℝ) + 1) * τ - n * τ = τ by ring]

end Interpolant

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {φ : X → EReal} {τ : ℝ≥0} {U : ℕ → X}
  {V : ℕ → ℝ → X}

/-- On the time interval `(n τ, (n + 1) τ]`, the variational interpolant of a family of resolvent
steps `V n r ∈ J_r (U n)` is the resolvent step of time `t - n τ` from `U n`. -/
theorem deGiorgiInterpolant_mem_moreauYosidaResolvent (hτ : 0 < τ) {n : ℕ}
    (hV : ∀ r ∈ Ioc 0 (τ : ℝ), V n r ∈ moreauYosidaResolvent φ r.toNNReal (U n))
    {t : ℝ} (ht : t ∈ Ioc (n * τ : ℝ) ((n + 1) * τ)) :
    deGiorgiInterpolant τ V t ∈ moreauYosidaResolvent φ (t - n * τ).toNNReal (U n) := by
  rw [deGiorgiInterpolant_of_mem_Ioc hτ ht]
  exact hV _ ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **Existence of a variational selection.** If every resolvent `J_r (U n)` with `0 < r < τ` is
nonempty, then there are resolvent steps `V n r ∈ J_r (U n)` for all `r ∈ (0, τ]` with
`V n τ = U (n + 1)`, provided `U` is a minimizing movement sequence with time step `τ`. -/
theorem exists_forall_mem_moreauYosidaResolvent_and_eq
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hJ : ∀ n, ∀ r ∈ Ioo 0 (τ : ℝ), (moreauYosidaResolvent φ r.toNNReal (U n)).Nonempty) :
    ∃ V : ℕ → ℝ → X, (∀ n, ∀ r ∈ Ioc 0 (τ : ℝ), V n r ∈ moreauYosidaResolvent φ r.toNNReal (U n)) ∧
      ∀ n, V n τ = U (n + 1) := by
  classical
  refine ⟨fun n r ↦ if hr : r ∈ Ioo 0 (τ : ℝ) then (hJ n r hr).some else U (n + 1),
    fun n r hr ↦ ?_, fun n ↦ by simp⟩
  rcases hr.2.lt_or_eq with hrτ | rfl
  · simpa [hr.1, hrτ] using (hJ n r ⟨hr.1, hrτ⟩).some_mem
  · simpa using hU n

/-- **Energy along the variational interpolant.** On the time interval `(n τ, (n + 1) τ]`, the
variational interpolant has energy at most `φ (U n)`. -/
theorem apply_deGiorgiInterpolant_le (hτ : 0 < τ) {n : ℕ}
    (hV : ∀ r ∈ Ioc 0 (τ : ℝ), V n r ∈ moreauYosidaResolvent φ r.toNNReal (U n))
    {t : ℝ} (ht : t ∈ Ioc (n * τ : ℝ) ((n + 1) * τ)) :
    φ (deGiorgiInterpolant τ V t) ≤ φ (U n) :=
  apply_le_of_mem_moreauYosidaResolvent (deGiorgiInterpolant_mem_moreauYosidaResolvent hτ hV ht)

/-- **Distance along the variational interpolant.** On the time interval `(n τ, (n + 1) τ]`, the
variational interpolant of a selection with `V n τ = U (n + 1)` stays within distance
`d(U n, U (n + 1))` of `U n`, provided `φ (U n) ≠ ⊤` and `φ (U (n + 1)) ≠ ⊥`. -/
theorem edist_deGiorgiInterpolant_le (hτ : 0 < τ) {n : ℕ}
    (hV : ∀ r ∈ Ioc 0 (τ : ℝ), V n r ∈ moreauYosidaResolvent φ r.toNNReal (U n))
    (hVU : V n τ = U (n + 1)) (hn : φ (U n) ≠ ⊤) (hn' : φ (U (n + 1)) ≠ ⊥) {t : ℝ}
    (ht : t ∈ Ioc (n * τ : ℝ) ((n + 1) * τ)) :
    edist (U n) (deGiorgiInterpolant τ V t) ≤ edist (U n) (U (n + 1)) := by
  rw [deGiorgiInterpolant_of_mem_Ioc hτ ht]
  have hU : U (n + 1) ∈ moreauYosidaResolvent φ τ (U n) := by
    simpa [hVU] using hV τ ⟨NNReal.coe_pos.2 hτ, le_rfl⟩
  have hr : t - n * τ ∈ Ioc 0 (τ : ℝ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rcases hr.2.lt_or_eq with hrτ | hrτ
  · -- A shorter resolvent step goes less far.
    have hr₀ : 0 < (t - n * τ).toNNReal := Real.toNNReal_pos.2 hr.1
    have hrτ' : (t - n * τ).toNNReal < τ := by
      rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1.le]
    have hy := hV _ hr
    refine edist_le_edist_of_mem_moreauYosidaResolvent hr₀ hrτ' hy hU
      (ne_bot_of_le_ne_bot hn' (apply_le_apply_of_mem_moreauYosidaResolvent hr₀ hrτ' hy hU))
      (ne_top_of_le_ne_top hn (moreauYosida_le_self φ _ _))
  · rw [hrτ, hVU]

end PseudoEMetricSpace

section EMetricSpace

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {τ : ℝ≥0} {U : ℕ → X} {V : ℕ → ℝ → X}

/-- **Discrete energy–dissipation inequality** (compare Ambrosio–Gigli–Savaré, Lemma 3.2.2).
Let `U` be a minimizing movement sequence for `φ` with time step `τ > 0`, and let
`V n r ∈ J_r (U n)` be resolvent steps for every `r ∈ (0, τ]`. Then, with `W` the variational
interpolant `deGiorgiInterpolant τ V`, for every `N`

`φ (U N) + ∑_{n < N} d(U n, U (n + 1))² / (2τ) + ∫₀^{Nτ} |∂φ|²(W t) / 2 dt ≤ φ (U 0)`,

where `|∂φ|` is the descending slope. -/
theorem apply_add_sum_add_lintegral_descendingSlope_le_of_forall_mem_moreauYosidaResolvent
    (hτ : 0 < τ) (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ n, ∀ r ∈ Ioc 0 (τ : ℝ), V n r ∈ moreauYosidaResolvent φ r.toNNReal (U n)) (N : ℕ) :
    φ (U N) + (∑ n ∈ Finset.range N, edist (U n) (U (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) +
      ((∫⁻ t in Ioc 0 (N * τ : ℝ), descendingSlope φ (deGiorgiInterpolant τ V t) ^ 2 / 2 :
        ℝ≥0∞) : EReal) ≤ φ (U 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    set f : ℝ → ℝ≥0∞ := fun t ↦ descendingSlope φ (deGiorgiInterpolant τ V t) ^ 2 / 2
    -- Split off the last step and the last time interval `(N τ, (N + 1) τ]`.
    have hsplit : ∫⁻ t in Ioc 0 ((N + 1 : ℕ) * τ : ℝ), f t =
        (∫⁻ t in Ioc 0 (N * τ : ℝ), f t) + ∫⁻ r in Ioc 0 (τ : ℝ),
          descendingSlope φ (V N r) ^ 2 / 2 := by
      have hNτ : (0 : ℝ) ≤ N * τ := by positivity
      rw [Nat.cast_succ, ← Ioc_union_Ioc_eq_Ioc hNτ (by gcongr; linarith),
        lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
        setLIntegral_deGiorgiInterpolant hτ (fun x ↦ descendingSlope φ x ^ 2 / 2) N]
    calc φ (U (N + 1)) + ((∑ n ∈ Finset.range (N + 1),
            edist (U n) (U (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) : EReal) +
          ((∫⁻ t in Ioc 0 ((N + 1 : ℕ) * τ : ℝ), f t : ℝ≥0∞) : EReal)
        = (φ (U (N + 1)) + (edist (U N) (U (N + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) +
            ((∫⁻ r in Ioc 0 (τ : ℝ), descendingSlope φ (V N r) ^ 2 / 2 : ℝ≥0∞) : EReal)) +
            (∑ n ∈ Finset.range N, edist (U n) (U (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) +
            ((∫⁻ t in Ioc 0 (N * τ : ℝ), f t : ℝ≥0∞) : EReal) := by
          rw [Finset.sum_range_succ, hsplit, EReal.coe_ennreal_add, EReal.coe_ennreal_add]
          ac_rfl
      _ ≤ φ (U N) + (∑ n ∈ Finset.range N, edist (U n) (U (n + 1)) ^ 2 / (2 * τ) : ℝ≥0∞) +
            ((∫⁻ t in Ioc 0 (N * τ : ℝ), f t : ℝ≥0∞) : EReal) := by
          gcongr
          exact apply_add_add_lintegral_descendingSlope_le hτ (hU N) (hV N)
      _ ≤ φ (U 0) := ih

end EMetricSpace

end TauCeti
