/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpectralFlow.Window
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# Spectral flow of a path of self-adjoint operators

Let `A : ℝ → E →L[ℂ] E` be a family of bounded self-adjoint operators on a complex Hilbert space,
continuous on `[a, b]`, with a spectral window (`ContinuousLinearMap.IsSpectralWindow`) at every
time. The **spectral flow** `TauCeti.spectralFlow A a b` is the net number of eigenvalues of `A t`
crossing `0` from below as `t` runs from `a` to `b`, counted with multiplicity: an eigenvalue
moving from negative to nonnegative counts `+1`, one moving from nonnegative to negative counts
`-1`.

Phillips defines it through a partition `a = t₀ < ⋯ < tₙ = b` and windows `rᵢ` valid on
`[tᵢ₋₁, tᵢ]`, as `∑ᵢ (N_{rᵢ}(tᵢ) - N_{rᵢ}(tᵢ₋₁))`, where `N_r(t)` is the number of eigenvalues
of `A t` in `[0, r)`. Here the partition is replaced by a **potential**
(`TauCeti.IsSpectralFlowPotential`): an integer-valued function `F` such that near every time,
`F - N_r` is constant for a window `r` there. Phillips' sum telescopes to `F b - F a` for the
potential that is `N_{rᵢ}` up to a constant on each piece. Potentials exist
(`TauCeti.exists_isSpectralFlowPotential`): locally a single window works, and potentials on
adjacent intervals glue (`TauCeti.IsSpectralFlowPotential.glue`). They are unique up to a constant
(`TauCeti.IsSpectralFlowPotential.sub_eq_sub`), because the counts of two windows of the same
operator differ by a locally constant amount
(`ContinuousLinearMap.IsSpectralWindow.eventually_spectralRank_sub_eq`). So the spectral flow
`F b - F a` does not depend on the choices.

## Main results

* `TauCeti.IsSpectralFlowPotential.spectralFlow_eq`: the spectral flow is computed by any
  potential.
* `TauCeti.spectralFlow_eq_of_isSpectralWindow`: over an interval with a single window `r`, the
  spectral flow is the change in the number of eigenvalues in `[0, r)`.
* `TauCeti.spectralFlow_add`: the spectral flow is additive under concatenation of intervals.

The scalar path `tanh t` crosses `0` upwards once and has spectral flow `1` on `[-1, 1]`; this is
checked at the end of the file.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460–467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33.
-/

public section

open Set Filter Topology

namespace TauCeti

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℝ → E →L[ℂ] E} {s : Set ℝ}

/-- A **spectral flow potential** of a family `A` of operators on a set `s ⊆ ℝ` is a function
`F : ℝ → ℤ` such that near every `t ∈ s`, `F` differs by a constant from the number of eigenvalues
of `A` in `[0, r)`, for some spectral window `r` of `A t`. -/
def IsSpectralFlowPotential (A : ℝ → E →L[ℂ] E) (s : Set ℝ) (F : ℝ → ℤ) : Prop :=
  ∀ t ∈ s, ∃ r, IsSpectralWindow (A t) r ∧
    ∀ᶠ u in 𝓝[s] t, F u - spectralRank (A u) (Ico 0 r) = F t - spectralRank (A t) (Ico 0 r)

namespace IsSpectralFlowPotential

variable {F G : ℝ → ℤ}

/-- A family with a potential on `s` is self-adjoint on `s`. -/
theorem isSelfAdjoint (hF : IsSpectralFlowPotential A s F) {t : ℝ} (ht : t ∈ s) :
    IsSelfAdjoint (A t) :=
  (hF t ht).choose_spec.1.isSelfAdjoint

/-- A potential on `s` is a potential on every subset of `s`. -/
theorem mono (hF : IsSpectralFlowPotential A s F) {s' : Set ℝ} (hs : s' ⊆ s) :
    IsSpectralFlowPotential A s' F := fun t ht ↦
  let ⟨r, hr, hev⟩ := hF t (hs ht)
  ⟨r, hr, hev.filter_mono (nhdsWithin_mono t hs)⟩

/-- A potential differs locally by a constant from the eigenvalue count of *every* spectral window,
not only from that of the window in its definition. -/
theorem eventually_sub_eq (hF : IsSpectralFlowPotential A s F) (hA : ContinuousOn A s)
    {t r : ℝ} (ht : t ∈ s) (hr : IsSpectralWindow (A t) r) :
    ∀ᶠ u in 𝓝[s] t, F u - spectralRank (A u) (Ico 0 r) = F t - spectralRank (A t) (Ico 0 r) := by
  obtain ⟨r₀, hr₀, hev⟩ := hF t ht
  have hsa : ∀ᶠ u in 𝓝[s] t, IsSelfAdjoint (A u) :=
    eventually_mem_nhdsWithin.mono fun u hu ↦ hF.isSelfAdjoint hu
  filter_upwards [hev, hr₀.eventually_spectralRank_sub_eq hr (hA t ht) hsa] with u hu hu'
  linarith

/-- **Uniqueness of potentials.** On a preconnected set, two potentials of a continuous family
differ by a constant. -/
theorem sub_eq_sub (hF : IsSpectralFlowPotential A s F) (hG : IsSpectralFlowPotential A s G)
    (hs : IsPreconnected s) (hA : ContinuousOn A s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    F x - G x = F y - G y := by
  refine hs.induction₂ (fun x y ↦ F x - G x = F y - G y) (fun t ht ↦ ?_)
    (fun _ _ _ _ _ _ h h' ↦ h.trans h') (fun _ _ _ _ h ↦ h.symm) hx hy
  obtain ⟨r, hr, hev⟩ := hF t ht
  filter_upwards [hev, hG.eventually_sub_eq hA ht hr] with u hu hu'
  linarith

/-- Two potentials of a continuous family on adjacent closed intervals glue to a potential on
their union, after shifting the second by a constant to match at the common endpoint. -/
theorem glue {a b c : ℝ} (hF : IsSpectralFlowPotential A (Icc a b) F)
    (hG : IsSpectralFlowPotential A (Icc b c) G) (hA : ContinuousOn A (Icc b c))
    (hab : a ≤ b) (hbc : b ≤ c) :
    IsSpectralFlowPotential A (Icc a c)
      (fun u ↦ if u ≤ b then F u else G u + (F b - G b)) := by
  intro t ht
  rcases lt_trichotomy t b with htb | rfl | hbt
  · -- Left of the junction, the glued function is `F`.
    obtain ⟨r, hr, hev⟩ := hF t ⟨ht.1, htb.le⟩
    refine ⟨r, hr, ?_⟩
    have hle : 𝓝[Icc a c] t ≤ 𝓝[Icc a b] t := nhdsWithin_le_of_mem <| mem_nhdsWithin.2
      ⟨Iio b, isOpen_Iio, htb, fun u ⟨hu, hu'⟩ ↦ ⟨hu'.1, le_of_lt hu⟩⟩
    filter_upwards [hle hev, hle (eventually_mem_nhdsWithin.mono fun u hu ↦ hu.2)]
      with u hu hub
    simpa [hub, htb.le] using hu
  · -- At the junction, compare `G` with the window of `F` at `b`.
    obtain ⟨r, hr, hev⟩ := hF t ⟨ht.1, le_rfl⟩
    refine ⟨r, hr, ?_⟩
    have hev' := hG.eventually_sub_eq hA ⟨le_rfl, hbc⟩ hr
    rw [← Icc_union_Icc_eq_Icc hab hbc, nhdsWithin_union]
    refine Filter.eventually_sup.2 ⟨?_, ?_⟩
    · filter_upwards [hev, eventually_mem_nhdsWithin] with u hu hu'
      simpa [hu'.2] using hu
    · filter_upwards [hev', eventually_mem_nhdsWithin] with u hu hu'
      rcases hu'.1.eq_or_lt with rfl | htu
      · simp
      · simp only [not_le.2 htu, le_refl, ite_true, ite_false]
        linarith
  · -- Right of the junction, the glued function is `G` up to a constant.
    obtain ⟨r, hr, hev⟩ := hG t ⟨hbt.le, ht.2⟩
    refine ⟨r, hr, ?_⟩
    have hle : 𝓝[Icc a c] t ≤ 𝓝[Icc b c] t := nhdsWithin_le_of_mem <| mem_nhdsWithin.2
      ⟨Ioi b, isOpen_Ioi, hbt, fun u ⟨hu, hu'⟩ ↦ ⟨le_of_lt hu, hu'.2⟩⟩
    filter_upwards [hle hev, nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hbt)] with u hu hbu
    simp only [not_le.2 hbt, not_le.2 (mem_Ioi.1 hbu), ite_false]
    linarith

end IsSpectralFlowPotential

/-- **Existence of potentials.** A family of operators that is continuous on `[a, b]` and has a
spectral window at every point has a potential there. -/
theorem exists_isSpectralFlowPotential {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hw : ∀ t ∈ Icc a b, ∃ r, IsSpectralWindow (A t) r) :
    ∃ F, IsSpectralFlowPotential A (Icc a b) F := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨0, fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.2 hba)⟩
  refine isPreconnected_Icc.induction₂'
    (fun x y ↦ x ≤ y → ∃ F, IsSpectralFlowPotential A (Icc x y) F) (fun x hx ↦ ?_)
    (fun x y z hx hy hz hxy hyz hxz ↦ ?_) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  · -- Near `x`, a single window works, and its eigenvalue count is a potential.
    obtain ⟨r, hr⟩ := hw x hx
    have hsa : ∀ᶠ u in 𝓝[Icc a b] x, IsSelfAdjoint (A u) :=
      eventually_mem_nhdsWithin.mono fun u hu ↦ (hw u hu).choose_spec.isSelfAdjoint
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hr.eventually (hA x hx) hsa)
    have hloc {y : ℝ} (hy : y ∈ Metric.ball x ε) (hyI : y ∈ Icc a b) {p q : ℝ}
        (hpq : Icc p q ⊆ uIcc x y) : ∃ F, IsSpectralFlowPotential A (Icc p q) F := by
      refine ⟨fun u ↦ spectralRank (A u) (Ico 0 r), fun t ht ↦ ⟨r, hball ⟨?_, ?_⟩, by simp⟩⟩
      · exact Metric.mem_ball.2 <| (dist_comm t x ▸ Real.dist_left_le_of_mem_uIcc (hpq ht)).trans_lt
          (Metric.mem_ball'.1 hy)
      · exact uIcc_subset_Icc hx hyI (hpq ht)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε),
      eventually_mem_nhdsWithin] with y hy hyI
    exact ⟨fun hxy ↦ hloc hy hyI (Icc_subset_uIcc), fun hyx ↦ hloc hy hyI (Icc_subset_uIcc')⟩
  · -- Potentials on adjacent intervals glue; on nested intervals they restrict.
    rcases le_total x y with hxy' | hyx
    · rcases le_total y z with hyz' | hzy
      · obtain ⟨F, hF⟩ := hxy hxy'
        obtain ⟨G, hG⟩ := hyz hyz'
        exact ⟨_, hF.glue hG (hA.mono (Icc_subset_Icc hy.1 hz.2)) hxy' hyz'⟩
      · obtain ⟨F, hF⟩ := hxy hxy'
        exact ⟨F, hF.mono (Icc_subset_Icc le_rfl hzy)⟩
    · obtain ⟨G, hG⟩ := hyz (hyx.trans hxz)
      exact ⟨G, hG.mono (Icc_subset_Icc hyx le_rfl)⟩

open scoped Classical in
/-- The **spectral flow** of a family `A` of self-adjoint operators over `[a, b]`: the net number
of eigenvalues crossing `0` from below, `F b - F a` for any potential `F` of `A` on `[a, b]`. It is
well defined for continuous families with a spectral window at every point; it is `0` when no
potential exists or `b < a`. -/
noncomputable def spectralFlow (A : ℝ → E →L[ℂ] E) (a b : ℝ) : ℤ :=
  if h : a ≤ b ∧ ∃ F, IsSpectralFlowPotential A (Icc a b) F then
    h.2.choose b - h.2.choose a else 0

/-- The spectral flow is computed by any potential. -/
theorem IsSpectralFlowPotential.spectralFlow_eq {F : ℝ → ℤ} {a b : ℝ}
    (hF : IsSpectralFlowPotential A (Icc a b) F) (hA : ContinuousOn A (Icc a b)) (hab : a ≤ b) :
    spectralFlow A a b = F b - F a := by
  unfold spectralFlow
  split_ifs with h
  · have := h.2.choose_spec.sub_eq_sub hF isPreconnected_Icc hA (right_mem_Icc.2 hab)
      (left_mem_Icc.2 hab)
    linarith
  · exact absurd ⟨hab, F, hF⟩ h

/-- Over an interval on which a single `r` is a spectral window throughout, the spectral flow is
the change in the number of eigenvalues in `[0, r)`. -/
theorem spectralFlow_eq_of_isSpectralWindow {a b r : ℝ} (hA : ContinuousOn A (Icc a b))
    (hr : ∀ t ∈ Icc a b, IsSpectralWindow (A t) r) (hab : a ≤ b) :
    spectralFlow A a b = spectralRank (A b) (Ico 0 r) - spectralRank (A a) (Ico 0 r) :=
  IsSpectralFlowPotential.spectralFlow_eq (F := fun u ↦ spectralRank (A u) (Ico 0 r))
    (fun t ht ↦ ⟨r, hr t ht, by simp⟩) hA hab

/-- The spectral flow over a degenerate interval vanishes. -/
@[simp]
theorem spectralFlow_self (A : ℝ → E →L[ℂ] E) (a : ℝ) : spectralFlow A a a = 0 := by
  unfold spectralFlow
  split_ifs <;> simp

/-- **Concatenation.** The spectral flow over `[a, c]` is the sum of the flows over `[a, b]` and
`[b, c]`. -/
theorem spectralFlow_add {a b c : ℝ} (hA : ContinuousOn A (Icc a c))
    (hw : ∀ t ∈ Icc a c, ∃ r, IsSpectralWindow (A t) r) (hab : a ≤ b) (hbc : b ≤ c) :
    spectralFlow A a c = spectralFlow A a b + spectralFlow A b c := by
  obtain ⟨F, hF⟩ := exists_isSpectralFlowPotential hA hw
  have hab' : Icc a b ⊆ Icc a c := Icc_subset_Icc le_rfl hbc
  have hbc' : Icc b c ⊆ Icc a c := Icc_subset_Icc hab le_rfl
  rw [hF.spectralFlow_eq hA (hab.trans hbc), (hF.mono hab').spectralFlow_eq (hA.mono hab') hab,
    (hF.mono hbc').spectralFlow_eq (hA.mono hbc') hbc]
  ring

end TauCeti

/-! ### An upward crossing -/

open ContinuousLinearMap in
/-- The scalar path `tanh s` crosses `0` upwards once on `[-1, 1]`, so its spectral flow is `1`. -/
example : TauCeti.spectralFlow (fun t ↦ algebraMap ℝ (ℂ →L[ℂ] ℂ) (Real.tanh t)) (-1) 1 = 1 := by
  classical
  have h₁ : Real.tanh 1 ∈ Ico (0 : ℝ) 1 := ⟨Real.tanh_nonneg zero_le_one, Real.tanh_lt_one 1⟩
  have h₂ : Real.tanh (-1) ∉ Ico (0 : ℝ) 1 := fun h ↦
    (Real.tanh_neg_iff.2 (by norm_num : (-1 : ℝ) < 0)).not_ge h.1
  rw [TauCeti.spectralFlow_eq_of_isSpectralWindow (r := 1)
    (A := fun t ↦ algebraMap ℝ (ℂ →L[ℂ] ℂ) (Real.tanh t))
    ((continuous_algebraMap ℝ _).comp Real.continuous_tanh).continuousOn
    (fun t _ ↦ isSpectralWindow_algebraMap (abs_lt.2 ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩))
    (by norm_num), spectralRank_algebraMap, spectralRank_algebraMap]
  simp only [h₁, h₂, ↓reduceIte, Module.finrank_self]
  norm_num
