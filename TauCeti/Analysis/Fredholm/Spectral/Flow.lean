/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Projection
public import TauCeti.Analysis.InnerProductSpace.Spectral.FiniteRank
import TauCeti.Topology.Algebra.Indicator

/-!
# The spectral flow of a path of self-adjoint Fredholm operators

Let `A : ℝ → (H →L[𝕜] H)` be a continuous path of self-adjoint Fredholm operators on a real or
complex Hilbert space `H`, over an interval `[a, b]`. Its **spectral flow** is the net number of
eigenvalues of `A t` that cross `0` from negative to positive as `t` runs from `a` to `b`. This file
constructs it following Phillips.

**Local counts.** A number `c > 0` is a *spectral cut* of `A` on a set `s` of times
(`TauCeti.IsSpectralCutOn`) if for every `u ∈ s` neither `-c` nor `c` is in the spectrum of `A u`
and the spectral projection of `A u` for `[-c, c]` has finite rank. Then the spectrum of `A u`
meets `[-c, c]` in finitely many eigenvalues of finite multiplicity, and
`TauCeti.spectralCount c (A u)`, the rank of the spectral projection for `[0, c]`, counts those in
`[0, c]`. Along an interval `[s, t]` with a cut `c`, the change
`spectralCount c (A t) - spectralCount c (A s)` is the net number of eigenvalues crossing `0`
upwards: none cross `±c`. It does not depend on the cut
(`TauCeti.IsSpectralCutOn.spectralCount_sub_spectralCount_eq`): for cuts `c' ≤ c`, the counts differ
by the rank of the spectral projection for `(c', c]`, whose frontier avoids every spectrum along
`[s, t]`, so this rank is constant. Near a self-adjoint Fredholm operator there is a cut
(`IsSelfAdjoint.exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm`), so every
time has a neighbourhood with a cut (`TauCeti.exists_isSpectralCutOn_ball_inter_Icc`).

**Gluing the local counts.** A *spectral flow potential* (`TauCeti.IsSpectralFlowPotential`) is an
integer function `F` on `[a, b]` whose increment over every subinterval `[s, t]` with a cut `c` is
`spectralCount c (A t) - spectralCount c (A s)`. Potentials exist
(`TauCeti.exists_isSpectralFlowPotential`): by the Lebesgue number lemma, all short enough
subintervals have cuts, and summing the local counts along a fixed grid gives a potential. Two
potentials differ by a locally constant, hence constant, function on `[a, b]`
(`TauCeti.IsSpectralFlowPotential.sub_eq_sub`). For `a ≤ b`, the spectral flow
`TauCeti.spectralFlow A a b` is `F b - F a` for any potential `F`. For `b < a` every function is
vacuously a potential, and the spectral flow is a junk value.

Phillips' definition is recovered as the partition formula `TauCeti.spectralFlow_eq_sum`: for any
partition `a = t₀ ≤ t₁ ≤ ⋯ ≤ tₙ = b` with a cut `cₖ` on each `[tₖ, tₖ₊₁]`, the spectral flow is the
sum of the local counts, whatever the partition and the cuts. Spectral flow is additive under
concatenation (`TauCeti.spectralFlow_add_adjacent_intervals`) and changes sign when the path is
reversed (`TauCeti.spectralFlow_comp_neg`). For the path `t ↦ t • 1` on a finite-dimensional
space, through `0` from `a < 0` to `b ≥ 0`, every eigenvalue crosses upwards once and the spectral
flow is the dimension (`TauCeti.spectralFlow_algebraMap`). This is the sign convention in which
positive crossings count positively.

## Main definitions

* `TauCeti.IsSpectralCutOn A c s`: `c` is a spectral cut of `A` at every time of `s`.
* `TauCeti.spectralCount c T`: the rank of the spectral projection of `T` for `[0, c]`.
* `TauCeti.IsSpectralFlowPotential A a b F`: `F` integrates the local counts on `[a, b]`.
* `TauCeti.spectralFlow A a b`: the spectral flow of `A` from `a` to `b`.

## Main results

* `TauCeti.IsSpectralCutOn.spectralCount_sub_spectralCount_eq`: the local count does not depend on
  the cut.
* `TauCeti.exists_isSpectralFlowPotential`, `TauCeti.IsSpectralFlowPotential.sub_eq_sub`: existence
  and uniqueness of potentials.
* `TauCeti.spectralFlow_eq_sum`: Phillips' partition formula.
* `TauCeti.spectralFlow_eq_of_isSpectralCutOn`: the spectral flow over an interval with a single
  cut.
* `TauCeti.spectralFlow_add_adjacent_intervals`, `TauCeti.spectralFlow_comp_neg`: concatenation
  and reversal.
* `TauCeti.spectralFlow_algebraMap`: the path `t ↦ t • 1` through `0`.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Filter Metric Set Topology

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace TauCeti

/-! ### Spectral cuts and local counts -/

/-- `c` is a **spectral cut** of the path `A` on the set `s` of times: `c > 0`, and for every
`u ∈ s` neither `-c` nor `c` is in the spectrum of `A u`, and the spectral projection of `A u` for
`[-c, c]` has finite rank. -/
def IsSpectralCutOn (A : ℝ → H →L[𝕜] H) (c : ℝ) (s : Set ℝ) : Prop :=
  0 < c ∧ ∀ u ∈ s, -c ∉ spectrum ℝ (A u) ∧ c ∉ spectrum ℝ (A u) ∧
    FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A u)).range

/-- The number of eigenvalues of `T` in `[0, c]`, counted with multiplicity: the rank of the
spectral projection of `T` for `[0, c]`. When `c` is a spectral cut of `T`, the indicator of
`[0, c]` is continuous on the spectrum and this rank is finite. -/
noncomputable def spectralCount (c : ℝ) (T : H →L[𝕜] H) : ℕ :=
  Module.finrank 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) T).range

/-- Unfolds `TauCeti.spectralCount` to the rank of the spectral projection for `[0, c]`. -/
theorem spectralCount_def (c : ℝ) (T : H →L[𝕜] H) :
    spectralCount c T = Module.finrank 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) T).range :=
  (rfl)

variable {A : ℝ → H →L[𝕜] H} {c : ℝ} {s t : Set ℝ}

/-- Unfolds `TauCeti.IsSpectralCutOn`. -/
theorem isSpectralCutOn_iff : IsSpectralCutOn A c s ↔ 0 < c ∧ ∀ u ∈ s,
    -c ∉ spectrum ℝ (A u) ∧ c ∉ spectrum ℝ (A u) ∧
      FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A u)).range :=
  Iff.rfl

/-- A spectral cut is positive. -/
theorem IsSpectralCutOn.pos (h : IsSpectralCutOn A c s) : 0 < c := h.1

/-- At a time of a spectral cut `c`, `-c` is not in the spectrum. -/
theorem IsSpectralCutOn.neg_notMem_spectrum (h : IsSpectralCutOn A c s) {u : ℝ} (hu : u ∈ s) :
    -c ∉ spectrum ℝ (A u) :=
  (h.2 u hu).1

/-- At a time of a spectral cut `c`, `c` is not in the spectrum. -/
theorem IsSpectralCutOn.notMem_spectrum (h : IsSpectralCutOn A c s) {u : ℝ} (hu : u ∈ s) :
    c ∉ spectrum ℝ (A u) :=
  (h.2 u hu).2.1

/-- At a time of a spectral cut `c`, the spectral projection for `[-c, c]` has finite rank. -/
theorem IsSpectralCutOn.finiteDimensional_range_cfc_indicator_Icc (h : IsSpectralCutOn A c s)
    {u : ℝ} (hu : u ∈ s) :
    FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A u)).range :=
  (h.2 u hu).2.2

/-- A spectral cut on a set of times is a spectral cut on every subset. -/
theorem IsSpectralCutOn.mono (h : IsSpectralCutOn A c s) (hts : t ⊆ s) : IsSpectralCutOn A c t :=
  ⟨h.1, fun u hu ↦ h.2 u (hts hu)⟩

/-- A spectral cut of the reversed path `t ↦ A (-t)` on `[s, t]` is a spectral cut of `A` on
`[-t, -s]`. -/
theorem IsSpectralCutOn.of_comp_neg {s t : ℝ} (h : IsSpectralCutOn (fun u ↦ A (-u)) c (Icc s t)) :
    IsSpectralCutOn A c (Icc (-t) (-s)) := by
  refine ⟨h.1, fun u hu ↦ ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w, u = -w := ⟨-u, (neg_neg u).symm⟩
  exact h.2 w ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- `F` is a **spectral flow potential** of the path `A` on `[a, b]`: over every subinterval
`[s, t]` of `[a, b]` on which `A` has a spectral cut `c`, the increment of `F` is the change of the
number of eigenvalues in `[0, c]`. -/
def IsSpectralFlowPotential (A : ℝ → H →L[𝕜] H) (a b : ℝ) (F : ℝ → ℤ) : Prop :=
  ∀ ⦃s t c : ℝ⦄, a ≤ s → s ≤ t → t ≤ b → IsSpectralCutOn A c (Icc s t) →
    F t - F s = (spectralCount c (A t) : ℤ) - spectralCount c (A s)

/-- Unfolds `TauCeti.IsSpectralFlowPotential`. -/
theorem isSpectralFlowPotential_iff {a b : ℝ} {F : ℝ → ℤ} :
    IsSpectralFlowPotential A a b F ↔ ∀ ⦃s t c : ℝ⦄, a ≤ s → s ≤ t → t ≤ b →
      IsSpectralCutOn A c (Icc s t) →
        F t - F s = (spectralCount c (A t) : ℤ) - spectralCount c (A s) :=
  Iff.rfl

/-- The increment of a spectral flow potential over a subinterval `[s, t]` with a spectral cut `c`
is the change of the number of eigenvalues in `[0, c]`. -/
theorem IsSpectralFlowPotential.sub_eq {a b s t : ℝ} {F : ℝ → ℤ}
    (hF : IsSpectralFlowPotential A a b F) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hc : IsSpectralCutOn A c (Icc s t)) :
    F t - F s = (spectralCount c (A t) : ℤ) - spectralCount c (A s) :=
  hF has hst htb hc

/-- A spectral flow potential on `[a, b]` is a spectral flow potential on every subinterval. -/
theorem IsSpectralFlowPotential.mono {a b a' b' : ℝ} {F : ℝ → ℤ}
    (hF : IsSpectralFlowPotential A a b F) (ha : a ≤ a') (hb : b' ≤ b) :
    IsSpectralFlowPotential A a' b' F :=
  fun _ _ _ hs hst ht hc ↦ hF (ha.trans hs) hst (ht.trans hb) hc

open scoped Classical in
/-- The **spectral flow** of the path `A` from `a` to `b`: the increment `F b - F a` of a spectral
flow potential `F` of `A` on `[a, b]`. For `a ≤ b` and a continuous path of self-adjoint Fredholm
operators on `[a, b]`, potentials exist and all give the same value (`TauCeti.spectralFlow_eq_sub`);
it is the net number of eigenvalues crossing `0` upwards. Otherwise it is a junk value: in
particular, for `b < a` every function is vacuously a potential, so the value is arbitrary and need
not be `-spectralFlow A b a`. -/
noncomputable def spectralFlow (A : ℝ → H →L[𝕜] H) (a b : ℝ) : ℤ :=
  if h : ∃ F, IsSpectralFlowPotential A a b F then h.choose b - h.choose a else 0

/-- The spectral flow over a single time vanishes. -/
@[simp]
theorem spectralFlow_self (A : ℝ → H →L[𝕜] H) (a : ℝ) : spectralFlow A a a = 0 := by
  unfold spectralFlow
  split_ifs <;> simp

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

section Single

variable {S : H →L[𝕜] H}

/-- The frontier of `[-c, c]` avoids a set containing neither `-c` nor `c`. -/
private theorem disjoint_frontier_Icc {c : ℝ} {X : Set ℝ} (hc : 0 ≤ c) (h₁ : -c ∉ X)
    (h₂ : c ∉ X) : Disjoint (frontier (Icc (-c) c)) X := by
  rw [frontier_Icc (by linarith), disjoint_left]
  rintro x (rfl | rfl)
  exacts [h₁, h₂]

/-- The frontier of `(c', c]` avoids a set containing neither `c'` nor `c`. -/
private theorem disjoint_frontier_Ioc {c' c : ℝ} {X : Set ℝ} (hcc : c' < c) (h₁ : c' ∉ X)
    (h₂ : c ∉ X) : Disjoint (frontier (Ioc c' c)) X := by
  rw [frontier_Ioc hcc, disjoint_left]
  rintro x (rfl | rfl)
  exacts [h₁, h₂]

variable (hS : IsSelfAdjoint S) (hc : 0 ≤ c) (h₁ : -c ∉ spectrum ℝ S) (h₂ : c ∉ spectrum ℝ S)
  (hfd : FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range)
include hS hc h₁ h₂ hfd

/-- At a cut `c`, the indicator of `[0, c]` is continuous on the spectrum, since the spectrum
meets `[-c, c]` in finitely many points. -/
private theorem continuousOn_indicator_Icc_zero :
    ContinuousOn ((Icc 0 c).indicator (1 : ℝ → ℝ)) (spectrum ℝ S) :=
  Set.Finite.continuousOn_indicator
    (hS.finite_spectrum_inter_of_finiteDimensional_range_cfc_indicator
      (continuousOn_const.continuousOn_indicator_of_disjoint_frontier
        (disjoint_frontier_Icc hc h₁ h₂)) hfd)
    (Icc_subset_Icc (by linarith) le_rfl) (disjoint_frontier_Icc hc h₁ h₂)

/-- At a cut `c`, the spectral projection for `[0, c]` has finite rank. -/
private theorem finiteDimensional_range_cfc_indicator_Icc_zero :
    FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) S).range :=
  Submodule.finiteDimensional_of_le (S.range_cfc_indicator_le_of_subset
    (Icc_subset_Icc (by linarith) le_rfl) (continuousOn_indicator_Icc_zero hS hc h₁ h₂ hfd)
    (continuousOn_const.continuousOn_indicator_of_disjoint_frontier
      (disjoint_frontier_Icc hc h₁ h₂)))

omit hc in
/-- For cuts `c' < c` of `S`, the count for `c` is the count for `c'` plus the rank of the spectral
projection for `(c', c]`. -/
private theorem spectralCount_eq_add {c' : ℝ} (hc' : 0 < c') (hcc : c' < c)
    (h₁' : -c' ∉ spectrum ℝ S) (h₂' : c' ∉ spectrum ℝ S)
    (hfd' : FiniteDimensional 𝕜 (cfc ((Icc (-c') c').indicator (1 : ℝ → ℝ)) S).range) :
    spectralCount c S =
      spectralCount c' S + Module.finrank 𝕜 (cfc ((Ioc c' c).indicator (1 : ℝ → ℝ)) S).range := by
  have hc : 0 ≤ c := by linarith
  have hcont : ContinuousOn ((Ioc c' c).indicator (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    continuousOn_const.continuousOn_indicator_of_disjoint_frontier
      (disjoint_frontier_Ioc hcc h₂' h₂)
  have := finiteDimensional_range_cfc_indicator_Icc_zero hS hc'.le h₁' h₂' hfd'
  have : FiniteDimensional 𝕜 (cfc ((Ioc c' c).indicator (1 : ℝ → ℝ)) S).range :=
    Submodule.finiteDimensional_of_le (S.range_cfc_indicator_le_of_subset (Ω' := Icc (-c) c)
      (fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩) hcont
      (continuousOn_const.continuousOn_indicator_of_disjoint_frontier
        (disjoint_frontier_Icc hc h₁ h₂)))
  rw [spectralCount_def, spectralCount_def, ← Icc_union_Ioc_eq_Icc hc'.le hcc.le]
  exact S.finrank_range_cfc_indicator_union
    (disjoint_left.2 fun x hx hx' ↦ (not_lt.2 hx.2) hx'.1)
    (continuousOn_indicator_Icc_zero hS hc'.le h₁' h₂' hfd') hcont

end Single

/-- At a time `u` of a spectral cut `c`, the indicator of `[0, c]` is continuous on the spectrum of
the self-adjoint operator `A u`. -/
theorem IsSpectralCutOn.continuousOn_indicator_Icc_zero (h : IsSpectralCutOn A c s) {u : ℝ}
    (hu : u ∈ s) (hsa : IsSelfAdjoint (A u)) :
    ContinuousOn ((Icc 0 c).indicator (1 : ℝ → ℝ)) (spectrum ℝ (A u)) :=
  TauCeti.continuousOn_indicator_Icc_zero hsa h.pos.le (h.neg_notMem_spectrum hu)
    (h.notMem_spectrum hu) (h.finiteDimensional_range_cfc_indicator_Icc hu)

/-- At a time `u` of a spectral cut `c`, the spectral projection of the self-adjoint operator `A u`
for `[0, c]` has finite rank, so `TauCeti.spectralCount c (A u)` is a genuine count. -/
theorem IsSpectralCutOn.finiteDimensional_range_cfc_indicator_Icc_zero (h : IsSpectralCutOn A c s)
    {u : ℝ} (hu : u ∈ s) (hsa : IsSelfAdjoint (A u)) :
    FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A u)).range :=
  TauCeti.finiteDimensional_range_cfc_indicator_Icc_zero hsa h.pos.le (h.neg_notMem_spectrum hu)
    (h.notMem_spectrum hu) (h.finiteDimensional_range_cfc_indicator_Icc hu)

/-- **The local count does not depend on the cut.** If `c` and `c'` are spectral cuts of a
continuous path of self-adjoint operators on `[s, t]`, the changes of the counts of eigenvalues in
`[0, c]` and in `[0, c']` from `s` to `t` agree. -/
theorem IsSpectralCutOn.spectralCount_sub_spectralCount_eq {s t c c' : ℝ} (hst : s ≤ t)
    (hA : ContinuousOn A (Icc s t)) (hsa : ∀ u ∈ Icc s t, IsSelfAdjoint (A u))
    (hc : IsSpectralCutOn A c (Icc s t)) (hc' : IsSpectralCutOn A c' (Icc s t)) :
    (spectralCount c (A t) : ℤ) - spectralCount c (A s) =
      (spectralCount c' (A t) : ℤ) - spectralCount c' (A s) := by
  wlog hcc : c' ≤ c generalizing c c'
  · exact (this hc' hc (le_of_not_ge hcc)).symm
  rcases hcc.lt_or_eq with hcc | rfl
  · -- The counts differ by the rank of the projection for `(c', c]`, which is constant along the
    -- path since `c'` and `c` stay out of the spectrum.
    have hdec : ∀ u ∈ Icc s t, spectralCount c (A u) = spectralCount c' (A u) +
        Module.finrank 𝕜 (cfc ((Ioc c' c).indicator (1 : ℝ → ℝ)) (A u)).range := fun u hu ↦
      spectralCount_eq_add (hsa u hu) (hc.2 u hu).1 (hc.2 u hu).2.1 (hc.2 u hu).2.2 hc'.pos hcc
        (hc'.2 u hu).1 (hc'.2 u hu).2.1 (hc'.2 u hu).2.2
    have hr := congr_arg Cardinal.toNat (isPreconnected_Icc.rank_range_cfc_indicator_eq hA hsa
      (Ω := Ioc c' c) (fun u hu ↦ disjoint_frontier_Ioc hcc (hc'.notMem_spectrum hu)
        (hc.notMem_spectrum hu)) ⟨hst, le_rfl⟩ ⟨le_rfl, hst⟩)
    have hr' : (Module.finrank 𝕜 (cfc ((Ioc c' c).indicator (1 : ℝ → ℝ)) (A t)).range : ℤ) =
        Module.finrank 𝕜 (cfc ((Ioc c' c).indicator (1 : ℝ → ℝ)) (A s)).range := by
      exact_mod_cast hr
    rw [hdec t ⟨hst, le_rfl⟩, hdec s ⟨le_rfl, hst⟩]
    push_cast
    linarith
  · rfl

/-- **Spectral cuts exist locally.** Every time `t₀` of a continuous path of self-adjoint Fredholm
operators on `[a, b]` has a neighbourhood in `[a, b]` on which the path has a spectral cut. -/
theorem exists_isSpectralCutOn_ball_inter_Icc {a b t₀ : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    (ht₀ : t₀ ∈ Icc a b) : ∃ c, ∃ ε > 0, IsSpectralCutOn A c (ball t₀ ε ∩ Icc a b) := by
  obtain ⟨c, hc, hev⟩ :=
    (hsa t₀ ht₀).exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm (hF t₀ ht₀)
  have hT : Tendsto A (𝓝[Icc a b] t₀) (𝓝[{S | IsSelfAdjoint S}] (A t₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hA t₀ ht₀, eventually_nhdsWithin_of_forall hsa⟩
  obtain ⟨ε, hε, hball⟩ := nhdsWithin_basis_ball.eventually_iff.1 (hT.eventually hev)
  exact ⟨c, ε, hε, hc, fun u hu ↦ ⟨(hball hu).1, (hball hu).2.1, (hball hu).2.2.1⟩⟩

/-- An interval whose endpoints lie within `ε` of `x` is contained in the ball of radius `ε`
about `x`. -/
private theorem Icc_subset_ball {x ε s t : ℝ} (hs : x - ε < s) (ht : t < x + ε) :
    Icc s t ⊆ ball x ε := by
  rw [Real.ball_eq_Ioo]
  exact Icc_subset_Ioo hs ht

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- By the Lebesgue number lemma, if every time has a neighbourhood with a spectral cut, then all
short enough subintervals of `[a, b]` have spectral cuts. -/
private theorem exists_pos_forall_exists_isSpectralCutOn {a b : ℝ}
    (hloc : ∀ t ∈ Icc a b, ∃ c, ∃ ε > 0, IsSpectralCutOn A c (ball t ε ∩ Icc a b)) :
    ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b → t - s < δ → ∃ c, IsSpectralCutOn A c (Icc s t) := by
  choose c ε hε hcut using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric
    (c := fun i : Icc a b ↦ ball (i : ℝ) (ε i i.2)) isCompact_Icc (fun _ ↦ isOpen_ball)
    (fun t ht ↦ mem_iUnion.2 ⟨⟨t, ht⟩, mem_ball_self (hε t ht)⟩)
  refine ⟨δ, hδ, fun s t has hst htb hlt ↦ ?_⟩
  obtain ⟨i, hi⟩ := hleb s ⟨has, hst.trans htb⟩
  exact ⟨c i i.2, (hcut i i.2).mono fun u hu ↦
    ⟨hi (Icc_subset_ball (by linarith) (by linarith) hu), has.trans hu.1, hu.2.trans htb⟩⟩

open scoped Classical in
/-- The change of the count over `[s, t]` for some spectral cut, or `0` if there is none. -/
private noncomputable def localCount (A : ℝ → H →L[𝕜] H) (s t : ℝ) : ℤ :=
  if h : ∃ c, IsSpectralCutOn A c (Icc s t) then
    (spectralCount h.choose (A t) : ℤ) - spectralCount h.choose (A s)
  else 0

section Existence

variable {a b : ℝ} (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
include hA hsa

private theorem localCount_eq {s t c : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hc : IsSpectralCutOn A c (Icc s t)) :
    localCount A s t = (spectralCount c (A t) : ℤ) - spectralCount c (A s) := by
  have h : ∃ c, IsSpectralCutOn A c (Icc s t) := ⟨c, hc⟩
  simp only [localCount, h, ↓reduceDIte]
  exact h.choose_spec.spectralCount_sub_spectralCount_eq hst
    (hA.mono (Icc_subset_Icc has htb)) (fun u hu ↦ hsa u ⟨has.trans hu.1, hu.2.trans htb⟩) hc

/-- Local counts add up over an interval with a spectral cut. -/
private theorem localCount_add {x y z c : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzb : z ≤ b) (hc : IsSpectralCutOn A c (Icc x z)) :
    localCount A x z = localCount A x y + localCount A y z := by
  rw [localCount_eq hA hsa hax (hxy.trans hyz) hzb hc,
    localCount_eq hA hsa hax hxy (hyz.trans hzb) (hc.mono (Icc_subset_Icc le_rfl hyz)),
    localCount_eq hA hsa (hax.trans hxy) hyz hzb (hc.mono (Icc_subset_Icc hxy le_rfl))]
  ring

end Existence

/-- The grid point `a + ⌊(x - a) / h⌋ h` is at most `x`. -/
private theorem add_floor_mul_le {a h x : ℝ} (hh : 0 < h) (hax : a ≤ x) :
    a + (⌊(x - a) / h⌋₊ : ℝ) * h ≤ x := by
  have := Nat.floor_le (div_nonneg (sub_nonneg.2 hax) hh.le)
  rw [le_div_iff₀ hh] at this
  linarith

/-- The next grid point `a + (⌊(x - a) / h⌋ + 1) h` exceeds `x`. -/
private theorem lt_add_floor_add_one_mul {a h x : ℝ} (hh : 0 < h) :
    x < a + ((⌊(x - a) / h⌋₊ + 1 : ℕ) : ℝ) * h := by
  have := Nat.lt_floor_add_one ((x - a) / h)
  rw [div_lt_iff₀ hh] at this
  push_cast
  linarith

/-- Summing local counts along the grid `a + k h` up to `x`. -/
private noncomputable def gridPotential (A : ℝ → H →L[𝕜] H) (a h x : ℝ) : ℤ :=
  ∑ k ∈ Finset.range ⌊(x - a) / h⌋₊,
      localCount A (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h) +
    localCount A (a + (⌊(x - a) / h⌋₊ : ℝ) * h) x

section Existence

variable {a b : ℝ} (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
  {δ : ℝ} (hcut : ∀ s t, a ≤ s → s ≤ t → t ≤ b → t - s < δ → ∃ c, IsSpectralCutOn A c (Icc s t))
include hA hsa hcut

/-- Over a subinterval of length at most `h < δ`, the increment of the grid potential is the local
count. -/
private theorem gridPotential_sub_gridPotential {h : ℝ} (hh : 0 < h) (hhδ : h < δ) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (hlen : t - s ≤ h) :
    gridPotential A a h t - gridPotential A a h s = localCount A s t := by
  set n := ⌊(s - a) / h⌋₊ with hn
  have hgn : a + (n : ℝ) * h ≤ s := add_floor_mul_le hh has
  have hsn : s < a + ((n + 1 : ℕ) : ℝ) * h := lt_add_floor_add_one_mul hh
  have han : a ≤ a + (n : ℝ) * h := le_add_of_nonneg_right (by positivity)
  have hle : n ≤ ⌊(t - a) / h⌋₊ := Nat.floor_le_floor (by gcongr)
  have hle' : ⌊(t - a) / h⌋₊ ≤ n + 1 := by
    rw [hn, ← Nat.floor_add_one (div_nonneg (sub_nonneg.2 has) hh.le)]
    refine Nat.floor_le_floor ?_
    rw [div_add_one hh.ne', div_le_div_iff_of_pos_right hh]
    linarith
  obtain hm | hm : ⌊(t - a) / h⌋₊ = n ∨ ⌊(t - a) / h⌋₊ = n + 1 := by omega
  · -- `s` and `t` lie in the same grid cell `[g, g + h)`.
    have htn : t < a + ((n + 1 : ℕ) : ℝ) * h := hm ▸ lt_add_floor_add_one_mul hh
    push_cast at htn
    obtain ⟨c, hc⟩ := hcut _ _ han (hgn.trans hst) htb (by linarith)
    rw [gridPotential, gridPotential, hm, ← hn,
      localCount_add hA hsa han hgn hst htb hc]
    ring
  · -- `t` lies in the cell after that of `s`.
    have hgt : a + ((n + 1 : ℕ) : ℝ) * h ≤ t := hm ▸ add_floor_mul_le hh (has.trans hst)
    obtain ⟨c₁, hc₁⟩ := hcut _ _ han (hgn.trans (hsn.le)) (hgt.trans htb) (by push_cast; linarith)
    obtain ⟨c₂, hc₂⟩ := hcut _ _ has hst htb (by linarith)
    rw [gridPotential, gridPotential, hm, ← hn, Finset.sum_range_succ,
      localCount_add hA hsa han hgn hsn.le (hgt.trans htb) hc₁,
      localCount_add hA hsa has hsn.le hgt htb hc₂]
    ring

/-- The grid potential is a spectral flow potential. -/
private theorem isSpectralFlowPotential_gridPotential (hδ : 0 < δ) :
    IsSpectralFlowPotential A a b (gridPotential A a (δ / 2)) := by
  intro s t c has hst htb hc
  -- Subdivide `[s, t]` into `N` pieces of length at most `δ / 2`.
  obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / (δ / 2))
  have hN0 : 0 < (N : ℝ) := lt_of_le_of_lt (div_nonneg (sub_nonneg.2 hst) (by positivity)) hN
  have hstep : (t - s) / N ≤ δ / 2 := by
    rw [div_lt_iff₀ (by positivity)] at hN
    rw [div_le_iff₀ hN0]
    linarith
  set p : ℕ → ℝ := fun k ↦ s + k / N * (t - s) with hp
  have hpk (k : ℕ) (hk : k ≤ N) : s ≤ p k ∧ p k ≤ t := by
    have h₀ : 0 ≤ (k : ℝ) / N := by positivity
    have h₁ : (k : ℝ) / N ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hk)
    constructor <;> nlinarith
  have hsucc (k : ℕ) : p (k + 1) - p k = (t - s) / N := by
    simp only [hp]
    push_cast
    field_simp
    ring
  have key : ∀ k ≤ N, gridPotential A a (δ / 2) (p k) - gridPotential A a (δ / 2) s =
      (spectralCount c (A (p k)) : ℤ) - spectralCount c (A s) := by
    intro k
    induction k with
    | zero => intro; simp [p]
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      have hsk := (hpk k (by omega)).1
      have hkt' := (hpk (k + 1) hk).2
      have hkk : p k ≤ p (k + 1) := by linarith [hsucc k, div_nonneg (sub_nonneg.2 hst) hN0.le]
      have h₁ := gridPotential_sub_gridPotential hA hsa hcut (half_pos hδ) (half_lt_self hδ)
        (has.trans hsk) hkk (hkt'.trans htb) (by linarith [hsucc k])
      rw [localCount_eq hA hsa (has.trans hsk) hkk (hkt'.trans htb)
        (hc.mono (Icc_subset_Icc hsk hkt'))] at h₁
      linarith
  have hpN : p N = t := by
    simp only [hp]
    field_simp
    ring
  simpa [hpN] using key N le_rfl

end Existence

/-- Potentials exist when every time has a neighbourhood with a spectral cut. -/
private theorem exists_isSpectralFlowPotential_of_loc {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (hloc : ∀ t ∈ Icc a b, ∃ c, ∃ ε > 0, IsSpectralCutOn A c (ball t ε ∩ Icc a b)) :
    ∃ F, IsSpectralFlowPotential A a b F := by
  obtain ⟨δ, hδ, hcut⟩ := exists_pos_forall_exists_isSpectralCutOn hloc
  exact ⟨_, isSpectralFlowPotential_gridPotential hA hsa hcut hδ⟩

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Two potentials have the same increment over `[a, b]` when every time has a neighbourhood with a
spectral cut: their difference is locally constant on the interval. -/
private theorem IsSpectralFlowPotential.sub_eq_sub_of_loc {a b : ℝ} {F G : ℝ → ℤ}
    (hF : IsSpectralFlowPotential A a b F) (hG : IsSpectralFlowPotential A a b G) (hab : a ≤ b)
    (hloc : ∀ t ∈ Icc a b, ∃ c, ∃ ε > 0, IsSpectralCutOn A c (ball t ε ∩ Icc a b)) :
    F b - F a = G b - G a := by
  have hD : ContinuousOn (fun x ↦ F x - G x) (Icc a b) := by
    intro t₀ ht₀
    obtain ⟨c, ε, hε, hc⟩ := hloc t₀ ht₀
    refine (continuousWithinAt_const (b := F t₀ - G t₀)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [inter_mem_nhdsWithin (Icc a b) (ball_mem_nhds t₀ hε)] with u hu
    obtain ⟨⟨hau, hub⟩, hu⟩ := hu
    rw [mem_ball, Real.dist_eq, abs_lt] at hu
    -- Compare `F` and `G` over the interval between `u` and `t₀`.
    have hm : a ≤ min u t₀ := le_min hau ht₀.1
    have hM : max u t₀ ≤ b := max_le hub ht₀.2
    have hcu : IsSpectralCutOn A c (Icc (min u t₀) (max u t₀)) := hc.mono fun v hv ↦
      ⟨Icc_subset_ball (lt_min (by linarith) (by linarith)) (max_lt (by linarith) (by linarith))
        hv, hm.trans hv.1, hv.2.trans hM⟩
    have h₁ := hF hm min_le_max hM hcu
    have h₂ := hG hm min_le_max hM hcu
    rcases le_total u t₀ with h | h
    · rw [min_eq_left h, max_eq_right h] at h₁ h₂
      linarith
    · rw [min_eq_right h, max_eq_left h] at h₁ h₂
      linarith
  have := isPreconnected_Icc.constant hD ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  linarith

/-- **Existence of spectral flow potentials** for a continuous path of self-adjoint Fredholm
operators. -/
theorem exists_isSpectralFlowPotential {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) :
    ∃ F, IsSpectralFlowPotential A a b F :=
  exists_isSpectralFlowPotential_of_loc hA hsa fun _ ht ↦
    exists_isSpectralCutOn_ball_inter_Icc hA hsa hF ht

/-- **Uniqueness of spectral flow potentials**: for a continuous path of self-adjoint Fredholm
operators on `[a, b]`, any two potentials have the same increment over `[a, b]`. -/
theorem IsSpectralFlowPotential.sub_eq_sub {a b : ℝ} {F G : ℝ → ℤ}
    (hFp : IsSpectralFlowPotential A a b F) (hGp : IsSpectralFlowPotential A a b G) (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) : F b - F a = G b - G a :=
  hFp.sub_eq_sub_of_loc hGp hab fun _ ht ↦ exists_isSpectralCutOn_ball_inter_Icc hA hsa hF ht

/-! ### Spectral flow -/

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
private theorem spectralFlow_eq_sub_of_loc {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Icc a b, ∃ c, ∃ ε > 0, IsSpectralCutOn A c (ball t ε ∩ Icc a b))
    {F : ℝ → ℤ} (hFp : IsSpectralFlowPotential A a b F) : spectralFlow A a b = F b - F a := by
  have h : ∃ F, IsSpectralFlowPotential A a b F := ⟨F, hFp⟩
  simp only [spectralFlow, h, ↓reduceDIte]
  exact h.choose_spec.sub_eq_sub_of_loc hFp hab hloc

/-- The spectral flow is the increment of any spectral flow potential. -/
theorem spectralFlow_eq_sub {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    {F : ℝ → ℤ} (hFp : IsSpectralFlowPotential A a b F) : spectralFlow A a b = F b - F a :=
  spectralFlow_eq_sub_of_loc hab (fun _ ht ↦ exists_isSpectralCutOn_ball_inter_Icc hA hsa hF ht)
    hFp

/-- **Phillips' partition formula.** For a partition `a = p 0 ≤ p 1 ≤ ⋯ ≤ p n = b` and a spectral
cut `c k` of `A` on each `[p k, p (k + 1)]`, the spectral flow is the sum of the changes of the
counts of eigenvalues in `[0, c k]` over the pieces. -/
theorem spectralFlow_eq_sum {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    {n : ℕ} {p : ℕ → ℝ} (hp : Monotone p) (hp0 : p 0 = a) (hpn : p n = b) {c : ℕ → ℝ}
    (hc : ∀ k < n, IsSpectralCutOn A (c k) (Icc (p k) (p (k + 1)))) :
    spectralFlow A a b = ∑ k ∈ Finset.range n,
      ((spectralCount (c k) (A (p (k + 1))) : ℤ) - spectralCount (c k) (A (p k))) := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  have hab : a ≤ b := hp0 ▸ hpn ▸ hp (Nat.zero_le n)
  rw [spectralFlow_eq_sub hab hA hsa hF hFp, ← hp0, ← hpn,
    ← Finset.sum_range_sub (fun k ↦ F (p k))]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk := Finset.mem_range.1 hk
  exact hFp (hp0 ▸ hp (Nat.zero_le k)) (hp k.le_succ) (hpn ▸ hp hk) (hc k hk)

/-- **The spectral flow over an interval with a single cut** `c` is the change of the number of
eigenvalues in `[0, c]`. No Fredholm hypothesis is needed beyond the cut. -/
theorem spectralFlow_eq_of_isSpectralCutOn {a b c : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (hc : IsSpectralCutOn A c (Icc a b)) :
    spectralFlow A a b = (spectralCount c (A b) : ℤ) - spectralCount c (A a) := by
  have hloc : ∀ t ∈ Icc a b, ∃ c, ∃ ε > 0, IsSpectralCutOn A c (ball t ε ∩ Icc a b) :=
    fun _ _ ↦ ⟨c, 1, one_pos, hc.mono inter_subset_right⟩
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential_of_loc hA hsa hloc
  rw [spectralFlow_eq_sub_of_loc hab hloc hFp]
  exact hFp le_rfl hab le_rfl hc

/-- **Concatenation.** The spectral flow from `a` to `d` is the spectral flow from `a` to `b` plus
the spectral flow from `b` to `d`. -/
theorem spectralFlow_add_adjacent_intervals {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d)
    (hA : ContinuousOn A (Icc a d)) (hsa : ∀ t ∈ Icc a d, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc a d, (A t).IsFredholm) :
    spectralFlow A a d = spectralFlow A a b + spectralFlow A b d := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  have h₁ : Icc a b ⊆ Icc a d := Icc_subset_Icc le_rfl hbd
  have h₂ : Icc b d ⊆ Icc a d := Icc_subset_Icc hab le_rfl
  rw [spectralFlow_eq_sub (hab.trans hbd) hA hsa hF hFp,
    spectralFlow_eq_sub hab (hA.mono h₁) (fun t ht ↦ hsa t (h₁ ht)) (fun t ht ↦ hF t (h₁ ht))
      (hFp.mono le_rfl hbd),
    spectralFlow_eq_sub hbd (hA.mono h₂) (fun t ht ↦ hsa t (h₂ ht)) (fun t ht ↦ hF t (h₂ ht))
      (hFp.mono hab le_rfl)]
  ring

/-- **Reversal.** Running the path backwards changes the sign of the spectral flow. -/
theorem spectralFlow_comp_neg {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) :
    spectralFlow (fun t ↦ A (-t)) (-b) (-a) = -spectralFlow A a b := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  have hmem {t : ℝ} (ht : t ∈ Icc (-b) (-a)) : -t ∈ Icc a b :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hGp : IsSpectralFlowPotential (fun t ↦ A (-t)) (-b) (-a) fun x ↦ F (-x) := by
    intro s t c hs hst ht hc
    have := hFp (by linarith) (neg_le_neg hst) (by linarith) hc.of_comp_neg
    linarith
  rw [spectralFlow_eq_sub (A := fun t ↦ A (-t)) (neg_le_neg hab)
      (hA.comp continuous_neg.continuousOn fun _ ↦ hmem)
      (fun t ht ↦ hsa _ (hmem ht)) (fun t ht ↦ hF _ (hmem ht)) hGp,
    spectralFlow_eq_sub hab hA hsa hF hFp, neg_neg, neg_neg]
  ring

/-- On a finite-dimensional space, the spectral flow of the path `t ↦ t • 1` from `a < 0` to
`b ≥ 0` is the dimension: its one eigenvalue crosses `0` upwards with full multiplicity. -/
theorem spectralFlow_algebraMap [FiniteDimensional 𝕜 H] {a b : ℝ} (ha : a < 0) (hb : 0 ≤ b) :
    spectralFlow (fun t ↦ algebraMap ℝ (H →L[𝕜] H) t) a b = Module.finrank 𝕜 H := by
  set c := max (-a) b + 1
  have hac : -c < a := by linarith [le_max_left (-a) b]
  have hbc : b < c := by linarith [le_max_right (-a) b]
  have hc : IsSpectralCutOn (fun t ↦ algebraMap ℝ (H →L[𝕜] H) t) c (Icc a b) := by
    refine ⟨by linarith, fun u hu ↦ ⟨fun h ↦ ?_, fun h ↦ ?_, inferInstance⟩⟩
    · have := CFC.spectrum_algebraMap_subset (p := IsSelfAdjoint) u h
      rw [mem_singleton_iff] at this
      linarith [hu.1]
    · have := CFC.spectrum_algebraMap_subset (p := IsSelfAdjoint) u h
      rw [mem_singleton_iff] at this
      linarith [hu.2]
  -- The `ℝ`-action on operators comes from the `NormedAlgebra` instance, so its continuity is
  -- obtained from `NormedSpace.toIsBoundedSMul` explicitly.
  have hcont : Continuous fun t : ℝ ↦ algebraMap ℝ (H →L[𝕜] H) t := by
    have := (NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := H →L[𝕜] H)).continuousSMul
    exact continuous_algebraMap ℝ _
  rw [spectralFlow_eq_of_isSpectralCutOn (ha.le.trans hb) hcont.continuousOn
    (fun t _ ↦ cfc_predicate_algebraMap (A := H →L[𝕜] H) t) hc, spectralCount_def,
    spectralCount_def, cfc_algebraMap, cfc_algebraMap,
    indicator_of_mem (⟨hb, hbc.le⟩ : b ∈ Icc 0 c),
    indicator_of_notMem (fun h : a ∈ Icc 0 c ↦ (not_le.2 ha) h.1), Pi.one_apply, map_one,
    map_zero, ContinuousLinearMap.toLinearMap_one, ContinuousLinearMap.toLinearMap_zero,
    Module.End.one_eq_id,
    LinearMap.range_id, LinearMap.range_zero, finrank_top, finrank_bot]
  simp

end TauCeti
