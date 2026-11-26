/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Projection
public import TauCeti.Analysis.InnerProductSpace.Spectral.FiniteRank
import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Algebra.Indicator
import TauCeti.Topology.LocallyConstant.Preconnected
import TauCeti.Topology.Order.Interval.Basic

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
time has a neighbourhood with a cut (`TauCeti.exists_isSpectralCutOn_ball_inter`).

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
concatenation (`TauCeti.spectralFlow_add_adjacent_intervals`). It is unchanged by a continuous
change of the parameter `φ` with `φ a ≤ φ b`, `SF(A ∘ φ, a, b) = SF(A, φ a, φ b)`
(`TauCeti.spectralFlow_comp_of_mapsTo`), and changes sign when `φ b ≤ φ a`
(`TauCeti.spectralFlow_comp_of_mapsTo_of_ge`), in particular when the path is reversed
(`TauCeti.spectralFlow_comp_neg`). Here `φ` need not be monotone, and only has to map `[a, b]` into
an interval on which `A` is a continuous path of self-adjoint Fredholm operators: a potential of
`A` composed with `φ` is a potential of `A ∘ φ`, since by the intermediate value theorem `φ` maps
each subinterval onto a set containing the interval between its values. More generally, a path
with the same potentials as a continuous path of self-adjoint Fredholm operators has the same
spectral flow (`TauCeti.spectralFlow_eq_of_isSpectralFlowPotential_iff`); this compares paths on
different Hilbert spaces, as in `TauCeti.Analysis.Fredholm.Spectral.Conjugation`. The scalar paths
`t ↦ f t • 1` on a finite-dimensional space are computed in
`TauCeti.Analysis.Fredholm.Spectral.FiniteDimensional`
(`TauCeti.spectralFlow_algebraMap_comp`).

**Homotopy invariance.** For a continuous family `G s t` of self-adjoint Fredholm operators on a
rectangle `[u, v] × [a, b]`, the spectral flow around the boundary of the rectangle vanishes
(`TauCeti.spectralFlow_add_spectralFlow_eq_add`): the spectral flow along the bottom side `G u`
and then up the right side `s ↦ G s b` equals that up the left side `s ↦ G s a` and then along the
top side `G v`. By the Lebesgue number lemma on the rectangle, there is a `δ > 0` such that every
product of `δ`-balls carries a single cut. On a horizontal strip of height less than `δ`, the
difference between the potentials of the bottom and top sides, minus the spectral flow of the
vertical path through `t`, is then locally constant in `t`, so the difference between the two
horizontal sides is the difference between the two vertical sides. Gluing the strips gives the
whole rectangle. A path constant on `[a, b]` has no spectral flow
(`TauCeti.spectralFlow_eq_zero_of_forall_eq`), so the spectral flow is invariant under homotopies
that fix the endpoints (`TauCeti.spectralFlow_eq_of_homotopy`). Neither has a path of invertible
operators (`TauCeti.spectralFlow_eq_zero_of_forall_zero_notMem_spectrum`), so the spectral flow is
also invariant under homotopies whose endpoints stay invertible
(`TauCeti.spectralFlow_eq_of_homotopy_of_zero_notMem_spectrum`).

## Main definitions

* `TauCeti.IsSpectralCutOn A c s`: `c` is a spectral cut of `A` at every time of `s`.
* `TauCeti.spectralCount c T`: the rank of the spectral projection of `T` for `[0, c]`.
* `TauCeti.IsSpectralFlowPotential A a b F`: `F` integrates the local counts on `[a, b]`.
* `TauCeti.spectralFlow A a b`: the spectral flow of `A` from `a` to `b`.

## Main results

* `TauCeti.isSpectralCutOn_of_norm_lt`: a bound above the norms is a spectral cut.
* `TauCeti.IsSpectralCutOn.spectralCount_sub_spectralCount_eq`: the local count does not depend on
  the cut.
* `TauCeti.exists_isSpectralCutOn_ball_inter_lt`: small spectral cuts exist locally.
* `TauCeti.exists_isSpectralFlowPotential`, `TauCeti.IsSpectralFlowPotential.sub_eq_sub`: existence
  and uniqueness of potentials.
* `TauCeti.spectralFlow_eq_sum`: Phillips' partition formula.
* `TauCeti.spectralFlow_eq_of_isSpectralCutOn`: the spectral flow over an interval with a single
  cut.
* `TauCeti.spectralFlow_eq_of_isSpectralFlowPotential_iff`: paths with the same potentials have
  the same spectral flow.
* `TauCeti.spectralFlow_eq_of_forall_exists_isSpectralCutOn`: paths whose local counts change
  alike have the same spectral flow.
* `TauCeti.spectralFlow_add_adjacent_intervals`: concatenation.
* `TauCeti.spectralFlow_comp_of_mapsTo`, `TauCeti.spectralFlow_comp_of_mapsTo_of_ge`,
  `TauCeti.spectralFlow_comp_neg`: reparametrization and reversal.
* `TauCeti.spectralFlow_add_spectralFlow_eq_add`: the spectral flow around a rectangle vanishes.
* `TauCeti.spectralFlow_eq_of_homotopy`: homotopy invariance with fixed endpoints.
* `TauCeti.spectralFlow_eq_of_homotopy_of_zero_notMem_spectrum`: homotopy invariance with
  invertible endpoints.

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

/-- `c` is a **spectral cut** of the family `A` on the set `s` of parameters, typically the times
of a path: `c > 0`, and for every `u ∈ s` neither `-c` nor `c` is in the spectrum of `A u`, and the
spectral projection of `A u` for `[-c, c]` has finite rank. -/
def IsSpectralCutOn {α : Type*} (A : α → H →L[𝕜] H) (c : ℝ) (s : Set α) : Prop :=
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

/-- The number of eigenvalues in `[0, c]` of the scalar operator `x • 1` is the dimension of `H`
if `x ∈ [0, c]`, and `0` otherwise. -/
@[simp]
theorem spectralCount_algebraMap (c x : ℝ) :
    spectralCount c (algebraMap ℝ (H →L[𝕜] H) x) =
      if x ∈ Icc 0 c then Module.finrank 𝕜 H else 0 := by
  rw [spectralCount_def, cfc_algebraMap]
  -- `simp` cannot rewrite the operator inside `finrank` of its range, whose type depends on it,
  -- so the range is computed first.
  split_ifs with hx
  · have h : ((algebraMap ℝ (H →L[𝕜] H) ((Icc 0 c).indicator 1 x) : H →L[𝕜] H) :
        H →ₗ[𝕜] H).range = ⊤ := by
      simp [hx, Module.End.one_eq_id]
    rw [h, finrank_top]
  · have h : ((algebraMap ℝ (H →L[𝕜] H) ((Icc 0 c).indicator 1 x) : H →L[𝕜] H) :
        H →ₗ[𝕜] H).range = ⊥ := by
      simp [hx]
    rw [h, finrank_bot]

section General

variable {α : Type*} {A : α → H →L[𝕜] H} {c : ℝ} {s t : Set α}

/-- Unfolds `TauCeti.IsSpectralCutOn`. -/
theorem isSpectralCutOn_iff : IsSpectralCutOn A c s ↔ 0 < c ∧ ∀ u ∈ s,
    -c ∉ spectrum ℝ (A u) ∧ c ∉ spectrum ℝ (A u) ∧
      FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A u)).range :=
  Iff.rfl

/-- A positive `c` strictly above the norms of `A` on `s` is a spectral cut on `s`, provided the
spectral projections for `[-c, c]` have finite rank: then `±c` lie outside every spectrum. -/
theorem isSpectralCutOn_of_norm_lt (hc : 0 < c) (h : ∀ u ∈ s, ‖A u‖ < c)
    (hfin : ∀ u ∈ s,
      FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A u)).range) :
    IsSpectralCutOn A c s := by
  have hnotMem {u : α} {r : ℝ} (hu : u ∈ s) (hr : c = |r|) : r ∉ spectrum ℝ (A u) := by
    intro hr'
    rcases subsingleton_or_nontrivial H with _ | _
    · rw [spectrum.of_subsingleton] at hr'
      exact hr'
    · have := spectrum.norm_le_norm_of_mem hr'
      rw [Real.norm_eq_abs] at this
      linarith [h u hu]
  exact ⟨hc, fun u hu ↦ ⟨hnotMem hu (by rw [abs_neg, abs_of_pos hc]),
    hnotMem hu (abs_of_pos hc).symm, hfin u hu⟩⟩

/-- A spectral cut is positive. -/
theorem IsSpectralCutOn.pos (h : IsSpectralCutOn A c s) : 0 < c := h.1

/-- At a parameter of a spectral cut `c`, `-c` is not in the spectrum. -/
theorem IsSpectralCutOn.neg_notMem_spectrum (h : IsSpectralCutOn A c s) {u : α} (hu : u ∈ s) :
    -c ∉ spectrum ℝ (A u) :=
  (h.2 u hu).1

/-- At a parameter of a spectral cut `c`, `c` is not in the spectrum. -/
theorem IsSpectralCutOn.notMem_spectrum (h : IsSpectralCutOn A c s) {u : α} (hu : u ∈ s) :
    c ∉ spectrum ℝ (A u) :=
  (h.2 u hu).2.1

/-- At a parameter of a spectral cut `c`, the spectral projection for `[-c, c]` has finite rank. -/
theorem IsSpectralCutOn.finiteDimensional_range_cfc_indicator_Icc (h : IsSpectralCutOn A c s)
    {u : α} (hu : u ∈ s) :
    FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A u)).range :=
  (h.2 u hu).2.2

/-- A spectral cut on a set of parameters is a spectral cut on every subset. -/
theorem IsSpectralCutOn.mono (h : IsSpectralCutOn A c s) (hts : t ⊆ s) : IsSpectralCutOn A c t :=
  ⟨h.1, fun u hu ↦ h.2 u (hts hu)⟩

/-- A spectral cut of a reparametrized family `A ∘ φ` on `s` is a spectral cut of `A` on every set
of parameters covered by `φ '' s`. -/
theorem IsSpectralCutOn.of_comp {β : Type*} {φ : β → α} {s : Set β}
    (h : IsSpectralCutOn (A ∘ φ) c s) (hts : t ⊆ φ '' s) : IsSpectralCutOn A c t := by
  refine ⟨h.1, fun u hu ↦ ?_⟩
  obtain ⟨w, hw, rfl⟩ := hts hu
  exact h.2 w hw

end General

variable {A : ℝ → H →L[𝕜] H} {c : ℝ} {s t : Set ℝ}

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

/-- The increment of a spectral flow potential between two times `s` and `t` of `[a, b]`, in
either order, with a spectral cut `c` on the interval between them, is the change of the number of
eigenvalues in `[0, c]`. -/
theorem IsSpectralFlowPotential.sub_eq_of_uIcc {a b s t : ℝ} {F : ℝ → ℤ}
    (hF : IsSpectralFlowPotential A a b F) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hc : IsSpectralCutOn A c (uIcc s t)) :
    F t - F s = (spectralCount c (A t) : ℤ) - spectralCount c (A s) := by
  rcases le_total s t with h | h
  · exact hF hs.1 h ht.2 (uIcc_of_le h ▸ hc)
  · have := hF ht.1 h hs.2 (uIcc_of_ge h ▸ hc)
    linarith

/-- A spectral flow potential `F` of `A` on `[p, q]`, for `φ` continuous on `[a, b]` and mapping it
into `[p, q]`, gives the spectral flow potential `F ∘ φ` of the reparametrized path `A ∘ φ` on
`[a, b]`. -/
theorem IsSpectralFlowPotential.comp_of_mapsTo {φ : ℝ → ℝ} {a b p q : ℝ} {F : ℝ → ℤ}
    (hF : IsSpectralFlowPotential A p q F) (hφ : ContinuousOn φ (Icc a b))
    (hmaps : MapsTo φ (Icc a b) (Icc p q)) : IsSpectralFlowPotential (A ∘ φ) a b (F ∘ φ) := by
  intro s t c has hst htb hc
  have hivt := intermediate_value_uIcc (a := s) (b := t)
    (uIcc_of_le hst ▸ hφ.mono (Icc_subset_Icc has htb))
  rw [uIcc_of_le hst] at hivt
  exact hF.sub_eq_of_uIcc (hmaps ⟨has, hst.trans htb⟩) (hmaps ⟨has.trans hst, htb⟩)
    (hc.of_comp hivt)

open scoped Classical in
/-- The **spectral flow** of the path `A` from `a` to `b`: the increment `F b - F a` of a spectral
flow potential `F` of `A` on `[a, b]`. For `a ≤ b` and a continuous path of self-adjoint Fredholm
operators on `[a, b]`, potentials exist and all give the same value (`TauCeti.spectralFlow_eq_sub`);
it is the net number of eigenvalues crossing `0` upwards. Otherwise it is a junk value: in
particular, for `b < a` every function is vacuously a potential, so the value is arbitrary and need
not be `-spectralFlow A b a`. -/
noncomputable def spectralFlow (A : ℝ → H →L[𝕜] H) (a b : ℝ) : ℤ :=
  if h : ∃ F, IsSpectralFlowPotential A a b F then h.choose b - h.choose a else 0

/-- The spectral flow from `a` to `b` only depends on the path on `[a, b]`. -/
theorem spectralFlow_congr {B : ℝ → H →L[𝕜] H} {a b : ℝ} (h : EqOn A B (Icc a b)) :
    spectralFlow A a b = spectralFlow B a b := by
  have key {A B : ℝ → H →L[𝕜] H} (h : EqOn A B (Icc a b)) (F : ℝ → ℤ)
      (hF : IsSpectralFlowPotential A a b F) : IsSpectralFlowPotential B a b F := by
    intro s t c has hst htb hc
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hcA : IsSpectralCutOn A c (Icc s t) :=
      ⟨hc.1, fun u hu ↦ by rw [h (hsub hu)]; exact hc.2 u hu⟩
    rw [hF has hst htb hcA, h ⟨has, hst.trans htb⟩, h ⟨has.trans hst, htb⟩]
  have hpot : IsSpectralFlowPotential A a b = IsSpectralFlowPotential B a b :=
    funext fun F ↦ propext ⟨key h F, key h.symm F⟩
  unfold spectralFlow
  rw [hpot]

/-- The spectral flow over a single time vanishes. -/
@[simp]
theorem spectralFlow_self (A : ℝ → H →L[𝕜] H) (a : ℝ) : spectralFlow A a a = 0 := by
  unfold spectralFlow
  split_ifs <;> simp

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

section Single

variable {S : H →L[𝕜] H}

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
        (disjoint_frontier_Icc h₁ h₂)) hfd)
    (Icc_subset_Icc (by linarith) le_rfl) (disjoint_frontier_Icc h₁ h₂)

/-- At a cut `c`, the spectral projection for `[0, c]` has finite rank. -/
private theorem finiteDimensional_range_cfc_indicator_Icc_zero :
    FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) S).range :=
  Submodule.finiteDimensional_of_le (S.range_cfc_indicator_le_of_subset
    (Icc_subset_Icc (by linarith) le_rfl) (continuousOn_indicator_Icc_zero hS hc h₁ h₂ hfd)
    (continuousOn_const.continuousOn_indicator_of_disjoint_frontier
      (disjoint_frontier_Icc h₁ h₂)))

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

/-- At a time `u` of a spectral cut `c`, and for `c < d` with `d` not in the spectrum of the
self-adjoint operator `A u`, the rank of the spectral projection for `[0, d]`, if finite, is the
count of eigenvalues in `[0, c]` plus the rank of the spectral projection for `(c, d]`. -/
theorem IsSpectralCutOn.finrank_range_cfc_indicator_Icc_eq_add (h : IsSpectralCutOn A c s)
    {u d : ℝ} (hu : u ∈ s) (hsa : IsSelfAdjoint (A u)) (hcd : c < d)
    (hd : d ∉ spectrum ℝ (A u))
    (hfd : FiniteDimensional 𝕜 (cfc ((Icc 0 d).indicator (1 : ℝ → ℝ)) (A u)).range) :
    Module.finrank 𝕜 (cfc ((Icc 0 d).indicator (1 : ℝ → ℝ)) (A u)).range =
      spectralCount c (A u) +
        Module.finrank 𝕜 (cfc ((Ioc c d).indicator (1 : ℝ → ℝ)) (A u)).range := by
  have hdisj : Disjoint (Icc 0 c) (Ioc c d) :=
    disjoint_left.2 fun x (hx : x ∈ Icc 0 c) (hx' : x ∈ Ioc c d) ↦ (not_lt.2 hx.2) hx'.1
  have h₀ := h.continuousOn_indicator_Icc_zero hu hsa
  have := h.finiteDimensional_range_cfc_indicator_Icc_zero hu hsa
  have hcont : ContinuousOn ((Ioc c d).indicator (1 : ℝ → ℝ)) (spectrum ℝ (A u)) :=
    continuousOn_const.continuousOn_indicator_of_disjoint_frontier
      (disjoint_frontier_Ioc (h.notMem_spectrum hu) hd)
  have hcontd : ContinuousOn ((Icc 0 d).indicator (1 : ℝ → ℝ)) (spectrum ℝ (A u)) := by
    rw [← Icc_union_Ioc_eq_Icc h.pos.le hcd.le, indicator_union_of_disjoint hdisj]
    exact h₀.add hcont
  have : FiniteDimensional 𝕜 (cfc ((Ioc c d).indicator (1 : ℝ → ℝ)) (A u)).range :=
    Submodule.finiteDimensional_of_le ((A u).range_cfc_indicator_le_of_subset (Ω := Ioc c d)
      (Ω' := Icc 0 d) (fun x hx ↦ ⟨h.pos.le.trans hx.1.le, hx.2⟩) hcont hcontd)
  rw [spectralCount_def, ← Icc_union_Ioc_eq_Icc h.pos.le hcd.le]
  exact (A u).finrank_range_cfc_indicator_union hdisj h₀ hcont

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
      (spectralCount_def c (A u)).trans (hc'.finrank_range_cfc_indicator_Icc_eq_add hu (hsa u hu)
        hcc (hc.notMem_spectrum hu)
        (hc.finiteDimensional_range_cfc_indicator_Icc_zero hu (hsa u hu)))
    have hr := isPreconnected_Icc.finrank_range_cfc_indicator_eq hA hsa
      (Ω := Ioc c' c) (fun u hu ↦ disjoint_frontier_Ioc (hc'.notMem_spectrum hu)
        (hc.notMem_spectrum hu)) ⟨hst, le_rfl⟩ ⟨le_rfl, hst⟩
    rw [hdec t ⟨hst, le_rfl⟩, hdec s ⟨le_rfl, hst⟩]
    push_cast
    linarith
  · rfl

/-- **Small spectral cuts exist locally.** For every `η > 0`, every point `z` of a set `K` of
parameters, on which a family of self-adjoint Fredholm operators is continuous, has a neighbourhood
in `K` on which the family has a spectral cut `c < η`. -/
theorem exists_isSpectralCutOn_ball_inter_lt {X : Type*} [PseudoMetricSpace X]
    {B : X → H →L[𝕜] H} {K : Set X} {z : X} (hB : ContinuousOn B K)
    (hsa : ∀ x ∈ K, IsSelfAdjoint (B x)) (hF : ∀ x ∈ K, (B x).IsFredholm) (hz : z ∈ K) {η : ℝ}
    (hη : 0 < η) : ∃ c < η, ∃ ε > 0, IsSpectralCutOn B c (ball z ε ∩ K) := by
  obtain ⟨c, hc, hcη, hev⟩ :=
    (hsa z hz).exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm (hF z hz) hη
  have hT : Tendsto B (𝓝[K] z) (𝓝[{S | IsSelfAdjoint S}] (B z)) :=
    tendsto_nhdsWithin_iff.2 ⟨hB z hz, eventually_nhdsWithin_of_forall hsa⟩
  obtain ⟨ε, hε, hball⟩ := nhdsWithin_basis_ball.eventually_iff.1 (hT.eventually hev)
  exact ⟨c, hcη, ε, hε, hc, fun u hu ↦ ⟨(hball hu).1, (hball hu).2.1, (hball hu).2.2.1⟩⟩

/-- **Spectral cuts exist locally.** Every point `z` of a set `K` of parameters, on which a family
of self-adjoint Fredholm operators is continuous, has a neighbourhood in `K` on which the family has
a spectral cut. For instance, every time of a continuous path of self-adjoint Fredholm operators on
`[a, b]` has a neighbourhood in `[a, b]` on which the path has a spectral cut. -/
theorem exists_isSpectralCutOn_ball_inter {X : Type*} [PseudoMetricSpace X] {B : X → H →L[𝕜] H}
    {K : Set X} {z : X} (hB : ContinuousOn B K) (hsa : ∀ x ∈ K, IsSelfAdjoint (B x))
    (hF : ∀ x ∈ K, (B x).IsFredholm) (hz : z ∈ K) :
    ∃ c, ∃ ε > 0, IsSpectralCutOn B c (ball z ε ∩ K) :=
  let ⟨c, _, h⟩ := exists_isSpectralCutOn_ball_inter_lt hB hsa hF hz one_pos
  ⟨c, h⟩

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- By the Lebesgue number lemma, if every point of a compact set `K` has a neighbourhood in `K`
with a spectral cut, then there is a `δ > 0` such that every `δ`-ball about a point of `K` meets
`K` in a set with a spectral cut. -/
private theorem exists_pos_forall_exists_isSpectralCutOn_ball_inter {X : Type*}
    [PseudoMetricSpace X] {B : X → H →L[𝕜] H} {K : Set X} (hK : IsCompact K)
    (hloc : ∀ z ∈ K, ∃ c, ∃ ε > 0, IsSpectralCutOn B c (ball z ε ∩ K)) :
    ∃ δ > 0, ∀ z ∈ K, ∃ c, IsSpectralCutOn B c (ball z δ ∩ K) := by
  choose! c ε hε hcut using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun z : K ↦ ball (z : X) (ε z))
    hK (fun _ ↦ isOpen_ball) (fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hε z hz)⟩)
  refine ⟨δ, hδ, fun z hz ↦ ?_⟩
  obtain ⟨i, hi⟩ := hleb z hz
  exact ⟨c i, (hcut i i.property).mono fun w hw ↦ ⟨hi hw.1, hw.2⟩⟩

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- By the Lebesgue number lemma, if every time has a neighbourhood with a spectral cut, then all
short enough subintervals of `[a, b]` have spectral cuts. -/
private theorem exists_pos_forall_exists_isSpectralCutOn {a b : ℝ}
    (hloc : ∀ t ∈ Icc a b, ∃ c, ∃ ε > 0, IsSpectralCutOn A c (ball t ε ∩ Icc a b)) :
    ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b → t - s < δ → ∃ c, IsSpectralCutOn A c (Icc s t) := by
  obtain ⟨δ, hδ, hcut⟩ := exists_pos_forall_exists_isSpectralCutOn_ball_inter isCompact_Icc hloc
  refine ⟨δ, hδ, fun s t has hst htb hlt ↦ ?_⟩
  obtain ⟨c, hc⟩ := hcut s ⟨has, hst.trans htb⟩
  exact ⟨c, hc.mono fun u hu ↦
    ⟨Real.Icc_subset_ball (by linarith) (by linarith) hu, has.trans hu.1, hu.2.trans htb⟩⟩

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
  have := isPreconnected_Icc.apply_eq_of_eventually_eq (f := fun x ↦ F x - G x) (fun t₀ ht₀ ↦ by
    obtain ⟨c, ε, hε, hc⟩ := hloc t₀ ht₀
    filter_upwards [inter_mem_nhdsWithin (Icc a b) (ball_mem_nhds t₀ hε)] with u ⟨hu, huε⟩
    -- Compare `F` and `G` over the interval between `t₀` and `u`.
    have hcu := hc.mono (ordConnected_Icc.uIcc_subset_ball_inter ht₀ ⟨huε, hu⟩)
    have h₁ := hF.sub_eq_of_uIcc ht₀ hu hcu
    have h₂ := hG.sub_eq_of_uIcc ht₀ hu hcu
    linarith) ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  linarith

/-- **Existence of spectral flow potentials** for a continuous path of self-adjoint Fredholm
operators. -/
theorem exists_isSpectralFlowPotential {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) :
    ∃ F, IsSpectralFlowPotential A a b F :=
  exists_isSpectralFlowPotential_of_loc hA hsa fun _ ht ↦
    exists_isSpectralCutOn_ball_inter hA hsa hF ht

/-- **Uniqueness of spectral flow potentials**: for a continuous path of self-adjoint Fredholm
operators on `[a, b]`, any two potentials have the same increment over `[a, b]`. -/
theorem IsSpectralFlowPotential.sub_eq_sub {a b : ℝ} {F G : ℝ → ℤ}
    (hFp : IsSpectralFlowPotential A a b F) (hGp : IsSpectralFlowPotential A a b G) (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) : F b - F a = G b - G a :=
  hFp.sub_eq_sub_of_loc hGp hab fun _ ht ↦ exists_isSpectralCutOn_ball_inter hA hsa hF ht

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
  spectralFlow_eq_sub_of_loc hab (fun _ ht ↦ exists_isSpectralCutOn_ball_inter hA hsa hF ht)
    hFp

section Comparison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  [NormedAlgebra ℝ (K →L[𝕜] K)] [IsometricContinuousFunctionalCalculus ℝ (K →L[𝕜] K) IsSelfAdjoint]

/-- **Comparison of spectral flows.** A path `B`, on a possibly different Hilbert space, with the
same spectral flow potentials on `[a, b]` as a continuous path `A` of self-adjoint Fredholm
operators has the same spectral flow. No regularity of `B` is assumed. -/
theorem spectralFlow_eq_of_isSpectralFlowPotential_iff {B : ℝ → K →L[𝕜] K} {a b : ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    (h : ∀ F, IsSpectralFlowPotential B a b F ↔ IsSpectralFlowPotential A a b F) :
    spectralFlow B a b = spectralFlow A a b := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  have hB : ∃ G, IsSpectralFlowPotential B a b G := ⟨F, (h F).2 hFp⟩
  rw [spectralFlow_eq_sub hab hA hsa hF hFp]
  simp only [spectralFlow, hB, ↓reduceDIte]
  exact ((h _).1 hB.choose_spec).sub_eq_sub hFp hab hA hsa hF

/-- **Local comparison of spectral flows.** Two continuous paths `A` and `B` of self-adjoint
Fredholm operators, on possibly different Hilbert spaces, have the same spectral flow over
`[a, b]` if near every time `t` they have spectral cuts `c` and `c'` across which their counts of
eigenvalues change in the same way: for every nearby time `u`, the count of `B` in `[0, c']`
changes from `t` to `u` as much as the count of `A` in `[0, c]`. -/
theorem spectralFlow_eq_of_forall_exists_isSpectralCutOn [IsScalarTower ℝ 𝕜 (K →L[𝕜] K)]
    {B : ℝ → K →L[𝕜] K} {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) (hB : ContinuousOn B (Icc a b))
    (hsaB : ∀ t ∈ Icc a b, IsSelfAdjoint (B t)) (hFB : ∀ t ∈ Icc a b, (B t).IsFredholm)
    (hloc : ∀ t ∈ Icc a b, ∃ ε > 0, ∃ c c', IsSpectralCutOn A c (ball t ε ∩ Icc a b) ∧
      IsSpectralCutOn B c' (ball t ε ∩ Icc a b) ∧ ∀ u ∈ ball t ε ∩ Icc a b,
        (spectralCount c' (B u) : ℤ) - spectralCount c' (B t) =
          (spectralCount c (A u) : ℤ) - spectralCount c (A t)) :
    spectralFlow B a b = spectralFlow A a b := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  obtain ⟨G, hGp⟩ := exists_isSpectralFlowPotential hB hsaB hFB
  rw [spectralFlow_eq_sub hab hB hsaB hFB hGp, spectralFlow_eq_sub hab hA hsa hF hFp]
  -- The difference of the two potentials is locally constant on `[a, b]`.
  have := isPreconnected_Icc.apply_eq_of_eventually_eq (f := fun x ↦ G x - F x) (fun t₀ ht₀ ↦ by
    obtain ⟨ε, hε, c, c', hc, hc', hcount⟩ := hloc t₀ ht₀
    filter_upwards [inter_mem_nhdsWithin (Icc a b) (ball_mem_nhds t₀ hε)] with u ⟨hu, huε⟩
    have hsub := ordConnected_Icc.uIcc_subset_ball_inter ht₀ ⟨huε, hu⟩
    have h₁ := hFp.sub_eq_of_uIcc ht₀ hu (hc.mono hsub)
    have h₂ := hGp.sub_eq_of_uIcc ht₀ hu (hc'.mono hsub)
    have h₃ := hcount u ⟨huε, hu⟩
    linarith) ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  linarith

end Comparison

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

/-! ### Reparametrization -/

/-- For `φ` continuous on `[a, b]` and mapping it into `[p, q]`, the spectral flow of the
reparametrized path `A ∘ φ` from `a` to `b` is the increment `F (φ b) - F (φ a)` of a spectral
flow potential `F` of `A` on `[p, q]`. -/
private theorem spectralFlow_comp_eq_sub {φ : ℝ → ℝ} {a b p q : ℝ} {F : ℝ → ℤ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hmaps : MapsTo φ (Icc a b) (Icc p q))
    (hA : ContinuousOn A (Icc p q)) (hsa : ∀ t ∈ Icc p q, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc p q, (A t).IsFredholm) (hFp : IsSpectralFlowPotential A p q F) :
    spectralFlow (A ∘ φ) a b = F (φ b) - F (φ a) :=
  spectralFlow_eq_sub hab (hA.comp hφ hmaps) (fun _ ht ↦ hsa _ (hmaps ht))
    (fun _ ht ↦ hF _ (hmaps ht)) (hFp.comp_of_mapsTo hφ hmaps)

/-- **Reparametrization.** For `φ` continuous on `[a, b]` with `φ a ≤ φ b`, mapping `[a, b]` into
an interval `[p, q]` on which `A` is a continuous path of self-adjoint Fredholm operators, the
spectral flow of the reparametrized path `A ∘ φ` from `a` to `b` is the spectral flow of `A` from
`φ a` to `φ b`. The map `φ` need not be monotone, and may leave `[φ a, φ b]`. -/
theorem spectralFlow_comp_of_mapsTo {φ : ℝ → ℝ} {a b p q : ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hmaps : MapsTo φ (Icc a b) (Icc p q)) (hφab : φ a ≤ φ b)
    (hA : ContinuousOn A (Icc p q)) (hsa : ∀ t ∈ Icc p q, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc p q, (A t).IsFredholm) :
    spectralFlow (A ∘ φ) a b = spectralFlow A (φ a) (φ b) := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  have ha := hmaps ⟨le_rfl, hab⟩
  have hb := hmaps ⟨hab, le_rfl⟩
  have hsub : Icc (φ a) (φ b) ⊆ Icc p q := Icc_subset_Icc ha.1 hb.2
  rw [spectralFlow_comp_eq_sub hab hφ hmaps hA hsa hF hFp,
    spectralFlow_eq_sub hφab (hA.mono hsub) (fun t ht ↦ hsa t (hsub ht))
      (fun t ht ↦ hF t (hsub ht)) (hFp.mono ha.1 hb.2)]

/-- **Reparametrization reversing the direction.** For `φ` continuous on `[a, b]` with
`φ b ≤ φ a`, mapping `[a, b]` into an interval `[p, q]` on which `A` is a continuous path of
self-adjoint Fredholm operators, the spectral flow of the reparametrized path `A ∘ φ` from `a` to
`b` is minus the spectral flow of `A` from `φ b` to `φ a`. -/
theorem spectralFlow_comp_of_mapsTo_of_ge {φ : ℝ → ℝ} {a b p q : ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hmaps : MapsTo φ (Icc a b) (Icc p q)) (hφba : φ b ≤ φ a)
    (hA : ContinuousOn A (Icc p q)) (hsa : ∀ t ∈ Icc p q, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc p q, (A t).IsFredholm) :
    spectralFlow (A ∘ φ) a b = -spectralFlow A (φ b) (φ a) := by
  obtain ⟨F, hFp⟩ := exists_isSpectralFlowPotential hA hsa hF
  have ha := hmaps ⟨le_rfl, hab⟩
  have hb := hmaps ⟨hab, le_rfl⟩
  have hsub : Icc (φ b) (φ a) ⊆ Icc p q := Icc_subset_Icc hb.1 ha.2
  rw [spectralFlow_comp_eq_sub hab hφ hmaps hA hsa hF hFp,
    spectralFlow_eq_sub hφba (hA.mono hsub) (fun t ht ↦ hsa t (hsub ht))
      (fun t ht ↦ hF t (hsub ht)) (hFp.mono hb.1 ha.2), neg_sub]

/-- **Reversal.** Running the path backwards changes the sign of the spectral flow. -/
theorem spectralFlow_comp_neg {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) :
    spectralFlow (fun t ↦ A (-t)) (-b) (-a) = -spectralFlow A a b := by
  have h := spectralFlow_comp_of_mapsTo_of_ge (A := A) (φ := Neg.neg) (neg_le_neg hab)
    continuous_neg.continuousOn (fun _ ht ↦ ⟨le_neg.2 ht.2, neg_le.2 ht.1⟩)
    (by simpa using hab) hA hsa hF
  rw [neg_neg, neg_neg] at h
  exact h

/-! ### Homotopy invariance -/

/-- A path that is constant on `[a, b]` at a self-adjoint Fredholm operator has no spectral flow. -/
theorem spectralFlow_eq_zero_of_forall_eq {a b : ℝ} (hab : a ≤ b) (hsa : IsSelfAdjoint (A a))
    (hF : (A a).IsFredholm) (hA : ∀ t ∈ Icc a b, A t = A a) : spectralFlow A a b = 0 := by
  obtain ⟨c, hc, -, hev⟩ :=
    hsa.exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm hF one_pos
  obtain ⟨h₁, h₂, hfd, -⟩ := hev.self_of_nhdsWithin hsa
  have hcut : IsSpectralCutOn A c (Icc a b) := ⟨hc, fun t ht ↦ hA t ht ▸ ⟨h₁, h₂, hfd⟩⟩
  rw [spectralFlow_eq_of_isSpectralCutOn hab (continuousOn_const.congr hA)
    (fun t ht ↦ hA t ht ▸ hsa) hcut, hA b ⟨hab, le_rfl⟩, sub_self]

/-- A constant path at a self-adjoint Fredholm operator has no spectral flow. -/
theorem spectralFlow_const {a b : ℝ} (hab : a ≤ b) {T : H →L[𝕜] H} (hsa : IsSelfAdjoint T)
    (hF : T.IsFredholm) : spectralFlow (fun _ ↦ T) a b = 0 :=
  spectralFlow_eq_zero_of_forall_eq hab hsa hF fun _ _ ↦ rfl

/-- A continuous path of invertible self-adjoint operators on `[a, b]`, that is, of self-adjoint
operators without `0` in their spectra, has no spectral flow: no eigenvalue crosses `0`. -/
theorem spectralFlow_eq_zero_of_forall_zero_notMem_spectrum {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (h0 : ∀ t ∈ Icc a b, (0 : ℝ) ∉ spectrum ℝ (A t)) : spectralFlow A a b = 0 := by
  have hF (t : ℝ) (ht : t ∈ Icc a b) : (A t).IsFredholm :=
    (ContinuousLinearMap.isInvertible_iff_isUnit.2
      ((spectrum.zero_notMem_iff ℝ).1 (h0 t ht))).isFredholm
  -- Since `0` and the cut stay out of the spectrum, every local count vanishes.
  have hp : IsSpectralFlowPotential A a b 0 := by
    intro s t c has hst htb hc
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hr : spectralCount c (A t) = spectralCount c (A s) := by
      rw [spectralCount_def, spectralCount_def]
      exact isPreconnected_Icc.finrank_range_cfc_indicator_eq (hA.mono hsub)
        (fun u hu ↦ hsa u (hsub hu)) (Ω := Icc 0 c) (fun u hu ↦ disjoint_frontier_Icc
          (h0 u (hsub hu)) (hc.notMem_spectrum hu)) ⟨hst, le_rfl⟩ ⟨le_rfl, hst⟩
    simp [hr]
  rw [spectralFlow_eq_sub hab hA hsa hF hp]
  simp

section Homotopy

variable {G : ℝ → ℝ → H →L[𝕜] H} {u v a b : ℝ}

/-- The spectral flow around a thin rectangle `[u, v] × [a, b]` vanishes when every time `t₀` of
`[a, b]` has a neighbourhood which, together with `[u, v]`, carries a common spectral cut. -/
private theorem spectralFlow_sub_spectralFlow_of_forall_exists_isSpectralCutOn (hab : a ≤ b)
    (huv : u ≤ v) (hG₁ : ∀ s ∈ Icc u v, ContinuousOn (G s) (Icc a b))
    (hG₂ : ∀ t ∈ Icc a b, ContinuousOn (fun s ↦ G s t) (Icc u v))
    (hsa : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, IsSelfAdjoint (G s t))
    (hF : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, (G s t).IsFredholm)
    (hloc : ∀ t₀ ∈ Icc a b, ∃ c, ∃ ε > 0, ∀ s ∈ Icc u v,
      IsSpectralCutOn (G s) c (ball t₀ ε ∩ Icc a b)) :
    spectralFlow (G v) a b - spectralFlow (G u) a b =
      spectralFlow (fun s ↦ G s b) u v - spectralFlow (fun s ↦ G s a) u v := by
  have hu : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have hv : v ∈ Icc u v := ⟨huv, le_rfl⟩
  obtain ⟨Fu, hFu⟩ := exists_isSpectralFlowPotential (hG₁ u hu) (hsa u hu) (hF u hu)
  obtain ⟨Fv, hFv⟩ := exists_isSpectralFlowPotential (hG₁ v hv) (hsa v hv) (hF v hv)
  -- Along the strip, the difference of the potentials of the two sides minus the spectral flow
  -- of the vertical path is locally constant, hence constant.
  have hD' := isPreconnected_Icc.apply_eq_of_eventually_eq
      (f := fun t ↦ Fv t - Fu t - spectralFlow (fun s ↦ G s t) u v) (fun t₀ ht₀ ↦ by
    obtain ⟨c, ε, hε, hc⟩ := hloc t₀ ht₀
    filter_upwards [inter_mem_nhdsWithin (Icc a b) (ball_mem_nhds t₀ hε)] with t ⟨ht, htε⟩
    have hsub := ordConnected_Icc.uIcc_subset_ball_inter ht₀ ⟨htε, ht⟩
    -- The vertical path at a time of the neighbourhood has the cut `c`.
    have hvert {t' : ℝ} (ht' : t' ∈ ball t₀ ε ∩ Icc a b) :
        spectralFlow (fun s ↦ G s t') u v =
          (spectralCount c (G v t') : ℤ) - spectralCount c (G u t') :=
      spectralFlow_eq_of_isSpectralCutOn huv (hG₂ t' ht'.2) (fun s hs ↦ hsa s hs t' ht'.2)
        ⟨(hc u hu).pos, fun s hs ↦ (hc s hs).2 t' ht'⟩
    have h₁ := hFv.sub_eq_of_uIcc ht₀ ht ((hc v hv).mono hsub)
    have h₂ := hFu.sub_eq_of_uIcc ht₀ ht ((hc u hu).mono hsub)
    rw [hvert ⟨htε, ht⟩, hvert ⟨mem_ball_self hε, ht₀⟩]
    linarith) ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  rw [spectralFlow_eq_sub hab (hG₁ v hv) (hsa v hv) (hF v hv) hFv,
    spectralFlow_eq_sub hab (hG₁ u hu) (hsa u hu) (hF u hu) hFu]
  linarith

/-- By the Lebesgue number lemma on the compact rectangle `[u, v] × [a, b]`, there is a `δ > 0`
such that every product of `δ`-balls about points of the rectangle carries a common spectral cut
of a continuous family of self-adjoint Fredholm operators. -/
private theorem exists_pos_forall_exists_isSpectralCutOn_ball
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsa : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, IsSelfAdjoint (G s t))
    (hF : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, (G s t).IsFredholm) :
    ∃ δ > 0, ∀ s₀ ∈ Icc u v, ∀ t₀ ∈ Icc a b, ∃ c, ∀ s ∈ ball s₀ δ ∩ Icc u v,
      IsSpectralCutOn (G s) c (ball t₀ δ ∩ Icc a b) := by
  set K := Icc u v ×ˢ Icc a b
  -- Every point of the rectangle has a ball on which a single cut works.
  have hloc (z : ℝ × ℝ) (hz : z ∈ K) :
      ∃ c, ∃ ε > 0, IsSpectralCutOn (Function.uncurry G) c (ball z ε ∩ K) :=
    exists_isSpectralCutOn_ball_inter hG (fun w hw ↦ hsa w.1 hw.1 w.2 hw.2)
      (fun w hw ↦ hF w.1 hw.1 w.2 hw.2) hz
  obtain ⟨δ, hδ, hcut⟩ :=
    exists_pos_forall_exists_isSpectralCutOn_ball_inter (isCompact_Icc.prod isCompact_Icc) hloc
  refine ⟨δ, hδ, fun s₀ hs₀ t₀ ht₀ ↦ ?_⟩
  obtain ⟨c, hc⟩ := hcut (s₀, t₀) ⟨hs₀, ht₀⟩
  refine ⟨c, fun s hs ↦ ⟨hc.pos, fun t ht ↦ hc.2 (s, t) ⟨?_, hs.2, ht.2⟩⟩⟩
  rw [← ball_prod_same]
  exact ⟨hs.1, ht.1⟩

/-- **The spectral flow around a rectangle vanishes.** For a continuous two-parameter family
`G s t` of self-adjoint Fredholm operators on `[u, v] × [a, b]`, the spectral flow along the
bottom side `G u` followed by the right side `s ↦ G s b` equals the spectral flow along the left
side `s ↦ G s a` followed by the top side `G v`. -/
theorem spectralFlow_add_spectralFlow_eq_add (hab : a ≤ b) (huv : u ≤ v)
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsa : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, IsSelfAdjoint (G s t))
    (hF : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, (G s t).IsFredholm) :
    spectralFlow (G u) a b + spectralFlow (fun s ↦ G s b) u v =
      spectralFlow (fun s ↦ G s a) u v + spectralFlow (G v) a b := by
  obtain ⟨δ, hδ, hcut⟩ := exists_pos_forall_exists_isSpectralCutOn_ball hG hsa hF
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  -- The spectral flow of a side `[a, b]` at height `s` minus that of the right side up to `s`
  -- plus that of the left side up to `s`.
  set Θ : ℝ → ℤ := fun s ↦ spectralFlow (G s) a b - spectralFlow (fun s' ↦ G s' b) u s +
    spectralFlow (fun s' ↦ G s' a) u s
  -- On a strip of height less than `δ`, `Θ` takes the same value at both ends.
  have key {p q : ℝ} (hup : u ≤ p) (hpq : p ≤ q) (hqv : q ≤ v) (hlt : q - p < δ) : Θ q = Θ p := by
    have hsub : Icc p q ⊆ Icc u v := Icc_subset_Icc hup hqv
    have hstrip := spectralFlow_sub_spectralFlow_of_forall_exists_isSpectralCutOn hab hpq
      (fun s hs ↦ hG.uncurry_left s (hsub hs)) (fun t ht ↦ (hG.uncurry_right t ht).mono hsub)
      (fun s hs ↦ hsa s (hsub hs)) (fun s hs ↦ hF s (hsub hs)) fun t₀ ht₀ ↦ by
        obtain ⟨c, hc⟩ := hcut p ⟨hup, hpq.trans hqv⟩ t₀ ht₀
        exact ⟨c, δ, hδ, fun s hs ↦
          hc s ⟨Real.Icc_subset_ball (by linarith) (by linarith) hs, hsub hs⟩⟩
    -- Split the vertical sides at `p`.
    have hconcat {t : ℝ} (ht : t ∈ Icc a b) : spectralFlow (fun s ↦ G s t) u q =
        spectralFlow (fun s ↦ G s t) u p + spectralFlow (fun s ↦ G s t) p q :=
      spectralFlow_add_adjacent_intervals hup hpq
        ((hG.uncurry_right t ht).mono (Icc_subset_Icc le_rfl hqv))
        (fun s hs ↦ hsa s ⟨hs.1, hs.2.trans hqv⟩ t ht)
        (fun s hs ↦ hF s ⟨hs.1, hs.2.trans hqv⟩ t ht)
    simp only [Θ, hconcat ha, hconcat hb]
    linarith
  have := isPreconnected_Icc.apply_eq_of_eventually_eq (f := Θ) (fun σ hσ ↦ by
    filter_upwards [inter_mem_nhdsWithin (Icc u v) (ball_mem_nhds σ hδ)] with s ⟨hs, hsδ⟩
    rw [Real.ball_eq_Ioo] at hsδ
    rcases le_total s σ with h | h
    · exact (key hs.1 h hσ.2 (by linarith [hsδ.1])).symm
    · exact key hσ.1 h hs.2 (by linarith [hsδ.2])) ⟨huv, le_rfl⟩ ⟨le_rfl, huv⟩
  simp only [Θ, spectralFlow_self] at this
  linarith

/-- **Homotopy invariance of the spectral flow.** Two continuous paths of self-adjoint Fredholm
operators on `[a, b]` joined by a continuous family `G` of such paths over `[u, v]` whose
endpoints `G s a` and `G s b` do not move have the same spectral flow. -/
theorem spectralFlow_eq_of_homotopy (hab : a ≤ b) (huv : u ≤ v)
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsa : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, IsSelfAdjoint (G s t))
    (hF : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, (G s t).IsFredholm)
    (ha : ∀ s ∈ Icc u v, G s a = G u a) (hb : ∀ s ∈ Icc u v, G s b = G u b) :
    spectralFlow (G v) a b = spectralFlow (G u) a b := by
  have hu : u ∈ Icc u v := ⟨le_rfl, huv⟩
  have := spectralFlow_add_spectralFlow_eq_add hab huv hG hsa hF
  rw [spectralFlow_eq_zero_of_forall_eq huv (hsa u hu a ⟨le_rfl, hab⟩) (hF u hu a ⟨le_rfl, hab⟩)
      ha,
    spectralFlow_eq_zero_of_forall_eq huv (hsa u hu b ⟨hab, le_rfl⟩) (hF u hu b ⟨hab, le_rfl⟩)
      hb] at this
  linarith

/-- **Homotopy invariance with invertible endpoints.** Two continuous paths of self-adjoint
Fredholm operators on `[a, b]` joined by a continuous family `G` of such paths over `[u, v]` whose
endpoints `G s a` and `G s b` stay invertible have the same spectral flow. -/
theorem spectralFlow_eq_of_homotopy_of_zero_notMem_spectrum (hab : a ≤ b) (huv : u ≤ v)
    (hG : ContinuousOn (Function.uncurry G) (Icc u v ×ˢ Icc a b))
    (hsa : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, IsSelfAdjoint (G s t))
    (hF : ∀ s ∈ Icc u v, ∀ t ∈ Icc a b, (G s t).IsFredholm)
    (ha : ∀ s ∈ Icc u v, (0 : ℝ) ∉ spectrum ℝ (G s a))
    (hb : ∀ s ∈ Icc u v, (0 : ℝ) ∉ spectrum ℝ (G s b)) :
    spectralFlow (G v) a b = spectralFlow (G u) a b := by
  have := spectralFlow_add_spectralFlow_eq_add hab huv hG hsa hF
  rw [spectralFlow_eq_zero_of_forall_zero_notMem_spectrum huv
      (hG.uncurry_right a (left_mem_Icc.2 hab)) (fun s hs ↦ hsa s hs a ⟨le_rfl, hab⟩) ha,
    spectralFlow_eq_zero_of_forall_zero_notMem_spectrum huv
      (hG.uncurry_right b (right_mem_Icc.2 hab)) (fun s hs ↦ hsa s hs b ⟨hab, le_rfl⟩) hb] at this
  linarith

end Homotopy

end TauCeti
