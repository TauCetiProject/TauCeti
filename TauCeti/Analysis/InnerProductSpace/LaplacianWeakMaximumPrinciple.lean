/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.InnerProductSpace.LaplacianMaximumPrinciple

/-!
# The weak maximum principle for subharmonic functions

`TauCeti.Analysis.InnerProductSpace.LaplacianMaximumPrinciple` proves the *strict* boundary
maximum principle: a `C²` function with `0 < Δ f` on the interior of a compact set attains its
maximum on the frontier. That strict hypothesis is only a warm-up; the theorem PDE theory
actually uses is the **weak maximum principle**, which relaxes `0 < Δ f` to the borderline
`0 ≤ Δ f` (subharmonic). This file supplies it, in bound form and in the extremum (`∃`) form.

## Main declarations

* `TauCeti.le_of_laplacian_nonneg_le_frontier`: **weak maximum principle**. A continuous function
  on a compact set that is `C²` and subharmonic (`0 ≤ Δ f`) on the interior is bounded on all of
  `K` by any bound it satisfies on `frontier K`.
* `TauCeti.ge_of_laplacian_nonpos_ge_frontier`: the dual weak minimum principle for superharmonic
  functions (`Δ f ≤ 0`).
* `TauCeti.exists_mem_frontier_isMaxOn_of_laplacian_nonneg` /
  `TauCeti.exists_mem_frontier_isMinOn_of_laplacian_nonpos`: on a nonempty compact set in a
  nontrivial finite-dimensional real inner product space, a subharmonic (resp. superharmonic)
  function attains a maximum (resp. minimum) on the frontier.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Nontrivial

variable [Nontrivial E]

/-- **Weak maximum principle for subharmonic functions.**

Let `K` be compact. If `f` is continuous on `K`, is `C²` on `interior K`, and is subharmonic
there (`0 ≤ Δ f`), then any bound `m` that `f` respects on `frontier K` bounds `f` on all of `K`. -/
theorem le_of_laplacian_nonneg_le_frontier {K : Set E} (hK : IsCompact K) {f : E → ℝ} {m : ℝ}
    (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ Δ f x) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  -- Perturb `f` to the strictly subharmonic `f + ε‖·‖²`, apply the strict boundary maximum
  -- principle, and let `ε → 0`.
  intro x hxK
  -- `‖·‖²` is bounded above by some `C ≥ 0` on the compact set `K`.
  obtain ⟨C, hCub⟩ := hK.bddAbove_image (f := fun y : E => ‖y‖ ^ 2) (by fun_prop)
  have hCnonneg : 0 ≤ C := le_trans (sq_nonneg _) (hCub ⟨x, hxK, rfl⟩)
  have hfrpos : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  -- Perturbation estimate: `f x ≤ m + ε C` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → f x ≤ m + ε * C := by
    intro ε hε
    have hεsq : ∀ y : E, ContDiffAt ℝ 2 (fun z : E => ε • ‖z‖ ^ 2) y :=
      fun y => ((contDiff_norm_sq ℝ).contDiffAt).const_smul ε
    have hgcont : ContinuousOn (fun y : E => f y + ε • ‖y‖ ^ 2) K := hcont.add (by fun_prop)
    have hgcd : ∀ ⦃y⦄, y ∈ interior K → ContDiffAt ℝ 2 (fun y : E => f y + ε • ‖y‖ ^ 2) y :=
      fun y hy => (hcd hy).add (hεsq y)
    have hglap : ∀ ⦃y⦄, y ∈ interior K → 0 < Δ (fun y : E => f y + ε • ‖y‖ ^ 2) y := by
      intro y hy
      have hadd : Δ (fun y : E => f y + ε • ‖y‖ ^ 2) y
          = Δ f y + Δ (fun z : E => ε • ‖z‖ ^ 2) y := (hcd hy).laplacian_add (hεsq y)
      have hsmul : Δ (fun z : E => ε • ‖z‖ ^ 2) y = ε • Δ (fun z : E => ‖z‖ ^ 2) y :=
        laplacian_smul ε (contDiff_norm_sq ℝ).contDiffAt
      have hΔ : Δ (fun y : E => f y + ε • ‖y‖ ^ 2) y
          = Δ f y + ε * (2 * (Module.finrank ℝ E : ℝ)) := by
        rw [hadd, hsmul, laplacian_norm_sq, smul_eq_mul]
      rw [hΔ]
      have hpos : 0 < ε * (2 * (Module.finrank ℝ E : ℝ)) := mul_pos hε (mul_pos two_pos hfrpos)
      linarith [hlap hy]
    -- Strict boundary maximum principle applied to the perturbed function.
    obtain ⟨z, hzfr, hzmax⟩ :=
      exists_mem_frontier_isMaxOn_of_laplacian_pos hK ⟨x, hxK⟩ hgcont hgcd hglap
    have hzK : z ∈ K := hK.isClosed.frontier_subset hzfr
    have hxle : f x + ε * ‖x‖ ^ 2 ≤ f z + ε * ‖z‖ ^ 2 := by
      simpa [smul_eq_mul] using hzmax hxK
    have hzC : ‖z‖ ^ 2 ≤ C := hCub ⟨z, hzK, rfl⟩
    have := mul_le_mul_of_nonneg_left hzC hε.le
    have := mul_nonneg hε.le (sq_nonneg ‖x‖)
    linarith [hbdry hzfr]
  -- Let `ε → 0`.
  rcases eq_or_lt_of_le hCnonneg with hC0 | hCpos
  · have := key 1 one_pos
    rw [← hC0] at this
    simpa using this
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hk := key (δ / C) (by positivity)
    have : δ / C * C = δ := by field_simp
    linarith

/-- **Weak minimum principle for superharmonic functions.**

The dual of `le_of_laplacian_nonneg_le_frontier`: a continuous, `C²`, superharmonic (`Δ f ≤ 0`)
function on a compact set is bounded below on `K` by any lower bound it respects on `frontier K`.
-/
theorem ge_of_laplacian_nonpos_ge_frontier {K : Set E} (hK : IsCompact K) {f : E → ℝ} {m : ℝ}
    (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x ≤ 0) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hxK
  have hle := le_of_laplacian_nonneg_le_frontier (f := -f) (m := -m) hK hcont.neg
    (fun y hy => (hcd hy).neg)
    (fun y hy => by
      rw [congrFun laplacian_neg y, Pi.neg_apply]; linarith [hlap hy])
    (fun y hy => neg_le_neg (hbdry hy)) hxK
  simp only [Pi.neg_apply] at hle
  linarith

/-- A subharmonic (`0 ≤ Δ f`) continuous function on a nonempty compact set in a nontrivial
finite-dimensional real inner product space attains a maximum on the frontier. This is the
`∃`-form of the weak maximum principle, mirroring
`exists_mem_frontier_isMaxOn_of_laplacian_pos` for the strict case. -/
theorem exists_mem_frontier_isMaxOn_of_laplacian_nonneg {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ Δ f x) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  have hfrsub : frontier K ⊆ K := hK.isClosed.frontier_subset
  have hfrcompact : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier hfrsub
  have hfrne : (frontier K).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rcases frontier_eq_empty_iff.mp hempty with h | h
    · exact hne.ne_empty h
    · exact noncompact_univ E (h ▸ hK)
  obtain ⟨z, hzfr, hzmax⟩ := hfrcompact.exists_isMaxOn hfrne (hcont.mono hfrsub)
  refine ⟨z, hzfr, isMaxOn_iff.mpr fun y hyK => ?_⟩
  exact le_of_laplacian_nonneg_le_frontier hK hcont hcd hlap
    (fun w hw => isMaxOn_iff.mp hzmax w hw) hyK

/-- A superharmonic (`Δ f ≤ 0`) continuous function on a nonempty compact set in a nontrivial
finite-dimensional real inner product space attains a minimum on the frontier. -/
theorem exists_mem_frontier_isMinOn_of_laplacian_nonpos {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x ≤ 0) :
    ∃ x ∈ frontier K, IsMinOn f K x := by
  obtain ⟨z, hzfr, hzmax⟩ := exists_mem_frontier_isMaxOn_of_laplacian_nonneg hK hne hcont.neg
    (fun y hy => (hcd hy).neg)
    (fun y hy => by
      rw [congrFun laplacian_neg y, Pi.neg_apply]; linarith [hlap hy])
  refine ⟨z, hzfr, isMinOn_iff.mpr fun y hyK => ?_⟩
  have := isMaxOn_iff.mp hzmax y hyK
  simpa using neg_le_neg this

end Nontrivial

end TauCeti

end
