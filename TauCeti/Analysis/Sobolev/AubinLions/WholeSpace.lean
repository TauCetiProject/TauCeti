/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.AubinLions.Basic
public import TauCeti.Analysis.Sobolev.GraphStep.LocalCompactness
public import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.Analysis.Sobolev.GraphStep.Coordinates
import TauCeti.Order.Filter.AtTopBot

/-!
# The Aubin–Lions theorem on the whole space

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
`F` a finite-dimensional real inner product space. Write `H¹(E, F)` for the first-order Sobolev
space `TauCeti.WeakDerivStep μ ⊤ 2 (id)` of `F`-valued fields on `E`, and `H⁻¹(E, F)` for its dual.
A field `u ∈ H¹(E, F)` acts on `H¹(E, F)` through the `L²` pairing `v ↦ ∫ ⟪u, v⟫`, which is
`ι.gelfandDual (ι u)` for the field map `ι : H¹(E, F) → L²(E, F)`.

This file proves the local form of the Aubin–Lions theorem used on the whole space: a sequence
`uₙ` bounded in `Lᵖ(a, b; H¹(E, F))`, whose time derivatives, taken in `H⁻¹(E, F)`, are bounded
in `Lʳ(a, b; H⁻¹(E, F))` for some `r > 1`, has a subsequence converging in `Lᵖ(a, b; L²(B, F))`
for every bounded set `B ⊆ E`
(`TauCeti.exists_subseq_forall_tendsto_eLpNorm_restrict_of_hasWeakLineDerivOn`).
This is the compactness step in the construction of Leray–Hopf weak solutions of the
Navier–Stokes equations on the whole space, with `p = 2`.

The conclusion is only local. Translates `u(· - n e)` of a fixed nonzero `u ∈ H¹(E, F)`, constant in
time, are bounded with zero time derivative, and have no subsequence converging in `L²(E, F)`.

## Proof

Fix a smooth cutoff `χ` with compact support, equal to one on a ball. Multiplication by `χ`
followed by the field map, `u ↦ χ u`, is a compact operator `H¹(E, F) → L²(E, F)`
(`TauCeti.WeakDerivStep.isCompactOperator_prevL_comp_smulLeftCLM`), the fields of `H¹(E, F)` are
dense in `L²(E, F)` (`TauCeti.WeakDerivStep.denseRange_prevL_two`), and multiplication by `χ` is
symmetric for the `L²` pairing (`TauCeti.WeakDerivStep.inner_prev_smulLeftCLM`). The Gelfand-triple
form of the abstract theorem,
`IsCompactOperator.exists_subseq_tendsto_eLpNorm_of_hasWeakLineDerivOn_gelfandDual`, then gives a
subsequence along which `χ uₙ` converges in `Lᵖ(a, b; L²(E, F))`, hence `uₙ` converges on the ball
where `χ = 1`. A diagonal
extraction over the balls of integer radius gives one subsequence for every bounded set.

## References

* J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non linéaires*,
  Dunod, 1969, Chapitre 1, Théorème 5.1.
* J. Simon, *Compact sets in the space `Lᵖ(0, T; B)`*, Ann. Mat. Pura Appl. **146** (1987),
  65–96, Corollary 4.
-/

public section

open MeasureTheory Set Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {μ : Measure E} [μ.IsAddHaarMeasure] {p r : ℝ≥0∞} {a b : ℝ}
  {M M' : ℝ≥0}
  {u : ℕ → ℝ → WeakDerivStep μ ⊤ 2 (ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E))))}
  {u' : ℕ → ℝ → StrongDual ℝ
    (WeakDerivStep μ ⊤ 2 (ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E)))))}

/-- The Aubin–Lions theorem on the whole space for the localized fields `ψ u n`, where `ψ` is a
smooth function with compact support: a subsequence of `ψ u n` converges in
`Lᵖ(a, b; L²(E, F))`. -/
private theorem exists_subseq_tendsto_eLpNorm_prev_smulLeftCLM {ψ : E → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ (⊤ : Opens E)) (h₀ : ∃ C, ∀ x ∈ (⊤ : Opens E), ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ (⊤ : Opens E), ‖fderiv ℝ ψ x‖ ≤ C) (hc : HasCompactSupport ψ)
    (hp : 1 ≤ p) (hr : 1 < r) (huM : ∀ n, eLpNorm (u n) p (volume.restrict (Ioo a b)) ≤ M)
    (hderiv : ∀ n, HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ (WeakDerivStep.prevL
        (ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E))))).gelfandDual
          (WeakDerivStep.prev _ (u n t))) (u' n) 1)
    (hu'M : ∀ n, eLpNorm (u' n) r (volume.restrict (Ioo a b)) ≤ M') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → Lp F 2 (μ.restrict (⊤ : Opens E)),
      MemLp g p (volume.restrict (Ioo a b)) ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦ WeakDerivStep.prev _
          (WeakDerivStep.smulLeftCLM ψ hψ h₀ h₁ (fun _ _ ↦ rfl) (u (φ n) t)) - g t) p
        (volume.restrict (Ioo a b))) atTop (𝓝 0) := by
  have hm (v w : WeakDerivStep μ ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E))))) :
      ⟪WeakDerivStep.prevL _ (WeakDerivStep.smulLeftCLM ψ hψ h₀ h₁ (fun _ _ ↦ rfl) v),
      WeakDerivStep.prevL _ w⟫_ℝ = ⟪WeakDerivStep.prevL _ v,
        WeakDerivStep.prevL _ (WeakDerivStep.smulLeftCLM ψ hψ h₀ h₁ (fun _ _ ↦ rfl) w)⟫_ℝ := by
    simpa only [WeakDerivStep.prevL_apply] using
      WeakDerivStep.inner_prev_smulLeftCLM hψ h₀ h₁ (fun _ _ ↦ rfl) v w
  have hi : IsCompactOperator ((WeakDerivStep.prevL
      (ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E))))).comp
        (WeakDerivStep.smulLeftCLM ψ hψ h₀ h₁ fun _ _ ↦ rfl)) :=
    WeakDerivStep.isCompactOperator_prevL_comp_smulLeftCLM hψ h₀ h₁ hc (subset_univ _)
  obtain ⟨φ, hφ, g, hg, hconv⟩ :=
    hi.exists_subseq_tendsto_eLpNorm_of_hasWeakLineDerivOn_gelfandDual
        WeakDerivStep.denseRange_prevL_two hm hp hr huM
        (fun n ↦ by simpa only [WeakDerivStep.prevL_apply] using hderiv n) hu'M
  exact ⟨φ, hφ, g, hg, by simpa only [WeakDerivStep.prevL_apply] using hconv⟩

/-- The Aubin–Lions theorem on the whole space, for the sets inside one ball: the subsequence
may depend on the radius. -/
private theorem exists_subseq_forall_subset_ball_tendsto_eLpNorm (hp : 1 ≤ p) (hr : 1 < r)
    (huM : ∀ n, eLpNorm (u n) p (volume.restrict (Ioo a b)) ≤ M)
    (hderiv : ∀ n, HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ (WeakDerivStep.prevL
        (ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E))))).gelfandDual
          (WeakDerivStep.prev _ (u n t))) (u' n) 1)
    (hu'M : ∀ n, eLpNorm (u' n) r (volume.restrict (Ioo a b)) ≤ M') (R : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B ⊆ ball (0 : E) R, ∃ g : ℝ → Lp F 2 (μ.restrict B),
      MemLp g p (volume.restrict (Ioo a b)) ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦ Lp.restrictOfSubsetL (t := ((⊤ : Opens E) : Set E))
          (subset_univ B) (WeakDerivStep.prev _ (u (φ n) t)) - g t) p
        (volume.restrict (Ioo a b))) atTop (𝓝 0) := by
  -- A smooth cutoff `χ`, equal to one on `ball 0 R` and with compact support.
  let χ : ContDiffBump (0 : E) :=
    ⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  have hχ' : ContDiff ℝ ∞ χ := χ.contDiff
  have hχ : ContDiffOn ℝ ∞ χ (⊤ : Opens E) := hχ'.contDiffOn
  have h₀ : ∃ C, ∀ x ∈ (⊤ : Opens E), ‖χ x‖ ≤ C :=
    ⟨1, fun x _ ↦ by rw [Real.norm_of_nonneg χ.nonneg]; exact χ.le_one⟩
  have h₁ : ∃ C, ∀ x ∈ (⊤ : Opens E), ‖fderiv ℝ χ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hχ'.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (χ.hasCompactSupport.fderiv ℝ)
    exact ⟨C, fun x _ ↦ hC x⟩
  set m := WeakDerivStep.smulLeftCLM (χ : E → ℝ) hχ h₀ h₁
    (T := ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E)))) fun _ _ ↦ rfl
  obtain ⟨φ, hφ, g, hg, hconv⟩ :=
    exists_subseq_tendsto_eLpNorm_prev_smulLeftCLM hχ h₀ h₁ χ.hasCompactSupport hp hr huM hderiv
      hu'M
  refine ⟨φ, hφ, fun B hB ↦ ?_⟩
  set L := Lp.restrictOfSubsetL (F := F) (μ := μ) (p := 2) (t := ((⊤ : Opens E) : Set E))
    (subset_univ B) with hL
  refine ⟨fun t ↦ L (g t), L.comp_memLp' hg, ?_⟩
  -- On `B`, `χ u = u`, and restriction to `B` does not increase norms.
  have hres (w) : L (WeakDerivStep.prev _ w) = L (WeakDerivStep.prev _ (m w)) := by
    rw [hL]
    refine Lp.ext ?_
    have hB' : ∀ᵐ x ∂μ.restrict B, x ∈ closedBall (0 : E) χ.rIn :=
      ae_mono (Measure.restrict_mono_set μ (hB.trans (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (le_max_left R 1)))))
        (ae_restrict_mem measurableSet_closedBall)
    filter_upwards [Lp.coeFn_restrictOfSubsetL (subset_univ B) (WeakDerivStep.prev _ w),
      Lp.coeFn_restrictOfSubsetL (subset_univ B) (WeakDerivStep.prev _ (m w)),
      ae_mono (Measure.restrict_mono_set μ (subset_univ B))
        (WeakDerivStep.prev_smulLeftCLM_ae hχ h₀ h₁ (fun _ _ ↦ rfl) w), hB']
      with x hx₁ hx₂ hx₃ hx
    rw [hx₁, hx₂, hx₃, χ.one_of_mem_closedBall hx, one_smul]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ ↦ zero_le)
    fun n ↦ ?_
  have hu : MemLp (u (φ n)) p (volume.restrict (Ioo a b)) :=
    (huM (φ n)).trans_lt ENNReal.coe_lt_top
  have hmeas : AEStronglyMeasurable (fun t ↦ WeakDerivStep.prev _ (m (u (φ n) t)) - g t)
      (volume.restrict (Ioo a b)) := by
    simpa only [Pi.sub_def, ContinuousLinearMap.comp_apply, WeakDerivStep.prevL_apply] using
      (((WeakDerivStep.prevL _).comp m).continuous.comp_aestronglyMeasurable
        hu.aestronglyMeasurable).sub hg.aestronglyMeasurable
  calc _ = eLpNorm (fun t ↦ L (WeakDerivStep.prev _ (m (u (φ n) t)) - g t)) p
        (volume.restrict (Ioo a b)) := by simp only [map_sub, ← hres]
    _ ≤ _ := eLpNorm_mono (L.continuous.comp_aestronglyMeasurable hmeas) fun t ↦
        (L.le_of_opNorm_le (Lp.norm_restrictOfSubsetL_le _) _).trans_eq (one_mul _)

/-- **The Aubin–Lions theorem on the whole space, local form.** Let `1 ≤ p ≤ ∞` and `1 < r ≤ ∞`.
Let `u n` be bounded in `Lᵖ(a, b; H¹(E, F))`, and let the `H⁻¹(E, F)`-valued functions
`t ↦ (v ↦ ∫ ⟪u n t, v⟫)` have weak time derivatives `u' n` on `(a, b)` bounded in
`Lʳ(a, b; H⁻¹(E, F))`. Then one subsequence of `u n` converges in `Lᵖ(a, b; L²(B, F))` for every
bounded set `B ⊆ E`. -/
theorem exists_subseq_forall_tendsto_eLpNorm_restrict_of_hasWeakLineDerivOn (hp : 1 ≤ p)
    (hr : 1 < r) (huM : ∀ n, eLpNorm (u n) p (volume.restrict (Ioo a b)) ≤ M)
    (hderiv : ∀ n, HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ (WeakDerivStep.prevL
        (ContinuousLinearMap.id ℝ (Lp F 2 (μ.restrict (⊤ : Opens E))))).gelfandDual
          (WeakDerivStep.prev _ (u n t))) (u' n) 1)
    (hu'M : ∀ n, eLpNorm (u' n) r (volume.restrict (Ioo a b)) ≤ M') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B : Set E, Bornology.IsBounded B →
      ∃ g : ℝ → Lp F 2 (μ.restrict B), MemLp g p (volume.restrict (Ioo a b)) ∧
        Tendsto (fun n ↦ eLpNorm (fun t ↦ Lp.restrictOfSubsetL (t := ((⊤ : Opens E) : Set E))
            (subset_univ B) (WeakDerivStep.prev _ (u (φ n) t)) - g t) p
          (volume.restrict (Ioo a b))) atTop (𝓝 0) := by
  -- Extract diagonally over the balls of radius `k`, passing to further subsequences.
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_antitone
    (P := fun k l ↦ ∀ B ⊆ ball (0 : E) k, ∃ g : ℝ → Lp F 2 (μ.restrict B),
      MemLp g p (volume.restrict (Ioo a b)) ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦ Lp.restrictOfSubsetL (t := ((⊤ : Opens E) : Set E))
          (subset_univ B) (WeakDerivStep.prev _ (u n t)) - g t) p
        (volume.restrict (Ioo a b))) l (𝓝 0))
    (fun _ _ _ hl h B hB ↦ (h B hB).imp fun _ hg ↦ ⟨hg.1, hg.2.mono_left hl⟩) fun k ψ _ ↦ by
      obtain ⟨ψ', hψ', h⟩ := exists_subseq_forall_subset_ball_tendsto_eLpNorm (u := fun n ↦ u (ψ n))
        hp hr (fun n ↦ huM (ψ n)) (fun n ↦ hderiv (ψ n)) (fun n ↦ hu'M (ψ n)) k
      exact ⟨ψ', hψ', fun B hB ↦ (h B hB).imp fun _ hg ↦ ⟨hg.1, tendsto_map'_iff.2 hg.2⟩⟩
  refine ⟨φ, hφ, fun B hB ↦ ?_⟩
  obtain ⟨R, hR⟩ := hB.subset_ball 0
  obtain ⟨k, hk⟩ := exists_nat_gt R
  exact (hP k B (hR.trans (ball_subset_ball hk.le))).imp fun _ hg ↦
    ⟨hg.1, tendsto_map'_iff.1 hg.2⟩

end TauCeti
