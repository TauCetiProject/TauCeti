/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev

/-!
# Interior elliptic estimates on a manifold

Let `P` be a properly supported classical pseudodifferential operator of order `m` on a σ-compact
manifold `M` modelled on `ℝⁿ`, which need not be compact, and suppose that `P` is elliptic
(`TauCeti.IsClassicalElliptic`). Read smooth functions in charts through cutoffs: `u` is read in
a chart `e` through a cutoff `φ` as the Schwartz function `φ · (u ∘ e⁻¹)` on `ℝⁿ`. This file proves
the **interior elliptic estimate**: for a cutoff `φ` in a chart `e` there is a compact set
`K ⊆ M` such that, for finitely many cutoffs `ψᵢ` in charts `e'ᵢ` whose readings `ψᵢ ∘ e'ᵢ` on
`M` add up to `1` on `K`, for all real `s` and `r` and `1 < p < ∞` there is a constant `C` with

`‖φ · (u ∘ e⁻¹)‖_{H^{s + m,p}} ≤
  C (∑ᵢ ‖ψᵢ · ((P u) ∘ e'ᵢ⁻¹)‖_{H^{s,p}} + ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{r,p}})`

for every smooth `u` on `M`
(`TauCeti.IsClassicalElliptic.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_add`).
The `H^{s + m,p}` norm of `u` near the support of `φ` is controlled by the `H^{s,p}` norm of `P u`
and an arbitrarily weak norm of `u`, both on the compact set `K`, with no global hypothesis on `u`.
The set `K` does not depend on `s`, `r` or `p`, and cutoffs `ψᵢ` adding up to `1` on it exist
(`IsCompact.exists_sum_cutoffPullback_eq_one`). On a compact manifold every operator is properly
supported, and cutoffs adding up to `1` everywhere serve for every `K`; summing the estimate over
finitely many cutoffs `φⱼ` then gives the global elliptic estimate
(`TauCeti.IsClassicalElliptic.exists_sum_norm_le_add`).

The proof is the parametrix argument of the compact case, localized by proper support. A
parametrix `Q` of `P`, of order `-m`, has `R = Q P - 1` of order `-∞`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`), so
`u = Q (P u) - R u`. Both `Q` and `R` are properly supported, so near the support of `φ` the
readings of `Q (P u)` and `R u` only depend on `P u` and `u` on a compact set `K`, and they are
bounded in `H^{s + m,p}` by the readings of `P u` in `H^{s,p}` and of `u` in `H^{r,p}`
(`TauCeti.IsProperlySupported.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_sum`),
since `R` has every order `-N`, in particular one with `s + m ≤ r + N`.

## Main results

* `TauCeti.IsClassicalElliptic.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_add`: the
  interior elliptic estimate in `H^{s,p}` norms, `1 < p < ∞`, on a σ-compact manifold.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (4.6)–(4.11)
  and Lecture II, (3.1)–(3.8).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (properly supported operators and parametrices on manifolds).
-/

public section

open OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap ENNReal

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}

/-- **The interior elliptic estimate on a manifold.** Let `P` be a properly supported elliptic
classical pseudodifferential operator of order `m` on a σ-compact manifold, and `φ` a cutoff in a
chart `e`. There is a compact set `K ⊆ M` with the following property. Let `ψᵢ` be finitely many
cutoffs in charts `e'ᵢ` whose readings `ψᵢ ∘ e'ᵢ` on `M`, extended by `0`, add up to `1` on `K`.
Such cutoffs exist (`IsCompact.exists_sum_cutoffPullback_eq_one`). Then for all real `s` and `r`
and `1 < p < ∞` there is a constant `C` such that every smooth `u` on `M` satisfies

`‖φ · (u ∘ e⁻¹)‖_{H^{s + m,p}} ≤
  C (∑ᵢ ‖ψᵢ · ((P u) ∘ e'ᵢ⁻¹)‖_{H^{s,p}} + ∑ᵢ ‖ψᵢ · (u ∘ e'ᵢ⁻¹)‖_{H^{r,p}})`. -/
theorem IsClassicalElliptic.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_add
    [SigmaCompactSpace M] (hPe : IsClassicalElliptic m P) (hPs : IsProperlySupported P)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ K : Set M, IsCompact K ∧ ∀ {ι : Type*} [Fintype ι]
      {e' : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
      (he' : ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (ψ : ∀ i, 𝓓(⟨(e' i).target, (e' i).open_target⟩, ℝ)),
      (∀ x ∈ K, ∑ i, (e' i).cutoffPullback (he' i) (ψ i) 1 x = 1) →
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ → ∀ s r : ℝ, ∃ C,
        ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
          ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) p (e.cutoffPushforwardSchwartz he φ u)‖ ≤
            C * (∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s p
                ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖ +
              ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r p
                ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖) := by
  -- A parametrix `Q` of order `-m`, with `R = Q P - 1` of order `-∞`; both are properly supported.
  obtain ⟨Q, hQ, -, hR⟩ := hPe.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators hPs
  set R := Q ∘ₗ P - LinearMap.id with hRdef
  have hQs : IsProperlySupported Q := (mem_classicalPseudodifferentialOperators_iff.1 hQ).1
  have hRs : IsProperlySupported R := (mem_classicalPseudodifferentialOperators_iff.1
    (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators 0 hR)).1
  obtain ⟨K₁, hK₁, hQK⟩ :=
    hQs.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_sum he φ
  obtain ⟨K₂, hK₂, hRK⟩ :=
    hRs.exists_isCompact_forall_norm_toBesselPotentialSpaceCLM_le_sum he φ
  refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun {ι} _ e' he' ψ hψ p _ hp hp_top s r ↦ ?_⟩
  -- `R` has an order `-N` with `s + m ≤ r + N`.
  set N := ⌈s + m - r⌉₊
  have hN : s + m ≤ r - -(N : ℝ) := by
    linarith [Nat.le_ceil (s + m - r)]
  obtain ⟨A, hA⟩ := hQK he' ψ (fun x hx ↦ hψ x (Or.inl hx)) _ hQ p hp hp_top s
  obtain ⟨B, hB⟩ := hRK he' ψ (fun x hx ↦ hψ x (Or.inr hx)) _
    (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators _ hR) p hp hp_top
    r
  rw [sub_neg_eq_add] at hA
  set c := ‖(BesselPotentialSpace.inclusion (E := CoordinateSpace n) (G := ℂ) (p := p) hN)‖
  refine ⟨|A| + c * |B|, fun u ↦ ?_⟩
  set X := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM s p
    ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) (P u))‖
  set Y := ∑ i, ‖SchwartzMap.toBesselPotentialSpaceCLM r p
    ((e' i).cutoffPushforwardSchwartz (he' i) (ψ i) u)‖
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  -- The reading of `u = Q (P u) - R u` is split accordingly.
  have hu : ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) p (e.cutoffPushforwardSchwartz he φ u)‖ ≤
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s + m) p
        (e.cutoffPushforwardSchwartz he φ (Q (P u)))‖ +
      c * ‖SchwartzMap.toBesselPotentialSpaceCLM (r - -(N : ℝ)) p
        (e.cutoffPushforwardSchwartz he φ (R u))‖ := by
    have hsplit : u = Q (P u) - R u := by simp [hRdef]
    conv_lhs => rw [hsplit, map_sub, map_sub]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hN]
    exact ContinuousLinearMap.le_opNorm _ _
  have hc : 0 ≤ c := norm_nonneg _
  calc _ ≤ A * X + c * (B * Y) :=
        hu.trans (add_le_add (hA (P u)) (mul_le_mul_of_nonneg_left (hB u) hc))
    _ ≤ (|A| + c * |B|) * (X + Y) := by
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self A) hX,
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self B) hY) hc,
          mul_nonneg (abs_nonneg A) hY, mul_nonneg (mul_nonneg hc (abs_nonneg B)) hX]

end TauCeti
