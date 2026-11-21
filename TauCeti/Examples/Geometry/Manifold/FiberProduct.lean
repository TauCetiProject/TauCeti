/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Field.Basic
import TauCeti.Geometry.Manifold.FiberProduct.Simplicial
import TauCeti.Geometry.Manifold.Gluing.Double
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Examples: iterated submersion fibre products and local sections

Concrete examples exercising iterated submersion fibre products, their Čech nerve, and local
sections: `Prod.fst : ℝ × ℝ → ℝ` (dimension `3`, diffeomorphic to `ℝ × ℝ × ℝ`), `@id ℝ`,
the non-Hausdorff doubled-origin line `D` (smooth `1`-manifold twofold fibre product without
`T2Space`), and `x ↦ x ^ 2 : ℝ → ℝ` (no local section around `0`).
-/

noncomputable section

open Function Set Topology TopologicalSpace TauCeti TopCat.GlueData Module
open scoped Manifold ContDiff

example : IsClosed {y : Fin 2 → ℝ × ℝ | ∀ i j, (y i).fst = (y j).fst} :=
  isClosed_setOf_map_eq continuous_fst 2

example :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    let hπ := Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞)
    letI := iteratedFiberProductChartedSpace hn hπ 1
    IteratedFiberProduct (@Prod.fst ℝ ℝ) 2
      ≃ₘ^∞⟮𝓘(ℝ, Fin ((1 + 1) * finrank ℝ (ℝ × ℝ) - 1 * finrank ℝ ℝ) → ℝ),
        𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))⟯ (ℝ × ℝ × ℝ) := by
  let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
  let hπ := Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞)
  letI := iteratedFiberProductChartedSpace hn hπ 1
  have hproj (i : Fin 2) := contMDiff_eval hn hπ (m := 1) le_rfl i
  refine
    { toFun := fun y ↦ ((IteratedFiberProduct.eval 0 y).fst,
        (IteratedFiberProduct.eval 0 y).snd, (IteratedFiberProduct.eval 1 y).snd)
      invFun := fun p ↦ ⟨![(p.fst, p.snd.fst), (p.fst, p.snd.snd)],
        by intro i j; fin_cases i <;> fin_cases j <;> rfl⟩
      left_inv := fun y ↦ IteratedFiberProduct.ext fun i ↦ by
        fin_cases i
        · simp
        · simpa [Prod.ext_iff] using y.property 0 1
      right_inv := fun ⟨_, _, _⟩ ↦ by simp
      contMDiff_toFun := (hproj 0).fst.prodMk ((hproj 0).snd.prodMk (hproj 1).snd)
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).mpr fun i ↦ by
        fin_cases i
        · simpa using contMDiff_fst.prodMk contMDiff_snd.fst
        · simpa using contMDiff_fst.prodMk contMDiff_snd.snd }

example (i : Fin 3) (j : Fin 2) :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    let hπ := Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞)
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := iteratedFiberProductChartedSpace hn hπ 2
    Manifold.IsSubmersion 𝓘(ℝ, Fin ((2 + 1) * finrank ℝ (ℝ × ℝ) - 2 * finrank ℝ ℝ) → ℝ)
      𝓘(ℝ, Fin ((1 + 1) * finrank ℝ (ℝ × ℝ) - 1 * finrank ℝ ℝ) → ℝ) ∞
      (IteratedFiberProduct.face (π := @Prod.fst ℝ ℝ) i) ∧
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin ((1 + 1) * finrank ℝ (ℝ × ℝ) - 1 * finrank ℝ ℝ) → ℝ)
      𝓘(ℝ, Fin ((2 + 1) * finrank ℝ (ℝ × ℝ) - 2 * finrank ℝ ℝ) → ℝ) ∞
      (IteratedFiberProduct.degeneracy (π := @Prod.fst ℝ ℝ) j) :=
  ⟨isSubmersion_face (by simp) Manifold.isSubmersion_fst i,
    isSmoothEmbedding_degeneracy (by simp) Manifold.isSubmersion_fst j⟩

example (m : ℕ) :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    letI := iteratedFiberProductChartedSpace hn
      (Manifold.IsSubmersion.id (I := 𝓘(ℝ, ℝ)) (M := ℝ) (n := ∞)) m
    IteratedFiberProduct (@id ℝ) (m + 1)
      ≃ₘ^∞⟮𝓘(ℝ, Fin ((m + 1) * finrank ℝ ℝ - m * finrank ℝ ℝ) → ℝ), 𝓘(ℝ, ℝ)⟯ ℝ :=
  iteratedFiberProductIdDiffeomorph (IM := 𝓘(ℝ, ℝ)) (by simp) m

example :
    let D := doubleGlueData ℝ ⟨{0}ᶜ, isOpen_compl_singleton⟩
    let π : ℝ ⊕ ℝ → D.toGlueData.glued := Sum.elim (D.toGlueData.ι ⟨false⟩) (D.toGlueData.ι ⟨true⟩)
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    letI := D.chartedSpace ℝ
    haveI : IsManifold 𝓘(ℝ, ℝ) ∞ D.toGlueData.glued := (isCompatible_doubleGlueData _).isManifold
    ¬ T2Space D.toGlueData.glued ∧ Surjective π ∧
    (∃ hπ : Manifold.IsSubmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ π,
      letI := iteratedFiberProductChartedSpace hn hπ 1
      IsManifold 𝓘(ℝ, Fin ((1 + 1) * finrank ℝ ℝ - 1 * finrank ℝ ℝ) → ℝ) ∞
        (IteratedFiberProduct π 2) ∧
      (1 + 1) * finrank ℝ ℝ - 1 * finrank ℝ ℝ = 1) ∧
    ¬ IsClosed {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)} := by
  let D := doubleGlueData ℝ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let π : ℝ ⊕ ℝ → D.toGlueData.glued := Sum.elim (D.toGlueData.ι ⟨false⟩) (D.toGlueData.ι ⟨true⟩)
  let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
  let := D.chartedSpace ℝ
  have : IsManifold 𝓘(ℝ, ℝ) ∞ D.toGlueData.glued := (isCompatible_doubleGlueData _).isManifold
  refine ⟨by simpa [D, t2Space_doubleGlueData_iff] using fun _ ↦ not_isOpen_singleton (0 : ℝ),
    fun z ↦ ?_, ?_, fun hclosed ↦ ?_⟩
  · obtain ⟨⟨b⟩, x, rfl⟩ := D.ι_jointly_surjective z
    cases b <;> [exact ⟨Sum.inl x, rfl⟩; exact ⟨Sum.inr x, rfl⟩]
  · have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ π := fun
      | Sum.inl x => .of_comp_right (f := π) (e := Sum.inl)
          ((isCompatible_doubleGlueData _).isLocalDiffeomorph_ι ⟨false⟩ x)
          (isLocalDiffeomorph_sumInl x)
      | Sum.inr x => .of_comp_right (f := π) (e := Sum.inr)
          ((isCompatible_doubleGlueData _).isLocalDiffeomorph_ι ⟨true⟩ x)
          (isLocalDiffeomorph_sumInr x)
    have hπ := hloc.isSubmersion (by simp)
    exact ⟨hπ, isManifold_iteratedFiberProduct hn hπ 1, by simp⟩
  · let γ : ℝ → Fin 2 → ℝ ⊕ ℝ := fun t ↦ ![Sum.inl t, Sum.inr t]
    have hpre := hclosed.preimage (f := γ) <| continuous_pi fun i ↦ by
      fin_cases i <;> [exact continuous_inl; exact continuous_inr]
    have hsub : ({0}ᶜ : Set ℝ) ⊆ γ ⁻¹' {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)} := by
      intro t ht i j
      have h01 : D.toGlueData.ι ⟨false⟩ t = D.toGlueData.ι ⟨true⟩ t :=
        doubleGlueData_ι_eq_iff.mpr ⟨rfl, Or.inr ht⟩
      fin_cases i <;> fin_cases j <;> [rfl; exact h01; exact h01.symm; rfl]
    have hcl := closure_mono hsub
    rw [closure_compl_singleton (0 : ℝ), hpre.closure_eq] at hcl
    exact doubleGlueData_false_ne_true
      ((doubleGlueData_ι_eq_iff.mp (hcl (mem_univ 0) 0 1)).right.resolve_right (by simp))

example :
    (¬ ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∃ s : ℝ → ℝ, ∀ y ∈ U, (s y) ^ 2 = y) ∧
    ¬ Manifold.IsSubmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ ↦ x ^ 2) 0 := by
  have hnosec : ¬ ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∃ s : ℝ → ℝ, ∀ y ∈ U, (s y) ^ 2 = y := by
    rintro ⟨U, hU, h0U, s, hs⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
    have hmem : -(ε / 2) ∈ U := hball <| by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    linarith [hs (-(ε / 2)) hmem, sq_nonneg (s (-(ε / 2)))]
  refine ⟨hnosec, fun hsub ↦ hnosec ?_⟩
  obtain ⟨U, hU, h0U, s, -, -, hs⟩ := hsub.exists_contMDiffOn_section
  exact ⟨U, hU, by simpa using h0U, s, hs⟩

end
