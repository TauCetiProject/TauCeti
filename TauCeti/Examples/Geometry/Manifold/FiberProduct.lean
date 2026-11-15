/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Field.Basic
import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Simplicial
import TauCeti.Geometry.Manifold.Gluing.Double
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum

/-!
# Examples: iterated submersion fibre products and local sections

Concrete examples exercising iterated submersion fibre products, their Čech nerve, and local
sections: `Prod.fst : ℝ × ℝ → ℝ` (dimension `3`, diffeomorphic to `ℝ × ℝ × ℝ`), `@id ℝ`,
the non-Hausdorff doubled-origin line `D` (smooth `1`-manifold twofold fibre product without
`T2Space`), and `x ↦ x ^ 2 : ℝ → ℝ` (no local section around `0`).
-/

noncomputable section

open Function Set Topology TopologicalSpace TauCeti TopCat.GlueData
open scoped Manifold ContDiff

example : iteratedFiberProductDim (ℝ × ℝ) ℝ 2 = 3 := by simp [iteratedFiberProductDim]

example : IsClosed {y : Fin 2 → ℝ × ℝ | ∀ i j, (y i).1 = (y j).1} :=
  IteratedFiberProduct.isClosed_setOf_apply_eq continuous_fst 2

example :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    letI := iteratedFiberProductChartedSpace 2 hn
      (Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞))
    IteratedFiberProduct (@Prod.fst ℝ ℝ) 2
      ≃ₘ^∞⟮𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 2) → ℝ),
        𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))⟯ (ℝ × ℝ × ℝ) := by
  let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
  let hπ := Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞)
  letI := iteratedFiberProductChartedSpace 2 hn hπ
  have hproj (i : Fin 2) :
      ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 2) → ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (IteratedFiberProduct.proj i : IteratedFiberProduct (@Prod.fst ℝ ℝ) 2 → ℝ × ℝ) :=
    contMDiff_proj_iteratedFiberProduct 2 hn hπ le_rfl i
  refine
    { toFun := fun y ↦ ((IteratedFiberProduct.proj 0 y).1, (IteratedFiberProduct.proj 0 y).2,
        (IteratedFiberProduct.proj 1 y).2)
      invFun := fun p ↦ ⟨Fin.cases (motive := fun _ ↦ ℝ × ℝ) (p.1, p.2.1) (fun _ ↦ (p.1, p.2.2)),
        by intro i j; fin_cases i <;> fin_cases j <;> rfl⟩
      left_inv := fun y ↦ IteratedFiberProduct.ext fun i ↦ by
        refine Fin.cases (by simp) (fun j ↦ ?_) i
        rw [Fin.eq_zero j]; simp only [IteratedFiberProduct.val_apply, Fin.succ_zero_eq_one]
        exact Prod.ext (y.apply_proj_eq 0 1) rfl
      right_inv := fun ⟨_, _, _⟩ ↦ by
        simp only [IteratedFiberProduct.proj_mk, Fin.cases_zero]
        rw [← Fin.succ_zero_eq_one, Fin.cases_succ]
      contMDiff_toFun := (hproj 0).fst.prodMk ((hproj 0).snd.prodMk (hproj 1).snd)
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦ by
        refine Fin.cases ?_ (fun _ ↦ ?_) i
        · simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk, Fin.cases_zero] using
            contMDiff_fst.prodMk contMDiff_snd.fst
        · simpa only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk, Fin.cases_succ] using
            contMDiff_fst.prodMk contMDiff_snd.snd }

example (i : Fin 3) (j : Fin 2) :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    let hπ := Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞)
    letI := iteratedFiberProductChartedSpace 2 hn hπ
    letI := iteratedFiberProductChartedSpace 3 hn hπ
    Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 3) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 2) → ℝ) ∞
      (IteratedFiberProduct.face (π := @Prod.fst ℝ ℝ) i) ∧
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 2) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 3) → ℝ) ∞
      (IteratedFiberProduct.degen (π := @Prod.fst ℝ ℝ) j) :=
  let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
  let hπ := Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞)
  ⟨IteratedFiberProduct.isSubmersion_face (k := 2) hn hπ i,
    IteratedFiberProduct.isSmoothEmbedding_degen (k := 2) hn hπ j⟩

example (k : ℕ) [NeZero k] :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    letI := iteratedFiberProductChartedSpace k hn
      (Manifold.IsSubmersion.id (I := 𝓘(ℝ, ℝ)) (M := ℝ) (n := ∞))
    IteratedFiberProduct (@id ℝ) k ≃ₘ^∞⟮𝓘(ℝ, Fin (iteratedFiberProductDim ℝ ℝ k) → ℝ), 𝓘(ℝ, ℝ)⟯
      ℝ :=
  iteratedFiberProductIdDiffeomorph 𝓘(ℝ, ℝ) ℝ k (by simp)

example : ¬ T2Space (doubleGlueData ℝ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.glued := by
  simpa [t2Space_doubleGlueData_iff] using fun _ ↦ not_isOpen_singleton (0 : ℝ)

example :
    let D := doubleGlueData ℝ ⟨{0}ᶜ, isOpen_compl_singleton⟩
    let π : ℝ ⊕ ℝ → D.toGlueData.glued :=
      Sum.elim (D.toGlueData.ι ⟨false⟩) (D.toGlueData.ι ⟨true⟩)
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    letI := D.chartedSpace ℝ
    haveI : IsManifold 𝓘(ℝ, ℝ) ∞ D.toGlueData.glued := (isCompatible_doubleGlueData _).isManifold
    Surjective π ∧
    (∃ hπ : Manifold.IsSubmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ π,
      letI := iteratedFiberProductChartedSpace 2 hn hπ
      IsManifold 𝓘(ℝ, Fin (iteratedFiberProductDim ℝ ℝ 2) → ℝ) ∞ (IteratedFiberProduct π 2) ∧
      iteratedFiberProductDim ℝ ℝ 2 = 1) ∧
    ¬ IsClosed {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)} := by
  let D := doubleGlueData ℝ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let π : ℝ ⊕ ℝ → D.toGlueData.glued := Sum.elim (D.toGlueData.ι ⟨false⟩) (D.toGlueData.ι ⟨true⟩)
  let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
  let := D.chartedSpace ℝ
  have : IsManifold 𝓘(ℝ, ℝ) ∞ D.toGlueData.glued := (isCompatible_doubleGlueData _).isManifold
  refine ⟨fun z ↦ ?_, ?_, fun hclosed ↦ ?_⟩
  · obtain ⟨⟨b⟩, x, rfl⟩ := D.ι_jointly_surjective z
    cases b <;> [exact ⟨Sum.inl x, rfl⟩; exact ⟨Sum.inr x, rfl⟩]
  · have hloc : IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ π := by
      rintro (x | x)
      · exact IsLocalDiffeomorphAt.of_comp_right (f := π) (e := (Sum.inl : ℝ → ℝ ⊕ ℝ))
          ((isCompatible_doubleGlueData _).isLocalDiffeomorph_ι ⟨false⟩ x)
          (isLocalDiffeomorph_sumInl x)
      · exact IsLocalDiffeomorphAt.of_comp_right (f := π) (e := (Sum.inr : ℝ → ℝ ⊕ ℝ))
          ((isCompatible_doubleGlueData _).isLocalDiffeomorph_ι ⟨true⟩ x)
          (isLocalDiffeomorph_sumInr x)
    have hπ : Manifold.IsSubmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ π := hloc.isSubmersion (by simp)
    exact ⟨hπ, isManifold_iteratedFiberProduct 2 hn hπ, by simp [iteratedFiberProductDim]⟩
  · let γ : ℝ → Fin 2 → ℝ ⊕ ℝ := fun t ↦ ![Sum.inl t, Sum.inr t]
    have hγ : Continuous γ := continuous_pi fun i ↦ by
      fin_cases i <;> [exact continuous_inl; exact continuous_inr]
    have hpre := hclosed.preimage hγ
    have hsub : ({0}ᶜ : Set ℝ) ⊆ γ ⁻¹' {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)} := by
      intro t ht i j
      have h01 : D.toGlueData.ι ⟨false⟩ t = D.toGlueData.ι ⟨true⟩ t :=
        doubleGlueData_ι_eq_iff.2 ⟨rfl, Or.inr ht⟩
      fin_cases i <;> fin_cases j <;> [rfl; exact h01; exact h01.symm; rfl]
    have hcl := closure_mono hsub; rw [closure_compl_singleton (0 : ℝ), hpre.closure_eq] at hcl
    have heq : D.toGlueData.ι ⟨false⟩ (0 : ℝ) = D.toGlueData.ι ⟨true⟩ (0 : ℝ) :=
      hcl (mem_univ 0) 0 1
    exact doubleGlueData_false_ne_true ((doubleGlueData_ι_eq_iff.1 heq).2.resolve_right (by simp))

example :
    (¬ ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∃ s : ℝ → ℝ, ∀ y ∈ U, (s y) ^ 2 = y) ∧
    ¬ Manifold.IsSubmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ ↦ x ^ 2) 0 := by
  have hnosec : ¬ ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∃ s : ℝ → ℝ, ∀ y ∈ U, (s y) ^ 2 = y := by
    rintro ⟨U, hU, h0U, s, hs⟩; obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
    have hmem : -(ε / 2) ∈ U := hball <| by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    linarith [hs (-(ε / 2)) hmem, sq_nonneg (s (-(ε / 2)))]
  refine ⟨hnosec, fun hsub ↦ hnosec ?_⟩
  obtain ⟨U, hU, h0U, s, -, -, hs⟩ := hsub.exists_contMDiffOn_section
  exact ⟨U, hU, by simpa using h0U, s, hs⟩

end
