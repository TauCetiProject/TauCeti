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

These examples exercise the iterated submersion fibre product API, its Čech simplicial structure,
and the local-section criterion for submersions on concrete smooth manifolds:

* for the product projection `Prod.fst : ℝ × ℝ → ℝ`, the twofold fibre product
  `IteratedFiberProduct (@Prod.fst ℝ ℝ) 2` has dimension `3`, is closed in `Fin 2 → ℝ × ℝ`, and is
  smoothly diffeomorphic to `ℝ × ℝ × ℝ` via `y ↦ ((y.proj 0).1, (y.proj 0).2, (y.proj 1).2)`, while
  its simplicial face and degeneracy maps are submersions and smooth embeddings respectively;
* for the identity map `@id ℝ`, every `k`-fold fibre product (`k ≥ 1`) is smoothly diffeomorphic to
  `ℝ` via `iteratedFiberProductIdDiffeomorph`;
* for the non-Hausdorff line `D` with a doubled origin (`TauCeti.doubleGlueData ℝ {0}ᶜ`) and its
  two-chart disjoint-union cover `π : ℝ ⊕ ℝ → D`, `π` is a surjective `C^∞` submersion so
  `IteratedFiberProduct π 2` is a smooth `1`-manifold without any `T2Space` assumption on `D`, yet
  its underlying subset of `Fin 2 → ℝ ⊕ ℝ` is not closed;
* for the non-submersion `x ↦ x ^ 2 : ℝ → ℝ`, no open neighbourhood of `0` admits even a
  set-theoretic local section, witnessing the sharpness of the submersion hypothesis in
  `Manifold.IsSubmersionAt.exists_contMDiffOn_section`.
-/

noncomputable section

open Function Set Topology TopologicalSpace TauCeti TopCat.GlueData
open scoped Manifold ContDiff

/-! ### 1. Product projection `Prod.fst : ℝ × ℝ → ℝ` and identity cover `@id ℝ` -/

-- The twofold fibre product of `Prod.fst : ℝ × ℝ → ℝ` has dimension `2 * 2 - 1 * 1 = 3`.
example : iteratedFiberProductDim (ℝ × ℝ) ℝ 2 = 3 := by
  simp [iteratedFiberProductDim]

-- Because the base `ℝ` is Hausdorff, the twofold fibre product is closed in `Fin 2 → ℝ × ℝ`.
example : IsClosed {y : Fin 2 → ℝ × ℝ | ∀ i j, (y i).1 = (y j).1} :=
  IteratedFiberProduct.isClosed_setOf_apply_eq continuous_fst 2

-- Explicit `C^∞` diffeomorphism `(ℝ × ℝ) ×_ℝ (ℝ × ℝ) ≃ₘ^∞ ℝ × ℝ × ℝ` sending
-- `((x, u), (x, v)) ↦ (x, u, v)`.
example :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    letI := iteratedFiberProductChartedSpace 2 hn
      (Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞))
    IteratedFiberProduct (@Prod.fst ℝ ℝ) 2
      ≃ₘ^∞⟮𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 2) → ℝ),
        𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))⟯
      (ℝ × ℝ × ℝ) := by
  let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
  let hπ := Manifold.isSubmersion_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := ℝ) (n := ∞)
  letI := iteratedFiberProductChartedSpace 2 hn hπ
  have hproj (i : Fin 2) :
      ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim (ℝ × ℝ) ℝ 2) → ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (IteratedFiberProduct.proj i : IteratedFiberProduct (@Prod.fst ℝ ℝ) 2 → ℝ × ℝ) :=
    contMDiff_proj_iteratedFiberProduct 2 hn hπ le_rfl i
  refine
    { toFun := fun y ↦
        ((IteratedFiberProduct.proj 0 y).1, (IteratedFiberProduct.proj 0 y).2,
          (IteratedFiberProduct.proj 1 y).2)
      invFun := fun p ↦
        ⟨Fin.cases (p.1, p.2.1) (fun _ ↦ (p.1, p.2.2)), by
          intro i j
          fin_cases i <;> fin_cases j <;> rfl⟩
      left_inv := fun y ↦ IteratedFiberProduct.ext fun i ↦ by
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp
        · rw [Fin.eq_zero j]
          simp only [IteratedFiberProduct.val_apply, Fin.succ_zero_eq_one]
          exact Prod.ext (y.apply_proj_eq 0 1) rfl
      right_inv := fun p ↦ by
        rcases p with ⟨_, _, _⟩
        simp only [IteratedFiberProduct.proj_mk, Fin.cases_zero]
        rw [← Fin.succ_zero_eq_one, Fin.cases_succ]
      contMDiff_toFun :=
        (hproj 0).fst.prodMk ((hproj 0).snd.prodMk (hproj 1).snd)
      contMDiff_invFun := by
        refine (contMDiff_iteratedFiberProduct_iff hn hπ le_rfl).2 fun i ↦ ?_
        refine Fin.cases ?_ (fun _ ↦ ?_) i
        · simp only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk, Fin.cases_zero]
          exact contMDiff_fst.prodMk contMDiff_snd.fst
        · simp only [Equiv.coe_fn_symm_mk, IteratedFiberProduct.proj_mk, Fin.cases_succ]
          exact contMDiff_fst.prodMk contMDiff_snd.snd }

-- On the Čech nerve of `Prod.fst : ℝ × ℝ → ℝ`, every face map is a smooth submersion and every
-- degeneracy map is a smooth embedding.
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

-- Every `k`-fold fibre product of the identity cover `@id ℝ` (`k ≥ 1`) is `C^∞` diffeomorphic to
-- `ℝ`.
example (k : ℕ) [NeZero k] :
    let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
    letI := iteratedFiberProductChartedSpace k hn
      (Manifold.IsSubmersion.id (I := 𝓘(ℝ, ℝ)) (M := ℝ) (n := ∞))
    IteratedFiberProduct (@id ℝ) k ≃ₘ^∞⟮𝓘(ℝ, Fin (iteratedFiberProductDim ℝ ℝ k) → ℝ), 𝓘(ℝ, ℝ)⟯
      ℝ :=
  iteratedFiberProductIdDiffeomorph 𝓘(ℝ, ℝ) ℝ k (by simp)

/-! ### 2. Non-Hausdorff base: the line with a doubled origin -/

-- The line with a doubled origin is not Hausdorff.
example : ¬ T2Space (doubleGlueData ℝ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.glued := by
  simpa [t2Space_doubleGlueData_iff] using fun _ ↦ not_isOpen_singleton (0 : ℝ)

-- Its two-chart disjoint-union cover `ℝ ⊕ ℝ → D` is a surjective `C^∞` submersion, so the twofold
-- fibre product `IteratedFiberProduct π 2` is a smooth `1`-manifold without any `T2Space`
-- assumption on the base, yet is not closed in `Fin 2 → ℝ ⊕ ℝ`.
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
      IsManifold 𝓘(ℝ, Fin (iteratedFiberProductDim ℝ ℝ 2) → ℝ) ∞
        (IteratedFiberProduct π 2) ∧
      iteratedFiberProductDim ℝ ℝ 2 = 1) ∧
    ¬ IsClosed {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)} := by
  let D := doubleGlueData ℝ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let π : ℝ ⊕ ℝ → D.toGlueData.glued :=
    Sum.elim (D.toGlueData.ι ⟨false⟩) (D.toGlueData.ι ⟨true⟩)
  let hn : (1 : ℕ∞ω) ≤ ∞ := by simp
  let := D.chartedSpace ℝ
  have : IsManifold 𝓘(ℝ, ℝ) ∞ D.toGlueData.glued := (isCompatible_doubleGlueData _).isManifold
  refine ⟨?_, ?_, ?_⟩
  · intro z
    obtain ⟨⟨b⟩, x, rfl⟩ := D.ι_jointly_surjective z
    cases b
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr x, rfl⟩
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
  · intro hclosed
    let γ : ℝ → Fin 2 → ℝ ⊕ ℝ := fun t ↦ ![Sum.inl t, Sum.inr t]
    have hγ : Continuous γ := by
      refine continuous_pi fun i ↦ ?_
      fin_cases i
      · exact continuous_inl
      · exact continuous_inr
    have hpre : IsClosed (γ ⁻¹' {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)}) :=
      hclosed.preimage hγ
    have hsub : ({0}ᶜ : Set ℝ) ⊆ γ ⁻¹' {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)} := by
      intro t ht i j
      have h01 : D.toGlueData.ι ⟨false⟩ t = D.toGlueData.ι ⟨true⟩ t :=
        doubleGlueData_ι_eq_iff.2 ⟨rfl, Or.inr ht⟩
      fin_cases i <;> fin_cases j
      · rfl
      · exact h01
      · exact h01.symm
      · rfl
    have h0 : (0 : ℝ) ∈ γ ⁻¹' {y : Fin 2 → ℝ ⊕ ℝ | ∀ i j, π (y i) = π (y j)} := by
      have hcl := closure_mono hsub
      rw [closure_compl_singleton (0 : ℝ), hpre.closure_eq] at hcl
      exact hcl (mem_univ 0)
    have heq : D.toGlueData.ι ⟨false⟩ (0 : ℝ) = D.toGlueData.ι ⟨true⟩ (0 : ℝ) := h0 0 1
    exact doubleGlueData_false_ne_true ((doubleGlueData_ι_eq_iff.1 heq).2.resolve_right (by simp))

/-! ### 3. Sharpness of the submersion hypothesis for local sections: `x ↦ x ^ 2` -/

-- The map `x ↦ x ^ 2 : ℝ → ℝ` admits no local section on any open neighbourhood of `0`, and is
-- therefore not a smooth submersion at `0`.
example :
    (¬ ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∃ s : ℝ → ℝ, ∀ y ∈ U, (s y) ^ 2 = y) ∧
    ¬ Manifold.IsSubmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ ↦ x ^ 2) 0 := by
  have hnosec : ¬ ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∃ s : ℝ → ℝ, ∀ y ∈ U, (s y) ^ 2 = y := by
    rintro ⟨U, hU, h0U, s, hs⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
    have hmem : -(ε / 2) ∈ U := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    linarith [hs (-(ε / 2)) hmem, sq_nonneg (s (-(ε / 2)))]
  refine ⟨hnosec, fun hsub ↦ hnosec ?_⟩
  obtain ⟨U, hU, h0U, s, -, -, hs⟩ := hsub.exists_contMDiffOn_section
  exact ⟨U, hU, by simpa using h0U, s, hs⟩

end
