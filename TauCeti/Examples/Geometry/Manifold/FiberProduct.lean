/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Field.Basic
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Geometry.Manifold.FiberProduct.Simplicial
import TauCeti.Geometry.Manifold.Gluing.Double
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Examples: iterated submersion fibre products and local sections

Concrete examples exercising iterated submersion fibre products, their Čech nerve, and local
sections: `Prod.fst : ℝ × ℝ → ℝ` (dimension `3`, diffeomorphic to `ℝ × ℝ × ℝ`), `@id ℝ`,
the non-Hausdorff doubled-origin line `D` (smooth `1`-manifold twofold fibre product without
`T2Space`), and `x ↦ x ^ 2 : ℝ → ℝ` (no right-differentiable local section on `[0, ∞)` at `0`,
and a self fibre product that is not locally Euclidean at `(0, 0)`).
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
    (¬ ∃ U ∈ 𝓝[Ici (0 : ℝ)] 0, ∃ s : ℝ → ℝ,
      (∀ y ∈ U ∩ Ici 0, (s y) ^ 2 = y) ∧ DifferentiableWithinAt ℝ s (Ici 0) 0) ∧
    ¬ Manifold.IsSubmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ ↦ x ^ 2) 0 := by
  have hnosec : ¬ ∃ U ∈ 𝓝[Ici (0 : ℝ)] 0, ∃ s : ℝ → ℝ,
      (∀ y ∈ U ∩ Ici 0, (s y) ^ 2 = y) ∧ DifferentiableWithinAt ℝ s (Ici 0) 0 := by
    rintro ⟨U, hU, s, hs, hd⟩
    have hUIci : U ∩ Ici (0 : ℝ) ∈ 𝓝[Ici (0 : ℝ)] 0 := Filter.inter_mem hU self_mem_nhdsWithin
    have h0 : (0 : ℝ) ∈ U ∩ Ici 0 := mem_of_mem_nhdsWithin (mem_Ici.mpr le_rfl) hUIci
    have hs0 : s 0 = 0 := sq_eq_zero_iff.mp (by simpa using hs 0 h0)
    have hpow : HasDerivWithinAt (fun y : ℝ ↦ (s y) ^ 2) 0 (Ici 0) 0 := by
      simpa only [hs0, zero_mul, add_zero, mul_zero] using
        (hd.hasDerivWithinAt.mul hd.hasDerivWithinAt).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y ↦ sq (s y)) (sq (s 0))
    have hid : HasDerivWithinAt (fun y : ℝ ↦ (s y) ^ 2) 1 (Ici 0) 0 :=
      (hasDerivWithinAt_id 0 (Ici 0)).congr_of_eventuallyEq
        (Filter.Eventually.mono hUIci fun y hy ↦ hs y hy) (hs 0 h0)
    have heq := ContinuousLinearMap.toSpanSingleton_inj.mp ((uniqueDiffWithinAt_Ici 0).eq hpow hid)
    exact zero_ne_one heq
  refine ⟨hnosec, fun hsub ↦ ?_⟩
  obtain ⟨U, hU, h0U, s, -, hs_diff, hs⟩ := hsub.exists_contMDiffOn_section
  have h0U' : (0 : ℝ) ∈ U := by simpa using h0U
  refine hnosec ⟨U, nhdsWithin_le_nhds (hU.mem_nhds h0U'), s, fun y hy ↦ hs y hy.1, ?_⟩
  have hd : DifferentiableAt ℝ s 0 :=
    ((hs_diff.contMDiffAt (hU.mem_nhds h0U')).mdifferentiableAt (by simp)).differentiableAt
  exact hd.differentiableWithinAt

example :
    let X := IteratedFiberProduct (fun x : ℝ ↦ x ^ 2) 2
    let x₀ : X := ⟨0, fun _ _ ↦ rfl⟩
    ∀ (n : ℕ) (U : Set X) (V : Set (Fin n → ℝ)),
      IsOpen U → x₀ ∈ U → IsOpen V → IsEmpty (U ≃ₜ V) := by
  intro X x₀ n U V hU hx₀ hV
  let Q : Fin 4 → Set X := fun k ↦
    {x | (if k.val = 0 ∨ k.val = 3 then 0 < x.val 0 else x.val 0 < 0) ∧
         (if k.val = 0 ∨ k.val = 1 then 0 < x.val 1 else x.val 1 < 0)}
  have hQ_open : ∀ k, IsOpen (Q k) := fun k ↦ by
    have hc0 : Continuous (fun x : X ↦ x.val 0) := (continuous_apply 0).comp continuous_subtypeVal
    have hc1 : Continuous (fun x : X ↦ x.val 1) := (continuous_apply 1).comp continuous_subtypeVal
    dsimp [Q]
    split_ifs <;> [exact (isOpen_lt continuous_const hc0).inter (isOpen_lt continuous_const hc1);
      exact (isOpen_lt continuous_const hc0).inter (isOpen_lt hc1 continuous_const);
      exact (isOpen_lt hc0 continuous_const).inter (isOpen_lt continuous_const hc1);
      exact (isOpen_lt hc0 continuous_const).inter (isOpen_lt hc1 continuous_const)]
  have hQ_disj : Pairwise (Disjoint on Q) := fun a b hab ↦ Set.disjoint_left.mpr fun _ hxa hxb ↦ by
    fin_cases a <;> fin_cases b <;> simp_all [Q] <;> linarith
  have hQ_cover : ∀ {x : X}, x ≠ x₀ → x ∈ ⋃ k, Q k := fun {x} hxne ↦ by
    have hx0 : x.val 0 ≠ 0 := fun h0 ↦ hxne <| Subtype.ext <| funext fun i ↦ by
      fin_cases i
      · exact h0
      · exact sq_eq_zero_iff.mp (by simpa [h0] using (x.property 0 1).symm)
    have hx1 : x.val 1 ≠ 0 := fun h1 ↦
      hx0 (sq_eq_zero_iff.mp (by simpa [h1] using x.property 0 1))
    rcases lt_or_gt_of_ne hx0 with h0 | h0 <;> rcases lt_or_gt_of_ne hx1 with h1 | h1
    · exact mem_iUnion.mpr ⟨2, by simp [Q, h0, h1]⟩
    · exact mem_iUnion.mpr ⟨1, by simp [Q, h0, h1]⟩
    · exact mem_iUnion.mpr ⟨3, by simp [Q, h0, h1]⟩
    · exact mem_iUnion.mpr ⟨0, by simp [Q, h0, h1]⟩
  have hQ_mem : ∀ W : Set X, IsOpen W → x₀ ∈ W → ∀ k, ((W \ {x₀}) ∩ Q k).Nonempty := by
    intro W hW hxW k
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x₀ hxW
    let xpt : X :=
      ⟨![if k.val = 0 ∨ k.val = 3 then ε / 2 else -(ε / 2),
         if k.val = 0 ∨ k.val = 1 then ε / 2 else -(ε / 2)], by
        intro i j; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp⟩
    refine ⟨xpt, ⟨hεW ?_, fun hk ↦ ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, dist_pi_lt_iff hε]
      intro i; fin_cases i <;> fin_cases k <;> simp [xpt, x₀, abs_of_pos hε, half_lt_self hε]
    · have h0 := congrArg (fun x : X ↦ x.val 0) hk
      fin_cases k <;> simp [xpt, x₀] at h0 <;> linarith
    · fin_cases k <;> exact ⟨by simp [xpt]; linarith, by simp [xpt]; linarith⟩
  exact not_homeomorph_of_punctured_nhds_splits (by decide) Q hQ_open hQ_disj hQ_cover hQ_mem
    hU hx₀ hV

end
