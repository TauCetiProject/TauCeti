/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Geometry.Manifold.FiberProduct.Simplicial
import TauCeti.Geometry.Manifold.Gluing.Double
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
public import TauCeti.Topology.Connected.Basic

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

namespace TauCeti

/-- Auxiliary dimension-`1` step for `not_homeomorph_of_punctured_nhds_splits`: removing the centre
splits an open interval in `Fin 1 → ℝ` into two connected pieces, which cannot meet `m ≥ 3`
pairwise disjoint open sets covering the punctured neighbourhood. -/
private theorem not_homeomorph_finOne_of_punctured_nhds_splits
    {X : Type*} [TopologicalSpace X] {x₀ : X} {m : ℕ} (hm : 2 < m) {Q : Fin m → Set X}
    (hQ_disj : Pairwise (Disjoint on Q))
    {U : Set X} {V : Set (Fin 1 → ℝ)} (hx₀ : x₀ ∈ U) (hV : IsOpen V) (e : U ≃ₜ V)
    {r : ℝ} (hr : 0 < r) (hballV : Metric.ball (e ⟨x₀, hx₀⟩).val r ⊆ V)
    {S₀ : Set X}
    (hS₀_eq : S₀ = Subtype.val ''
      (e.symm '' (Subtype.val ⁻¹' (Metric.ball (e ⟨x₀, hx₀⟩).val r \ {(e ⟨x₀, hx₀⟩).val}) :
        Set V)))
    (hpre_sub : ∀ {C : Set X}, IsPreconnected C → C ⊆ S₀ → ∃ k : Fin m, C ⊆ Q k)
    (hS₀_Q : ∀ k : Fin m, (S₀ ∩ Q k).Nonempty) : False := by
  let y₀ : Fin 1 → ℝ := (e ⟨x₀, hx₀⟩).val
  let φ := IsometryEquiv.funUnique (Fin 1) ℝ
  let z₀ : ℝ := φ y₀
  have hball : φ.symm '' Metric.ball z₀ r = Metric.ball y₀ r := by simp [z₀]
  let C : Set ℝ → Set X := fun I ↦ Subtype.val '' (e.symm '' (Subtype.val ⁻¹' (φ.symm '' I)))
  have hpiece : ∀ I : Set ℝ, I ⊆ Metric.ball z₀ r → z₀ ∉ I → IsPreconnected I →
      ∃ i : Fin m, C I ⊆ Q i := by
    intro I hI hz₀ hIconn
    have hIV : φ.symm '' I ⊆ V := (image_mono hI).trans (hball.symm ▸ hballV)
    have hA : IsPreconnected (Subtype.val ⁻¹' (φ.symm '' I) : Set V) :=
      (hIconn.image _ φ.symm.continuous.continuousOn).preimage_of_isOpenMap
        Subtype.val_injective hV.isOpenMap_subtypeVal (Subtype.range_coe_subtype ▸ hIV)
    have hC_pre : IsPreconnected (C I) :=
      (hA.image _ e.symm.continuous.continuousOn).image _ continuous_subtypeVal.continuousOn
    have hy₀ : φ.symm z₀ = (e ⟨x₀, hx₀⟩).val := φ.symm_apply_apply y₀
    have hC_sub : C I ⊆ S₀ := by
      rw [hS₀_eq]
      refine image_mono (image_mono (preimage_mono ?_))
      rw [← hball, ← hy₀]
      exact Set.subset_sdiff_singleton (image_mono hI) fun ⟨t, ht, htv⟩ ↦
        hz₀ (φ.symm.injective htv ▸ ht)
    exact hpre_sub hC_pre hC_sub
  let J₁ : Set ℝ := Ioo (z₀ - r) z₀
  let J₂ : Set ℝ := Ioo z₀ (z₀ + r)
  obtain ⟨i₁, hi₁⟩ := hpiece J₁
    (Real.ball_eq_Ioo z₀ r ▸ Ioo_subset_Ioo_right (by linarith)) (fun h ↦ lt_irrefl _ h.2)
    isPreconnected_Ioo
  obtain ⟨i₂, hi₂⟩ := hpiece J₂
    (Real.ball_eq_Ioo z₀ r ▸ Ioo_subset_Ioo_left (by linarith)) (fun h ↦ lt_irrefl _ h.1)
    isPreconnected_Ioo
  have hJ : J₁ ∪ J₂ = Metric.ball z₀ r \ {z₀} := by
    rw [Real.ball_eq_Ioo]
    exact Set.Ioo_union_Ioo_eq_Ioo_sdiff_singleton (by linarith) (by linarith)
  have hS₀_cover : S₀ ⊆ C J₁ ∪ C J₂ := by
    rw [hS₀_eq, ← hball]
    have hdiff : φ.symm '' Metric.ball z₀ r \ {y₀} = φ.symm '' (J₁ ∪ J₂) := by
      rw [hJ, Set.image_sdiff φ.symm.injective, image_singleton, φ.symm_apply_apply]
    change Subtype.val '' (e.symm '' (Subtype.val ⁻¹' (φ.symm '' Metric.ball z₀ r \ {y₀}))) ⊆ _
    rw [hdiff]
    simp only [C, image_union, preimage_union, subset_rfl]
  obtain ⟨k, hk₁, hk₂⟩ := Fin.exists_ne_and_ne_of_two_lt i₁ i₂ hm
  obtain ⟨x, hxS, hxQ⟩ := hS₀_Q k
  rcases hS₀_cover hxS with hxC | hxC
  · exact Set.disjoint_left.mp (hQ_disj hk₁) hxQ (hi₁ hxC)
  · exact Set.disjoint_left.mp (hQ_disj hk₂) hxQ (hi₂ hxC)

/-- Punctured-neighbourhood obstruction to being locally Euclidean: if `x₀` has a family of
`m > 2` pairwise disjoint open sets `Q k` covering `{x₀}ᶜ` such that every open neighbourhood of
`x₀` meets every `Q k` away from `x₀`, then no open neighbourhood of `x₀` is homeomorphic to an
open subset of `Fin n → ℝ`. -/
public theorem not_homeomorph_of_punctured_nhds_splits
    {X : Type*} [TopologicalSpace X] {x₀ : X} {m : ℕ} (hm : 2 < m)
    (Q : Fin m → Set X) (hQ_open : ∀ k, IsOpen (Q k)) (hQ_disj : Pairwise (Disjoint on Q))
    (hQ_cover : ∀ {x}, x ≠ x₀ → x ∈ ⋃ k, Q k)
    (hQ_mem : ∀ W : Set X, IsOpen W → x₀ ∈ W → ∀ k, ((W \ {x₀}) ∩ Q k).Nonempty)
    {n : ℕ} {U : Set X} {V : Set (Fin n → ℝ)} (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hV : IsOpen V) :
    IsEmpty (U ≃ₜ V) := by
  refine ⟨fun e ↦ ?_⟩
  let y₀ : Fin n → ℝ := (e ⟨x₀, hx₀⟩).val
  obtain ⟨r, hr, hballV⟩ := Metric.isOpen_iff.mp hV y₀ (e ⟨x₀, hx₀⟩).property
  let B : Set U := (fun u ↦ (e u).val) ⁻¹' Metric.ball y₀ r
  have hB_open : IsOpen B :=
    Metric.isOpen_ball.preimage (continuous_subtypeVal.comp e.continuous)
  have hu₀ : ⟨x₀, hx₀⟩ ∈ B := Metric.mem_ball_self hr
  let W : Set X := Subtype.val '' B
  have hW_open : IsOpen W := hU.isOpenMap_subtypeVal B hB_open
  have hxW : x₀ ∈ W := ⟨⟨x₀, hx₀⟩, hu₀, rfl⟩
  let S₀ : Set X := Subtype.val '' (B \ {⟨x₀, hx₀⟩})
  have hS₀_eq_sdiff : S₀ = W \ {x₀} := by
    simp only [S₀, W, Set.image_sdiff Subtype.val_injective, image_singleton]
  have hS₀_Q : ∀ k : Fin m, (S₀ ∩ Q k).Nonempty := fun k ↦
    hS₀_eq_sdiff ▸ hQ_mem W hW_open hxW k
  have hS₀_sub : S₀ ⊆ ⋃ k, Q k := fun _ hx ↦ hQ_cover (hS₀_eq_sdiff ▸ hx).2
  have hpre_sub : ∀ {C : Set X}, IsPreconnected C → C ⊆ S₀ → ∃ k, C ⊆ Q k := by
    intro C hC hCS
    by_cases hne : C.Nonempty
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hS₀_sub (hCS hx))
      exact ⟨k, hC.subset_of_subset_iUnion hQ_open hQ_disj (hCS.trans hS₀_sub) ⟨x, hx, hk⟩⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact ⟨⟨0, by omega⟩, empty_subset _⟩
  have hS₀_eq :
      S₀ = Subtype.val '' (e.symm '' (Subtype.val ⁻¹' (Metric.ball y₀ r \ {y₀}) : Set V)) := by
    have hpre : (e.symm.symm ⁻¹' (Subtype.val ⁻¹' {y₀} : Set V)) = {⟨x₀, hx₀⟩} := by
      ext u; simp [y₀, Subtype.val_inj, e.injective.eq_iff]
    rw [e.symm.image_eq_preimage_symm, Set.preimage_sdiff, Set.preimage_sdiff, hpre]
    rfl
  rcases lt_trichotomy n 1 with hn0 | rfl | hn2
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn0
    have hsub0 : Subsingleton (Fin 0 → ℝ) := inferInstance
    have hsubV : Subsingleton V := ⟨fun a b ↦ Subtype.ext (hsub0.elim a.val b.val)⟩
    obtain ⟨_, ⟨u, ⟨-, hune⟩, rfl⟩, -⟩ := hS₀_Q ⟨0, by omega⟩
    exact hune (e.injective (hsubV.elim (e u) (e ⟨x₀, hx₀⟩)))
  · exact not_homeomorph_finOne_of_punctured_nhds_splits hm hQ_disj hx₀ hV e hr hballV hS₀_eq
      hpre_sub hS₀_Q
  · have hrank : 1 < Module.rank ℝ (Fin n → ℝ) := by
      rw [← finrank_eq_rank, finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact_mod_cast hn2
    have hA : IsPreconnected (Subtype.val ⁻¹' (Metric.ball y₀ r \ {y₀}) : Set V) :=
      (TauCeti.isConnected_ball_sdiff_singleton hrank y₀ hr).isPreconnected.preimage_of_isOpenMap
        Subtype.val_injective hV.isOpenMap_subtypeVal
        (Subtype.range_coe_subtype ▸ sdiff_subset.trans hballV)
    have hS₀_pre : IsPreconnected S₀ := by
      rw [hS₀_eq]
      exact (hA.image _ e.symm.continuous.continuousOn).image _ continuous_subtypeVal.continuousOn
    obtain ⟨i, hi⟩ := hpre_sub hS₀_pre Subset.rfl
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨k, hki⟩ := exists_ne i
    obtain ⟨_, hxS, hxQ⟩ := hS₀_Q k
    exact Set.disjoint_left.mp (hQ_disj hki) hxQ (hi hxS)

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

end TauCeti

end
