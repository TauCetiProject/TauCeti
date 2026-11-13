/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Runge.Hull
public import TauCeti.Analysis.Complex.Runge.Operator
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.FilledHull

/-!
# Runge's approximation theorem and holomorphic hulls

This file completes Layer 2 of the global holomorphic functions roadmap by proving Runge's
theorem in its full domain-relative form, identifying the holomorphic hull with the domain-relative
fill, and specializing to polynomial approximation on compact sets with connected complement.

## Main results

* `TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt`: uniform approximation on a
  Runge compact pair by functions holomorphic on `Ω`.
* `TauCeti.isRungeCompactPair_iff_approximation`: equivalence between `IsRungeCompactPair Ω K`
  and uniform approximation on `K` of every function holomorphic on a neighbourhood `U ⊇ K` by
  functions holomorphic on `Ω`.
* `TauCeti.holomorphicHull_eq_fill`: `holomorphicHull Ω K` is compact and equals the union of `K`
  with all relatively compact holes of `K` inside `Ω`.
* `TauCeti.holomorphicHull_eq_self_iff_isFilledIn`: `holomorphicHull Ω K = K ↔ IsFilledIn K Ω`.
* `TauCeti.isRungeCompactPair_iff_forall_notMem_exists_norm_gt`: point-separation criterion for
  Runge pairs.
* `TauCeti.IsCompact.isConnected_compl_iff_polynomial_approximation`: polynomial Runge theorem
  on `ℂ`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Theorem 1.3.1.
* W. Rudin, *Real and Complex Analysis*, Chapter 13 (Runge's theorem).
-/

public section

open Metric Set
open scoped NNReal Topology

namespace TauCeti

/-- Forward Runge approximation for a `IsRungeCompactPair`: every function holomorphic on an open
neighbourhood `U` of `K` can be approximated uniformly on `K` by functions holomorphic on `Ω`. -/
theorem IsRungeCompactPair.exists_differentiableOn_norm_sub_lt {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, -, hLUO, hop⟩ := exists_finite_rank_runge_operator hRunge hU hKU
  obtain ⟨M, hM⟩ :=
    hL.bddAbove_image (hf.continuousOn.mono (hLUO.trans inter_subset_left)).norm
  set B : ℝ := max M 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hLB : ∀ z ∈ L, ‖f z‖ ≤ B := fun z hz =>
    (hM ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  set ε' : ℝ := ε / (2 * (B + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨N, ζ, w, g, -, hg_diff, hbound⟩ := hop ε' hε'
  refine ⟨fun z => ∑ j : Fin N, w j * f (ζ j) * g j z, ?_, fun z hz => ?_⟩
  · exact DifferentiableOn.fun_sum fun j _ => (hg_diff j).const_mul (w j * f (ζ j))
  · calc ‖f z - ∑ j : Fin N, w j * f (ζ j) * g j z‖
        ≤ ε' * B := hbound f hf B hB0 hLB z hz
      _ = (ε / 2) * (B / (B + 1)) := by
          simp only [ε']
          field_simp
      _ ≤ (ε / 2) * 1 := by
          gcongr
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = ε / 2 := mul_one _
      _ < ε := half_lt_self hε

/-- **Runge's approximation theorem** (domain-relative form): for compact `K ⊆ Ω` with `Ω ⊆ ℂ`
open, `IsRungeCompactPair Ω K` holds if and only if every function holomorphic on an open
neighbourhood `U ⊇ K` can be uniformly approximated on `K` by functions holomorphic on `Ω`. -/
theorem isRungeCompactPair_iff_approximation {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
          ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hRunge U hU hKU f hf ε hε =>
    hRunge.exists_differentiableOn_norm_sub_lt hU hKU hf hε, fun happrox => ?_⟩
  refine isRungeCompactPair_iff.mpr ⟨hΩ, hK, hKΩ, isFilledIn_iff.mpr fun x hx ⟨hCc, hCΩ⟩ => ?_⟩
  set C : Set ℂ := connectedComponentIn (Ω \ K) x
  have hKU : K ⊆ {x}ᶜ := fun w hw hwx => hx.2 (hwx ▸ hw)
  have hf_diff : DifferentiableOn ℂ (fun z : ℂ => (z - x)⁻¹) {x}ᶜ :=
    (differentiableOn_id.sub_const x).inv fun _ hz => sub_ne_zero.mpr hz
  obtain ⟨M, hM⟩ := hK.bddAbove_image (continuous_id.sub continuous_const).norm.continuousOn
  set B : ℝ := max M 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hKB : ∀ w ∈ K, ‖w - x‖ ≤ B := fun w hw =>
    (hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  set ε : ℝ := (2 * (B + 1))⁻¹
  have hε : 0 < ε := by positivity
  obtain ⟨g, hg_diff, hg_lt⟩ := happrox {x}ᶜ isOpen_ne hKU (fun z => (z - x)⁻¹) hf_diff ε hε
  let h : ℂ → ℂ := fun z => 1 - (z - x) * g z
  have hh_diff : DifferentiableOn ℂ h (closure C) :=
    ((differentiableOn_id.sub_const x).mul (hg_diff.mono hCΩ)).const_sub 1
  have hh_cl : DiffContOnCl ℂ h C :=
    ⟨hh_diff.mono subset_closure, hh_diff.continuousOn⟩
  have hh_fr : ∀ w ∈ frontier C, ‖h w‖ ≤ (1 / 2 : ℝ) := fun w hw => by
    have hwK : w ∈ K := by
      by_contra hwK
      exact frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK.isClosed) x hw
        ⟨hCΩ (frontier_subset_closure hw), hwK⟩
    have hwx : w - x ≠ 0 := sub_ne_zero.mpr (fun heq => hx.2 (heq ▸ hwK))
    have hfactor : h w = (w - x) * ((w - x)⁻¹ - g w) := by
      simp only [h]
      rw [mul_sub, mul_inv_cancel₀ hwx]
    rw [hfactor, norm_mul]
    calc ‖w - x‖ * ‖(w - x)⁻¹ - g w‖
        ≤ B * ε := mul_le_mul (hKB w hwK) (hg_lt w hwK).le (norm_nonneg _) hB0
      _ = (1 / 2 : ℝ) * (B / (B + 1)) := by
          simp only [ε]
          field_simp
      _ ≤ (1 / 2 : ℝ) * 1 := by
          gcongr
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = 1 / 2 := mul_one _
  have hhx : ‖h x‖ ≤ (1 / 2 : ℝ) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le (hCc.isBounded.subset subset_closure) hh_cl
      hh_fr (subset_closure (mem_connectedComponentIn hx))
  have hhx1 : h x = 1 := by simp [h]
  rw [hhx1, norm_one] at hhx
  linarith

private lemma connectedComponentIn_compl_subset_of_closure_subset {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) {w : ℂ} (hw : w ∈ Ω \ K)
    (hwΩ : closure (connectedComponentIn (Ω \ K) w) ⊆ Ω) :
    connectedComponentIn Kᶜ w ⊆ connectedComponentIn (Ω \ K) w := by
  let C : Set ℂ := connectedComponentIn (Ω \ K) w
  have hCopen : IsOpen C := (hΩ.sdiff hK.isClosed).connectedComponentIn
  have hfr : frontier C ⊆ K := fun y hy => by
    by_contra hyK
    exact frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK.isClosed) w hy
      ⟨hwΩ (frontier_subset_closure hy), hyK⟩
  have hsub_union : Kᶜ ⊆ C ∪ (closure C)ᶜ := fun y hy => by
    by_cases hyC : y ∈ closure C
    · left
      by_contra hyC'
      have hy_fr : y ∈ frontier C := by
        change y ∈ closure C \ interior C
        rw [hCopen.interior_eq]
        exact ⟨hyC, hyC'⟩
      exact hy (hfr hy_fr)
    · right
      exact hyC
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hCopen
    isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure)
    ((connectedComponentIn_subset Kᶜ w).trans hsub_union)
    ⟨w, mem_connectedComponentIn (show w ∈ Kᶜ from hw.2), mem_connectedComponentIn hw⟩

private lemma isCompact_and_isFilledIn_fill {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    let Ktilde : Set ℂ := K ∪ {z | z ∈ Ω \ K ∧
      IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}
    IsCompact Ktilde ∧ Ktilde ⊆ Ω ∧ IsFilledIn Ktilde Ω := by
  intro Ktilde
  have hKtilde_Ω : Ktilde ⊆ Ω := by
    rintro z (hzK | ⟨hz, -, -⟩)
    · exact hKΩ hzK
    · exact hz.1
  have hKtilde_fill : Ktilde ⊆ filledHull K := by
    rintro z (hzK | ⟨hz, hCc, hCΩ⟩)
    · exact subset_filledHull hzK
    · have hfr : frontier (connectedComponentIn (Ω \ K) z) ⊆ K := fun y hy => by
        by_contra hyK
        exact frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK.isClosed) z hy
          ⟨hCΩ (frontier_subset_closure hy), hyK⟩
      exact subset_filledHull_of_frontier_subset (hCc.isBounded.subset subset_closure) hfr
        (mem_connectedComponentIn hz)
  have hcomp_miss : ∀ z ∈ filledHull K \ Ktilde,
      connectedComponentIn Kᶜ z ⊆ Ktildeᶜ := fun z ⟨_, hzKt⟩ w hwD hwKt => by
    have hzK : z ∉ K := fun hz => hzKt (Or.inl hz)
    have hwK : w ∉ K := connectedComponentIn_subset Kᶜ z hwD
    rcases hwKt with hwK' | ⟨hw, hwCc, hwΩ⟩
    · exact hwK hwK'
    · have hD_sub : connectedComponentIn Kᶜ w ⊆ connectedComponentIn (Ω \ K) w :=
        connectedComponentIn_compl_subset_of_closure_subset hΩ hK hw hwΩ
      have hD_eq : connectedComponentIn Kᶜ w = connectedComponentIn Kᶜ z :=
        (connectedComponentIn_eq hwD).symm
      have hzC : z ∈ connectedComponentIn (Ω \ K) w :=
        hD_sub (hD_eq ▸ mem_connectedComponentIn hzK)
      have hC_eq : connectedComponentIn (Ω \ K) z = connectedComponentIn (Ω \ K) w :=
        (connectedComponentIn_eq hzC).symm
      have hz_mem : z ∈ Ω \ K := connectedComponentIn_subset (Ω \ K) w hzC
      exact hzKt (Or.inr ⟨hz_mem, hC_eq ▸ hwCc, hC_eq ▸ hwΩ⟩)
  have hKtilde_closed : IsClosed Ktilde := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    by_cases hzF : z ∈ filledHull K
    · have hzK : z ∉ K := fun h => hz (Or.inl h)
      refine ⟨connectedComponentIn Kᶜ z, fun w hw => hcomp_miss z ⟨hzF, hz⟩ hw,
        hK.isClosed.isOpen_compl.connectedComponentIn, mem_connectedComponentIn hzK⟩
    · exact ⟨(filledHull K)ᶜ, fun w hw hwK => hw (hKtilde_fill hwK),
        hK.isClosed.isClosed_filledHull.isOpen_compl, hzF⟩
  have hKtilde_cpt : IsCompact Ktilde :=
    isCompact_of_isClosed_isBounded hKtilde_closed
      ((isBounded_filledHull.mpr hK.isBounded).subset hKtilde_fill)
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  have hfill_sub : filledHull Ktilde ⊆ filledHull K := fun y hy => by
    by_contra hyF
    have hcomp_pre : IsPreconnected (filledHull K)ᶜ :=
      (isConnected_compl_filledHull hrank hK.isBounded).isPreconnected
    have hcomp_sub : (filledHull K)ᶜ ⊆ connectedComponentIn Ktildeᶜ y :=
      hcomp_pre.subset_connectedComponentIn hyF fun w hw hwK => hw (hKtilde_fill hwK)
    have hunb : ¬ Bornology.IsBounded (filledHull K)ᶜ := fun h =>
      NormedSpace.unbounded_univ ℝ ℂ <| by
        simpa using h.union (isBounded_filledHull.mpr hK.isBounded)
    exact hunb ((mem_filledHull_iff.mp hy).subset hcomp_sub)
  have hKtilde_filled : IsFilledIn Ktilde Ω := by
    refine (isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
      hKtilde_cpt.isClosed hΩ hKtilde_Ω).2 fun x ⟨hx_fill, hx_not⟩ hsub => ?_
    have hxF : x ∈ filledHull K := hfill_sub hx_fill
    have hxK : x ∉ K := fun h => hx_not (Or.inl h)
    let D : Set ℂ := connectedComponentIn Kᶜ x
    have hD_miss : D ⊆ Ktildeᶜ := hcomp_miss x ⟨hxF, hx_not⟩
    have hD_sub : D ⊆ connectedComponentIn Ktildeᶜ x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxK) hD_miss
    have hD_Ω : D ⊆ Ω := hD_sub.trans hsub
    have hD_sub_ΩK : D ⊆ Ω \ K := fun w hw =>
      ⟨hD_Ω hw, connectedComponentIn_subset Kᶜ x hw⟩
    have hD_eq : connectedComponentIn (Ω \ K) x = D := by
      refine Subset.antisymm (connectedComponentIn_mono _ (sdiff_subset_compl Ω K)) ?_
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxK) hD_sub_ΩK
    have hfrD : frontier D ⊆ K := by
      simpa [D] using frontier_connectedComponentIn_subset_compl hK.isClosed.isOpen_compl x
    have hclD_Ω : closure D ⊆ Ω := by
      rw [closure_eq_self_union_frontier]
      exact union_subset hD_Ω (hfrD.trans hKΩ)
    have hclD_cpt : IsCompact (closure D) :=
      isCompact_of_isClosed_isBounded isClosed_closure (mem_filledHull_iff.mp hxF).closure
    exact hx_not (Or.inr ⟨⟨hD_Ω (mem_connectedComponentIn hxK), hxK⟩,
      hD_eq ▸ hclD_cpt, hD_eq ▸ hclD_Ω⟩)
  exact ⟨hKtilde_cpt, hKtilde_Ω, hKtilde_filled⟩

private lemma isPreconnected_connectedComponentIn_sdiff_singleton
    {K : Set ℂ} (hK : IsCompact K) (x z : ℂ) :
    IsPreconnected (connectedComponentIn Kᶜ x \ {z}) := by
  let D : Set ℂ := connectedComponentIn Kᶜ x
  by_cases hz : z ∈ D
  · have hD_open : IsOpen D := hK.isClosed.isOpen_compl.connectedComponentIn
    have : PreconnectedSpace D := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    let z' : D := ⟨z, hz⟩
    have hdisc : IsDiscrete ({z'} : Set D) := isDiscrete_iff_discreteTopology.mpr inferInstance
    have hpre : IsPreconnected ({z'}ᶜ : Set D) := by
      refine isPreconnected_compl_of_isDiscrete isClosed_singleton hdisc ?_
      rintro y rfl U hU
      rw [Metric.mem_nhds_iff] at hU
      obtain ⟨r₀, hr₀, hr₀U⟩ := hU
      obtain ⟨r₁, hr₁, hr₁D⟩ := Metric.isOpen_iff.mp hD_open z hz
      set r : ℝ := min r₀ r₁
      have hr : 0 < r := lt_min hr₀ hr₁
      refine ⟨((↑) : D → ℂ) ⁻¹' ball z r,
        continuous_subtype_val.continuousAt (ball_mem_nhds z hr), ?_, ?_⟩
      · intro w hw
        have hwd : dist w z' < r := by
          rw [Subtype.dist_eq]
          exact hw
        exact hr₀U (mem_ball.mpr (lt_of_lt_of_le hwd (min_le_left r₀ r₁)))
      · have himg : ((↑) : D → ℂ) '' (((↑) : D → ℂ) ⁻¹' ball z r \ {z'}) = ball z r \ {z} := by
          ext w
          simp only [mem_image, mem_sdiff, mem_preimage, mem_singleton_iff, Subtype.exists]
          constructor
          · rintro ⟨a, haD, ⟨ha_ball, ha_ne⟩, rfl⟩
            exact ⟨ha_ball, fun heq => ha_ne (Subtype.ext heq)⟩
          · rintro ⟨hw_ball, hw_ne⟩
            exact ⟨w, hr₁D (ball_subset_ball (min_le_right _ _) hw_ball),
              ⟨hw_ball, fun heq => hw_ne (congrArg Subtype.val heq)⟩, rfl⟩
        have hconn_ball : IsConnected (ball z r \ {z}) :=
          isConnected_ball_sdiff_singleton hrank z hr
        have hpre_sub : IsPreconnected (((↑) : D → ℂ) ⁻¹' ball z r \ {z'}) := by
          refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
          rw [himg]
          exact hconn_ball.isPreconnected
        have hne_sub : (((↑) : D → ℂ) ⁻¹' ball z r \ {z'}).Nonempty := by
          obtain ⟨w, hw⟩ := hconn_ball.nonempty
          rw [← himg] at hw
          obtain ⟨y, hy, -⟩ := hw
          exact ⟨y, hy⟩
        exact ⟨hne_sub, hpre_sub⟩
    have himg' : ((↑) : D → ℂ) '' ({z'}ᶜ : Set D) = D \ {z} := by
      ext w
      simp [z']
    simpa [← himg'] using hpre.image _ continuous_subtype_val.continuousOn
  · rw [show connectedComponentIn Kᶜ x \ {z} = D from sdiff_singleton_eq_self hz]
    exact isPreconnected_connectedComponentIn

/-- The holomorphic hull of a compact subset `K ⊆ Ω` is compact and coincides with the union of
`K` and all connected components of `Ω \ K` whose closures are compact subsets of `Ω`. -/
theorem holomorphicHull_eq_fill {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (holomorphicHull Ω K) ∧
      holomorphicHull Ω K = K ∪ {z | z ∈ Ω \ K ∧
        IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
        closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} := by
  let Ktilde : Set ℂ := K ∪ {z | z ∈ Ω \ K ∧
    IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
    closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}
  obtain ⟨hKt_cpt, hKt_Ω, hKt_filled⟩ := isCompact_and_isFilledIn_fill hΩ hK hKΩ
  have hsub : Ktilde ⊆ holomorphicHull Ω K := fill_subset_holomorphicHull hΩ hK hKΩ
  have hsup : holomorphicHull Ω K ⊆ Ktilde := fun z hz => by
    by_contra hzKt
    have hzΩ : z ∈ Ω := holomorphicHull_subset hz
    let K₁ : Set ℂ := insert z Ktilde
    have hK₁_cpt : IsCompact K₁ := hKt_cpt.insert z
    have hK₁_Ω : K₁ ⊆ Ω := insert_subset_iff.mpr ⟨hzΩ, hKt_Ω⟩
    have hK₁_filled : IsFilledIn K₁ Ω := by
      refine (isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
        hK₁_cpt.isClosed hΩ hK₁_Ω).2 fun x ⟨hx_fill, hx_not⟩ hsub₁ => ?_
      have hx_not_Kt : x ∉ Ktilde := fun h => hx_not (mem_insert_of_mem z h)
      have hxz : x ≠ z := fun h => hx_not (h ▸ mem_insert z Ktilde)
      have hpre : IsPreconnected (connectedComponentIn Ktildeᶜ x \ {z}) :=
        isPreconnected_connectedComponentIn_sdiff_singleton hKt_cpt x z
      have hD_sub_K₁ : connectedComponentIn Ktildeᶜ x \ {z} ⊆ K₁ᶜ :=
        fun w ⟨hw1, hw2⟩ hwK₁ => by
          rcases mem_insert_iff.mp hwK₁ with rfl | hwKt
          · exact hw2 rfl
          · exact connectedComponentIn_subset Ktildeᶜ x hw1 hwKt
      have hD_sub : connectedComponentIn Ktildeᶜ x \ {z} ⊆ connectedComponentIn K₁ᶜ x :=
        hpre.subset_connectedComponentIn ⟨mem_connectedComponentIn hx_not_Kt, hxz⟩ hD_sub_K₁
      have hD_bdd : Bornology.IsBounded (connectedComponentIn Ktildeᶜ x) := by
        have hsub' : connectedComponentIn Ktildeᶜ x ⊆
            (connectedComponentIn Ktildeᶜ x \ {z}) ∪ {z} := fun w hw => by
          by_cases hwz : w = z
          · right; exact hwz
          · left; exact ⟨hw, hwz⟩
        exact (((mem_filledHull_iff.mp hx_fill).subset hD_sub).union
          (Bornology.isBounded_singleton)).subset hsub'
      have hD_Ω : connectedComponentIn Ktildeᶜ x ⊆ Ω := fun w hw => by
        by_cases hwz : w = z
        · exact hwz ▸ hzΩ
        · exact (hD_sub.trans hsub₁) ⟨hw, hwz⟩
      exact (isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
        hKt_cpt.isClosed hΩ hKt_Ω).1 hKt_filled x
        ⟨mem_filledHull_iff.mpr hD_bdd, hx_not_Kt⟩ hD_Ω
    have hRunge₁ : IsRungeCompactPair Ω K₁ :=
      isRungeCompactPair_iff.mpr ⟨hΩ, hK₁_cpt, hK₁_Ω, hK₁_filled⟩
    obtain ⟨r, hr, hr_ball⟩ := Metric.isOpen_iff.mp hKt_cpt.isClosed.isOpen_compl z hzKt
    set r' : ℝ := r / 2
    have hr' : 0 < r' := half_pos hr
    let U₁ : Set ℂ := (closedBall z r')ᶜ
    let U₂ : Set ℂ := ball z r'
    have hU₁ : IsOpen U₁ := isClosed_closedBall.isOpen_compl
    have hU₂ : IsOpen U₂ := isOpen_ball
    have hKtU₁ : Ktilde ⊆ U₁ := fun w hwK hw_cb =>
      hr_ball (closedBall_subset_ball (half_lt_self hr) hw_cb) hwK
    have hzU₂ : z ∈ U₂ := mem_ball_self hr'
    have hdisj : Disjoint U₁ U₂ := disjoint_left.mpr fun w hw1 hw2 =>
      hw1 (ball_subset_closedBall hw2)
    classical
    let f : ℂ → ℂ := fun w => if w ∈ U₁ then 0 else 1
    have hf_diff : DifferentiableOn ℂ f (U₁ ∪ U₂) := fun w hw => by
      rcases hw with hw1 | hw2
      · have heq : f =ᶠ[𝓝 w] fun _ => (0 : ℂ) :=
          Filter.eventually_of_mem (hU₁.mem_nhds hw1) fun y hy => by simp [f, hy]
        exact (differentiableAt_const 0).congr_of_eventuallyEq heq |>.differentiableWithinAt
      · have heq : f =ᶠ[𝓝 w] fun _ => (1 : ℂ) :=
          Filter.eventually_of_mem (hU₂.mem_nhds hw2) fun y hy => by
            simp [f, hdisj.notMem_of_mem_right hy]
        exact (differentiableAt_const 1).congr_of_eventuallyEq heq |>.differentiableWithinAt
    obtain ⟨g, hg_diff, hg_lt⟩ :=
      hRunge₁.exists_differentiableOn_norm_sub_lt (hU₁.union hU₂)
        (insert_subset_iff.mpr ⟨Or.inr hzU₂, hKtU₁.trans subset_union_left⟩)
        hf_diff (by norm_num : (0 : ℝ) < 1 / 3)
    have hgK : ∀ w ∈ K, ‖g w‖ ≤ (1 / 3 : ℝ) := fun w hwK => by
      have hwKt : w ∈ Ktilde := Or.inl hwK
      have hlt := hg_lt w (mem_insert_of_mem z hwKt)
      have hfw : f w = 0 := by simp [f, hKtU₁ hwKt]
      rw [hfw, zero_sub, norm_neg] at hlt
      exact hlt.le
    have hgz := (mem_holomorphicHull_iff.mp hz).2 g hg_diff (1 / 3) hgK
    have hgz1 := hg_lt z (mem_insert z Ktilde)
    have hfz : f z = 1 := by simp [f, hdisj.notMem_of_mem_right hzU₂]
    rw [hfz] at hgz1
    have htri : (1 : ℝ) ≤ ‖(1 : ℂ) - g z‖ + ‖g z‖ := by
      calc (1 : ℝ) = ‖(1 : ℂ) - g z + g z‖ := by simp
        _ ≤ ‖(1 : ℂ) - g z‖ + ‖g z‖ := norm_add_le _ _
    linarith
  have heq : holomorphicHull Ω K = Ktilde := Subset.antisymm hsup hsub
  exact ⟨heq ▸ hKt_cpt, heq⟩

/-- For compact `K ⊆ Ω` with `Ω` open, `holomorphicHull Ω K = K` if and only if `K` is filled in
`Ω`. -/
theorem holomorphicHull_eq_self_iff_isFilledIn {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔ IsFilledIn K Ω := by
  have heq := (holomorphicHull_eq_fill hΩ hK hKΩ).2
  constructor
  · intro h
    refine isFilledIn_iff.mpr fun x hx ⟨hCc, hCΩ⟩ => ?_
    have hx_hull : x ∈ holomorphicHull Ω K := by
      rw [heq]
      exact Or.inr ⟨hx, hCc, hCΩ⟩
    rw [h] at hx_hull
    exact hx.2 hx_hull
  · intro hfill
    rw [heq]
    refine union_eq_left.mpr fun z ⟨hz, hCc, hCΩ⟩ => ?_
    exact (isFilledIn_iff.mp hfill z hz ⟨hCc, hCΩ⟩).elim

/-- A compact subset `K ⊆ Ω` forms a Runge pair with `Ω` if and only if `holomorphicHull Ω K = K`.
-/
theorem isRungeCompactPair_iff_holomorphicHull_eq {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔ holomorphicHull Ω K = K := by
  rw [holomorphicHull_eq_self_iff_isFilledIn hΩ hK hKΩ, isRungeCompactPair_iff]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hΩ, hK, hKΩ, h⟩⟩

/-- Point-separation criterion for Runge compact pairs: `IsRungeCompactPair Ω K` holds if and
only if every `z ∈ Ω \ K` is separated from `K` by a holomorphic function on `Ω`. -/
theorem isRungeCompactPair_iff_forall_notMem_exists_norm_gt {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔
      ∀ z ∈ Ω \ K, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ 1 < ‖f z‖ ∧ ∀ w ∈ K, ‖f w‖ ≤ 1 := by
  rw [isRungeCompactPair_iff_holomorphicHull_eq hΩ hK hKΩ]
  constructor
  · intro hhull z hz
    rcases K.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
    · exact ⟨fun _ => 2, differentiableOn_const 2, by norm_num, fun _ h => h.elim⟩
    have hz' : z ∉ holomorphicHull Ω K := by
      rw [hhull]
      exact hz.2
    rw [mem_holomorphicHull_iff] at hz'
    push Not at hz'
    obtain ⟨f, hf, B, hKB, hfz⟩ := hz' hz.1
    have hB0 : 0 ≤ B := (norm_nonneg (f w₀)).trans (hKB w₀ hw₀)
    let t : ℝ := (B + ‖f z‖) / 2
    have ht0 : 0 < t := by dsimp only [t]; linarith [norm_nonneg (f z)]
    have hBt : B < t := by dsimp only [t]; linarith
    refine ⟨fun w => (t⁻¹ : ℂ) * f w, hf.const_mul _, ?_, fun w hw => ?_⟩
    · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, inv_mul_eq_div,
        lt_div_iff₀ ht0]
      dsimp only [t]
      linarith
    · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, inv_mul_eq_div,
        div_le_one ht0]
      exact (hKB w hw).trans hBt.le
  · intro hsep
    refine Subset.antisymm (fun z hz => ?_) (subset_holomorphicHull hKΩ)
    by_contra hzK
    obtain ⟨f, hf, hfz, hKB⟩ := hsep z ⟨holomorphicHull_subset hz, hzK⟩
    exact hfz.not_ge ((mem_holomorphicHull_iff.mp hz).2 f hf 1 hKB)

/-- Every stage of `TauCeti.rungeExhaustion Ω` equals its own holomorphic hull in `Ω`. -/
theorem holomorphicHull_rungeExhaustion {Ω : Set ℂ} (hΩ : IsOpen Ω) (n : ℕ) :
    holomorphicHull Ω (rungeExhaustion Ω n) = rungeExhaustion Ω n :=
  (holomorphicHull_eq_self_iff_isFilledIn hΩ (isCompact_rungeExhaustion Ω n)
    (rungeExhaustion_subset Ω n)).mpr (isFilledIn_rungeExhaustion hΩ n)

/-- Every entire function on `ℂ` can be approximated uniformly on any compact set `K ⊆ ℂ` by
polynomials in `Polynomial ℂ`. -/
theorem _root_.Differentiable.exists_polynomial_norm_sub_lt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball 0
  set R : NNReal := (max R₀ 1).toNNReal
  have hR : (R : ℝ) = max R₀ 1 := Real.coe_toNNReal _ (le_max_of_le_right zero_le_one)
  have hRpos : 0 < R := by
    rw [← NNReal.coe_pos, hR]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set R' : NNReal := R + 1
  have hR'pos : 0 < R' := lt_of_lt_of_le hRpos le_self_add
  have hKsub : K ⊆ ball (0 : ℂ) R := fun w hw =>
    ball_subset_ball (hR ▸ le_max_left _ _) (hR₀ hw)
  have hps := (hf.differentiableOn.mono (subset_univ (closedBall (0 : ℂ) R'))).hasFPowerSeriesOnBall
    hR'pos
  have hu := hps.tendstoUniformlyOn (r' := R) (ENNReal.coe_lt_coe.2 (lt_add_one R))
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hu ε hε).exists
  set q := cauchyPowerSeries f 0 R'
  refine ⟨∑ n ∈ Finset.range N, Polynomial.C (q.coeff n) * Polynomial.X ^ n, fun z hz => ?_⟩
  have hq_eval : (∑ n ∈ Finset.range N, Polynomial.C (q.coeff n) * Polynomial.X ^ n).eval z =
      q.partialSum N z := by
    change (Polynomial.evalRingHom z)
        (∑ n ∈ Finset.range N, Polynomial.C (q.coeff n) * Polynomial.X ^ n) =
      q.partialSum N z
    simp only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, Polynomial.eval_X, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  rw [hq_eval]
  simpa [zero_add, dist_eq_norm, norm_sub_rev] using hN z (hKsub hz)

/-- **Polynomial Runge theorem**: a compact set `K ⊆ ℂ` has connected complement `Kᶜ` if and only
if every holomorphic function on an open neighbourhood `U ⊇ K` can be approximated uniformly on `K`
by polynomials `p : Polynomial ℂ`. -/
theorem _root_.IsCompact.isConnected_compl_iff_polynomial_approximation {K : Set ℂ}
    (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  have hconn_iff_runge : IsConnected Kᶜ ↔ IsRungeCompactPair Set.univ K := by
    rw [isRungeCompactPair_iff_holomorphicHull_eq isOpen_univ hK (subset_univ K),
      holomorphicHull_eq_self_iff_isFilledIn isOpen_univ hK (subset_univ K),
      isFilledIn_univ_iff hK.isClosed]
    constructor
    · intro hconn
      refine Subset.antisymm (fun x hx => ?_) (subset_filledHull)
      by_contra hxK
      have hcomp_eq : connectedComponentIn Kᶜ x = Kᶜ :=
        hconn.isPreconnected.connectedComponentIn hxK
      have hunb : ¬ Bornology.IsBounded Kᶜ := fun hb =>
        NormedSpace.unbounded_univ ℝ ℂ <| by simpa using hb.union hK.isBounded
      rw [mem_filledHull_iff, hcomp_eq] at hx
      exact hunb hx
    · intro hfill
      rw [← hfill]
      exact isConnected_compl_filledHull hrank hK.isBounded
  rw [hconn_iff_runge, isRungeCompactPair_iff_approximation isOpen_univ hK (subset_univ K)]
  constructor
  · intro h U hU hKU f hf ε hε
    obtain ⟨g, hg_diff, hg_lt⟩ := h U hU hKU f hf (ε / 2) (half_pos hε)
    obtain ⟨p, hp_lt⟩ := (differentiableOn_univ.mp hg_diff).exists_polynomial_norm_sub_lt
      hK (half_pos hε)
    refine ⟨p, fun z hz => ?_⟩
    calc ‖f z - p.eval z‖
        ≤ ‖f z - g z‖ + ‖g z - p.eval z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hg_lt z hz) (hp_lt z hz)
      _ = ε := add_halves ε
  · intro h U hU hKU f hf ε hε
    obtain ⟨p, hp_lt⟩ := h U hU hKU f hf ε hε
    exact ⟨fun z => p.eval z, p.differentiable.differentiableOn, hp_lt⟩

end TauCeti
