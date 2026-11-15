/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.DenseEmbedding
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic

/-!
# Elliott's two-way approximate intertwining

This file proves two forms of Elliott's back-and-forth approximate intertwining argument for
complex C⋆-algebras:

* `TauCeti.exists_starAlgEquiv_of_approx_intertwining`: given sequences of possibly nonunital
  `⋆`-homomorphisms `φ : ℕ → A →⋆ₙₐ[ℂ] B` and `ψ : ℕ → B →⋆ₙₐ[ℂ] A` between possibly nonunital
  C⋆-algebras, increasing finite subsets `F n ⊆ A` and `G n ⊆ B` generating dense nonunital
  `⋆`-subalgebras such that `φ n (F n) ⊆ G n` and `ψ n (G n) ⊆ F (n + 1)`, and summable error
  sequences `δ, ε : ℕ → ℝ` bounding `‖ψ n (φ n a) - a‖ ≤ δ n` on `F n` and
  `‖φ (n + 1) (ψ n b) - b‖ ≤ ε n` on `G n`, the sequences `φ` and `ψ` converge in the point-norm
  topology to mutually inverse `⋆`-isomorphisms `θ : A ≃⋆ₐ[ℂ] B` and `θ.symm`, with explicit
  series tail bounds on `F n` and `G n`.
* `TauCeti.elliott_intertwining` (and the two-sided refinement
  `TauCeti.exists_starAlgEquiv_approximatelyUnitarilyEquivalent`): if `φ : A →⋆ₙₐ[ℂ] B` and
  `ψ : B →⋆ₙₐ[ℂ] A` between separable unital C⋆-algebras satisfy `ψ ∘ φ ≈ᵤ id_A` and
  `φ ∘ ψ ≈ᵤ id_B` with target unitaries, then there exists a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B`
  approximately unitarily equivalent to `φ` (with `θ.symm` approximately unitarily equivalent to
  `ψ`).

## References

* [M. Rørdam, *Classification of Nuclear, Simple C*-Algebras*], Proposition 2.3.2 / Corollary 2.3.4
* [E. Kirchberg and N. C. Phillips, *Embedding of exact C*-algebras in the Cuntz algebra
  $\mathcal{O}_2$*], Lemma 0.6
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

section StationaryIntertwining

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Single-step Cauchy bound in an approximate intertwining: if `g (f a)` approximates `a` within
`δ` and `f' (g (f a))` approximates `f a` within `ε`, contractivity of `f'` bounds
`dist (f a) (f' a)` by `δ + ε`. -/
private theorem approx_intertwining_step_le {f f' : A →⋆ₙₐ[ℂ] B} {g : B →⋆ₙₐ[ℂ] A} {a : A}
    {δ ε : ℝ} (hgf : ‖g (f a) - a‖ ≤ δ) (hf'g : ‖f' (g (f a)) - f a‖ ≤ ε) :
    dist (f a) (f' a) ≤ δ + ε := by
  have hsplit : f' a - f a = f' (a - g (f a)) + (f' (g (f a)) - f a) := by
    simp only [map_sub]
    abel
  rw [dist_comm, dist_eq_norm, hsplit]
  calc
    ‖f' (a - g (f a)) + (f' (g (f a)) - f a)‖
      ≤ ‖f' (a - g (f a))‖ + ‖f' (g (f a)) - f a‖ := norm_add_le _ _
    _ ≤ ‖a - g (f a)‖ + ‖f' (g (f a)) - f a‖ :=
      add_le_add (NonUnitalStarAlgHom.norm_apply_le f' _) le_rfl
    _ = ‖g (f a) - a‖ + ‖f' (g (f a)) - f a‖ := by rw [norm_sub_rev a]
    _ ≤ δ + ε := add_le_add hgf hf'g

/-- From summable consecutive step bounds on an increasing sequence of finite sets generating a
dense nonunital `⋆`-subalgebra, construct the point-norm limit `⋆`-homomorphism together with the
series tail estimate on each `F n`. -/
private theorem exists_tendsto_and_tsum_le_of_step
    (φ : ℕ → A →⋆ₙₐ[ℂ] B) (F : ℕ → Finset A) (hF_mono : Monotone F)
    (hF_dense : Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (F n : Set A)) : Set A))
    {d : ℕ → ℝ} (hd : Summable d)
    (hstep : ∀ k, ∀ a ∈ F k, dist (φ k a) (φ (k + 1) a) ≤ d k) :
    ∃ φ_lim : A →⋆ₙₐ[ℂ] B,
      Tendsto φ atTop (𝓝 φ_lim) ∧
      ∀ n, ∀ a ∈ F n, ‖φ_lim a - φ n a‖ ≤ ∑' m, d (m + n) := by
  have hcauchy : ∀ a ∈ (⋃ n, (F n : Set A)), CauchySeq fun k ↦ φ k a := by
    rintro a ⟨_, ⟨n, rfl⟩, ha⟩
    refine (cauchySeq_shift n).mp ?_
    refine cauchySeq_of_dist_le_of_summable (fun m ↦ d (m + n)) (fun m ↦ ?_)
      ((summable_nat_add_iff n).mpr hd)
    simpa only [Nat.succ_add] using hstep (m + n) a (hF_mono (Nat.le_add_left n m) ha)
  obtain ⟨φ_lim, hφ_lim⟩ :=
    NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq_adjoin hF_dense hcauchy
  refine ⟨φ_lim, hφ_lim, fun n a ha ↦ ?_⟩
  have hta : Tendsto (fun m ↦ φ (m + n) a) atTop (𝓝 (φ_lim a)) :=
    (tendsto_add_atTop_iff_nat n).mpr
      (NonUnitalStarAlgHom.tendsto_iff_forall_tendsto.mp hφ_lim a)
  have hdist := dist_le_tsum_of_dist_le_of_tendsto₀ (fun m ↦ d (m + n))
    (fun m ↦ by simpa only [Nat.succ_add] using hstep (m + n) a (hF_mono (Nat.le_add_left n m) ha))
    ((summable_nat_add_iff n).mpr hd) hta
  simpa only [zero_add, dist_eq_norm, norm_sub_rev (φ n a)] using hdist

/-- If `f` and `g` converge in the point-norm topology to `f₀` and `g₀` and `‖g k (f k a) - a‖`
is bounded on `F k` by a sequence tending to `0`, then `g₀.comp f₀ = .id ℂ A`. -/
private theorem comp_eq_id_of_tendsto_intertwining
    {f : ℕ → A →⋆ₙₐ[ℂ] B} {g : ℕ → B →⋆ₙₐ[ℂ] A} {f₀ : A →⋆ₙₐ[ℂ] B} {g₀ : B →⋆ₙₐ[ℂ] A}
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (F : ℕ → Finset A) (hF_mono : Monotone F)
    (hF_dense : Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (F n : Set A)) : Set A))
    {δ : ℕ → ℝ} (hδ0 : Tendsto δ atTop (𝓝 0))
    (herr : ∀ k, ∀ a ∈ F k, ‖g k (f k a) - a‖ ≤ δ k) :
    g₀.comp f₀ = .id ℂ A := by
  have h₁ : Tendsto (fun k ↦ (g k).comp (f k)) atTop (𝓝 (g₀.comp f₀)) :=
    NonUnitalStarAlgHom.tendsto_comp hg hf
  have h₂ : Tendsto (fun k ↦ (g k).comp (f k)) atTop (𝓝 (.id ℂ A)) := by
    refine NonUnitalStarAlgHom.tendsto_of_tendsto_adjoin hF_dense ?_
    rintro a ⟨_, ⟨n, rfl⟩, ha⟩
    simp only [NonUnitalStarAlgHom.coe_id, id_eq]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hδ0
    filter_upwards [eventually_ge_atTop n] with k hk
    exact herr k a (hF_mono hk ha)
  exact tendsto_nhds_unique h₁ h₂

/-- **Stationary two-way approximate intertwining** for possibly nonunital C⋆-algebras.

Given `φ : ℕ → A →⋆ₙₐ[ℂ] B` and `ψ : ℕ → B →⋆ₙₐ[ℂ] A`, monotone finite sets `F : ℕ → Finset A`
and `G : ℕ → Finset B` generating dense nonunital `⋆`-subalgebras with `φ n (F n) ⊆ G n` and
`ψ n (G n) ⊆ F (n + 1)`, and summable error sequences `δ, ε : ℕ → ℝ` controlling
`‖ψ n (φ n a) - a‖ ≤ δ n` on `F n` and `‖φ (n + 1) (ψ n b) - b‖ ≤ ε n` on `G n`, both `φ` and `ψ`
converge in the point-norm topology to mutually inverse `⋆`-isomorphisms `θ : A ≃⋆ₐ[ℂ] B` and
`θ.symm`, with explicit tail-error estimates on each `F n` and `G n`. -/
theorem exists_starAlgEquiv_of_approx_intertwining
    (φ : ℕ → A →⋆ₙₐ[ℂ] B) (ψ : ℕ → B →⋆ₙₐ[ℂ] A)
    (F : ℕ → Finset A) (G : ℕ → Finset B)
    (hF_mono : Monotone F) (hG_mono : Monotone G)
    (hφG : ∀ n, ∀ a ∈ F n, φ n a ∈ G n)
    (hψF : ∀ n, ∀ b ∈ G n, ψ n b ∈ F (n + 1))
    (hF_dense : Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (F n : Set A)) : Set A))
    (hG_dense : Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (G n : Set B)) : Set B))
    {δ ε : ℕ → ℝ} (hδ : Summable δ) (hε : Summable ε)
    (hψφ : ∀ n, ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ δ n)
    (hφψ : ∀ n, ∀ b ∈ G n, ‖φ (n + 1) (ψ n b) - b‖ ≤ ε n) :
    ∃ θ : A ≃⋆ₐ[ℂ] B,
      Tendsto φ atTop (𝓝 θ.toNonUnitalStarAlgHom) ∧
      Tendsto ψ atTop (𝓝 θ.symm.toNonUnitalStarAlgHom) ∧
      (∀ n, ∀ a ∈ F n, ‖θ a - φ n a‖ ≤ ∑' m, (δ (m + n) + ε (m + n))) ∧
      (∀ n, ∀ b ∈ G n, ‖θ.symm b - ψ n b‖ ≤ ∑' m, (ε (m + n) + δ (m + n + 1))) := by
  obtain ⟨φ_lim, hφ_lim, hφ_tail⟩ := exists_tendsto_and_tsum_le_of_step φ F hF_mono hF_dense
    (hδ.add hε) fun k a ha ↦ approx_intertwining_step_le (hψφ k a ha) (hφψ k (φ k a) (hφG k a ha))
  obtain ⟨ψ_lim, hψ_lim, hψ_tail⟩ := exists_tendsto_and_tsum_le_of_step ψ G hG_mono hG_dense
    (hε.add ((summable_nat_add_iff 1).mpr hδ)) fun k b hb ↦
      approx_intertwining_step_le (hφψ k b hb) (hψφ (k + 1) (ψ k b) (hψF k b hb))
  have hcomp_A : ψ_lim.comp φ_lim = .id ℂ A :=
    comp_eq_id_of_tendsto_intertwining hφ_lim hψ_lim F hF_mono hF_dense hδ.tendsto_atTop_zero hψφ
  have hcomp_B : φ_lim.comp ψ_lim = .id ℂ B :=
    comp_eq_id_of_tendsto_intertwining hψ_lim ((tendsto_add_atTop_iff_nat 1).mpr hφ_lim)
      G hG_mono hG_dense hε.tendsto_atTop_zero hφψ
  exact ⟨StarAlgEquiv.ofNonUnitalStarAlgHom φ_lim ψ_lim hcomp_A hcomp_B,
    hφ_lim, hψ_lim, hφ_tail, hψ_tail⟩

end StationaryIntertwining

section ElliottIntertwining

/-- Two-sided form of Elliott's approximate intertwining theorem for separable unital C⋆-algebras:
if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A` are mutually inverse up to target-unitary approximate
unitary equivalence, then there is a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` with `θ ≈ᵤ φ` and
`θ.symm ≈ᵤ ψ`. -/
theorem exists_starAlgEquiv_approximatelyUnitarilyEquivalent
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B,
      ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ ∧
      ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  classical
  -- Step 1: Promote `φ` and `ψ` to unital homomorphisms so unitary postcomposition applies.
  obtain ⟨hφ1, hψ1⟩ := ApproximatelyUnitarilyEquivalent.map_one_of_comp_id hψφ hφψ
  let φ₀ : A →⋆ₐ[ℂ] B := φ.toStarAlgHom hφ1
  let ψ₀ : B →⋆ₐ[ℂ] A := ψ.toStarAlgHom hψ1
  let conjB (u : unitary B) : A →⋆ₙₐ[ℂ] B :=
    (Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ
  let conjA (v : unitary A) : B →⋆ₙₐ[ℂ] A :=
    (Unitary.conjStarAlgAut ℂ A v).toNonUnitalStarAlgHom.comp ψ
  have hconjB_equiv (u : unitary B) : ApproximatelyUnitarilyEquivalent (conjB u) φ :=
    (ApproximatelyUnitarilyEquivalent.of_unitary u fun _ ↦ rfl).symm
  have hconjA_equiv (v : unitary A) : ApproximatelyUnitarilyEquivalent (conjA v) ψ :=
    (ApproximatelyUnitarilyEquivalent.of_unitary v fun _ ↦ rfl).symm
  -- Step 2: Single-step unitary selection on finite sets in `A` and `B`.
  have hexistsV (u : unitary B) (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
      ∃ v : unitary A, ∀ a ∈ F, ‖conjA v (conjB u a) - a‖ ≤ ε := by
    have hrel : ApproximatelyUnitarilyEquivalent (ψ.comp (conjB u)) (.id ℂ A) := by
      have hp := (hconjB_equiv u).postcomp ψ₀
      rw [ψ.toNonUnitalStarAlgHom_toStarAlgHom hψ1] at hp
      exact hp.trans hψφ
    obtain ⟨v, hv⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp hrel F ε hε
    exact ⟨v, fun a ha ↦ (hv a ha).le⟩
  have hexistsU (v : unitary A) (G : Finset B) (ε : ℝ) (hε : 0 < ε) :
      ∃ u : unitary B, ∀ b ∈ G, ‖conjB u (conjA v b) - b‖ ≤ ε := by
    have hrel : ApproximatelyUnitarilyEquivalent (φ.comp (conjA v)) (.id ℂ B) := by
      have hp := (hconjA_equiv v).postcomp φ₀
      rw [φ.toNonUnitalStarAlgHom_toStarAlgHom hφ1] at hp
      exact hp.trans hφψ
    obtain ⟨u, hu⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp hrel G ε hε
    exact ⟨u, fun b hb ↦ (hu b hb).le⟩
  let chooseV (u : unitary B) (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
      {v : unitary A // ∀ a ∈ F, ‖conjA v (conjB u a) - a‖ ≤ ε} :=
    Classical.indefiniteDescription _ (hexistsV u F ε hε)
  let chooseU (v : unitary A) (G : Finset B) (ε : ℝ) (hε : 0 < ε) :
      {u : unitary B // ∀ b ∈ G, ‖conjB u (conjA v b) - b‖ ≤ ε} :=
    Classical.indefiniteDescription _ (hexistsU v G ε hε)
  -- Step 3: Back-and-forth recursion alternating unitaries and countable dense sequences.
  let dA : ℕ → A := TopologicalSpace.denseSeq A
  let dB : ℕ → B := TopologicalSpace.denseSeq B
  let step : ℕ → unitary B × unitary A × Finset A × Finset B :=
    Nat.rec
      (let u₀ : unitary B := 1
       let F₀ : Finset A := {dA 0}
       let G₀ : Finset B := F₀.image (conjB u₀) ∪ {dB 0}
       let v₀ : unitary A := (chooseV u₀ F₀ (((1 : ℝ) / 2) ^ 0) (by positivity)).1
       (u₀, v₀, F₀, G₀))
      (fun n st ↦
       let F' : Finset A := st.2.2.1 ∪ st.2.2.2.image (conjA st.2.1) ∪ {dA (n + 1)}
       let u' : unitary B := (chooseU st.2.1 st.2.2.2 (((1 : ℝ) / 2) ^ n) (by positivity)).1
       let G' : Finset B := st.2.2.2 ∪ F'.image (conjB u') ∪ {dB (n + 1)}
       let v' : unitary A := (chooseV u' F' (((1 : ℝ) / 2) ^ (n + 1)) (by positivity)).1
       (u', v', F', G'))
  let φSeq (n : ℕ) : A →⋆ₙₐ[ℂ] B := conjB (step n).1
  let ψSeq (n : ℕ) : B →⋆ₙₐ[ℂ] A := conjA (step n).2.1
  let F (n : ℕ) : Finset A := (step n).2.2.1
  let G (n : ℕ) : Finset B := (step n).2.2.2
  -- Step 4: Verify monotonicity, propagation, density, and geometric error bounds, then pass to
  -- the point-norm limit via `exists_starAlgEquiv_of_approx_intertwining`.
  have hF_mono : Monotone F := monotone_nat_of_le_succ fun n ↦
    Finset.subset_union_left.trans Finset.subset_union_left
  have hG_mono : Monotone G := monotone_nat_of_le_succ fun n ↦
    Finset.subset_union_left.trans Finset.subset_union_left
  have hφG (n : ℕ) (a : A) (ha : a ∈ F n) : φSeq n a ∈ G n := by
    cases n with
    | zero =>
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
    | succ n =>
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
  have hψF (n : ℕ) (b : B) (hb : b ∈ G n) : ψSeq n b ∈ F (n + 1) :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  have hdA_mem (n : ℕ) : dA n ∈ F n := by
    cases n with
    | zero => exact Finset.mem_singleton_self _
    | succ n => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hdB_mem (n : ℕ) : dB n ∈ G n := by
    cases n with
    | zero => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    | succ n => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hF_dense : Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (F n : Set A)) : Set A) := by
    refine (TopologicalSpace.denseRange_denseSeq A).mono ?_
    refine Set.Subset.trans ?_ (NonUnitalStarAlgebra.subset_adjoin ℂ _)
    rintro _ ⟨n, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, hdA_mem n⟩
  have hG_dense : Dense (NonUnitalStarAlgebra.adjoin ℂ (⋃ n, (G n : Set B)) : Set B) := by
    refine (TopologicalSpace.denseRange_denseSeq B).mono ?_
    refine Set.Subset.trans ?_ (NonUnitalStarAlgebra.subset_adjoin ℂ _)
    rintro _ ⟨n, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, hdB_mem n⟩
  have herr_A (n : ℕ) (a : A) (ha : a ∈ F n) : ‖ψSeq n (φSeq n a) - a‖ ≤ ((1 : ℝ) / 2) ^ n := by
    cases n with
    | zero => exact (chooseV _ _ _ (by positivity)).2 a ha
    | succ n => exact (chooseV _ _ _ (by positivity)).2 a ha
  have herr_B (n : ℕ) (b : B) (hb : b ∈ G n) :
      ‖φSeq (n + 1) (ψSeq n b) - b‖ ≤ ((1 : ℝ) / 2) ^ n :=
    (chooseU _ _ _ (by positivity)).2 b hb
  obtain ⟨θ, hφ_lim, hψ_lim, -, -⟩ := exists_starAlgEquiv_of_approx_intertwining
    φSeq ψSeq F G hF_mono hG_mono hφG hψF hF_dense hG_dense
    summable_geometric_two summable_geometric_two herr_A herr_B
  exact ⟨θ, .of_tendsto_left hφ_lim (Eventually.of_forall fun n ↦ hconjB_equiv (step n).1),
    .of_tendsto_left hψ_lim (Eventually.of_forall fun n ↦ hconjA_equiv (step n).2.1)⟩

/-- Elliott's approximate intertwining theorem (Rørdam, *Classification of Nuclear C\*-Algebras*,
§2.3; the isomorphism conclusion is Kirchberg–Phillips, *Embedding of exact C\*-algebras in the
Cuntz algebra $\mathcal{O}_2$*, Lemma 0.6): if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A` are
`⋆`-homomorphisms between separable unital C⋆-algebras with `ψ ∘ φ` approximately unitarily
equivalent to the identity of `A` and `φ ∘ ψ` approximately unitarily equivalent to the identity
of `B`, then there is a `⋆`-isomorphism `A ≃⋆ₐ[ℂ] B` approximately unitarily equivalent to `φ`.
The two hypotheses force `φ` and `ψ` to be unital. -/
theorem elliott_intertwining {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ :=
  let ⟨θ, hθ, _⟩ := exists_starAlgEquiv_approximatelyUnitarilyEquivalent φ ψ hψφ hφψ
  ⟨θ, hθ⟩

end ElliottIntertwining

end TauCeti
