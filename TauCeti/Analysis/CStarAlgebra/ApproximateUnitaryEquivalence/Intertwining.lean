/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Unital
public import TauCeti.Analysis.CStarAlgebra.Hom

/-!
# Elliott's approximate intertwining between C⋆-algebras

Two sequences of `⋆`-homomorphisms `φ : ℕ → A →⋆ₙₐ[ℂ] B` and `ψ : ℕ → B →⋆ₙₐ[ℂ] A` between
C⋆-algebras that map monotone dense-union families `F : ℕ → Set A` and `G : ℕ → Set B` forward
(`φ n '' F n ⊆ G n`, `ψ n '' G n ⊆ F (n + 1)`) and satisfy summable approximate-inverse bounds
`‖ψ n (φ n a) - a‖ ≤ ε n` on `F n` and `‖φ (n + 1) (ψ n b) - b‖ ≤ δ n` on `G n` converge
pointwise to mutually inverse `⋆`-isomorphisms `θ : A ≃⋆ₐ[ℂ] B` and `θ.symm`, with explicit
tail-error bounds (`TauCeti.exists_starAlgEquiv_of_approx_intertwining`).

For separable unital C⋆-algebras `A` and `B`, if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A` satisfy
`ψ.comp φ ≈ᵤ id` and `φ.comp ψ ≈ᵤ id` via target unitaries, both maps are forced to be unital and
a back-and-forth conjugation along countable dense sequences constructs an approximate intertwining
of unitary conjugates of `φ` and `ψ`. Passing to the limit yields Elliott's intertwining theorem
(`TauCeti.elliott_intertwining`): there exists a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` approximately
unitarily equivalent to `φ` (and with `θ.symm` approximately unitarily equivalent to `ψ` via
`ApproximatelyUnitarilyEquivalent.symm_toNonUnitalStarAlgHom_of_comp_id`).

## Main results

* `TauCeti.exists_starAlgEquiv_of_approx_intertwining`: limit `⋆`-isomorphism and tail-error
  bounds from a two-sided approximate intertwining between possibly non-unital C⋆-algebras.
* `TauCeti.elliott_intertwining`: two-sided approximate unitary inverses between separable unital
  C⋆-algebras produce a `⋆`-isomorphism `A ≃⋆ₐ[ℂ] B` approximately unitarily equivalent to `φ`.

## References

* E. Kirchberg and N. C. Phillips, *Embedding of exact C*-algebras in the Cuntz algebra O₂*,
  J. reine angew. Math. 525 (2000), 17–53, Lemma 0.6.
* M. Rørdam, *Classification of Nuclear, Simple C*-Algebras*, Encyclopaedia Math. Sci. 126,
  Springer, 2002, §2.3, Corollary 2.3.4.
-/

public section

open Filter Set Topology
open scoped CStarAlgebra

namespace TauCeti

/-- **Two-algebra approximate intertwining.** Given sequences of `⋆`-homomorphisms
`φ : ℕ → M₁` and `ψ : ℕ → M₂` between (possibly non-unital) C⋆-algebras `A` and `B` (in any
morphism classes, unital or not) and monotone families `F : ℕ → Set A`, `G : ℕ → Set B` with dense
unions such that `φ n` maps `F n` into `G n`, `ψ n` maps `G n` into `F (n + 1)`, and
`‖ψ n (φ n a) - a‖ ≤ ε n` on `F n` and `‖φ (n + 1) (ψ n b) - b‖ ≤ δ n` on `G n` for summable
`ε, δ`, the sequences `φ n` and `ψ n` converge pointwise to a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` and
its inverse `θ.symm`, with explicit tail-error bounds on each `F n` and `G n`. -/
theorem exists_starAlgEquiv_of_approx_intertwining {A B M₁ M₂ : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [FunLike M₁ A B] [NonUnitalAlgHomClass M₁ ℂ A B] [StarHomClass M₁ A B]
    [FunLike M₂ B A] [NonUnitalAlgHomClass M₂ ℂ B A] [StarHomClass M₂ B A]
    (φ : ℕ → M₁) (ψ : ℕ → M₂)
    {F : ℕ → Set A} {G : ℕ → Set B}
    (hF_mono : Monotone F) (hG_mono : Monotone G)
    (hF_dense : Dense (⋃ n, F n)) (hG_dense : Dense (⋃ n, G n))
    (hφF : ∀ n, MapsTo (φ n) (F n) (G n))
    (hψG : ∀ n, MapsTo (ψ n) (G n) (F (n + 1)))
    {ε δ : ℕ → ℝ} (hε : Summable ε) (hδ : Summable δ)
    (hψφ : ∀ n, ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ ε n)
    (hφψ : ∀ n, ∀ b ∈ G n, ‖φ (n + 1) (ψ n b) - b‖ ≤ δ n) :
    ∃ θ : A ≃⋆ₐ[ℂ] B,
      (∀ a, Tendsto (fun n ↦ φ n a) atTop (𝓝 (θ a))) ∧
      (∀ b, Tendsto (fun n ↦ ψ n b) atTop (𝓝 (θ.symm b))) ∧
      (∀ n, ∀ a ∈ F n, ‖θ a - φ n a‖ ≤ ∑' m, (ε (n + m) + δ (n + m))) ∧
      (∀ n, ∀ b ∈ G n, ‖θ.symm b - ψ n b‖ ≤ ∑' m, (δ (n + m) + ε (n + m + 1))) := by
  have hφ_step : ∀ n, ∀ a ∈ F n, ‖φ (n + 1) a - φ n a‖ ≤ ε n + δ n := by
    intro n a ha
    calc
      ‖φ (n + 1) a - φ n a‖
          ≤ ‖φ (n + 1) a - φ (n + 1) (ψ n (φ n a))‖ +
              ‖φ (n + 1) (ψ n (φ n a)) - φ n a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε n + δ n := by
        refine add_le_add ?_ (hφψ n (φ n a) (hφF n ha))
        have hcontr := NonUnitalStarAlgHom.norm_apply_le (φ (n + 1)) (a - ψ n (φ n a))
        rw [map_sub, norm_sub_rev a] at hcontr
        exact hcontr.trans (hψφ n a ha)
  have hψ_step : ∀ n, ∀ b ∈ G n, ‖ψ (n + 1) b - ψ n b‖ ≤ δ n + ε (n + 1) := by
    intro n b hb
    calc
      ‖ψ (n + 1) b - ψ n b‖
          ≤ ‖ψ (n + 1) b - ψ (n + 1) (φ (n + 1) (ψ n b))‖ +
              ‖ψ (n + 1) (φ (n + 1) (ψ n b)) - ψ n b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ n + ε (n + 1) := by
        refine add_le_add ?_ (hψφ (n + 1) (ψ n b) (hψG n hb))
        have hcontr := NonUnitalStarAlgHom.norm_apply_le (ψ (n + 1)) (b - φ (n + 1) (ψ n b))
        rw [map_sub, norm_sub_rev b] at hcontr
        exact hcontr.trans (hφψ n b hb)
  obtain ⟨Φ, hΦ_lim, hΦ_tail⟩ := NonUnitalStarAlgHom.exists_tendsto_of_norm_succ_sub_le φ
    hF_mono hF_dense (hε.add hδ) hφ_step
  have hε_shift : Summable fun n ↦ ε (n + 1) := hε.comp_injective Nat.succ_injective
  obtain ⟨Ψ, hΨ_lim, hΨ_tail⟩ := NonUnitalStarAlgHom.exists_tendsto_of_norm_succ_sub_le ψ
    hG_mono hG_dense (hδ.add hε_shift) hψ_step
  have hΨΦ : Ψ.comp Φ = NonUnitalStarAlgHom.id ℂ A := by
    ext a
    refine (isClosed_eq (map_continuous (Ψ.comp Φ)) continuous_id).closure_subset_iff.mpr ?_
      (hF_dense a)
    rintro x hx
    rcases mem_iUnion.mp hx with ⟨N, hxN⟩
    suffices h0 : ‖Ψ (Φ x) - x‖ ≤ 0 from sub_eq_zero.mp (norm_le_zero_iff.mp h0)
    have ht1 : Tendsto (fun n ↦ ‖φ n x - Φ x‖) atTop (𝓝 0) := by
      simpa using ((hΦ_lim x).sub_const (Φ x)).norm
    have ht2 : Tendsto (fun n ↦ ∑' m, (δ (n + m) + ε (n + m + 1))) atTop (𝓝 0) := by
      have ht2' := _root_.tendsto_sum_nat_add (fun k ↦ δ k + ε (k + 1))
      simpa only [Nat.add_comm] using ht2'
    have hmaj : Tendsto
        (fun n ↦ ‖φ n x - Φ x‖ + (∑' m, (δ (n + m) + ε (n + m + 1))) + ε n) atTop (𝓝 0) := by
      simpa using (ht1.add ht2).add hε.tendsto_atTop_zero
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hmaj ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hxn : x ∈ F n := hF_mono hn hxN
    have hφxn : φ n x ∈ G n := hφF n hxn
    calc
      ‖Ψ (Φ x) - x‖
          ≤ ‖Ψ (Φ x) - Ψ (φ n x)‖ + ‖Ψ (φ n x) - ψ n (φ n x)‖ + ‖ψ n (φ n x) - x‖ := by
            linarith [norm_sub_le_norm_sub_add_norm_sub (Ψ (Φ x)) (Ψ (φ n x)) (ψ n (φ n x)),
              norm_sub_le_norm_sub_add_norm_sub (Ψ (Φ x)) (ψ n (φ n x)) x]
      _ ≤ ‖φ n x - Φ x‖ + (∑' m, (δ (n + m) + ε (n + m + 1))) + ε n := by
        refine add_le_add (add_le_add ?_ (hΨ_tail n (φ n x) hφxn)) (hψφ n x hxn)
        simpa only [← map_sub, norm_sub_rev] using
          NonUnitalStarAlgHom.norm_apply_le Ψ (Φ x - φ n x)
  have hΦΨ : Φ.comp Ψ = NonUnitalStarAlgHom.id ℂ B := by
    ext b
    refine (isClosed_eq (map_continuous (Φ.comp Ψ)) continuous_id).closure_subset_iff.mpr ?_
      (hG_dense b)
    rintro y hy
    rcases mem_iUnion.mp hy with ⟨N, hyN⟩
    suffices h0 : ‖Φ (Ψ y) - y‖ ≤ 0 from sub_eq_zero.mp (norm_le_zero_iff.mp h0)
    have ht1 : Tendsto (fun n ↦ ‖ψ n y - Ψ y‖) atTop (𝓝 0) := by
      simpa using ((hΨ_lim y).sub_const (Ψ y)).norm
    have ht2 : Tendsto (fun n ↦ ∑' m, (ε (n + 1 + m) + δ (n + 1 + m))) atTop (𝓝 0) := by
      have ht2' : Tendsto (fun k ↦ ∑' m, (ε (k + m) + δ (k + m))) atTop (𝓝 0) := by
        simpa only [Nat.add_comm] using _root_.tendsto_sum_nat_add (fun k ↦ ε k + δ k)
      exact (tendsto_add_atTop_iff_nat 1).mpr ht2'
    have hmaj : Tendsto
        (fun n ↦ ‖ψ n y - Ψ y‖ + (∑' m, (ε (n + 1 + m) + δ (n + 1 + m))) + δ n)
        atTop (𝓝 0) := by
      simpa using (ht1.add ht2).add hδ.tendsto_atTop_zero
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hmaj ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hyn : y ∈ G n := hG_mono hn hyN
    have hψyn : ψ n y ∈ F (n + 1) := hψG n hyn
    calc
      ‖Φ (Ψ y) - y‖
          ≤ ‖Φ (Ψ y) - Φ (ψ n y)‖ + ‖Φ (ψ n y) - φ (n + 1) (ψ n y)‖ +
              ‖φ (n + 1) (ψ n y) - y‖ := by
            linarith [norm_sub_le_norm_sub_add_norm_sub (Φ (Ψ y)) (Φ (ψ n y))
                (φ (n + 1) (ψ n y)),
              norm_sub_le_norm_sub_add_norm_sub (Φ (Ψ y)) (φ (n + 1) (ψ n y)) y]
      _ ≤ ‖ψ n y - Ψ y‖ + (∑' m, (ε (n + 1 + m) + δ (n + 1 + m))) + δ n := by
        refine add_le_add (add_le_add ?_ (hΦ_tail (n + 1) (ψ n y) hψyn)) (hφψ n y hyn)
        simpa only [← map_sub, norm_sub_rev] using
          NonUnitalStarAlgHom.norm_apply_le Φ (Ψ y - ψ n y)
  exact ⟨StarAlgEquiv.ofNonUnitalStarAlgHom Φ Ψ hΨΦ hΦΨ, hΦ_lim, hΨ_lim, hΦ_tail, hΨ_tail⟩

/-- **Elliott's approximate intertwining** (Kirchberg–Phillips, Lemma 0.6; Rørdam, Corollary
2.3.4): if `A` and `B` are separable unital C⋆-algebras and `φ : A →⋆ₙₐ[ℂ] B`,
`ψ : B →⋆ₙₐ[ℂ] A` satisfy `ψ.comp φ ≈ᵤ .id ℂ A` and `φ.comp ψ ≈ᵤ .id ℂ B` via target unitaries,
then there is a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B` approximately unitarily equivalent to `φ`. -/
theorem elliott_intertwining {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ := by
  classical
  have hψ1 : ψ 1 = 1 := hψφ.left_map_one_eq_one_of_comp_id
  have hφ1 : φ 1 = 1 := hφψ.left_map_one_eq_one_of_comp_id
  let conjB (v : unitary B) : A →⋆ₙₐ[ℂ] B :=
    (Unitary.conjStarAlgAut ℂ B v).toNonUnitalStarAlgHom.comp φ
  let conjA (u : unitary A) : B →⋆ₙₐ[ℂ] A :=
    (Unitary.conjStarAlgAut ℂ A u).toNonUnitalStarAlgHom.comp ψ
  let ε : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 1)
  have hε_pos (n : ℕ) : 0 < ε n := by positivity
  have hε_sum : Summable ε :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num)).comp_injective Nat.succ_injective
  have hA (n : ℕ) (S : Finset A) (v : unitary B) :
      ∃ u : unitary A, ∀ a ∈ S, ‖conjA u (conjB v a) - a‖ < ε n := by
    have heqv := (ApproximatelyUnitarilyEquivalent.comp_conjStarAlgAut_comp φ hψ1 v).trans hψφ
    rw [approximatelyUnitarilyEquivalent_def] at heqv
    exact heqv S (ε n) (hε_pos n)
  have hB (n : ℕ) (T : Finset B) (u : unitary A) :
      ∃ v : unitary B, ∀ b ∈ T, ‖conjB v (conjA u b) - b‖ < ε n := by
    have heqv := (ApproximatelyUnitarilyEquivalent.comp_conjStarAlgAut_comp ψ hφ1 u).trans hφψ
    rw [approximatelyUnitarilyEquivalent_def] at heqv
    exact heqv T (ε n) (hε_pos n)
  let dA := TopologicalSpace.denseSeq A
  let dB := TopologicalSpace.denseSeq B
  let step : ℕ → Finset A × Finset B × unitary B := fun n ↦
    Nat.rec ({dA 0}, ∅, 1)
      (fun k s ↦
        let uk := (hA k s.1 s.2.2).choose
        let Gk : Finset B := s.2.1 ∪ s.1.image (conjB s.2.2) ∪ {dB k}
        let vk1 := (hB k Gk uk).choose
        let Fk1 : Finset A := s.1 ∪ Gk.image (conjA uk) ∪ {dA (k + 1)}
        (Fk1, Gk, vk1)) n
  let F (n : ℕ) : Finset A := (step n).1
  let V (n : ℕ) : unitary B := (step n).2.2
  let U (n : ℕ) : unitary A := (hA n (F n) (V n)).choose
  let G (n : ℕ) : Finset B := (step n).2.1 ∪ (F n).image (conjB (V n)) ∪ {dB n}
  have hF_succ (n : ℕ) : F (n + 1) = F n ∪ (G n).image (conjA (U n)) ∪ {dA (n + 1)} := rfl
  have hG_prev (n : ℕ) : (step (n + 1)).2.1 = G n := rfl
  have hV_succ (n : ℕ) : V (n + 1) = (hB n (G n) (U n)).choose := rfl
  have hF_mono : Monotone fun n ↦ (F n : Set A) :=
    monotone_nat_of_le_succ fun n ↦ Finset.coe_subset.mpr <| by
      rw [hF_succ]
      exact Finset.subset_union_left.trans Finset.subset_union_left
  have hG_mono : Monotone fun n ↦ (G n : Set B) :=
    monotone_nat_of_le_succ fun n ↦ Finset.coe_subset.mpr <| by
      dsimp only [G]
      rw [hG_prev]
      exact Finset.subset_union_left.trans Finset.subset_union_left
  have hF_dense : Dense (⋃ n, (F n : Set A)) := by
    refine (TopologicalSpace.denseRange_denseSeq A).mono ?_
    rintro _ ⟨n, rfl⟩
    refine mem_iUnion.mpr ⟨n, ?_⟩
    cases n with
    | zero => exact Finset.mem_singleton_self (dA 0)
    | succ k =>
      rw [Finset.mem_coe, hF_succ]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hG_dense : Dense (⋃ n, (G n : Set B)) := by
    refine (TopologicalSpace.denseRange_denseSeq B).mono ?_
    rintro _ ⟨n, rfl⟩
    exact mem_iUnion.mpr ⟨n, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  have hφF (n : ℕ) : MapsTo (conjB (V n)) (F n : Set A) (G n : Set B) := by
    intro a ha
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
  have hψG (n : ℕ) : MapsTo (conjA (U n)) (G n : Set B) (F (n + 1) : Set A) := by
    intro b hb
    rw [Finset.mem_coe, hF_succ]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  have hU_spec (n : ℕ) : ∀ a ∈ (F n : Set A), ‖conjA (U n) (conjB (V n) a) - a‖ ≤ ε n :=
    fun a ha ↦ ((hA n (F n) (V n)).choose_spec a ha).le
  have hV_spec (n : ℕ) : ∀ b ∈ (G n : Set B), ‖conjB (V (n + 1)) (conjA (U n) b) - b‖ ≤ ε n := by
    intro b hb
    rw [hV_succ]
    exact ((hB n (G n) (U n)).choose_spec b hb).le
  obtain ⟨θ, hθ_lim, _, _, _⟩ := exists_starAlgEquiv_of_approx_intertwining
    (fun n ↦ conjB (V n)) (fun n ↦ conjA (U n))
    hF_mono hG_mono hF_dense hG_dense hφF hψG hε_sum hε_sum hU_spec hV_spec
  exact ⟨θ, (ApproximatelyUnitarilyEquivalent.of_tendsto V hθ_lim).symm⟩

end TauCeti
