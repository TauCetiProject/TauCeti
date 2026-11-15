/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import TauCeti.Analysis.Normed.Ring.Idempotent
public import TauCeti.Topology.Algebra.Star.Hom
public import TauCeti.Topology.UniformSpace.Equicontinuity

/-!
# Elliott's approximate intertwining of C⋆-algebras

Two separable unital C⋆-algebras `A` and `B` equipped with `⋆`-homomorphisms `φ : A →⋆ₙₐ[ℂ] B` and
`ψ : B →⋆ₙₐ[ℂ] A` whose composites `ψ.comp φ` and `φ.comp ψ` are approximately unitarily equivalent
to the respective identities are `⋆`-isomorphic via an isomorphism `θ : A ≃⋆ₐ[ℂ] B` that is itself
approximately unitarily equivalent to `φ` (with `θ.symm` simultaneously approximately unitarily
equivalent to `ψ`).

The proof factors into three reusable layers of strictly increasing specialization:

1. **Pointwise Cauchy extension and two-algebra analytical approximate intertwining** for general
   (possibly nonunital, possibly nonseparable) C⋆-algebras:
   * `NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq_on_dense`: contractivity makes any family of
     `⋆`-homomorphisms `ι → A →⋆ₙₐ[ℂ] B` equicontinuous, so Cauchyness on a dense subset propagates
     to all of `A` and yields a pointwise limit `A →⋆ₙₐ[ℂ] B`.
   * `TauCeti.exists_starAlgEquiv_of_approxIntertwining`: given sequences `φ : ℕ → A →⋆ₙₐ[ℂ] B`
     and `ψ : ℕ → B →⋆ₙₐ[ℂ] A` together with increasing exhaustions `F : ℕ → Set A` and
     `G : ℕ → Set B` having dense unions, if `φ n` maps `F n` into `G n`, `ψ n` maps `G n` into
     `F (n + 1)`, and the back-and-forth defects `‖ψ n (φ n a) - a‖ ≤ ε n` (`a ∈ F n`) and
     `‖φ (n + 1) (ψ n b) - b‖ ≤ δ n` (`b ∈ G n`) are summable, then `(φ n)` and `(ψ n)` converge
     pointwise to mutually inverse `⋆`-isomorphisms `θ : A ≃⋆ₐ[ℂ] B` and `θ.symm` satisfying
     explicit tail-sum error bounds on each `F n` and `G n`.

2. **Automatic unitality** for maps into unital C⋆-algebras:
   * `TauCeti.ApproximatelyUnitarilyEquivalent.map_one_eq_one_iff`: approximate unitary equivalence
     between maps `φ, ψ : A →⋆ₙₐ[ℂ] B` of unital C⋆-algebras preserves the condition `φ 1 = 1`,
     because unitary conjugates of `φ 1` are idempotents and `1` sits at norm distance at least `1`
     from every other idempotent (`IsIdempotentElem.eq_one_of_norm_sub_one_lt_one`).
   * `TauCeti.ApproximatelyUnitarilyEquivalent.left_map_one_eq_one_of_comp_id`: the single one-sided
     relation `ApproximatelyUnitarilyEquivalent (ψ.comp φ) (.id ℂ A)` already forces `ψ 1 = 1`, via
     `ψ 1 = ψ (φ 1) * ψ 1 = ψ (φ 1 * 1) = ψ (φ 1) = 1`; the symmetric hypothesis forces `φ 1 = 1`.

3. **Inductive unitary selection (`TauCeti.elliott_intertwining`) and unitary-sequence
   intertwining**:
   Once `φ` and `ψ` are known to be unital, `ApproximatelyUnitarilyEquivalent.postcomp` preserves
   approximate unitary equivalence after postcomposing with `ψ` or `φ`. Alternating unitary choices
   with tolerances `(1 / 2) ^ n` along countable dense sequences of `A` and `B` feeds into
   `exists_starAlgEquiv_of_approxIntertwining`, and `ApproximatelyUnitarilyEquivalent.of_tendsto`
   recovers approximate unitary equivalence between `θ` and `φ` (and between `θ.symm` and `ψ`).
   For a sequence of inner automorphisms `Ad(u n)` on a single C⋆-algebra,
   `Unitary.norm_conjStarAlgAut_sub_le`, `Unitary.exists_tendsto_of_summable_norm_sub`, and
   `TauCeti.exists_unitary_tendsto_and_approxIntertwining` show that summable unitary increments
   `‖u (n + 1) - u n‖` control the intertwining Cauchy steps and identify the intertwining limit
   isomorphism with `Ad(lim u_n)`.

## References

* G. A. Elliott, *On the classification of C⋆-algebras of real rank zero*, J. Reine Angew. Math.
  **443** (1993), 179–219, Theorem 2.1.
* E. Kirchberg and N. C. Phillips, *Embedding of exact C⋆-algebras in the Cuntz algebra `𝒪₂`*,
  J. Reine Angew. Math. **525** (2000), 17–53, Lemma 0.6.
* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Encyclopaedia Math. Sci. **126**,
  Springer, 2002, Proposition 2.3.4 and Corollary 2.3.4.
-/

public section

open Filter Set Topology
open scoped CStarAlgebra

/-! ### Pointwise Cauchy extension for `⋆`-homomorphisms -/

namespace NonUnitalStarAlgHom

/-- Every family of `⋆`-homomorphisms between nonunital C⋆-algebras is uniformly 1-Lipschitz, hence
equicontinuous; if it is pointwise Cauchy on a dense subset `s ⊆ A` along a nonempty directed
preorder, it converges pointwise everywhere to a bundled `A →⋆ₙₐ[ℂ] B`. -/
theorem exists_tendsto_of_cauchySeq_on_dense {ι A B : Type*} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : ι → A →⋆ₙₐ[ℂ] B) {s : Set A} (hs : Dense s)
    (hc : ∀ a ∈ s, CauchySeq fun i ↦ φ i a) :
    ∃ Φ : A →⋆ₙₐ[ℂ] B, ∀ a, Tendsto (fun i ↦ φ i a) atTop (𝓝 (Φ a)) := by
  have he : Equicontinuous fun i a ↦ φ i a := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro a b i
    simpa only [id_eq, dist_eq_norm, ← map_sub] using norm_apply_le (φ i) (a - b)
  have hc_all : ∀ a, CauchySeq fun i ↦ φ i a := fun a ↦
    (he.isClosed_setOfPred_cauchySeq.closure_subset_iff.mpr hc) (hs a)
  choose f hf using fun a ↦ cauchySeq_tendsto_of_complete (hc_all a)
  exact ⟨ofTendsto f φ (tendsto_pi_nhds.mpr hf), fun a ↦ by simpa only [ofTendsto_apply] using hf a⟩

end NonUnitalStarAlgHom

/-! ### Unitality forcing under approximate unitary equivalence -/

namespace TauCeti.ApproximatelyUnitarilyEquivalent

section UnitalForcing

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Approximate unitary equivalence between maps of unital C⋆-algebras preserves unitality:
if `ψ 1 = 1`, any unitary conjugate `(u : B) * φ 1 * star (u : B)` is an idempotent arbitrarily
close to `1`, hence equal to `1` by the norm-`1` isolation of `1` among idempotents. -/
theorem map_one_eq_one_iff {φ ψ : A →⋆ₙₐ[ℂ] B}
    (h : ApproximatelyUnitarilyEquivalent φ ψ) : φ 1 = 1 ↔ ψ 1 = 1 := by
  have aux {f g : A →⋆ₙₐ[ℂ] B} (hfg : ApproximatelyUnitarilyEquivalent f g) (hg : g 1 = 1) :
      f 1 = 1 := by
    rw [approximatelyUnitarilyEquivalent_def] at hfg
    obtain ⟨u, hu⟩ := hfg {1} (1 / 2) (by norm_num)
    let e := Unitary.conjStarAlgAut ℂ B u
    have hidem : IsIdempotentElem (e (f 1)) := (IsIdempotentElem.one.map f).map e
    have hlt : ‖e (f 1) - 1‖ < 1 := by
      have hu1 := hu 1 (Finset.mem_singleton_self 1)
      simpa only [e, Unitary.conjStarAlgAut_apply, hg] using hu1.trans (by norm_num)
    exact e.injective ((hidem.eq_one_of_norm_sub_one_lt_one hlt).trans (map_one e).symm)
  exact ⟨aux h.symm, aux h⟩

/-- An endomorphism of a unital C⋆-algebra that is approximately unitarily equivalent to the
identity preserves `1`. -/
theorem map_one_eq_one_of_id {α : A →⋆ₙₐ[ℂ] A}
    (h : ApproximatelyUnitarilyEquivalent α (.id ℂ A)) : α 1 = 1 :=
  h.map_one_eq_one_iff.mpr rfl

/-- If `ψ.comp φ` is approximately unitarily equivalent to `.id ℂ A`, then the outer map `ψ`
automatically preserves `1` (even without any hypothesis on `φ.comp ψ`). -/
theorem left_map_one_eq_one_of_comp_id {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (.id ℂ A)) : ψ 1 = 1 := by
  have h1 : ψ (φ 1) = 1 := hψφ.map_one_eq_one_of_id
  calc
    ψ 1 = 1 * ψ 1 := (one_mul (ψ 1)).symm
    _ = ψ (φ 1) * ψ 1 := by rw [h1]
    _ = ψ (φ 1 * 1) := (map_mul ψ (φ 1) 1).symm
    _ = ψ (φ 1) := by rw [mul_one]
    _ = 1 := h1

/-- Upgrade a nonunital `⋆`-homomorphism preserving `1` to a unital `StarAlgHom`. -/
private def toStarAlgHomOfMapOne (φ : A →⋆ₙₐ[ℂ] B) (hφ : φ 1 = 1) : A →⋆ₐ[ℂ] B where
  toFun := φ
  map_one' := hφ
  map_mul' := map_mul φ
  map_zero' := map_zero φ
  map_add' := map_add φ
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ, Algebra.algebraMap_eq_smul_one]
  map_star' := map_star φ

end UnitalForcing

end TauCeti.ApproximatelyUnitarilyEquivalent

/-! ### Analytical two-algebra approximate intertwining -/

namespace TauCeti

section AnalyticalIntertwining

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Consecutive-step Cauchy estimate on the left side of an approximate intertwining diagram:
contractivity of `φ (n + 1)` splits `φ (n + 1) a - φ n a` into `φ (n + 1) (a - ψ n (φ n a))` plus
`φ (n + 1) (ψ n (φ n a)) - φ n a`. -/
theorem norm_approxIntertwining_sub_le_left
    {φ : ℕ → A →⋆ₙₐ[ℂ] B} {ψ : ℕ → B →⋆ₙₐ[ℂ] A}
    {F : ℕ → Set A} {G : ℕ → Set B} {ε δ : ℕ → ℝ}
    (hφG : ∀ n, MapsTo (φ n) (F n) (G n))
    (hψφ : ∀ n, ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ ε n)
    (hφψ : ∀ n, ∀ b ∈ G n, ‖φ (n + 1) (ψ n b) - b‖ ≤ δ n)
    {n : ℕ} {a : A} (ha : a ∈ F n) :
    ‖φ (n + 1) a - φ n a‖ ≤ ε n + δ n := by
  have hsplit : φ (n + 1) a - φ n a =
      φ (n + 1) (a - ψ n (φ n a)) + (φ (n + 1) (ψ n (φ n a)) - φ n a) := by
    rw [map_sub]
    abel
  rw [hsplit]
  calc
    ‖φ (n + 1) (a - ψ n (φ n a)) + (φ (n + 1) (ψ n (φ n a)) - φ n a)‖
        ≤ ‖φ (n + 1) (a - ψ n (φ n a))‖ + ‖φ (n + 1) (ψ n (φ n a)) - φ n a‖ := norm_add_le _ _
    _ ≤ ‖a - ψ n (φ n a)‖ + δ n :=
      add_le_add (NonUnitalStarAlgHom.norm_apply_le (φ (n + 1)) _) (hφψ n (φ n a) (hφG n ha))
    _ = ‖ψ n (φ n a) - a‖ + δ n := by rw [norm_sub_rev]
    _ ≤ ε n + δ n := add_le_add (hψφ n a ha) le_rfl

/-- Consecutive-step Cauchy estimate on the right side of an approximate intertwining diagram. -/
theorem norm_approxIntertwining_sub_le_right
    {φ : ℕ → A →⋆ₙₐ[ℂ] B} {ψ : ℕ → B →⋆ₙₐ[ℂ] A}
    {F : ℕ → Set A} {G : ℕ → Set B} {ε δ : ℕ → ℝ}
    (hψF : ∀ n, MapsTo (ψ n) (G n) (F (n + 1)))
    (hψφ : ∀ n, ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ ε n)
    (hφψ : ∀ n, ∀ b ∈ G n, ‖φ (n + 1) (ψ n b) - b‖ ≤ δ n)
    {n : ℕ} {b : B} (hb : b ∈ G n) :
    ‖ψ (n + 1) b - ψ n b‖ ≤ δ n + ε (n + 1) := by
  have hsplit : ψ (n + 1) b - ψ n b =
      ψ (n + 1) (b - φ (n + 1) (ψ n b)) + (ψ (n + 1) (φ (n + 1) (ψ n b)) - ψ n b) := by
    rw [map_sub]
    abel
  rw [hsplit]
  calc
    ‖ψ (n + 1) (b - φ (n + 1) (ψ n b)) + (ψ (n + 1) (φ (n + 1) (ψ n b)) - ψ n b)‖
        ≤ ‖ψ (n + 1) (b - φ (n + 1) (ψ n b))‖ +
            ‖ψ (n + 1) (φ (n + 1) (ψ n b)) - ψ n b‖ := norm_add_le _ _
    _ ≤ ‖b - φ (n + 1) (ψ n b)‖ + ε (n + 1) :=
      add_le_add (NonUnitalStarAlgHom.norm_apply_le (ψ (n + 1)) _)
        (hψφ (n + 1) (ψ n b) (hψF n hb))
    _ = ‖φ (n + 1) (ψ n b) - b‖ + ε (n + 1) := by rw [norm_sub_rev]
    _ ≤ δ n + ε (n + 1) := add_le_add (hφψ n b hb) le_rfl

/-- **Two-algebra analytical approximate intertwining**: if sequences of `⋆`-homomorphisms
`φ : ℕ → A →⋆ₙₐ[ℂ] B` and `ψ : ℕ → B →⋆ₙₐ[ℂ] A` between (possibly nonunital) C⋆-algebras
approximately invert one another with summable errors `ε` and `δ` along increasing exhaustions
`F : ℕ → Set A` and `G : ℕ → Set B` having dense unions, then `(φ n)` and `(ψ n)` converge
pointwise everywhere to mutually inverse `⋆`-isomorphisms `θ : A ≃⋆ₐ[ℂ] B` and `θ.symm`, with
explicit tail-sum error bounds on every `F n` and `G n`. -/
theorem exists_starAlgEquiv_of_approxIntertwining
    (φ : ℕ → A →⋆ₙₐ[ℂ] B) (ψ : ℕ → B →⋆ₙₐ[ℂ] A)
    (F : ℕ → Set A) (G : ℕ → Set B) (ε δ : ℕ → ℝ)
    (hF_mono : Monotone F) (hG_mono : Monotone G)
    (hF_dense : Dense (⋃ n, F n)) (hG_dense : Dense (⋃ n, G n))
    (hφG : ∀ n, MapsTo (φ n) (F n) (G n))
    (hψF : ∀ n, MapsTo (ψ n) (G n) (F (n + 1)))
    (hε : Summable ε) (hδ : Summable δ)
    (hψφ : ∀ n, ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ ε n)
    (hφψ : ∀ n, ∀ b ∈ G n, ‖φ (n + 1) (ψ n b) - b‖ ≤ δ n) :
    ∃ θ : A ≃⋆ₐ[ℂ] B,
      (∀ a, Tendsto (fun n ↦ φ n a) atTop (𝓝 (θ a))) ∧
      (∀ b, Tendsto (fun n ↦ ψ n b) atTop (𝓝 (θ.symm b))) ∧
      (∀ n, ∀ a ∈ F n, ‖θ a - φ n a‖ ≤ ∑' k, (ε (n + k) + δ (n + k))) ∧
      (∀ n, ∀ b ∈ G n, ‖θ.symm b - ψ n b‖ ≤ ∑' k, (δ (n + k) + ε (n + k + 1))) := by
  -- Step 1: Cauchyness of `(φ k a)` on `⋃ n, F n` via shifted summable consecutive distances.
  have hφ_step (n k : ℕ) {a : A} (ha : a ∈ F n) :
      dist (φ (n + k) a) (φ (n + (k + 1)) a) ≤ ε (n + k) + δ (n + k) := by
    have hak : a ∈ F (n + k) := hF_mono (Nat.le_add_right n k) ha
    rw [dist_eq_norm, norm_sub_rev, ← Nat.add_assoc]
    exact norm_approxIntertwining_sub_le_left hφG hψφ hφψ hak
  have hφ_sum (n : ℕ) : Summable fun k ↦ ε (n + k) + δ (n + k) :=
    (hε.add hδ).comp_injective (add_right_injective n)
  have hφ_cau : ∀ a ∈ ⋃ n, F n, CauchySeq fun k ↦ φ k a := by
    rintro a ha
    obtain ⟨n, ha⟩ := mem_iUnion.mp ha
    have hc : CauchySeq fun k ↦ φ (k + n) a := by
      simpa only [Nat.add_comm n] using
        cauchySeq_of_dist_le_of_summable _ (fun k ↦ hφ_step n k ha) (hφ_sum n)
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
    exact ((tendsto_add_atTop_iff_nat n).mp hy).cauchySeq
  obtain ⟨Φ, hΦ⟩ := NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq_on_dense φ hF_dense hφ_cau
  -- Step 2: Cauchyness of `(ψ k b)` on `⋃ n, G n` by the symmetric shifted estimate.
  have hψ_step (n k : ℕ) {b : B} (hb : b ∈ G n) :
      dist (ψ (n + k) b) (ψ (n + (k + 1)) b) ≤ δ (n + k) + ε (n + k + 1) := by
    have hbk : b ∈ G (n + k) := hG_mono (Nat.le_add_right n k) hb
    rw [dist_eq_norm, norm_sub_rev, ← Nat.add_assoc]
    exact norm_approxIntertwining_sub_le_right hψF hψφ hφψ hbk
  have hψ_sum (n : ℕ) : Summable fun k ↦ δ (n + k) + ε (n + k + 1) :=
    (hδ.comp_injective (add_right_injective n)).add
      (hε.comp_injective (fun _ _ h ↦ Nat.add_left_cancel (Nat.succ.inj h)))
  have hψ_cau : ∀ b ∈ ⋃ n, G n, CauchySeq fun k ↦ ψ k b := by
    rintro b hb
    obtain ⟨n, hb⟩ := mem_iUnion.mp hb
    have hc : CauchySeq fun k ↦ ψ (k + n) b := by
      simpa only [Nat.add_comm n] using
        cauchySeq_of_dist_le_of_summable _ (fun k ↦ hψ_step n k hb) (hψ_sum n)
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
    exact ((tendsto_add_atTop_iff_nat n).mp hx).cauchySeq
  obtain ⟨Ψ, hΨ⟩ := NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq_on_dense ψ hG_dense hψ_cau
  -- Step 3: Tail error bounds on `F n` and `G n`.
  have hΦ_tail (n : ℕ) {a : A} (ha : a ∈ F n) :
      ‖Φ a - φ n a‖ ≤ ∑' k, (ε (n + k) + δ (n + k)) := by
    have ht : Tendsto (fun k ↦ φ (n + k) a) atTop (𝓝 (Φ a)) := by
      simpa only [Nat.add_comm n] using (tendsto_add_atTop_iff_nat n).mpr (hΦ a)
    have hd := dist_le_tsum_of_dist_le_of_tendsto₀ _ (fun k ↦ hφ_step n k ha) (hφ_sum n) ht
    simpa only [Nat.add_zero, dist_eq_norm, norm_sub_rev] using hd
  have hΨ_tail (n : ℕ) {b : B} (hb : b ∈ G n) :
      ‖Ψ b - ψ n b‖ ≤ ∑' k, (δ (n + k) + ε (n + k + 1)) := by
    have ht : Tendsto (fun k ↦ ψ (n + k) b) atTop (𝓝 (Ψ b)) := by
      simpa only [Nat.add_comm n] using (tendsto_add_atTop_iff_nat n).mpr (hΨ b)
    have hd := dist_le_tsum_of_dist_le_of_tendsto₀ _ (fun k ↦ hψ_step n k hb) (hψ_sum n) ht
    simpa only [Nat.add_zero, dist_eq_norm, norm_sub_rev] using hd
  -- Step 4: `Ψ (Φ a) = a` on `⋃ n, F n`, hence everywhere by continuity and density.
  have hΨΦ_dense : ∀ a ∈ ⋃ n, F n, Ψ (Φ a) = a := by
    rintro a ha
    obtain ⟨n₀, ha⟩ := mem_iUnion.mp ha
    -- `ψ k (φ k a)` tends both to `a` (by `hψφ`) and to `Ψ (Φ a)` (by contractivity of `ψ k`).
    have ht1 : Tendsto (fun k ↦ ψ k (φ k a)) atTop (𝓝 a) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hε.tendsto_atTop_zero
      filter_upwards [eventually_ge_atTop n₀] with k hk
      exact hψφ k a (hF_mono hk ha)
    have ht2 : Tendsto (fun k ↦ ψ k (φ k a)) atTop (𝓝 (Ψ (Φ a))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hdiff : Tendsto (fun k ↦ ‖φ k a - Φ a‖ + ‖ψ k (Φ a) - Ψ (Φ a)‖) atTop (𝓝 0) := by
        simpa only [add_zero] using
          (tendsto_iff_norm_sub_tendsto_zero.mp (hΦ a)).add
            (tendsto_iff_norm_sub_tendsto_zero.mp (hΨ (Φ a)))
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hdiff
      have hsplit : ψ k (φ k a) - Ψ (Φ a) = ψ k (φ k a - Φ a) + (ψ k (Φ a) - Ψ (Φ a)) := by
        rw [map_sub]; abel
      rw [hsplit]
      exact (norm_add_le _ _).trans
        (add_le_add (NonUnitalStarAlgHom.norm_apply_le (ψ k) _) le_rfl)
    exact tendsto_nhds_unique ht2 ht1
  have hΨΦ : Ψ.comp Φ = .id ℂ A := by
    ext a
    exact (isClosed_eq ((map_continuous Ψ).comp (map_continuous Φ)) continuous_id
      |>.closure_subset_iff.mpr hΨΦ_dense) (hF_dense a)
  -- Step 5: `Φ (Ψ b) = b` on `⋃ n, G n`, hence everywhere by continuity and density.
  have hΦΨ_dense : ∀ b ∈ ⋃ n, G n, Φ (Ψ b) = b := by
    rintro b hb
    obtain ⟨n₀, hb⟩ := mem_iUnion.mp hb
    have ht1 : Tendsto (fun k ↦ φ (k + 1) (ψ k b)) atTop (𝓝 b) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hδ.tendsto_atTop_zero
      filter_upwards [eventually_ge_atTop n₀] with k hk
      exact hφψ k b (hG_mono hk hb)
    have ht2 : Tendsto (fun k ↦ φ (k + 1) (ψ k b)) atTop (𝓝 (Φ (Ψ b))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hΦ_shift : Tendsto (fun k ↦ φ (k + 1) (Ψ b)) atTop (𝓝 (Φ (Ψ b))) :=
        (tendsto_add_atTop_iff_nat 1).mpr (hΦ (Ψ b))
      have hdiff : Tendsto (fun k ↦ ‖ψ k b - Ψ b‖ + ‖φ (k + 1) (Ψ b) - Φ (Ψ b)‖) atTop (𝓝 0) := by
        simpa only [add_zero] using
          (tendsto_iff_norm_sub_tendsto_zero.mp (hΨ b)).add
            (tendsto_iff_norm_sub_tendsto_zero.mp hΦ_shift)
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hdiff
      have hsplit : φ (k + 1) (ψ k b) - Φ (Ψ b) =
          φ (k + 1) (ψ k b - Ψ b) + (φ (k + 1) (Ψ b) - Φ (Ψ b)) := by
        rw [map_sub]; abel
      rw [hsplit]
      exact (norm_add_le _ _).trans
        (add_le_add (NonUnitalStarAlgHom.norm_apply_le (φ (k + 1)) _) le_rfl)
    exact tendsto_nhds_unique ht2 ht1
  have hΦΨ : Φ.comp Ψ = .id ℂ B := by
    ext b
    exact (isClosed_eq ((map_continuous Φ).comp (map_continuous Ψ)) continuous_id
      |>.closure_subset_iff.mpr hΦΨ_dense) (hG_dense b)
  refine ⟨StarAlgEquiv.ofNonUnitalStarAlgHom Φ Ψ hΨΦ hΦΨ, hΦ, hΨ,
    fun n a ha ↦ hΦ_tail n ha, fun n b hb ↦ hΨ_tail n hb⟩

end AnalyticalIntertwining

/-! ### Elliott's approximate intertwining for separable unital C⋆-algebras -/

section ElliottIntertwining

/-- Bundled stage data for the inductive unitary-selection construction in
`elliott_intertwining`. -/
private structure IntertwiningStep (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] where
  F : Finset A
  u : unitary B
  G : Finset B
  v : unitary A

/-- Two-sided version of **Elliott's approximate intertwining theorem**: if `φ : A →⋆ₙₐ[ℂ] B` and
`ψ : B →⋆ₙₐ[ℂ] A` between separable unital C⋆-algebras have composites `ψ.comp φ` and `φ.comp ψ`
approximately unitarily equivalent to the identities, there exists a `⋆`-isomorphism
`θ : A ≃⋆ₐ[ℂ] B` such that `θ` is approximately unitarily equivalent to `φ` and `θ.symm` is
approximately unitarily equivalent to `ψ`. -/
theorem elliott_intertwining_symm {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B,
      ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ ∧
      ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  classical
  -- Both maps automatically preserve `1`, so postcomposition with either map preserves
  -- approximate unitary equivalence.
  have hφ1 : φ 1 = 1 := hφψ.left_map_one_eq_one_of_comp_id
  have hψ1 : ψ 1 = 1 := hψφ.left_map_one_eq_one_of_comp_id
  let φᵤ : A →⋆ₐ[ℂ] B := ApproximatelyUnitarilyEquivalent.toStarAlgHomOfMapOne φ hφ1
  let ψᵤ : B →⋆ₐ[ℂ] A := ApproximatelyUnitarilyEquivalent.toStarAlgHomOfMapOne ψ hψ1
  have hφᵤ : φᵤ.toNonUnitalStarAlgHom = φ := rfl
  have hψᵤ : ψᵤ.toNonUnitalStarAlgHom = ψ := rfl
  let φc (u : unitary B) : A →⋆ₙₐ[ℂ] B :=
    (Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ
  let ψc (v : unitary A) : B →⋆ₙₐ[ℂ] A :=
    (Unitary.conjStarAlgAut ℂ A v).toNonUnitalStarAlgHom.comp ψ
  have hψφ_conj (u : unitary B) :
      ∀ (F : Finset A) (ε : ℝ), 0 < ε →
        ∃ v : unitary A, ∀ a ∈ F, ‖ψc v (φc u a) - a‖ < ε := by
    have hu : ApproximatelyUnitarilyEquivalent (φc u) φ :=
      (ApproximatelyUnitarilyEquivalent.of_unitary u fun a ↦ rfl).symm
    have hpost := hu.postcomp ψᵤ
    rw [hψᵤ] at hpost
    exact (approximatelyUnitarilyEquivalent_def _ _).mp (hpost.trans hψφ)
  have hφψ_conj (v : unitary A) :
      ∀ (G : Finset B) (ε : ℝ), 0 < ε →
        ∃ u : unitary B, ∀ b ∈ G, ‖φc u (ψc v b) - b‖ < ε := by
    have hv : ApproximatelyUnitarilyEquivalent (ψc v) ψ :=
      (ApproximatelyUnitarilyEquivalent.of_unitary v fun b ↦ rfl).symm
    have hpost := hv.postcomp φᵤ
    rw [hφᵤ] at hpost
    exact (approximatelyUnitarilyEquivalent_def _ _).mp (hpost.trans hφψ)
  let dA : ℕ → A := TopologicalSpace.denseSeq A
  let dB : ℕ → B := TopologicalSpace.denseSeq B
  let step : ℕ → IntertwiningStep A B :=
    Nat.rec
      (let F₀ : Finset A := {dA 0}
       let u₀ : unitary B := 1
       let G₀ : Finset B := insert (dB 0) (F₀.image (φc u₀))
       let v₀ : unitary A :=
         (hψφ_conj u₀ F₀ ((1 / 2 : ℝ) ^ 0) (by positivity)).choose
       ⟨F₀, u₀, G₀, v₀⟩)
      fun n s ↦
        let F' : Finset A := insert (dA (n + 1)) (s.F ∪ s.G.image (ψc s.v))
        let u' : unitary B :=
          (hφψ_conj s.v s.G ((1 / 2 : ℝ) ^ n) (by positivity)).choose
        let G' : Finset B := insert (dB (n + 1)) (s.G ∪ F'.image (φc u'))
        let v' : unitary A :=
          (hψφ_conj u' F' ((1 / 2 : ℝ) ^ (n + 1)) (by positivity)).choose
        ⟨F', u', G', v'⟩
  have hF_mono : Monotone fun n ↦ ((step n).F : Set A) :=
    monotone_nat_of_le_succ fun n ↦
      Finset.coe_subset.mpr (Finset.subset_union_left.trans (Finset.subset_insert _ _))
  have hG_mono : Monotone fun n ↦ ((step n).G : Set B) :=
    monotone_nat_of_le_succ fun n ↦
      Finset.coe_subset.mpr (Finset.subset_union_left.trans (Finset.subset_insert _ _))
  have hdA_mem (n : ℕ) : dA n ∈ (step n).F := by
    cases n with
    | zero => exact Finset.mem_singleton_self _
    | succ n => exact Finset.mem_insert_self _ _
  have hdB_mem (n : ℕ) : dB n ∈ (step n).G := by
    cases n with
    | zero => exact Finset.mem_insert_self _ _
    | succ n => exact Finset.mem_insert_self _ _
  have hF_dense : Dense (⋃ n, ((step n).F : Set A)) :=
    (TopologicalSpace.denseRange_denseSeq A).mono <|
      range_subset_iff.mpr fun n ↦ mem_iUnion.mpr ⟨n, hdA_mem n⟩
  have hG_dense : Dense (⋃ n, ((step n).G : Set B)) :=
    (TopologicalSpace.denseRange_denseSeq B).mono <|
      range_subset_iff.mpr fun n ↦ mem_iUnion.mpr ⟨n, hdB_mem n⟩
  have hφG (n : ℕ) : MapsTo (φc (step n).u) ((step n).F : Set A) ((step n).G : Set B) := by
    intro a ha
    cases n with
    | zero => exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
    | succ n =>
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
  have hψF (n : ℕ) : MapsTo (ψc (step n).v) ((step n).G : Set B) ((step (n + 1)).F : Set A) := by
    intro b hb
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  have hψφ_le (n : ℕ) : ∀ a ∈ ((step n).F : Set A),
      ‖ψc (step n).v (φc (step n).u a) - a‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro a ha
    cases n with
    | zero =>
      exact ((hψφ_conj 1 {dA 0} ((1 / 2 : ℝ) ^ 0) (by positivity)).choose_spec a ha).le
    | succ n =>
      exact ((hψφ_conj (step (n + 1)).u (step (n + 1)).F ((1 / 2 : ℝ) ^ (n + 1))
        (by positivity)).choose_spec a ha).le
  have hφψ_le (n : ℕ) : ∀ b ∈ ((step n).G : Set B),
      ‖φc (step (n + 1)).u (ψc (step n).v b) - b‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro b hb
    exact ((hφψ_conj (step n).v (step n).G ((1 / 2 : ℝ) ^ n) (by positivity)).choose_spec b hb).le
  obtain ⟨θ, hθ, hθ_symm, -, -⟩ := exists_starAlgEquiv_of_approxIntertwining
    (fun n ↦ φc (step n).u) (fun n ↦ ψc (step n).v)
    (fun n ↦ ((step n).F : Set A)) (fun n ↦ ((step n).G : Set B))
    (fun n ↦ (1 / 2 : ℝ) ^ n) (fun n ↦ (1 / 2 : ℝ) ^ n)
    hF_mono hG_mono hF_dense hG_dense hφG hψF
    summable_geometric_two summable_geometric_two hψφ_le hφψ_le
  refine ⟨θ, ?_, ?_⟩
  · exact (ApproximatelyUnitarilyEquivalent.of_tendsto (fun n ↦ (step n).u) hθ).symm
  · exact (ApproximatelyUnitarilyEquivalent.of_tendsto (fun n ↦ (step n).v) hθ_symm).symm

/-- **Elliott's approximate intertwining theorem**: if `φ : A →⋆ₙₐ[ℂ] B` and `ψ : B →⋆ₙₐ[ℂ] A`
between separable unital C⋆-algebras satisfy `ψ ∘ φ ≈ᵤ id_A` and `φ ∘ ψ ≈ᵤ id_B`, then `φ` is
approximately unitarily equivalent to a `⋆`-isomorphism `θ : A ≃⋆ₐ[ℂ] B`. -/
theorem elliott_intertwining {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] A)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ := by
  obtain ⟨θ, hθφ, -⟩ := elliott_intertwining_symm φ ψ hψφ hφψ
  exact ⟨θ, hθφ⟩

/-- Characterization of `⋆`-homomorphisms approximately unitarily equivalent to a `⋆`-isomorphism
between separable unital C⋆-algebras: such an isomorphism exists iff `φ` admits an approximate
unitary two-sided inverse `ψ : B →⋆ₙₐ[ℂ] A`. -/
theorem exists_starAlgEquiv_approximatelyUnitarilyEquivalent_iff
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (φ : A →⋆ₙₐ[ℂ] B) :
    (∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ) ↔
      ∃ ψ : B →⋆ₙₐ[ℂ] A,
        ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A) ∧
        ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B) := by
  refine ⟨?_, fun ⟨ψ, hψφ, hφψ⟩ ↦ elliott_intertwining φ ψ hψφ hφψ⟩
  rintro ⟨θ, hθφ⟩
  refine ⟨θ.symm.toNonUnitalStarAlgHom, ?_, ?_⟩
  · have hpost := hθφ.symm.postcomp θ.symm.toStarAlgHom
    have hid : θ.symm.toNonUnitalStarAlgHom.comp θ.toNonUnitalStarAlgHom = .id ℂ A := by
      ext a; exact θ.symm_apply_apply a
    rwa [StarAlgEquiv.toNonUnitalStarAlgHom_toStarAlgHom, hid] at hpost
  · have hpre := hθφ.symm.precomp θ.symm.toNonUnitalStarAlgHom
    have hid : θ.toNonUnitalStarAlgHom.comp θ.symm.toNonUnitalStarAlgHom = .id ℂ B := by
      ext b; exact θ.apply_symm_apply b
    rwa [hid] at hpre

end ElliottIntertwining

end TauCeti

/-! ### Unitary-conjugation intertwining -/

namespace Unitary

/-- Unitary conjugation `Unitary.conjStarAlgAut` is norm-preserving in any unital C⋆-ring. -/
theorem norm_conjStarAlgAut_apply (S : Type*) {A : Type*} [NormedRing A] [StarRing A]
    [CStarRing A] [SMul S A] [IsScalarTower S A A] [SMulCommClass S A A]
    (u : unitary A) (a : A) :
    ‖Unitary.conjStarAlgAut S A u a‖ = ‖a‖ := by
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]

/-- Perturbation bound for unitary conjugation in a unital C⋆-ring:
`‖u a u* - v a v*‖ ≤ 2 * ‖u - v‖ * ‖a‖`. -/
theorem norm_conjStarAlgAut_sub_le (S : Type*) {A : Type*} [NormedRing A] [StarRing A]
    [CStarRing A] [SMul S A] [IsScalarTower S A A] [SMulCommClass S A A]
    (u v : unitary A) (a : A) :
    ‖Unitary.conjStarAlgAut S A u a - Unitary.conjStarAlgAut S A v a‖ ≤
      2 * ‖(u : A) - (v : A)‖ * ‖a‖ := by
  have hdecomp : Unitary.conjStarAlgAut S A u a - Unitary.conjStarAlgAut S A v a =
      ((u : A) - (v : A)) * a * (star u : unitary A) +
        (v : A) * a * star ((u : A) - (v : A)) := by
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, sub_mul, mul_sub, star_sub]
    abel
  calc ‖Unitary.conjStarAlgAut S A u a - Unitary.conjStarAlgAut S A v a‖
    _ ≤ ‖((u : A) - (v : A)) * a * (star u : unitary A)‖ +
          ‖(v : A) * a * star ((u : A) - (v : A))‖ := hdecomp ▸ norm_add_le _ _
    _ = ‖((u : A) - (v : A)) * a‖ + ‖a * star ((u : A) - (v : A))‖ := by
          rw [CStarRing.norm_mul_coe_unitary, mul_assoc, CStarRing.norm_coe_unitary_mul]
    _ ≤ ‖(u : A) - (v : A)‖ * ‖a‖ + ‖a‖ * ‖star ((u : A) - (v : A))‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖(u : A) - (v : A)‖ * ‖a‖ := by rw [norm_star]; ring

/-- If a family of unitaries converges in `unitary A`, the associated inner automorphisms
`Unitary.conjStarAlgAut S A (u i)` converge pointwise to `Unitary.conjStarAlgAut S A u₀`. -/
theorem tendsto_conjStarAlgAut_of_tendsto (S : Type*) {ι A : Type*} [TopologicalSpace A]
    [Semiring A] [StarMul A] [ContinuousMul A] [ContinuousStar A] [SMul S A]
    [IsScalarTower S A A] [SMulCommClass S A A] {u : ι → unitary A} {u₀ : unitary A}
    {l : Filter ι} (hu : Tendsto u l (𝓝 u₀)) (a : A) :
    Tendsto (fun i ↦ Unitary.conjStarAlgAut S A (u i) a) l
      (𝓝 (Unitary.conjStarAlgAut S A u₀ a)) := by
  have hcoe : Tendsto (fun i ↦ (u i : A)) l (𝓝 (u₀ : A)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hu
  simpa only [Unitary.conjStarAlgAut_apply] using (hcoe.mul tendsto_const_nhds).mul hcoe.star

/-- A sequence of unitaries in a complete normed `⋆`-ring with continuous involution whose
successive norm differences are summable converges in `unitary A`. -/
theorem exists_tendsto_of_summable_norm_sub {A : Type*} [NormedRing A] [StarRing A]
    [ContinuousStar A] [CompleteSpace A] {u : ℕ → unitary A}
    (hsum : Summable fun n ↦ ‖(u (n + 1) : A) - (u n : A)‖) :
    ∃ u₀ : unitary A, Tendsto u atTop (𝓝 u₀) := by
  have hcauchy : CauchySeq fun n ↦ (u n : A) :=
    cauchySeq_of_dist_le_of_summable _
      (fun n ↦ by rw [dist_eq_norm, norm_sub_rev]) hsum
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hx_mem : x ∈ unitary A :=
    isClosed_unitary.mem_of_tendsto hx (Eventually.of_forall fun n ↦ (u n).2)
  exact ⟨⟨x, hx_mem⟩, tendsto_subtype_rng.mpr hx⟩

end Unitary

namespace TauCeti

/-- Specializing `exists_starAlgEquiv_of_approxIntertwining` to inner automorphisms
`φ n = Ad(u n)` and `ψ n = Ad(star (u n))` on the exhausting closed balls
`Metric.closedBall 0 (n + 1)` of a unital C⋆-algebra: when `2 * (n + 1) * ‖u (n + 1) - u n‖ ≤ δ n`
for a summable sequence `δ`, `(u n)` converges to some `u₀ : unitary A`, the intertwining limit
isomorphism `θ : A ≃⋆ₐ[ℂ] A` equals `Unitary.conjStarAlgAut ℂ A u₀`, and the tail sum of `δ`
bounds `‖Ad(u₀) a - Ad(u n) a‖` on `Metric.closedBall 0 (n + 1)`. -/
theorem exists_unitary_tendsto_and_approxIntertwining {A : Type*} [CStarAlgebra A]
    (u : ℕ → unitary A) (δ : ℕ → ℝ) (hδ : Summable δ)
    (hu : ∀ n : ℕ, 2 * ((n : ℝ) + 1) * ‖(u (n + 1) : A) - (u n : A)‖ ≤ δ n) :
    ∃ u₀ : unitary A, Tendsto u atTop (𝓝 u₀) ∧
      ∃ θ : A ≃⋆ₐ[ℂ] A,
        θ = Unitary.conjStarAlgAut ℂ A u₀ ∧
        (∀ a, Tendsto (fun n ↦ Unitary.conjStarAlgAut ℂ A (u n) a) atTop (𝓝 (θ a))) ∧
        (∀ n : ℕ, ∀ a ∈ Metric.closedBall (0 : A) ((n : ℝ) + 1),
          ‖θ a - Unitary.conjStarAlgAut ℂ A (u n) a‖ ≤ ∑' k, δ (n + k)) := by
  have hsum_sub : Summable fun n ↦ ‖(u (n + 1) : A) - (u n : A)‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hδ
    have hcoeff : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc ‖(u (n + 1) : A) - (u n : A)‖
      _ = 1 * ‖(u (n + 1) : A) - (u n : A)‖ := (one_mul _).symm
      _ ≤ (2 * ((n : ℝ) + 1)) * ‖(u (n + 1) : A) - (u n : A)‖ :=
            mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ ≤ δ n := hu n
  obtain ⟨u₀, hu₀⟩ := Unitary.exists_tendsto_of_summable_norm_sub hsum_sub
  let φ : ℕ → A →⋆ₙₐ[ℂ] A := fun n ↦ (Unitary.conjStarAlgAut ℂ A (u n)).toNonUnitalStarAlgHom
  let ψ : ℕ → A →⋆ₙₐ[ℂ] A :=
    fun n ↦ (Unitary.conjStarAlgAut ℂ A (star (u n))).toNonUnitalStarAlgHom
  let F : ℕ → Set A := fun n ↦ Metric.closedBall (0 : A) ((n : ℝ) + 1)
  have hF_mono : Monotone F := fun m n hmn ↦
    Metric.closedBall_subset_closedBall (by gcongr)
  have hF_dense : Dense (⋃ n, F n) := by
    have huniv : (⋃ n, F n) = univ := eq_univ_of_forall fun a ↦
      mem_iUnion.mpr ⟨⌊‖a‖⌋₊, by simpa [F, dist_zero_right] using (Nat.lt_floor_add_one ‖a‖).le⟩
    exact huniv ▸ dense_univ
  have hφF (n : ℕ) : MapsTo (φ n) (F n) (F n) := by
    intro a ha
    simp only [F, Metric.mem_closedBall, dist_zero_right] at ha ⊢
    have hnorm : ‖φ n a‖ = ‖a‖ := Unitary.norm_conjStarAlgAut_apply ℂ (u n) a
    rwa [hnorm]
  have hψF (n : ℕ) : MapsTo (ψ n) (F n) (F (n + 1)) := by
    intro b hb
    simp only [F, Metric.mem_closedBall, dist_zero_right] at hb ⊢
    have hnorm : ‖ψ n b‖ = ‖b‖ := Unitary.norm_conjStarAlgAut_apply ℂ (star (u n)) b
    push_cast
    linarith
  have hψφ_zero (n : ℕ) (a : A) : ψ n (φ n a) = a := by
    have hmul := congrArg (fun e : A ≃⋆ₐ[ℂ] A ↦ e a)
      ((Unitary.conjStarAlgAut ℂ A).map_mul (star (u n)) (u n)).symm
    simpa [φ, ψ] using hmul
  have hφψ_zero (n : ℕ) (b : A) : Unitary.conjStarAlgAut ℂ A (u n) (ψ n b) = b := by
    have hmul := congrArg (fun e : A ≃⋆ₐ[ℂ] A ↦ e b)
      ((Unitary.conjStarAlgAut ℂ A).map_mul (u n) (star (u n))).symm
    simpa [ψ] using hmul
  have hε_le (n : ℕ) : ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ 0 := fun a _ ↦ by
    simp [hψφ_zero]
  have hδ_le (n : ℕ) : ∀ b ∈ F n, ‖φ (n + 1) (ψ n b) - b‖ ≤ δ n := by
    intro b hb
    have hb_norm : ‖b‖ ≤ (n : ℝ) + 1 := by simpa [F, dist_zero_right] using hb
    have hψ_norm : ‖ψ n b‖ = ‖b‖ := Unitary.norm_conjStarAlgAut_apply ℂ (star (u n)) b
    calc ‖φ (n + 1) (ψ n b) - b‖
      _ = ‖Unitary.conjStarAlgAut ℂ A (u (n + 1)) (ψ n b) -
            Unitary.conjStarAlgAut ℂ A (u n) (ψ n b)‖ := by rw [hφψ_zero]; rfl
      _ ≤ 2 * ‖(u (n + 1) : A) - (u n : A)‖ * ‖ψ n b‖ :=
            Unitary.norm_conjStarAlgAut_sub_le ℂ (u (n + 1)) (u n) (ψ n b)
      _ = 2 * ‖(u (n + 1) : A) - (u n : A)‖ * ‖b‖ := by rw [hψ_norm]
      _ ≤ 2 * ‖(u (n + 1) : A) - (u n : A)‖ * ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hb_norm (by positivity)
      _ = 2 * ((n : ℝ) + 1) * ‖(u (n + 1) : A) - (u n : A)‖ := by ring
      _ ≤ δ n := hu n
  obtain ⟨θ, hθ_tendsto, -, hθ_err, -⟩ := exists_starAlgEquiv_of_approxIntertwining φ ψ F F
    (fun _ ↦ 0) δ hF_mono hF_mono hF_dense hF_dense hφF hψF summable_zero hδ hε_le hδ_le
  have hθ_eq : θ = Unitary.conjStarAlgAut ℂ A u₀ := by
    ext a
    exact tendsto_nhds_unique (hθ_tendsto a) (Unitary.tendsto_conjStarAlgAut_of_tendsto ℂ hu₀ a)
  refine ⟨u₀, hu₀, θ, hθ_eq, hθ_tendsto, fun n a ha ↦ ?_⟩
  have h := hθ_err n a ha
  simp only [zero_add] at h
  exact h

end TauCeti
