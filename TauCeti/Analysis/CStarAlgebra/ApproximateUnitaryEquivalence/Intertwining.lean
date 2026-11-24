/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import TauCeti.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Elliott's approximate intertwining

An approximate intertwining between two C⋆-algebras consists of sequences of
`⋆`-homomorphisms `φ n : A → B` and `ψ n : B → A`, and increasing sets `F n ⊆ A`,
`G n ⊆ B` with dense unions, such that `φ n` maps `F n` into `G n`, `ψ n` maps `G n`
into `F (n + 1)`, and on these sets `ψ n ∘ φ n` and `φ (n + 1) ∘ ψ n` are within
summable errors of the identity. Then `φ n` and `ψ n` converge pointwise to mutually
inverse `⋆`-isomorphisms (`exists_starAlgEquiv_of_intertwining`). For separable algebras,
such an intertwining can be chosen inductively from two families of maps, each member of
which is almost inverted, on every finite set, by some member of the other family
(`exists_starAlgEquiv_of_forall_finset_approx`).

The main application is Elliott's approximate intertwining theorem
(`elliott_intertwining`): for separable unital C⋆-algebras `A` and `B` and
`⋆`-homomorphisms `φ : A → B` and `ψ : B → A` such that `ψ ∘ φ` and `φ ∘ ψ` are
approximately unitarily equivalent to the identities, there is a `⋆`-isomorphism
`A ≃ B` approximately unitarily equivalent to `φ`; it is the pointwise limit of a
sequence of unitary conjugates of `φ`.

## References

* M. Rørdam, *Classification of nuclear, simple C⋆-algebras*, Encyclopaedia Math. Sci. 126,
  §2.3 (Elliott's intertwining argument).
* E. Kirchberg and N. C. Phillips, *Embedding of exact C⋆-algebras in the Cuntz algebra
  `O₂`*, J. reine angew. Math. 525 (2000), Lemma 0.6.
-/

public section

open Filter Topology Set
open scoped CStarAlgebra

namespace TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- One step of an approximate intertwining: `f' a` is close to `f a` when `g` almost inverts
`f` at `a` and `f'` almost inverts `g` at `f a`. -/
private theorem norm_sub_le_of_intertwining (f f' : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] A) (a : A) :
    ‖f' a - f a‖ ≤ ‖g (f a) - a‖ + ‖f' (g (f a)) - f a‖ := by
  simp only [← dist_eq_norm]
  calc dist (f' a) (f a) ≤ dist (f' a) (f' (g (f a))) + dist (f' (g (f a))) (f a) :=
        dist_triangle _ _ _
    _ ≤ dist (g (f a)) a + dist (f' (g (f a))) (f a) := by
        gcongr
        exact (NonUnitalStarAlgHom.dist_apply_le f' _ _).trans_eq (dist_comm _ _)

/-- The Cauchy step of an approximate intertwining: if `ψ n ∘ φ n` is within `ε n` of the
identity on `F n` and `φ (n + 1) ∘ ψ n` is within `ε' n` of the identity on `G n`, for summable
`ε` and `ε'`, then `φ n` is pointwise Cauchy on `⋃ n, F n`. -/
private theorem cauchySeq_of_intertwining {φ : ℕ → A →⋆ₙₐ[ℂ] B} {ψ : ℕ → B →⋆ₙₐ[ℂ] A}
    {F : ℕ → Set A} {G : ℕ → Set B} {ε ε' : ℕ → ℝ} (hF : Monotone F)
    (hφ : ∀ n, MapsTo (φ n) (F n) (G n)) (hε : Summable ε) (hε' : Summable ε')
    (hψφ : ∀ n, ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ ε n)
    (hφψ : ∀ n, ∀ b ∈ G n, ‖φ (n + 1) (ψ n b) - b‖ ≤ ε' n) :
    ∀ a ∈ ⋃ n, F n, CauchySeq fun m ↦ φ m a := by
  simp only [mem_iUnion]
  rintro a ⟨n, ha⟩
  refine cauchySeq_of_eventually_dist_le_of_summable (hε.add hε')
    (eventually_atTop.mpr ⟨n, fun m hm ↦ ?_⟩)
  rw [dist_comm, dist_eq_norm]
  exact (norm_sub_le_of_intertwining (φ m) (φ (m + 1)) (ψ m) a).trans
    (add_le_add (hψφ m a (hF hm ha)) (hφψ m _ (hφ m (hF hm ha))))

/-- The limit step of an approximate intertwining: if `θ` and `η` are the pointwise limits of
`φ n` and `ψ n`, and at each point `a` of a dense set `ψ n ∘ φ n` is eventually within `ε n` of
the identity, for `ε` tending to `0`, then `η ∘ θ` is the identity. -/
private theorem comp_eq_id_of_tendsto {φ : ℕ → A →⋆ₙₐ[ℂ] B} {ψ : ℕ → B →⋆ₙₐ[ℂ] A}
    {θ : A →⋆ₙₐ[ℂ] B} {η : B →⋆ₙₐ[ℂ] A} (hθ : ∀ a, Tendsto (fun n ↦ φ n a) atTop (𝓝 (θ a)))
    (hη : ∀ b, Tendsto (fun n ↦ ψ n b) atTop (𝓝 (η b))) {S : Set A} (hS : Dense S)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hψφ : ∀ a ∈ S, ∀ᶠ n in atTop, ‖ψ n (φ n a) - a‖ ≤ ε n) :
    η.comp θ = NonUnitalStarAlgHom.id ℂ A :=
  NonUnitalStarAlgHom.ext <| congrFun <|
    Continuous.ext_on hS (map_continuous (η.comp θ)) continuous_id fun a ha ↦
      tendsto_nhds_unique (NonUnitalStarAlgHom.tendsto_apply_of_tendsto hη (hθ a))
        (tendsto_sub_nhds_zero_iff.mp <| squeeze_zero_norm' (hψφ a ha) hε)

/-- **Approximate intertwining.** Let `φ n : A → B` and `ψ n : B → A` be `⋆`-homomorphisms
and `F n ⊆ A`, `G n ⊆ B` increasing sets with dense unions, such that `φ n` maps `F n` into
`G n` and `ψ n` maps `G n` into `F (n + 1)`. If `ψ n ∘ φ n` is within `ε n` of the identity
on `F n` and `φ (n + 1) ∘ ψ n` is within `ε n` of the identity on `G n`, for a summable
sequence `ε`, then `φ n` and `ψ n` converge pointwise to a `⋆`-isomorphism `A ≃ B` and to
its inverse. -/
theorem exists_starAlgEquiv_of_intertwining (φ : ℕ → A →⋆ₙₐ[ℂ] B) (ψ : ℕ → B →⋆ₙₐ[ℂ] A)
    {F : ℕ → Set A} {G : ℕ → Set B} {ε : ℕ → ℝ} (hF : Monotone F) (hG : Monotone G)
    (hFd : Dense (⋃ n, F n)) (hGd : Dense (⋃ n, G n))
    (hφ : ∀ n, MapsTo (φ n) (F n) (G n)) (hψ : ∀ n, MapsTo (ψ n) (G n) (F (n + 1)))
    (hε : Summable ε) (hψφ : ∀ n, ∀ a ∈ F n, ‖ψ n (φ n a) - a‖ ≤ ε n)
    (hφψ : ∀ n, ∀ b ∈ G n, ‖φ (n + 1) (ψ n b) - b‖ ≤ ε n) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, (∀ a, Tendsto (fun n ↦ φ n a) atTop (𝓝 (θ a))) ∧
      ∀ b, Tendsto (fun n ↦ ψ n b) atTop (𝓝 (θ.symm b)) := by
  have hε0 := hε.tendsto_atTop_zero
  -- The backward maps form the same kind of intertwining, with `F` and `ε` shifted by one.
  obtain ⟨θ, hθ⟩ := NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq hFd
    (cauchySeq_of_intertwining hF hφ hε hε hψφ hφψ)
  obtain ⟨η, hη⟩ := NonUnitalStarAlgHom.exists_tendsto_of_cauchySeq hGd
    (cauchySeq_of_intertwining (ψ := fun n ↦ φ (n + 1)) hG hψ hε
      ((summable_nat_add_iff 1).mpr hε) hφψ fun n ↦ hψφ (n + 1))
  -- Each point of `⋃ n, F n` (resp. `⋃ n, G n`) lies in `F n` (resp. `G n`) for all large `n`.
  have hηθ : η.comp θ = NonUnitalStarAlgHom.id ℂ A := by
    refine comp_eq_id_of_tendsto hθ hη hFd hε0 fun a ha ↦ ?_
    obtain ⟨n, ha⟩ := mem_iUnion.mp ha
    exact eventually_atTop.mpr ⟨n, fun m hm ↦ hψφ m a (hF hm ha)⟩
  have hθη : θ.comp η = NonUnitalStarAlgHom.id ℂ B := by
    refine comp_eq_id_of_tendsto (ψ := fun n ↦ φ (n + 1)) hη
      (fun x ↦ (hθ x).comp (tendsto_add_atTop_nat 1)) hGd hε0 fun b hb ↦ ?_
    obtain ⟨n, hb⟩ := mem_iUnion.mp hb
    exact eventually_atTop.mpr ⟨n, fun m hm ↦ hφψ m b (hG hm hb)⟩
  exact ⟨StarAlgEquiv.ofNonUnitalStarAlgHom θ η hηθ hθη, hθ, hη⟩

/-- **Approximate intertwining from almost inverse families.** Let `A` and `B` be separable,
and let `Φ i : A → B` (`i : I`) and `Ψ j : B → A` (`j : J`) be families of
`⋆`-homomorphisms such that each `Φ i` has an almost left inverse in the family `Ψ` and each
`Ψ j` an almost left inverse in the family `Φ`, on every finite set and to every positive
tolerance. Then some sequence `Φ (i n)` converges pointwise to a `⋆`-isomorphism `A ≃ B`. -/
theorem exists_starAlgEquiv_of_forall_finset_approx [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace B] {I J : Type*} [Nonempty I]
    (Φ : I → A →⋆ₙₐ[ℂ] B) (Ψ : J → B →⋆ₙₐ[ℂ] A)
    (hΨΦ : ∀ i (F : Finset A) (δ : ℝ), 0 < δ → ∃ j, ∀ a ∈ F, ‖Ψ j (Φ i a) - a‖ < δ)
    (hΦΨ : ∀ j (G : Finset B) (δ : ℝ), 0 < δ → ∃ i, ∀ b ∈ G, ‖Φ i (Ψ j b) - b‖ < δ) :
    ∃ (i : ℕ → I) (θ : A ≃⋆ₐ[ℂ] B), ∀ a, Tendsto (fun n ↦ Φ (i n) a) atTop (𝓝 (θ a)) := by
  classical
  let ε (n : ℕ) : ℝ := (1 / 2) ^ n
  choose V hV using fun i (F : Finset A) (n : ℕ) ↦ hΨΦ i F (ε n) (by positivity)
  choose W hW using fun j (G : Finset B) (n : ℕ) ↦ hΦΨ j G (ε n) (by positivity)
  let a := TopologicalSpace.denseSeq A
  let b := TopologicalSpace.denseSeq B
  -- The stage-`n` data is an index `i` and finite sets `F ⊆ A`, `G ⊆ B`. The next stage uses
  -- `j = V i F n` and the index `W j G n`, and enlarges `F` and `G` by the images under the
  -- new maps and by the next terms of the dense sequences.
  let next (n : ℕ) (s : I × Finset A × Finset B) : I × Finset A × Finset B :=
    let j := V s.1 s.2.1 n
    let i := W j s.2.2 n
    let F := insert (a (n + 1)) (s.2.1 ∪ s.2.2.image (Ψ j))
    (i, F, insert (b (n + 1)) (s.2.2 ∪ F.image (Φ i)))
  let i₀ : I := Classical.arbitrary I
  let s (n : ℕ) : I × Finset A × Finset B :=
    Nat.rec (motive := fun _ ↦ I × Finset A × Finset B)
      (i₀, {a 0}, insert (b 0) (({a 0} : Finset A).image (Φ i₀))) next n
  have hs (n : ℕ) : s (n + 1) = next n (s n) := rfl
  have ha (n : ℕ) : a n ∈ (s n).2.1 := by
    cases n <;> simp [s, next]
  have hb (n : ℕ) : b n ∈ (s n).2.2 := by
    cases n <;> simp [s, next]
  have hmaps (n : ℕ) : MapsTo (Φ (s n).1) (s n).2.1 (s n).2.2 := by
    intro x hx
    cases n with
    | zero => simp_all [s]
    | succ n => simp only [hs, next]; grind
  obtain ⟨θ, hθ, -⟩ := exists_starAlgEquiv_of_intertwining (fun n ↦ Φ (s n).1)
    (fun n ↦ Ψ (V (s n).1 (s n).2.1 n)) (F := fun n ↦ ((s n).2.1 : Set A))
    (G := fun n ↦ ((s n).2.2 : Set B)) (ε := ε)
    (monotone_nat_of_le_succ fun n x hx ↦ by simp [hs, next, Finset.mem_coe.mp hx])
    (monotone_nat_of_le_succ fun n x hx ↦ by simp [hs, next, Finset.mem_coe.mp hx])
    ((TopologicalSpace.denseRange_denseSeq A).mono
      (range_subset_iff.mpr fun n ↦ mem_iUnion.mpr ⟨n, ha n⟩))
    ((TopologicalSpace.denseRange_denseSeq B).mono
      (range_subset_iff.mpr fun n ↦ mem_iUnion.mpr ⟨n, hb n⟩))
    hmaps (fun n y hy ↦ by simp only [hs, next]; grind)
    summable_geometric_two (fun n x hx ↦ (hV _ _ n x hx).le) (fun n y hy ↦ (hW _ _ n y hy).le)
  exact ⟨fun n ↦ (s n).1, θ, hθ⟩

/-- If `g ∘ f` is approximately unitarily equivalent to the identity, then so is the composite
of `g` with any unitary conjugate of `f`: postcomposition with `g`, which preserves the unit,
preserves the approximate unitary equivalence of `f` with its conjugate. The conclusion is
stated in the finite-set form of `approximatelyUnitarilyEquivalent_def`. -/
private theorem exists_norm_comp_conj_sub_lt {D E : Type*} [CStarAlgebra D]
    [CStarAlgebra E] {f : D →⋆ₙₐ[ℂ] E} {g : E →⋆ₙₐ[ℂ] D}
    (h : ApproximatelyUnitarilyEquivalent (g.comp f) (NonUnitalStarAlgHom.id ℂ D))
    (w : unitary E) (F : Finset D) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : unitary D, ∀ a ∈ F,
      ‖(v : D) * g ((w : E) * f a * star (w : E)) * star (v : D) - a‖ < δ := by
  have hw : ApproximatelyUnitarilyEquivalent f
      ((Unitary.conjStarAlgAut ℂ E w).toNonUnitalStarAlgHom.comp f) :=
    .of_unitary w fun a ↦ by
      simp only [NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
        Unitary.conjStarAlgAut_apply]
  simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    Unitary.conjStarAlgAut_apply, Unitary.coe_star, NonUnitalStarAlgHom.coe_id, id_eq] using
    (approximatelyUnitarilyEquivalent_def _ _).mp
      ((hw.postcomp_of_map_one g h.map_one_of_comp).symm.trans h) F δ hδ

/-- **Elliott's approximate intertwining theorem.** Let `A` and `B` be separable unital
C⋆-algebras and `φ : A → B`, `ψ : B → A` be `⋆`-homomorphisms such that `ψ ∘ φ` is
approximately unitarily equivalent to the identity of `A` and `φ ∘ ψ` to the identity of
`B`, with implementing unitaries in `A` and in `B` respectively. Then there is a
`⋆`-isomorphism `A ≃ B` approximately unitarily equivalent to `φ`. The hypotheses force `φ`
and `ψ` to be unital (`ApproximatelyUnitarilyEquivalent.map_one_of_comp`). -/
theorem elliott_intertwining {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (NonUnitalStarAlgHom.id ℂ A))
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (NonUnitalStarAlgHom.id ℂ B)) :
    ∃ θ : A ≃⋆ₐ[ℂ] B, ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ := by
  -- The intertwining maps are the unitary conjugates of `φ` and of `ψ`.
  let Φ (w : unitary B) : A →⋆ₙₐ[ℂ] B :=
    (Unitary.conjStarAlgAut ℂ B w).toNonUnitalStarAlgHom.comp φ
  let Ψ (v : unitary A) : B →⋆ₙₐ[ℂ] A :=
    (Unitary.conjStarAlgAut ℂ A v).toNonUnitalStarAlgHom.comp ψ
  have hΦ (w : unitary B) (x : A) : Φ w x = w * φ x * star (w : B) := by simp [Φ]
  have hΨ (v : unitary A) (y : B) : Ψ v y = v * ψ y * star (v : A) := by simp [Ψ]
  -- Conjugating one map keeps the composite approximately unitarily equivalent to the identity.
  obtain ⟨w, θ, hθ⟩ := exists_starAlgEquiv_of_forall_finset_approx Φ Ψ
    (fun w F δ hδ ↦ by simpa only [hΦ, hΨ] using exists_norm_comp_conj_sub_lt hψφ w F δ hδ)
    (fun v G δ hδ ↦ by simpa only [hΦ, hΨ] using exists_norm_comp_conj_sub_lt hφψ v G δ hδ)
  exact ⟨θ, (ApproximatelyUnitarilyEquivalent.of_tendsto (l := atTop) w fun x ↦ by
    simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, hΦ] using hθ x).symm⟩

end TauCeti
