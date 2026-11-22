/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
import TauCeti.Analysis.CStarAlgebra.ApproximateIntertwining.Unitary

/-!
# Elliott's approximate intertwining

For separable C⋆-algebras `A` and `B`, two families of `⋆`-homomorphisms `Φ i : A → B` and
`Ψ j : B → A` whose members almost invert one another on every finite set yield a sequence
`Φ (i n)` converging pointwise to a `⋆`-isomorphism `A ≃ B`
(`exists_starAlgEquiv_of_forall_finset_approx`), obtained by instantiating
`IsApproximateIntertwining.equiv` on constant systems.

The main application is Elliott's approximate intertwining theorem
(`elliott_intertwining`): for separable unital C⋆-algebras `A` and `B` and
`⋆`-homomorphisms `φ : A → B` and `ψ : B → A` such that `ψ ∘ φ` and `φ ∘ ψ` are
approximately unitarily equivalent to the identities, there is a `⋆`-isomorphism
`A ≃ B` approximately unitarily equivalent to `φ`, obtained by specializing
`elliott_intertwining_of_isSeqColimitCocone` to constant systems.

## References

* M. Rørdam, *Classification of nuclear, simple C⋆-algebras*, Encyclopaedia Math. Sci. 126,
  §2.3 (Elliott's intertwining argument).
* E. Kirchberg and N. C. Phillips, *Embedding of exact C⋆-algebras in the Cuntz algebra
  `O₂`*, J. reine angew. Math. 525 (2000), Lemma 0.6.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

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
  let α : ℕ → A →⋆ₙₐ[ℂ] A := fun _ ↦ .id ℂ A
  let β : ℕ → B →⋆ₙₐ[ℂ] B := fun _ ↦ .id ℂ B
  let ε (n : ℕ) : ℝ := (1 / 2) ^ n
  choose V hV using fun i (F : Finset A) (n : ℕ) ↦ hΨΦ i F (ε n) (by positivity)
  choose W hW using fun j (G : Finset B) (n : ℕ) ↦ hΦΨ j G (ε n) (by positivity)
  let j₀ : J := V (Classical.arbitrary I) ∅ 0
  let G₀ : Finset B := denseSeed β 0
  let F₀ : Finset A := G₀.image (Ψ j₀) ∪ denseSeed α 0
  let i₀ : I := W j₀ G₀ 0
  let next (n : ℕ) (s : I × J × Finset A × Finset B) : I × J × Finset A × Finset B :=
    let G' := s.2.2.2 ∪ s.2.2.1.image (Φ s.1) ∪ denseSeed β (n + 1)
    let j' := V s.1 s.2.2.1 n
    let F' := s.2.2.1 ∪ G'.image (Ψ j') ∪ denseSeed α (n + 1)
    (W j' G' (n + 1), j', F', G')
  let s : ℕ → I × J × Finset A × Finset B :=
    Nat.rec (motive := fun _ ↦ I × J × Finset A × Finset B) (i₀, j₀, F₀, G₀) next
  have hs_zero : s 0 = (i₀, j₀, F₀, G₀) := rfl
  have hs_succ (n : ℕ) : s (n + 1) = next n (s n) := rfl
  have hseedA (m : ℕ) : (denseSeed α m : Set A) ⊆ (s m).2.2.1 := fun x hx ↦ by
    cases m <;> simp [hs_zero, hs_succ, F₀, next, Finset.mem_coe.mp hx]
  have hseedB (m : ℕ) : (denseSeed β m : Set B) ⊆ (s m).2.2.2 := fun x hx ↦ by
    cases m <;> simp [hs_zero, hs_succ, G₀, next, Finset.mem_coe.mp hx]
  have hinter : IsApproximateIntertwining α β (fun n ↦ Φ (s n).1) (fun n ↦ Ψ (s n).2.1)
      (fun n ↦ ((s n).2.2.1 : Set A)) (fun n ↦ ((s n).2.2.2 : Set B)) ε ε :=
    { mapsTo_α := fun n a ha ↦ by
        simp only [Finset.mem_coe, α, NonUnitalStarAlgHom.coe_id, id_eq, hs_succ, next,
          Finset.mem_union] at ha ⊢
        grind
      mapsTo_β := fun n b hb ↦ by
        simp only [Finset.mem_coe, β, NonUnitalStarAlgHom.coe_id, id_eq, hs_succ, next,
          Finset.mem_union] at hb ⊢
        grind
      mapsTo_φ := fun n a ha ↦ by
        simp only [Finset.mem_coe, hs_succ, next, Finset.mem_union] at ha ⊢
        grind [Finset.mem_image_of_mem]
      mapsTo_ψ := fun n b hb ↦ by
        cases n <;>
          simp only [Finset.mem_coe, hs_zero, hs_succ, F₀, next, Finset.mem_union] at hb ⊢ <;>
          grind [Finset.mem_image_of_mem]
      approx_A := exists_approx_of_denseSeed_subset α hseedA
      approx_B := exists_approx_of_denseSeed_subset β hseedB
      norm_ψ_φ_sub_le := fun n a ha ↦ (hV (s n).1 (s n).2.2.1 n a ha).le
      norm_φ_ψ_sub_le := fun n b hb ↦ by
        cases n with
        | zero => exact (hW j₀ G₀ 0 b hb).le
        | succ n => exact (hW _ _ (n + 1) b hb).le
      summable_δ := summable_geometric_two
      summable_ε := summable_geometric_two }
  refine ⟨fun n ↦ (s n).1,
    hinter.equiv (IsSeqColimitCocone.const A) (IsSeqColimitCocone.const B), fun a ↦ ?_⟩
  simpa only [IsSeqColimitCocone.const, α, β, seqTransHom_id, NonUnitalStarAlgHom.coe_id,
    id_eq, Nat.zero_add] using
    hinter.tendsto_equiv (IsSeqColimitCocone.const A) (IsSeqColimitCocone.const B) 0 a

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
  obtain ⟨θ, hθ, -⟩ := elliott_intertwining_of_isSeqColimitCocone
    (IsSeqColimitCocone.const A) (IsSeqColimitCocone.const B)
    (fun _ ↦ φ) (fun _ ↦ ψ) (fun _ ↦ hψφ) (fun _ ↦ hφψ)
  refine ⟨θ, ?_⟩
  simpa only [NonUnitalStarAlgHom.comp_id, NonUnitalStarAlgHom.id_comp] using hθ 0

end TauCeti
