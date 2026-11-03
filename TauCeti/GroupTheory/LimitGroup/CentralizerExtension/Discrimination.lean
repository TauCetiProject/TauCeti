/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree

/-!
# Extensions of centralizers are discriminated by the base group

Let `G` be a CSA group with the big powers property, for instance a fully residually free group,
and let `u ≠ 1`. The retractions `ξₖ : G(u, ℤ) →* G`, `t ↦ u ^ k`, of the extension
`G(u, ℤ) = ⟨G, t | [c, t] = 1, c ∈ C_G(u)⟩` of the centralizer of `u` discriminate it by `G`: every
nonidentity element survives under `ξₖ` for all large `k`, so any finite family of nonidentity
elements survives under a single `ξₖ`. In particular `G(u, ℤ)` is fully residually free whenever
`G` is. The hypothesis `u ≠ 1` cannot be dropped: for `u = 1` every retraction kills `t`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.exists_forall_retraction_ne_one`: a nonidentity element of
  `G(u, ℤ)` survives under the retraction `t ↦ u ^ k` for every large `k`.
* `TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy`: `G(u, ℤ)` is discriminated by `G` over
  `G`.
* `TauCeti.LimitGroup.isFullyResiduallyFree_centralizerExt`: an extension of the centralizer of a
  nonidentity element of a fully residually free group is fully residually free.

## Implementation notes

An element of the HNN extension `G(u, ℤ)` is written as a reduced word
`g₀ * t ^ ε₁ * g₁ * ⋯ * t ^ εₙ * gₙ` (Mathlib's `HNNExtension.NormalWord`), in which a letter
`gᵢ ∈ C_G(u)` never separates `t` from `t⁻¹`. Its image under `ξₖ` is the alternating product
`g₀ * u ^ (k * ε₁) * g₁ * ⋯ * u ^ (k * εₙ) * gₙ`, which is nontrivial for all large `k` by the big
powers property (`Group.IsBP.exists_forall_mul_prod_ne_one`); when `n = 0` the element is `g₀`
itself.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. II*,
  J. Algebra 200 (1998), §0, Lemma 2 and Theorem 1.
-/

public section

open Group Subgroup

namespace TauCeti.LimitGroup

open GroupAlgGeom

namespace CentralizerExt

variable {G : Type*} [Group G] {u : G}

/-- In a CSA group `G` with the big powers property, a nonidentity element of the extension
`G(u, ℤ)` of the centralizer of `u ≠ 1` survives under the retraction `t ↦ u ^ k` for every large
`k`. -/
theorem exists_forall_retraction_ne_one (hBP : IsBP G) (hG : IsCSA G) (hu : u ≠ 1)
    {x : CentralizerExt u 1} (hx : x ≠ 1) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → retraction (fun _ => (k : ℤ)) x ≠ 1 := by
  obtain ⟨d⟩ := HNNExtension.NormalWord.TransversalPair.nonempty G (centralizer {u})
    (centralizer {u})
  -- A reduced word `g₀ * t ^ ε₁ * g₁ * ⋯ * t ^ εₙ * gₙ` representing `x`.
  set w := (HNNExtension.NormalWord.equiv (.refl (centralizer {u})) d
    (equivHNNExtension x)).toReducedWord
  have hw : equivHNNExtension.symm (w.prod (.refl _)) = x := by
    rw [MulEquiv.symm_apply_eq]
    exact (HNNExtension.NormalWord.equiv (.refl (centralizer {u})) d).symm_apply_apply _
  -- Its image under `t ↦ u ^ k` is the alternating product `g₀ * u ^ (k * ε₁) * g₁ * ⋯`.
  have hρ (k : ℕ) : retraction (fun _ => (k : ℤ)) x =
      w.head * (w.toList.map fun p => u ^ ((k : ℤ) * (p.1 : ℤ)) * p.2).prod := by
    rw [← hw, HNNExtension.NormalWord.ReducedWord.prod, map_mul, map_mul, map_list_prod,
      map_list_prod, List.map_map, List.map_map]
    simp [Function.comp_def, zpow_mul]
  by_cases hl : w.toList = []
  · refine ⟨0, fun k _ => ?_⟩
    rw [hρ, hl, List.map_nil, List.prod_nil, mul_one]
    intro h1
    apply hx
    rw [← hw, HNNExtension.NormalWord.ReducedWord.prod]
    simp [hl, h1]
  obtain ⟨N, hN⟩ := hBP.exists_forall_mul_prod_ne_one hG hu w.head
    (l := w.toList.map fun p => ((p.1 : ℤ), p.2)) (by simpa using hl)
    (fun q hq => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hq
      exact Units.ne_zero p.1)
    ((List.isChain_map _).2 (w.chain.imp fun p q h hp => by
      -- Both associated subgroups of the HNN extension are `C_G(u)`.
      rw [h (by rcases Int.units_eq_one_or p.1 with h₁ | h₁ <;> simpa [h₁] using hp)]))
  refine ⟨N, fun k hk => ?_⟩
  rw [hρ]
  simpa [Function.comp_def] using hN k hk

/-- **Extensions of centralizers are discriminated by the base group.** In a CSA group `G` with
the big powers property, the extension `G(u, ℤ)` of the centralizer of `u ≠ 1` is discriminated
by `G` over `G`: any finite family of nonidentity elements survives under one retraction
`t ↦ u ^ k`. -/
theorem isDiscriminatedBy (hBP : IsBP G) (hG : IsCSA G) (hu : u ≠ 1) :
    IsDiscriminatedBy (of : G →* CentralizerExt u 1) (.id G) := by
  classical
  refine (isDiscriminatedBy_def _ _).2 fun s hs => ?_
  choose! N hN using fun x (hx : x ∈ s) => exists_forall_retraction_ne_one hBP hG hu (hs x hx)
  exact ⟨⟨retraction fun _ => ((s.sup N : ℕ) : ℤ), retraction_of _⟩,
    fun x hx => hN x hx _ (Finset.le_sup hx)⟩

end CentralizerExt

/-- An extension `G(u, ℤ)` of the centralizer of a nonidentity element `u` of a fully residually
free group `G` is fully residually free. -/
theorem isFullyResiduallyFree_centralizerExt {G : Type*} [Group G] (h : IsFullyResiduallyFree G)
    {u : G} (hu : u ≠ 1) : IsFullyResiduallyFree (CentralizerExt u 1) := by
  classical
  refine isFullyResiduallyFree_def.2 fun s hs => ?_
  obtain ⟨φ, hφ⟩ := (isDiscriminatedBy_def _ _).1
    (CentralizerExt.isDiscriminatedBy h.isBP h.isCSA hu) s hs
  obtain ⟨ι, ψ, hψ⟩ := isFullyResiduallyFree_def.1 h (s.image φ) (by simpa using hφ)
  exact ⟨ι, ψ.comp (φ : CentralizerExt u 1 →* G), fun x hx =>
    hψ (φ x) (Finset.mem_image_of_mem φ hx)⟩

end TauCeti.LimitGroup
