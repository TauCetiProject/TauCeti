/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Quotients of a product of groups by a subgroup

Let `A` and `K` be groups and let `Γ` be a subgroup of `A × K`. Write
`Λ = {a | (a, 1) ∈ Γ}` for the part of `Γ` lying in the first factor, the subgroup
`Γ.comap (MonoidHom.inl A K)` of `A`. Two points `(a, k)` and `(a', k)` with the same second
coordinate lie in the same coset of `Γ` exactly when `a` and `a'` lie in the same coset of `Λ`.
So the projection `A × K → (A × K) ⧸ Γ` factors through

`Γ.prodQuotientMap : (A ⧸ Λ) × K → (A × K) ⧸ Γ`, `([a], k) ↦ [(a, k)]`.

Its fibres are in bijection with the image `Γ.map (MonoidHom.snd A K)` of `Γ` in the second
factor (`Subgroup.natCard_prodQuotientMap_preimage`), so they are finite when that image is
finite, for instance when `Γ` is central and `K` has finite centre
(`Subgroup.finite_map_snd_of_le_center`). By `Subgroup.relIndex_ker`, the fibre cardinality is the
index of `Λ × 1 = Γ ⊓ ker snd` in `Γ`.

For topological groups and discrete `Γ`, this map is a covering map; see
`TauCeti.Topology.Algebra.Group.Quotient.Prod`.

## Main declarations

* `Subgroup.prodQuotientMap`: the map `(A ⧸ Λ) × K → (A × K) ⧸ Γ`.
* `Subgroup.natCard_prodQuotientMap_preimage`: its fibres have the cardinality of the image of `Γ`
  in `K`.
* `Subgroup.finite_map_snd_of_le_center`: that image is finite when `Γ` is central and `K` has
  finite centre.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and
  Proposition 6.31).
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, Theorem 8.1 (the finite covering `T × K → G`).
-/

public section

noncomputable section

namespace Subgroup

variable {A K : Type*} [Group A] [Group K] (Γ : Subgroup (A × K))

/-- Two points of `A × K` with the same second coordinate lie in the same coset of `Γ` exactly
when their first coordinates lie in the same coset of `Γ.comap (MonoidHom.inl A K)`. -/
theorem quotientMk_mk_eq_quotientMk_mk_iff {a a' : A} (k : K) :
    ((a, k) : (A × K) ⧸ Γ) = ((a', k) : (A × K) ⧸ Γ) ↔
      (a : A ⧸ Γ.comap (MonoidHom.inl A K)) = a' := by
  simp [QuotientGroup.eq]

/-- The map `(A ⧸ Λ) × K → (A × K) ⧸ Γ`, `([a], k) ↦ [(a, k)]`, for `Λ = {a | (a, 1) ∈ Γ}`, through
which the projection `A × K → (A × K) ⧸ Γ` factors. -/
def prodQuotientMap : (A ⧸ Γ.comap (MonoidHom.inl A K)) × K → (A × K) ⧸ Γ :=
  fun p ↦ Quotient.liftOn' p.1 (fun a ↦ ((a, p.2) : (A × K) ⧸ Γ))
    fun _ _ h ↦ (Γ.quotientMk_mk_eq_quotientMk_mk_iff p.2).2 (Quotient.sound' h)

@[simp]
theorem prodQuotientMap_mk (a : A) (k : K) :
    Γ.prodQuotientMap ((a : A ⧸ Γ.comap (MonoidHom.inl A K)), k) = ((a, k) : (A × K) ⧸ Γ) :=
  (rfl)

theorem surjective_prodQuotientMap : Function.Surjective Γ.prodQuotientMap := by
  intro x
  obtain ⟨⟨a, k⟩, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨(a, k), rfl⟩

/-- The fibre of `Γ.prodQuotientMap` over `[(a, k)]` is in bijection with the image of `Γ` in `K`,
by `([a'], k') ↦ k⁻¹ k'`. -/
def prodQuotientMapPreimageEquiv (a : A) (k : K) :
    Γ.prodQuotientMap ⁻¹' {((a, k) : (A × K) ⧸ Γ)} ≃ Γ.map (MonoidHom.snd A K) :=
  Equiv.ofBijective
    (fun p ↦ ⟨k⁻¹ * p.1.2, by
      obtain ⟨⟨t, k'⟩, hp⟩ := p
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective t
      rw [Set.mem_preimage, Set.mem_singleton_iff, prodQuotientMap_mk, eq_comm,
        QuotientGroup.eq] at hp
      exact ⟨_, hp, by simp⟩⟩)
    (by
      constructor
      · rintro ⟨⟨t₁, k₁⟩, h₁⟩ ⟨⟨t₂, k₂⟩, h₂⟩ h
        have hk : k₁ = k₂ := by simpa using congrArg Subtype.val h
        subst hk
        obtain ⟨a₁, rfl⟩ := QuotientGroup.mk_surjective t₁
        obtain ⟨a₂, rfl⟩ := QuotientGroup.mk_surjective t₂
        rw [Set.mem_preimage, Set.mem_singleton_iff, prodQuotientMap_mk] at h₁ h₂
        exact Subtype.ext <| Prod.ext
          ((Γ.quotientMk_mk_eq_quotientMk_mk_iff k₁).1 (h₁.trans h₂.symm)) rfl
      · rintro ⟨_, γ, hγ, rfl⟩
        refine ⟨⟨((a * γ.1 : A), k * γ.2), ?_⟩, Subtype.ext (by simp)⟩
        rw [Set.mem_preimage, Set.mem_singleton_iff, prodQuotientMap_mk, eq_comm, QuotientGroup.eq]
        simpa using hγ)

@[simp]
theorem coe_prodQuotientMapPreimageEquiv_apply (a : A) (k : K)
    (p : Γ.prodQuotientMap ⁻¹' {((a, k) : (A × K) ⧸ Γ)}) :
    (Γ.prodQuotientMapPreimageEquiv a k p : K) = k⁻¹ * p.1.2 :=
  (rfl)

/-- **The fibres of `(A ⧸ Λ) × K → (A × K) ⧸ Γ` have the cardinality of the image of `Γ` in
`K`.** By `Subgroup.relIndex_ker` this is the index of `Λ × 1 = Γ ⊓ ker snd` in `Γ`. -/
theorem natCard_prodQuotientMap_preimage (x : (A × K) ⧸ Γ) :
    Nat.card (Γ.prodQuotientMap ⁻¹' {x}) = Nat.card (Γ.map (MonoidHom.snd A K)) := by
  obtain ⟨⟨a, k⟩, rfl⟩ := QuotientGroup.mk_surjective x
  exact Nat.card_congr (Γ.prodQuotientMapPreimageEquiv a k)

/-- The fibres of `Γ.prodQuotientMap` are finite when the image of `Γ` in `K` is finite. -/
theorem finite_prodQuotientMap_preimage [Finite (Γ.map (MonoidHom.snd A K))]
    (x : (A × K) ⧸ Γ) : Finite (Γ.prodQuotientMap ⁻¹' {x}) := by
  obtain ⟨⟨a, k⟩, rfl⟩ := QuotientGroup.mk_surjective x
  exact Finite.of_equiv _ (Γ.prodQuotientMapPreimageEquiv a k).symm

/-- A central subgroup of `A × K` has finite image in `K` when `K` has finite centre. -/
theorem finite_map_snd_of_le_center [Finite (center K)] (hΓ : Γ ≤ center (A × K)) :
    Finite (Γ.map (MonoidHom.snd A K)) := by
  refine Finite.Set.subset (center K : Set K) ?_
  rintro _ ⟨γ, hγ, rfl⟩
  rw [SetLike.mem_coe, mem_center_iff]
  intro k
  simpa using congrArg Prod.snd ((mem_center_iff.1 (hΓ hγ)) (1, k))

end Subgroup
