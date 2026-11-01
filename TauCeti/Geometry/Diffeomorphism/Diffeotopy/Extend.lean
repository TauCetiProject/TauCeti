/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.Extend
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod

/-!
# Extending diffeotopies by the identity

A diffeotopy of `N` which fixes every point outside a compact set at all times extends along a
smooth open embedding `χ : N → M` into a Hausdorff manifold: the extension moves `χ z` as the
original motion moves `z`, and fixes every point outside the image of the compact set
(`TauCeti.Diffeotopy.exists_extend_of_isCompact`). For the inclusion of an open subset this
transplants a motion built inside the open subset to the ambient manifold, keeping all of its
moving points inside the subset.

The total level-preserving diffeomorphism of `I × N` is extended along `Prod.map id χ` by
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact`; the extension preserves the time
coordinate and starts at the identity because it either agrees with the original motion or is
the identity.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for
  diffeotopies with compact support.
-/

public section

noncomputable section

open Set Topology unitInterval
open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] {n : ℕ∞ω}

/-- A diffeotopy of `N` fixing every point outside a compact set `K` at all times extends along a
smooth open embedding `χ : N → M` into a Hausdorff manifold. The extension moves `χ z` as the
original motion moves `z`, and fixes every point outside `χ '' K` at all times. -/
theorem exists_extend_of_isCompact [T2Space M] {χ : N → M} (hχ : IsLocalDiffeomorph J J' n χ)
    (hχo : IsOpenEmbedding χ) (Λ : Diffeotopy J n N) {K : Set N} (hK : IsCompact K)
    (hΛ : ∀ t, ∀ z ∉ K, Λ (t, z) = z) :
    ∃ Φ : Diffeotopy J' n M, (∀ t z, Φ (t, χ z) = χ (Λ (t, z))) ∧
      ∀ t, ∀ y ∉ χ '' K, Φ (t, y) = y := by
  let χ' : I × N → I × M := Prod.map id χ
  have hχ' : IsLocalDiffeomorph ((𝓡∂ 1).prod J) ((𝓡∂ 1).prod J') n χ' :=
    (Diffeomorph.refl (𝓡∂ 1) I n).isLocalDiffeomorph.prodMap hχ
  have hχ'o : IsOpenEmbedding χ' := IsOpenEmbedding.id.prodMap hχo
  obtain ⟨Ψ, hΨχ, hΨK⟩ := hχ'.exists_diffeomorph_extend_of_isCompact hχ'o Λ.toDiffeomorph
    (isCompact_univ.prod hK) fun z hz ↦ by
      rw [toDiffeomorph_apply, hΛ z.1 z.2 fun h ↦ hz ⟨mem_univ _, h⟩]
  -- Off the image of `univ ×ˢ K` the extension is the identity; on it, it is the motion.
  have hΨ (p : I × M) : Ψ p = p ∨ ∃ z : I × N, p = χ' z ∧ Ψ p = χ' (Λ.toDiffeomorph z) := by
    by_cases hp : p ∈ χ' '' (univ ×ˢ K)
    · obtain ⟨z, -, rfl⟩ := hp
      exact .inr ⟨z, rfl, hΨχ z⟩
    · exact .inl (hΨK p hp)
  refine ⟨⟨Ψ, fun p ↦ ?_, fun x ↦ ?_⟩, fun t z ↦ ?_, fun t y hy ↦ ?_⟩
  · rcases hΨ p with h | ⟨z, rfl, h⟩
    · rw [h]
    · simp [h, χ']
  · rcases hΨ (0, x) with h | ⟨⟨t, w⟩, hz, h⟩
    · rw [h]
    · simp only [χ', Prod.map, id, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      simp [h, χ']
  · rw [coe_apply, coe_apply]
    exact congrArg Prod.snd (hΨχ (t, z))
  · rw [coe_apply]
    exact congrArg Prod.snd (hΨK (t, y) fun ⟨z, hz, h⟩ ↦ hy ⟨z.2, hz.2, congrArg Prod.snd h⟩)

end TauCeti.Diffeotopy
