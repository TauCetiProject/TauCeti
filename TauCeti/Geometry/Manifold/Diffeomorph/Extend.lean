/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Topology.Homeomorph.Extend

/-!
# Extending diffeomorphisms by the identity

A diffeomorphism of an open part of a manifold extends by the identity when its moving points
are contained in a closed subset of the ambient manifold lying inside that open part.
`IsLocalDiffeomorph.exists_diffeomorph_extend` gives this extension along an open embedding which
is a local diffeomorphism. The source and ambient manifold may have different models.

For a compact set in the source, its image is closed in a Hausdorff ambient manifold, giving
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact`. In particular,
`Diffeomorph.exists_extend_of_isCompact` extends a compactly supported diffeomorphism of any open
submanifold. These results transplant diffeomorphisms constructed in coordinates to the ambient
manifold while keeping control of where points move.

The underlying homeomorphism is supplied by
`Topology.IsOpenEmbedding.exists_homeomorph_extend`. Smoothness follows locally: on the open
image, cancel the coordinate local diffeomorphism; away from the closed set, the extension is
locally the identity. This applies to the inverse as well, without any loss of regularity.

## References

* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277,
  for the use of coordinate extensions in ambient extension arguments.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8.
-/

public section

open Set Topology
open scoped Manifold ContDiff

namespace IsLocalDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} {χ : N → M}

/-- A diffeomorphism of `N` extends along a smooth open embedding `χ : N → M` by the identity
if its moving points lie over a closed set `C ⊆ range χ`. The extension intertwines the original
diffeomorphism with `χ` and fixes every point outside `C`. -/
theorem exists_diffeomorph_extend (hχ : IsLocalDiffeomorph J I n χ)
    (hχo : IsOpenEmbedding χ) (Λ : N ≃ₘ^n⟮J, J⟯ N) {C : Set M} (hC : IsClosed C)
    (hCχ : C ⊆ range χ) (hΛ : ∀ z, χ z ∉ C → Λ z = z) :
    ∃ Φ : M ≃ₘ^n⟮I, I⟯ M, (∀ z, Φ (χ z) = χ (Λ z)) ∧ ∀ y ∉ C, Φ y = y := by
  obtain ⟨Φ, hΦχ, hΦC⟩ := hχo.exists_homeomorph_extend Λ.toHomeomorph hC hCχ hΛ
  simp only [Diffeomorph.coe_toHomeomorph] at hΦχ
  -- Any homeomorphism with these local formulas is smooth. Use the same argument for its inverse.
  have hsmooth (Ψ : M ≃ₜ M) (L : N ≃ₘ^n⟮J, J⟯ N)
      (hΨχ : ∀ z, Ψ (χ z) = χ (L z)) (hΨC : ∀ y ∉ C, Ψ y = y) :
      ContMDiff I I n Ψ := by
    intro y
    by_cases hy : y ∈ range χ
    · obtain ⟨z, rfl⟩ := hy
      apply ((hχ z).contMDiffAt_comp_iff le_rfl).1
      have heq : Ψ ∘ χ = χ ∘ L := funext hΨχ
      rw [heq]
      exact (hχ.contMDiff.comp L.contMDiff).contMDiffAt
    · have hyC : y ∉ C := fun hyC ↦ hy (hCχ hyC)
      apply contMDiffAt_id.congr_of_eventuallyEq
      filter_upwards [hC.isOpen_compl.mem_nhds hyC] with w hw
      exact hΨC w hw
  have hinvχ (z : N) : Φ.symm (χ z) = χ (Λ.symm z) := by
    apply Φ.injective
    rw [Φ.apply_symm_apply, hΦχ, Λ.apply_symm_apply]
  have hinvC (y : M) (hy : y ∉ C) : Φ.symm y = y := by
    rw [Φ.symm_apply_eq, hΦC y hy]
  exact ⟨{ toEquiv := Φ.toEquiv
           contMDiff_toFun := hsmooth Φ Λ hΦχ hΦC
           contMDiff_invFun := hsmooth Φ.symm Λ.symm hinvχ hinvC }, hΦχ, hΦC⟩

/-- A diffeomorphism fixing the complement of a compact set `K` extends along a smooth open
embedding into a Hausdorff manifold, fixing the complement of the compact image `χ '' K`. -/
theorem exists_diffeomorph_extend_of_isCompact [T2Space M]
    (hχ : IsLocalDiffeomorph J I n χ) (hχo : IsOpenEmbedding χ)
    (Λ : N ≃ₘ^n⟮J, J⟯ N) {K : Set N} (hK : IsCompact K) (hΛ : ∀ z ∉ K, Λ z = z) :
    ∃ Φ : M ≃ₘ^n⟮I, I⟯ M, (∀ z, Φ (χ z) = χ (Λ z)) ∧
      ∀ y ∉ χ '' K, Φ y = y := by
  apply hχ.exists_diffeomorph_extend hχo Λ (hK.image hχo.continuous).isClosed
    (image_subset_range χ K)
  intro z hz
  exact hΛ z fun hzK ↦ hz ⟨z, hzK, rfl⟩

end IsLocalDiffeomorph

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {n : WithTop ℕ∞} {U : TopologicalSpace.Opens M}

/-- A diffeomorphism of an open submanifold, equal to the identity off a compact set `K` in
that submanifold, extends to an ambient diffeomorphism equal to the identity off `K`'s image.
In particular, the ambient diffeomorphism fixes every point outside the open submanifold. -/
theorem exists_extend_of_isCompact (Λ : U ≃ₘ^n⟮I, I⟯ U) {K : Set U}
    (hK : IsCompact K) (hΛ : ∀ z ∉ K, Λ z = z) :
    ∃ Φ : M ≃ₘ^n⟮I, I⟯ M, (∀ z : U, Φ z = Λ z) ∧
      ∀ y ∉ Subtype.val '' K, Φ y = y :=
  TauCeti.isLocalDiffeomorph_subtype_val.exists_diffeomorph_extend_of_isCompact
    U.isOpen.isOpenEmbedding_subtypeVal Λ hK hΛ

end Diffeomorph
