/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic

/-!
# Normalizer quotients under surjective homomorphisms

For a surjection `f : G →* K` and subgroups `H ≤ G`, `L ≤ K` with
`L.comap f = H`, the normalizer quotients of `H` and `L` are canonically
isomorphic. The kernel of `f` is absorbed by `H`, so no injectivity assumption
is needed. This permits computing a torus normalizer quotient before taking
a central quotient of its ambient group.

The construction uses Mathlib's `Subgroup.comap_normalizer_eq_of_surjective`
and the universal property of `Subgroup.normalizerQuotient`.
-/

public section

namespace Subgroup

variable {G K : Type*} [Group G] [Group K]

/-- A surjection maps the normalizer of a full inverse image into the original
normalizer. -/
def normalizerHomOfComapEq (H : Subgroup G) (L : Subgroup K) (f : G →* K)
    (hf : Function.Surjective f) (hH : L.comap f = H) :
    normalizer (H : Set G) →* normalizer (L : Set K) :=
  (f.comp (normalizer (H : Set G)).subtype).codRestrict (normalizer (L : Set K)) fun g ↦ by
    have h := comap_normalizer_eq_of_surjective L hf
    rw [hH] at h
    exact (SetLike.ext_iff.mp h (g : G)).mpr g.property

/-- The normalizer map applies the original homomorphism to the ambient element. -/
@[simp]
theorem coe_normalizerHomOfComapEq (H : Subgroup G) (L : Subgroup K) (f : G →* K)
    (hf : Function.Surjective f) (hH : L.comap f = H) (g : normalizer (H : Set G)) :
    (H.normalizerHomOfComapEq L f hf hH g : K) = f g :=
  (rfl)

/-- Every normalizer element lifts along a surjection to a normalizer element
of the full inverse image. -/
theorem normalizerHomOfComapEq_surjective (H : Subgroup G) (L : Subgroup K)
    (f : G →* K) (hf : Function.Surjective f) (hH : L.comap f = H) :
    Function.Surjective (H.normalizerHomOfComapEq L f hf hH) := by
  intro k
  obtain ⟨g, hg⟩ := hf k
  have hmem : g ∈ normalizer (H : Set G) := by
    rw [← hH, ← comap_normalizer_eq_of_surjective L hf, mem_comap, hg]
    exact k.property
  refine ⟨⟨g, hmem⟩, ?_⟩
  apply Subtype.ext
  simpa only [coe_normalizerHomOfComapEq] using hg

/-- A surjection induces an isomorphism of normalizer quotients when the source
subgroup is the full inverse image of the target subgroup. -/
noncomputable def normalizerQuotientEquivOfComapEq (H : Subgroup G) (L : Subgroup K)
    (f : G →* K) (hf : Function.Surjective f) (hH : L.comap f = H) :
    H.normalizerQuotient ≃* L.normalizerQuotient := by
  let φ := L.normalizerQuotientMk.comp (H.normalizerHomOfComapEq L f hf hH)
  have hker (g : normalizer (H : Set G)) : φ g = 1 ↔ (g : G) ∈ H := by
    rw [MonoidHom.comp_apply, normalizerQuotientMk_eq_one_iff,
      coe_normalizerHomOfComapEq, ← mem_comap, hH]
  let ψ := H.normalizerQuotientLift φ fun g hg ↦ (hker g).mpr hg
  exact MulEquiv.ofBijective ψ
    ⟨(H.normalizerQuotientLift_injective_iff _ _).mpr hker,
      H.normalizerQuotientLift_surjective_of_surjective _ _
        (L.normalizerQuotientMk_surjective.comp
          (H.normalizerHomOfComapEq_surjective L f hf hH))⟩

/-- On normalizer classes the comparison applies the given surjection. -/
@[simp]
theorem normalizerQuotientEquivOfComapEq_mk (H : Subgroup G) (L : Subgroup K)
    (f : G →* K) (hf : Function.Surjective f) (hH : L.comap f = H)
    (g : normalizer (H : Set G)) :
    H.normalizerQuotientEquivOfComapEq L f hf hH (g : H.normalizerQuotient) =
      (H.normalizerHomOfComapEq L f hf hH g : L.normalizerQuotient) :=
  (rfl)

end Subgroup
