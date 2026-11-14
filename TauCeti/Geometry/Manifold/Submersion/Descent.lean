/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Submersion.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Immersions, embeddings and uniqueness of smooth structures along surjective submersions

A map out of the target of a surjective submersion with boundaryless source is `C^n` exactly when
its composite with the submersion is `C^n` (`Manifold.IsSubmersion.contMDiff_comp_iff`). This file
draws two geometric consequences.

First, a map descended through a surjective submersion into a finite-dimensional boundaryless
manifold is an immersion, or a smooth embedding when it is also a topological embedding, exactly
when the original map is smooth and its differential has precisely the vertical kernel of the
submersion. This criterion applies to smooth quotients with positive-dimensional fibres, such as
homogeneous spaces and quotients removing the excess in composition of correspondences.

Second, a surjective `C^n` submersion out of a boundaryless manifold determines the `C^n` manifold
structure of its target uniquely: any bijection between the targets of two surjective `C^n`
submersions that intertwines the projections is a `C^n` diffeomorphism
(`Manifold.IsSubmersion.diffeomorphOfCompEq`), and two `C^n` manifold structures on the same
topological space making a surjective map a `C^n` submersion are `C^n`-diffeomorphic via the
identity (`Equiv.refl N`) and share the same maximal atlas when modelled on the same model with
corners (`Manifold.IsSubmersion.maximalAtlas_eq_of_surjective`).

## Main results

* `Manifold.IsSubmersion.isImmersion_iff_ker_mfderiv_comp` and
  `Manifold.IsSubmersion.isSmoothEmbedding_iff_ker_mfderiv_comp`: criteria for a map out of the
  target of a surjective submersion to be an immersion or a smooth embedding.
* `Manifold.IsSubmersion.diffeomorphOfCompEq`: a bijection intertwining two surjective `C^n`
  submersions out of a boundaryless manifold is a `C^n` diffeomorphism.
* `Manifold.IsSubmersion.maximalAtlas_eq_of_surjective`: uniqueness of the `C^n` manifold
  structure making a surjective map out of a boundaryless manifold a `C^n` submersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorems 4.26, 4.29 and 4.31
  (local sections, passing smoothly to a quotient, and uniqueness of quotient manifold structures).
-/

public section

open Function Filter Set Manifold Topology
open scoped Manifold ContDiff

namespace Manifold.IsSubmersion

section Immersion

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 F H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''} [K.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} [IsManifold J n N] [IsManifold K n P] {q : M → N} {f : N → P}

/-- A map descended through a surjective submersion is an immersion exactly when the original
map is smooth and its differential has precisely the vertical kernel. The target model is
finite dimensional; the source of the submersion need not be. -/
theorem isImmersion_iff_ker_mfderiv_comp (hq : IsSubmersion I J n q)
    (hsurj : Surjective q) (hn : 1 ≤ n) :
    IsImmersion J K n f ↔ ContMDiff I K n (f ∘ q) ∧
      ∀ x, (mfderiv I K (f ∘ q) x).ker = (mfderiv I J q x).ker := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  constructor
  · intro hf
    refine ⟨hf.contMDiff.comp hq.contMDiff, fun x ↦ ?_⟩
    rw [mfderiv_comp x (hf.contMDiff.mdifferentiable hn0 _) (hq.contMDiff.mdifferentiable hn0 _),
      ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot_of_injective (hf.mfderiv_injective hn0 _))
  · rintro ⟨hfq, hker⟩
    have hf := (hq.contMDiff_comp_iff hsurj le_rfl).mp hfq
    apply hf.isImmersion_of_injective_mfderiv hn
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    obtain ⟨u, rfl⟩ := hq.surjective_mfderiv hn0 x v
    have hu : u ∈ (mfderiv I K (f ∘ q) x).ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        mfderiv_comp x (hf.mdifferentiable hn0 _) (hq.contMDiff.mdifferentiable hn0 _),
        ContinuousLinearMap.comp_apply]
      exact hv
    exact LinearMap.mem_ker.mp (hker x ▸ hu)

/-- A map descended through a surjective submersion is a `C^n` smooth embedding, `1 ≤ n`, exactly
when it is a topological embedding, `f ∘ q` is `C^n`, and the differential of `f ∘ q` has
precisely the vertical kernel of `q`. -/
theorem isSmoothEmbedding_iff_ker_mfderiv_comp (hq : IsSubmersion I J n q)
    (hsurj : Surjective q) (hn : 1 ≤ n) :
    IsSmoothEmbedding J K n f ↔ IsEmbedding f ∧ ContMDiff I K n (f ∘ q) ∧
      ∀ x, (mfderiv I K (f ∘ q) x).ker = (mfderiv I J q x).ker := by
  rw [isSmoothEmbedding_iff, isImmersion_iff_ker_mfderiv_comp hq hsurj hn]
  tauto

end Immersion

section Uniqueness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F₁ F₂ H H₁ H₂ M N₁ N₂ N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [TopologicalSpace H₁]
  {J₁ : ModelWithCorners 𝕜 F₁ H₁}
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [TopologicalSpace H₂]
  {J₂ : ModelWithCorners 𝕜 F₂ H₂}
  {n : ℕ∞ω}

/-- **Uniqueness of quotient targets up to diffeomorphism.** Let `q₁ : M → N₁` and `q₂ : M → N₂`
be `C^n` submersions out of a boundaryless manifold `M`, with `q₁` surjective. Any bijection
`e : N₁ ≃ N₂` intertwining `q₁` and `q₂` (`e ∘ q₁ = q₂`) is a `C^n` diffeomorphism. -/
def diffeomorphOfCompEq [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
    [TopologicalSpace N₂] [ChartedSpace H₂ N₂] {q₁ : M → N₁} {q₂ : M → N₂}
    (hq₁ : IsSubmersion I J₁ n q₁) (hq₂ : IsSubmersion I J₂ n q₂) (hsurj₁ : Surjective q₁)
    (e : N₁ ≃ N₂) (he : ∀ x, e (q₁ x) = q₂ x) :
    N₁ ≃ₘ^n⟮J₁, J₂⟯ N₂ where
  toEquiv := e
  contMDiff_toFun := by
    rw [← hq₁.contMDiff_comp_iff hsurj₁ le_rfl]
    exact hq₂.contMDiff.congr he
  contMDiff_invFun := by
    have hsurj₂ : Surjective q₂ := by
      have hcomp : ⇑e ∘ q₁ = q₂ := funext he
      rw [← hcomp]
      exact e.surjective.comp hsurj₁
    rw [← hq₂.contMDiff_comp_iff hsurj₂ le_rfl]
    exact hq₁.contMDiff.congr fun x ↦ by rw [comp_apply, ← he x, e.symm_apply_apply]

/-- The diffeomorphism `diffeomorphOfCompEq` has the given underlying map. -/
@[simp]
theorem coe_diffeomorphOfCompEq [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
    [TopologicalSpace N₂] [ChartedSpace H₂ N₂] {q₁ : M → N₁} {q₂ : M → N₂}
    (hq₁ : IsSubmersion I J₁ n q₁) (hq₂ : IsSubmersion I J₂ n q₂) (hsurj₁ : Surjective q₁)
    (e : N₁ ≃ N₂) (he : ∀ x, e (q₁ x) = q₂ x) :
    ⇑(diffeomorphOfCompEq hq₁ hq₂ hsurj₁ e he) = e :=
  (rfl)

/-- The inverse of `diffeomorphOfCompEq` has the inverse equivalence as its underlying map. -/
@[simp]
theorem coe_diffeomorphOfCompEq_symm [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
    [TopologicalSpace N₂] [ChartedSpace H₂ N₂] {q₁ : M → N₁} {q₂ : M → N₂}
    (hq₁ : IsSubmersion I J₁ n q₁) (hq₂ : IsSubmersion I J₂ n q₂) (hsurj₁ : Surjective q₁)
    (e : N₁ ≃ N₂) (he : ∀ x, e (q₁ x) = q₂ x) :
    ⇑(diffeomorphOfCompEq hq₁ hq₂ hsurj₁ e he).symm = e.symm :=
  (rfl)

/-- **Uniqueness of the maximal atlas under a surjective submersion.** Two `C^n` manifold
structures on `N` with the same model `J₁` making a surjective map `q : M → N` out of a
boundaryless manifold a `C^n` submersion have the same maximal atlas. -/
theorem maximalAtlas_eq_of_surjective [TopologicalSpace N] {c₁ c₂ : ChartedSpace H₁ N}
    (hm₁ : letI := c₁; IsManifold J₁ n N) (hm₂ : letI := c₂; IsManifold J₁ n N)
    {q : M → N} (hq₁ : letI := c₁; IsSubmersion I J₁ n q)
    (hq₂ : letI := c₂; IsSubmersion I J₁ n q) (hsurj : Surjective q) :
    (letI := c₁; IsManifold.maximalAtlas J₁ n N) =
      (letI := c₂; IsManifold.maximalAtlas J₁ n N) := by
  have hsub (ca cb : ChartedSpace H₁ N) (hmb : letI := cb; IsManifold J₁ n N)
      (hqa : letI := ca; IsSubmersion I J₁ n q) (hqb : letI := cb; IsSubmersion I J₁ n q) :
      (letI := ca; IsManifold.maximalAtlas J₁ n N) ⊆
        (letI := cb; IsManifold.maximalAtlas J₁ n N) := by
    intro e he
    -- First read `e ∘ q` and local sections of `q` in the atlas `ca`, where `e` is a smooth chart.
    have heq : ContMDiffOn I J₁ n (e ∘ q) (q ⁻¹' e.source) := by
      let := ca
      intro x hx
      exact ((contMDiffAt_of_mem_maximalAtlas he hx).comp x
        hqa.contMDiff.contMDiffAt).contMDiffWithinAt
    have hesymm : ∀ z ∈ e.target, ∃ g : H₁ → M, ContMDiffAt J₁ I n g z ∧
        q ∘ g =ᶠ[𝓝 z] e.symm := by
      let := ca
      intro z hz
      obtain ⟨x, hx⟩ := hsurj (e.symm z)
      obtain ⟨U, hU, hxU, s, -, hs, hqs⟩ := (hqa.isSubmersionAt x).exists_contMDiffOn_section
      rw [hx] at hxU
      have hes : ContMDiffAt J₁ J₁ n e.symm z :=
        contMDiffAt_symm_of_mem_maximalAtlas he hz
      refine ⟨s ∘ e.symm, (hs.contMDiffAt (hU.mem_nhds hxU)).comp z hes, ?_⟩
      filter_upwards [hes.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with w hw
      exact hqs (e.symm w) hw
    -- Now verify smoothness of `e` and `e.symm` in the atlas `cb`.
    let := cb
    have := hmb
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact (((hqb.isSubmersionAt x).contMDiffAt_comp_iff le_rfl).1
        ((heq x hy).contMDiffAt ((e.open_source.preimage hqb.contMDiff.continuous).mem_nhds
          hy))).contMDiffWithinAt
    · intro z hz
      obtain ⟨g, hg, hqg⟩ := hesymm z hz
      exact ((hqb.contMDiff.contMDiffAt.comp z hg).congr_of_eventuallyEq
        hqg.symm).contMDiffWithinAt
  exact Subset.antisymm (hsub c₁ c₂ hm₂ hq₁ hq₂) (hsub c₂ c₁ hm₁ hq₂ hq₁)

end Uniqueness

end Manifold.IsSubmersion
