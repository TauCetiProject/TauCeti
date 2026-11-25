/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holder.Atlas
public import TauCeti.Geometry.Manifold.VectorBundle.Holder.Little.Basic

/-!
# Independence of the little Hölder space of sections from the atlas

Let `V → M` be a `Cⁿ` real vector bundle with complete model fibre over a `Cⁿ` manifold without
boundary, and let `A` and `B` be two finite bundle atlases. For `k + 1 ≤ n` and `α ≤ 1` the Hölder
spaces `C^{k,α}(V)` of `A` and `B` are identified by the identity on underlying sections, a Banach
space isomorphism (`TauCeti.HolderSection.atlasEquiv`). This file shows that the identification
carries the little Hölder space `h^{k,α}(V)` of `A`, the closure of the smooth sections
(`TauCeti.HolderSection.littleHolder`), onto that of `B`: smoothness of a section does not depend on
the atlas, and a homeomorphism carries closures to closures.

## Main results

* `TauCeti.HolderSection.smoothSections_map_atlasLinearEquiv`: the linear identification
  `TauCeti.HolderSection.atlasLinearEquiv` carries the smooth sections of `C^{k,α}(V)` for `A` onto
  those for `B`; this needs no completeness of the model fibre.
* `TauCeti.HolderSection.littleHolder_map_atlasEquiv`: the Banach space identification carries
  `h^{k,α}(V)` for `A` onto `h^{k,α}(V)` for `B`.
* `TauCeti.HolderSection.atlasEquiv_mem_littleHolder_iff`: an element lies in the little Hölder
  space of `A` exactly when its image lies in that of `B`.
-/

public section

open Bundle
open scoped Manifold NNReal ContDiff

universe u

namespace TauCeti

namespace HolderSection

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A B : FiniteBundleAtlas E M F V} {k : ℕ} {α : ℝ≥0} {n : WithTop ℕ∞}
  [IsManifold 𝓘(ℝ, E) n M] [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]

/-- The smooth sections of `C^{k,α}(V)` for `A` are the preimages of those for `B` under the
linear identification of the two Hölder spaces. -/
theorem smoothSections_comap_atlasLinearEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (smoothSections B k α).comap (atlasLinearEquiv A B k α hα hn).toLinearMap =
      smoothSections A k α :=
  Submodule.ext fun w ↦ by
    simp only [Submodule.mem_comap, mem_smoothSections_iff, LinearEquiv.coe_coe,
      toSection_atlasLinearEquiv]

/-- The linear identification of the Hölder spaces of two atlases carries the smooth sections for
`A` onto those for `B`. -/
theorem smoothSections_map_atlasLinearEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (smoothSections A k α).map (atlasLinearEquiv A B k α hα hn).toLinearMap =
      smoothSections B k α := by
  rw [← smoothSections_comap_atlasLinearEquiv hα hn (A := A) (B := B)]
  exact Submodule.map_comap_eq_of_surjective (atlasLinearEquiv A B k α hα hn).surjective _

variable [CompleteSpace F]

/-- **Atlas independence of the little Hölder space of sections**, preimage form: `h^{k,α}(V)`
for `A` is the preimage of `h^{k,α}(V)` for `B` under the identification of the two Hölder
spaces. -/
theorem littleHolder_comap_atlasEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (littleHolder B k α).comap
      (atlasEquiv A B k α hα hn : HolderSection A k α →ₗ[ℝ] HolderSection B k α) =
      littleHolder A k α := by
  apply SetLike.coe_injective
  rw [Submodule.comap_coe, coe_littleHolder, coe_littleHolder,
    ← smoothSections_comap_atlasLinearEquiv hα hn (A := A) (B := B), Submodule.comap_coe,
    ← toLinearEquiv_atlasEquiv hα hn]
  simpa only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearEquiv.coe_toHomeomorph] using
    (atlasEquiv A B k α hα hn).toHomeomorph.preimage_closure _

/-- An element of `C^{k,α}(V)` for `A` lies in the little Hölder space of `A` exactly when its
image under the identification of the Hölder spaces lies in that of `B`. -/
@[simp]
theorem atlasEquiv_mem_littleHolder_iff (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    {w : HolderSection A k α} :
    atlasEquiv A B k α hα hn w ∈ littleHolder B k α ↔ w ∈ littleHolder A k α := by
  rw [← littleHolder_comap_atlasEquiv hα hn (A := A) (B := B), Submodule.mem_comap,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- **Atlas independence of the little Hölder space of sections.** For a `Cⁿ` vector bundle with
complete model fibre, `k + 1 ≤ n` and `α ≤ 1`, the identification of the Hölder spaces
`C^{k,α}(V)` of two finite bundle atlases `A` and `B` carries the little Hölder space `h^{k,α}(V)`
of `A` onto that of `B`. -/
theorem littleHolder_map_atlasEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (littleHolder A k α).map
      (atlasEquiv A B k α hα hn : HolderSection A k α →ₗ[ℝ] HolderSection B k α) =
      littleHolder B k α := by
  rw [← littleHolder_comap_atlasEquiv hα hn (A := A) (B := B)]
  exact Submodule.map_comap_eq_of_surjective (atlasEquiv A B k α hα hn).surjective _

end HolderSection

end TauCeti
