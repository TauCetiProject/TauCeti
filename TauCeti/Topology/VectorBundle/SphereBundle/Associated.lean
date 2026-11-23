/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Topology.FiberBundle.Associated.Map
public import TauCeti.Topology.VectorBundle.Associated.Metric
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic

/-!
# Sphere bundles with an isometric structure group

Let `P` be a principal `G`-bundle over `B`, and let `G` act continuously and additively
(`DistribMulAction`) on a normed space `F` by isometries. Then `G` acts on the unit sphere
`S(F)` (`TauCeti.Sphere.instMulActionOfIsIsometricSMul`), and the associated bundle
`P ×_G S(F)` is a bundle of spheres with structure group `G`. On the other hand, the associated
bundle `P ×_G F` carries the fibre norm of the model (`TauCeti.AssociatedBundle.norm_mk`), and has
a unit sphere bundle `S(P ×_G F)` (`TauCeti.sphereBundle`).

The two agree: the inclusion `S(F) → F` is an equivariant embedding, so the induced map
`[p, v] ↦ [p, v]` is an embedding of total spaces
(`TauCeti.AssociatedBundle.isEmbedding_totalSpaceMap`), and its image is the set of unit vectors,
because each class `[p, v]` has the norm of `v`. This gives a homeomorphism over `B`

`P ×_G S(F) ≃ₜ S(P ×_G F)`

(`TauCeti.AssociatedBundle.sphereBundleHomeomorph`). It identifies the preferred charts of the two
bundles: read in the chart at any point of the base, it is the inclusion `S(F) → F`
(`TauCeti.AssociatedBundle.trivializationAt_sphereBundleHomeomorph`).

For the orthogonal group `O(V) = unitary (V →L[ℝ] V)` of a real inner product space `V` of
dimension `n + 1`, acting on `V` (`Unitary.instIsIsometricSMul`), this says that a sphere bundle
with fibre `Sⁿ` whose structure group reduces to the orthogonal group, presented as the bundle
associated with a principal `O(V)`-bundle, is the unit sphere bundle of the rank `n + 1` real
vector bundle with a fibre metric associated with the same principal bundle. The orthonormal frame
bundle of a Riemannian vector bundle is such a principal bundle
(`TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`).

## Main definitions

* `TauCeti.AssociatedBundle.sphereBundleHomeomorph`: the homeomorphism `P ×_G S(F) ≃ₜ S(P ×_G F)`,
  `[p, v] ↦ [p, v]`.

## Main results

* `TauCeti.AssociatedBundle.range_totalSpaceMap_subtypeMulActionHom`: the image of `P ×_G S(F)`
  in `P ×_G F` is the unit sphere bundle.
* `TauCeti.AssociatedBundle.coe_sphereBundleHomeomorph_proj`: the homeomorphism lies over `B`.
* `TauCeti.AssociatedBundle.trivializationAt_sphereBundleHomeomorph`: it is the inclusion of the
  sphere in the preferred charts.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§8–9 (the
  bundle associated with a new fibre, and bundles with a subgroup of the structure group acting
  on an invariant subspace of the fibre).
* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4, §5, and Chapter 8 (sphere bundles of vector bundles with a metric).
-/

public section

noncomputable section

open Bundle Metric Set Topology

universe u

namespace TauCeti.AssociatedBundle

variable {G : Type*} {B : Type u} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {F : Type u} [NormedAddCommGroup F] [DistribMulAction G F] [ContinuousSMul G F]
  [IsIsometricSMul G F]

variable (G P F) in
/-- The image of `P ×_G S(F)` in `P ×_G F` under the map induced by the inclusion of the sphere is
the unit sphere bundle. -/
theorem range_totalSpaceMap_subtypeMulActionHom :
    range (totalSpaceMap (P := P) (Sphere.subtypeMulActionHom G F 1)) =
      sphereBundle F (AssociatedBundle G P F) := by
  ext ⟨b, v⟩
  obtain ⟨p, v, rfl⟩ := exists_mk v
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨⟨b', w⟩, hw⟩
    obtain ⟨q, w, rfl⟩ := exists_mk w
    rw [totalSpaceMap_mk] at hw
    rw [← hw, mem_sphereBundle, norm_mk, Sphere.coe_subtypeMulActionHom,
      norm_eq_of_mem_sphere]
  · rw [mem_sphereBundle, norm_mk] at hv
    refine ⟨⟨b, mk G p ⟨v, mem_sphere_zero_iff_norm.2 hv⟩⟩, ?_⟩
    rw [totalSpaceMap_mk, Sphere.coe_subtypeMulActionHom]

variable (G P F) in
/-- **A sphere bundle with an isometric structure group is a unit sphere bundle.** The bundle
`P ×_G S(F)` associated with the unit sphere of the fibre is homeomorphic over the base to the
unit sphere bundle of `P ×_G F`, by `[p, v] ↦ [p, v]`
(`TauCeti.AssociatedBundle.coe_sphereBundleHomeomorph_mk`). -/
def sphereBundleHomeomorph :
    TotalSpace (sphere (0 : F) 1) (AssociatedBundle G P (sphere (0 : F) 1)) ≃ₜ
      sphereBundle F (AssociatedBundle G P F) :=
  (isEmbedding_totalSpaceMap _ Sphere.isEmbedding_subtypeMulActionHom).toHomeomorph.trans
    (Homeomorph.setCongr (range_totalSpaceMap_subtypeMulActionHom G P F))

/-- The homeomorphism `sphereBundleHomeomorph` is the map induced by the inclusion of the unit
sphere. -/
theorem coe_sphereBundleHomeomorph_apply
    (x : TotalSpace (sphere (0 : F) 1) (AssociatedBundle G P (sphere (0 : F) 1))) :
    (sphereBundleHomeomorph G P F x : TotalSpace F (AssociatedBundle G P F)) =
      totalSpaceMap (Sphere.subtypeMulActionHom G F 1) x := by
  (rfl)

/-- The homeomorphism `sphereBundleHomeomorph` sends `[p, v]` to `[p, v]`. -/
@[simp]
theorem coe_sphereBundleHomeomorph_mk {b : B} (p : P b) (v : sphere (0 : F) 1) :
    (sphereBundleHomeomorph G P F ⟨b, mk G p v⟩ : TotalSpace F (AssociatedBundle G P F)) =
      ⟨b, mk G p (v : F)⟩ := by
  rw [coe_sphereBundleHomeomorph_apply, totalSpaceMap_mk, Sphere.coe_subtypeMulActionHom]

/-- The inverse of `sphereBundleHomeomorph` sends a unit vector `[p, v]` to `[p, v]`. -/
@[simp]
theorem sphereBundleHomeomorph_symm_mk {b : B} (p : P b) (v : F)
    (hv : (⟨b, mk G p v⟩ : TotalSpace F (AssociatedBundle G P F)) ∈
      sphereBundle F (AssociatedBundle G P F)) :
    (sphereBundleHomeomorph G P F).symm ⟨⟨b, mk G p v⟩, hv⟩ =
      ⟨b, mk G p ⟨v, mem_sphere_zero_iff_norm.2 (by rwa [mem_sphereBundle, norm_mk] at hv)⟩⟩ := by
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (coe_sphereBundleHomeomorph_mk (G := G) (F := F) p ⟨v, _⟩).symm

/-- The homeomorphism `sphereBundleHomeomorph` lies over the base: it commutes with the
projections to `B`, the second one being `TauCeti.sphereBundleProj`. -/
@[simp]
theorem coe_sphereBundleHomeomorph_proj
    (x : TotalSpace (sphere (0 : F) 1) (AssociatedBundle G P (sphere (0 : F) 1))) :
    (sphereBundleHomeomorph G P F x : TotalSpace F (AssociatedBundle G P F)).proj = x.proj := by
  rw [coe_sphereBundleHomeomorph_apply, totalSpaceMap_proj]

/-- **The homeomorphism identifies the preferred charts.** Read in the preferred chart at any
point `i` of the base, `sphereBundleHomeomorph` is the inclusion of the unit sphere of the
fibre. -/
theorem trivializationAt_sphereBundleHomeomorph {i : B}
    {x : TotalSpace (sphere (0 : F) 1) (AssociatedBundle G P (sphere (0 : F) 1))}
    (hx : x.proj ∈ (trivializationAt G P i).baseSet) :
    trivializationAt F (AssociatedBundle G P F) i (sphereBundleHomeomorph G P F x) =
      (x.proj,
        ((trivializationAt (sphere (0 : F) 1) (AssociatedBundle G P (sphere (0 : F) 1)) i x).2 :
          F)) := by
  obtain ⟨b, v⟩ := x
  obtain ⟨p, v, rfl⟩ := exists_mk v
  rw [coe_sphereBundleHomeomorph_mk, trivializationAt_mk hx, trivializationAt_mk hx,
    Sphere.coe_smul_of_isIsometricSMul]

end TauCeti.AssociatedBundle
