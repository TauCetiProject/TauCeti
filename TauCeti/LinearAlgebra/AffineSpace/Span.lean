/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Projection

/-!
# Directions of affine spans under affine maps

The direction of the affine span of an image is the linear image of the original
direction. This formula supports transport of transversality and codimension
without requiring an invertible map or a nonempty set.
A linear map whose kernel contains the direction of a set is constant on it.
Equality of affine spans transfers tangency between level hyperplanes.
Adding unrestricted coordinates preserves and reflects equality of affine spans.
For nonempty sets it also preserves and reflects equality of their directions.

Over a division ring, a surjective linear map `A : V → V'` is the first coordinate of a linear
equivalence `V ≃ V' × ker A`, which carries the preimage `A⁻¹(S)` to the cylinder
`S × ker A`. Hence the direction of the affine span of a nonempty preimage is the preimage of
the direction. The splitting uses Mathlib's `LinearMap.equivProdOfSurjectiveOfIsCompl` and
`Submodule.projectionOnto`.

## Main results

* `AffineMap.direction_affineSpan_image`: affine maps transport the direction of an affine span by
  their linear part.
* `LinearMap.direction_affineSpan_preimage`: under a linear surjection, the direction of the affine
  span of the preimage of a nonempty set is the preimage of its direction.
* `TauCeti.affineSpan_prod_univ_eq_iff` and `TauCeti.direction_affineSpan_prod_univ_eq_iff`:
  adding unrestricted coordinates preserves and reflects equality of affine spans and of their
  directions.
* `LinearMap.map_eq_zero_of_affineSpan_eq`: equality of affine spans transfers tangency between
  level hyperplanes.

These transport affine directions, and hence transversality of a segment to a wall, along
affine maps, linear surjections and products.

## Attribution

Adapted from `Mei/Geometry/Affine/Span.lean` in Mei at commit
`68536122a97fed8e87bc6870b9427151971b9ab2`. Original copyright and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/68536122a97fed8e87bc6870b9427151971b9ab2/Mei/Geometry/Affine/Span.lean
-/

public section

namespace LinearMap

/-- A linear map whose kernel contains the direction of a set is constant on that set. -/
theorem apply_eq_of_direction_le_ker {K V W : Type*} [Ring K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) {P : Set V}
    (hf : (affineSpan K P).direction ≤ f.ker) {x y : V} (hx : x ∈ P) (hy : y ∈ P) :
    f x = f y := by
  have hd := hf (AffineSubspace.vsub_mem_direction (subset_affineSpan K P hx)
    (subset_affineSpan K P hy))
  rwa [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at hd

/-- If two sets share an affine span and the first has constant height for `f`,
a displacement tangent to the second at a point of the first is tangent for `f`. -/
theorem map_eq_zero_of_affineSpan_eq {K V : Type*} [Ring K] [AddCommGroup V] [Module K V]
    {W₁ W₂ : Set V} (f ν : V →ₗ[K] K) {c b : K}
    (hheight : ∀ x ∈ W₁, f x = c) (hspan : (affineSpan K W₂ : Set V) = {x | ν x = b})
    (heq : affineSpan K W₁ = affineSpan K W₂) {y q : V} (hy : y ∈ W₁) (hq : ν q = 0) :
    f q = 0 := by
  have hyν : ν y = b := (hspan.subset) (heq ▸ subset_affineSpan K _ hy)
  have hyq : y + q ∈ affineSpan K W₁ := by
    rw [heq]
    apply hspan.symm.subset
    simpa only [Set.mem_ofPred_eq, map_add, hq, add_zero] using hyν
  have hh := AffineMap.eqOn_affineSpan
    (f := f.toAffineMap) (g := AffineMap.const K V c) hheight hyq
  simpa only [LinearMap.coe_toAffineMap, AffineMap.const_apply, map_add,
    hheight _ hy, add_eq_left] using hh

end LinearMap

namespace AffineMap

variable {k V V' P P' : Type*} [Ring k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup V'] [Module k V'] [AddTorsor V' P']

/-- Affine maps transport the direction of an affine span by their linear part. -/
theorem direction_affineSpan_image (f : P →ᵃ[k] P') (s : Set P) :
    (affineSpan k (f '' s)).direction = (affineSpan k s).direction.map f.linear := by
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]

end AffineMap

namespace TauCeti

section Prod

variable {k V E P Q : Type*} [Ring k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup E] [Module k E] [AddTorsor E Q]

/-- Adding an unrestricted factor preserves and reflects equality of affine spans,
including for empty sets. -/
theorem affineSpan_prod_univ_eq_iff (s t : Set P) :
    affineSpan k (s ×ˢ (Set.univ : Set Q)) = affineSpan k (t ×ˢ (Set.univ : Set Q)) ↔
      affineSpan k s = affineSpan k t := by
  classical
  let q₀ : Q := Classical.arbitrary Q
  rw [affineSpan_prod_eq, affineSpan_prod_eq, AffineSubspace.span_univ]
  constructor
  · intro h
    ext p
    have := congrArg (fun A : AffineSubspace k (P × Q) => (p, q₀) ∈ A) h
    simpa using this
  · exact fun h => congrArg (fun A : AffineSubspace k P => A.prod ⊤) h

/-- The direction of the affine span of a nonempty cylinder has an unrestricted
second factor. Nonemptiness is needed because the empty span has zero direction. -/
theorem direction_affineSpan_prod_univ {s : Set P} (hs : s.Nonempty) :
    (affineSpan k (s ×ˢ (Set.univ : Set Q))).direction =
      (affineSpan k s).direction.prod ⊤ := by
  rw [direction_affineSpan, vectorSpan_prod_eq hs Set.univ_nonempty]
  rw [← direction_affineSpan, ← direction_affineSpan, AffineSubspace.span_univ,
    AffineSubspace.direction_top]

/-- Adding unrestricted coordinates preserves and reflects equality of supporting
directions for nonempty sets. -/
theorem direction_affineSpan_prod_univ_eq_iff {s t : Set P}
    (hs : s.Nonempty) (ht : t.Nonempty) :
    (affineSpan k (s ×ˢ (Set.univ : Set Q))).direction =
      (affineSpan k (t ×ˢ (Set.univ : Set Q))).direction ↔
      (affineSpan k s).direction = (affineSpan k t).direction := by
  rw [direction_affineSpan_prod_univ hs, direction_affineSpan_prod_univ ht]
  constructor
  · intro h
    ext v
    have := congrArg (fun S : Submodule k (V × E) => (v, 0) ∈ S) h
    simpa using this
  · exact fun h => congrArg (fun S : Submodule k V => S.prod (⊤ : Submodule k E)) h

end Prod
end TauCeti

namespace LinearMap

open Set

variable {K V V' : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] (A : V →ₗ[K] V') (hA : Function.Surjective A)

/-- A surjective linear map is the first coordinate of a linear equivalence with the product
of its target and its kernel. The kernel coordinate is the projection along a chosen
complement. -/
noncomputable def prodKerEquiv : V ≃ₗ[K] V' × LinearMap.ker A :=
  A.equivProdOfSurjectiveOfIsCompl
    (Submodule.projectionOnto (LinearMap.ker A)
      (Submodule.exists_isCompl (LinearMap.ker A)).choose
      (Submodule.exists_isCompl (LinearMap.ker A)).choose_spec)
    (LinearMap.range_eq_top.mpr hA) (Submodule.range_projectionOnto _)
    (by
      rw [Submodule.ker_projectionOnto]
      exact (Submodule.exists_isCompl (LinearMap.ker A)).choose_spec)

/-- The first coordinate of the splitting is the surjection itself. -/
@[simp]
theorem prodKerEquiv_apply_fst (x : V) : (A.prodKerEquiv hA x).1 = A x := (rfl)

/-- The first coordinate of the inverse splitting is recovered by the surjection. -/
@[simp]
theorem apply_prodKerEquiv_symm (z : V' × LinearMap.ker A) :
    A ((A.prodKerEquiv hA).symm z) = z.1 := by
  rw [← prodKerEquiv_apply_fst A hA, LinearEquiv.apply_symm_apply]

/-- The splitting carries the preimage of a set to the cylinder over that set. -/
theorem image_prodKerEquiv_preimage (S : Set V') :
    A.prodKerEquiv hA '' (A ⁻¹' S) = S ×ˢ (univ : Set (LinearMap.ker A)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa using hx, mem_univ _⟩
  · intro hz
    exact ⟨(A.prodKerEquiv hA).symm z, by simpa using hz.1,
      (A.prodKerEquiv hA).apply_symm_apply z⟩

/-- The inverse splitting carries the cylinder over a set to its preimage. -/
theorem image_prodKerEquiv_symm_prod_univ (S : Set V') :
    (A.prodKerEquiv hA).symm '' (S ×ˢ (univ : Set (LinearMap.ker A))) = A ⁻¹' S := by
  rw [← A.image_prodKerEquiv_preimage hA S]
  exact (A.prodKerEquiv hA).toEquiv.symm_image_image _

include hA in
/-- The supporting direction of a preimage of a nonempty set under a linear surjection is
the preimage of the original supporting direction. -/
theorem direction_affineSpan_preimage {S : Set V'} (hS : S.Nonempty) :
    (affineSpan K (A ⁻¹' S)).direction = (affineSpan K S).direction.comap A := by
  have he := AffineMap.direction_affineSpan_image
    (A.prodKerEquiv hA).symm.toLinearMap.toAffineMap (S ×ˢ (univ : Set (LinearMap.ker A)))
  rw [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe, A.image_prodKerEquiv_symm_prod_univ hA,
    TauCeti.direction_affineSpan_prod_univ hS] at he
  rw [he]
  ext v
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_prod, Submodule.mem_top,
    and_true, LinearMap.toAffineMap_linear, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro hv
    exact ⟨A.prodKerEquiv hA v, by simpa using hv, by simp⟩

end LinearMap
