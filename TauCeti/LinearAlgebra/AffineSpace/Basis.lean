/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Basis

/-!
# Affine equivalences between affine bases

Two affine bases indexed by the same type are related by an affine equivalence: there is an affine
equivalence sending the points of one basis to the corresponding points of the other
(`AffineBasis.exists_affineEquiv_apply_eq`), and every affine map that does so preserves
barycentric coordinates (`AffineBasis.coord_apply_of_forall_apply_eq`). This is how a statement
about barycentric coordinates relative to an arbitrary affine basis is reduced to one about a
fixed reference basis.

The file also computes the barycentric coordinates of a point after a homothety about the centroid
of an affine basis (`AffineBasis.coord_homothety_centroid`), which describes the homothetic images
of the simplex spanned by the basis.

## Main statements

* `AffineBasis.coord_apply_of_forall_apply_eq`: an affine map sending the affine basis `b` to the
  affine basis `b₂` carries barycentric coordinates relative to `b` to those relative to `b₂`;
* `AffineBasis.exists_affineEquiv_apply_eq`: there is an affine equivalence sending `b` to `b₂`;
* `AffineBasis.coord_homothety_centroid`: the barycentric coordinates of the image of a point under
  a homothety about the centroid of an affine basis.
-/

public section

namespace AffineBasis

variable {ι k V P V₂ P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] (b : AffineBasis ι k P)
  (b₂ : AffineBasis ι k P₂)

/-- An affine map sending each point `b i` of an affine basis to the point `b₂ i` of another affine
basis preserves barycentric coordinates. -/
theorem coord_apply_of_forall_apply_eq {f : P →ᵃ[k] P₂} (hf : ∀ i, f (b i) = b₂ i) (i : ι)
    (x : P) : b₂.coord i (f x) = b.coord i x := by
  have h : (b₂.coord i).comp f = b.coord i := by
    refine AffineMap.ext_on b.tot ?_
    rintro - ⟨j, rfl⟩
    rcases eq_or_ne i j with rfl | hij
    · simp [hf, coord_apply_eq]
    · simp [hf, coord_apply_ne _ hij]
  exact congr($h x)

/-- Two affine bases indexed by the same type are related by an affine equivalence sending each
point of the first basis to the corresponding point of the second. -/
theorem exists_affineEquiv_apply_eq : ∃ T : P ≃ᵃ[k] P₂, ∀ i, T (b i) = b₂ i := by
  obtain ⟨i₀⟩ := b.nonempty
  -- Translate `b i₀` to the origin, map the linear basis `b.basisOf i₀` to `b₂.basisOf i₀`, and
  -- translate the origin to `b₂ i₀`.
  let L : V ≃ₗ[k] V₂ := (b.basisOf i₀).equiv (b₂.basisOf i₀) (Equiv.refl _)
  refine ⟨((AffineEquiv.vaddConst k (b i₀)).symm.trans L.toAffineEquiv).trans
    (AffineEquiv.vaddConst k (b₂ i₀)), fun i => ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · simp
  · have hL : L (b i -ᵥ b i₀) = b₂ i -ᵥ b₂ i₀ := by
      rw [← b.basisOf_apply i₀ ⟨i, hi⟩, Module.Basis.equiv_apply, Equiv.refl_apply,
        basisOf_apply]
    simp [hL]

end AffineBasis

namespace AffineBasis

variable {ι k V P : Type*} [Fintype ι] [Field k] [CharZero k] [AddCommGroup V] [Module k V]
  [AddTorsor V P] (b : AffineBasis ι k P)

/-- The barycentric coordinates relative to an affine basis `b` of the image of a point `z` under
the homothety of ratio `t` about the centroid of `b`: the homothety moves each coordinate
`b.coord i z` towards the centroid's coordinate `1 / card ι` by the factor `t`. -/
theorem coord_homothety_centroid (t : k) (z : P) (i : ι) :
    b.coord i (AffineMap.homothety (Finset.univ.centroid k b) t z) =
      (1 - t) / Fintype.card ι + t * b.coord i z := by
  rw [AffineMap.homothety_eq_lineMap, AffineMap.apply_lineMap,
    b.coord_apply_centroid (Finset.mem_univ i), Finset.card_univ, AffineMap.lineMap_apply_ring']
  ring

end AffineBasis
