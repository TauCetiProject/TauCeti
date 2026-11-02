/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.LensSpace.FundamentalGroup
public import TauCeti.Geometry.Manifold.Instances.LensSpace
public import TauCeti.LowDimTopology.Heegaard.Clifford
public import TauCeti.LowDimTopology.Heegaard.FundamentalGroup
public import TauCeti.LowDimTopology.Heegaard.LensSpace.Embedding
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# The genus-one Heegaard splitting of a lens space

The three-dimensional lens space `L(m; ℓ₀, ℓ₁)` is the orbit space of the unit sphere
`S³ = {(z, w) | ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1}` of `ℂ²` under the rotations
`(z, w) ↦ (ζ ^ ℓ₀ z, ζ ^ ℓ₁ w)`, `ζ ^ m = 1`. The rotations preserve the two solid tori
`‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖` of the genus-one Heegaard splitting of `S³`
(`TauCeti.cliffordHeegaardSplitting`), so their images are two pieces covering the lens space and
meeting along the image of the Clifford torus. Each image is again a solid torus. On
`‖z‖ ≤ ‖w‖` the rotation acts on the coordinates `(u, v) = (z / ‖w‖, w / ‖w‖) ∈ D² × S¹`
(`TauCeti.sphereProdFstLeHomeomorph`) by
`(u, v) ↦ (ζ ^ ℓ₀ u, ζ ^ ℓ₁ v)`, freely on the core circle. The closed embeddings
`TauCeti.LensSpace.leftEmbedding` and `TauCeti.LensSpace.rightEmbedding` parametrize the two
quotient handlebodies by `D² × S¹`. This gives the genus-one Heegaard splitting
`TauCeti.LensSpace.heegaardSplitting` of `L(m; ℓ₀, ℓ₁)`.

The splitting is obtained by descending the splitting of the sphere along the projection, an open
quotient map for which both solid tori are saturated
(`TauCeti.HeegaardSplitting.ofIsOpenQuotientMap`).

Since the fundamental group `ℤ/m` of a lens space with `m ≠ 1` is nontrivial, and its rank is at
most the Heegaard genus (`TauCeti.rank_fundamentalGroup_le_heegaardGenus`), such a lens space has
Heegaard genus exactly one, and its Heegaard genus equals the rank of its fundamental group, as in
Waldhausen's rank-versus-genus conjecture (`TauCeti.RankGenusConjecture`).

## Main definitions

* `TauCeti.LensSpace.heegaardSplitting`: the genus-one Heegaard splitting of `L(m; ℓ₀, ℓ₁)` into
  the images of the solid tori `‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖`.

## Main results

* `TauCeti.LensSpace.rank_fundamentalGroup_eq_one`: for `m ≠ 1`, the fundamental group of
  `L(m; ℓ₀, ℓ₁)` has rank one.
* `TauCeti.LensSpace.heegaardGenus_eq_one`: a lens space `L(m; ℓ₀, ℓ₁)` with `m ≠ 1` has Heegaard
  genus one.
* `TauCeti.LensSpace.heegaardGenus_eq_rank`: its Heegaard genus is the rank of its fundamental
  group.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (lens spaces as unions of two
  solid tori).
* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, in *Handbook of Geometric
  Topology*, North-Holland (2002), Section 2.
-/

public section

noncomputable section

open Metric Set Module Function

namespace TauCeti

namespace LensSpace

variable (m : ℕ) [NeZero m] (ℓ : Fin 2 → (ZMod m)ˣ)

/-- The solid torus `‖x i‖ ≤ ‖x j‖` of the unit sphere of `ℂ²`. -/
private def piece (i j : Fin 2) : Set (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  {x | ‖(x : EuclideanSpace ℂ (Fin 2)) i‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) j‖}

/-- The solid tori are saturated for the projection to the lens space. -/
private theorem preimage_image_piece (i j : Fin 2) :
    mk m ℓ ⁻¹' (mk m ℓ '' piece i j) = piece i j := by
  refine (subset_preimage_image _ _).antisymm' ?_
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff m ℓ y x).1 hxy
  simpa [piece, ← ha] using hy

/-- The canonical integral twist for the handlebody with disc coordinate `i` and core `j`. -/
private theorem exists_twist (i j : Fin 2) : ∃ e : ℤ, (e : ZMod m) * ℓ j = ℓ i := by
  refine ⟨((ℓ i * (ℓ j)⁻¹ : (ZMod m)ˣ) : ZMod m).val, ?_⟩
  simp [Units.val_mul]

/-- The range of a solid-torus closed embedding is a genus-one handlebody. -/
private theorem nonempty_homeomorph_range (f : C(SolidTorus, LensSpace m ℓ))
    (hf : Topology.IsClosedEmbedding f) : Nonempty (range f ≃ₜ handlebody 1) :=
  ⟨hf.isEmbedding.toHomeomorph.symm.trans nonempty_homeomorph_handlebody_one.some.symm⟩

/-! ### The genus-one splitting -/

/-- The genus-one Heegaard splitting of the unit sphere of `ℂ²` into the solid tori `‖x 0‖ ≤ ‖x 1‖`
and `‖x 1‖ ≤ ‖x 0‖`, transported from `TauCeti.cliffordHeegaardSplitting`. -/
private def sphereHeegaardSplitting : HeegaardSplitting (sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  cliffordHeegaardSplitting.transHomeomorph
    ((EuclideanSpace.finTwoEquivProd ℂ).unitSphereIsometryEquiv.toHomeomorph.symm)

private theorem sphereHeegaardSplitting_left : sphereHeegaardSplitting.left = piece 0 1 := by
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_left, Homeomorph.image_symm]
  ext x
  simp [piece]

private theorem sphereHeegaardSplitting_right : sphereHeegaardSplitting.right = piece 1 0 := by
  rw [sphereHeegaardSplitting, HeegaardSplitting.transHomeomorph_right, Homeomorph.image_symm]
  ext x
  simp [piece]

/-- **The genus-one Heegaard splitting of a lens space.** The lens space `L(m; ℓ₀, ℓ₁)` is the
union of the images of the solid tori `‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖` of the unit sphere of `ℂ²`,
which are solid tori meeting along the image of the Clifford torus `‖z‖ = ‖w‖`. -/
def heegaardSplitting : HeegaardSplitting (LensSpace m ℓ) :=
  sphereHeegaardSplitting.ofIsOpenQuotientMap (isOpenQuotientMap_mk m ℓ)
    (by rw [sphereHeegaardSplitting_left]; exact preimage_image_piece m ℓ 0 1)
    (by rw [sphereHeegaardSplitting_right]; exact preimage_image_piece m ℓ 1 0) 1
    (by
      obtain ⟨e, he⟩ := exists_twist m ℓ 0 1
      rw [sphereHeegaardSplitting_left, piece, ← range_leftEmbedding he]
      exact nonempty_homeomorph_range m ℓ _ (isClosedEmbedding_leftEmbedding he))
    (by
      obtain ⟨e, he⟩ := exists_twist m ℓ 1 0
      rw [sphereHeegaardSplitting_right, piece, ← range_rightEmbedding he]
      exact nonempty_homeomorph_range m ℓ _ (isClosedEmbedding_rightEmbedding he))

@[simp] theorem heegaardSplitting_genus : (heegaardSplitting m ℓ).genus = 1 :=
  HeegaardSplitting.ofIsOpenQuotientMap_genus _ _ _ _ _ _ _

@[simp]
theorem heegaardSplitting_left :
    (heegaardSplitting m ℓ).left =
      mk m ℓ '' {x | ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖} := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsOpenQuotientMap_left, sphereHeegaardSplitting_left,
    piece]

@[simp]
theorem heegaardSplitting_right :
    (heegaardSplitting m ℓ).right =
      mk m ℓ '' {x | ‖(x : EuclideanSpace ℂ (Fin 2)) 1‖ ≤ ‖(x : EuclideanSpace ℂ (Fin 2)) 0‖} := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsOpenQuotientMap_right,
    sphereHeegaardSplitting_right, piece]

instance : Nonempty (HeegaardSplitting (LensSpace m ℓ)) := ⟨heegaardSplitting m ℓ⟩

/-- A lens space `L(m; ℓ₀, ℓ₁)` has Heegaard genus at most one. -/
theorem heegaardGenus_le_one : heegaardGenus (LensSpace m ℓ) ≤ 1 :=
  (heegaardGenus_le (heegaardSplitting m ℓ)).trans_eq (heegaardSplitting_genus m ℓ)

/-- The fundamental group of a lens space `L(m; ℓ₀, ℓ₁)` is finitely generated. -/
instance fg_fundamentalGroup (x : LensSpace m ℓ) : Group.FG (FundamentalGroup (LensSpace m ℓ) x) :=
  (heegaardSplitting m ℓ).fg_fundamentalGroup (E := EuclideanSpace ℝ (Fin 3)) (by simp) x

/-- For `m ≠ 1`, the fundamental group `ℤ/m` of a lens space `L(m; ℓ₀, ℓ₁)` has rank one: it is
nontrivial, while its rank is at most the Heegaard genus, which is at most one. -/
theorem rank_fundamentalGroup_eq_one (hm : m ≠ 1) (x : LensSpace m ℓ) :
    Group.rank (FundamentalGroup (LensSpace m ℓ) x) = 1 := by
  have := nontrivial_fundamentalGroup m ℓ le_rfl hm x
  have h := rank_fundamentalGroup_le_heegaardGenus (E := EuclideanSpace ℝ (Fin 3)) (by simp) x
  have h0 : Group.rank (FundamentalGroup (LensSpace m ℓ) x) ≠ 0 := by
    rw [Ne, Group.rank_eq_zero_iff]
    exact not_subsingleton _
  have := heegaardGenus_le_one m ℓ
  omega

/-- **A lens space `L(m; ℓ₀, ℓ₁)` with `m ≠ 1` has Heegaard genus one.** It has a splitting of
genus one, and none of genus zero, since its fundamental group `ℤ/m` has rank one while its rank is
at most the Heegaard genus. -/
theorem heegaardGenus_eq_one (hm : m ≠ 1) : heegaardGenus (LensSpace m ℓ) = 1 := by
  let x : LensSpace m ℓ := Classical.arbitrary _
  refine le_antisymm (heegaardGenus_le_one m ℓ) ?_
  exact (rank_fundamentalGroup_eq_one m ℓ hm x).ge.trans
    (rank_fundamentalGroup_le_heegaardGenus (E := EuclideanSpace ℝ (Fin 3)) (by simp) x)

/-- **A lens space satisfies Waldhausen's equation**: for `m ≠ 1`, the Heegaard genus of
`L(m; ℓ₀, ℓ₁)` equals the rank of its fundamental group, both being one. -/
theorem heegaardGenus_eq_rank (hm : m ≠ 1) (x : LensSpace m ℓ) :
    heegaardGenus (LensSpace m ℓ) = Group.rank (FundamentalGroup (LensSpace m ℓ) x) := by
  rw [heegaardGenus_eq_one m ℓ hm, rank_fundamentalGroup_eq_one m ℓ hm x]

end LensSpace

end TauCeti
