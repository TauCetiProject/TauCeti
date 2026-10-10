/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Chains
public import TauCeti.AlgebraicTopology.Singular.Cubical.Augment

/-!
# Associativity and units of the cubical cross product

The cross product of cubical chains of
`TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Chains` is **strictly associative** and
**strictly unital**: no shuffle or Eilenberg–Zilber correction is needed.

* Associativity is an equality of chains in `X × Y × Z` of dimension `(p + q) + r`, after pushing
  `(a × b) × c` forward along the associator `(X × Y) × Z ≃ₜ X × Y × Z` and reindexing
  `p + (q + r) = (p + q) + r` (`CubicalChain.crossProduct_assoc`).
* A `0`-cube `point x` at a point `x` is a unit up to the maps `y ↦ (x, y)` and `y ↦ (y, x)`
  (`CubicalChain.crossProduct_point_left`, `CubicalChain.crossProduct_point_right`), in particular
  `PUnit × X ≅ X ≅ X × PUnit` (`CubicalChain.crossProduct_punit_left`).
* The augmentation is multiplicative (`CubicalChain.augment_crossProduct`).

All three statements hold on normalized chains as well.

## Main definitions

* `TauCeti.SingularCube.point`: the `0`-cube at a point.
* `TauCeti.assocMap`: the associator `(X × Y) × Z → X × Y × Z` as a continuous map.

## Main results

* `TauCeti.CubicalChain.crossProduct_assoc`, `TauCeti.NormalizedCubicalChain.crossProduct_assoc`.
* `TauCeti.CubicalChain.crossProduct_point_left`, `TauCeti.CubicalChain.crossProduct_point_right`
  and their normalized versions.
* `TauCeti.CubicalChain.augment_crossProduct`,
  `TauCeti.NormalizedCubicalChain.augment_crossProduct`.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (X Y Z) in
/-- The associator `(X × Y) × Z → X × Y × Z` as a continuous map. -/
def assocMap : C((X × Y) × Z, X × Y × Z) := (Homeomorph.prodAssoc X Y Z : C((X × Y) × Z, X × Y × Z))

namespace SingularCube

/-- The `0`-cube at a point. -/
def point (x : X) : SingularCube X 0 := ContinuousMap.const _ x

@[simp]
theorem point_apply (x : X) (t : Fin 0 → I) : point x t = x :=
  (rfl)

/-- The cross product of cubes is associative, as a cube in `X × Y × Z`. -/
theorem map_assocMap_crossProduct {p q r : ℕ} (c : SingularCube X p) (d : SingularCube Y q)
    (e : SingularCube Z r) :
    (assocMap X Y Z).comp (crossProduct (crossProduct c d) e) =
      cast (Nat.add_assoc p q r).symm (crossProduct c (crossProduct d e)) :=
  (crossProduct_assoc c d e).symm

/-- A point on the left is a unit for the cross product of cubes, up to reindexing. -/
theorem cast_crossProduct_point_left {q : ℕ} (x : X) (d : SingularCube Y q) :
    cast (Nat.zero_add q) (crossProduct (point x) d) =
      (ContinuousMap.prodMk (ContinuousMap.const Y x) (ContinuousMap.id Y)).comp d := by
  apply ContinuousMap.ext
  intro t
  rw [cast_apply, crossProduct_zero_left]
  rfl

/-- A point on the right is a unit for the cross product of cubes, up to reindexing. -/
theorem cast_crossProduct_point_right {p : ℕ} (c : SingularCube X p) (y : Y) :
    cast (Nat.add_zero p) (crossProduct c (point y)) =
      (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y)).comp c := by
  apply ContinuousMap.ext
  intro t
  rw [cast_apply, crossProduct_zero_right]
  rfl

end SingularCube

namespace CubicalChain

variable {p q r : ℕ} (R : Type*) [CommSemiring R]

/-- **Strict associativity of the cross product**: `(a × b) × c = a × (b × c)`, after the
associator of the spaces and the reindexing `p + (q + r) = (p + q) + r`. -/
theorem crossProduct_assoc (a : CubicalChain X R p) (b : CubicalChain Y R q)
    (c : CubicalChain Z R r) :
    map R (assocMap X Y Z) (p + q + r)
        (crossProduct (X × Y) Z R (p + q) r (crossProduct X Y R p q a b) c) =
      cast R (Nat.add_assoc p q r).symm
        (crossProduct X (Y × Z) R p (q + r) a (crossProduct Y Z R q r b c)) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single c₁ s₁ =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, LinearMap.add_apply, hb, hb']
    | single c₂ s₂ =>
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c c' hc hc' => simp only [map_add, hc, hc']
      | single c₃ s₃ =>
        simp only [crossProduct_single, map_single, cast_single, mul_assoc]
        rw [SingularCube.map_assocMap_crossProduct]

/-- A point on the left is a unit for the cross product of chains: the cross product with the
`0`-cube at `x` is the push-forward along `y ↦ (x, y)`, up to reindexing `0 + q = q`. -/
theorem crossProduct_point_left (x : X) (b : CubicalChain Y R q) :
    cast R (Nat.zero_add q)
        (crossProduct X Y R 0 q (single (SingularCube.point x) 1) b) =
      map R (ContinuousMap.prodMk (ContinuousMap.const Y x) (ContinuousMap.id Y)) q b := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b b' hb hb' => simp only [map_add, hb, hb']
  | single d s =>
    simp only [crossProduct_single, cast_single, map_single, one_mul,
      SingularCube.cast_crossProduct_point_left]

/-- A point on the right is a unit for the cross product of chains: the cross product with the
`0`-cube at `y` is the push-forward along `x ↦ (x, y)`, up to reindexing `p + 0 = p`. -/
theorem crossProduct_point_right (a : CubicalChain X R p) (y : Y) :
    cast R (Nat.add_zero p)
        (crossProduct X Y R p 0 a (single (SingularCube.point y) 1)) =
      map R (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y)) p a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single c s =>
    simp only [crossProduct_single, cast_single, map_single, mul_one,
      SingularCube.cast_crossProduct_point_right]

/-- The cross product with the `0`-cube of the point `PUnit` is the identity, up to the
identification `PUnit × Y ≅ Y` and the reindexing `0 + q = q`. -/
theorem crossProduct_punit_left (b : CubicalChain Y R q) :
    map R (ContinuousMap.snd : C(PUnit × Y, Y)) q
        (cast R (Nat.zero_add q)
          (crossProduct PUnit Y R 0 q (single (SingularCube.point PUnit.unit) 1) b)) = b := by
  have h : (ContinuousMap.snd : C(PUnit × Y, Y)).comp
      (ContinuousMap.prodMk (ContinuousMap.const Y PUnit.unit) (ContinuousMap.id Y)) =
        ContinuousMap.id Y := by
    ext; rfl
  rw [crossProduct_point_left, ← LinearMap.comp_apply, ← map_comp R _ _ q, h, map_id,
    LinearMap.id_apply]

/-- The cross product with the `0`-cube of the point `PUnit` is the identity, up to the
identification `X × PUnit ≅ X` and the reindexing `p + 0 = p`. -/
theorem crossProduct_punit_right (a : CubicalChain X R p) :
    map R (ContinuousMap.fst : C(X × PUnit, X)) p
        (cast R (Nat.add_zero p)
          (crossProduct X PUnit R p 0 a (single (SingularCube.point PUnit.unit) 1))) = a := by
  have h : (ContinuousMap.fst : C(X × PUnit, X)).comp
      (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X PUnit.unit)) =
        ContinuousMap.id X := by
    ext; rfl
  rw [crossProduct_point_right, ← LinearMap.comp_apply, ← map_comp R _ _ p, h, map_id,
    LinearMap.id_apply]

/-- **The augmentation is multiplicative** on the cross product of `0`-chains. -/
theorem augment_crossProduct (a : CubicalChain X R 0) (b : CubicalChain Y R 0) :
    augment (X × Y) R (crossProduct X Y R 0 0 a b) = augment X R a * augment Y R b := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha', add_mul]
  | single c s =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, hb, hb', mul_add]
    | single d t =>
      rw [crossProduct_single, augment_single, augment_single, augment_single]

end CubicalChain

namespace NormalizedCubicalChain

open CubicalChain

variable {p q r : ℕ} (R : Type*) [CommRing R]

/-- **Strict associativity of the cross product** of normalized chains, after the associator of
the spaces and the reindexing `p + (q + r) = (p + q) + r`. -/
theorem crossProduct_assoc (a : NormalizedCubicalChain X R p) (b : NormalizedCubicalChain Y R q)
    (c : NormalizedCubicalChain Z R r) :
    map R (assocMap X Y Z) (p + q + r)
        (crossProduct (X × Y) Z R (p + q) r (crossProduct X Y R p q a b) c) =
      cast R (Nat.add_assoc p q r).symm
        (crossProduct X (Y × Z) R p (q + r) a (crossProduct Y Z R q r b c)) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      induction c using Submodule.Quotient.induction_on with
      | H c =>
        rw [crossProduct_mk, crossProduct_mk, crossProduct_mk, crossProduct_mk, map_mk, cast_mk,
          CubicalChain.crossProduct_assoc]

/-- A point on the left is a unit for the cross product of normalized chains. -/
theorem crossProduct_point_left (x : X) (b : NormalizedCubicalChain Y R q) :
    cast R (Nat.zero_add q) (crossProduct X Y R 0 q (ofCube X R (SingularCube.point x)) b) =
      map R (ContinuousMap.prodMk (ContinuousMap.const Y x) (ContinuousMap.id Y)) q b := by
  induction b using Submodule.Quotient.induction_on with
  | H b =>
    rw [ofCube_def, crossProduct_mk, cast_mk, map_mk, CubicalChain.crossProduct_point_left]

/-- A point on the right is a unit for the cross product of normalized chains. -/
theorem crossProduct_point_right (a : NormalizedCubicalChain X R p) (y : Y) :
    cast R (Nat.add_zero p) (crossProduct X Y R p 0 a (ofCube Y R (SingularCube.point y))) =
      map R (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y)) p a := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    rw [ofCube_def, crossProduct_mk, cast_mk, map_mk, CubicalChain.crossProduct_point_right]

/-- **The augmentation is multiplicative** on the cross product of normalized `0`-chains. -/
theorem augment_crossProduct (a : NormalizedCubicalChain X R 0)
    (b : NormalizedCubicalChain Y R 0) :
    augment (X × Y) R (crossProduct X Y R 0 0 a b) = augment X R a * augment Y R b := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      rw [crossProduct_mk, augment_mk, augment_mk, augment_mk, CubicalChain.augment_crossProduct]

end NormalizedCubicalChain

end TauCeti

end
