/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Assoc
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The product on the normalized cubical chains of a topological monoid

For a topological monoid `G`, the multiplication `G × G → G` and the cross product of normalized
cubical chains give the **Pontryagin product**
`a · b := mul_* (a × b) : C^□_{p + q}(G; R)` for `a ∈ C^□_p(G; R)` and `b ∈ C^□_q(G; R)`.  It is
strictly associative and strictly unital, with unit the `0`-cube at `1`, and the boundary is a
derivation for it with the Koszul sign.  These are the identities that make
`⨁_n C^□_n(G; R)` a differential graded algebra; the packaging as a graded algebra is done in a
separate file.

The statements are made at the level of the individual degrees, with the explicit reindexings
`(p + q) + r = p + (q + r)` and `0 + q = q = q + 0` (`NormalizedCubicalChain.cast`), exactly as
for the cross product.

## Main definitions

* `TauCeti.mulMap G`: the multiplication of a topological monoid as a continuous map `G × G → G`.
* `TauCeti.NormalizedCubicalChain.mul G R p q`: the product `C^□_p(G; R) ⊗ C^□_q(G; R) →
  C^□_{p + q}(G; R)`.
* `TauCeti.NormalizedCubicalChain.one G R`: the unit, the `0`-cube at `1`.

## Main results

* `TauCeti.NormalizedCubicalChain.mul_assoc`: strict associativity.
* `TauCeti.NormalizedCubicalChain.one_mul`, `TauCeti.NormalizedCubicalChain.mul_one`: strict units.
* `TauCeti.NormalizedCubicalChain.boundary_mul`: the Leibniz rule.
* `TauCeti.NormalizedCubicalChain.augment_mul`: the augmentation is multiplicative.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

section Casts

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace CubicalChain

variable (R : Type*) [Semiring R]

/-- Reindexing along successive dimension equalities is reindexing along their composite. -/
@[simp]
theorem cast_cast {n m k : ℕ} (h : n = m) (h' : m = k) (f : CubicalChain X R n) :
    cast R h' (cast R h f) = cast R (h.trans h') f := by
  induction f using Finsupp.induction_linear <;> simp_all

/-- Reindexing commutes with the push-forward. -/
theorem map_cast (f : C(X, Y)) {n m : ℕ} (h : n = m) (c : CubicalChain X R n) :
    map R f m (cast R h c) = cast R h (map R f n c) := by
  subst h
  simp

end CubicalChain

namespace NormalizedCubicalChain

variable (R : Type*) [CommRing R]

/-- Reindexing along successive dimension equalities is reindexing along their composite. -/
@[simp]
theorem cast_cast {n m k : ℕ} (h : n = m) (h' : m = k) (c : NormalizedCubicalChain X R n) :
    cast R h' (cast R h c) = cast R (h.trans h') c := by
  induction c using Submodule.Quotient.induction_on with
  | H c => simp

/-- Reindexing along `rfl` is the identity. -/
@[simp]
theorem cast_rfl {n : ℕ} (c : NormalizedCubicalChain X R n) : cast R rfl c = c := by
  induction c using Submodule.Quotient.induction_on with
  | H c => simp

/-- Pushing forward along a composite is pushing forward twice. -/
theorem map_comp_apply {Z : Type*} [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y)) (n : ℕ)
    (c : NormalizedCubicalChain X R n) :
    map R g n (map R f n c) = map R (g.comp f) n c := by
  rw [map_comp, LinearMap.comp_apply]

/-- Reindexing commutes with the push-forward. -/
theorem map_cast (f : C(X, Y)) {n m : ℕ} (h : n = m) (c : NormalizedCubicalChain X R n) :
    map R f m (cast R h c) = cast R h (map R f n c) := by
  subst h
  simp

/-- The cross product commutes with pushing forward the first factor. -/
theorem crossProduct_map_left {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W] {p q : ℕ}
    (R : Type*) [CommRing R] (f : C(X, Z)) (a : NormalizedCubicalChain X R p)
    (b : NormalizedCubicalChain W R q) :
    crossProduct Z W R p q (map R f p a) b =
      map R (f.prodMap (ContinuousMap.id W)) (p + q) (crossProduct X W R p q a b) := by
  rw [map_crossProduct, map_id, LinearMap.id_apply]

/-- The cross product commutes with pushing forward the second factor. -/
theorem crossProduct_map_right {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W] {p q : ℕ}
    (R : Type*) [CommRing R] (f : C(X, Z)) (a : NormalizedCubicalChain W R p)
    (b : NormalizedCubicalChain X R q) :
    crossProduct W Z R p q a (map R f q b) =
      map R ((ContinuousMap.id W).prodMap f) (p + q) (crossProduct W X R p q a b) := by
  rw [map_crossProduct, map_id, LinearMap.id_apply]

end NormalizedCubicalChain

end Casts

section Monoid

variable (G : Type*) [Monoid G] [TopologicalSpace G] [ContinuousMul G]

/-- The multiplication of a topological monoid as a continuous map `G × G → G`. -/
def mulMap : C(G × G, G) := ⟨fun x ↦ x.1 * x.2, continuous_mul⟩

@[simp]
theorem mulMap_apply (x : G × G) : mulMap G x = x.1 * x.2 :=
  (rfl)

namespace NormalizedCubicalChain

variable (R : Type*) [CommRing R]

/-- The **Pontryagin product** on normalized cubical chains of a topological monoid:
`a · b = mul_* (a × b)`. -/
def mul (p q : ℕ) :
    NormalizedCubicalChain G R p →ₗ[R] NormalizedCubicalChain G R q →ₗ[R]
      NormalizedCubicalChain G R (p + q) :=
  LinearMap.compr₂ (crossProduct G G R p q) (map R (mulMap G) (p + q))

/-- The unit of the Pontryagin product: the `0`-cube at `1`. -/
def one : NormalizedCubicalChain G R 0 := ofCube G R (SingularCube.point 1)

variable {G R}

/-- The product of two cubes is the class of the cube of products. -/
@[simp]
theorem mul_ofCube {p q : ℕ} (c : SingularCube G p) (d : SingularCube G q) :
    mul G R p q (ofCube G R c) (ofCube G R d) =
      ofCube G R ((mulMap G).comp (SingularCube.crossProduct c d)) := by
  simp [mul]

/-- **Strict associativity of the Pontryagin product**, after the reindexing
`(p + q) + r = p + (q + r)`. -/
theorem mul_assoc {p q r : ℕ} (a : NormalizedCubicalChain G R p) (b : NormalizedCubicalChain G R q)
    (c : NormalizedCubicalChain G R r) :
    cast R (Nat.add_assoc p q r) (mul G R (p + q) r (mul G R p q a b) c) =
      mul G R p (q + r) a (mul G R q r b c) := by
  have hZ := crossProduct_assoc R a b c
  -- `a × (b × c)` is the reindexed push-forward of `(a × b) × c` along the associator.
  have hW : crossProduct G (G × G) R p (q + r) a (crossProduct G G R q r b c) =
      cast R (Nat.add_assoc p q r)
        (map R (assocMap G G G) (p + q + r)
          (crossProduct (G × G) G R (p + q) r (crossProduct G G R p q a b) c)) := by
    rw [hZ, cast_cast, cast_rfl]
  have key : (mulMap G).comp ((mulMap G).prodMap (ContinuousMap.id G)) =
      (mulMap G).comp (((ContinuousMap.id G).prodMap (mulMap G)).comp (assocMap G G G)) := by
    ext x
    simp [_root_.mul_assoc]
  simp only [mul, LinearMap.compr₂_apply]
  rw [crossProduct_map_left, crossProduct_map_right, hW, map_cast, map_cast]
  simp only [map_comp_apply, key]

/-- **The unit is a left unit**, after the reindexing `0 + q = q`. -/
theorem one_mul {q : ℕ} (b : NormalizedCubicalChain G R q) :
    cast R (Nat.zero_add q) (mul G R 0 q (one G R) b) = b := by
  have h : (mulMap G).comp
      (ContinuousMap.prodMk (ContinuousMap.const G (1 : G)) (ContinuousMap.id G)) =
        ContinuousMap.id G := by
    ext x
    simp
  simp only [mul, one, LinearMap.compr₂_apply]
  rw [← map_cast, crossProduct_point_left, map_comp_apply, h, map_id, LinearMap.id_apply]

/-- **The unit is a right unit**, after the reindexing `p + 0 = p`. -/
theorem mul_one {p : ℕ} (a : NormalizedCubicalChain G R p) :
    cast R (Nat.add_zero p) (mul G R p 0 a (one G R)) = a := by
  have h : (mulMap G).comp
      (ContinuousMap.prodMk (ContinuousMap.id G) (ContinuousMap.const G (1 : G))) =
        ContinuousMap.id G := by
    ext x
    simp
  simp only [mul, one, LinearMap.compr₂_apply]
  rw [← map_cast, crossProduct_point_right, map_comp_apply, h, map_id, LinearMap.id_apply]

/-- **The Leibniz rule for the Pontryagin product**: for `a` of degree `p + 1` and `b` of degree
`q + 1`, `∂ (a · b) = ∂ a · b + (-1) ^ (p + 1) • (a · ∂ b)`, in degree `p + q + 1`. -/
theorem boundary_mul {p q : ℕ} (a : NormalizedCubicalChain G R (p + 1))
    (b : NormalizedCubicalChain G R (q + 1)) :
    boundary G R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1) (mul G R (p + 1) (q + 1) a b)) =
      mul G R p (q + 1) (boundary G R p a) b +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (mul G R (p + 1) q a (boundary G R q b)) := by
  simp only [mul, LinearMap.compr₂_apply]
  rw [← map_cast, ← LinearMap.comp_apply (boundary G R _), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct, map_add, map_smul, map_cast]
  rfl

/-- **The augmentation is multiplicative** on the Pontryagin product of `0`-chains. -/
theorem augment_mul (a b : NormalizedCubicalChain G R 0) :
    augment G R (mul G R 0 0 a b) = augment G R a * augment G R b := by
  simp only [mul, LinearMap.compr₂_apply]
  rw [← LinearMap.comp_apply (augment G R), augment_map, augment_crossProduct]

end NormalizedCubicalChain

end Monoid

end TauCeti

end
