/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Assoc
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The product on the normalized cubical chains of a topological monoid

For a topological monoid `G`, the multiplication `G × G → G` and the cross product of normalized
cubical chains give the **Pontryagin product**
`a · b := mul_* (a × b) : C^□_{p + q}(G; R)` for `a ∈ C^□_p(G; R)` and `b ∈ C^□_q(G; R)`.  It is
strictly associative and strictly unital, with unit the `0`-cube at `1`, and the boundary is a
derivation for it with the Koszul sign.  These are the multiplication, the unit and the Leibniz
rule that make `⨁_n C^□_n(G; R)` a differential graded algebra.

The product, the Leibniz rule and the augmentation only use a continuous multiplication; the unit
only uses a distinguished element; associativity and the unit laws use the corresponding monoid
axioms.

The statements are made at the level of the individual degrees, with the explicit reindexings
`(p + q) + r = p + (q + r)` and `0 + q = q = q + 0` (`NormalizedCubicalChain.cast`), exactly as
for the cross product.

## Main definitions

* `TauCeti.mulMap G`: the multiplication of a topological monoid as a continuous map `G × G → G`.
* `TauCeti.NormalizedCubicalChain.mul G R p q`: the product `C^□_p(G; R) ⊗ C^□_q(G; R) →
  C^□_{p + q}(G; R)`.
* `TauCeti.NormalizedCubicalChain.one G R`: the unit, the `0`-cube at `1`.

## Main results

* `TauCeti.NormalizedCubicalChain.mul_def`, `TauCeti.NormalizedCubicalChain.one_def`: the product
  is `mul_* (a × b)` and the unit is the class of the `0`-cube at `1`.
* `TauCeti.NormalizedCubicalChain.mul_assoc`: strict associativity.
* `TauCeti.NormalizedCubicalChain.one_mul`, `TauCeti.NormalizedCubicalChain.mul_one`: strict units.
* `TauCeti.NormalizedCubicalChain.boundary_mul`: the Leibniz rule, with
  `boundary_mul_zero_left` and `boundary_mul_zero_right` for a factor of degree `0`.
* `TauCeti.NormalizedCubicalChain.augment_mul`, `augment_one`: the augmentation is multiplicative
  and unital.
* `TauCeti.NormalizedCubicalChain.map_mul`, `TauCeti.NormalizedCubicalChain.map_one`: pushing
  forward along a continuous monoid homomorphism preserves the product and the unit.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

section Mul

variable (G : Type*) [Mul G] [TopologicalSpace G] [ContinuousMul G]

/-- The multiplication of a topological magma as a continuous map `G × G → G`. -/
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

variable {G R}

/-- The Pontryagin product is the push-forward of the cross product along the multiplication. -/
theorem mul_def {p q : ℕ} (a : NormalizedCubicalChain G R p) (b : NormalizedCubicalChain G R q) :
    mul G R p q a b = map R (mulMap G) (p + q) (crossProduct G G R p q a b) :=
  (rfl)

/-- The product of two cubes is the class of the cube of products. -/
@[simp]
theorem mul_ofCube {p q : ℕ} (c : SingularCube G p) (d : SingularCube G q) :
    mul G R p q (ofCube G R c) (ofCube G R d) =
      ofCube G R ((mulMap G).comp (SingularCube.crossProduct c d)) := by
  simp [mul_def]

/-- **The Leibniz rule for the Pontryagin product**: for `a` of degree `p + 1` and `b` of degree
`q + 1`, `∂ (a · b) = ∂ a · b + (-1) ^ (p + 1) • (a · ∂ b)`, in degree `p + q + 1`. -/
theorem boundary_mul {p q : ℕ} (a : NormalizedCubicalChain G R (p + 1))
    (b : NormalizedCubicalChain G R (q + 1)) :
    boundary G R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1) (mul G R (p + 1) (q + 1) a b)) =
      mul G R p (q + 1) (boundary G R p a) b +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (mul G R (p + 1) q a (boundary G R q b)) := by
  simp only [mul_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary G R _), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct, map_add, map_smul, map_cast]
  rfl

/-- The Leibniz rule for the Pontryagin product with a `0`-chain on the right. -/
theorem boundary_mul_zero_right {p : ℕ} (a : NormalizedCubicalChain G R (p + 1))
    (b : NormalizedCubicalChain G R 0) :
    boundary G R p (mul G R (p + 1) 0 a b) = mul G R p 0 (boundary G R p a) b := by
  simp only [mul_def]
  rw [← LinearMap.comp_apply (boundary G R p), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_right]
  rfl

/-- The Leibniz rule for the Pontryagin product with a `0`-chain on the left. -/
theorem boundary_mul_zero_left {q : ℕ} (a : NormalizedCubicalChain G R 0)
    (b : NormalizedCubicalChain G R (q + 1)) :
    boundary G R q (cast R (Nat.zero_add (q + 1)) (mul G R 0 (q + 1) a b)) =
      cast R (Nat.zero_add q) (mul G R 0 q a (boundary G R q b)) := by
  simp only [mul_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary G R q), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_left, map_cast]

/-- **The augmentation is multiplicative** on the Pontryagin product of `0`-chains. -/
theorem augment_mul (a b : NormalizedCubicalChain G R 0) :
    augment G R (mul G R 0 0 a b) = augment G R a * augment G R b := by
  rw [mul_def, ← LinearMap.comp_apply (augment G R), augment_map, augment_crossProduct]

end NormalizedCubicalChain

end Mul

section One

variable (G : Type*) [One G] [TopologicalSpace G]

namespace NormalizedCubicalChain

variable (R : Type*) [Ring R]

/-- The unit of the Pontryagin product: the `0`-cube at `1`. -/
def one : NormalizedCubicalChain G R 0 := ofCube G R (SingularCube.point 1)

/-- The unit of the Pontryagin product is the class of the `0`-cube at `1`. -/
theorem one_def : one G R = ofCube G R (SingularCube.point 1) :=
  (rfl)

end NormalizedCubicalChain

end One

namespace NormalizedCubicalChain

variable {R : Type*} [CommRing R]

section Semigroup

variable {G : Type*} [Semigroup G] [TopologicalSpace G] [ContinuousMul G]

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
        (map R (Homeomorph.prodAssoc G G G : C((G × G) × G, G × G × G)) (p + q + r)
          (crossProduct (G × G) G R (p + q) r (crossProduct G G R p q a b) c)) := by
    rw [hZ, cast_cast, cast_rfl]
  have key : (mulMap G).comp ((mulMap G).prodMap (ContinuousMap.id G)) =
      (mulMap G).comp (((ContinuousMap.id G).prodMap (mulMap G)).comp
        (Homeomorph.prodAssoc G G G : C((G × G) × G, G × G × G))) := by
    ext x
    simp [_root_.mul_assoc, Homeomorph.prodAssoc, Equiv.prodAssoc]
  -- Push the inner products out of the cross products.
  have hl : crossProduct G G R (p + q) r (map R (mulMap G) (p + q) (crossProduct G G R p q a b)) c =
      map R ((mulMap G).prodMap (ContinuousMap.id G)) (p + q + r)
        (crossProduct (G × G) G R (p + q) r (crossProduct G G R p q a b) c) := by
    rw [map_crossProduct, map_id, LinearMap.id_apply]
  have hr : crossProduct G G R p (q + r) a (map R (mulMap G) (q + r) (crossProduct G G R q r b c)) =
      map R ((ContinuousMap.id G).prodMap (mulMap G)) (p + (q + r))
        (crossProduct G (G × G) R p (q + r) a (crossProduct G G R q r b c)) := by
    rw [map_crossProduct, map_id, LinearMap.id_apply]
  simp only [mul_def]
  rw [hl, hr, hW, map_cast, map_cast]
  congr 1
  rw [← LinearMap.comp_apply (map R (mulMap G) (p + q + r)), ← map_comp, key, map_comp, map_comp,
    LinearMap.comp_apply, LinearMap.comp_apply]

end Semigroup

section MulOneClass

variable {G : Type*} [MulOneClass G] [TopologicalSpace G] [ContinuousMul G]

/-- **The unit is a left unit**, after the reindexing `0 + q = q`. -/
@[simp]
theorem one_mul {q : ℕ} (b : NormalizedCubicalChain G R q) :
    cast R (Nat.zero_add q) (mul G R 0 q (one G R) b) = b := by
  have h : (mulMap G).comp
      (ContinuousMap.prodMk (ContinuousMap.const G (1 : G)) (ContinuousMap.id G)) =
        ContinuousMap.id G := by
    ext x
    simp
  rw [mul_def, one_def, ← map_cast, crossProduct_point_left, ← LinearMap.comp_apply, ← map_comp,
    h, map_id, LinearMap.id_apply]

/-- **The unit is a right unit**, after the reindexing `p + 0 = p`. -/
theorem mul_one {p : ℕ} (a : NormalizedCubicalChain G R p) :
    cast R (Nat.add_zero p) (mul G R p 0 a (one G R)) = a := by
  have h : (mulMap G).comp
      (ContinuousMap.prodMk (ContinuousMap.id G) (ContinuousMap.const G (1 : G))) =
        ContinuousMap.id G := by
    ext x
    simp
  rw [mul_def, one_def, ← map_cast, crossProduct_point_right, ← LinearMap.comp_apply, ← map_comp,
    h, map_id, LinearMap.id_apply]

/-- The right unit law in simp normal form: since `p + 0` reduces to `p`, no reindexing is
needed. -/
@[simp]
theorem mul_one_eq_self {p : ℕ} (a : NormalizedCubicalChain G R p) :
    mul G R p 0 a (one G R) = a := by
  simpa using mul_one a

end MulOneClass

section Hom

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]

omit [ContinuousMul G] in
/-- The augmentation of the unit is `1`. -/
@[simp]
theorem augment_one : augment G R (one G R) = 1 :=
  augment_ofCube R _

variable {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ContinuousMul G']

/-- Pushing forward along a continuous monoid homomorphism is multiplicative for the Pontryagin
product. -/
theorem map_mul (φ : G →ₜ* G') {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (b : NormalizedCubicalChain G R q) :
    map R φ.toContinuousMap (p + q) (mul G R p q a b) =
      mul G' R p q (map R φ.toContinuousMap p a) (map R φ.toContinuousMap q b) := by
  have key : φ.toContinuousMap.comp (mulMap G) =
      (mulMap G').comp (φ.toContinuousMap.prodMap φ.toContinuousMap) := by
    ext x
    simp [_root_.map_mul]
  rw [mul_def, mul_def, ← LinearMap.comp_apply (map R φ.toContinuousMap (p + q)), ← map_comp, key,
    map_comp, LinearMap.comp_apply, map_crossProduct]

omit [ContinuousMul G] [ContinuousMul G'] in
/-- Pushing forward along a continuous monoid homomorphism sends the unit to the unit. -/
theorem map_one (φ : G →ₜ* G') : map R φ.toContinuousMap 0 (one G R) = one G' R := by
  simp only [one_def, map_ofCube]
  congr 1
  ext t
  simp [SingularCube.point_apply, _root_.map_one]

end Hom

end NormalizedCubicalChain

end TauCeti

end
