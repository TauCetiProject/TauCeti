/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.AlgebraicTopology.Singular.Cubical.Basic
import Mathlib.Data.Fin.Parity
import Mathlib.Tactic.Abel
import Mathlib.Topology.CompactOpen
import TauCeti.Data.Fin.FaceSwap

/-!
# Unnormalized cubical chains

The **unnormalized cubical `n`-chains** of a space `X` with coefficients in a ring `R` are the
formal `R`-combinations of singular `n`-cubes, `SingularCube X n →₀ R`.  The boundary of an
`(n+1)`-cube is the alternating sum of its faces,

`∂ c = Σᵢ (-1) ^ i (face i 0 c - face i 1 c)`,

following Massey, *Singular Homology Theory*, Chapter II, and it satisfies `∂ ∘ ∂ = 0`.  Chains
push forward along continuous maps, and the boundary is natural.

Chains are modelled concretely, as finitely supported functions on a type, rather than as a chain
complex in an abstract preadditive category: the normalized cubical chains built on top of this
file are the quotient of this module by the degenerate cubes, and the constructions on them
(products, actions) are maps between such carriers.  The coefficient ring need not be commutative:
only the central signs `(-1) ^ i` enter the boundary.

## Main definitions

* `TauCeti.CubicalChain X R n`: unnormalized cubical `n`-chains.
* `TauCeti.CubicalChain.boundary X R M n`: the boundary on original raw cubes with arbitrary
  module coefficients. Scalar, module and space universes are independent.
* `TauCeti.CubicalChain.map R f n`: the chains pushed forward along a continuous map.
* `TauCeti.CubicalChain.cast R h`: reindexing of chains along an equality of dimensions.

## Main results

* `TauCeti.CubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0`.
* `TauCeti.CubicalChain.map_boundary`: the boundary is natural.

## Implementation notes

The concrete model, with its `boundary` and `boundary_boundary`, follows
`TauCeti.AlgebraicTopology.Singular.Subdivision.AffineChain`.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The **unnormalized cubical `n`-chains** of `X` with coefficients in `R`: formal
`R`-combinations of singular `n`-cubes. -/
abbrev CubicalChain (X : Type*) [TopologicalSpace X] (R : Type*) [Semiring R] (n : ℕ) :
    Type _ :=
  SingularCube X n →₀ R

namespace CubicalChain

open SingularCube

section Map

variable (R : Type*) [Semiring R]

/-- Cubical chains pushed forward along a continuous map. -/
def map (f : C(X, Y)) (n : ℕ) : CubicalChain X R n →ₗ[R] CubicalChain Y R n :=
  lmapDomain R R f.comp

/-- An injective map of spaces preserves the coefficient of each cube at its image. -/
theorem map_apply_comp_of_injective (f : C(X, Y)) (hf : Function.Injective f)
    {n : ℕ} (g : CubicalChain X R n) (c : SingularCube X n) :
    map R f n g (f.comp c) = g c := by
  rw [map, lmapDomain_apply,
    mapDomain_apply_of_injective (ContinuousMap.postcomp_injective f hf)]

/-- An injective continuous map induces an injective push-forward on cubical chains. -/
theorem map_injective (f : C(X, Y)) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (map R f n) := by
  rw [map, coe_lmapDomain]
  exact mapDomain_injective (ContinuousMap.postcomp_injective f hf)

@[simp]
theorem map_single (f : C(X, Y)) {n : ℕ} (c : SingularCube X n) (a : R) :
    map R f n (single c a) = single (f.comp c) a := by
  rw [map, lmapDomain_apply, mapDomain_single]

@[simp]
theorem map_id (n : ℕ) : map R (ContinuousMap.id X) n = LinearMap.id := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) (n : ℕ) :
    map R (g.comp f) n = map R g n ∘ₗ map R f n := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [ContinuousMap.comp_assoc]

end Map

section Cast

variable (R : Type*) [Semiring R]

/-- Reindex cubical chains along an equality of dimensions. -/
def cast {n m : ℕ} (h : n = m) : CubicalChain X R n →ₗ[R] CubicalChain X R m :=
  lmapDomain R R (SingularCube.cast h)

@[simp]
theorem cast_single {n m : ℕ} (h : n = m) (c : SingularCube X n) (a : R) :
    cast R h (single c a) = single (SingularCube.cast h c) a := by
  rw [cast, lmapDomain_apply, mapDomain_single]

@[simp]
theorem cast_rfl {n : ℕ} (f : CubicalChain X R n) : cast R rfl f = f := by
  induction f using Finsupp.induction_linear <;> simp_all

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

end Cast

section Boundary

variable (R : Type*) [Semiring R] (M : Type*) [AddCommGroup M] [Module R M]

variable (X) in
/-- The boundary on original raw cubical chains with arbitrary module coefficients.
Central integer signs give the native interval boundary `[0] - [1]`. -/
def boundary (n : ℕ) :
    (SingularCube X (n + 1) →₀ M) →ₗ[R] (SingularCube X n →₀ M) :=
  ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
    (lmapDomain M R (face j 0) - lmapDomain M R (face j 1))

variable {M} in
/-- The module boundary is the alternating sum of its endpoint faces. -/
@[simp]
theorem boundary_single {n : ℕ} (c : SingularCube X (n + 1)) (a : M) :
    boundary X R M n (single c a) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        (single (face j 0 c) a - single (face j 1 c) a) := by
  simp [boundary]

/-- The cubical boundary squares to zero for arbitrary module coefficients. -/
theorem boundary_boundary (n : ℕ) : boundary X R M n ∘ₗ boundary X R M (n + 1) = 0 := by
  -- The terms of `∂ ∂ c` cancel in pairs under `Fin.faceSwap`, by the cubical identity and
  -- the parity of the swapped exponent.
  apply lhom_ext
  intro c a
  simp only [LinearMap.comp_apply, boundary_single, LinearMap.zero_apply,
    map_sum, map_zsmul, map_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ ↦ Fin.faceSwap p) (fun p _ ↦ ?_)
    (fun p _ _ ↦ Fin.faceSwap_ne p) (fun _ _ ↦ Finset.mem_univ _)
    (fun p _ ↦ Fin.faceSwap_faceSwap p)
  obtain ⟨i, j⟩ := p
  simp only [Fin.faceSwap_def, ← face_face, smul_sub, smul_smul,
    ← pow_add, Fin.neg_one_pow_succAbove_add_predAbove, neg_smul]
  abel

/-- The boundary with module coefficients commutes with push-forward along a continuous map. -/
theorem lmapDomain_comp_boundary (f : C(X, Y)) (n : ℕ) :
    lmapDomain M R f.comp ∘ₗ boundary X R M n = boundary Y R M n ∘ₗ lmapDomain M R f.comp := by
  refine lhom_ext fun c a ↦ ?_
  simp only [LinearMap.comp_apply, boundary_single, map_sum, map_zsmul, map_sub, lmapDomain_apply,
    mapDomain_single, face_comp]

end Boundary

section RingBoundary

variable (R : Type*) [Ring R]

/-- The boundary of a single `(n+1)`-cube, as an `n`-chain:
`∂ c = Σᵢ (-1) ^ i (face i 0 c - face i 1 c)`. -/
def boundaryCube {n : ℕ} (c : SingularCube X (n + 1)) : CubicalChain X R n :=
  ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • (single (face i 0 c) 1 - single (face i 1 c) 1)

theorem boundaryCube_def {n : ℕ} (c : SingularCube X (n + 1)) :
    boundaryCube R c =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • (single (face i 0 c) 1 - single (face i 1 c) 1) := by
  rw [boundaryCube]

/-- The scalar boundary agrees with the boundary of a cube with coefficient one. -/
theorem boundary_single_one {n : ℕ} (c : SingularCube X (n + 1)) :
    boundary X R R n (single c 1) = boundaryCube R c := by
  rw [boundary_single, boundaryCube_def]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ (j : ℕ))
    (single (face j 0 c) (1 : R) - single (face j 1 c) (1 : R))
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using h.symm

/-- The scalar boundary commutes with push-forward along a continuous map. -/
theorem map_boundary (f : C(X, Y)) (n : ℕ) :
    map R f n ∘ₗ boundary X R R n = boundary Y R R n ∘ₗ map R f (n + 1) :=
  lmapDomain_comp_boundary R R f n

end RingBoundary

end CubicalChain

end TauCeti

end
