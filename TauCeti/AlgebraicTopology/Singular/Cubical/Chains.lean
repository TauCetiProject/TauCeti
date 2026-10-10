/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.AlgebraicTopology.Singular.Cubical.Basic

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
* `TauCeti.CubicalChain.boundary X R n`: the boundary
  `CubicalChain X R (n + 1) →ₗ[R] CubicalChain X R n`.
* `TauCeti.CubicalChain.map R f n`: the chains pushed forward along a continuous map.

## Main results

* `TauCeti.CubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0`.
* `TauCeti.CubicalChain.map_boundary`: the boundary is natural.

## Implementation notes

The concrete model and the proof of `boundary_boundary` follow
`TauCeti.AlgebraicTopology.Singular.Subdivision.AffineChain`, whose `boundary` is also a
`Finsupp.linearCombination` of signed faces and whose `boundary_boundary` is also a
`Finset.sum_involution` over pairs of face indices.

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

section Boundary

variable (R : Type*) [Ring R]

/-- The boundary of a single `(n+1)`-cube, as an `n`-chain:
`∂ c = Σᵢ (-1) ^ i (face i 0 c - face i 1 c)`. -/
def boundaryCube {n : ℕ} (c : SingularCube X (n + 1)) : CubicalChain X R n :=
  ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • (single (face i 0 c) 1 - single (face i 1 c) 1)

theorem boundaryCube_def {n : ℕ} (c : SingularCube X (n + 1)) :
    boundaryCube R c =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • (single (face i 0 c) 1 - single (face i 1 c) 1) := by
  rw [boundaryCube]

variable (X) in
/-- The **boundary** of cubical chains, `∂ c = Σᵢ (-1) ^ i (face i 0 c - face i 1 c)` on a cube,
extended linearly. -/
def boundary (n : ℕ) : CubicalChain X R (n + 1) →ₗ[R] CubicalChain X R n :=
  linearCombination R (boundaryCube R)

/-- The boundary of a cube with coefficient one is `boundaryCube`. -/
theorem boundary_single_one {n : ℕ} (c : SingularCube X (n + 1)) :
    boundary X R n (single c 1) = boundaryCube R c := by
  rw [boundary, linearCombination_single, one_smul]

@[simp]
theorem boundary_single {n : ℕ} (c : SingularCube X (n + 1)) (a : R) :
    boundary X R n (single c a) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • (single (face i 0 c) a - single (face i 1 c) a) := by
  -- The coefficient `a` commutes with the signs, which are central.
  have hc : ∀ i : ℕ, a * (-1 : R) ^ i = (-1) ^ i * a := fun i ↦
    ((Commute.neg_one_right a).pow_right i).eq
  simp only [boundary, linearCombination_single, boundaryCube, Finset.smul_sum, smul_sub,
    smul_single, smul_eq_mul, mul_one, hc]

/-- The parity of the exponent after a cubical swap: `(-1) ^ (i.succAbove j + j.predAbove i)` is
the opposite of `(-1) ^ (i + j)`. -/
theorem neg_one_pow_succAbove_add_predAbove {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (-1 : R) ^ ((i.succAbove j : ℕ) + (j.predAbove i : ℕ)) = -(-1 : R) ^ ((i : ℕ) + j) := by
  rcases j.castSucc.lt_or_le i with h | h
  · rw [Fin.succAbove_of_castSucc_lt i j h, Fin.predAbove_of_castSucc_lt j i h, Fin.val_castSucc,
      Fin.val_pred]
    have hi : (i : ℕ) + j = (j + ((i : ℕ) - 1)) + 1 := by
      have := Fin.lt_def.1 h
      rw [Fin.val_castSucc] at this
      omega
    rw [hi, pow_succ, mul_neg_one, neg_neg]
  · -- The exponent `j + 1 + i` is the successor of `i + j`.
    have hj : (j : ℕ) + 1 + i = (i + j) + 1 := by omega
    rw [Fin.succAbove_of_le_castSucc i j h, Fin.predAbove_of_le_castSucc j i h, Fin.val_succ,
      Fin.coe_castPred, hj, pow_succ, mul_neg_one]

/-- The involution on pairs of face indices behind `∂ ∘ ∂ = 0`: `(i, j)` goes to
`(i.succAbove j, j.predAbove i)`. -/
def faceSwap {n : ℕ} (p : Fin (n + 2) × Fin (n + 1)) : Fin (n + 2) × Fin (n + 1) :=
  (p.1.succAbove p.2, p.2.predAbove p.1)

theorem faceSwap_faceSwap {n : ℕ} (p : Fin (n + 2) × Fin (n + 1)) : faceSwap (faceSwap p) = p := by
  obtain ⟨i, j⟩ := p
  simp [faceSwap, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

theorem faceSwap_ne {n : ℕ} (p : Fin (n + 2) × Fin (n + 1)) : faceSwap p ≠ p := by
  obtain ⟨i, j⟩ := p
  intro h
  exact Fin.succAbove_ne i j (congrArg Prod.fst h)

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary X R n ∘ₗ boundary X R (n + 1) = 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, LinearMap.zero_apply,
    boundary_single, map_sum, map_smul, map_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ ↦ faceSwap p) (fun p _ ↦ ?_) (fun p _ _ ↦ faceSwap_ne p)
    (fun _ _ ↦ Finset.mem_univ _) (fun p _ ↦ faceSwap_faceSwap p)
  obtain ⟨i, j⟩ := p
  simp only [faceSwap, ← face_face, smul_sub, smul_smul, ← pow_add,
    neg_one_pow_succAbove_add_predAbove, neg_smul]
  abel

/-- The boundary is natural. -/
theorem map_boundary (f : C(X, Y)) (n : ℕ) :
    map R f n ∘ₗ boundary X R n = boundary Y R n ∘ₗ map R f (n + 1) := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [face_comp]

end Boundary

end CubicalChain

end TauCeti

end
