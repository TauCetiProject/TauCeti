/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Module
public import TauCeti.AlgebraicTopology.Singular.Cubical.Basic

/-!
# Unnormalized cubical chains

The **unnormalized cubical `n`-chains** of a space `X` with coefficients in a commutative ring `R`
are the formal `R`-combinations of singular `n`-cubes, `SingularCube X n →₀ R`.  The boundary of
an `(n+1)`-cube is the alternating sum of its faces,

`∂ c = Σᵢ (-1) ^ i (face i 0 c - face i 1 c)`,

following Massey, *Singular Homology Theory*, Chapter II.  The main result is `∂ ∘ ∂ = 0`: the
terms of `∂ ∂ c` indexed by `(i, j)` and by `(i.succAbove j, j.predAbove i)` cancel, since the
cubical identity `face_face` matches their faces and the two signs are opposite.

Chains are modelled concretely, as finitely supported functions, rather than as a chain complex in
an abstract preadditive category: the roadmap that consumes them makes the normalized cubical
chains of a topological monoid into a differential graded algebra on a type (`TauCeti.IsDGAlgebra`),
which needs a carrier with a multiplication, and the cross product is bilinear on these carriers.
This is the convention of `TauCeti.AlgebraicTopology.Singular.Subdivision.AffineChain`, whose
`boundary_boundary` the proof here mirrors.  The degenerate cubes are not yet quotiented out; the
normalized complex is built on top of this file.

## Main definitions

* `TauCeti.CubicalChain X R n`: unnormalized cubical `n`-chains.
* `TauCeti.CubicalChain.boundary R n`: the boundary
  `CubicalChain X R (n + 1) →ₗ[R] CubicalChain X R n`.
* `TauCeti.CubicalChain.map f n`: the chains pushed forward along a continuous map.

## Main results

* `TauCeti.CubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0`.
* `TauCeti.CubicalChain.map_boundary`: the boundary is natural.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (R : Type*) [CommRing R]

/-- The **unnormalized cubical `n`-chains** of `X` with coefficients in `R`: formal
`R`-combinations of singular `n`-cubes. -/
abbrev CubicalChain (X : Type*) [TopologicalSpace X] (R : Type*) [CommRing R] (n : ℕ) :
    Type _ :=
  SingularCube X n →₀ R

namespace CubicalChain

open SingularCube

/-- The boundary of a single `(n+1)`-cube, as an `n`-chain:
`∂ c = Σᵢ (-1) ^ i (face i 0 c - face i 1 c)`. -/
def boundaryCube {n : ℕ} (c : SingularCube X (n + 1)) : CubicalChain X R n :=
  ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • (single (face i 0 c) 1 - single (face i 1 c) 1)

variable (X) in
/-- The **boundary** of cubical chains, `∂ c = Σᵢ (-1) ^ i (face i 0 c - face i 1 c)` on a cube,
extended linearly. -/
def boundary (n : ℕ) : CubicalChain X R (n + 1) →ₗ[R] CubicalChain X R n :=
  linearCombination R (boundaryCube R)

@[simp]
theorem boundary_single {n : ℕ} (c : SingularCube X (n + 1)) (a : R) :
    boundary X R n (single c a) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • (single (face i 0 c) a - single (face i 1 c) a) := by
  simp only [boundary, linearCombination_single, boundaryCube, Finset.smul_sum, smul_sub,
    smul_single, smul_eq_mul, mul_one, mul_comm a]

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
  · rw [Fin.succAbove_of_le_castSucc i j h, Fin.predAbove_of_le_castSucc j i h, Fin.val_succ,
      Fin.coe_castPred, show (j : ℕ) + 1 + i = (i + j) + 1 by omega, pow_succ, mul_neg_one]

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
    neg_one_pow_succAbove_add_predAbove]
  module

/-- Cubical chains pushed forward along a continuous map. -/
def map (f : C(X, Y)) (n : ℕ) : CubicalChain X R n →ₗ[R] CubicalChain Y R n :=
  lmapDomain R R f.comp

@[simp]
theorem map_single (f : C(X, Y)) {n : ℕ} (c : SingularCube X n) (a : R) :
    map R f n (single c a) = single (f.comp c) a := by
  rw [map, lmapDomain_apply, mapDomain_single]

theorem map_id (n : ℕ) : map R (ContinuousMap.id X) n = LinearMap.id := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) (n : ℕ) :
    map R (g.comp f) n = map R g n ∘ₗ map R f n := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [ContinuousMap.comp_assoc]

/-- The boundary is natural. -/
theorem map_boundary (f : C(X, Y)) (n : ℕ) :
    map R f n ∘ₗ boundary X R n = boundary Y R n ∘ₗ map R f (n + 1) := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [face_comp]

end CubicalChain

end TauCeti

end
