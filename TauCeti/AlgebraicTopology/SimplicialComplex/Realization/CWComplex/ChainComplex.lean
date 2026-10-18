/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic

import Mathlib.Data.Fin.Parity

/-!
# The ordered simplicial chain complex

For a simplicial complex with linearly ordered vertices, its simplicial chains are the free
modules on the faces of each dimension.  The boundary of a face with increasing vertex list
`[v₀, ..., vₙ]` is the alternating sum of the faces obtained by deleting one vertex:

`∂[v₀, ..., vₙ] = ∑ j, (-1) ^ j [v₀, ..., v̂ⱼ, ..., vₙ]`.

This file constructs the deleted-vertex face canonically from the increasing enumeration used
by the CW structure on the realization, proves the two-face identity, and packages the
alternating boundary as a chain complex over any coefficient ring.  The signs are central, so
the coefficient ring need not be commutative.

The comparison with the cellular chain complex of the realization is separate.  Both complexes
are already indexed by `RealizationCell`, so that comparison reduces to computing the cellular
incidence coefficients in these ordered coordinates.

## Main definitions

* `AbstractSimplicialComplex.RealizationCell.face`: delete one vertex of a simplicial cell.
* `TauCeti.OrderedSimplicialChain`: finite linear combinations of ordered simplicial cells.
* `TauCeti.OrderedSimplicialChain.boundary`: the alternating simplicial boundary.
* `TauCeti.orderedSimplicialChainComplex`: the resulting chain complex of modules.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1.
-/

@[expose] public section

noncomputable section

open CategoryTheory Finsupp

universe u

namespace AbstractSimplicialComplex.RealizationCell

variable {ι : Type u} [LinearOrder ι]
variable {K : AbstractSimplicialComplex ι} {n : ℕ}

/-- The codimension-one face obtained by deleting the `j`-th vertex in the increasing
enumeration of a simplicial cell. -/
def face (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) : RealizationCell K n := by
  let σ := c.1.1.erase (c.vertexEmbedding j)
  have hcard : σ.card = n + 1 := by
    dsimp only [σ]
    rw [Finset.card_erase_of_mem (c.vertexEmbedding_mem j), c.2]
    omega
  refine ⟨⟨σ, K.isRelLowerSet_faces.mem_of_le c.1.2 (Finset.erase_subset _ _) ?_⟩, hcard⟩
  exact Finset.card_pos.mp (hcard.trans_gt (Nat.zero_lt_succ n))

/-- The finite set underlying a deleted-vertex face is obtained by erasing that vertex. -/
@[simp]
theorem face_val (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    (c.face j).1.1 = c.1.1.erase (c.vertexEmbedding j) :=
  (rfl)

/-- The increasing enumeration of a deleted-vertex face skips exactly the deleted position. -/
theorem vertexEmbedding_face (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    ⇑(c.face j).vertexEmbedding = c.vertexEmbedding ∘ j.succAbove := by
  have hmono : StrictMono (c.vertexEmbedding ∘ j.succAbove) :=
    c.strictMono_vertexEmbedding.comp (Fin.strictMono_succAbove j)
  symm
  apply (hmono.range_inj_of_wellFoundedLT (c.face j).strictMono_vertexEmbedding).mp
  have himage : Finset.univ.image (c.vertexEmbedding ∘ j.succAbove) =
      Finset.univ.image (c.face j).vertexEmbedding := by
    rw [(c.face j).image_vertexEmbedding, face_val]
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply,
      Finset.mem_erase]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨fun h ↦ j.succAbove_ne i (c.vertexEmbedding.injective h),
        c.vertexEmbedding_mem (j.succAbove i)⟩
    · rintro ⟨hvj, hv⟩
      rw [← c.image_vertexEmbedding] at hv
      rcases Finset.mem_image.mp hv with ⟨i, -, rfl⟩
      rcases Fin.exists_succAbove_eq (fun h ↦ hvj (congrArg c.vertexEmbedding h)) with ⟨k, hk⟩
      exact ⟨k, congrArg c.vertexEmbedding hk⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    congrArg (fun s : Finset ι ↦ (s : Set ι)) himage

/-- Deleting two vertices is independent of their order, with the indices transported through
the first deletion.  This is the semisimplicial face identity. -/
theorem face_face (c : RealizationCell K (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (c.face i).face j = (c.face (i.succAbove j)).face (j.predAbove i) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [face_val, face_val, face_val, face_val]
  rw [congrFun (vertexEmbedding_face c i) j,
    congrFun (vertexEmbedding_face c (i.succAbove j)) (j.predAbove i)]
  simp only [Function.comp_apply, Fin.succAbove_succAbove_predAbove]
  ext v
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hvi, hvj, hv⟩
    exact ⟨hvj, hvi, hv⟩
  · rintro ⟨hvj, hvi, hv⟩
    exact ⟨hvi, hvj, hv⟩

end AbstractSimplicialComplex.RealizationCell

namespace TauCeti

variable {ι : Type u} [LinearOrder ι]
variable (K : _root_.AbstractSimplicialComplex ι)

/-- Ordered simplicial `n`-chains with coefficients in `R`: finite linear combinations of the
`n`-dimensional faces, oriented by their increasing vertex enumerations. -/
abbrev OrderedSimplicialChain (R : Type u) [Semiring R] (n : ℕ) :=
  _root_.AbstractSimplicialComplex.RealizationCell K n →₀ R

namespace OrderedSimplicialChain

variable {K}
variable (R : Type u) [Ring R]

/-- The boundary of a single `(n + 1)`-dimensional simplicial cell is the alternating sum of its
deleted-vertex faces. -/
def boundaryCell {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    OrderedSimplicialChain K R n :=
  ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • single (c.face j) 1

/-- The explicit alternating-sum formula for the boundary of one cell. -/
theorem boundaryCell_def {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    boundaryCell R c = ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • single (c.face j) 1 :=
  (rfl)

/-- The ordered simplicial boundary, extended linearly from cells. -/
def boundary (n : ℕ) : OrderedSimplicialChain K R (n + 1) →ₗ[R] OrderedSimplicialChain K R n :=
  linearCombination R (boundaryCell R)

/-- The boundary of a cell with coefficient one is its alternating deleted-face sum. -/
theorem boundary_single_one {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    boundary R n (single c 1) = boundaryCell R c := by
  rw [boundary, linearCombination_single, one_smul]

/-- The boundary of a scalar multiple of a cell is the corresponding alternating sum with that
coefficient on every face. -/
@[simp]
theorem boundary_single {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) (a : R) :
    boundary R n (single c a) =
      ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • single (c.face j) a := by
  have hc : ∀ j : ℕ, a * (-1 : R) ^ j = (-1) ^ j * a := fun j ↦
    ((Commute.neg_one_right a).pow_right j).eq
  simp only [boundary, linearCombination_single, boundaryCell, Finset.smul_sum, smul_single,
    smul_eq_mul, mul_one, hc]

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) :
    boundary (K := K) R n ∘ₗ boundary (K := K) R (n + 1) = 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, LinearMap.zero_apply,
    boundary_single, map_sum, map_smul, Finset.smul_sum]
  rw [← Finset.sum_product']
  let swap : Fin (n + 3) × Fin (n + 2) → Fin (n + 3) × Fin (n + 2) :=
    fun p ↦ (p.1.succAbove p.2, p.2.predAbove p.1)
  have hswap_swap : ∀ p, swap (swap p) = p := by
    rintro ⟨i, j⟩
    simp [swap, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  have hswap_ne : ∀ p, swap p ≠ p := by
    rintro ⟨i, j⟩ h
    exact Fin.succAbove_ne i j (congrArg Prod.fst h)
  refine Finset.sum_involution (fun p _ ↦ swap p) (fun p _ ↦ ?_) (fun p _ _ ↦ hswap_ne p)
    (fun _ _ ↦ Finset.mem_univ _) (fun p _ ↦ hswap_swap p)
  obtain ⟨i, j⟩ := p
  simp only [swap, ← _root_.AbstractSimplicialComplex.RealizationCell.face_face, smul_smul,
    ← pow_add, Fin.neg_one_pow_succAbove_add_predAbove, neg_smul, add_neg_cancel]

end OrderedSimplicialChain

/-- The ordered simplicial chain complex of `K`, with one basis vector for every face and the
usual alternating deleted-vertex boundary. -/
def orderedSimplicialChainComplex (R : Type u) [Ring R] : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (OrderedSimplicialChain K R n))
    (fun n ↦ ModuleCat.ofHom (OrderedSimplicialChain.boundary (K := K) R n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, OrderedSimplicialChain.boundary_boundary (K := K)]
      rfl

variable {K}
variable (R : Type u) [Ring R]

/-- The object in degree `n` of the ordered simplicial chain complex is the free module on the
`n`-dimensional faces. -/
@[simp]
theorem orderedSimplicialChainComplex_X (n : ℕ) :
    (orderedSimplicialChainComplex K R).X n = ModuleCat.of R (OrderedSimplicialChain K R n) :=
  (rfl)

/-- The differential of the ordered simplicial chain complex is the alternating simplicial
boundary. -/
@[simp]
theorem orderedSimplicialChainComplex_d_apply (n : ℕ)
    (x : OrderedSimplicialChain K R (n + 1)) :
    (orderedSimplicialChainComplex K R).d (n + 1) n x =
      OrderedSimplicialChain.boundary (K := K) R n x := by
  simp only [orderedSimplicialChainComplex, ChainComplex.of_d]
  rfl

end TauCeti
