/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Single
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Algebra.BigOperators.AlternatingSum
public import TauCeti.AlgebraicTopology.SimplicialComplex.Cell

/-!
# The ordered simplicial chain complex

For a simplicial complex with linearly ordered vertices, its simplicial chains are the free
modules on the faces of each dimension.  The boundary of a face with increasing vertex list
`[v₀, ..., vₙ]` is the alternating sum of the faces obtained by deleting one vertex:

`∂[v₀, ..., vₙ] = ∑ j, (-1) ^ j [v₀, ..., v̂ⱼ, ..., vₙ]`.

This file packages the alternating boundary as a chain complex over any coefficient ring.  The
signs are central, so the coefficient ring need not be commutative.

The comparison with the cellular chain complex of the realization is separate.  Both complexes
are indexed by `RealizationCell`, so that comparison reduces to computing the cellular incidence
coefficients in these ordered coordinates.  The support of each simplicial cell boundary is
identified explicitly with its codimension-one faces.

## Main definitions

* `TauCeti.OrderedSimplicialChain`: finite linear combinations of ordered simplicial cells.
* `TauCeti.OrderedSimplicialChain.boundary`: the alternating simplicial boundary.
* `TauCeti.orderedSimplicialChainComplex`: the resulting chain complex of modules.
* `TauCeti.orderedSimplicialChainComplexAugmentation`: the augmentation of the ordered chain
  complex, a chain map to the coefficient ring in degree `0`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Finsupp

universe u v

namespace TauCeti

variable {ι : Type u} [LinearOrder ι]
variable (K : _root_.AbstractSimplicialComplex ι)

/-- Ordered simplicial `n`-chains with coefficients in `R`: finite linear combinations of the
`n`-dimensional faces, oriented by their increasing vertex enumerations. -/
abbrev OrderedSimplicialChain (R : Type v) [Semiring R] (n : ℕ) :=
  _root_.AbstractSimplicialComplex.RealizationCell K n →₀ R

namespace OrderedSimplicialChain

variable {K}
variable (R : Type v) [Ring R]

/-- The boundary of a single `(n + 1)`-dimensional simplicial cell is the alternating sum of its
deleted-vertex faces. -/
def boundaryCell {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    OrderedSimplicialChain K R n :=
  ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • single (c.face j) 1

/-- The coefficient of a codimension-one face in the boundary of a cell is its alternating
sign. -/
@[simp]
theorem boundaryCell_apply_face {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    boundaryCell R c (c.face j) = (-1 : R) ^ (j : ℕ) := by
  classical
  rw [boundaryCell, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hface : c.face i ≠ c.face j := fun h => hij (c.face_injective h)
    simp [hface]
  · simp

/-- A cell which is not a codimension-one subface has coefficient zero in the boundary. -/
theorem boundaryCell_apply_eq_zero_of_not_subset {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1))
    (d : _root_.AbstractSimplicialComplex.RealizationCell K n)
    (h : ¬ d.1.1 ⊆ c.1.1) : boundaryCell R c d = 0 := by
  classical
  rw [boundaryCell, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hface : c.face j ≠ d := by
    intro hj
    apply h
    rw [← hj]
    simpa only [_root_.AbstractSimplicialComplex.RealizationCell.face_val] using
      Finset.erase_subset (c.vertexEmbedding j) c.1.1
  simp [hface]

/-- A cell has nonzero boundary coefficient exactly when it is a codimension-one subface. -/
@[simp]
theorem boundaryCell_apply_ne_zero_iff [Nontrivial R] {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1))
    (d : _root_.AbstractSimplicialComplex.RealizationCell K n) :
    boundaryCell R c d ≠ 0 ↔ d.1.1 ⊆ c.1.1 := by
  constructor
  · intro hne
    by_contra hdc
    exact hne (boundaryCell_apply_eq_zero_of_not_subset R c d hdc)
  · intro hdc
    obtain ⟨j, rfl⟩ := (c.exists_face_eq_iff_subset d).mpr hdc
    rw [boundaryCell_apply_face]
    exact (isUnit_neg_one.pow (j : ℕ)).ne_zero

/-- The support of a cell boundary is precisely the set of its codimension-one faces. -/
theorem support_boundaryCell [Nontrivial R] {n : ℕ}
    (c : _root_.AbstractSimplicialComplex.RealizationCell K (n + 1)) :
    (boundaryCell R c).support = Finset.univ.image c.face := by
  classical
  ext d
  rw [Finsupp.mem_support_iff, boundaryCell_apply_ne_zero_iff, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  exact (c.exists_face_eq_iff_subset d).symm

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
  have h := sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
      (fun i j ↦ single ((c.face i).face j) (1 : R)) fun i j hij ↦ by
        exact congrArg (fun d ↦ single d (1 : R))
          (by simpa [Fin.succAbove_castSucc_of_le i j hij,
              Fin.predAbove_castSucc_of_le j i hij] using
            (_root_.AbstractSimplicialComplex.RealizationCell.face_face c i.castSucc j).symm)
  simp_rw [← Int.cast_smul_eq_zsmul R] at h
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, Finset.smul_sum] using h

/-- The coefficients of the boundary of a `1`-chain sum to zero. -/
theorem augmentation_comp_boundary :
    linearCombination R (fun _ : _root_.AbstractSimplicialComplex.RealizationCell K 0 ↦ (1 : R)) ∘ₗ
      boundary R 0 = 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [Fin.sum_univ_two]

end OrderedSimplicialChain

/-- The ordered simplicial chain complex of `K`, with one basis vector for every face and the
usual alternating deleted-vertex boundary. -/
def orderedSimplicialChainComplex (R : Type v) [Ring R] :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (OrderedSimplicialChain K R n))
    (fun n ↦ ModuleCat.ofHom (OrderedSimplicialChain.boundary (K := K) R n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, OrderedSimplicialChain.boundary_boundary (K := K)]
      rfl

variable {K}
variable (R : Type v) [Ring R]

/-- The object in degree `n` of the ordered simplicial chain complex is the free module on the
`n`-dimensional faces. -/
@[simp]
theorem orderedSimplicialChainComplex_X (n : ℕ) :
    (orderedSimplicialChainComplex K R).X n = ModuleCat.of R (OrderedSimplicialChain K R n) :=
  (rfl)

/-- After identifying the objects with the free modules on cells, the differential of the
ordered simplicial chain complex is the alternating simplicial boundary. -/
@[simp]
theorem orderedSimplicialChainComplex_d (n : ℕ) :
    (orderedSimplicialChainComplex K R).d (n + 1) n =
      eqToHom (orderedSimplicialChainComplex_X R (n + 1)) ≫
        ModuleCat.ofHom (OrderedSimplicialChain.boundary (K := K) R n) ≫
          eqToHom (orderedSimplicialChainComplex_X R n).symm := by
  simp only [orderedSimplicialChainComplex, ChainComplex.of_d]
  rfl

/-- A short complex of modules whose first map is the differential `X (n + 1) ⟶ X n` of the
ordered chain complex is exact exactly when every `n`-chain killed by its second map is a
boundary. Here the second map is read on chains as `g'`, through an isomorphism `e` of its
target. -/
theorem exact_orderedSimplicialChainComplex_d_iff {n : ℕ} {M N : ModuleCat.{max u v} R}
    {g : (orderedSimplicialChainComplex K R).X n ⟶ M}
    (w : (orderedSimplicialChainComplex K R).d (n + 1) n ≫ g = 0) (e : M ≅ N)
    {g' : OrderedSimplicialChain K R n →ₗ[R] N}
    (hg : eqToHom (orderedSimplicialChainComplex_X R n).symm ≫ g ≫ e.hom = ModuleCat.ofHom g') :
    (ShortComplex.mk _ g w).Exact ↔
      ∀ z, g' z = 0 → ∃ y, OrderedSimplicialChain.boundary R n y = z := by
  have hb : ModuleCat.ofHom (OrderedSimplicialChain.boundary (K := K) R n) =
      eqToHom (orderedSimplicialChainComplex_X R (n + 1)).symm ≫
        (orderedSimplicialChainComplex K R).d (n + 1) n ≫
          eqToHom (orderedSimplicialChainComplex_X R n) := by
    simp
  let S : ShortComplex (ModuleCat.{max u v} R) :=
    ShortComplex.mk (ModuleCat.ofHom (OrderedSimplicialChain.boundary (K := K) R n))
      (ModuleCat.ofHom g') (by
        rw [hb, ← hg]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
          reassoc_of% w, Limits.zero_comp, Limits.comp_zero])
  rw [ShortComplex.exact_iff_of_iso (S₂ := S) (ShortComplex.isoMk
      (eqToIso (orderedSimplicialChainComplex_X R (n + 1)))
      (eqToIso (orderedSimplicialChainComplex_X R n)) e (by simp [S]) (by simp [S, ← hg])),
    ShortComplex.moduleCat_exact_iff]
  simp only [S, ModuleCat.hom_ofHom]

section Augmentation

variable (K) (R : Type u) [Ring R]

/-- The **augmentation** of the ordered chain complex: the chain map to `R`, placed in degree
`0`, that sums the coefficients of a `0`-chain. -/
def orderedSimplicialChainComplexAugmentation :
    orderedSimplicialChainComplex K R ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj
      (ModuleCat.of R R) :=
  ((orderedSimplicialChainComplex K R).toSingle₀Equiv _).symm
    ⟨eqToHom (orderedSimplicialChainComplex_X R 0) ≫
      ModuleCat.ofHom (linearCombination R fun _ ↦ (1 : R)), by
      simp [orderedSimplicialChainComplex_d, ← ModuleCat.ofHom_comp,
        OrderedSimplicialChain.augmentation_comp_boundary]⟩

/-- In degree `0` the augmentation sums the coefficients. -/
@[simp]
theorem orderedSimplicialChainComplexAugmentation_f_zero :
    (orderedSimplicialChainComplexAugmentation K R).f 0 =
      eqToHom (orderedSimplicialChainComplex_X R 0) ≫
        ModuleCat.ofHom (linearCombination R fun _ ↦ (1 : R)) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R R)).inv := by
  simp [orderedSimplicialChainComplexAugmentation, ChainComplex.toSingle₀Equiv]

end Augmentation

end TauCeti
