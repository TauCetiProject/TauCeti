/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.Grading.Basic
public import TauCeti.LowDimTopology.Bordered.TypeDD
public import TauCeti.RingTheory.TensorProduct.Grading

/-!
# Gradings of type `DD` structures

A type `DD` structure over differential algebras `(A, d_A)` and `(B, d_B)` is a type `D` structure
over `A ⊗ B` with the differential `d_A ⊗ 1 + 1 ⊗ d_B` (`TauCeti.TypeDDStructure`). Following
Lipshitz, Ozsváth and Thurston, when `A` is graded by a group `G_A` with a central element `l_A`
and `B` by a group `G_B` with a central element `l_B`, each differential shifting degrees by its
central element, `A ⊗ B` is graded by `G_A ×_λ G_B`, the quotient of `G_A × G_B` identifying
`(l_A, 1)` with `(1, l_B)`. In that grading `d_A ⊗ 1 + 1 ⊗ d_B` has the single central degree
`(l_A, 1)`, so the graded type `D` theory of `TauCeti.LowDimTopology.Bordered.Grading.Basic` applies
to type `DD` structures: a type `DD` structure is graded by a set `U` with an action of
`G_A × G_B`, and its structure map, morphisms and box tensor products are graded as for any type
`D` structure, over the parts `TauCeti.tensorGradedPart Ag Bg l_A l_B` of `A ⊗ B` and with the
central element `(l_A, 1)` (`TauCeti.mul_mem_tensorGradedPart`,
`TauCeti.ungradedTensorDifferential_mem_tensorGradedPart`, `Set.center_prod`).

This file grades the **exterior tensor product** `N ⊗ N'` of a type `D` structure `N` over `A` and
a type `D` structure `N'` over `B` (`TauCeti.TypeDStructure.tensorProduct`), with coefficient
matrix `δ ⊗ 1 + 1 ⊗ δ'`. If `N` is graded by a `G_A`-set `T` with structure map of degree `l_A` and
`N'` by a `G_B`-set `T'` with structure map of degree `l_B`, then `N ⊗ N'` is graded by any
`G_A × G_B`-set `U` receiving a map `π : T → T' → U` with
`π (g • t) (h • t') = (g, h) • π t t'`, with structure map of degree `(l_A, 1)`
(`TauCeti.TypeDStructure.tensorProductCoeff_mem_homogeneousMatrices`). The term `δ ⊗ 1` has degree
`(l_A, 1)` and the term `1 ⊗ δ'` has degree `(1, l_B)`; these agree because the parts of `A ⊗ B`
do not distinguish them (`TauCeti.homogeneousMatrices_tensorGradedPart_mul_left_eq`). The grading
set `U` need not identify `(l_A, 1)` with `(1, l_B)`: for the regular sets `T = G_A` and
`T' = G_B`, the pairing `π = Prod.mk` into the regular set `G_A × G_B` qualifies. Kronecker
products `F ⊗ G` of homogeneous morphisms have the product degree
(`TauCeti.kroneckerTMul_mem_homogeneousMatrices`).

The hypotheses are those satisfied by the matched algebras `A(Z)` of pointed matched circles,
graded by their strand grading groups with central element `λ⁻¹`
(`TauCeti.StrandsAlgebra.mul_mem_matchedGradedPart`,
`TauCeti.StrandsAlgebra.matchedDifferential_mem_matchedGradedPart`,
`TauCeti.StrandGradingGroup.lambda_mem_center`), over whose tensor products the type `DD`
bimodules of bordered Heegaard Floer homology are type `D` structures.

## Main results

* `TauCeti.TypeDStructure.tensorProductCoeff_mem_homogeneousMatrices`: the exterior tensor product
  of graded type `D` structures is a graded type `DD` structure, with structure map of degree
  `(l_A, 1)`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), §2.2
  (type `DD` structures) and §2.5 (gradings of bimodules by `G_1 ×_λ G_2`-sets).
-/

public section

open scoped TensorProduct Kronecker

namespace TauCeti

namespace TypeDStructure

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S S' : Type*} {ιA : S → A} {ιB : S' → B}
  {GA GB : Type*} [Group GA] [Group GB] {Ag : GA → Submodule R A} {Bg : GB → Submodule R B}
  {lA : GA} {lB : GB} {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
  {T T' U : Type*} [MulAction GA T] [MulAction GB T'] [MulAction (GA × GB) U]

/-- **The exterior tensor product of graded type `D` structures is graded.** Let the structure map
of `N` have degree `l_A` for a grading `gr` by a `G_A`-set, the structure map of `N'` degree `l_B`
for a grading `gr'` by a `G_B`-set, and the idempotents have degree `1`. For a map
`π : T → T' → U` into a `G_A × G_B`-set with `π (g • t) (h • t') = (g, h) • π t t'`, the
coefficient matrix `δ ⊗ 1 + 1 ⊗ δ'` of `N ⊗ N'` is homogeneous of degree `(l_A, 1)` for the
grading `(x, x') ↦ π (gr x) (gr' x')`, over the parts of `A ⊗ B` identifying `(l_A, 1)` with
`(1, l_B)`. -/
theorem tensorProductCoeff_mem_homogeneousMatrices {N : TypeDStructure dA ιA X}
    {N' : TypeDStructure dB ιB X'} (hιA : ∀ s, ιA s ∈ Ag 1) (hιB : ∀ s', ιB s' ∈ Bg 1)
    {gr : X → T} {gr' : X' → T'} (hN : N.coeff ∈ homogeneousMatrices Ag gr gr lA)
    (hN' : N'.coeff ∈ homogeneousMatrices Bg gr' gr' lB) {π : T → T' → U}
    (hπ : ∀ (g : GA) (h : GB) (t : T) (t' : T'), π (g • t) (h • t') = (g, h) • π t t') :
    tensorProductCoeff N N' ∈ homogeneousMatrices (tensorGradedPart Ag Bg lA lB)
      (fun p ↦ π (gr p.1) (gr' p.2)) (fun p ↦ π (gr p.1) (gr' p.2)) (lA, 1) := by
  have h₁ := kroneckerTMul_mem_homogeneousMatrices (lA := lA) (lB := lB) hπ hN
    (idMorphism_mem_homogeneousMatrices N' hιB gr')
  have h₂ := kroneckerTMul_mem_homogeneousMatrices (lA := lA) (lB := lB) hπ
    (idMorphism_mem_homogeneousMatrices N hιA gr) hN'
  -- The term `1 ⊗ δ'` has degree `(1, l_B)`, which the parts of `A ⊗ B` identify with `(l_A, 1)`.
  have h := homogeneousMatrices_tensorGradedPart_mul_left_eq (Ag := Ag) (Bg := Bg) (lA := lA)
    (lB := lB) (fun p : X × X' ↦ π (gr p.1) (gr' p.2)) (fun p : X × X' ↦ π (gr p.1) (gr' p.2)) 1
  rw [mul_one, mul_one] at h
  rw [tensorProductCoeff_def, h]
  exact add_mem (h ▸ h₁) h₂

end TypeDStructure

end TauCeti
