/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Data.Matrix.Mul

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# Complexes of free modules given by graded matrices

Let `ι` be a finite set of generators graded by `e : ι → A`, for an index `A` such as `ℤ` or
`ZMod n`, and let `D : Matrix ι ι R` be a square matrix over a commutative ring, read by rows: the
differential of the generator `i` is `∑ₖ D i k • k`. If `D` raises degrees by one,
`D i k ≠ 0 → e k = e i + 1`, and `D * D = 0`, then the free modules `R^{e⁻¹(a)}` on the generators
of each degree `a` form a complex for the shape `ComplexShape.up A`
(`TauCeti.gradedMatrixComplex`). Its term of degree `a` has the generators of degree `a` as a basis
(`TauCeti.gradedMatrixComplexBasis`), on which the differential is given by the rows of `D`
(`TauCeti.gradedMatrixComplex_d_basis`).

A degree-preserving matrix `Φ` with `D * Φ = Φ * D'` gives a chain map, again read by rows
(`TauCeti.gradedMatrixComplexHom`, `TauCeti.gradedMatrixComplexHom_f_basis`). Composition of such
chain maps is the product of their matrices (`TauCeti.gradedMatrixComplexHom_comp`), and the
identity matrix gives the identity (`TauCeti.gradedMatrixComplexHom_one`). A matrix `K` lowering
degrees by one with `Φ - Ψ = D * K + K * D'` gives a chain homotopy between the maps of `Φ` and
`Ψ` (`TauCeti.gradedMatrixComplexHomotopy`), so two matrices inverse to each other up to such
homotopies give a homotopy equivalence (`TauCeti.gradedMatrixComplexHomotopyEquiv`), whose maps
are the chain maps of the two matrices.

Over a field and with finitely many degrees, the total dimension of the homology of a complex
homotopy equivalent to `gradedMatrixComplex e D` is at most the number of generators
(`TauCeti.sum_finrank_homology_le_card_of_homotopyEquiv`). This is the chain-rank inequality
behind lower bounds for the number of generators of cyclically graded complexes, for instance the
number of periodic orbits of a Hamiltonian, whose Floer complex is graded modulo twice the minimal
Chern number.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*,
  IAS/Park City Math. Ser. 7 (1999), 143–229, on the rank inequality for the Arnold conjecture.
-/

public section

noncomputable section

open CategoryTheory Matrix Module

namespace TauCeti

universe u v

section Block

variable {R : Type u} [CommRing R] {A : Type*} [DecidableEq A] {ι κ ν : Type v} [Fintype ι]
  [Fintype κ]

/-- The block of a matrix `M` with rows of degree `a` for `e` and columns of degree `b` for `f`,
as a linear map of row vectors. -/
private def blockMap (e : ι → A) (f : κ → A) (a b : A) (M : Matrix ι κ R) :
    ModuleCat.of R ({i // e i = a} → R) ⟶ ModuleCat.of R ({k // f k = b} → R) :=
  ModuleCat.ofHom (M.submatrix Subtype.val Subtype.val).vecMulLinear

private theorem blockMap_basisFun (e : ι → A) (f : κ → A) (a b : A) (M : Matrix ι κ R)
    (i : {i // e i = a}) :
    (blockMap e f a b M).hom (Pi.basisFun R _ i) =
      ∑ k : {k // f k = b}, M i k • Pi.basisFun R _ k := by
  classical
  ext k
  simp [blockMap, Pi.basisFun_apply, Finset.sum_apply, Pi.single_apply]

private theorem blockMap_comp (e : ι → A) (f : κ → A) (g : ν → A) (a b c : A)
    (M : Matrix ι κ R) (N : Matrix κ ν R) (hM : ∀ i j, M i j ≠ 0 → e i = a → f j = b) :
    blockMap e f a b M ≫ blockMap f g b c N = blockMap e g a c (M * N) := by
  ext x : 2
  simp only [blockMap, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, vecMulLinear_apply, vecMul_vecMul,
    ← submatrix_mul_of_injective M N (Subtype.val : {i // e i = a} → ι)
      (Subtype.val : {j // f j = b} → κ) (Subtype.val : {k // g k = c} → ν)
      Subtype.val_injective fun i j h ↦ ⟨⟨j, hM i j h i.property⟩, rfl⟩]

private theorem blockMap_one [DecidableEq ι] (e : ι → A) (a : A) :
    blockMap e e a a (1 : Matrix ι ι R) = 𝟙 _ :=
  ModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
    simp [blockMap, submatrix_one _ Subtype.val_injective]

omit [Fintype κ] in
private theorem blockMap_eq_zero (e : ι → A) (f : κ → A) (a b : A) {M : Matrix ι κ R}
    (hM : ∀ i k, M i k ≠ 0 → e i = a → f k ≠ b) : blockMap e f a b M = 0 := by
  ext x k
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases h : M i k = 0
  · simp [h]
  · exact (hM i k h i.property k.property).elim

end Block

section Complex

variable {R : Type u} [CommRing R] {A : Type*} [AddRightCancelSemigroup A] [One A]
  [DecidableEq A] {ι κ ν : Type v} [Fintype ι] [Fintype κ] [Fintype ν]

variable (e : ι → A) (D : Matrix ι ι R) (hD : ∀ i k, D i k ≠ 0 → e k = e i + 1)
  (hDD : D * D = 0)

/-- The complex of free modules on the generators `ι` graded by `e`, with differential the matrix
`D` read by rows: its term of degree `a` is `R^{e⁻¹(a)}`, with the generators of degree `a` as
basis (`TauCeti.gradedMatrixComplexBasis`), and its differential sends the generator `i` to
`∑ₖ D i k • k` (`TauCeti.gradedMatrixComplex_d_basis`). -/
def gradedMatrixComplex : HomologicalComplex (ModuleCat.{max u v} R) (ComplexShape.up A) where
  X a := ModuleCat.of R ({i // e i = a} → R)
  d a b := blockMap e e a b D
  shape a b hab := blockMap_eq_zero e e a b fun i k h hi hk ↦
    hab (by rw [ComplexShape.up_Rel, ← hi, ← hk, hD i k h])
  d_comp_d' a b c hab _ := by
    rw [blockMap_comp e e e a b c D D fun i j h hi ↦ by rw [hD i j h, hi]; exact hab, hDD]
    exact blockMap_eq_zero e e a c fun i k h ↦ (h rfl).elim

/-- The basis of the term of degree `a` of `gradedMatrixComplex e D` given by the generators of
degree `a`. -/
def gradedMatrixComplexBasis (a : A) :
    Module.Basis {i // e i = a} R ((gradedMatrixComplex e D hD hDD).X a) :=
  Pi.basisFun R {i // e i = a}

variable {e D hD hDD}

/-- The differential of `gradedMatrixComplex e D` sends the generator `i` to `∑ₖ D i k • k`. -/
@[simp]
theorem gradedMatrixComplex_d_basis (a b : A) (i : {i // e i = a}) :
    ((gradedMatrixComplex e D hD hDD).d a b).hom (gradedMatrixComplexBasis e D hD hDD a i) =
      ∑ k : {k // e k = b}, D i k • gradedMatrixComplexBasis e D hD hDD b k :=
  blockMap_basisFun e e a b D i

instance (a : A) : Module.Free R ((gradedMatrixComplex e D hD hDD).X a) :=
  Module.Free.of_basis (gradedMatrixComplexBasis e D hD hDD a)

instance (a : A) : Module.Finite R ((gradedMatrixComplex e D hD hDD).X a) :=
  Module.Finite.of_basis (gradedMatrixComplexBasis e D hD hDD a)

/-- The term of degree `a` of `gradedMatrixComplex e D` is free on the generators of degree
`a`. -/
theorem finrank_gradedMatrixComplex_X [Nontrivial R] (a : A) :
    finrank R ((gradedMatrixComplex e D hD hDD).X a) = Fintype.card {i // e i = a} :=
  Module.finrank_eq_card_basis (gradedMatrixComplexBasis e D hD hDD a)

variable {e' : κ → A} {D' : Matrix κ κ R} {hD' : ∀ i k, D' i k ≠ 0 → e' k = e' i + 1}
  {hDD' : D' * D' = 0} {e'' : ν → A} {D'' : Matrix ν ν R}
  {hD'' : ∀ i k, D'' i k ≠ 0 → e'' k = e'' i + 1} {hDD'' : D'' * D'' = 0}

/-- The chain map given by a degree-preserving matrix `Φ` commuting with the differentials,
`D * Φ = Φ * D'`, read by rows: it sends the generator `i` to `∑ₖ Φ i k • k`
(`TauCeti.gradedMatrixComplexHom_f_basis`). -/
def gradedMatrixComplexHom (Φ : Matrix ι κ R) (hΦ : ∀ i k, Φ i k ≠ 0 → e' k = e i)
    (hΦD : D * Φ = Φ * D') :
    gradedMatrixComplex e D hD hDD ⟶ gradedMatrixComplex e' D' hD' hDD' where
  f a := blockMap e e' a a Φ
  comm' a b hab := by
    -- The differentials and the chain maps of these complexes are blocks of matrices by
    -- definition.
    change blockMap e e' a a Φ ≫ blockMap e' e' a b D' = blockMap e e a b D ≫ blockMap e e' b b Φ
    rw [blockMap_comp e e' e' a a b Φ D' fun i j h hi ↦ by rw [hΦ i j h, hi],
      blockMap_comp e e e' a b b D Φ fun i j h hi ↦ by rw [hD i j h, hi]; exact hab, hΦD]

/-- The chain map of a matrix `Φ` sends the generator `i` to `∑ₖ Φ i k • k`. -/
@[simp]
theorem gradedMatrixComplexHom_f_basis {Φ : Matrix ι κ R} {hΦ : ∀ i k, Φ i k ≠ 0 → e' k = e i}
    {hΦD : D * Φ = Φ * D'} (a : A) (i : {i // e i = a}) :
    ((gradedMatrixComplexHom (hD' := hD') (hDD' := hDD') Φ hΦ hΦD).f a).hom
        (gradedMatrixComplexBasis e D hD hDD a i) =
      ∑ k : {k // e' k = a}, Φ i k • gradedMatrixComplexBasis e' D' hD' hDD' a k :=
  blockMap_basisFun e e' a a Φ i

/-- The composite of the chain maps of two matrices is the chain map of their product. -/
theorem gradedMatrixComplexHom_comp {Φ : Matrix ι κ R} {Ψ : Matrix κ ν R}
    {hΦ : ∀ i k, Φ i k ≠ 0 → e' k = e i} {hΦD : D * Φ = Φ * D'}
    {hΨ : ∀ i k, Ψ i k ≠ 0 → e'' k = e' i} {hΨD : D' * Ψ = Ψ * D''} :
    gradedMatrixComplexHom (hD' := hD') (hDD' := hDD') Φ hΦ hΦD ≫
        gradedMatrixComplexHom (hD' := hD'') (hDD' := hDD'') Ψ hΨ hΨD =
      gradedMatrixComplexHom (hD := hD) (hDD := hDD) (Φ * Ψ) (eq_of_mul_apply_ne_zero hΦ hΨ)
        (mul_mul_eq_mul_mul_of_mul_eq_mul hΦD hΨD) := by
  refine HomologicalComplex.hom_ext _ _ fun a ↦ ?_
  exact blockMap_comp e e' e'' a a a Φ Ψ fun i j h hi ↦ by rw [hΦ i j h, hi]

/-- The identity matrix gives the identity chain map. -/
theorem gradedMatrixComplexHom_one [DecidableEq ι]
    {h₁ : ∀ i k, (1 : Matrix ι ι R) i k ≠ 0 → e k = e i} {h₁D : D * 1 = 1 * D} :
    gradedMatrixComplexHom (hD := hD) (hDD := hDD) (hD' := hD) (hDD' := hDD) 1 h₁ h₁D =
      𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun a ↦ ?_
  exact blockMap_one e a

end Complex

section Homotopy

variable {R : Type u} [CommRing R] {A : Type*} [AddGroup A] [One A] [DecidableEq A]
  {ι κ : Type v} [Fintype ι] [Fintype κ] {e : ι → A} {D : Matrix ι ι R}
  {hD : ∀ i k, D i k ≠ 0 → e k = e i + 1} {hDD : D * D = 0} {e' : κ → A} {D' : Matrix κ κ R}
  {hD' : ∀ i k, D' i k ≠ 0 → e' k = e' i + 1} {hDD' : D' * D' = 0}

/-- The components of the chain homotopy of a matrix `K`: its blocks, between the terms of the two
complexes. -/
private def homotopyBlock (K : Matrix ι κ R) (a b : A) :
    (gradedMatrixComplex e D hD hDD).X a ⟶ (gradedMatrixComplex e' D' hD' hDD').X b :=
  blockMap e e' a b K

/-- A matrix `K` lowering degrees by one with `Φ - Ψ = D * K + K * D'` is a chain homotopy between
the chain maps of `Φ` and `Ψ`. -/
def gradedMatrixComplexHomotopy {Φ Ψ : Matrix ι κ R} {hΦ : ∀ i k, Φ i k ≠ 0 → e' k = e i}
    {hΦD : D * Φ = Φ * D'} {hΨ : ∀ i k, Ψ i k ≠ 0 → e' k = e i} {hΨD : D * Ψ = Ψ * D'}
    (K : Matrix ι κ R) (hK : ∀ i k, K i k ≠ 0 → e' k + 1 = e i)
    (hΦΨ : Φ - Ψ = D * K + K * D') :
    Homotopy (gradedMatrixComplexHom (hD := hD) (hDD := hDD) (hD' := hD') (hDD' := hDD') Φ hΦ hΦD)
      (gradedMatrixComplexHom Ψ hΨ hΨD) where
  hom := homotopyBlock K
  zero a b hab := blockMap_eq_zero e e' a b fun i k h hi hk ↦
    hab (by rw [ComplexShape.up_Rel, ← hi, ← hk, hK i k h])
  comm a := by
    rw [dNext_eq _ (show (ComplexShape.up A).Rel a (a + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up A).Rel (a - 1) a from sub_add_cancel a 1)]
    -- The differentials and the chain maps of these complexes are blocks of matrices by
    -- definition.
    change blockMap e e' a a Φ = blockMap e e a (a + 1) D ≫ blockMap e e' (a + 1) a K +
      blockMap e e' a (a - 1) K ≫ blockMap e' e' (a - 1) a D' + blockMap e e' a a Ψ
    rw [blockMap_comp e e e' a (a + 1) a D K fun i j h hi ↦ by rw [hD i j h, hi],
      blockMap_comp e e' e' a (a - 1) a K D' fun i j h hi ↦ by
        rw [← hi, ← hK i j h, add_sub_cancel_right]]
    ext x : 2
    simp only [blockMap, ModuleCat.hom_add, ModuleCat.hom_ofHom, LinearMap.add_apply,
      vecMulLinear_apply, ← vecMul_add]
    rw [sub_eq_iff_eq_add.mp hΦΨ]
    simp only [submatrix_add, Pi.add_apply]

/-- The chain homotopy of a matrix `K` sends the generator `i` of degree `a` to `∑ₖ K i k • k`,
over the generators `k` of degree `b`. -/
@[simp]
theorem gradedMatrixComplexHomotopy_hom_basis {Φ Ψ : Matrix ι κ R}
    {hΦ : ∀ i k, Φ i k ≠ 0 → e' k = e i} {hΦD : D * Φ = Φ * D'}
    {hΨ : ∀ i k, Ψ i k ≠ 0 → e' k = e i} {hΨD : D * Ψ = Ψ * D'} {K : Matrix ι κ R}
    {hK : ∀ i k, K i k ≠ 0 → e' k + 1 = e i} {hΦΨ : Φ - Ψ = D * K + K * D'} (a b : A)
    (i : {i // e i = a}) :
    ((gradedMatrixComplexHomotopy (hΦ := hΦ) (hΦD := hΦD) (hΨ := hΨ) (hΨD := hΨD) K hK
        hΦΨ).hom a b).hom (gradedMatrixComplexBasis e D hD hDD a i) =
      ∑ k : {k // e' k = b}, K i k • gradedMatrixComplexBasis e' D' hD' hDD' b k :=
  blockMap_basisFun e e' a b K i

/-- Matrices `Φ` and `Ψ` inverse to each other up to homotopies `K` and `K'`,
`Φ * Ψ - 1 = D * K + K * D` and `Ψ * Φ - 1 = D' * K' + K' * D'`, give a homotopy equivalence
between the complexes of `D` and `D'`. Its maps are the chain maps of `Φ` and `Ψ`
(`TauCeti.gradedMatrixComplexHomotopyEquiv_hom`, `TauCeti.gradedMatrixComplexHomotopyEquiv_inv`).
-/
def gradedMatrixComplexHomotopyEquiv [DecidableEq ι] [DecidableEq κ] (Φ : Matrix ι κ R)
    (Ψ : Matrix κ ι R) (hΦ : ∀ i k, Φ i k ≠ 0 → e' k = e i) (hΦD : D * Φ = Φ * D')
    (hΨ : ∀ i k, Ψ i k ≠ 0 → e k = e' i) (hΨD : D' * Ψ = Ψ * D) (K : Matrix ι ι R)
    (hK : ∀ i k, K i k ≠ 0 → e k + 1 = e i) (hΦΨ : Φ * Ψ - 1 = D * K + K * D)
    (K' : Matrix κ κ R) (hK' : ∀ i k, K' i k ≠ 0 → e' k + 1 = e' i)
    (hΨΦ : Ψ * Φ - 1 = D' * K' + K' * D') :
    HomotopyEquiv (gradedMatrixComplex e D hD hDD) (gradedMatrixComplex e' D' hD' hDD') where
  hom := gradedMatrixComplexHom Φ hΦ hΦD
  inv := gradedMatrixComplexHom Ψ hΨ hΨD
  homotopyHomInvId := by
    rw [gradedMatrixComplexHom_comp, ← gradedMatrixComplexHom_one (h₁ := eq_of_one_apply_ne_zero)
      (h₁D := by rw [Matrix.mul_one, Matrix.one_mul])]
    exact gradedMatrixComplexHomotopy K hK hΦΨ
  homotopyInvHomId := by
    rw [gradedMatrixComplexHom_comp, ← gradedMatrixComplexHom_one (h₁ := eq_of_one_apply_ne_zero)
      (h₁D := by rw [Matrix.mul_one, Matrix.one_mul])]
    exact gradedMatrixComplexHomotopy K' hK' hΨΦ

section HomotopyEquiv

variable [DecidableEq ι] [DecidableEq κ] {Φ : Matrix ι κ R} {Ψ : Matrix κ ι R}
  {hΦ : ∀ i k, Φ i k ≠ 0 → e' k = e i} {hΦD : D * Φ = Φ * D'} {hΨ : ∀ i k, Ψ i k ≠ 0 → e k = e' i}
  {hΨD : D' * Ψ = Ψ * D} {K : Matrix ι ι R} {hK : ∀ i k, K i k ≠ 0 → e k + 1 = e i}
  {hΦΨ : Φ * Ψ - 1 = D * K + K * D} {K' : Matrix κ κ R}
  {hK' : ∀ i k, K' i k ≠ 0 → e' k + 1 = e' i} {hΨΦ : Ψ * Φ - 1 = D' * K' + K' * D'}

/-- The forward map of the homotopy equivalence of `Φ` and `Ψ` is the chain map of `Φ`. -/
@[simp]
theorem gradedMatrixComplexHomotopyEquiv_hom :
    (gradedMatrixComplexHomotopyEquiv (hD := hD) (hDD := hDD) (hD' := hD') (hDD' := hDD') Φ Ψ hΦ
        hΦD hΨ hΨD K hK hΦΨ K' hK' hΨΦ).hom =
      gradedMatrixComplexHom Φ hΦ hΦD :=
  (rfl)

/-- The backward map of the homotopy equivalence of `Φ` and `Ψ` is the chain map of `Ψ`. -/
@[simp]
theorem gradedMatrixComplexHomotopyEquiv_inv :
    (gradedMatrixComplexHomotopyEquiv (hD := hD) (hDD := hDD) (hD' := hD') (hDD' := hDD') Φ Ψ hΦ
        hΦD hΨ hΨD K hK hΦΨ K' hK' hΨΦ).inv =
      gradedMatrixComplexHom Ψ hΨ hΨD :=
  (rfl)

end HomotopyEquiv

end Homotopy

section Finrank

variable {k : Type u} [Field k] {A : Type*} [AddRightCancelSemigroup A] [One A] [DecidableEq A]
  [Fintype A] {ι : Type v} [Fintype ι] {e : ι → A} {D : Matrix ι ι k}
  {hD : ∀ i k, D i k ≠ 0 → e k = e i + 1} {hDD : D * D = 0}

/-- **The chain-rank inequality.** A complex homotopy equivalent to the complex of a graded matrix
over a field, with finitely many degrees, has total homology of dimension at most the number of
generators. -/
theorem sum_finrank_homology_le_card_of_homotopyEquiv
    {C : HomologicalComplex (ModuleCat.{max u v} k) (ComplexShape.up A)}
    (E : HomotopyEquiv (gradedMatrixComplex e D hD hDD) C) :
    ∑ a, finrank k (C.homology a) ≤ Fintype.card ι := by
  calc ∑ a, finrank k (C.homology a)
      = ∑ a, finrank k ((gradedMatrixComplex e D hD hDD).homology a) :=
        Finset.sum_congr rfl fun a _ ↦ (E.toHomologyIso a).toLinearEquiv.finrank_eq.symm
    _ ≤ ∑ a, finrank k ((gradedMatrixComplex e D hD hDD).X a) :=
        Finset.sum_le_sum fun a _ ↦ HomologicalComplex.finrank_homology_le_finrank_X _ a
    _ = Fintype.card ι := by
        simp_rw [finrank_gradedMatrixComplex_X]
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv e)

end Finrank

end TauCeti
