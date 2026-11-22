/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ComplexShape.Signs
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.Algebra.Homology.Monoidal.Cup

/-!
# Koszul braiding for nonnegative chain complexes

On the summand of bidegree `(p, q)`, interchange of tensor factors carries the sign
`(-1)^(p*q)` to commute with the differential. For chain complexes indexed by `ℕ`, this
interchange is the shape-generic `HomologicalComplex.koszulBraiding` of
`TauCeti/Algebra/Homology/Monoidal/Braiding.lean`, whose sign at `ComplexShape.down ℕ` is that of
the instance `HomologicalComplex₂.totalComplexShapeSymmetryDownNat`. It exists in any braided
preadditive monoidal category, assuming only that the two tensor complexes exist. This file
evaluates it on each summand with the sign `(-1)^(p*q)`. Since that sign is symmetric
(`HomologicalComplex₂.totalComplexShapeSymmetrySymmetryDownNat`), the general
`HomologicalComplex.koszulBraiding_inv` and `HomologicalComplex.koszulBraiding_hom_comp_hom`
apply in a symmetric category: the inverse is the interchange of the swapped factors, and
interchanging twice is the identity.

The tensor-cochain formula is the chain-level interchange needed to compare the Alexander–Whitney
diagonal with its transpose, and hence to prove graded commutativity of cup products. The cup
formulas give signed interchange along a transposed diagonal, with the braided coefficient
pairing. No commutativity is asserted for the Alexander–Whitney diagonal itself.

## Main definitions and results

* `TauCeti.NatChainComplex.ιTensorObj_koszulBraiding_hom_f` and
  `TauCeti.NatChainComplex.ιTensorObj_koszulBraiding_inv_f`: the interchange and its inverse on
  each bidegree summand, with the sign `(-1)^(p*q)`.
* `TauCeti.NatChainComplex.koszulBraiding_hom_f_comp_tensorCochain`: signed tensor-cochain
  interchange in every output degree.
* `TauCeti.NatChainComplex.cupCochain_koszulBraiding_hom`: signed cup-cochain interchange.
* `TauCeti.NatChainComplex.cup_koszulBraiding_hom`: signed interchange on cohomology.

## Implementation notes

The `TauCeti.NatChainComplex` namespace distinguishes these lemmas from the integer-indexed
cochain braiding. The tensor-cochain and cup formulas use the existing API in
`TauCeti.ChainComplex`.

The summand rules restate `HomologicalComplex.ιTensorObj_koszulBraiding_hom_f` and
`HomologicalComplex.ιTensorObj_koszulBraiding_inv_f` with the sign evaluated as the integer
`(-1)^(p*q)`. They have higher `simp` priority than the general rules, so that `simp` uses them
on chain complexes indexed by `ℕ`. The interchange requires no monoidal structure on the entire
category of complexes.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, for the graded-commutativity sign.
* C. Weibel, *An Introduction to Homological Algebra*, Section 2.7, for tensor complexes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.NatChainComplex

open TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]

section Braided

variable [BraidedCategory C]

/-- On the bidegree-`(p, q)` summand, the Koszul braiding `HomologicalComplex.koszulBraiding` of
chain complexes is the coefficient braiding multiplied by `(-1)^(p*q)`, followed by the inclusion
of the swapped summand. -/
@[reassoc (attr := simp high)]
lemma ιTensorObj_koszulBraiding_hom_f (p q n : ℕ) (h : p + q = n) :
    ιTensorObj A B p q n h ≫ (HomologicalComplex.koszulBraiding A B).hom.f n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
        ιTensorObj B A q p n (by omega)) := by
  rw [HomologicalComplex.ιTensorObj_koszulBraiding_hom_f, Units.smul_def]
  -- The sign of `HomologicalComplex₂.totalComplexShapeSymmetryDownNat` is `(-1)^(q*p)`.
  change (((-1 : ℤˣ) ^ (q * p) : ℤˣ) : ℤ) • _ = _
  simp [Nat.mul_comm q p]

/-- On the bidegree-`(q, p)` summand, the inverse Koszul braiding is the inverse coefficient
braiding multiplied by `(-1)^(p*q)`, followed by the inclusion of the swapped summand. -/
@[reassoc (attr := simp high)]
lemma ιTensorObj_koszulBraiding_inv_f (p q n : ℕ) (h : q + p = n) :
    ιTensorObj B A q p n h ≫ (HomologicalComplex.koszulBraiding A B).inv.f n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).inv ≫
        ιTensorObj A B p q n (by omega)) := by
  rw [HomologicalComplex.ιTensorObj_koszulBraiding_inv_f, Units.smul_def]
  -- The sign of `HomologicalComplex₂.totalComplexShapeSymmetryDownNat` is `(-1)^(q*p)`.
  change (((-1 : ℤˣ) ^ (q * p) : ℤˣ) : ℤ) • _ = _
  simp [Nat.mul_comm q p]

end Braided

section Cochain

variable [BraidedCategory C]

/-- Precomposing a tensor product of cochains with Koszul interchange swaps the cochains and
braids their coefficient pairing, with sign `(-1)^(p*q)`. This holds in every output degree,
including `n ≠ p + q`, where both sides are zero. -/
@[reassoc]
lemma koszulBraiding_hom_f_comp_tensorCochain {M N P : C} (μ : N ⊗ M ⟶ P) {p q : ℕ}
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (HomologicalComplex.koszulBraiding A B).hom.f n ≫ tensorCochain μ ψ φ n =
      ((-1 : ℤ) ^ (p * q)) • tensorCochain ((β_ M N).hom ≫ μ) φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ιTensorObj_koszulBraiding_hom_f_assoc, Preadditive.comp_zsmul]
  by_cases hi : i = p
  · subst i
    by_cases hj : j = q
    · subst j
      simp only [ιTensorObj_tensorCochain, Preadditive.zsmul_comp, Category.assoc]
      rw [BraidedCategory.braiding_naturality_assoc]
    · simp [ιTensorObj_tensorCochain_of_ne_left _ _ _ _ hj,
        ιTensorObj_tensorCochain_of_ne_right _ _ _ _ hj]
  · simp [ιTensorObj_tensorCochain_of_ne_right _ _ _ _ hi,
      ιTensorObj_tensorCochain_of_ne_left _ _ _ _ hi]

/-- Transposing a diagonal swaps its cup product of cochains, braids the pairing, and
introduces the Koszul sign. -/
lemma cupCochain_koszulBraiding_hom {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommSemiring k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ tensorObj A B) (μ : N ⊗ M ⟶ P)
    {p q n : ℕ} (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k (D ≫ (HomologicalComplex.koszulBraiding A B).hom) μ q p n (by omega) ψ φ =
      ((-1 : ℤ) ^ (p * q)) • cupCochain k D ((β_ M N).hom ≫ μ) p q n h φ ψ := by
  simp only [cupCochain_apply, HomologicalComplex.comp_f, Category.assoc,
    koszulBraiding_hom_f_comp_tensorCochain, Preadditive.comp_zsmul]

end Cochain

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]

/-- Transposing a diagonal swaps the cup product on cohomology, with the Koszul sign and
the braided coefficient pairing. -/
lemma cup_koszulBraiding_hom {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ HomologicalComplex.tensorObj A B)
    (μ : N ⊗ M ⟶ P) {p q n : ℕ} (h : p + q = n) (a : (A.linearYonedaObj k M).homology p)
    (b : (B.linearYonedaObj k N).homology q) :
    cup k (D ≫ (HomologicalComplex.koszulBraiding A B).hom) μ q p n (by omega) b a =
      ((-1 : ℤ) ^ (p * q)) • cup k D ((β_ M N).hom ≫ μ) p q n h a b := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  simp only [cup_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [iCycles_cupCycles, map_zsmul]
  exact cupCochain_koszulBraiding_hom A B k D μ h _ _

end TauCeti.NatChainComplex
