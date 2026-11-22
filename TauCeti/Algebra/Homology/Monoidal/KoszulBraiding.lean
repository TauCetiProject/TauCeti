/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ComplexShape.Signs
public import TauCeti.Algebra.Homology.Monoidal.Cup
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Symmetry

/-!
# Koszul interchange of cochains and cup products

For nonnegative chain complexes `A` and `B` in a braided preadditive monoidal category, the
signed interchange `HomologicalComplex.tensorBraiding A B : A ⊗ B ≅ B ⊗ A` is, on the summand of
bidegree `(p, q)`, the coefficient braiding multiplied by the Koszul sign `(-1)^(p*q)`
(`HomologicalComplex.ιTensorObj_tensorBraiding_hom_f` with `ComplexShape.σ_down_ℕ`). This file
computes how it acts on tensor products of cochains and on cup products.

The tensor-cochain formula is the chain-level interchange needed to compare the Alexander–Whitney
diagonal with its transpose, and hence to prove graded commutativity of cup products. The cup
formulas give signed interchange along a transposed diagonal, with the braided coefficient
pairing. No commutativity is asserted for the Alexander–Whitney diagonal itself.

## Main results

* `TauCeti.ChainComplex.tensorBraiding_hom_f_comp_tensorCochain`: signed tensor-cochain
  interchange in every output degree.
* `TauCeti.ChainComplex.cupCochain_tensorBraiding_hom`: signed cup-cochain interchange.
* `TauCeti.ChainComplex.cup_tensorBraiding_hom`: signed interchange on cohomology.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, for the graded-commutativity sign.
* C. Weibel, *An Introduction to Homological Algebra*, Section 2.7, for tensor complexes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]

section Cochain

variable [BraidedCategory C]

/-- Precomposing a tensor product of cochains with the signed interchange swaps the cochains and
braids their coefficient pairing, with sign `(-1)^(p*q)`. This holds in every output degree,
including `n ≠ p + q`, where both sides are zero. -/
@[reassoc]
lemma tensorBraiding_hom_f_comp_tensorCochain {M N P : C} (μ : N ⊗ M ⟶ P) {p q : ℕ}
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (tensorBraiding A B).hom.f n ≫ tensorCochain μ ψ φ n =
      ((-1 : ℤ) ^ (p * q)) • tensorCochain ((β_ M N).hom ≫ μ) φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ιTensorObj_tensorBraiding_hom_f_assoc, ComplexShape.σ_down_ℕ, Units.smul_def,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Preadditive.comp_zsmul]
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
lemma cupCochain_tensorBraiding_hom {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommSemiring k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ tensorObj A B) (μ : N ⊗ M ⟶ P)
    {p q n : ℕ} (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k (D ≫ (tensorBraiding A B).hom) μ q p n (by omega) ψ φ =
      ((-1 : ℤ) ^ (p * q)) • cupCochain k D ((β_ M N).hom ≫ μ) p q n h φ ψ := by
  simp only [cupCochain_apply, HomologicalComplex.comp_f, Category.assoc,
    tensorBraiding_hom_f_comp_tensorCochain, Preadditive.comp_zsmul]

end Cochain

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]

/-- Transposing a diagonal swaps the cup product on cohomology, with the Koszul sign and
the braided coefficient pairing. -/
lemma cup_tensorBraiding_hom {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ HomologicalComplex.tensorObj A B)
    (μ : N ⊗ M ⟶ P) {p q n : ℕ} (h : p + q = n) (a : (A.linearYonedaObj k M).homology p)
    (b : (B.linearYonedaObj k N).homology q) :
    cup k (D ≫ (tensorBraiding A B).hom) μ q p n (by omega) b a =
      ((-1 : ℤ) ^ (p * q)) • cup k D ((β_ M N).hom ≫ μ) p q n h a b := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  simp only [cup_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [iCycles_cupCycles, map_zsmul]
  exact cupCochain_tensorBraiding_hom A B k D μ h _ _

end TauCeti.ChainComplex
