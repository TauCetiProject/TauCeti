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
# Koszul braiding for nonnegative chain complexes

On the summand of bidegree `(p, q)`, interchange of tensor factors carries the sign
`(-1)^(p*q)` to commute with the differential. `TauCeti.NatChainComplex.koszulBraidingHom`
is this chain map in any braided preadditive monoidal category, assuming only that the two tensor
complexes exist: it is the signed interchange `HomologicalComplex.tensorBraiding` for the signs
of `HomologicalComplex₂.totalComplexShapeSymmetryDownNat`. It is an isomorphism in a braided
category; in a symmetric category, its inverse is the same construction with the factors
swapped.

The tensor-cochain formula is the chain-level interchange needed to compare the Alexander–Whitney
diagonal with its transpose, and hence to prove graded commutativity of cup products. The cup
formulas give signed interchange along a transposed diagonal, with the braided coefficient
pairing. No commutativity is asserted for the Alexander–Whitney diagonal itself.

## Main definitions and results

* `TauCeti.NatChainComplex.koszulBraidingHom`: the signed interchange chain map.
* `TauCeti.NatChainComplex.ιTensorObj_koszulBraidingHom_f`: its value on each bidegree summand.
* `TauCeti.NatChainComplex.koszulBraidingHom_naturality`: naturality in both chain complexes.
* `TauCeti.NatChainComplex.koszulBraidingHom_comp`: interchanging twice is the identity in a
  symmetric category.
* `TauCeti.NatChainComplex.koszulBraidingHom_f_comp_tensorCochain`: signed tensor-cochain
  interchange in every output degree.
* `TauCeti.NatChainComplex.cupCochain_koszulBraidingHom`: signed cup-cochain interchange.
* `TauCeti.NatChainComplex.cup_koszulBraidingHom`: signed interchange on cohomology.

## Implementation notes

The `TauCeti.NatChainComplex` namespace distinguishes this construction from the
integer-indexed cochain braiding. The tensor-cochain and cup formulas use the existing API in
`TauCeti.ChainComplex`.

The interchange, its inverse, naturality and symmetry come from the generic
`HomologicalComplex.tensorBraiding` API, specialized to `ComplexShape.down ℕ`; the summand formula
`TauCeti.NatChainComplex.ιTensorObj_koszulBraidingHom_f` states the sign as an integer power. The
construction requires no monoidal structure on the entire category of complexes.

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

/-- Interchange the factors of a tensor product of nonnegative chain complexes, with the
Koszul sign `(-1)^(p*q)` on its bidegree-`(p, q)` summand: the signed interchange
`HomologicalComplex.tensorBraiding` for the signs of
`HomologicalComplex₂.totalComplexShapeSymmetryDownNat`. -/
def koszulBraidingHom : tensorObj A B ⟶ tensorObj B A :=
  (HomologicalComplex.tensorBraiding A B).hom

/-- On the bidegree-`(p, q)` summand, interchange is the coefficient braiding multiplied by
`(-1)^(p*q)`, followed by the inclusion of the swapped summand. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_koszulBraidingHom_f (p q n : ℕ) (h : p + q = n) :
    ιTensorObj A B p q n h ≫ (koszulBraidingHom A B).f n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
        ιTensorObj B A q p n (by omega)) := by
  rw [koszulBraidingHom, HomologicalComplex.ιTensorObj_tensorBraiding_hom_f, Units.smul_def,
    ComplexShape.σ_down_ℕ, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- Koszul interchange is natural in both chain complexes. -/
@[reassoc]
lemma koszulBraidingHom_naturality {A' B' : ChainComplex C ℕ} [A'.HasTensor B'] [B'.HasTensor A']
    (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom f g ≫ koszulBraidingHom A' B' = koszulBraidingHom A B ≫ tensorHom g f :=
  HomologicalComplex.tensorBraiding_hom_naturality f g

instance : IsIso (koszulBraidingHom A B) := (HomologicalComplex.tensorBraiding A B).isIso_hom

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- In a symmetric category, interchanging tensor factors twice is the identity chain map. -/
@[reassoc (attr := simp)]
lemma koszulBraidingHom_comp : koszulBraidingHom A B ≫ koszulBraidingHom B A = 𝟙 _ :=
  HomologicalComplex.tensorBraiding_hom_comp_tensorBraiding_hom A B

end Symmetric

section Cochain

variable [BraidedCategory C]

/-- Precomposing a tensor product of cochains with Koszul interchange swaps the cochains and
braids their coefficient pairing, with sign `(-1)^(p*q)`. This holds in every output degree,
including `n ≠ p + q`, where both sides are zero. -/
@[reassoc]
lemma koszulBraidingHom_f_comp_tensorCochain {M N P : C} (μ : N ⊗ M ⟶ P) {p q : ℕ}
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (koszulBraidingHom A B).f n ≫ tensorCochain μ ψ φ n =
      ((-1 : ℤ) ^ (p * q)) • tensorCochain ((β_ M N).hom ≫ μ) φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ιTensorObj_koszulBraidingHom_f_assoc, Preadditive.comp_zsmul]
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
lemma cupCochain_koszulBraidingHom {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommSemiring k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ tensorObj A B) (μ : N ⊗ M ⟶ P)
    {p q n : ℕ} (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k (D ≫ koszulBraidingHom A B) μ q p n (by omega) ψ φ =
      ((-1 : ℤ) ^ (p * q)) • cupCochain k D ((β_ M N).hom ≫ μ) p q n h φ ψ := by
  simp only [cupCochain_apply, HomologicalComplex.comp_f, Category.assoc,
    koszulBraidingHom_f_comp_tensorCochain, Preadditive.comp_zsmul]

end Cochain

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]

/-- Transposing a diagonal swaps the cup product on cohomology, with the Koszul sign and
the braided coefficient pairing. -/
lemma cup_koszulBraidingHom {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ HomologicalComplex.tensorObj A B)
    (μ : N ⊗ M ⟶ P) {p q n : ℕ} (h : p + q = n) (a : (A.linearYonedaObj k M).homology p)
    (b : (B.linearYonedaObj k N).homology q) :
    cup k (D ≫ koszulBraidingHom A B) μ q p n (by omega) b a =
      ((-1 : ℤ) ^ (p * q)) • cup k D ((β_ M N).hom ≫ μ) p q n h a b := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  simp only [cup_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [iCycles_cupCycles, map_zsmul]
  exact cupCochain_koszulBraidingHom A B k D μ h _ _

end TauCeti.NatChainComplex
