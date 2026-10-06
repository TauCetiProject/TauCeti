/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cup

/-!
# Koszul interchange for nonnegative chain complexes

The interchange of tensor factors in chain complexes is not the unsigned braiding of graded
objects: on the summand of bidegree `(p, q)` it must carry the sign `(-1)^(p*q)` to commute with
the differential. `TauCeti.tensorFlip` constructs this chain map in any braided
preadditive monoidal category, assuming only that the two tensor complexes exist. In a symmetric
category, interchanging twice is the identity, giving `tensorFlipIso`.

The formula `tensorFlip_f_comp_tensorCochain` identifies precomposition of a tensor cochain with
this map with the swapped tensor cochain and its Koszul sign. It is the chain-level interchange
needed to compare the Alexander–Whitney diagonal with its transpose, and hence to prove graded
commutativity of cup products. `cup_tensorFlip` gives the signed interchange formula on
cohomology along a transposed diagonal. No commutativity is asserted for the Alexander–Whitney
diagonal itself.

The construction follows the signed tensor differential in Mathlib's
`HomologicalComplex.tensorObj`, and the summand method of `TauCeti.koszulBraidingHom` for
integer-indexed cochain complexes. The nonnegative chain grading has zero boundary terms, and
the construction here does not require a monoidal structure on the entire category of complexes.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, for the graded-commutativity sign.
* C. Weibel, *An Introduction to Homological Algebra*, Section 2.7, for tensor complexes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open TauCeti.ChainComplex

namespace TauCeti

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]

section Braided

variable [BraidedCategory C]

private def tensorFlipX (n : ℕ) : (tensorObj A B).X n ⟶ (tensorObj B A).X n :=
  mapBifunctorDesc fun p q (h : p + q = n) ↦
    ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
      ιTensorObj B A q p n (by omega))

@[reassoc]
private lemma ιTensorObj_tensorFlipX (p q n : ℕ) (h : p + q = n) :
    ιTensorObj A B p q n h ≫ tensorFlipX A B n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
        ιTensorObj B A q p n (by omega)) := by
  rw [tensorFlipX, ι_mapBifunctorDesc]

private lemma tensorFlipX_comm (n : ℕ) :
    tensorFlipX A B (n + 1) ≫ (tensorObj B A).d (n + 1) n =
      (tensorObj A B).d (n + 1) n ≫ tensorFlipX A B n := by
  refine mapBifunctor.hom_ext fun p q (h : p + q = n + 1) ↦ ?_
  rw [ιTensorObj_tensorFlipX_assoc]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    Preadditive.zsmul_comp, Category.assoc]
  -- In degree zero one Leibniz term vanishes; in positive bidegrees the two terms swap.
  obtain _ | p := p
  · obtain _ | q := q
    · omega
    obtain rfl : q = n := by omega
    simp only [ChainComplex.ιTensorObj_D₁_zero_assoc,
      ChainComplex.ιTensorObj_D₂_zero, ChainComplex.ιTensorObj_D₁_succ,
      ChainComplex.ιTensorObj_D₂_succ_assoc, Category.assoc, ιTensorObj_tensorFlipX,
      Nat.zero_mul, pow_zero, one_smul, comp_zero, zero_comp, add_zero, zero_add]
    rw [BraidedCategory.braiding_naturality_right_assoc]
  · obtain _ | q := q
    · obtain rfl : p = n := by omega
      simp only [ChainComplex.ιTensorObj_D₂_zero_assoc,
        ChainComplex.ιTensorObj_D₁_zero, ChainComplex.ιTensorObj_D₂_succ,
        ChainComplex.ιTensorObj_D₁_succ_assoc, ιTensorObj_tensorFlipX,
        Nat.mul_zero, pow_zero, one_smul, comp_zero, zero_comp, add_zero, zero_add]
      rw [BraidedCategory.braiding_naturality_left_assoc]
    · simp only [ChainComplex.ιTensorObj_D₁_succ, ChainComplex.ιTensorObj_D₂_succ,
        ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
        ιTensorObj_tensorFlipX, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
        Category.assoc, smul_smul]
      rw [BraidedCategory.braiding_naturality_left_assoc,
        BraidedCategory.braiding_naturality_right_assoc]
      have hs₁ : (-1 : ℤ) ^ ((p + 1) * (q + 1)) * (-1) ^ (q + 1) =
          (-1) ^ (p * (q + 1)) := by
        have he : (p + 1) * (q + 1) + (q + 1) =
            p * (q + 1) + 2 * (q + 1) := by ring
        rw [← pow_add, he, pow_add, pow_mul]
        simp
      have hs₂ : (-1 : ℤ) ^ ((p + 1) * (q + 1)) =
          (-1) ^ (p + 1) * (-1) ^ ((p + 1) * q) := by
        rw [← pow_add]
        congr 1
        ring
      rw [hs₁, hs₂]
      exact add_comm _ _

/-- Interchange the factors of a tensor product of nonnegative chain complexes, with the
Koszul sign `(-1)^(p*q)` on its bidegree-`(p, q)` summand. -/
def tensorFlip : tensorObj A B ⟶ tensorObj B A where
  f := tensorFlipX A B
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact tensorFlipX_comm A B j

/-- On the bidegree-`(p, q)` summand, interchange is the coefficient braiding multiplied by
`(-1)^(p*q)`, followed by the inclusion of the swapped summand. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorFlip_f (p q n : ℕ) (h : p + q = n) :
    ιTensorObj A B p q n h ≫ (tensorFlip A B).f n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
        ιTensorObj B A q p n (by omega)) :=
  ιTensorObj_tensorFlipX A B p q n h

/-- Koszul interchange is natural in both chain complexes. -/
@[reassoc]
lemma tensorHom_tensorFlip {A' B' : ChainComplex C ℕ} [A'.HasTensor B'] [B'.HasTensor A']
    (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom f g ≫ tensorFlip A' B' = tensorFlip A B ≫ tensorHom g f := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
  simp only [HomologicalComplex.comp_f, ι_tensorHom_assoc, ιTensorObj_tensorFlip_f,
    ιTensorObj_tensorFlip_f_assoc, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.assoc, ι_tensorHom]
  rw [BraidedCategory.braiding_naturality_assoc]

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- In a symmetric category, interchanging tensor factors twice is the identity chain map. -/
@[simp]
lemma tensorFlip_tensorFlip : tensorFlip A B ≫ tensorFlip B A = 𝟙 _ := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
  simp only [HomologicalComplex.comp_f, ιTensorObj_tensorFlip_f_assoc,
    ιTensorObj_tensorFlip_f, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.assoc, smul_smul, SymmetricCategory.symmetry_assoc,
    HomologicalComplex.id_f, Category.comp_id]
  rw [Nat.mul_comm q p, ← pow_add, ← two_mul, pow_mul]
  simp

/-- The signed interchange isomorphism of tensor complexes in a symmetric coefficient category. -/
def tensorFlipIso : tensorObj A B ≅ tensorObj B A where
  hom := tensorFlip A B
  inv := tensorFlip B A
  hom_inv_id := tensorFlip_tensorFlip A B
  inv_hom_id := tensorFlip_tensorFlip B A

/-- The forward map of signed interchange is `tensorFlip`. -/
@[simp]
lemma tensorFlipIso_hom : (tensorFlipIso A B).hom = tensorFlip A B := (rfl)

/-- The inverse of signed interchange swaps the factors in the opposite order. -/
@[simp]
lemma tensorFlipIso_inv : (tensorFlipIso A B).inv = tensorFlip B A := (rfl)

end Symmetric

section Cochain

variable [BraidedCategory C]

/-- Precomposing a tensor product of cochains with Koszul interchange swaps the cochains and
braids their coefficient pairing, with sign `(-1)^(p*q)`. This holds in every output degree,
including degrees where both cochains vanish. -/
@[reassoc]
lemma tensorFlip_f_comp_tensorCochain {M N P : C} (μ : N ⊗ M ⟶ P) {p q : ℕ}
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (tensorFlip A B).f n ≫ tensorCochain μ ψ φ n =
      ((-1 : ℤ) ^ (p * q)) • tensorCochain ((β_ M N).hom ≫ μ) φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ιTensorObj_tensorFlip_f_assoc, Preadditive.comp_zsmul]
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
lemma cupCochain_tensorFlip {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommSemiring k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ tensorObj A B) (μ : N ⊗ M ⟶ P)
    {p q n : ℕ} (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k (D ≫ tensorFlip A B) μ q p n (by omega) ψ φ =
      ((-1 : ℤ) ^ (p * q)) • cupCochain k D ((β_ M N).hom ≫ μ) p q n h φ ψ := by
  simp only [cupCochain_apply, HomologicalComplex.comp_f, Category.assoc,
    tensorFlip_f_comp_tensorCochain, Preadditive.comp_zsmul]

end Cochain

end TauCeti

namespace TauCeti

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]

/-- Transposing a diagonal swaps the cup product on cohomology, with the Koszul sign and
the braided coefficient pairing. -/
lemma cup_tensorFlip {E : ChainComplex C ℕ} {M N P : C} (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (D : E ⟶ HomologicalComplex.tensorObj A B)
    (μ : N ⊗ M ⟶ P) {p q n : ℕ} (h : p + q = n) (a : (A.linearYonedaObj k M).homology p)
    (b : (B.linearYonedaObj k N).homology q) :
    cup k (D ≫ tensorFlip A B) μ q p n (by omega) b a =
      ((-1 : ℤ) ^ (p * q)) • cup k D ((β_ M N).hom ≫ μ) p q n h a b := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  simp only [cup_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [iCycles_cupCycles, map_zsmul]
  exact cupCochain_tensorFlip A B k D μ h _ _

end TauCeti
