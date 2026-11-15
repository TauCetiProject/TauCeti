/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cup

/-!
# Koszul braiding for nonnegative chain complexes

On the summand of bidegree `(p, q)`, interchange of tensor factors carries the sign
`(-1)^(p*q)` to commute with the differential. `TauCeti.NatChainComplex.koszulBraidingHom`
constructs this chain map in any braided preadditive monoidal category, assuming only that the
two tensor complexes exist. It is an isomorphism in a braided category; in a symmetric category,
its inverse is the same construction with the factors swapped.

The tensor-cochain formula is the chain-level interchange needed to compare the Alexander–Whitney
diagonal with its transpose, and hence to prove graded commutativity of cup products. The cup
formulas give signed interchange along a transposed diagonal, with the braided coefficient
pairing. No commutativity is asserted for the Alexander–Whitney diagonal itself.

## Main definitions and results

* `TauCeti.NatChainComplex.koszulBraidingHom`: the signed interchange chain map.
* `TauCeti.NatChainComplex.ιTensorObj_koszulBraidingHom_f`: its value on each bidegree summand.
* `TauCeti.NatChainComplex.koszulBraidingHom_naturality`: naturality in both chain complexes.
* `TauCeti.NatChainComplex.koszulBraiding`: the signed interchange isomorphism.
* `TauCeti.NatChainComplex.inv_koszulBraidingHom`: the inverse of the signed interchange map.
* `TauCeti.NatChainComplex.ιTensorObj_koszulBraiding_inv_f`: its inverse on each summand.
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

The construction follows the signed tensor differential in Mathlib's
`HomologicalComplex.tensorObj`, and the summand method of `TauCeti.koszulBraidingHom` for
integer-indexed cochain complexes. The differential out of degree zero vanishes, so one Leibniz
term drops in bidegrees with a zero index. The construction requires no monoidal structure on
the entire category of complexes. The inverse uses the inverse coefficient braiding, lifted by
`HomologicalComplex.Hom.isoOfComponents`.

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

private def koszulBraidingX (n : ℕ) : (tensorObj A B).X n ⟶ (tensorObj B A).X n :=
  mapBifunctorDesc fun p q (h : p + q = n) ↦
    ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
      ιTensorObj B A q p n (by omega))

@[reassoc]
private lemma ιTensorObj_koszulBraidingX (p q n : ℕ) (h : p + q = n) :
    ιTensorObj A B p q n h ≫ koszulBraidingX A B n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
        ιTensorObj B A q p n (by omega)) := by
  rw [koszulBraidingX, ι_mapBifunctorDesc]

private lemma koszulBraidingX_comm (n : ℕ) :
    koszulBraidingX A B (n + 1) ≫ (tensorObj B A).d (n + 1) n =
      (tensorObj A B).d (n + 1) n ≫ koszulBraidingX A B n := by
  refine mapBifunctor.hom_ext fun p q (h : p + q = n + 1) ↦ ?_
  rw [ιTensorObj_koszulBraidingX_assoc]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    Preadditive.zsmul_comp, Category.assoc]
  -- In degree zero one Leibniz term vanishes; in positive bidegrees the two terms swap.
  obtain _ | p := p
  · obtain _ | q := q
    · omega
    obtain rfl : q = n := by omega
    simp only [_root_.ChainComplex.ιTensorObj_D₁_zero_assoc,
      _root_.ChainComplex.ιTensorObj_D₂_zero, _root_.ChainComplex.ιTensorObj_D₁_succ,
      _root_.ChainComplex.ιTensorObj_D₂_succ_assoc, Category.assoc, ιTensorObj_koszulBraidingX,
      Nat.zero_mul, pow_zero, one_smul, comp_zero, zero_comp, add_zero, zero_add]
    rw [BraidedCategory.braiding_naturality_right_assoc]
  · obtain _ | q := q
    · obtain rfl : p = n := by omega
      simp only [_root_.ChainComplex.ιTensorObj_D₂_zero_assoc,
        _root_.ChainComplex.ιTensorObj_D₁_zero, _root_.ChainComplex.ιTensorObj_D₂_succ,
        _root_.ChainComplex.ιTensorObj_D₁_succ_assoc, ιTensorObj_koszulBraidingX,
        Nat.mul_zero, pow_zero, one_smul, comp_zero, zero_comp, add_zero, zero_add]
      rw [BraidedCategory.braiding_naturality_left_assoc]
    · simp only [_root_.ChainComplex.ιTensorObj_D₁_succ, _root_.ChainComplex.ιTensorObj_D₂_succ,
        _root_.ChainComplex.ιTensorObj_D₁_succ_assoc, _root_.ChainComplex.ιTensorObj_D₂_succ_assoc,
        ιTensorObj_koszulBraidingX, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
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
def koszulBraidingHom : tensorObj A B ⟶ tensorObj B A where
  f := koszulBraidingX A B
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact koszulBraidingX_comm A B j

/-- On the bidegree-`(p, q)` summand, interchange is the coefficient braiding multiplied by
`(-1)^(p*q)`, followed by the inclusion of the swapped summand. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_koszulBraidingHom_f (p q n : ℕ) (h : p + q = n) :
    ιTensorObj A B p q n h ≫ (koszulBraidingHom A B).f n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).hom ≫
        ιTensorObj B A q p n (by omega)) :=
  ιTensorObj_koszulBraidingX A B p q n h

/-- Koszul interchange is natural in both chain complexes. -/
@[reassoc]
lemma koszulBraidingHom_naturality {A' B' : ChainComplex C ℕ} [A'.HasTensor B'] [B'.HasTensor A']
    (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom f g ≫ koszulBraidingHom A' B' = koszulBraidingHom A B ≫ tensorHom g f := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
  simp only [HomologicalComplex.comp_f, ι_tensorHom_assoc, ιTensorObj_koszulBraidingHom_f,
    ιTensorObj_koszulBraidingHom_f_assoc, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.assoc, ι_tensorHom]
  rw [BraidedCategory.braiding_naturality_assoc]

private def koszulBraidingXIso (n : ℕ) : (tensorObj A B).X n ≅ (tensorObj B A).X n where
  hom := koszulBraidingX A B n
  inv := mapBifunctorDesc fun q p (h : q + p = n) ↦
    ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).inv ≫
      ιTensorObj A B p q n (by omega))
  hom_inv_id := by
    refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
    rw [ιTensorObj_koszulBraidingX_assoc]
    simp only [Preadditive.zsmul_comp, Category.assoc, ι_mapBifunctorDesc,
      Preadditive.comp_zsmul, smul_smul, Iso.hom_inv_id_assoc, Category.comp_id]
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  inv_hom_id := by
    refine mapBifunctor.hom_ext fun q p (h : q + p = n) ↦ ?_
    rw [ι_mapBifunctorDesc_assoc]
    simp only [Preadditive.zsmul_comp, Category.assoc, ιTensorObj_koszulBraidingX,
      Preadditive.comp_zsmul, smul_smul, Iso.inv_hom_id_assoc, Category.comp_id]
    rw [← pow_add, ← two_mul, pow_mul]
    simp

/-- The signed interchange isomorphism of tensor complexes in a braided coefficient category. -/
def koszulBraiding : tensorObj A B ≅ tensorObj B A :=
  HomologicalComplex.Hom.isoOfComponents (koszulBraidingXIso A B)
    (fun i j _ ↦ (koszulBraidingHom A B).comm i j)

/-- The forward map of signed interchange is `koszulBraidingHom`. -/
@[simp]
lemma koszulBraiding_hom : (koszulBraiding A B).hom = koszulBraidingHom A B := (rfl)

instance : IsIso (koszulBraidingHom A B) := (koszulBraiding A B).isIso_hom

/-- The categorical inverse of signed interchange is the inverse of `koszulBraiding`. -/
@[simp]
lemma inv_koszulBraidingHom : inv (koszulBraidingHom A B) = (koszulBraiding A B).inv :=
  IsIso.inv_eq_of_hom_inv_id (koszulBraiding A B).hom_inv_id

/-- Signed interchange followed by its inverse is the identity chain map. -/
@[reassoc (attr := simp)]
lemma koszulBraidingHom_comp_koszulBraiding_inv :
    koszulBraidingHom A B ≫ (koszulBraiding A B).inv = 𝟙 _ :=
  (koszulBraiding A B).hom_inv_id

/-- The inverse of signed interchange followed by the forward map is the identity chain map. -/
@[reassoc (attr := simp)]
lemma koszulBraiding_inv_comp_koszulBraidingHom :
    (koszulBraiding A B).inv ≫ koszulBraidingHom A B = 𝟙 _ :=
  (koszulBraiding A B).inv_hom_id

/-- On the bidegree-`(q, p)` summand, inverse interchange is the inverse coefficient braiding
multiplied by `(-1)^(p*q)`, followed by the inclusion of the swapped summand. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_koszulBraiding_inv_f (p q n : ℕ) (h : q + p = n) :
    ιTensorObj B A q p n h ≫ (koszulBraiding A B).inv.f n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.X p) (B.X q)).inv ≫
        ιTensorObj A B p q n (by omega)) := by
  rw [koszulBraiding, HomologicalComplex.Hom.isoOfComponents_inv_f _
    (fun i j _ ↦ (koszulBraidingHom A B).comm i j), koszulBraidingXIso, ι_mapBifunctorDesc]

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- In a symmetric category, interchanging tensor factors twice is the identity chain map. -/
@[reassoc (attr := simp)]
lemma koszulBraidingHom_comp : koszulBraidingHom A B ≫ koszulBraidingHom B A = 𝟙 _ := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
  simp only [HomologicalComplex.comp_f, ιTensorObj_koszulBraidingHom_f_assoc,
    ιTensorObj_koszulBraidingHom_f, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.assoc, smul_smul, SymmetricCategory.symmetry_assoc,
    HomologicalComplex.id_f, Category.comp_id]
  rw [Nat.mul_comm q p, ← pow_add, ← two_mul, pow_mul]
  simp

/-- The inverse of signed interchange swaps the factors in the opposite order. -/
@[simp]
lemma koszulBraiding_inv : (koszulBraiding A B).inv = koszulBraidingHom B A := by
  apply (cancel_epi (koszulBraiding A B).hom).1
  rw [Iso.hom_inv_id, koszulBraiding_hom, koszulBraidingHom_comp]

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
