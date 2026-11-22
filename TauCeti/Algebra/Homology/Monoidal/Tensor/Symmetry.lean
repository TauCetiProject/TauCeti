/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.Algebra.Homology.Monoidal.Summand

/-!
# The signed interchange of tensor products of homological complexes

Let `c` be a complex shape with tensor signs, so that homological complexes of shape `c` in a
monoidal preadditive category `C` have totalized tensor products `K ⊗ L`, and suppose the signs
come with a `TotalComplexShapeSymmetry c c c`: units `σ p q` relating the Leibniz signs of
`K ⊗ L` and `L ⊗ K`. If `C` is braided, the tensor products `K ⊗ L` and `L ⊗ K` are isomorphic
through the map `HomologicalComplex.tensorBraiding K L`, which on the summand `K_p ⊗ L_q` is the
braiding of `C` multiplied by `σ p q`
(`HomologicalComplex.ιTensorObj_tensorBraiding_hom_f`). For cochain complexes indexed by `ℤ` the
unit `σ p q` is the Koszul sign `(-1)^(p q)`, and so it is for chain complexes indexed by `ℤ`
(`ComplexShape.σ_down_ℤ`); for modules the interchange is `x ⊗ y ↦ (-1)^(|x| |y|) y ⊗ x`.

The interchange is built from Mathlib's identification
`HomologicalComplex.mapBifunctorFlipIso` of the total complex of a bifunctor with that of its
flip, which carries the signs, followed by the map of total complexes induced by the braiding of
`C`, which carries no sign. It requires only the tensor products of the two complexes, not a
monoidal structure on the whole category of complexes. The interchange and its inverse are natural
(`HomologicalComplex.tensorBraiding_hom_naturality`,
`HomologicalComplex.tensorBraiding_inv_naturality`), and when `C` is symmetric and the signs are
symmetric (`TotalComplexShapeSymmetrySymmetry`) interchanging twice is the identity
(`HomologicalComplex.tensorBraiding_hom_comp_tensorBraiding_hom`).

The interchange of chain complexes indexed by `ℤ` is the exchange of the inputs of a product on
Floer complexes, which are graded by an index; its compatibility with the cohomological
regrading `C^k = CF_(n-k)` is `ChainComplex.regradeTensorHom_comp_restrictionMap_tensorBraiding`.

## Main definitions

* `HomologicalComplex.tensorBraiding K L`: the signed interchange `K ⊗ L ≅ L ⊗ K`.

## Main results

* `HomologicalComplex.ιTensorObj_tensorBraiding_hom_f`,
  `HomologicalComplex.ιTensorObj_tensorBraiding_inv_f`: the interchange and its inverse on
  summands.
* `HomologicalComplex.tensorBraiding_hom_naturality`,
  `HomologicalComplex.tensorBraiding_inv_naturality`: naturality of the interchange and of its
  inverse in both complexes.
* `HomologicalComplex.tensorBraiding_inv_eq_reverseBraiding`: with symmetric signs, the inverse
  interchange is the interchange of the swapped complexes for the reversed braiding of `C`.
* `HomologicalComplex.tensorBraiding_inv`: over symmetric coefficients with symmetric signs, the
  inverse interchange is the interchange of the swapped complexes.

## References

* The total complex of the flip of a bicomplex, `HomologicalComplex₂.totalFlipIso` in
  `Mathlib/Algebra/Homology/TotalComplexSymmetry.lean`, and its form for bifunctors in
  `Mathlib/Algebra/Homology/BifunctorFlip.lean`, by Joël Riou.
* C. Weibel, *An Introduction to Homological Algebra*, Section 2.7, for the Koszul sign of the
  interchange of tensor products of complexes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I}
  [c.TensorSigns] [TotalComplexShapeSymmetry c c c]

section Braided

variable [BraidedCategory C]

/-- The braiding of `C` on the summands of `K_p ⊗ L_q`, as an isomorphism from the bicomplex
`(q, p) ↦ K_p ⊗ L_q` whose total complex is that of the flipped tensor bifunctor to the bicomplex
`(q, p) ↦ L_q ⊗ K_p` whose total complex is `L ⊗ K`. It commutes with both differentials by
naturality of the braiding, and carries no sign. -/
private def braidingBicomplexIso (K L : HomologicalComplex C c) :
    (((curriedTensor C).flip.mapBifunctorHomologicalComplex c c).obj L).obj K ≅
      (((curriedTensor C).mapBifunctorHomologicalComplex c c).obj L).obj K where
  hom := HomologicalComplex₂.homMk (fun x ↦ (β_ (K.X x.2) (L.X x.1)).hom)
    (fun _ _ _ _ ↦ by simp [BraidedCategory.braiding_naturality_right])
    (fun _ _ _ _ ↦ by simp [BraidedCategory.braiding_naturality_left])
  inv := HomologicalComplex₂.homMk (fun x ↦ (β_ (K.X x.2) (L.X x.1)).inv)
    (fun _ _ _ _ ↦ by simp [BraidedCategory.braiding_inv_naturality_left])
    (fun _ _ _ _ ↦ by simp [BraidedCategory.braiding_inv_naturality_right])
  hom_inv_id := by ext; simp [HomologicalComplex₂.homMk]
  inv_hom_id := by ext; simp [HomologicalComplex₂.homMk]

variable (K L : HomologicalComplex C c) [K.HasTensor L] [L.HasTensor K]

/-- The **signed interchange** `K ⊗ L ≅ L ⊗ K` of the tensor product of two homological
complexes over a braided coefficient category: on the summand `K_p ⊗ L_q` it is the braiding of
`C` multiplied by the sign `σ p q` of the `TotalComplexShapeSymmetry c c c`, which is the Koszul
sign `(-1)^(p q)` for complexes indexed by `ℤ`. -/
def tensorBraiding : tensorObj K L ≅ tensorObj L K :=
  (mapBifunctorFlipIso K L (curriedTensor C) c).symm ≪≫
    HomologicalComplex₂.total.mapIso (braidingBicomplexIso K L) c

/-- On the summand `K_p ⊗ L_q`, the signed interchange is `σ p q` times the braiding of `C`,
followed by the inclusion of the summand `L_q ⊗ K_p`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorBraiding_hom_f (p q j : I) (h : p + q = j) :
    ιTensorObj K L p q j h ≫ (tensorBraiding K L).hom.f j =
      ComplexShape.σ c c c p q • ((β_ (K.X p) (L.X q)).hom ≫
        ιTensorObj L K q p j (by rw [← h]; exact ComplexShape.π_symm c c c p q)) := by
  rw [tensorBraiding, Iso.trans_hom, Iso.symm_hom, comp_f, ι_mapBifunctorFlipIso_inv_assoc,
    Linear.units_smul_comp]
  -- The inclusions of summands into `mapBifunctor` are those into the total complex of the
  -- underlying bicomplex, and the summand component of the braiding bicomplex map is `β_`.
  exact congrArg _ (HomologicalComplex₂.ιTotal_map _ _ (braidingBicomplexIso K L).hom c q p j _)

/-- On the summand `L_q ⊗ K_p`, the inverse of the signed interchange is `σ p q` times the inverse
braiding of `C`, followed by the inclusion of the summand `K_p ⊗ L_q`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorBraiding_inv_f (p q j : I) (h : q + p = j) :
    ιTensorObj L K q p j h ≫ (tensorBraiding K L).inv.f j =
      ComplexShape.σ c c c p q • ((β_ (K.X p) (L.X q)).inv ≫
        ιTensorObj K L p q j (by rw [← h]; exact (ComplexShape.π_symm c c c p q).symm)) := by
  -- As for `ιTensorObj_tensorBraiding_hom_f`, the summand inclusions are those of total
  -- complexes, and the summand component of the inverse braiding bicomplex map is `β_⁻¹`.
  rw [tensorBraiding, Iso.trans_inv, Iso.symm_inv, comp_f, HomologicalComplex₂.total.mapIso_inv,
    ← Category.assoc, HomologicalComplex₂.ιTotal_map _ _ (braidingBicomplexIso K L).inv c q p j h,
    Category.assoc, ι_mapBifunctorFlipIso_hom, Linear.comp_units_smul]
  rfl

variable {K L} in
/-- The signed interchange is natural in both complexes. -/
@[reassoc]
lemma tensorBraiding_hom_naturality {K' L' : HomologicalComplex C c} [K'.HasTensor L']
    [L'.HasTensor K'] (f : K ⟶ K') (g : L ⟶ L') :
    tensorHom f g ≫ (tensorBraiding K' L').hom = (tensorBraiding K L).hom ≫ tensorHom g f := by
  ext j : 1
  refine mapBifunctor.hom_ext fun p q (h : p + q = j) ↦ ?_
  simp only [comp_f, ι_tensorHom_assoc, ιTensorObj_tensorBraiding_hom_f,
    ιTensorObj_tensorBraiding_hom_f_assoc, Linear.comp_units_smul, Linear.units_smul_comp,
    Category.assoc, ι_tensorHom, BraidedCategory.braiding_naturality_assoc]

variable {K L} in
/-- The inverse of the signed interchange is natural in both complexes. -/
@[reassoc]
lemma tensorBraiding_inv_naturality {K' L' : HomologicalComplex C c} [K'.HasTensor L']
    [L'.HasTensor K'] (f : K ⟶ K') (g : L ⟶ L') :
    tensorHom g f ≫ (tensorBraiding K' L').inv = (tensorBraiding K L).inv ≫ tensorHom f g := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorBraiding_hom_naturality, Iso.inv_hom_id_assoc]

/-- With symmetric signs, the inverse of the signed interchange of `K ⊗ L` is the signed
interchange of `L ⊗ K` for the reversed braiding of `C`: on each summand both are the inverse
braiding of `C` with the sign `σ p q = σ q p`. -/
lemma tensorBraiding_inv_eq_reverseBraiding [TotalComplexShapeSymmetrySymmetry c c c] :
    (tensorBraiding K L).inv = (letI := reverseBraiding C; tensorBraiding L K).hom := by
  ext j : 1
  refine mapBifunctor.hom_ext fun q p (h : q + p = j) ↦ ?_
  rw [ιTensorObj_tensorBraiding_inv_f,
    (letI := reverseBraiding C; ιTensorObj_tensorBraiding_hom_f L K q p j h), ComplexShape.σ_symm]
  -- Under `reverseBraiding C`, the braiding `β_ (L.X q) (K.X p)` is `(β_ (K.X p) (L.X q)).symm`.
  rfl

end Braided

section Symmetric

variable [SymmetricCategory C] [TotalComplexShapeSymmetrySymmetry c c c]
  (K L : HomologicalComplex C c) [K.HasTensor L] [L.HasTensor K]

/-- Over symmetric coefficients with symmetric signs, the inverse of the signed interchange of
`K ⊗ L` is the signed interchange of `L ⊗ K`. -/
@[simp]
lemma tensorBraiding_inv : (tensorBraiding K L).inv = (tensorBraiding L K).hom := by
  rw [tensorBraiding_inv_eq_reverseBraiding, SymmetricCategory.reverseBraiding_eq]

/-- Over symmetric coefficients with symmetric signs, interchanging the factors of a tensor
product of complexes twice is the identity. -/
@[reassoc (attr := simp)]
lemma tensorBraiding_hom_comp_tensorBraiding_hom :
    (tensorBraiding K L).hom ≫ (tensorBraiding L K).hom = 𝟙 _ := by
  rw [← tensorBraiding_inv K L, Iso.hom_inv_id]

end Symmetric

end HomologicalComplex
