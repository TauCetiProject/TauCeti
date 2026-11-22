/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.BifunctorFlip
public import TauCeti.Algebra.Homology.ComplexShape.Signs
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The Koszul braiding of homological complexes

Mathlib's `HomologicalComplex.monoidalCategory`, instantiated at `ComplexShape.up ℤ` and its
`ComplexShape.TensorSigns`, makes `CochainComplex C ℤ` monoidal by totalizing the
degreewise tensor product.  It does not make it braided: Mathlib's `GradedObject.braidedCategory`
uses the braiding of the base category on each summand with no sign, and that map does not commute
with the totalized differential.

The Koszul braiding `HomologicalComplex.koszulBraiding X Y : tensorObj X Y ≅ tensorObj Y X` is
defined for complexes of any shape `c` with tensor signs and a symmetry
`TotalComplexShapeSymmetry c c c` of its total complex shape, in any braided monoidal preadditive
category, assuming only that the tensor products of `X` and `Y` in both orders exist.  This file
combines the coefficient braiding on each summand with Mathlib's signed flip
`HomologicalComplex.mapBifunctorFlipIso` of the total complex, which provides the sign
`ComplexShape.σ` and the compatibility with the differentials.  When the signs of the shape are
symmetric in the two factors (`TotalComplexShapeSymmetrySymmetry c c c`), the inverse of the Koszul
braiding is the Koszul braiding of the swapped complexes over the reversed coefficient braiding,
and over symmetric coefficients it is the Koszul braiding of the swapped complexes.  The file then
supplies the complex-level braiding axioms for cochain complexes indexed by `ℤ`.  The same
braiding of chain complexes indexed by `ℕ` is evaluated in
`TauCeti/Algebra/Homology/Monoidal/KoszulBraiding.lean`.

For cochain complexes, `C` is any braided monoidal preadditive category with a zero object and the
coproduct and tensor-preservation hypotheses of Mathlib's totalized monoidal structure.
When the coefficient braiding is symmetric, so is the Koszul braiding.

At `ComplexShape.up ℤ`, the sign `ComplexShape.σ` of the flip is `(-1)^{p * q}`, so on the
bidegree-`(p, q)` summand of `X ⊗ Y` the braiding is `(-1)^{p * q}` times the braiding of `C`.
For modules, this is `x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x` on homogeneous elements.  With this sign
the braiding commutes with the differentials: the totalized differential carries
`ComplexShape.up ℤ`'s tensor signs `ε₁ = 1` and `ε₂ (p, q) = (-1)^p`, and after transposing,
the Koszul sign makes the two Leibniz terms match.

## Main definitions

* `HomologicalComplex.koszulBraiding`: the Koszul braiding `tensorObj X Y ≅ tensorObj Y X` of
  homological complexes of a shape `c` with tensor signs `[c.TensorSigns]` and a chosen symmetry
  `[TotalComplexShapeSymmetry c c c]` of its total complex shape, whenever the tensor products of
  the two complexes in both orders exist.
* `TauCeti.koszulBraidingSummand`: the bidegree component of the braiding of cochain complexes.
* `TauCeti.koszulBraidedCategory` and `TauCeti.koszulSymmetricCategory`: the `BraidedCategory`
  and `SymmetricCategory` instances on `CochainComplex C ℤ`, whose braiding is
  `HomologicalComplex.koszulBraiding`.

## Main results

* `HomologicalComplex.ιTensorObj_koszulBraiding_hom_f` and
  `HomologicalComplex.ιTensorObj_koszulBraiding_inv_f`: the Koszul braiding and its inverse on a
  homogeneous summand, with the sign `ComplexShape.σ` of the shape.
* `HomologicalComplex.koszulBraiding_hom_naturality`: the Koszul braiding is natural in both
  complexes.
* `HomologicalComplex.koszulBraiding_inv_eq_reverseBraiding`: for symmetric signs, the inverse
  Koszul braiding is the Koszul braiding of the swapped complexes over `reverseBraiding C`.
* `HomologicalComplex.koszulBraiding_inv` and `HomologicalComplex.koszulBraiding_hom_comp_hom`:
  for symmetric signs and symmetric coefficients, the inverse is the Koszul braiding of the
  swapped complexes, and interchanging twice is the identity.
* `TauCeti.ι_koszulBraiding_hom` and `TauCeti.ι_koszulBraiding_inv`: on the summand
  `X.X p ⊗ Y.X q`, the braiding of cochain complexes is the coefficient braiding followed by the
  inclusion of the swapped summand, with the sign `(-1)^(p * q)`, and dually for its inverse.
* `TauCeti.koszulBraiding_hom_naturality_left` and `TauCeti.koszulBraiding_hom_naturality_right`:
  the braiding of cochain complexes is natural in each factor.
* `TauCeti.koszulBraiding_hom_hexagon_forward` and `TauCeti.koszulBraiding_hom_hexagon_reverse`:
  the two hexagon identities.
* `TauCeti.ι_tensorμ`: on a homogeneous summand, the middle-four interchange
  `MonoidalCategory.tensorμ` of cochain complexes is that of `C`, with the Koszul sign of
  the two factors it exchanges.

The two auxiliary equations `HomologicalComplex.whiskerLeft_eq_mapBifunctorMap` and
`HomologicalComplex.whiskerRight_eq_mapBifunctorMap` of
`TauCeti/Algebra/Homology/Monoidal/Summand.lean`, which record that the whiskerings of
`CochainComplex C ℤ` are `HomologicalComplex.mapBifunctorMap`, are used throughout.

For module-valued complexes, this braiding supplies the signs in Hom-complex composition
and in the tensor product and opposite of differential graded categories.

## Implementation notes

The hypotheses of the braiding of cochain complexes are the graded-object tensor existence and
preservation classes used by Mathlib's `HomologicalComplex.monoidalCategory`. In particular,
modules over a commutative ring satisfy them through their closed symmetric monoidal structure.

`HomologicalComplex.koszulBraiding` totalizes the coefficient braiding, viewed as an isomorphism
onto the bicomplex of the flipped tensor bifunctor, and composes with Mathlib's
`HomologicalComplex.mapBifunctorFlipIso`, so its inverse comes with it.  At `ComplexShape.up ℤ`
the sign `ComplexShape.σ` of that isomorphism is `(p * q).negOnePow`.  The braiding of
`CochainComplex C ℤ` is this isomorphism itself, whose type `tensorObj X Y ≅ tensorObj Y X` is the
monoidal `X ⊗ Y ≅ Y ⊗ X` by definition.

The summand rules `HomologicalComplex.ιTensorObj_koszulBraiding_hom_f` and
`HomologicalComplex.ιTensorObj_koszulBraiding_inv_f` are `simp` lemmas with the sign
`ComplexShape.σ` of the shape left unevaluated.  Their specializations with the sign evaluated,
`TauCeti.ι_koszulBraiding_hom` and `TauCeti.ι_koszulBraiding_inv` here and the rules for chain
complexes indexed by `ℕ` in `TauCeti/Algebra/Homology/Monoidal/KoszulBraiding.lean`, have higher
`simp` priority, so that they apply first on the same summands.

## References

* The totalized monoidal structure `HomologicalComplex.monoidalCategory` in
  `Mathlib/Algebra/Homology/Monoidal.lean`, by Joël Riou and Kim Morrison, and the unsigned
  `GradedObject.Monoidal.braiding` of `Mathlib/CategoryTheory/GradedObject/Braiding.lean`, by
  Joël Riou, and the signed flip `HomologicalComplex.mapBifunctorFlipIso` of
  `Mathlib/Algebra/Homology/BifunctorFlip.lean`, by Joël Riou, which provides the Koszul sign.
  This file combines it with the coefficient braiding and supplies the complex-level braiding
  axioms; nothing is vendored.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

section KoszulBraiding

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]
  [TotalComplexShapeSymmetry c c c]

section Braided

variable [BraidedCategory C]

/- The coefficient braiding on each bidegree, as an isomorphism from the bicomplex whose
totalization is `HomologicalComplex.tensorObj X Y` to the bicomplex of the flipped tensor
bifunctor, whose totalization `HomologicalComplex.mapBifunctorFlipIso` identifies with
`HomologicalComplex.tensorObj Y X`.  Its rows are the braiding `curriedBraidingNatIso` at
`X.X p`, applied to `Y` degreewise. -/
private noncomputable def braidingBicomplexIso (X Y : HomologicalComplex C c) :
    (((curriedTensor C).mapBifunctorHomologicalComplex c c).obj X).obj Y ≅
      (((curriedTensor C).flip.mapBifunctorHomologicalComplex c c).obj X).obj Y :=
  Hom.isoOfComponents
    (fun p ↦ (NatIso.mapHomologicalComplex
      ((BraidedCategory.curriedBraidingNatIso C).app (X.X p)) c).app Y)
    (fun _ _ _ ↦ by ext; simp [BraidedCategory.braiding_naturality_left])

variable [DecidableEq I]

/-- **The Koszul braiding** `tensorObj X Y ≅ tensorObj Y X` of two homological complexes whose
tensor products in both orders exist: the coefficient braiding on each summand `X.X p ⊗ Y.X q`,
totalized and followed by Mathlib's `HomologicalComplex.mapBifunctorFlipIso`, which carries the
sign `ComplexShape.σ c c c q p` of the shape and the compatibility with the differentials. -/
noncomputable def koszulBraiding (X Y : HomologicalComplex C c) [X.HasTensor Y] [Y.HasTensor X] :
    tensorObj X Y ≅ tensorObj Y X :=
  HomologicalComplex₂.total.mapIso (braidingBicomplexIso X Y) c ≪≫
    mapBifunctorFlipIso Y X (curriedTensor C) c

variable (X Y : HomologicalComplex C c) [X.HasTensor Y] [Y.HasTensor X]

/-- On the summand `X.X p ⊗ Y.X q`, the Koszul braiding is the coefficient braiding followed by
the inclusion of the swapped summand, with the sign `ComplexShape.σ c c c q p`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_koszulBraiding_hom_f (p q j : I) (h : p + q = j) :
    ιTensorObj X Y p q j h ≫ (koszulBraiding X Y).hom.f j =
      ComplexShape.σ c c c q p • ((β_ (X.X p) (Y.X q)).hom ≫
        ιTensorObj Y X q p j ((ComplexShape.π_symm c c c p q).trans h)) := by
  simp [koszulBraiding, braidingBicomplexIso]

/-- On the summand `Y.X q ⊗ X.X p`, the inverse Koszul braiding is the inverse coefficient
braiding followed by the inclusion of the swapped summand, with the same sign
`ComplexShape.σ c c c q p` as `HomologicalComplex.ιTensorObj_koszulBraiding_hom_f`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_koszulBraiding_inv_f (q p j : I) (h : q + p = j) :
    ιTensorObj Y X q p j h ≫ (koszulBraiding X Y).inv.f j =
      ComplexShape.σ c c c q p • ((β_ (X.X p) (Y.X q)).inv ≫
        ιTensorObj X Y p q j ((ComplexShape.π_symm c c c p q).symm.trans h)) := by
  simp [koszulBraiding, braidingBicomplexIso]

/-- The Koszul braiding is natural in both complexes. -/
@[reassoc (attr := simp)]
lemma koszulBraiding_hom_naturality {X' Y' : HomologicalComplex C c}
    [X'.HasTensor Y'] [Y'.HasTensor X'] (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorHom f g ≫ (koszulBraiding X' Y').hom = (koszulBraiding X Y).hom ≫ tensorHom g f := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q (h : p + q = n) ↦ ?_
  simp only [comp_f, ι_tensorHom_assoc, ιTensorObj_koszulBraiding_hom_f,
    ιTensorObj_koszulBraiding_hom_f_assoc, Linear.comp_units_smul, Linear.units_smul_comp,
    Category.assoc, ι_tensorHom]
  rw [BraidedCategory.braiding_naturality_assoc]

/-- When the signs of the shape are symmetric in the two factors, the inverse Koszul braiding is
the Koszul braiding of the swapped complexes over the reversed coefficient braiding
`reverseBraiding C`: on each summand both are the inverse coefficient braiding with the same
sign. -/
lemma koszulBraiding_inv_eq_reverseBraiding [TotalComplexShapeSymmetrySymmetry c c c] :
    (koszulBraiding X Y).inv = (letI := reverseBraiding C; koszulBraiding Y X).hom := by
  ext j : 1
  refine mapBifunctor.hom_ext fun q p (h : q + p = j) ↦ ?_
  -- The summand rule of the Koszul braiding over `reverseBraiding C`, which instance search does
  -- not find on its own.
  have hrev := (letI := reverseBraiding C; ιTensorObj_koszulBraiding_hom_f Y X q p j h)
  rw [ιTensorObj_koszulBraiding_inv_f, hrev, ComplexShape.σ_symm]
  -- Under `reverseBraiding C`, the braiding `β_ (Y.X q) (X.X p)` is `(β_ (X.X p) (Y.X q)).symm`.
  -- It sits in an instance argument, which `dsimp` unfolds only with `+instances`.
  dsimp +instances only [reverseBraiding, Iso.symm_hom]

end Braided

section Symmetric

variable [SymmetricCategory C] [TotalComplexShapeSymmetrySymmetry c c c] [DecidableEq I]
  (X Y : HomologicalComplex C c) [X.HasTensor Y] [Y.HasTensor X]

/-- Over symmetric coefficients, and when the signs of the shape are symmetric in the two
factors, the inverse Koszul braiding is the Koszul braiding of the swapped complexes. -/
@[simp]
lemma koszulBraiding_inv : (koszulBraiding X Y).inv = (koszulBraiding Y X).hom := by
  rw [koszulBraiding_inv_eq_reverseBraiding X Y, SymmetricCategory.reverseBraiding_eq C]

/-- Over symmetric coefficients, and when the signs of the shape are symmetric in the two
factors, interchanging the factors twice is the identity. -/
@[reassoc (attr := simp)]
lemma koszulBraiding_hom_comp_hom :
    (koszulBraiding X Y).hom ≫ (koszulBraiding Y X).hom = 𝟙 _ := by
  rw [← koszulBraiding_inv X Y, Iso.hom_inv_id]

end Symmetric

end KoszulBraiding

end HomologicalComplex

namespace TauCeti

section Summand

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]

/-- On a homogeneous summand, the inverse Koszul braiding of cochain complexes is the inverse
coefficient braiding multiplied by the same Koszul sign `(-1)^(q * p)`.  It needs only the two
tensor products of `X` and `Y`, not the monoidal structure on all cochain complexes.  Like
`TauCeti.ι_koszulBraiding_hom`, it has higher `simp` priority than the general
`HomologicalComplex.ιTensorObj_koszulBraiding_inv_f`. -/
@[reassoc (attr := simp high)]
lemma ι_koszulBraiding_inv (X Y : CochainComplex C ℤ) [X.HasTensor Y] [Y.HasTensor X]
    (q p j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, p) = j) :
    HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
        (ComplexShape.up ℤ) q p j h ≫ (HomologicalComplex.koszulBraiding X Y).inv.f j =
      (q * p).negOnePow • ((β_ (X.X p) (Y.X q)).inv ≫
        HomologicalComplex.ιMapBifunctor X Y (curriedTensor C)
          (ComplexShape.up ℤ) p q j (by dsimp at h ⊢; omega)) := by
  simp

end Summand

variable (C : Type*) [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X Y : GradedObject ℤ C), GradedObject.HasTensor X Y]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

section Braided

variable [BraidedCategory C]

/-- The bidegree-`(p, q)` component of the Koszul braiding `X ⊗ Y ⟶ Y ⊗ X`: the braiding of
`C` on the summand `X.X p ⊗ Y.X q`, carrying the Koszul sign `(-1)^{p * q}`. -/
noncomputable def koszulBraidingSummand (X Y : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    X.X p ⊗ Y.X q ⟶ (Y ⊗ X).X j :=
  (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
    HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
      (ComplexShape.up ℤ) q p j (by dsimp at h ⊢; omega))

/-- The bidegree component of the Koszul braiding is the coefficient braiding, followed by
the inclusion of the swapped summand, and scaled by `(-1)^(p*q)`. -/
lemma koszulBraidingSummand_def (X Y : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    koszulBraidingSummand C X Y p q j h =
      (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
          (ComplexShape.up ℤ) q p j (by dsimp at h ⊢; omega)) :=
  (rfl)

/-- On the summand `X.X p ⊗ Y.X q`, the Koszul braiding of cochain complexes is its bidegree
component `TauCeti.koszulBraidingSummand`: the coefficient braiding followed by the inclusion of
the swapped summand, with the sign `(-1)^(p * q)`.  It has higher `simp` priority than the general
`HomologicalComplex.ιTensorObj_koszulBraiding_hom_f`, so that `simp` reaches the bidegree
component rather than the unevaluated sign `ComplexShape.σ`. -/
@[reassoc (attr := simp high)]
lemma ι_koszulBraiding_hom (X Y : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor X Y (curriedTensor C)
        (ComplexShape.up ℤ) p q j h ≫ (HomologicalComplex.koszulBraiding X Y).hom.f j =
      koszulBraidingSummand C X Y p q j h := by
  simp [koszulBraidingSummand, mul_comm q p]

/-- The Koszul braiding of cochain complexes is natural in the left-hand factor. -/
lemma koszulBraiding_hom_naturality_left {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (Z : CochainComplex C ℤ) :
    f ▷ Z ≫ (HomologicalComplex.koszulBraiding Y Z).hom =
      (HomologicalComplex.koszulBraiding X Z).hom ≫ Z ◁ f :=
  HomologicalComplex.koszulBraiding_hom_naturality X Z f (𝟙 Z)

/-- The Koszul braiding of cochain complexes is natural in the right-hand factor. -/
lemma koszulBraiding_hom_naturality_right (X : CochainComplex C ℤ)
    {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    X ◁ f ≫ (HomologicalComplex.koszulBraiding X Z).hom =
      (HomologicalComplex.koszulBraiding X Y).hom ≫ f ▷ X :=
  HomologicalComplex.koszulBraiding_hom_naturality X Y (𝟙 X) f

/- Composing a left whiskering into the braiding summand: the braiding of `C` is natural,
so a map into the second factor passes through it and becomes a right whiskering.  Stating this
with a general `g` avoids rewriting under the two different spellings (`⊗` and
`HomologicalComplex.mapBifunctor`) of a totalized tensor product. -/
@[reassoc]
private lemma whiskerLeft_comp_koszulBraidingSummand (X W : CochainComplex C ℤ)
    (A : C) (p m j : ℤ) (g : A ⟶ W.X m)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, m) = j) :
    (X.X p ◁ g) ≫ koszulBraidingSummand C X W p m j h =
      (p * m).negOnePow • ((β_ (X.X p) A).hom ≫ (g ▷ X.X p) ≫
        HomologicalComplex.ιMapBifunctor W X (curriedTensor C)
          (ComplexShape.up ℤ) m p j (by dsimp at h ⊢; omega)) := by
  rw [koszulBraidingSummand, Linear.comp_units_smul,
    BraidedCategory.braiding_naturality_right_assoc]

/- The counterpart of `whiskerLeft_comp_koszulBraidingSummand` for a right whiskering. -/
@[reassoc]
private lemma whiskerRight_comp_koszulBraidingSummand (W X : CochainComplex C ℤ)
    (A : C) (m p j : ℤ) (g : A ⟶ W.X m)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (m, p) = j) :
    (g ▷ X.X p) ≫ koszulBraidingSummand C W X m p j h =
      (m * p).negOnePow • ((β_ A (X.X p)).hom ≫ (X.X p ◁ g) ≫
        HomologicalComplex.ιMapBifunctor X W (curriedTensor C)
          (ComplexShape.up ℤ) p m j (by dsimp at h ⊢; omega)) := by
  rw [koszulBraidingSummand, Linear.comp_units_smul,
    BraidedCategory.braiding_naturality_left_assoc]

section Hexagon

variable (X Y Z : CochainComplex C ℤ)

/- `ComplexShape.r` at `ComplexShape.up ℤ` is addition of the three degrees; Mathlib has no named
specialization reducing it. -/
private lemma up_r_eq {p q r j : ℤ}
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) : p + q + r = j := h

private lemma up_r_of {p q r j : ℤ} (h : p + q + r = j) :
    ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j := h

private lemma ι₁₂_hexagon_forward_lhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C)
        (curriedTensor C) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      ((α_ X Y Z).hom ≫ (HomologicalComplex.koszulBraiding X (Y ⊗ Z)).hom ≫
        (α_ Y Z X).hom).f j =
      (p * (q + r)).negOnePow • ((α_ (X.X p) (Y.X q) (Z.X r)).hom ≫
        (β_ (X.X p) (Y.X q ⊗ Z.X r)).hom ≫ (α_ (Y.X q) (Z.X r) (X.X p)).hom ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C)
            (curriedTensor C) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r (p + q) j rfl h',
    Category.assoc,
    HomologicalComplex.ι_ι_associator_hom_assoc _ _ _ p q r (p + q) (q + r) j rfl rfl h'
      (by omega),
    ι_koszulBraiding_hom_assoc,
    whiskerLeft_comp_koszulBraidingSummand_assoc C X (Y ⊗ Z) _ p (q + r) j
      (HomologicalComplex.ιTensorObj Y Z q r (q + r) rfl)]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [HomologicalComplex.ι_ι_associator_hom Y Z X q r p (q + r) (r + p) j rfl rfl (by omega)
    (by omega), Linear.comp_units_smul,
    ← HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft Y Z X q r p (r + p) j rfl (by omega)]

private lemma ι₁₂_hexagon_forward_rhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C)
        (curriedTensor C) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      (((HomologicalComplex.koszulBraiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫
        (Y ◁ (HomologicalComplex.koszulBraiding X Z).hom)).f j =
      (p * (q + r)).negOnePow • (((β_ (X.X p) (Y.X q)).hom ▷ Z.X r) ≫
        (α_ (Y.X q) (X.X p) (Z.X r)).hom ≫ (Y.X q ◁ (β_ (X.X p) (Z.X r)).hom) ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C)
            (curriedTensor C) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r (q + p) j (by omega)
      (by omega),
    Category.assoc, HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [curriedTensor_map_app]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ι_koszulBraiding_hom, koszulBraidingSummand,
    Units.smul_def, ← tensorHom_id, zsmul_tensorHom, tensorHom_id, ← Units.smul_def,
    MonoidalCategory.comp_whiskerRight,
    Linear.units_smul_comp, Category.assoc]
  -- The whiskered braiding has domain `HomologicalComplex.tensorObj X Y`, so its summand inclusion
  -- is spelled with `HomologicalComplex.tensorObj Y X` rather than `Y ⊗ X`; the two agree only
  -- after unfolding the monoidal structure.
  erw [HomologicalComplex.ι_ι_associator_hom_assoc Y X Z q p r (q + p) (p + r) j rfl rfl
    (by omega) (by omega)]
  rw [HomologicalComplex.whiskerLeft_eq_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]
  simp only [curriedTensor_obj_map]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ι_koszulBraiding_hom, koszulBraidingSummand,
    Units.smul_def (p * r).negOnePow, ← id_tensorHom, tensorHom_zsmul, id_tensorHom,
    ← Units.smul_def,
    MonoidalCategory.whiskerLeft_comp,
    Linear.units_smul_comp, Category.assoc]
  -- As above, the inclusion is spelled with `HomologicalComplex.tensorObj Z X` for `Z ⊗ X`.
  erw [← HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft Y Z X q r p (p + r) j (by omega)
    (by omega)]
  rw [Linear.comp_units_smul, Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add,
    show p * q + p * r = p * (q + r) by ring]

/-- **The first hexagon identity** for the Koszul braiding of cochain complexes. -/
lemma koszulBraiding_hom_hexagon_forward :
    (α_ X Y Z).hom ≫ (HomologicalComplex.koszulBraiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((HomologicalComplex.koszulBraiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫
        (Y ◁ (HomologicalComplex.koszulBraiding X Z).hom) := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  rw [ι₁₂_hexagon_forward_lhs, ι₁₂_hexagon_forward_rhs]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact BraidedCategory.hexagon_forward (X.X p) (Y.X q) (Z.X r)

end Hexagon

variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

/-- **The second hexagon identity** for the Koszul braiding of cochain complexes. -/
lemma koszulBraiding_hom_hexagon_reverse (X Y Z : CochainComplex C ℤ) :
    (α_ X Y Z).inv ≫ (HomologicalComplex.koszulBraiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (HomologicalComplex.koszulBraiding Y Z).hom) ≫ (α_ X Z Y).inv ≫
        ((HomologicalComplex.koszulBraiding X Z).hom ▷ Y) := by
  apply (Iso.inv_eq_inv
      ((α_ X Y Z).symm ≪≫ HomologicalComplex.koszulBraiding (X ⊗ Y) Z ≪≫ (α_ Z X Y).symm)
      (whiskerLeftIso X (HomologicalComplex.koszulBraiding Y Z) ≪≫ (α_ X Z Y).symm ≪≫
        whiskerRightIso (HomologicalComplex.koszulBraiding X Z) Y)).1
  -- The forward hexagon for the reversed coefficient braiding is the inverse of this hexagon.
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    HomologicalComplex.koszulBraiding_inv_eq_reverseBraiding, Category.assoc]
  let := reverseBraiding C
  exact koszulBraiding_hom_hexagon_forward C Z X Y

/-- Cochain complexes in `C` form a braided monoidal category under the Koszul braiding: on the
summand `X^p ⊗ Y^q` of Mathlib's totalized tensor product it is `(-1)^(p * q)` times the
coefficient braiding of `X^p` and `Y^q`. For complexes of modules, whose coefficient braiding is
the tensor flip, this is `x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x`. -/
noncomputable instance koszulBraidedCategory :
    BraidedCategory (CochainComplex C ℤ) where
  braiding X Y := HomologicalComplex.koszulBraiding X Y
  braiding_naturality_right X _ _ f := koszulBraiding_hom_naturality_right C X f
  braiding_naturality_left f Z := koszulBraiding_hom_naturality_left C f Z
  hexagon_forward X Y Z := koszulBraiding_hom_hexagon_forward C X Y Z
  hexagon_reverse X Y Z := koszulBraiding_hom_hexagon_reverse C X Y Z

/-- The braiding of the monoidal category `CochainComplex C ℤ` is the Koszul
braiding. -/
lemma braiding_eq_koszulBraiding (X Y : CochainComplex C ℤ) :
    β_ X Y = HomologicalComplex.koszulBraiding X Y :=
  (rfl)

section TensorMu

/-- **The middle-four interchange on a homogeneous summand.**  On the summand
`(X₁.X a ⊗ X₂.X b) ⊗ (Y₁.X c ⊗ Y₂.X d)` of `(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂)`, the interchange
`MonoidalCategory.tensorμ` of cochain complexes is the interchange of the four coefficient objects,
landing
in the summand `(X₁.X a ⊗ Y₁.X c) ⊗ (X₂.X b ⊗ Y₂.X d)`, with the Koszul sign `(-1)^(b * c)` of
moving the degree-`b` factor past the degree-`c` factor. -/
@[reassoc]
lemma ι_tensorμ (X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ) (a b c d ab cd n : ℤ)
    (hab : a + b = ab) (hcd : c + d = cd) (h : ab + cd = n) :
    (HomologicalComplex.ιTensorObj X₁ X₂ a b ab hab ⊗ₘ
        HomologicalComplex.ιTensorObj Y₁ Y₂ c d cd hcd) ≫
        HomologicalComplex.ιTensorObj (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) ab cd n h ≫
          (tensorμ X₁ X₂ Y₁ Y₂).f n =
      (b * c).negOnePow • (tensorμ (X₁.X a) (X₂.X b) (Y₁.X c) (Y₂.X d) ≫
        (HomologicalComplex.ιTensorObj X₁ Y₁ a c (a + c) rfl ⊗ₘ
          HomologicalComplex.ιTensorObj X₂ Y₂ b d (b + d) rfl) ≫
          HomologicalComplex.ιTensorObj (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (a + c) (b + d) n (by omega)) := by
  subst hab hcd
  -- Follow the summand through the five factors of `tensorμ`.  The codomain of `ιTensorObj` is
  -- spelled `(HomologicalComplex.tensorObj K L).X j` rather than `(K ⊗ L).X j`, so the
  -- associator steps match the whiskered inclusions only up to unfolding the monoidal structure.
  simp only [tensorμ, HomologicalComplex.comp_f, tensorHom_def', Category.assoc]
  erw [HomologicalComplex.ι_ι_associator_hom_assoc X₁ X₂ (Y₁ ⊗ Y₂) a b (c + d)
    (a + b) (b + (c + d)) n rfl rfl h (by omega), associator_naturality_right_assoc]
  rw [HomologicalComplex.ι_whiskerLeft_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc,
    HomologicalComplex.ι_ι_associator_inv X₂ Y₁ Y₂ b c d (b + c) (c + d) _ rfl rfl (by omega) rfl,
    HomologicalComplex.ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, Category.assoc,
    Category.assoc, HomologicalComplex.ι_whiskerRight, ← comp_whiskerRight_assoc,
    braiding_eq_koszulBraiding, ι_koszulBraiding_hom, koszulBraidingSummand_def]
  -- Pull the Koszul sign out of the whiskerings; what remains is sign-free.
  simp only [Units.smul_def, ← tensorHom_id, ← id_tensorHom, zsmul_tensorHom, tensorHom_zsmul,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  simp only [tensorHom_id, id_tensorHom]
  congr 1
  rw [HomologicalComplex.ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, comp_whiskerRight]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_ι_associator_hom Y₁ X₂ Y₂ c b d
    (b + c) (b + d) (b + (c + d)) (by omega) rfl (by omega) (by omega)]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [HomologicalComplex.ι_ι_associator_inv X₁ Y₁ (X₂ ⊗ Y₂) a c (b + d) (a + c) (b + (c + d)) n
    rfl (by omega) (by omega) (by omega), ← associator_inv_naturality_right_assoc]
  rfl

end TensorMu

end Braided

section Symmetric

variable [SymmetricCategory C]

variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

/-- The Koszul braiding over symmetric coefficients is symmetric. -/
noncomputable instance koszulSymmetricCategory :
    SymmetricCategory (CochainComplex C ℤ) where
  symmetry X Y := HomologicalComplex.koszulBraiding_hom_comp_hom X Y

end Symmetric

end TauCeti
