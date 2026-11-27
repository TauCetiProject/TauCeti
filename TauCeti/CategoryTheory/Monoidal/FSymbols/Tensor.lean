/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.FSymbols.Model
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Tensor products in the model of F-symbols

The fusion multiplicities give the tensor product of graded bases. In each output grade, the
tensor product of maps is a block diagonal matrix whose blocks are Kronecker products with an
identity on the multiplicity index. The unit laws identify the tensor product with the simple
object at the unit grade with the original graded basis, giving the unitors. The F-matrices
give the natural associator, and their middle-unit equation gives the triangle.

We use `Matrix.blockDiagonal'` and `Matrix.kroneckerMap` to compose the maps on the graded
bases, and `TauCeti.FSymbols.Model.isoOfEquiv` for the unitors.

## References

* A. Kitaev, *Anyons in an exactly solved model and beyond*, Appendix E, §E.7.2.
-/

public section

noncomputable section

open CategoryTheory Matrix
open scoped Kronecker

namespace TauCeti.FSymbols.Model

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type v} [CommSemiring R]
  {N : FusionRules ι} {P : FSymbols R N}

/-- The tensor product of two graded bases, with one copy of each pair of basis vectors for
each fusion channel. The body is exposed so that callers can index its matrices by these
pairs of basis vectors and fusion indices. -/
@[expose]
def tensorObj (X Y : Model P) : Model P :=
  ⟨fun c ↦ Σ ab : ι × ι, (X.basis ab.1 × Y.basis ab.2) × Fin (N.N ab.1 ab.2 c)⟩

variable {X X' X'' Y Y' Y'' : Model P}

/-- The tensor product of two maps is block diagonal in the pair of input grades. Each block is
the Kronecker product of the two maps and the identity on the fusion indices. -/
def tensorHom (f : X ⟶ X') (g : Y ⟶ Y') : tensorObj X Y ⟶ tensorObj X' Y' :=
  fun c ↦ blockDiagonal' fun ab ↦ (f ab.1 ⊗ₖ g ab.2) ⊗ₖ (1 : Matrix (Fin (N.N ab.1 ab.2 c)) _ R)

/-- Within a fixed pair of input grades, tensoring multiplies the two matrix entries and acts
by the identity on the fusion indices. -/
@[simp]
theorem tensorHom_apply (f : X ⟶ X') (g : Y ⟶ Y') (a b c : ι)
    (x : X.basis a) (x' : X'.basis a) (y : Y.basis b) (y' : Y'.basis b)
    (i j : Fin (N.N a b c)) :
    tensorHom f g c ⟨(a, b), (x, y), i⟩ ⟨(a, b), (x', y'), j⟩ =
      f a x x' * g b y y' * (1 : Matrix (Fin (N.N a b c)) _ R) i j :=
  blockDiagonal'_apply_eq _ _ _ _

/-- A tensor product of maps has zero entries between different pairs of input grades. -/
theorem tensorHom_apply_of_ne (f : X ⟶ X') (g : Y ⟶ Y') {ab ab' : ι × ι}
    (h : ab ≠ ab') (c : ι) (x : X.basis ab.1) (y : Y.basis ab.2)
    (x' : X'.basis ab'.1) (y' : Y'.basis ab'.2)
    (i : Fin (N.N ab.1 ab.2 c)) (j : Fin (N.N ab'.1 ab'.2 c)) :
    tensorHom f g c ⟨ab, (x, y), i⟩ ⟨ab', (x', y'), j⟩ = 0 :=
  blockDiagonal'_apply_ne _ _ _ h

/-- Tensoring two identity maps gives the identity of the tensor product. -/
@[simp]
theorem tensorHom_id_id (X Y : Model P) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  ext1 c
  simp only [tensorHom, id_apply, one_kronecker_one]
  exact blockDiagonal'_one

/-- Tensoring commutes with composition. -/
@[simp]
theorem tensorHom_comp_tensorHom (f : X ⟶ X') (g : Y ⟶ Y')
    (f' : X' ⟶ X'') (g' : Y' ⟶ Y'') :
    tensorHom f g ≫ tensorHom f' g' = tensorHom (f ≫ f') (g ≫ g') := by
  ext1 c
  simp only [comp_apply, tensorHom]
  refine (blockDiagonal'_mul _ _).symm.trans (congrArg blockDiagonal' (funext fun ab ↦ ?_))
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul]

section Linear

variable {K : Type v} [CommRing K] {Q : FSymbols K N}
  {A A' B B' : Model Q}

/-- Tensoring is additive in its first map. -/
@[simp]
theorem tensorHom_add_left (f f' : A ⟶ A') (g : B ⟶ B') :
    tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  ext1 c
  simp only [tensorHom, add_apply, add_kronecker]
  exact blockDiagonal'_add _ _

/-- Tensoring is additive in its second map. -/
@[simp]
theorem tensorHom_add_right (f : A ⟶ A') (g g' : B ⟶ B') :
    tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  ext1 c
  simp only [tensorHom, add_apply, kronecker_add, add_kronecker]
  exact blockDiagonal'_add _ _

/-- Tensoring is homogeneous in its first map. -/
@[simp]
theorem tensorHom_smul_left (r : K) (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom (r • f) g = r • tensorHom f g := by
  ext1 c
  simp only [tensorHom, smul_apply, smul_kronecker]
  exact blockDiagonal'_smul (α := K) r _

/-- Tensoring is homogeneous in its second map. -/
@[simp]
theorem tensorHom_smul_right (r : K) (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom f (r • g) = r • tensorHom f g := by
  ext1 c
  simp only [tensorHom, smul_apply, kronecker_smul, smul_kronecker]
  exact blockDiagonal'_smul (α := K) r _

end Linear

/-- The tensor bifunctor on the model category, exposed for the types of its maps. -/
@[expose]
def tensorFunctor : Model P × Model P ⥤ Model P where
  obj XY := tensorObj XY.1 XY.2
  map fg := tensorHom fg.1 fg.2
  map_id XY := tensorHom_id_id XY.1 XY.2
  map_comp f g := (tensorHom_comp_tensorHom f.1 f.2 g.1 g.2).symm

/-- The objects of the tensor bifunctor are the tensor products of the input objects. -/
@[simp]
theorem tensorFunctor_obj (X Y : Model P) :
    (tensorFunctor (P := P)).obj (X, Y) = tensorObj X Y :=
  (rfl)

/-- The maps of the tensor bifunctor are the tensor products of the input maps. -/
@[simp]
theorem tensorFunctor_map (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorFunctor (P := P)).map (X := (X, Y)) (Y := (X', Y')) (f, g) = tensorHom f g :=
  (rfl)

/-- A pair of grade-wise basis bijections induces a bijection of tensor product bases. -/
def tensorBasisCongr (e : ∀ a, X.basis a ≃ X'.basis a) (e' : ∀ b, Y.basis b ≃ Y'.basis b)
    (c : ι) : (tensorObj X Y).basis c ≃ (tensorObj X' Y').basis c :=
  Equiv.sigmaCongrRight fun ab ↦ ((e ab.1).prodCongr (e' ab.2)).prodCongr (Equiv.refl _)

/-- Applying a tensor product of basis bijections keeps the grades and fusion index fixed. -/
@[simp]
theorem tensorBasisCongr_apply (e : ∀ a, X.basis a ≃ X'.basis a)
    (e' : ∀ b, Y.basis b ≃ Y'.basis b) (a b c : ι) (x : X.basis a) (y : Y.basis b)
    (i : Fin (N.N a b c)) :
    tensorBasisCongr e e' c ⟨(a, b), (x, y), i⟩ = ⟨(a, b), (e a x, e' b y), i⟩ :=
  (rfl)

/-- Tensoring permutation matrices gives the permutation matrix of the tensor basis bijection. -/
theorem tensorHom_isoOfEquiv_hom (e : ∀ a, X.basis a ≃ X'.basis a)
    (e' : ∀ b, Y.basis b ≃ Y'.basis b) :
    tensorHom (isoOfEquiv e).hom (isoOfEquiv e').hom =
      (isoOfEquiv (tensorBasisCongr e e')).hom := by
  ext1 c
  ext ⟨⟨a, b⟩, ⟨x, y⟩, i⟩ ⟨⟨a', b'⟩, ⟨x', y'⟩, j⟩
  erw [isoOfEquiv_hom_apply, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply,
    tensorBasisCongr_apply]
  by_cases hab : (a, b) = (a', b')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    erw [tensorHom_apply, isoOfEquiv_hom_apply, isoOfEquiv_hom_apply,
      PEquiv.toMatrix_toPEquiv_apply, PEquiv.toMatrix_toPEquiv_apply,
      Pi.single_apply, Pi.single_apply]
    simp only [Matrix.one_apply]
    have _hcoords (hh : (⟨(a, b), (x', y'), j⟩ : (tensorObj X' Y').basis c) =
        ⟨(a, b), (e a x, e' b y), i⟩) :
        x' = e a x ∧ y' = e' b y ∧ i = j := by
      have hdata := (Sigma.mk.inj_iff.mp hh).2.eq
      exact ⟨congrArg (fun z ↦ z.1.1) hdata, congrArg (fun z ↦ z.1.2) hdata,
        (congrArg Prod.snd hdata).symm⟩
    split_ifs <;> simp only [mul_zero, mul_one] <;> grind
  · erw [tensorHom_apply_of_ne _ _ hab]
    split_ifs with h
    · exact (hab (congrArg Sigma.fst h).symm).elim
    · rfl

/-- The left unitor on graded bases. Its inverse inserts the unique unit vector and fusion
index. -/
def leftUnitorBasis (X : Model P) (c : ι) :
    (tensorObj (simple P N.unit) X).basis c ≃ X.basis c :=
  (Equiv.ofBijective (fun x ↦ ⟨(N.unit, c), (default, x), N.unitLeft c⟩) (by
    constructor
    · intro x y h
      exact congrArg (fun z ↦ z.1.2) (Sigma.mk.inj_iff.mp h).2.eq
    · rintro ⟨⟨a, b⟩, ⟨i, x⟩, j⟩
      obtain rfl := eq_of_simple_basis i
      have hb : b = c := by
        by_contra h
        simpa [N.N_unit_left_of_ne b c h] using j.isLt
      subst b
      exact ⟨x, by rw [Subsingleton.elim i default, Subsingleton.elim j (N.unitLeft c)]⟩)).symm

/-- The right unitor on graded bases. Its inverse inserts the unique unit vector and fusion
index. -/
def rightUnitorBasis (X : Model P) (c : ι) :
    (tensorObj X (simple P N.unit)).basis c ≃ X.basis c :=
  (Equiv.ofBijective (fun x ↦ ⟨(c, N.unit), (x, default), N.unitRight c⟩) (by
    constructor
    · intro x y h
      exact congrArg (fun z ↦ z.1.1) (Sigma.mk.inj_iff.mp h).2.eq
    · rintro ⟨⟨a, b⟩, ⟨x, i⟩, j⟩
      obtain rfl := eq_of_simple_basis i
      have ha : a = c := by
        by_contra h
        simpa [N.N_unit_right_of_ne a c h] using j.isLt
      subst a
      exact ⟨x, by rw [Subsingleton.elim i default, Subsingleton.elim j (N.unitRight c)]⟩)).symm

/-- The inverse left unitor on a basis vector. -/
@[simp]
theorem leftUnitorBasis_symm_apply (X : Model P) (c : ι) (x : X.basis c) :
    (leftUnitorBasis X c).symm x = ⟨(N.unit, c), (default, x), N.unitLeft c⟩ :=
  (rfl)

/-- The inverse right unitor on a basis vector. -/
@[simp]
theorem rightUnitorBasis_symm_apply (X : Model P) (c : ι) (x : X.basis c) :
    (rightUnitorBasis X c).symm x = ⟨(c, N.unit), (x, default), N.unitRight c⟩ :=
  (rfl)

/-- Left tensoring with the simple object at the unit grade is isomorphic to the original
object, by the corresponding bijections of graded bases. -/
def leftUnitor (X : Model P) : tensorObj (simple P N.unit) X ≅ X :=
  isoOfEquiv (leftUnitorBasis X)

/-- Right tensoring with the simple object at the unit grade is isomorphic to the original
object, by the corresponding bijections of graded bases. -/
def rightUnitor (X : Model P) : tensorObj X (simple P N.unit) ≅ X :=
  isoOfEquiv (rightUnitorBasis X)

/-- The forward left unitor is the permutation matrix of the basis bijection. -/
@[simp]
theorem leftUnitor_hom_apply (X : Model P) (c : ι) :
    (leftUnitor X).hom c = (leftUnitorBasis X c).toPEquiv.toMatrix :=
  isoOfEquiv_hom_apply _ _

/-- The forward right unitor is the permutation matrix of the basis bijection. -/
@[simp]
theorem rightUnitor_hom_apply (X : Model P) (c : ι) :
    (rightUnitor X).hom c = (rightUnitorBasis X c).toPEquiv.toMatrix :=
  isoOfEquiv_hom_apply _ _

/-- The inverse left unitor is the permutation matrix of the inverse basis bijection. -/
@[simp]
theorem leftUnitor_inv_apply (X : Model P) (c : ι) :
    (leftUnitor X).inv c = (leftUnitorBasis X c).symm.toPEquiv.toMatrix :=
  isoOfEquiv_inv_apply _ _

/-- The inverse right unitor is the permutation matrix of the inverse basis bijection. -/
@[simp]
theorem rightUnitor_inv_apply (X : Model P) (c : ι) :
    (rightUnitor X).inv c = (rightUnitorBasis X c).symm.toPEquiv.toMatrix :=
  isoOfEquiv_inv_apply _ _

/-- Naturality of the left unitor. -/
@[reassoc]
theorem leftUnitor_naturality (f : X ⟶ X') :
    tensorHom (𝟙 (simple P N.unit)) f ≫ (leftUnitor X').hom = (leftUnitor X).hom ≫ f := by
  ext1 c
  ext i j
  obtain ⟨x, rfl⟩ := (leftUnitorBasis X c).symm.surjective i
  rw [comp_apply, comp_apply, leftUnitor_hom_apply, leftUnitor_hom_apply,
    PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  dsimp only [Matrix.submatrix, Matrix.of_apply, id]
  erw [Equiv.apply_symm_apply, leftUnitorBasis_symm_apply, leftUnitorBasis_symm_apply,
    tensorHom_apply, id_apply]
  simp

/-- Naturality of the right unitor. -/
@[reassoc]
theorem rightUnitor_naturality (f : X ⟶ X') :
    tensorHom f (𝟙 (simple P N.unit)) ≫ (rightUnitor X').hom = (rightUnitor X).hom ≫ f := by
  ext1 c
  ext i j
  obtain ⟨x, rfl⟩ := (rightUnitorBasis X c).symm.surjective i
  rw [comp_apply, comp_apply, rightUnitor_hom_apply, rightUnitor_hom_apply,
    PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  dsimp only [Matrix.submatrix, Matrix.of_apply, id]
  erw [Equiv.apply_symm_apply, rightUnitorBasis_symm_apply, rightUnitorBasis_symm_apply,
    tensorHom_apply, id_apply]
  simp

section Associator

variable {Z Z' : Model P}

/-- Reorder the basis of the left-associated tensor product to group the three original basis
vectors together and the two fusion indices together. -/
def leftAssocBasisEquiv (X Y Z : Model P) (d : ι) :
    (tensorObj (tensorObj X Y) Z).basis d ≃
      Σ abc : ι × ι × ι, (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) ×
        N.Left abc.1 abc.2.1 abc.2.2 d where
  toFun p :=
    let xy := p.2.1.1
    ⟨(xy.1.1, xy.1.2, p.1.2), (xy.2.1.1, xy.2.1.2, p.2.1.2), ⟨p.1.1, xy.2.2, p.2.2⟩⟩
  invFun p :=
    let abc := p.1
    let xyz := p.2.1
    let fusion := p.2.2
    ⟨(fusion.1, abc.2.2), (⟨(abc.1, abc.2.1), (xyz.1, xyz.2.1), fusion.2.1⟩, xyz.2.2), fusion.2.2⟩
  left_inv := by rintro ⟨⟨e, c⟩, ⟨⟨⟨a, b⟩, ⟨x, y⟩, i⟩, z⟩, j⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, ⟨x, y, z⟩, ⟨e, i, j⟩⟩; rfl

/-- Reorder the basis of the right-associated tensor product to group the three original basis
vectors together and the two fusion indices together. -/
def rightAssocBasisEquiv (X Y Z : Model P) (d : ι) :
    (tensorObj X (tensorObj Y Z)).basis d ≃
      Σ abc : ι × ι × ι, (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) ×
        N.Right abc.1 abc.2.1 abc.2.2 d where
  toFun p :=
    let yz := p.2.1.2
    ⟨(p.1.1, yz.1.1, yz.1.2), (p.2.1.1, yz.2.1.1, yz.2.1.2), ⟨p.1.2, yz.2.2, p.2.2⟩⟩
  invFun p :=
    let abc := p.1
    let xyz := p.2.1
    let fusion := p.2.2
    ⟨(abc.1, fusion.1), (xyz.1, ⟨(abc.2.1, abc.2.2), xyz.2, fusion.2.1⟩), fusion.2.2⟩
  left_inv := by rintro ⟨⟨a, f⟩, ⟨x, ⟨⟨b, c⟩, ⟨y, z⟩, k⟩⟩, l⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, ⟨x, y, z⟩, ⟨f, k, l⟩⟩; rfl

/-- In the left-associated tensor product, the two fusion indices form the left index of
an F-matrix. -/
@[simp]
theorem leftAssocBasisEquiv_symm_apply (X Y Z : Model P) (a b c d : ι)
    (xyz : X.basis a × Y.basis b × Z.basis c) (l : N.Left a b c d) :
    (leftAssocBasisEquiv X Y Z d).symm ⟨(a, b, c), xyz, l⟩ =
      ⟨(l.1, c), (⟨(a, b), (xyz.1, xyz.2.1), l.2.1⟩, xyz.2.2), l.2.2⟩ :=
  (rfl)

/-- In the right-associated tensor product, the two fusion indices form the right index of
an F-matrix. -/
@[simp]
theorem rightAssocBasisEquiv_symm_apply (X Y Z : Model P) (a b c d : ι)
    (xyz : X.basis a × Y.basis b × Z.basis c) (r : N.Right a b c d) :
    (rightAssocBasisEquiv X Y Z d).symm ⟨(a, b, c), xyz, r⟩ =
      ⟨(a, r.1), (xyz.1, ⟨(b, c), xyz.2, r.2.1⟩), r.2.2⟩ :=
  (rfl)

private abbrev assocHomBlock (X Y Z : Model P) (d : ι) (abc : ι × ι × ι) :=
  (1 : Matrix (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2)
      (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) R) ⊗ₖ
    (P.Finv abc.1 abc.2.1 abc.2.2 d)ᵀ

private abbrev assocInvBlock (X Y Z : Model P) (d : ι) (abc : ι × ι × ι) :=
  (1 : Matrix (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2)
      (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) R) ⊗ₖ
    (P.F abc.1 abc.2.1 abc.2.2 d)ᵀ

private theorem assocHomBlock_mul_assocInvBlock (X Y Z : Model P) (d : ι) (abc : ι × ι × ι) :
    assocHomBlock X Y Z d abc * assocInvBlock X Y Z d abc = 1 := by
  rw [← mul_kronecker_mul, Matrix.one_mul, ← transpose_mul, P.F_mul_Finv, transpose_one,
    one_kronecker_one]

private theorem assocInvBlock_mul_assocHomBlock (X Y Z : Model P) (d : ι) (abc : ι × ι × ι) :
    assocInvBlock X Y Z d abc * assocHomBlock X Y Z d abc = 1 := by
  rw [← mul_kronecker_mul, Matrix.one_mul, ← transpose_mul, P.Finv_mul_F, transpose_one,
    one_kronecker_one]

/-- The associator isomorphism of the model. With rows indexed by source basis vectors, its
forward map uses the transposes of the inverse F-matrices and its inverse map uses the transposes
of the F-matrices. The transposes account for the fusion basis consisting of maps out of the
tensor product. -/
def associator (X Y Z : Model P) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom d := (blockDiagonal' (assocHomBlock X Y Z d)).submatrix
    (leftAssocBasisEquiv X Y Z d) (rightAssocBasisEquiv X Y Z d)
  inv d := (blockDiagonal' (assocInvBlock X Y Z d)).submatrix
    (rightAssocBasisEquiv X Y Z d) (leftAssocBasisEquiv X Y Z d)
  hom_inv_id := by
    ext1 d
    simp only [comp_apply, id_apply]
    rw [submatrix_mul_equiv _ _ _ (rightAssocBasisEquiv X Y Z d), ← blockDiagonal'_mul]
    simp only [assocHomBlock_mul_assocInvBlock]
    refine Eq.trans ?_ (submatrix_one_equiv (leftAssocBasisEquiv X Y Z d))
    congr 1
    exact blockDiagonal'_one
  inv_hom_id := by
    ext1 d
    simp only [comp_apply, id_apply]
    rw [submatrix_mul_equiv _ _ _ (leftAssocBasisEquiv X Y Z d), ← blockDiagonal'_mul]
    simp only [assocInvBlock_mul_assocHomBlock]
    refine Eq.trans ?_ (submatrix_one_equiv (rightAssocBasisEquiv X Y Z d))
    congr 1
    exact blockDiagonal'_one

/-- In grouped coordinates the associator is block diagonal in the three input grades, with
the transpose of the inverse F-matrix acting on the fusion indices in each block. -/
theorem associator_hom_submatrix (X Y Z : Model P) (d : ι) :
    ((associator X Y Z).hom d).submatrix (leftAssocBasisEquiv X Y Z d).symm
      (rightAssocBasisEquiv X Y Z d).symm =
    blockDiagonal' (fun (abc : ι × ι × ι) ↦
      (1 : Matrix (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2)
      (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) R) ⊗ₖ
        (P.Finv abc.1 abc.2.1 abc.2.2 d)ᵀ) := by
  ext i j
  simp [associator, Matrix.submatrix]

/-- In grouped coordinates the inverse associator is block diagonal in the three input grades,
with the transpose of the F-matrix acting on the fusion indices in each block. -/
theorem associator_inv_submatrix (X Y Z : Model P) (d : ι) :
    ((associator X Y Z).inv d).submatrix (rightAssocBasisEquiv X Y Z d).symm
      (leftAssocBasisEquiv X Y Z d).symm =
    blockDiagonal' (fun (abc : ι × ι × ι) ↦
      (1 : Matrix (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2)
      (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) R) ⊗ₖ
        (P.F abc.1 abc.2.1 abc.2.2 d)ᵀ) := by
  ext i j
  simp [associator, Matrix.submatrix]

private abbrev tripleTensorBlock (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (abc : ι × ι × ι) :=
  f abc.1 ⊗ₖ (g abc.2.1 ⊗ₖ h abc.2.2)

private theorem leftAssoc_tensorHom_submatrix (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : ι) :
    (tensorHom (tensorHom f g) h d).submatrix (leftAssocBasisEquiv X Y Z d).symm
      (leftAssocBasisEquiv X' Y' Z' d).symm =
    blockDiagonal' (fun (abc : ι × ι × ι) ↦
      tripleTensorBlock f g h abc ⊗ₖ (1 : Matrix (N.Left abc.1 abc.2.1 abc.2.2 d) _ R)) := by
  ext ⟨⟨a, b, c⟩, ⟨x, y, z⟩, ⟨e, i, j⟩⟩ ⟨⟨a', b', c'⟩, ⟨x', y', z'⟩, ⟨e', i', j'⟩⟩
  dsimp only [Matrix.submatrix, Matrix.of_apply]
  erw [leftAssocBasisEquiv_symm_apply, leftAssocBasisEquiv_symm_apply]
  by_cases h₁ : (a, b, c) = (a', b', c')
  · obtain ⟨rfl, rfl, rfl⟩ := by simpa using h₁
    by_cases he : e = e'
    · subst e'
      erw [tensorHom_apply, tensorHom_apply, blockDiagonal'_apply_eq]
      simp only [tripleTensorBlock, kronecker_apply, Matrix.one_apply, Sigma.mk.inj_iff,
        heq_eq_eq, Prod.mk.injEq, true_and]
      by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj, mul_assoc]
    · have h₂ : ¬((e, c) = (e', c)) := fun h₂ ↦
        he (congrArg Prod.fst h₂)
      erw [tensorHom_apply_of_ne _ _ h₂, blockDiagonal'_apply_eq]
      simp [tripleTensorBlock, he]
  · erw [blockDiagonal'_apply_ne _ _ _ h₁]
    by_cases h₂ : (e, c) = (e', c')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
      have h₃ : (a, b) ≠ (a', b') := fun h₃ ↦ h₁ (by simpa using h₃)
      erw [tensorHom_apply, tensorHom_apply_of_ne _ _ h₃]
      simp
    · exact tensorHom_apply_of_ne _ _ h₂ _ _ _ _ _ _ _

private theorem rightAssoc_tensorHom_submatrix (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : ι) :
    (tensorHom f (tensorHom g h) d).submatrix (rightAssocBasisEquiv X Y Z d).symm
      (rightAssocBasisEquiv X' Y' Z' d).symm =
    blockDiagonal' (fun (abc : ι × ι × ι) ↦
      tripleTensorBlock f g h abc ⊗ₖ (1 : Matrix (N.Right abc.1 abc.2.1 abc.2.2 d) _ R)) := by
  ext ⟨⟨a, b, c⟩, ⟨x, y, z⟩, ⟨e, i, j⟩⟩ ⟨⟨a', b', c'⟩, ⟨x', y', z'⟩, ⟨e', i', j'⟩⟩
  dsimp only [Matrix.submatrix, Matrix.of_apply]
  erw [rightAssocBasisEquiv_symm_apply, rightAssocBasisEquiv_symm_apply]
  by_cases h₁ : (a, b, c) = (a', b', c')
  · obtain ⟨rfl, rfl, rfl⟩ := by simpa using h₁
    by_cases he : e = e'
    · subst e'
      erw [tensorHom_apply, tensorHom_apply, blockDiagonal'_apply_eq]
      simp only [tripleTensorBlock, kronecker_apply, Matrix.one_apply, Sigma.mk.inj_iff,
        heq_eq_eq, Prod.mk.injEq, true_and]
      by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj]
    · have h₂ : ¬((a, e) = (a, e')) := fun h₂ ↦
        he (congrArg Prod.snd h₂)
      erw [tensorHom_apply_of_ne _ _ h₂, blockDiagonal'_apply_eq]
      simp [tripleTensorBlock, he]
  · erw [blockDiagonal'_apply_ne _ _ _ h₁]
    by_cases h₂ : (a, e) = (a', e')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
      have h₃ : (b, c) ≠ (b', c') := fun h₃ ↦ h₁ (by simpa using h₃)
      erw [tensorHom_apply, tensorHom_apply_of_ne _ _ h₃]
      simp
    · exact tensorHom_apply_of_ne _ _ h₂ _ _ _ _ _ _ _

/-- The associator commutes with tensoring a triple of maps. -/
@[reassoc]
theorem associator_naturality (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    tensorHom (tensorHom f g) h ≫ (associator X' Y' Z').hom =
      (associator X Y Z).hom ≫ tensorHom f (tensorHom g h) := by
  ext1 d
  simp only [comp_apply]
  apply Matrix.submatrix_injective (leftAssocBasisEquiv X Y Z d).symm.surjective
    (rightAssocBasisEquiv X' Y' Z' d).symm.surjective
  dsimp only
  rw [← submatrix_mul_equiv _ _ _ (leftAssocBasisEquiv X' Y' Z' d).symm,
    ← submatrix_mul_equiv _ _ _ (rightAssocBasisEquiv X Y Z d).symm,
    leftAssoc_tensorHom_submatrix, rightAssoc_tensorHom_submatrix,
    associator_hom_submatrix, associator_hom_submatrix,
    ← blockDiagonal'_mul, ← blockDiagonal'_mul]
  refine congrArg blockDiagonal' (funext fun abc ↦ ?_)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.one_mul, Matrix.one_mul]

end Associator

section Triangle

variable (X Y)

/-- The basis map underlying the inverse associator with the unit in the middle. -/
private def triangleBasis (c : ι) :
    (tensorObj X (tensorObj (simple P N.unit) Y)).basis c ≃
      (tensorObj (tensorObj X (simple P N.unit)) Y).basis c :=
  (tensorBasisCongr (fun _ ↦ Equiv.refl _) (leftUnitorBasis Y) c).trans
    (tensorBasisCongr (fun a ↦ (rightUnitorBasis X a).symm) (fun _ ↦ Equiv.refl _) c)

private theorem associator_unit_inv :
    (associator X (simple P N.unit) Y).inv = (isoOfEquiv (triangleBasis X Y)).hom := by
  ext1 d
  apply Matrix.submatrix_injective
    (tensorBasisCongr (fun _ ↦ Equiv.refl _) (fun a ↦ (leftUnitorBasis Y a).symm) d).surjective
    (tensorBasisCongr (fun a ↦ (rightUnitorBasis X a).symm) (fun _ ↦ Equiv.refl _) d).surjective
  dsimp only
  ext ⟨⟨a, b⟩, ⟨x, y⟩, j⟩ ⟨⟨a', b'⟩, ⟨x', y'⟩, i⟩
  -- Expose the inserted unit vectors before rewriting matrix entries. Ordinary simplification
  -- does not unfold the dependent basis types of tensor products.
  let row : (tensorObj X (tensorObj (simple P N.unit) Y)).basis d :=
    ⟨(a, b), (x, ⟨(N.unit, b), (default, y), N.unitLeft b⟩), j⟩
  let col : (tensorObj (tensorObj X (simple P N.unit)) Y).basis d :=
    ⟨(a', b'), (⟨(a', N.unit), (x', default), N.unitRight a'⟩, y'), i⟩
  change (associator X (simple P N.unit) Y).inv d row col =
    (isoOfEquiv (triangleBasis X Y)).hom d row col
  have hrow : triangleBasis X Y d row =
      ⟨(a, b), (⟨(a, N.unit), (x, default), N.unitRight a⟩, y), j⟩ := by
    let e := tensorBasisCongr (fun a ↦ Equiv.refl (X.basis a)) (leftUnitorBasis Y) d
    let p : (tensorObj X Y).basis d := ⟨(a, b), (x, y), j⟩
    -- The displayed row is the image of p under the inverse of the first equivalence.
    change tensorBasisCongr (fun a ↦ (rightUnitorBasis X a).symm) (fun _ ↦ Equiv.refl _) d
      (e (e.symm p)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  erw [isoOfEquiv_hom_apply, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply, hrow]
  -- Reduce the reindexing to explicit indices so that the block-diagonal lemmas match.
  change blockDiagonal' (assocInvBlock X (simple P N.unit) Y d)
    ⟨(a, N.unit, b), (x, default, y), ⟨b, N.unitLeft b, j⟩⟩
    ⟨(a', N.unit, b'), (x', default, y'), ⟨a', N.unitRight a', i⟩⟩ = _
  by_cases hab : (a, b) = (a', b')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    erw [blockDiagonal'_apply_eq]
    simp only [assocInvBlock, kronecker_apply, transpose_apply, P.triangle, Matrix.one_apply]
    dsimp only [col]
    have _hcoords (hh :
        (⟨(a, b), (⟨(a, N.unit), (x', default), N.unitRight a⟩, y'), i⟩ :
          (tensorObj (tensorObj X (simple P N.unit)) Y).basis d) =
        ⟨(a, b), (⟨(a, N.unit), (x, default), N.unitRight a⟩, y), j⟩) :
        x' = x ∧ y' = y ∧ i = j := by
      have hdata := (Sigma.mk.inj_iff.mp hh).2.eq
      have hx := (Sigma.mk.inj_iff.mp (congrArg (fun p ↦ p.1.1) hdata)).2.eq
      exact ⟨congrArg (fun p ↦ p.1.1) hx, congrArg (fun p ↦ p.1.2) hdata, congrArg Prod.snd hdata⟩
    split_ifs <;> simp only [mul_zero, mul_one] <;> grind
  · have hab' : (a, N.unit, b) ≠ (a', N.unit, b') := by simpa using hab
    erw [blockDiagonal'_apply_ne _ _ _ hab']
    split_ifs with hc
    · exact (hab (congrArg Sigma.fst hc).symm).elim
    · rfl

private theorem triangle_inv :
    tensorHom (𝟙 X) (leftUnitor Y).inv ≫ (associator X (simple P N.unit) Y).inv =
      tensorHom (rightUnitor X).inv (𝟙 Y) := by
  have hId (A : Model P) :
      (isoOfEquiv (fun a ↦ Equiv.refl (A.basis a))).hom = 𝟙 A := by
    ext1 a
    simp
  have hL : (leftUnitor Y).inv = (isoOfEquiv (fun a ↦ (leftUnitorBasis Y a).symm)).hom := by
    ext1 a
    simp
  have hR : (rightUnitor X).inv = (isoOfEquiv (fun a ↦ (rightUnitorBasis X a).symm)).hom := by
    ext1 a
    simp
  rw [associator_unit_inv, hL, hR, ← hId X, ← hId Y,
    tensorHom_isoOfEquiv_hom, tensorHom_isoOfEquiv_hom]
  ext1 d
  simp only [comp_apply, isoOfEquiv_hom_apply, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  congr 2
  let e := tensorBasisCongr (fun a ↦ Equiv.refl (X.basis a)) (leftUnitorBasis Y) d
  let e' := tensorBasisCongr (fun a ↦ (rightUnitorBasis X a).symm)
    (fun a ↦ Equiv.refl (Y.basis a)) d
  exact Equiv.ext fun p ↦ congrArg e' (e.apply_symm_apply p)

/-- The associator and the unitors satisfy the monoidal triangle. -/
theorem triangle :
    (associator X (simple P N.unit) Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
      tensorHom (rightUnitor X).hom (𝟙 Y) := by
  have hL : tensorHom (𝟙 X) (leftUnitor Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).inv =
      𝟙 (tensorObj X (tensorObj (simple P N.unit) Y)) := by simp
  have hR : tensorHom (rightUnitor X).inv (𝟙 Y) ≫ tensorHom (rightUnitor X).hom (𝟙 Y) =
      𝟙 (tensorObj X Y) := by simp
  have hCancel : tensorHom (𝟙 X) (leftUnitor Y).hom ≫ tensorHom (rightUnitor X).inv (𝟙 Y) =
      (associator X (simple P N.unit) Y).inv := by
    rw [← triangle_inv, ← Category.assoc, hL, Category.id_comp]
  calc
    _ = (associator X (simple P N.unit) Y).hom ≫
        (tensorHom (𝟙 X) (leftUnitor Y).hom ≫ tensorHom (rightUnitor X).inv (𝟙 Y)) ≫
        tensorHom (rightUnitor X).hom (𝟙 Y) := by
      rw [Category.assoc, hR, Category.comp_id]
    _ = _ := by rw [hCancel, Iso.hom_inv_id_assoc]

end Triangle

end TauCeti.FSymbols.Model
