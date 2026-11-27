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
theorem id_tensorHom_id (X Y : Model P) :
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
  -- Destructuring the indices exposes their sigma type, while the entry lemma uses `basis`.
  erw [isoOfEquiv_hom_entry, tensorBasisCongr_apply]
  by_cases hab : (a, b) = (a', b')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    rw [tensorHom_apply, isoOfEquiv_hom_entry, isoOfEquiv_hom_entry]
    simp only [Matrix.one_apply]
    split_ifs <;> simp only [mul_zero, mul_one] <;> grind
  · rw [tensorHom_apply_of_ne _ _ hab]
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
  rw [leftUnitor, leftUnitor]
  apply isoOfEquiv_hom_naturality
  intro c x y
  rw [leftUnitorBasis_symm_apply, leftUnitorBasis_symm_apply, tensorHom_apply, id_apply]
  simp

/-- Naturality of the right unitor. -/
@[reassoc]
theorem rightUnitor_naturality (f : X ⟶ X') :
    tensorHom f (𝟙 (simple P N.unit)) ≫ (rightUnitor X').hom = (rightUnitor X).hom ≫ f := by
  rw [rightUnitor, rightUnitor]
  apply isoOfEquiv_hom_naturality
  intro c x y
  rw [rightUnitorBasis_symm_apply, rightUnitorBasis_symm_apply, tensorHom_apply, id_apply]
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
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) := by
  refine
    { hom := fun d ↦ (blockDiagonal' (assocHomBlock X Y Z d)).submatrix
        (leftAssocBasisEquiv X Y Z d) (rightAssocBasisEquiv X Y Z d)
      inv := fun d ↦ (blockDiagonal' (assocInvBlock X Y Z d)).submatrix
        (rightAssocBasisEquiv X Y Z d) (leftAssocBasisEquiv X Y Z d)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals
    ext1 d
    simp only [comp_apply, id_apply, submatrix_mul_equiv, ← blockDiagonal'_mul,
      assocHomBlock_mul_assocInvBlock, assocInvBlock_mul_assocHomBlock]
    first
    | refine Eq.trans ?_ (submatrix_one_equiv (leftAssocBasisEquiv X Y Z d))
    | refine Eq.trans ?_ (submatrix_one_equiv (rightAssocBasisEquiv X Y Z d))
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

private theorem tensorHom_assoc_submatrices
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : ι) :
    ((tensorHom (tensorHom f g) h d).submatrix (leftAssocBasisEquiv X Y Z d).symm
        (leftAssocBasisEquiv X' Y' Z' d).symm =
      blockDiagonal' (fun (abc : ι × ι × ι) ↦
        tripleTensorBlock f g h abc ⊗ₖ (1 : Matrix (N.Left abc.1 abc.2.1 abc.2.2 d) _ R))) ∧
    ((tensorHom f (tensorHom g h) d).submatrix (rightAssocBasisEquiv X Y Z d).symm
        (rightAssocBasisEquiv X' Y' Z' d).symm =
      blockDiagonal' (fun (abc : ι × ι × ι) ↦
        tripleTensorBlock f g h abc ⊗ₖ (1 : Matrix (N.Right abc.1 abc.2.1 abc.2.2 d) _ R))) := by
  constructor <;>
    ext ⟨⟨a, b, c⟩, ⟨x, y, z⟩, ⟨e, i, j⟩⟩ ⟨⟨a', b', c'⟩, ⟨x', y', z'⟩, ⟨e', i', j'⟩⟩
  all_goals
    -- The explicit sigma indices of the grouped bases unfold the corresponding `basis` types.
    erw [Matrix.submatrix_apply]
    first
    | erw [leftAssocBasisEquiv_symm_apply, leftAssocBasisEquiv_symm_apply]
    | erw [rightAssocBasisEquiv_symm_apply, rightAssocBasisEquiv_symm_apply]
    unfold tensorHom
    by_cases a = a' <;> by_cases b = b' <;> by_cases c = c' <;> by_cases e = e' <;> subst_vars <;>
      simp_all only [blockDiagonal'_apply', tripleTensorBlock, kroneckerMap_apply, Matrix.one_apply,
        Prod.mk.injEq, and_true, and_false, dite_true, dite_false, cast_eq]
  all_goals
    -- The inner Kronecker factor still has indices in a tensor product basis.
    try erw [kroneckerMap_apply]
    simp_all [blockDiagonal'_apply', Matrix.one_apply]
  all_goals split_ifs <;> simp_all [mul_assoc]

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
  obtain ⟨hLeft, hRight⟩ := tensorHom_assoc_submatrices f g h d
  rw [← submatrix_mul_equiv _ _ _ (leftAssocBasisEquiv X' Y' Z' d).symm,
    ← submatrix_mul_equiv _ _ _ (rightAssocBasisEquiv X Y Z d).symm,
    hLeft, hRight,
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

private theorem triangleBasis_apply (a b d : ι) (x : X.basis a) (y : Y.basis b)
    (j : Fin (N.N a b d)) :
    triangleBasis X Y d ⟨(a, b), (x, (leftUnitorBasis Y b).symm y), j⟩ =
      ⟨(a, b), ((rightUnitorBasis X a).symm x, y), j⟩ := by
  -- The input is written as a sigma constructor in the basis of the nested tensor product.
  erw [triangleBasis, Equiv.trans_apply, tensorBasisCongr_apply]
  dsimp only [Equiv.refl_apply]
  rw [Equiv.apply_symm_apply]

private theorem associator_unit_inv :
    (associator X (simple P N.unit) Y).inv = (isoOfEquiv (triangleBasis X Y)).hom := by
  ext1 d
  apply Matrix.submatrix_injective
    (tensorBasisCongr (fun _ ↦ Equiv.refl _) (fun a ↦ (leftUnitorBasis Y a).symm) d).surjective
    (tensorBasisCongr (fun a ↦ (rightUnitorBasis X a).symm) (fun _ ↦ Equiv.refl _) d).surjective
  dsimp only
  ext ⟨⟨a, b⟩, ⟨x, y⟩, j⟩ ⟨⟨a', b'⟩, ⟨x', y'⟩, i⟩
  -- Destructuring the indices exposes the sigma type of the unitor-reindexed bases.
  erw [Matrix.submatrix_apply, Matrix.submatrix_apply, tensorBasisCongr_apply,
    tensorBasisCongr_apply, isoOfEquiv_hom_entry]
  rw [Equiv.refl_apply, Equiv.refl_apply, triangleBasis_apply]
  simp only [leftUnitorBasis_symm_apply, rightUnitorBasis_symm_apply]
  have hAssoc := congrFun (congrFun (associator_inv_submatrix X (simple P N.unit) Y d)
    ⟨(a, N.unit, b), (x, default, y), ⟨b, N.unitLeft b, j⟩⟩)
    ⟨(a', N.unit, b'), (x', default, y'), ⟨a', N.unitRight a', i⟩⟩
  -- The grouped bases are expressed as sigma types in `associator_inv_submatrix`.
  erw [Matrix.submatrix_apply, rightAssocBasisEquiv_symm_apply,
    leftAssocBasisEquiv_symm_apply] at hAssoc
  erw [hAssoc]
  by_cases hab : (a, b) = (a', b')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    rw [blockDiagonal'_apply_eq]
    simp only [kronecker_apply, transpose_apply, P.triangle, Matrix.one_apply]
    have hcoords :
        (⟨(a, b), ((rightUnitorBasis X a).symm x', y'), i⟩ =
          (⟨(a, b), ((rightUnitorBasis X a).symm x, y), j⟩ :
            (tensorObj (tensorObj X (simple P N.unit)) Y).basis d)) ↔
          x' = x ∧ y' = y ∧ i = j := by
      constructor
      · intro hh
        have hdata := (Sigma.mk.inj_iff.mp hh).2.eq
        exact ⟨(rightUnitorBasis X a).symm.injective (congrArg (fun p ↦ p.1.1) hdata),
          congrArg (fun p ↦ p.1.2) hdata, congrArg Prod.snd hdata⟩
      · rintro ⟨rfl, rfl, rfl⟩
        rfl
    -- The permutation entry tests equality in the dependent tensor basis.
    erw [if_congr hcoords (rfl : (1 : R) = 1) (rfl : (0 : R) = 0)]
    split_ifs <;> simp only [mul_zero, mul_one] <;> grind
  · have hab' : (a, N.unit, b) ≠ (a', N.unit, b') := by simpa using hab
    rw [blockDiagonal'_apply_ne _ _ _ hab']
    split_ifs with hc
    · exact (hab (congrArg Sigma.fst hc).symm).elim
    · rfl

private theorem triangle_inv :
    tensorHom (𝟙 X) (leftUnitor Y).inv ≫ (associator X (simple P N.unit) Y).inv =
      tensorHom (rightUnitor X).inv (𝟙 Y) := by
  rw [associator_unit_inv, leftUnitor, rightUnitor, ← Iso.symm_hom, ← Iso.symm_hom,
    isoOfEquiv_symm, isoOfEquiv_symm, ← isoOfEquiv_refl_hom X, ← isoOfEquiv_refl_hom Y,
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
