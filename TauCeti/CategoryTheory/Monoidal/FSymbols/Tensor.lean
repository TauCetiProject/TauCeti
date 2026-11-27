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

/-- The basis in an output grade is indexed by the input grades, basis vectors and
fusion channel. -/
@[simp]
theorem tensorObj_basis (X Y : Model P) (c : ι) :
    (tensorObj X Y).basis c = Σ ab : ι × ι, (X.basis ab.1 × Y.basis ab.2) × Fin (N.N ab.1 ab.2 c) :=
  (rfl)

variable {X X' X'' Y Y' Y'' : Model P}

/-- A tensor product basis vector with the given input grades, basis vectors and
fusion channel. -/
abbrev tensorBasisMk {c : ι} (ab : ι × ι) (x : X.basis ab.1) (y : Y.basis ab.2)
    (i : Fin (N.N ab.1 ab.2 c)) : (tensorObj X Y).basis c :=
  ⟨ab, (x, y), i⟩

private theorem tensorBasisMk_exists {c : ι} (p : (tensorObj X Y).basis c) :
    ∃ ab x y i, p = tensorBasisMk ab x y i := by
  obtain ⟨ab, ⟨x, y⟩, i⟩ := p
  exact ⟨ab, x, y, i, rfl⟩

/-- In fixed input grades, two tensor basis vectors agree exactly when their basis
vectors and fusion channels agree. -/
@[simp]
theorem tensorBasisMk_inj {c : ι} {ab : ι × ι} {x x' : X.basis ab.1} {y y' : Y.basis ab.2}
    {i j : Fin (N.N ab.1 ab.2 c)} :
    tensorBasisMk ab x y i = tensorBasisMk (X := X) (Y := Y) ab x' y' j ↔
      x = x' ∧ y = y' ∧ i = j := by
  constructor
  · intro h
    have hdata : ((x, y), i) = ((x', y'), j) :=
      sigma_mk_injective (β := fun ab : ι × ι ↦
        (X.basis ab.1 × Y.basis ab.2) × Fin (N.N ab.1 ab.2 c)) h
    obtain ⟨hxy, hij⟩ := Prod.mk.inj hdata
    exact ⟨(Prod.mk.inj hxy).1, (Prod.mk.inj hxy).2, hij⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem tensorBasisMk_ne_of_ne {c : ι} {ab ab' : ι × ι}
    {x : X.basis ab.1} {x' : X.basis ab'.1} {y : Y.basis ab.2} {y' : Y.basis ab'.2}
    {i : Fin (N.N ab.1 ab.2 c)} {j : Fin (N.N ab'.1 ab'.2 c)} (h : ab ≠ ab') :
    tensorBasisMk ab x y i ≠ tensorBasisMk (X := X) (Y := Y) ab' x' y' j :=
  fun he ↦ h (congrArg Sigma.fst he)

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
    tensorHom f g c (tensorBasisMk (a, b) x y i) (tensorBasisMk (a, b) x' y' j) =
      f a x x' * g b y y' * (1 : Matrix (Fin (N.N a b c)) _ R) i j :=
  blockDiagonal'_apply_eq _ _ _ _

/-- A tensor product of maps has zero entries between different pairs of input grades. -/
theorem tensorHom_apply_of_ne (f : X ⟶ X') (g : Y ⟶ Y') {ab ab' : ι × ι}
    (h : ab ≠ ab') (c : ι) (x : X.basis ab.1) (y : Y.basis ab.2)
    (x' : X'.basis ab'.1) (y' : Y'.basis ab'.2)
    (i : Fin (N.N ab.1 ab.2 c)) (j : Fin (N.N ab'.1 ab'.2 c)) :
    tensorHom f g c (tensorBasisMk ab x y i) (tensorBasisMk ab' x' y' j) = 0 :=
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
theorem add_tensorHom (f f' : A ⟶ A') (g : B ⟶ B') :
    tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  ext1 c
  simp only [tensorHom, add_apply, add_kronecker]
  exact blockDiagonal'_add _ _

/-- Tensoring is additive in its second map. -/
@[simp]
theorem tensorHom_add (f : A ⟶ A') (g g' : B ⟶ B') :
    tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  ext1 c
  simp only [tensorHom, add_apply, kronecker_add, add_kronecker]
  exact blockDiagonal'_add _ _

/-- Tensoring is homogeneous in its first map. -/
@[simp]
theorem smul_tensorHom (r : K) (f : A ⟶ A') (g : B ⟶ B') :
    tensorHom (r • f) g = r • tensorHom f g := by
  ext1 c
  simp only [tensorHom, smul_apply, smul_kronecker]
  exact blockDiagonal'_smul (α := K) r _

/-- Tensoring is homogeneous in its second map. -/
@[simp]
theorem tensorHom_smul (r : K) (f : A ⟶ A') (g : B ⟶ B') :
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
    tensorBasisCongr e e' c (tensorBasisMk (a, b) x y i) =
      tensorBasisMk (a, b) (e a x) (e' b y) i :=
  (rfl)

/-- Inverting the tensor basis bijection inverts each factor's bijection. -/
@[simp]
theorem tensorBasisCongr_symm (e : ∀ a, X.basis a ≃ X'.basis a)
    (e' : ∀ b, Y.basis b ≃ Y'.basis b) (c : ι) :
    (tensorBasisCongr e e' c).symm =
      tensorBasisCongr (fun a ↦ (e a).symm) (fun b ↦ (e' b).symm) c :=
  (rfl)

/-- Composing tensor basis bijections composes the bijections in each factor. -/
@[simp]
theorem tensorBasisCongr_trans (e : ∀ a, X.basis a ≃ X'.basis a)
    (e' : ∀ b, Y.basis b ≃ Y'.basis b) (f : ∀ a, X'.basis a ≃ X''.basis a)
    (f' : ∀ b, Y'.basis b ≃ Y''.basis b) (c : ι) :
    (tensorBasisCongr e e' c).trans (tensorBasisCongr f f' c) =
      tensorBasisCongr (fun a ↦ (e a).trans (f a)) (fun b ↦ (e' b).trans (f' b)) c :=
  (rfl)

/-- Tensoring permutation matrices gives the permutation matrix of the tensor basis bijection. -/
theorem tensorHom_isoOfEquiv_hom (e : ∀ a, X.basis a ≃ X'.basis a)
    (e' : ∀ b, Y.basis b ≃ Y'.basis b) :
    tensorHom (isoOfEquiv e).hom (isoOfEquiv e').hom =
      (isoOfEquiv (tensorBasisCongr e e')).hom := by
  ext1 c
  apply Matrix.ext
  intro p q
  obtain ⟨⟨a, b⟩, x, y, i, rfl⟩ := tensorBasisMk_exists p
  obtain ⟨⟨a', b'⟩, x', y', j, rfl⟩ := tensorBasisMk_exists q
  rw [isoOfEquiv_hom_entry, tensorBasisCongr_apply]
  by_cases hab : (a, b) = (a', b')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    rw [tensorHom_apply, isoOfEquiv_hom_entry, isoOfEquiv_hom_entry]
    simp only [tensorBasisMk_inj, Matrix.one_apply, eq_comm (a := i) (b := j), ite_and,
      ite_mul, zero_mul, one_mul]
  · rw [tensorHom_apply_of_ne _ _ hab, ite_eq_right (tensorBasisMk_ne_of_ne (Ne.symm hab))]

omit [Fintype ι] [DecidableEq ι] in
private theorem eq_of_fusion_index {a b c k : ι} (i : Fin (N.N a b c))
    (h : k ≠ c → N.N a b c = 0) : k = c := by
  classical
  by_contra hk
  simpa [h hk] using i.isLt

/-- The left unitor on graded bases. Its inverse inserts the unique unit vector and fusion
index. -/
def leftUnitorBasis (X : Model P) (c : ι) :
    (tensorObj (simple P N.unit) X).basis c ≃ X.basis c :=
  (Equiv.ofBijective (fun x ↦ tensorBasisMk (N.unit, c) default x (N.unitLeft c)) (by
    constructor
    · intro x y h
      exact (tensorBasisMk_inj.mp h).2.1
    · rintro ⟨⟨a, b⟩, ⟨i, x⟩, j⟩
      obtain rfl := eq_of_simple_basis i
      have hb := eq_of_fusion_index j (N.N_unit_left_of_ne b c)
      subst b
      exact ⟨x, by rw [Subsingleton.elim i default, Subsingleton.elim j (N.unitLeft c)]⟩)).symm

/-- The right unitor on graded bases. Its inverse inserts the unique unit vector and fusion
index. -/
def rightUnitorBasis (X : Model P) (c : ι) :
    (tensorObj X (simple P N.unit)).basis c ≃ X.basis c :=
  (Equiv.ofBijective (fun x ↦ tensorBasisMk (c, N.unit) x default (N.unitRight c)) (by
    constructor
    · intro x y h
      exact (tensorBasisMk_inj.mp h).1
    · rintro ⟨⟨a, b⟩, ⟨x, i⟩, j⟩
      obtain rfl := eq_of_simple_basis i
      have ha := eq_of_fusion_index j (N.N_unit_right_of_ne a c)
      subst a
      exact ⟨x, by rw [Subsingleton.elim i default, Subsingleton.elim j (N.unitRight c)]⟩)).symm

/-- The inverse left unitor on a basis vector. -/
@[simp]
theorem leftUnitorBasis_symm_apply (X : Model P) (c : ι) (x : X.basis c) :
    (leftUnitorBasis X c).symm x = tensorBasisMk (N.unit, c) default x (N.unitLeft c) :=
  (rfl)

/-- The inverse right unitor on a basis vector. -/
@[simp]
theorem rightUnitorBasis_symm_apply (X : Model P) (c : ι) (x : X.basis c) :
    (rightUnitorBasis X c).symm x = tensorBasisMk (c, N.unit) x default (N.unitRight c) :=
  (rfl)

/-- The left unitor removes the unit vector and fusion index from a tensor basis vector. -/
@[simp]
theorem leftUnitorBasis_apply (X : Model P) (c : ι) (x : X.basis c)
    (i : (simple P N.unit).basis N.unit) (j : Fin (N.N N.unit c c)) :
    leftUnitorBasis X c (tensorBasisMk (N.unit, c) i x j) = x := by
  rw [Subsingleton.elim i default, Subsingleton.elim j (N.unitLeft c),
    ← leftUnitorBasis_symm_apply, Equiv.apply_symm_apply]

/-- The right unitor removes the unit vector and fusion index from a tensor basis vector. -/
@[simp]
theorem rightUnitorBasis_apply (X : Model P) (c : ι) (x : X.basis c)
    (i : (simple P N.unit).basis N.unit) (j : Fin (N.N c N.unit c)) :
    rightUnitorBasis X c (tensorBasisMk (c, N.unit) x i j) = x := by
  rw [Subsingleton.elim i default, Subsingleton.elim j (N.unitRight c),
    ← rightUnitorBasis_symm_apply, Equiv.apply_symm_apply]

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
theorem leftAssocBasisEquiv_symm_apply (X Y Z : Model P) (d : ι)
    (p : Σ abc : ι × ι × ι, (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) ×
      N.Left abc.1 abc.2.1 abc.2.2 d) :
    (leftAssocBasisEquiv X Y Z d).symm p =
      tensorBasisMk (p.2.2.1, p.1.2.2)
        (tensorBasisMk (p.1.1, p.1.2.1) p.2.1.1 p.2.1.2.1 p.2.2.2.1) p.2.1.2.2 p.2.2.2.2 :=
  (rfl)

/-- In the right-associated tensor product, the two fusion indices form the right index of
an F-matrix. -/
@[simp]
theorem rightAssocBasisEquiv_symm_apply (X Y Z : Model P) (d : ι)
    (p : Σ abc : ι × ι × ι, (X.basis abc.1 × Y.basis abc.2.1 × Z.basis abc.2.2) ×
      N.Right abc.1 abc.2.1 abc.2.2 d) :
    (rightAssocBasisEquiv X Y Z d).symm p =
      tensorBasisMk (p.1.1, p.2.2.1) p.2.1.1
        (tensorBasisMk (p.1.2.1, p.1.2.2) p.2.1.2.1 p.2.1.2.2 p.2.2.2.1) p.2.2.2.2 :=
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
  simp only [associator, Matrix.submatrix_apply, Equiv.apply_symm_apply]

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
  simp only [associator, Matrix.submatrix_apply, Equiv.apply_symm_apply]

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
  constructor <;> apply Matrix.ext <;>
    rintro ⟨⟨a, b, c⟩, ⟨x, y, z⟩, ⟨e, i, j⟩⟩ ⟨⟨a', b', c'⟩, ⟨x', y', z'⟩, ⟨e', i', j'⟩⟩
  all_goals
    simp only [Matrix.submatrix_apply, leftAssocBasisEquiv_symm_apply,
      rightAssocBasisEquiv_symm_apply]
    by_cases habc : (a, b, c) = (a', b', c')
    · obtain ⟨rfl, hbc⟩ := Prod.mk.inj habc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbc
      rw [blockDiagonal'_apply_eq, kronecker_apply]
      -- In this block only the two fusion indices can make the identity factor vanish.
      by_cases he : e = e'
      · subst e'
        rw [tensorHom_apply, tensorHom_apply]
        simp only [tripleTensorBlock, kronecker_apply, Matrix.one_apply]
        by_cases hi : i = i' <;> by_cases hj : j = j' <;>
          simp [hi, hj, mul_assoc]
      · rw [tensorHom_apply_of_ne _ _ (by simp [he]), Matrix.one_apply]
        split_ifs with hEq
        · exact (he (congrArg Sigma.fst hEq)).elim
        · rw [mul_zero]
    · rw [blockDiagonal'_apply_ne _ _ _ habc]
      -- If the outer input grades agree, the inner pair of input grades must differ.
      first
      | by_cases hec : (e, c) = (e', c')
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hec
          have hab : (a, b) ≠ (a', b') := by simpa using habc
          rw [tensorHom_apply, tensorHom_apply_of_ne _ _ hab, zero_mul, zero_mul]
        · exact tensorHom_apply_of_ne _ _ hec _ _ _ _ _ _ _
      | by_cases hae : (a, e) = (a', e')
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hae
          have hbc : (b, c) ≠ (b', c') := by simpa using habc
          rw [tensorHom_apply, tensorHom_apply_of_ne _ _ hbc, mul_zero, zero_mul]
        · exact tensorHom_apply_of_ne _ _ hae _ _ _ _ _ _ _

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
    triangleBasis X Y d (tensorBasisMk (a, b) x ((leftUnitorBasis Y b).symm y) j) =
      tensorBasisMk (a, b) ((rightUnitorBasis X a).symm x) y j := by
  simp only [triangleBasis, Equiv.trans_apply, tensorBasisCongr_apply, Equiv.refl_apply,
    Equiv.apply_symm_apply]

private theorem associator_unit_inv :
    (associator X (simple P N.unit) Y).inv = (isoOfEquiv (triangleBasis X Y)).hom := by
  ext1 d
  apply Matrix.submatrix_injective
    (tensorBasisCongr (fun _ ↦ Equiv.refl _) (leftUnitorBasis Y) d).symm.surjective
    (tensorBasisCongr (fun a ↦ (rightUnitorBasis X a).symm) (fun _ ↦ Equiv.refl _) d).surjective
  dsimp only
  apply Matrix.ext
  intro p q
  obtain ⟨⟨a, b⟩, x, y, j, rfl⟩ := tensorBasisMk_exists p
  obtain ⟨⟨a', b'⟩, x', y', i, rfl⟩ := tensorBasisMk_exists q
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply, tensorBasisCongr_symm]
  simp only [Equiv.refl_symm, tensorBasisCongr_apply, Equiv.refl_apply, isoOfEquiv_hom_entry,
    triangleBasis_apply]
  simp only [leftUnitorBasis_symm_apply, rightUnitorBasis_symm_apply]
  have hAssoc := congrFun (congrFun (associator_inv_submatrix X (simple P N.unit) Y d)
    ⟨(a, N.unit, b), (x, default, y), ⟨b, N.unitLeft b, j⟩⟩)
    ⟨(a', N.unit, b'), (x', default, y'), ⟨a', N.unitRight a', i⟩⟩
  simp only [Matrix.submatrix_apply, rightAssocBasisEquiv_symm_apply,
    leftAssocBasisEquiv_symm_apply] at hAssoc
  rw [hAssoc]
  by_cases hab : (a, b) = (a', b')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
    rw [blockDiagonal'_apply_eq]
    simp only [kronecker_apply, transpose_apply, P.triangle, Matrix.one_apply, tensorBasisMk_inj,
      Prod.mk.injEq, and_true, true_and, eq_comm (a := x) (b := x'), eq_comm (a := y) (b := y'),
      ite_and, ite_mul, zero_mul, one_mul]
  · have hab' : (a, N.unit, b) ≠ (a', N.unit, b') := by simpa using hab
    rw [blockDiagonal'_apply_ne _ _ _ hab', ite_eq_right (tensorBasisMk_ne_of_ne (Ne.symm hab))]

private theorem triangle_inv :
    tensorHom (𝟙 X) (leftUnitor Y).inv ≫ (associator X (simple P N.unit) Y).inv =
      tensorHom (rightUnitor X).inv (𝟙 Y) := by
  rw [associator_unit_inv, leftUnitor, rightUnitor, ← Iso.symm_hom, ← Iso.symm_hom,
    isoOfEquiv_symm, isoOfEquiv_symm, ← isoOfEquiv_refl_hom X, ← isoOfEquiv_refl_hom Y,
    tensorHom_isoOfEquiv_hom, tensorHom_isoOfEquiv_hom, ← Iso.trans_hom, isoOfEquiv_trans]
  simp only [triangleBasis, tensorBasisCongr_trans, Equiv.refl_trans, Equiv.trans_refl,
    Equiv.symm_trans_self]

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
