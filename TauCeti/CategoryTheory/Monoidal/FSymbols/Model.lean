/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.PEquiv
public import TauCeti.CategoryTheory.Linear.SplitSimpleFamily
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Defs

/-!
# The model category of F-symbols

For F-symbols `P` over a commutative ring `R`, indexed by a finite set `ι` of simple objects, the
**model category** `TauCeti.FSymbols.Model P` is the category of `ι`-graded free `R`-modules of
finite rank with chosen bases. An object is a family of finite types `X.basis a`, one for each
grade `a : ι`, and a morphism `X ⟶ Y` is a family of matrices `X.basis a × Y.basis a → R`, one for
each grade, composed grade-wise by matrix multiplication. The object `Model.simple a` has a single
basis vector, in grade `a`.

This file sets up the linear structure of the model. The monoidal structure, whose associator is
read off from the F-matrices of `P`, is to be built on this category; that is why the category is
indexed by `P` although its morphisms do not depend on `P`.

## Main definitions and results

* `TauCeti.FSymbols.Model P`: the objects, with the category structure given by grade-wise matrix
  multiplication (`TauCeti.FSymbols.Model.comp_apply`).
* The model is preadditive and `R`-linear, has finite biproducts (the grade-wise disjoint union of
  bases, `TauCeti.FSymbols.Model.binaryBicone`), and is essentially small.
* `TauCeti.FSymbols.Model.finrank_hom`: over a nontrivial ring, `X ⟶ Y` is free of rank
  `∑ a, |X.basis a| * |Y.basis a|`.
* `TauCeti.FSymbols.Model.isoOfEquiv`: bijections of the bases in each grade give an isomorphism.
* `TauCeti.FSymbols.Model.simple a`: one basis vector, in grade `a`. Morphisms out of and into
  `simple a` are vectors indexed by the grade-`a` basis
  (`TauCeti.FSymbols.Model.simpleHomEquiv`, `TauCeti.FSymbols.Model.homSimpleEquiv`).
* `TauCeti.FSymbols.Model.isoBiproduct`: every object is the biproduct of copies of the simple
  objects, one for each of its basis vectors.
* `TauCeti.FSymbols.Model.isSplitSimpleFamily_simple`: the simple objects form a split simple
  family: their endomorphisms are the scalars, there are no nonzero morphisms between distinct
  ones, and every object is a finite biproduct of them.
* Over a nontrivial ring the simple objects are pairwise non-isomorphic
  (`TauCeti.FSymbols.Model.isEmpty_simple_iso`), while over the zero ring every morphism is `0`.

## Implementation notes

The basis of each grade is a type in the universe of `ι`, carrying `Fintype` and `DecidableEq`
instances, rather than an object of `FintypeCat`: the intended tensor product has basis
`Σ a b, X.basis a × Y.basis b × Fin N_{ab}^c` in grade `c`, and with the instances as data,
matrix products and identity matrices on such sums compute with their canonical instances.
Mathlib's `CategoryTheory.Mat R` would give one grade, but its objects live in the universe of
`R`, not of `ι`.

## References

* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics 321 (2006),
  Appendix E, Definition E.17: the category of graded vector spaces with chosen bases on which the
  monoidal structure defined by F-symbols lives.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

namespace FSymbols

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type v}

section CommSemiring

variable [CommSemiring R] {N : FusionRules ι}

/-- An object of the **model category** of F-symbols `P`: an `ι`-graded free module of finite
rank with a chosen basis, given by the finite basis set `basis a` of each grade `a`. Morphisms
are grade-wise matrices with entries in `R`. The morphisms do not depend on `P`; the index
records the F-symbols for the monoidal structure intended on this category. -/
structure Model (P : FSymbols R N) : Type (u + 1) where
  /-- The basis of the grade-`a` component. -/
  basis : ι → Type u
  /-- Each grade has a finite basis. -/
  [fintype : ∀ a, Fintype (basis a)]
  /-- The basis vectors of each grade have decidable equality. -/
  [decidableEq : ∀ a, DecidableEq (basis a)]

namespace Model

attribute [instance] fintype decidableEq

variable {P : FSymbols R N}

/-- Morphisms of the model are grade-wise matrices, composed by matrix multiplication. -/
instance : Category.{max u v} (Model P) where
  Hom X Y := ∀ a, Matrix (X.basis a) (Y.basis a) R
  id _ _ := 1
  comp f g a := f a * g a
  id_comp f := funext fun a ↦ Matrix.one_mul (f a)
  comp_id f := funext fun a ↦ Matrix.mul_one (f a)
  assoc f g h := funext fun a ↦ Matrix.mul_assoc (f a) (g a) (h a)

variable {X Y Z : Model P}

@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : ∀ a, f a = g a) : f = g :=
  funext h

/-- Equal morphisms have equal matrix entries. -/
theorem congr_apply {f g : X ⟶ Y} (h : f = g) (a : ι) (i : X.basis a) (j : Y.basis a) :
    f a i j = g a i j := by
  rw [h]

@[simp]
theorem id_apply (X : Model P) (a : ι) : (𝟙 X : X ⟶ X) a = 1 :=
  (rfl)

@[simp]
theorem comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : ι) : (f ≫ g) a = f a * g a :=
  (rfl)

/-- Bijections between the bases in each grade give an isomorphism, by permutation matrices. -/
def isoOfEquiv (e : ∀ a, X.basis a ≃ Y.basis a) : X ≅ Y where
  hom a := (e a).toPEquiv.toMatrix
  inv a := (e a).symm.toPEquiv.toMatrix
  hom_inv_id := by
    ext1 a
    simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  inv_hom_id := by
    ext1 a
    simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

@[simp]
theorem isoOfEquiv_hom_apply (e : ∀ a, X.basis a ≃ Y.basis a) (a : ι) :
    (isoOfEquiv e).hom a = (e a).toPEquiv.toMatrix :=
  (rfl)

@[simp]
theorem isoOfEquiv_inv_apply (e : ∀ a, X.basis a ≃ Y.basis a) (a : ι) :
    (isoOfEquiv e).inv a = (e a).symm.toPEquiv.toMatrix :=
  (rfl)

/-- Over the zero ring, every morphism of the model is `0`. -/
instance [Subsingleton R] (X Y : Model P) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs <| Subsingleton (∀ a, Matrix (X.basis a) (Y.basis a) R)

/-- The model category is essentially small: every object is isomorphic to one whose basis in
grade `a` is `Fin n` for some `n`. -/
instance : EssentiallySmall.{max u v} (Model P) := by
  refine (essentiallySmall_iff _).2 ⟨?_, inferInstance⟩
  let std (n : ι → ℕ) : Model P := ⟨fun a ↦ ULift (Fin (n a))⟩
  have : Small.{u} (Skeleton (Model P)) :=
    small_of_surjective (f := fun n ↦ toSkeleton (std n)) fun X ↦ by
      refine ⟨fun a ↦ Fintype.card (((fromSkeleton _).obj X).basis a),
        toSkeleton_eq_iff.2 ⟨isoOfEquiv fun a ↦ ?_⟩⟩
      exact Equiv.ulift.trans (Fintype.equivFin _).symm
  exact small_lift _

end Model

end CommSemiring

section CommRing

variable [CommRing R] {N : FusionRules ι} {P : FSymbols R N}

namespace Model

variable {X Y Z : Model P}

instance (X Y : Model P) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs <| AddCommGroup (∀ a, Matrix (X.basis a) (Y.basis a) R)

instance (X Y : Model P) : Module R (X ⟶ Y) :=
  inferInstanceAs <| Module R (∀ a, Matrix (X.basis a) (Y.basis a) R)

@[simp]
theorem zero_apply (X Y : Model P) (a : ι) : (0 : X ⟶ Y) a = 0 :=
  (rfl)

@[simp]
theorem add_apply (f g : X ⟶ Y) (a : ι) : (f + g) a = f a + g a :=
  (rfl)

@[simp]
theorem neg_apply (f : X ⟶ Y) (a : ι) : (-f) a = -f a :=
  (rfl)

@[simp]
theorem sub_apply (f g : X ⟶ Y) (a : ι) : (f - g) a = f a - g a :=
  (rfl)

@[simp]
theorem smul_apply (r : R) (f : X ⟶ Y) (a : ι) : (r • f) a = r • f a :=
  (rfl)

/-- The model category is preadditive, with grade-wise addition of matrices. -/
instance : Preadditive (Model P) where
  add_comp _ _ _ f f' g := funext fun a ↦ Matrix.add_mul (f a) (f' a) (g a)
  comp_add _ _ _ f g g' := funext fun a ↦ Matrix.mul_add (f a) (g a) (g' a)

/-- The model category is `R`-linear, with grade-wise scalar multiplication of matrices. -/
instance : Linear R (Model P) where
  smul_comp _ _ _ r f g := funext fun a ↦ Matrix.smul_mul r (f a) (g a)
  comp_smul _ _ _ f r g := funext fun a ↦ Matrix.mul_smul (f a) r (g a)

@[simp]
theorem sum_apply {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ Y)) (a : ι) :
    (∑ k ∈ s, f k) a = ∑ k ∈ s, f k a :=
  Finset.sum_apply a s f

/-- The scalar endomorphism `r` of `X` is `r` times the identity matrix in each grade. -/
@[simp]
theorem algebraMap_asHom_apply (X : Model P) (r : R) (a : ι) :
    (algebraMap R (End X) r).asHom a = r • 1 := by
  rw [Algebra.algebraMap_eq_smul_one, End.smul_asHom, End.one_asHom, smul_apply, id_apply]

instance (X Y : Model P) : Module.Free R (X ⟶ Y) :=
  inferInstanceAs <| Module.Free R (∀ a, Matrix (X.basis a) (Y.basis a) R)

instance (X Y : Model P) : Module.Finite R (X ⟶ Y) :=
  inferInstanceAs <| Module.Finite R (∀ a, Matrix (X.basis a) (Y.basis a) R)

/-- Over a nontrivial ring, the morphisms `X ⟶ Y` form a free module whose rank is
`∑ a, |X.basis a| * |Y.basis a|`. -/
theorem finrank_hom [Nontrivial R] (X Y : Model P) :
    Module.finrank R (X ⟶ Y) = ∑ a, Fintype.card (X.basis a) * Fintype.card (Y.basis a) := by
  have h := Module.finrank_pi_fintype R (M := fun a ↦ Matrix (X.basis a) (Y.basis a) R)
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one] at h
  -- `X ⟶ Y` is by definition the product of the grade-wise matrix modules
  exact h

/-- An object without basis vectors is a zero object. -/
theorem isZero_of_isEmpty (X : Model P) [∀ a, IsEmpty (X.basis a)] : IsZero X :=
  (IsZero.iff_id_eq_zero X).2 <| by
    ext a i
    exact isEmptyElim i

/-- Over a nontrivial ring, an object is a zero object exactly when it has no basis vectors. -/
theorem isZero_iff [Nontrivial R] (X : Model P) : IsZero X ↔ ∀ a, IsEmpty (X.basis a) := by
  refine ⟨fun h a ↦ ⟨fun i ↦ ?_⟩, fun h ↦ isZero_of_isEmpty X⟩
  simpa using congr_apply (h.eq_of_src (𝟙 X) 0) a i i

instance : HasZeroObject (Model P) :=
  ⟨⟨⟨fun _ ↦ PEmpty⟩, isZero_of_isEmpty _⟩⟩

/-- The binary biproduct of `X` and `Y`: in each grade, the disjoint union of the bases, with
inclusions and projections the block matrices of the identity. Its body is exposed because the
statements of `TauCeti.FSymbols.Model.binaryBicone_fst_apply` and its siblings need the basis of
the cone point to unfold to a sum type. -/
@[expose]
def binaryBicone (X Y : Model P) : BinaryBicone X Y where
  pt := ⟨fun a ↦ X.basis a ⊕ Y.basis a⟩
  fst _ := Matrix.fromRows 1 0
  snd _ := Matrix.fromRows 0 1
  inl _ := Matrix.fromCols 1 0
  inr _ := Matrix.fromCols 0 1
  inl_fst := by ext1; simp [Matrix.fromCols_mul_fromRows]
  inl_snd := by ext1; simp [Matrix.fromCols_mul_fromRows]
  inr_fst := by ext1; simp [Matrix.fromCols_mul_fromRows]
  inr_snd := by ext1; simp [Matrix.fromCols_mul_fromRows]

@[simp]
theorem binaryBicone_pt_basis (X Y : Model P) (a : ι) :
    (binaryBicone X Y).pt.basis a = (X.basis a ⊕ Y.basis a) :=
  (rfl)

@[simp]
theorem binaryBicone_fst_apply (X Y : Model P) (a : ι) :
    (binaryBicone X Y).fst a = Matrix.fromRows (1 : Matrix (X.basis a) (X.basis a) R) 0 :=
  (rfl)

@[simp]
theorem binaryBicone_snd_apply (X Y : Model P) (a : ι) :
    (binaryBicone X Y).snd a = Matrix.fromRows (0 : Matrix (X.basis a) (Y.basis a) R) 1 :=
  (rfl)

@[simp]
theorem binaryBicone_inl_apply (X Y : Model P) (a : ι) :
    (binaryBicone X Y).inl a = Matrix.fromCols (1 : Matrix (X.basis a) (X.basis a) R) 0 :=
  (rfl)

@[simp]
theorem binaryBicone_inr_apply (X Y : Model P) (a : ι) :
    (binaryBicone X Y).inr a = Matrix.fromCols (0 : Matrix (Y.basis a) (X.basis a) R) 1 :=
  (rfl)

/-- `TauCeti.FSymbols.Model.binaryBicone` is a biproduct. -/
def binaryBiconeIsBilimit (X Y : Model P) : (binaryBicone X Y).IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
    ext1 a
    have : Matrix.fromRows (1 : Matrix (X.basis a) (X.basis a) R) 0 *
          Matrix.fromCols (1 : Matrix (X.basis a) (X.basis a) R) 0 +
        Matrix.fromRows (0 : Matrix (X.basis a) (Y.basis a) R) (1 : Matrix (Y.basis a) _ R) *
          Matrix.fromCols (0 : Matrix (Y.basis a) (X.basis a) R) (1 : Matrix _ (Y.basis a) R) =
        1 := by
      rw [Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add]
      simp
    -- after unfolding `binaryBicone`, the goal is this identity of block matrices
    exact this

instance : HasBinaryBiproducts (Model P) :=
  ⟨fun X Y ↦ ⟨⟨⟨binaryBicone X Y, binaryBiconeIsBilimit X Y⟩⟩⟩⟩

instance : HasFiniteBiproducts (Model P) :=
  have : HasFiniteProducts (Model P) := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

end Model

end CommRing

namespace Model

section CommSemiring

variable [CommSemiring R] {N : FusionRules ι} {P : FSymbols R N}

variable (P) in
/-- The **simple object** `simple a` of the model: a single basis vector, in grade `a`. -/
def simple (a : ι) : Model P :=
  ⟨fun b ↦ {_x : PUnit.{u + 1} // b = a}⟩

@[no_expose]
instance (a : ι) : Unique ((simple P a).basis a) where
  default := ⟨PUnit.unit, rfl⟩
  uniq _ := Subtype.ext rfl

/-- The basis vectors of `simple a` all lie in grade `a`. -/
theorem eq_of_simple_basis {a b : ι} (i : (simple P a).basis b) : b = a :=
  i.property

/-- `simple a` has no basis vectors outside grade `a`. -/
theorem isEmpty_simple_basis {a b : ι} (h : b ≠ a) : IsEmpty ((simple P a).basis b) :=
  ⟨fun i ↦ h (eq_of_simple_basis i)⟩

variable {X : Model P}

/-- The inclusion of the simple summand of `X` spanned by a basis vector `p` of grade `p.1`. -/
def incl (X : Model P) (p : Σ a, X.basis a) : simple P p.1 ⟶ X :=
  fun c _ y ↦ if (⟨c, y⟩ : Σ a, X.basis a) = p then 1 else 0

/-- The projection of `X` onto the simple summand spanned by a basis vector `p` of grade `p.1`,
taking the `p`-th coordinate. -/
def proj (X : Model P) (p : Σ a, X.basis a) : X ⟶ simple P p.1 :=
  fun c y _ ↦ if (⟨c, y⟩ : Σ a, X.basis a) = p then 1 else 0

theorem incl_apply (p : Σ a, X.basis a) (c : ι) (i : (simple P p.1).basis c) (y : X.basis c) :
    incl X p c i y = if (⟨c, y⟩ : Σ a, X.basis a) = p then 1 else 0 :=
  (rfl)

theorem proj_apply (p : Σ a, X.basis a) (c : ι) (y : X.basis c) (i : (simple P p.1).basis c) :
    proj X p c y i = if (⟨c, y⟩ : Σ a, X.basis a) = p then 1 else 0 :=
  (rfl)

/-- The projection onto the summand spanned by a basis vector is a retraction of its inclusion. -/
@[simp]
theorem incl_comp_proj (p : Σ a, X.basis a) : incl X p ≫ proj X p = 𝟙 _ := by
  obtain ⟨a, x⟩ := p
  ext c i j
  obtain rfl := eq_of_simple_basis i
  rw [Subsingleton.elim i j]
  simp [incl_apply, proj_apply, Matrix.mul_apply]

end CommSemiring

section CommRing

variable [CommRing R] {N : FusionRules ι} {P : FSymbols R N}

variable {X : Model P}

/-- The summands spanned by distinct basis vectors are orthogonal. -/
theorem incl_comp_proj_of_ne {p q : Σ a, X.basis a} (h : p ≠ q) :
    incl X p ≫ proj X q = 0 := by
  ext c i j
  simp only [comp_apply, Matrix.mul_apply, incl_apply, proj_apply, zero_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  split_ifs with h₁ h₂ <;> simp_all

/-- The idempotents projecting onto the summands spanned by the basis vectors sum to the
identity. -/
theorem sum_proj_comp_incl (X : Model P) : ∑ p, proj X p ≫ incl X p = 𝟙 X := by
  ext c y y'
  simp only [sum_apply, comp_apply, Matrix.sum_apply, Matrix.mul_apply, proj_apply, incl_apply,
    id_apply, Matrix.one_apply]
  rw [Fintype.sum_eq_single ⟨c, y⟩ fun p hp ↦ Finset.sum_eq_zero fun _ _ ↦ by simp [Ne.symm hp]]
  simp [eq_comm]

/-- Every object of the model is the biproduct of copies of the simple objects, one for each of its
basis vectors, with components the projections `TauCeti.FSymbols.Model.proj` and inclusions
`TauCeti.FSymbols.Model.incl`. -/
def isoBiproduct (X : Model P) : X ≅ ⨁ fun p : Σ a, X.basis a ↦ simple P p.1 where
  hom := biproduct.lift (proj X)
  inv := biproduct.desc (incl X)
  hom_inv_id := by rw [biproduct.lift_desc, sum_proj_comp_incl]
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun p ↦ biproduct.hom_ext _ _ fun q ↦ ?_
    by_cases h : p = q
    · subst h
      simp
    · simp [biproduct.ι_π_ne _ h, incl_comp_proj_of_ne h]

@[simp]
theorem isoBiproduct_hom (X : Model P) : X.isoBiproduct.hom = biproduct.lift (proj X) :=
  (rfl)

@[simp]
theorem isoBiproduct_inv (X : Model P) : X.isoBiproduct.inv = biproduct.desc (incl X) :=
  (rfl)

/-- Morphisms out of `simple a` are vectors indexed by the grade-`a` basis of the target. -/
def simpleHomEquiv (X : Model P) (a : ι) : (simple P a ⟶ X) ≃ₗ[R] (X.basis a → R) where
  toFun f := f a default
  invFun v b i := cast (congrArg (fun c ↦ X.basis c → R) (eq_of_simple_basis i).symm) v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    ext b i
    obtain rfl := eq_of_simple_basis i
    rfl
  right_inv _ := rfl

/-- Morphisms into `simple a` are vectors indexed by the grade-`a` basis of the source. -/
def homSimpleEquiv (X : Model P) (a : ι) : (X ⟶ simple P a) ≃ₗ[R] (X.basis a → R) where
  toFun f x := f a x default
  invFun v b x i := cast (congrArg (fun c ↦ X.basis c → R) (eq_of_simple_basis i).symm) v x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    ext b x i
    obtain rfl := eq_of_simple_basis i
    rfl
  right_inv _ := rfl

@[simp]
theorem simpleHomEquiv_apply (a : ι) (f : simple P a ⟶ X) :
    simpleHomEquiv X a f = f a default :=
  (rfl)

@[simp]
theorem homSimpleEquiv_apply (a : ι) (f : X ⟶ simple P a) (x : X.basis a) :
    homSimpleEquiv X a f x = f a x default :=
  (rfl)

@[simp]
theorem simpleHomEquiv_symm_apply (a : ι) (v : X.basis a → R) (i : (simple P a).basis a) :
    (simpleHomEquiv X a).symm v a i = v :=
  (rfl)

@[simp]
theorem homSimpleEquiv_symm_apply (a : ι) (v : X.basis a → R) (x : X.basis a)
    (i : (simple P a).basis a) : (homSimpleEquiv X a).symm v a x i = v x :=
  (rfl)

/-- The endomorphisms of `simple a` are the scalars. -/
theorem bijective_algebraMap_simple (a : ι) :
    Function.Bijective (algebraMap R (End (simple P a))) := by
  refine ⟨fun r s h ↦ ?_, fun e ↦ ⟨e.asHom a default default, End.ext ?_⟩⟩
  · simpa using congr_apply (congrArg End.asHom h) a default default
  · ext c i j
    obtain rfl := eq_of_simple_basis i
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp

/-- There are no nonzero morphisms between distinct simple objects. -/
theorem homOrthogonal_simple : HomOrthogonal (simple P) := fun a b hab ↦
  ⟨fun f g ↦ by
    ext c i j
    exact absurd ((eq_of_simple_basis i).symm.trans (eq_of_simple_basis j)) hab⟩

/-- Over a nontrivial ring, distinct simple objects are not isomorphic. -/
theorem isEmpty_simple_iso [Nontrivial R] {a b : ι} (hab : a ≠ b) :
    IsEmpty (simple P a ≅ simple P b) := by
  refine ⟨fun e ↦ ?_⟩
  have := (homOrthogonal_simple hab).elim e.hom 0
  simpa [this] using congr_apply e.hom_inv_id a default default

/-- The simple objects of the model form a split simple family: each has endomorphisms the
scalars, there are no nonzero morphisms between distinct ones, and every object is a finite
biproduct of them. -/
theorem isSplitSimpleFamily_simple : IsSplitSimpleFamily R (simple P) where
  bijective_algebraMap := bijective_algebraMap_simple
  homOrthogonal := homOrthogonal_simple
  exists_iso_biproduct X := by
    let e := (Fintype.equivFin (Σ a, X.basis a)).symm
    exact ⟨_, inferInstance, fun k ↦ (e k).1,
      ⟨X.isoBiproduct ≪≫ (biproduct.whiskerEquiv e fun _ ↦ Iso.refl _).symm⟩⟩

end CommRing

end Model

end FSymbols

end TauCeti
