/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.CategoryTheory.Preadditive.Mat
public import TauCeti.CategoryTheory.Dagger.Basic
public import TauCeti.CategoryTheory.Linear.Mat
public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# Algebraic finite linking algebras of dagger linear categories

Given a finite family of objects `X : ι → C` (in particular `L.get : Fin L.length → C` for a list
`L : List C`), the finite linking algebra `TauCeti.LinkingAlgebra X` is defined as a type synonym
of `CategoryTheory.End (Mat_.mk ι X)`. Indexing entries in operator order via
`A.entry i j := End.asHom A j i : X j ⟶ X i`, multiplication in `End (Mat_.mk ι X)` gives
operator-order matrix multiplication `(A * B).entry i k = ∑ j, B.entry j k ≫ A.entry i j`, while
the dagger structure equips `LinkingAlgebra X` with the conjugate-transpose involution
`(star A).entry i j = dagger (A.entry j i)`.

This file establishes the algebraic ring, module, algebra, and star-ring structures on
`TauCeti.LinkingAlgebra X`, together with the bundled algebra equivalence
`LinkingAlgebra.endMatAlgEquiv`, matrix units `LinkingAlgebra.single`, diagonal corner projections
`LinkingAlgebra.proj`, non-unital star-algebra diagonal embeddings `LinkingAlgebra.diagHom`, and
corner membership `LinkingAlgebra.mem_cornerSubmodule` for `TauCeti.cornerSubmodule`. For the
C*-algebra norm, GNS representations, isometric corner identifications, and matrix positivity
criterion on C*-categories, see `TauCeti.Analysis.CStarAlgebra.Category.LinkingAlgebra.CStar`.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109,
  Section 1.
-/

public section

noncomputable section

open CategoryTheory

universe r v u

namespace TauCeti

/-- The finite linking algebra associated to a family of objects `X : ι → C`, defined as a type
synonym of `CategoryTheory.End (Mat_.mk ι X)`. Its `(i, j)` matrix entry `A.entry i j` is a
morphism `X j ⟶ X i`, equipped with operator-order matrix multiplication and (in a dagger
category) conjugate-transpose involution. -/
def LinkingAlgebra {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type} [Fintype ι] (X : ι → C) : Type v :=
  End (Mat_.mk ι X)

namespace LinkingAlgebra

/-! ### Conjugate-transpose star, ring, and algebra structures -/

section Basic

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} [Fintype ι] {X : ι → C}

/-- The `(i, j)` matrix entry of an element of `LinkingAlgebra X`, a morphism `X j ⟶ X i`. -/
def entry (A : LinkingAlgebra X) (i j : ι) : X j ⟶ X i :=
  End.asHom A j i

/-- Construct an element of `LinkingAlgebra X` from its matrix of entries
`f i j : X j ⟶ X i`. -/
def ofEntry (f : (i j : ι) → (X j ⟶ X i)) : LinkingAlgebra X :=
  End.of (X := Mat_.mk ι X) fun j i => f i j

@[simp] theorem ofEntry_entry (f : (i j : ι) → (X j ⟶ X i)) (i j : ι) :
    (ofEntry f).entry i j = f i j := (rfl)

@[ext] theorem ext {A B : LinkingAlgebra X} (h : ∀ i j, A.entry i j = B.entry i j) : A = B :=
  End.ext (Mat_.hom_ext _ _ fun j i => h i j)

@[simp] theorem ofEntry_self (A : LinkingAlgebra X) : ofEntry A.entry = A := by
  ext i j; rfl

/-- The ring structure on `LinkingAlgebra X`, inherited from `End (Mat_.mk ι X)`. -/
instance instRing : Ring (LinkingAlgebra X) :=
  inferInstanceAs (Ring (End (Mat_.mk ι X)))

@[simp] theorem zero_entry (i j : ι) : (0 : LinkingAlgebra X).entry i j = 0 := (rfl)
@[simp] theorem add_entry (A B : LinkingAlgebra X) (i j : ι) :
    (A + B).entry i j = A.entry i j + B.entry i j := (rfl)
@[simp] theorem neg_entry (A : LinkingAlgebra X) (i j : ι) :
    (-A).entry i j = -A.entry i j := (rfl)
@[simp] theorem sub_entry (A B : LinkingAlgebra X) (i j : ι) :
    (A - B).entry i j = A.entry i j - B.entry i j := (rfl)
-- Not `@[simp]`: `nsmul_eq_mul`/`zsmul_eq_mul` and `mul_entry` simplify the LHS (`simpNF`).
theorem nsmul_entry (n : ℕ) (A : LinkingAlgebra X) (i j : ι) :
    (n • A).entry i j = n • A.entry i j := (rfl)
theorem zsmul_entry (n : ℤ) (A : LinkingAlgebra X) (i j : ι) :
    (n • A).entry i j = n • A.entry i j := (rfl)

/-- Matrix entries commute with finite sums in `LinkingAlgebra X`. -/
@[simp] theorem sum_entry {κ : Type*} (s : Finset κ) (f : κ → LinkingAlgebra X) (i j : ι) :
    (∑ a ∈ s, f a).entry i j = ∑ a ∈ s, (f a).entry i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

@[simp] theorem mul_entry (A B : LinkingAlgebra X) (i k : ι) :
    (A * B).entry i k = ∑ j : ι, B.entry j k ≫ A.entry i j := (rfl)

@[simp] theorem one_entry_self (i : ι) : (1 : LinkingAlgebra X).entry i i = 𝟙 (X i) :=
  Mat_.id_apply_self (Mat_.mk ι X) i

@[simp] theorem one_entry_of_ne {i j : ι} (h : i ≠ j) : (1 : LinkingAlgebra X).entry i j = 0 :=
  Mat_.id_apply_of_ne (Mat_.mk ι X) j i h.symm

/-- Explicit entrywise formula for the identity matrix `1 : LinkingAlgebra X`. -/
theorem one_entry [DecidableEq ι] (i j : ι) :
    (1 : LinkingAlgebra X).entry i j =
      if h : i = j then eqToHom (congrArg X h.symm) else 0 := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

section Linear

variable {R : Type r} [Semiring R] [CategoryTheory.Linear R C]

/-- The `R`-module structure on `LinkingAlgebra X`, inherited from `End (Mat_.mk ι X)`. -/
instance instModule : Module R (LinkingAlgebra X) :=
  inferInstanceAs (Module R (End (Mat_.mk ι X)))

@[simp] theorem smul_entry (c : R) (A : LinkingAlgebra X) (i j : ι) :
    (c • A).entry i j = c • A.entry i j := (rfl)

/-- Left scalar multiplication commutes with multiplication in `LinkingAlgebra X`. -/
instance instSMulCommClass : SMulCommClass R (LinkingAlgebra X) (LinkingAlgebra X) where
  smul_comm c A B := by
    ext i k
    simp [smul_eq_mul, Finset.smul_sum]

/-- Left scalar multiplication associates with multiplication in `LinkingAlgebra X`. -/
instance instIsScalarTower : IsScalarTower R (LinkingAlgebra X) (LinkingAlgebra X) where
  smul_assoc c A B := by
    ext i k
    simp [smul_eq_mul, Finset.smul_sum]

end Linear

section Algebra

variable {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]

/-- The `R`-algebra structure on `LinkingAlgebra X`, built via `Algebra.ofModule` on top of
`instModule` and `instRing` to stay diamond-free with `instModule`. -/
instance instAlgebra : Algebra R (LinkingAlgebra X) :=
  Algebra.ofModule (fun _ _ _ => smul_mul_assoc _ _ _) (fun _ _ _ => mul_smul_comm _ _ _)

@[simp] theorem algebraMap_entry [DecidableEq ι] (c : R) (i j : ι) :
    (algebraMap R (LinkingAlgebra X) c).entry i j =
      if h : i = j then c • eqToHom (congrArg X h.symm) else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, smul_entry, one_entry]
  split_ifs <;> simp

end Algebra

section EndMatAlgEquiv

/-- The canonical `R`-algebra equivalence identifying `LinkingAlgebra X` with
`CategoryTheory.End (Mat_.mk ι X)`, reversing entry indices to match operator order. -/
def endMatAlgEquiv (X : ι → C) (R : Type r)
    [CommSemiring R] [CategoryTheory.Linear R C] :
    LinkingAlgebra X ≃ₐ[R] End (Mat_.mk ι X) where
  toFun A := A
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' c := by
    apply End.ext
    refine Mat_.hom_ext _ _ fun j i => ?_
    classical
    change (algebraMap R (LinkingAlgebra X) c).entry i j =
      (algebraMap R (End (Mat_.mk ι X)) c).asHom j i
    rw [algebraMap_entry, Algebra.algebraMap_eq_smul_one, End.smul_asHom, End.one_asHom,
      Mat_.smul_apply]
    by_cases hji : i = j
    · subst hji; simp [Mat_.id_apply_self]
    · simp [hji, Mat_.id_apply_of_ne (Mat_.mk ι X) j i (Ne.symm hji)]

/-- Entrywise evaluation of `endMatAlgEquiv`. -/
@[simp] theorem endMatAlgEquiv_asHom {R : Type r} [CommSemiring R]
    [CategoryTheory.Linear R C] (A : LinkingAlgebra X) (j i : ι) :
    (endMatAlgEquiv X R A).asHom j i = A.entry i j := (rfl)

/-- Entrywise evaluation of `(endMatAlgEquiv X R).symm`. -/
@[simp] theorem endMatAlgEquiv_symm_entry {R : Type r} [CommSemiring R]
    [CategoryTheory.Linear R C] (f : End (Mat_.mk ι X)) (i j : ι) :
    ((endMatAlgEquiv X R).symm f).entry i j = f.asHom j i := (rfl)

end EndMatAlgEquiv

section Star

variable [DaggerCategory C]

/-- The conjugate-transpose involution on `LinkingAlgebra X`, given by
`(star A).entry i j = dagger (A.entry j i)`. -/
instance instStar : Star (LinkingAlgebra X) where
  star A := ofEntry fun i j => dagger (A.entry j i)

@[simp] theorem star_entry (A : LinkingAlgebra X) (i j : ι) :
    (star A).entry i j = dagger (A.entry j i) := (rfl)

instance instInvolutiveStar : InvolutiveStar (LinkingAlgebra X) where
  star_involutive A := by ext i j; simp

instance instStarAddMonoid [DaggerPreadditive C] : StarAddMonoid (LinkingAlgebra X) where
  star_add A B := by ext i j; simp

instance instStarRing [DaggerPreadditive C] : StarRing (LinkingAlgebra X) where
  star_mul A B := by ext i k; simp [dagger_sum]
  star_add := star_add

instance instStarModule {R : Type r} [Semiring R] [Star R] [CategoryTheory.Linear R C]
    [DaggerLinear R C] : StarModule R (LinkingAlgebra X) where
  star_smul c A := by ext i j; simp

end Star

end Basic

/-! ### Matrix units, corner projections, diagonal embeddings, and corner submodules -/

section MatrixUnits

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → C)

/-- The matrix unit with entry `f : X j ⟶ X i` at position `(i, j)` and `0` elsewhere. -/
def single (i j : ι) (f : X j ⟶ X i) : LinkingAlgebra X :=
  ofEntry fun i' j' =>
    if hi : i' = i then
      if hj : j' = j then eqToHom (congrArg X hj) ≫ f ≫ eqToHom (congrArg X hi.symm) else 0
    else 0

/-- Explicit entrywise formula for the matrix unit `single X i j f`. -/
theorem single_entry (i j i' j' : ι) (f : X j ⟶ X i) :
    (single X i j f).entry i' j' =
      if hi : i' = i then
        if hj : j' = j then eqToHom (congrArg X hj) ≫ f ≫ eqToHom (congrArg X hi.symm) else 0
      else 0 := (rfl)

/-- The `(i, j)` entry of `single X i j f` is `f`. -/
@[simp] theorem single_entry_self (i j : ι) (f : X j ⟶ X i) :
    (single X i j f).entry i j = f := by simp [single_entry]

/-- Off-row entries of `single X i j f` vanish. -/
@[simp] theorem single_entry_of_ne_left {i j i' j' : ι} (hi : i' ≠ i) (f : X j ⟶ X i) :
    (single X i j f).entry i' j' = 0 := by simp [single_entry, hi]

/-- Off-column entries of `single X i j f` vanish. -/
@[simp] theorem single_entry_of_ne_right {i j i' j' : ι} (hj : j' ≠ j) (f : X j ⟶ X i) :
    (single X i j f).entry i' j' = 0 := by simp [single_entry, hj]

/-- `single X i j` sends `0` to `0`. -/
@[simp] theorem single_zero (i j : ι) : single X i j 0 = 0 := by
  ext i' j'; simp only [single_entry, zero_entry]; split_ifs <;> simp

/-- `single X i j` is additive. -/
@[simp] theorem single_add (i j : ι) (f g : X j ⟶ X i) :
    single X i j (f + g) = single X i j f + single X i j g := by
  ext i' j'; simp only [single_entry, add_entry]; split_ifs <;> simp

/-- `single X i j` preserves negation. -/
@[simp] theorem single_neg (i j : ι) (f : X j ⟶ X i) :
    single X i j (-f) = -single X i j f := by
  ext i' j'; simp only [single_entry, neg_entry]; split_ifs <;> simp

/-- `single X i j` preserves subtraction. -/
@[simp] theorem single_sub (i j : ι) (f g : X j ⟶ X i) :
    single X i j (f - g) = single X i j f - single X i j g := by
  rw [sub_eq_add_neg, single_add, single_neg, ← sub_eq_add_neg]

/-- `single X i j` is linear with respect to scalar multiplication. -/
@[simp] theorem single_smul {R : Type r} [Semiring R] [CategoryTheory.Linear R C]
    (i j : ι) (c : R) (f : X j ⟶ X i) :
    single X i j (c • f) = c • single X i j f := by
  ext i' j'; simp only [single_entry, smul_entry]; split_ifs <;> simp

/-- `single X i j` is injective. -/
theorem single_injective (i j : ι) : Function.Injective (single X i j) := fun _ _ h => by
  simpa only [single_entry_self] using congrArg (fun A : LinkingAlgebra X => A.entry i j) h

/-- Taking the star of a matrix unit transposes its indices and takes the dagger of its entry. -/
@[simp] theorem star_single [DaggerCategory C] [DaggerPreadditive C]
    (i j : ι) (f : X j ⟶ X i) :
    star (single X i j f) = single X j i (dagger f) := by
  ext i' j'
  by_cases hi : i' = j
  · subst hi
    by_cases hj : j' = i
    · subst hj; simp
    · simp [single_entry_of_ne_left X hj, single_entry_of_ne_right X hj]
  · simp [single_entry_of_ne_left X hi, single_entry_of_ne_right X hi]

/-- Multiplying compatible matrix units composes their entries in operator order. -/
@[simp] theorem single_mul_single_same (i j k : ι) (f : X j ⟶ X i) (g : X k ⟶ X j) :
    single X i j f * single X j k g = single X i k (g ≫ f) := by
  ext i' k'
  by_cases hi : i' = i
  · subst hi
    by_cases hk : k' = k
    · subst hk
      simp only [mul_entry, single_entry_self]
      rw [Fintype.sum_eq_single j]
      · simp
      · intro m hm; simp [single_entry_of_ne_right X hm]
    · simp [mul_entry, single_entry_of_ne_right X hk]
  · simp [mul_entry, single_entry_of_ne_left X hi]

/-- Multiplying incompatible matrix units gives `0`. -/
@[simp] theorem single_mul_single_of_ne {i j j' k : ι} (h : j ≠ j') (f : X j ⟶ X i)
    (g : X k ⟶ X j') : single X i j f * single X j' k g = 0 := by
  ext i' k'
  simp only [mul_entry, zero_entry]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m = j
  · subst hm; simp [h]
  · simp [hm]

/-- Multiplying a matrix unit on the left by its star yields the diagonal matrix unit of
`f ≫ dagger f`. -/
theorem star_single_mul_single [DaggerCategory C] [DaggerPreadditive C]
    (i j : ι) (f : X j ⟶ X i) :
    star (single X i j f) * single X i j f = single X j j (f ≫ dagger f) := by
  rw [star_single, single_mul_single_same]

/-- Every element of `LinkingAlgebra X` decomposes as the sum of its matrix units. -/
theorem eq_sum_single (A : LinkingAlgebra X) :
    A = ∑ i : ι, ∑ j : ι, single X i j (A.entry i j) := by
  ext i k
  simp only [sum_entry]
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single k]
    · simp
    · intro j hj; exact single_entry_of_ne_right X (Ne.symm hj) _
  · intro i' hi'
    exact Finset.sum_eq_zero fun j _ => single_entry_of_ne_left X (Ne.symm hi') _

/-- The `i`-th diagonal corner projection `single X i i (𝟙 (X i))` in `LinkingAlgebra X`. -/
def proj (i : ι) : LinkingAlgebra X := single X i i (𝟙 (X i))

/-- Definitional characterization of `proj X i` as a diagonal matrix unit. -/
theorem proj_def (i : ι) : proj X i = single X i i (𝟙 (X i)) := (rfl)

@[simp] theorem proj_entry_self (i : ι) : (proj X i).entry i i = 𝟙 (X i) :=
  single_entry_self X i i (𝟙 (X i))

/-- Off-row entries of `proj X i` vanish. -/
@[simp] theorem proj_entry_of_ne_left {i i' j' : ι} (hi : i' ≠ i) :
    (proj X i).entry i' j' = 0 :=
  single_entry_of_ne_left X hi _

/-- Off-column entries of `proj X i` vanish. -/
@[simp] theorem proj_entry_of_ne_right {i i' j' : ι} (hj : j' ≠ i) :
    (proj X i).entry i' j' = 0 :=
  single_entry_of_ne_right X hj _

@[simp] theorem star_proj [DaggerCategory C] [DaggerPreadditive C] (i : ι) :
    star (proj X i) = proj X i := by
  rw [proj_def, star_single, dagger_id]

/-- Each diagonal corner projection is self-adjoint. -/
theorem isSelfAdjoint_proj [DaggerCategory C] [DaggerPreadditive C] (i : ι) :
    IsSelfAdjoint (proj X i) := star_proj X i

/-- Corner projections are mutually orthogonal idempotents. -/
theorem proj_mul_proj (i j : ι) :
    proj X i * proj X j = if i = j then proj X i else 0 := by
  by_cases h : i = j
  · subst h; rw [proj_def, single_mul_single_same, Category.id_comp, ite_eq_left rfl]
  · rw [proj_def, proj_def, single_mul_single_of_ne X h, ite_eq_right h]

@[simp] theorem proj_mul_proj_self (i : ι) : proj X i * proj X i = proj X i := by
  simp [proj_mul_proj]

/-- Each diagonal corner projection is idempotent. -/
theorem isIdempotentElem_proj (i : ι) : IsIdempotentElem (proj X i) :=
  proj_mul_proj_self X i

/-- Each diagonal corner projection is a star projection. -/
theorem isStarProjection_proj [DaggerCategory C] [DaggerPreadditive C] (i : ι) :
    IsStarProjection (proj X i) :=
  ⟨proj_mul_proj_self X i, isSelfAdjoint_proj X i⟩

/-- The diagonal corner projections sum to the identity of `LinkingAlgebra X`. -/
@[simp] theorem sum_proj : ∑ i : ι, proj X i = 1 := by
  ext i j
  simp only [sum_entry, one_entry]
  by_cases hij : i = j
  · subst hij
    rw [dite_eq_left rfl, Fintype.sum_eq_single i]
    · simp
    · intro k hk; exact proj_entry_of_ne_left X (Ne.symm hk)
  · rw [dite_eq_right hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk; exact proj_entry_of_ne_right X (Ne.symm hij)
    · exact proj_entry_of_ne_left X (Ne.symm hk)

/-- Left-right compression by `proj X i` and `proj X j` extracts the `(i, j)` matrix unit. -/
@[simp] theorem proj_mul_mul_proj (A : LinkingAlgebra X) (i j : ι) :
    proj X i * A * proj X j = single X i j (A.entry i j) := by
  conv_lhs => rw [eq_sum_single X A]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp [proj_def]
    · intro j' hj'
      simp [proj_def, hj']
  · intro i' hi'
    exact Finset.sum_eq_zero fun j' _ => by
      simp [proj_def, Ne.symm hi']

section DiagHom

variable (R : Type r) [Semiring R] [CategoryTheory.Linear R C]
  [DaggerCategory C] [DaggerPreadditive C]

/-- The non-unital star-algebra embedding of the `i`-th endomorphism algebra `End (X i)` into
`LinkingAlgebra X` as the `(i, i)` diagonal corner. -/
def diagHom (i : ι) : End (X i) →⋆ₙₐ[R] LinkingAlgebra X where
  toFun a := single X i i a.asHom
  map_zero' := single_zero X i i
  map_add' a b := single_add X i i a.asHom b.asHom
  map_smul' c a := single_smul X i i c a.asHom
  map_mul' a b := by rw [End.mul_asHom, single_mul_single_same]
  map_star' a := (star_single X i i a.asHom).symm

variable {R}

@[simp] theorem diagHom_apply (i : ι) (a : End (X i)) :
    diagHom X R i a = single X i i a.asHom := (rfl)

/-- The diagonal embedding `diagHom X R i` sends `1 : End (X i)` to `proj X i`. -/
-- Not `@[simp]`: `diagHom_apply` and `End.one_asHom` simplify the LHS (`simpNF`).
theorem diagHom_one (i : ι) : diagHom X R i 1 = proj X i := by
  rw [diagHom_apply, End.one_asHom, proj_def]

/-- The diagonal embedding `diagHom X R i` is injective. -/
theorem diagHom_injective (i : ι) : Function.Injective (diagHom X R i) := fun _ _ h =>
  End.ext (single_injective X i i h)

/-- An element of `LinkingAlgebra X` lies in the range of `diagHom X R i` if and only if it is
fixed by compression by `proj X i`. -/
theorem mem_range_diagHom_iff (i : ι) (A : LinkingAlgebra X) :
    A ∈ Set.range (diagHom X R i) ↔ proj X i * A * proj X i = A := by
  constructor
  · rintro ⟨a, rfl⟩; simp [diagHom_apply]
  · intro h
    refine ⟨End.of (A.entry i i), ?_⟩
    simpa only [diagHom_apply, ← proj_mul_mul_proj] using h

end DiagHom

/-- Membership in the `(i, j)` idempotent corner `TauCeti.cornerSubmodule R (proj X i) (proj X j)`
is characterized by left-right compression `proj X i * A * proj X j = A`. -/
@[simp] theorem mem_cornerSubmodule {R : Type r} [Semiring R] [CategoryTheory.Linear R C]
    (i j : ι) (A : LinkingAlgebra X) :
    A ∈ TauCeti.cornerSubmodule R (proj X i) (proj X j) ↔ proj X i * A * proj X j = A :=
  TauCeti.mem_cornerSubmodule_iff R (isIdempotentElem_proj X i) (isIdempotentElem_proj X j)

end MatrixUnits

/-- Multiplying the `(1, 0)` corner element `single ![X, Y] 1 0 f` on the left by its star yields
the diagonal embedding of `End.of (f ≫ dagger f)` in `LinkingAlgebra ![X, Y]`. -/
theorem star_mul_single_pair {C : Type u} [Category.{v} C] [Preadditive C]
    {R : Type r} [Semiring R] [CategoryTheory.Linear R C]
    [DaggerCategory C] [DaggerPreadditive C] {X Y : C} (f : X ⟶ Y) :
    star (single ![X, Y] (1 : Fin 2) 0 f) * single ![X, Y] (1 : Fin 2) 0 f =
      diagHom ![X, Y] R 0 (End.of (f ≫ dagger f)) := by
  rw [diagHom_apply]
  exact star_single_mul_single ![X, Y] 1 0 f

end LinkingAlgebra

end TauCeti
