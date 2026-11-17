/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Mat
public import TauCeti.Analysis.StarAlgebra.GNS.Bounded
public import TauCeti.CategoryTheory.CStar.Basic
public import TauCeti.CategoryTheory.Linear.Mat

import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import TauCeti.Analysis.CStarAlgebra.State.Spectrum

/-!
# Finite linking algebras of C*-categories

Given a finite family of objects `X : ι → C` (in particular `L.get : Fin L.length → C` for a list
`L : List C`), the finite linking algebra `TauCeti.LinkingAlgebra X` is defined as a type synonym
of `CategoryTheory.End (Mat_.mk ι X)`. Indexing entries in operator order via
`A.entry i j := End.asHom A j i : X j ⟶ X i`, multiplication in `End (Mat_.mk ι X)` gives
operator-order matrix multiplication `(A * B).entry i k = ∑ j, B.entry j k ≫ A.entry i j`, while
the dagger structure equips `LinkingAlgebra X` with the conjugate-transpose involution
`(star A).entry i j = dagger (A.entry j i)`.

For a C*-category `C`, every positive linear functional `φ : End (X k) →ₚ[ℂ] ℂ` pulls back to a
`StarPositiveFunctional` `LinkingAlgebra.cornerFunctional X k φ` on `LinkingAlgebra X`. Every
matrix unit acts boundedly on its GNS space (by `CStarCategory.comp_self_comp_dagger_le`), so
`TauCeti.StarPositiveFunctional.boundedRepresentation` yields a unital star-representation
`LinkingAlgebra.gnsRep X k φ`. Taking the supremum of operator norms over all `(k, φ)` equips
`LinkingAlgebra X` with a `CStarAlgebra` structure whose norm satisfies
`‖A.entry i j‖ ≤ ‖A‖ ≤ ∑ i, ∑ j, ‖A.entry i j‖` and `‖single X i j f‖ = ‖f‖`.

From this we obtain isometric corner identifications
`cornerSubmodule X ℂ i j ≃ₗᵢ[ℂ] (X j ⟶ X i)`, isometric order-embedding diagonal
maps `diagHom X ℂ i : End (X i) →⋆ₙₐ[ℂ] LinkingAlgebra X`, the matrix positivity criterion
`LinkingAlgebra.nonneg_iff`, and recovery of the Hom norm and endomorphism positivity from
two-object corners `LinkingAlgebra ![X, Y]`.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109,
  Section 1.
-/

public section

open CategoryTheory
open scoped ComplexOrder InnerProductSpace

universe r v u

namespace TauCeti

/-- The finite linking algebra associated to a family of objects `X : ι → C`, defined as a type
synonym of `CategoryTheory.End (Mat_.mk ι X)`. Its `(i, j)` matrix entry `A.entry i j` is a
morphism `X j ⟶ X i`, equipped with operator-order matrix multiplication and (in a dagger
category) conjugate-transpose involution. -/
@[expose] def LinkingAlgebra {C : Type u} [Category.{v} C] [Preadditive C]
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
noncomputable instance instRing : Ring (LinkingAlgebra X) :=
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
noncomputable instance instModule : Module R (LinkingAlgebra X) :=
  inferInstanceAs (Module R (End (Mat_.mk ι X)))

@[simp] theorem smul_entry (c : R) (A : LinkingAlgebra X) (i j : ι) :
    (c • A).entry i j = c • A.entry i j := (rfl)

end Linear

section Algebra

variable {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]

/-- The `R`-algebra structure on `LinkingAlgebra X`, built via `Algebra.ofModule` on top of
`instModule` and `instRing` to stay diamond-free with `instModule`. -/
noncomputable instance instAlgebra : Algebra R (LinkingAlgebra X) :=
  Algebra.ofModule
    (fun c A B => by ext i k; simp [Finset.smul_sum])
    (fun c A B => by ext i k; simp [Finset.smul_sum])

@[simp] theorem algebraMap_entry [DecidableEq ι] (c : R) (i j : ι) :
    (algebraMap R (LinkingAlgebra X) c).entry i j =
      if h : i = j then c • eqToHom (congrArg X h.symm) else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, smul_entry, one_entry]
  split_ifs <;> simp

end Algebra

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
theorem single_entry_of_ne_left {i j i' j' : ι} (hi : i' ≠ i) (f : X j ⟶ X i) :
    (single X i j f).entry i' j' = 0 := by simp [single_entry, hi]

/-- Off-column entries of `single X i j f` vanish. -/
theorem single_entry_of_ne_right {i j i' j' : ι} (hj : j' ≠ j) (f : X j ⟶ X i) :
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
theorem single_mul_single_of_ne {i j j' k : ι} (h : j ≠ j') (f : X j ⟶ X i) (g : X k ⟶ X j') :
    single X i j f * single X j' k g = 0 := by
  ext i' k'
  simp only [mul_entry, zero_entry]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m = j
  · subst hm; simp [single_entry_of_ne_left X h]
  · simp [single_entry_of_ne_right X hm]

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
theorem proj_entry_of_ne_left {i i' j' : ι} (hi : i' ≠ i) : (proj X i).entry i' j' = 0 :=
  single_entry_of_ne_left X hi _

/-- Off-column entries of `proj X i` vanish. -/
theorem proj_entry_of_ne_right {i i' j' : ι} (hj : j' ≠ i) : (proj X i).entry i' j' = 0 :=
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
      simp [proj_def, single_mul_single_of_ne X hj']
  · intro i' hi'
    exact Finset.sum_eq_zero fun j' _ => by
      simp [proj_def, single_mul_single_of_ne X (Ne.symm hi')]

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

/-- The `(i, j)` corner submodule `{ A : LinkingAlgebra X | proj X i * A * proj X j = A }`. -/
def cornerSubmodule (R : Type r) [Semiring R] [CategoryTheory.Linear R C] (i j : ι) :
    Submodule R (LinkingAlgebra X) where
  carrier := { A : LinkingAlgebra X | proj X i * A * proj X j = A }
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    simp only [Set.mem_ofPred_eq] at hA hB ⊢
    rw [mul_add, add_mul, hA, hB]
  smul_mem' c {A} hA := by
    simp only [Set.mem_ofPred_eq] at hA ⊢
    rw [proj_mul_mul_proj, smul_entry, single_smul, ← proj_mul_mul_proj, hA]

@[simp] theorem mem_cornerSubmodule {R : Type r} [Semiring R] [CategoryTheory.Linear R C]
    (i j : ι) (A : LinkingAlgebra X) :
    A ∈ cornerSubmodule X R i j ↔ proj X i * A * proj X j = A :=
  Iff.rfl

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

/-! ### Corner positive functionals, GNS representations, and C*-algebra structure -/

section CStar

open scoped _root_.CStarAlgebra

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {ι : Type} [Fintype ι]

variable (X : ι → C)

section GNS

variable (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ)

/-- The `StarPositiveFunctional` on `LinkingAlgebra X` obtained by composing a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ` with extraction of the `(k, k)` diagonal corner. -/
def cornerFunctional : StarPositiveFunctional (LinkingAlgebra X) where
  toLinearMap :=
    { toFun A := φ (End.of (A.entry k k))
      map_add' A B := by simp only [add_entry, End.of_add, map_add]
      map_smul' c A := by simp only [smul_entry, End.of_smul, map_smul, RingHom.id_apply] }
  square_nonneg A := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_entry, star_entry, End.of_sum, map_sum]
    exact Finset.sum_nonneg fun j _ =>
      φ.map_nonneg (CStarCategory.self_comp_dagger_nonneg (A.entry j k))

@[simp] theorem cornerFunctional_apply (A : LinkingAlgebra X) :
    cornerFunctional X k φ A = φ (End.of (A.entry k k)) := (rfl)

private theorem cornerFunctional_single_bound [DecidableEq ι]
    (i j : ι) (f : X j ⟶ X i) (B : LinkingAlgebra X) :
    cornerFunctional X k φ (star B * star (single X i j f) * single X i j f * B) ≤
      (‖f‖ : ℂ) ^ 2 * cornerFunctional X k φ (star B * B) := by
  have hprod_entry (m : ι) :
      (single X i j f * B).entry m k =
        if hm : m = i then B.entry j k ≫ f ≫ eqToHom (congrArg X hm.symm) else 0 := by
    simp only [mul_entry]
    by_cases hm : m = i
    · subst hm
      rw [dite_eq_left rfl, Fintype.sum_eq_single j]
      · simp
      · intro l hl; simp [single_entry_of_ne_right X hl]
    · rw [dite_eq_right hm]
      exact Finset.sum_eq_zero fun l _ => by simp [single_entry_of_ne_left X hm]
  have hlhs :
      End.of ((star B * star (single X i j f) * single X i j f * B).entry k k) =
        End.of ((B.entry j k ≫ f) ≫ dagger (B.entry j k ≫ f)) := by
    have hassoc : star B * star (single X i j f) * single X i j f * B =
        star (single X i j f * B) * (single X i j f * B) := by
      simp only [star_mul, mul_assoc]
    rw [hassoc, mul_entry]
    simp only [star_entry]
    rw [Fintype.sum_eq_single i]
    · have hi := hprod_entry i
      simp only [↓reduceDIte, eqToHom_refl, Category.comp_id] at hi
      rw [hi]
    · intro m hm; rw [hprod_entry m, dite_eq_right hm]; simp
  have hle_end :
      End.of ((star B * star (single X i j f) * single X i j f * B).entry k k) ≤
        (‖f‖ ^ 2 : ℝ) • End.of ((star B * B).entry k k) := by
    rw [hlhs]
    simp only [mul_entry, star_entry, End.of_sum]
    refine (CStarCategory.comp_self_comp_dagger_le (B.entry j k) f).trans ?_
    refine smul_le_smul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum
      (fun m _ => CStarCategory.self_comp_dagger_nonneg (B.entry m k)) (Finset.mem_univ j)
  have hφ := OrderHomClass.mono φ hle_end
  rw [LinearMapClass.map_smul_of_tower, Complex.real_smul, Complex.ofReal_pow] at hφ
  exact hφ

private theorem continuous_leftMul_single [DecidableEq ι] (i j : ι) (f : X j ⟶ X i) :
    Continuous ((cornerFunctional X k φ).leftMul (single X i j f)) :=
  ((cornerFunctional X k φ).continuous_leftMul_iff _).mpr
    ⟨‖f‖, norm_nonneg f, cornerFunctional_single_bound X k φ i j f⟩

/-- Every element of `LinkingAlgebra X` acts continuously on the algebraic GNS space of
`cornerFunctional X k φ`. -/
theorem continuous_leftMul_cornerFunctional (A : LinkingAlgebra X) :
    Continuous ((cornerFunctional X k φ).leftMul A) := by
  classical
  rw [← (cornerFunctional X k φ).mem_boundedSubalgebra, eq_sum_single X A]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  rw [(cornerFunctional X k φ).mem_boundedSubalgebra]
  exact continuous_leftMul_single X k φ i j (A.entry i j)

/-- The completed GNS Hilbert space of `LinkingAlgebra X` associated to a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ`. Defined as `@[expose] def` rather than `abbrev` because
operator-norm rewrites and `NegPart` synthesis on `(cornerFunctional X k φ).HilbertGNS →L[ℂ] ...`
time out unfolding `UniformSpace.Completion (SeparationQuotient PreGNS)`. -/
@[expose] def GNS : Type v :=
  (cornerFunctional X k φ).HilbertGNS

noncomputable instance instGNSNormedAddCommGroup : NormedAddCommGroup (GNS X k φ) :=
  inferInstanceAs (NormedAddCommGroup (cornerFunctional X k φ).HilbertGNS)

noncomputable instance instGNSInnerProductSpace : InnerProductSpace ℂ (GNS X k φ) :=
  inferInstanceAs (InnerProductSpace ℂ (cornerFunctional X k φ).HilbertGNS)

instance instGNSCompleteSpace : CompleteSpace (GNS X k φ) :=
  inferInstanceAs (CompleteSpace (cornerFunctional X k φ).HilbertGNS)

/-- The canonical linear isometry equivalence identifying `GNS X k φ` with
`(cornerFunctional X k φ).HilbertGNS`. -/
noncomputable def gnsEquiv : GNS X k φ ≃ₗᵢ[ℂ] (cornerFunctional X k φ).HilbertGNS where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The canonical linear map sending an element of `LinkingAlgebra X` to its class in
`GNS X k φ`. -/
noncomputable def gnsClassMap : LinkingAlgebra X →ₗ[ℂ] GNS X k φ :=
  (gnsEquiv X k φ).symm.toLinearMap.comp (cornerFunctional X k φ).hilbertClassMap

/-- The canonical cyclic vector represented by `1` in `GNS X k φ`. -/
noncomputable def gnsCyclicVector : GNS X k φ :=
  (gnsEquiv X k φ).symm (cornerFunctional X k φ).hilbertCyclicVector

@[simp] theorem gnsEquiv_gnsClassMap (A : LinkingAlgebra X) :
    gnsEquiv X k φ (gnsClassMap X k φ A) = (cornerFunctional X k φ).hilbertClassMap A := (rfl)

@[simp] theorem gnsEquiv_gnsCyclicVector :
    gnsEquiv X k φ (gnsCyclicVector X k φ) = (cornerFunctional X k φ).hilbertCyclicVector := (rfl)

@[simp] theorem inner_gnsClassMap (A B : LinkingAlgebra X) :
    ⟪gnsClassMap X k φ A, gnsClassMap X k φ B⟫_ℂ = cornerFunctional X k φ (star A * B) :=
  (cornerFunctional X k φ).inner_hilbertClassMap A B

theorem norm_gnsClassMap_sq (A : LinkingAlgebra X) :
    ‖gnsClassMap X k φ A‖ ^ 2 = (cornerFunctional X k φ (star A * A)).re :=
  (cornerFunctional X k φ).norm_hilbertClassMap_sq A

theorem norm_gnsCyclicVector (hφ : φ 1 = 1) : ‖gnsCyclicVector X k φ‖ = 1 :=
  (cornerFunctional X k φ).norm_hilbertCyclicVector (by simpa using hφ)

/-- Algebra classes are dense in `GNS X k φ`. -/
theorem denseRange_gnsClassMap : DenseRange (gnsClassMap X k φ) :=
  (gnsEquiv X k φ).symm.surjective.denseRange.comp
    (cornerFunctional X k φ).denseRange_hilbertClassMap (gnsEquiv X k φ).symm.continuous

/-- The canonical unital GNS star-representation of `LinkingAlgebra X` induced by a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ`, built via
`TauCeti.StarPositiveFunctional.boundedRepresentation`. -/
noncomputable def gnsRep : LinkingAlgebra X →⋆ₐ[ℂ] (GNS X k φ →L[ℂ] GNS X k φ) :=
  (cornerFunctional X k φ).boundedRepresentation (continuous_leftMul_cornerFunctional X k φ)

/-- Transporting `gnsRep X k φ A` along `gnsEquiv X k φ` recovers the Hilbert GNS
left-multiplication operator of `cornerFunctional X k φ`. -/
theorem gnsEquiv_gnsRep_apply (A : LinkingAlgebra X) (x : GNS X k φ) :
    gnsEquiv X k φ (gnsRep X k φ A x) =
      (cornerFunctional X k φ).hilbertLeftMul (continuous_leftMul_cornerFunctional X k φ A)
        (gnsEquiv X k φ x) :=
  congrArg (fun T => T (gnsEquiv X k φ x))
    ((cornerFunctional X k φ).boundedRepresentation_apply _ A)

/-- Action of `gnsRep X k φ` on `gnsClassMap X k φ`. -/
@[simp] theorem gnsRep_gnsClassMap (A B : LinkingAlgebra X) :
    gnsRep X k φ A (gnsClassMap X k φ B) = gnsClassMap X k φ (A * B) :=
  (cornerFunctional X k φ).boundedRepresentation_hilbertClassMap _ A B

/-- Action of `gnsRep X k φ` on `gnsCyclicVector X k φ`. -/
@[simp] theorem gnsRep_gnsCyclicVector (A : LinkingAlgebra X) :
    gnsRep X k φ A (gnsCyclicVector X k φ) = gnsClassMap X k φ A :=
  (cornerFunctional X k φ).boundedRepresentation_hilbertCyclicVector _ A

/-- Operator-norm bound for `gnsRep X k φ A` in terms of the quadratic form of
`cornerFunctional X k φ`. -/
theorem norm_gnsRep_le_iff (A : LinkingAlgebra X) {R : ℝ} (hR : 0 ≤ R) :
    ‖gnsRep X k φ A‖ ≤ R ↔
      ∀ B : LinkingAlgebra X,
        cornerFunctional X k φ (star B * star A * A * B) ≤
          (R : ℂ) ^ 2 * cornerFunctional X k φ (star B * B) := by
  rw [← (cornerFunctional X k φ).norm_hilbertLeftMul_le_iff
    (continuous_leftMul_cornerFunctional X k φ A) hR,
    ContinuousLinearMap.opNorm_le_iff hR, ContinuousLinearMap.opNorm_le_iff hR]
  refine ⟨fun h y => ?_, fun h x => ?_⟩
  · have hy := h ((gnsEquiv X k φ).symm y)
    rw [← (gnsEquiv X k φ).norm_map, gnsEquiv_gnsRep_apply,
      (gnsEquiv X k φ).apply_symm_apply, (gnsEquiv X k φ).symm.norm_map] at hy
    exact hy
  · simpa only [← gnsEquiv_gnsRep_apply, LinearIsometryEquiv.norm_map] using
      h (gnsEquiv X k φ x)

private theorem norm_gnsRep_single_le [DecidableEq ι] (i j : ι) (f : X j ⟶ X i) :
    ‖gnsRep X k φ (single X i j f)‖ ≤ ‖f‖ :=
  (norm_gnsRep_le_iff X k φ (single X i j f) (norm_nonneg f)).mpr
    (cornerFunctional_single_bound X k φ i j f)

private theorem norm_gnsRep_le_sum (A : LinkingAlgebra X) :
    ‖gnsRep X k φ A‖ ≤ ∑ i : ι, ∑ j : ι, ‖A.entry i j‖ := by
  classical
  calc ‖gnsRep X k φ A‖
      = ‖∑ i : ι, ∑ j : ι, gnsRep X k φ (single X i j (A.entry i j))‖ := by
          conv_lhs => rw [eq_sum_single X A]
          simp only [map_sum]
    _ ≤ ∑ i : ι, ‖∑ j : ι, gnsRep X k φ (single X i j (A.entry i j))‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι, ‖gnsRep X k φ (single X i j (A.entry i j))‖ :=
          Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι, ‖A.entry i j‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            norm_gnsRep_single_le X k φ i j (A.entry i j)

end GNS

/-- The C*-norm on `LinkingAlgebra X`, defined as the supremum of operator norms over all GNS
representations induced by positive linear functionals on `End (X k)`. -/
noncomputable instance instNorm : Norm (LinkingAlgebra X) where
  norm A := ⨆ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖

variable {X}

/-- Definitional formula for the C*-norm on `LinkingAlgebra X`. -/
theorem norm_def (A : LinkingAlgebra X) :
    ‖A‖ = ⨆ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖ := (rfl)

private theorem bddAbove_gnsRep_inner (k : ι) (A : LinkingAlgebra X) :
    BddAbove (Set.range fun φ : End (X k) →ₚ[ℂ] ℂ => ‖gnsRep X k φ A‖) :=
  ⟨∑ i : ι, ∑ j : ι, ‖A.entry i j‖, by rintro _ ⟨φ, rfl⟩; exact norm_gnsRep_le_sum X k φ A⟩

private theorem bddAbove_gnsRep_outer (A : LinkingAlgebra X) :
    BddAbove (Set.range fun k : ι => ⨆ φ : End (X k) →ₚ[ℂ] ℂ, ‖gnsRep X k φ A‖) :=
  ⟨∑ i : ι, ∑ j : ι, ‖A.entry i j‖, by
    rintro _ ⟨k, rfl⟩
    exact Real.iSup_le (fun φ => norm_gnsRep_le_sum X k φ A)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)⟩

/-- The norm of `A` in `LinkingAlgebra X` dominates every GNS operator norm `‖gnsRep X k φ A‖`. -/
theorem norm_gnsRep_le (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) (A : LinkingAlgebra X) :
    ‖gnsRep X k φ A‖ ≤ ‖A‖ :=
  (le_ciSup (bddAbove_gnsRep_inner k A) φ).trans (le_ciSup (bddAbove_gnsRep_outer A) k)

/-- Upper bound for the C*-norm on `LinkingAlgebra X` from a uniform bound on all GNS
representations. -/
theorem norm_le_of_forall_gnsRep {A : LinkingAlgebra X} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖ ≤ M) : ‖A‖ ≤ M :=
  Real.iSup_le (fun k => Real.iSup_le (fun φ => h k φ) hM) hM

/-- The C*-norm on `LinkingAlgebra X` is bounded above by the entrywise `ℓ¹` norm. -/
theorem norm_le_sum_norm_entry (A : LinkingAlgebra X) :
    ‖A‖ ≤ ∑ i : ι, ∑ j : ι, ‖A.entry i j‖ :=
  norm_le_of_forall_gnsRep
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun k φ => norm_gnsRep_le_sum X k φ A)

/-- Every matrix entry has norm bounded by the C*-norm of the linking-algebra element. -/
theorem norm_entry_le (A : LinkingAlgebra X) (i j : ι) : ‖A.entry i j‖ ≤ ‖A‖ := by
  have hA_nn : 0 ≤ ‖A‖ := (norm_nonneg (gnsRep X j 0 A)).trans (norm_gnsRep_le j 0 A)
  by_cases h0 : A.entry i j = 0
  · rw [h0, norm_zero]; exact hA_nn
  · let a : End (X j) := End.of (A.entry i j ≫ dagger (A.entry i j))
    have ha_nn : 0 ≤ a := CStarCategory.self_comp_dagger_nonneg (A.entry i j)
    have ha_ne : a ≠ 0 := fun h =>
      h0 ((CStarCategory.self_comp_dagger_eq_zero (A.entry i j)).mp (congrArg End.asHom h))
    have : Nontrivial (End (X j)) := nontrivial_of_ne a 0 ha_ne
    obtain ⟨φ₀, hφ1, -, hφa⟩ :=
      TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_eq_norm ha_nn
    let φ : End (X j) →ₚ[ℂ] ℂ := φ₀.toPositiveLinearMap
    have hcyc : ‖gnsCyclicVector X j φ‖ = 1 := norm_gnsCyclicVector X j φ hφ1
    have hge : ‖A.entry i j‖ ^ 2 ≤ ‖gnsRep X j φ A (gnsCyclicVector X j φ)‖ ^ 2 := by
      rw [gnsRep_gnsCyclicVector, norm_gnsClassMap_sq]
      simp only [cornerFunctional_apply, mul_entry, star_entry, End.of_sum, map_sum, Complex.re_sum]
      have hterm : ‖A.entry i j‖ ^ 2 = (φ (End.of (A.entry i j ≫ dagger (A.entry i j)))).re := by
        simpa only [a, φ, PositiveContinuousLinearMap.coe_toPositiveLinearMap, End.norm_of,
          CStarCategory.norm_self_comp_dagger, Complex.ofReal_re] using
          (congrArg Complex.re hφa).symm
      rw [hterm]
      exact Finset.single_le_sum (fun m _ =>
        (RCLike.nonneg_iff.mp (φ.map_nonneg
          (CStarCategory.self_comp_dagger_nonneg (A.entry m j)))).1) (Finset.mem_univ i)
    have hle : ‖gnsRep X j φ A (gnsCyclicVector X j φ)‖ ≤ ‖A‖ :=
      calc ‖gnsRep X j φ A (gnsCyclicVector X j φ)‖
          ≤ ‖gnsRep X j φ A‖ * ‖gnsCyclicVector X j φ‖ := (gnsRep X j φ A).le_opNorm _
        _ = ‖gnsRep X j φ A‖ := by rw [hcyc, mul_one]
        _ ≤ ‖A‖ := norm_gnsRep_le j φ A
    exact (sq_le_sq₀ (norm_nonneg _) hA_nn).mp
      (hge.trans (pow_le_pow_left₀ (norm_nonneg _) hle 2))

private theorem norm_nonneg_aux (A : LinkingAlgebra X) : 0 ≤ ‖A‖ := by
  rw [norm_def]; exact Real.iSup_nonneg fun k => Real.iSup_nonneg fun φ => norm_nonneg _

private theorem norm_neg_le_aux (A : LinkingAlgebra X) : ‖-A‖ ≤ ‖A‖ := by
  refine norm_le_of_forall_gnsRep (norm_nonneg_aux A) fun k φ => ?_
  rw [map_neg, norm_neg]; exact norm_gnsRep_le k φ A

private theorem norm_neg_aux (A : LinkingAlgebra X) : ‖-A‖ = ‖A‖ :=
  le_antisymm (norm_neg_le_aux A) (by simpa only [neg_neg] using norm_neg_le_aux (-A))

private theorem norm_add_le_aux (A B : LinkingAlgebra X) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := by
  refine norm_le_of_forall_gnsRep (add_nonneg (norm_nonneg_aux A) (norm_nonneg_aux B)) fun k φ => ?_
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add (norm_gnsRep_le k φ A) (norm_gnsRep_le k φ B))

/-- The normed ring structure on `LinkingAlgebra X`, reusing the native `Ring` instance. -/
noncomputable instance instNormedRing : NormedRing (LinkingAlgebra X) where
  toNorm := instNorm X
  toRing := instRing
  dist A B := ‖A - B‖
  dist_self A := by
    rw [sub_self]
    exact le_antisymm (by simpa using norm_le_sum_norm_entry (0 : LinkingAlgebra X))
      (norm_nonneg_aux 0)
  dist_comm A B := by rw [← neg_sub, norm_neg_aux]
  dist_triangle A B D := by
    simpa only [sub_add_sub_cancel] using norm_add_le_aux (A - B) (B - D)
  eq_of_dist_eq_zero {A B} h := by
    apply sub_eq_zero.mp; ext i j
    exact norm_eq_zero.mp (le_antisymm ((norm_entry_le (A - B) i j).trans_eq h) (norm_nonneg _))
  dist_eq A B := by rw [neg_add_eq_sub, ← neg_sub, norm_neg_aux]
  norm_mul_le A B := by
    refine norm_le_of_forall_gnsRep (mul_nonneg (norm_nonneg_aux A) (norm_nonneg_aux B))
      fun k φ => ?_
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_gnsRep_le k φ A) (norm_gnsRep_le k φ B)
      (norm_nonneg _) (norm_nonneg_aux A))

/-- The normed `ℂ`-algebra structure on `LinkingAlgebra X`, reusing the native `Algebra ℂ`
instance. -/
noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (LinkingAlgebra X) where
  toAlgebra := instAlgebra
  norm_smul_le c A := by
    refine norm_le_of_forall_gnsRep (mul_nonneg (norm_nonneg c) (norm_nonneg A)) fun k φ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_gnsRep_le k φ A) (norm_nonneg c)

/-- Finite linking algebras of a C*-category are complete. -/
instance instCompleteSpace : CompleteSpace (LinkingAlgebra X) :=
  Metric.complete_of_cauchySeq_tendsto fun u hu => by
    have hcoord (i j : ι) : CauchySeq fun n => (u n).entry i j := by
      rw [Metric.cauchySeq_iff] at hu ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      rw [dist_eq_norm, ← sub_entry]
      exact (norm_entry_le (u m - u n) i j).trans_lt
        (by simpa only [dist_eq_norm] using hN m hm n hn)
    choose L hL using fun i j => cauchySeq_tendsto_of_complete (hcoord i j)
    refine ⟨ofEntry L, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
    have hsum : Filter.Tendsto (fun n => ∑ i : ι, ∑ j : ι, ‖(u n).entry i j - L i j‖)
        Filter.atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum Finset.univ fun i _ =>
          tendsto_finsetSum Finset.univ fun j _ => tendsto_iff_norm_sub_tendsto_zero.mp (hL i j)
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hsum) ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have h0 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h0
    exact (norm_le_sum_norm_entry (u n - ofEntry L)).trans_lt
      (by simpa only [sub_entry, ofEntry_entry] using h0)

/-- The C*-identity holds on `LinkingAlgebra X`. -/
instance instCStarRing : CStarRing (LinkingAlgebra X) where
  norm_mul_self_le A := by
    have hsqrt : ‖A‖ ≤ √‖star A * A‖ := by
      refine norm_le_of_forall_gnsRep (Real.sqrt_nonneg _) fun k φ => ?_
      refine Real.le_sqrt_of_sq_le ?_
      rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
      exact norm_gnsRep_le k φ (star A * A)
    calc ‖A‖ * ‖A‖ = ‖A‖ ^ 2 := (sq ‖A‖).symm
      _ ≤ (√‖star A * A‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsqrt 2
      _ = ‖star A * A‖ := Real.sq_sqrt (norm_nonneg _)

/-- Finite linking algebras of a C*-category are unital C*-algebras. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (LinkingAlgebra X) where

/-- The spectral partial order on `LinkingAlgebra X`. -/
noncomputable instance instPartialOrder : PartialOrder (LinkingAlgebra X) :=
  CStarAlgebra.spectralOrder _

/-- Finite linking algebras of a C*-category are star-ordered rings under the spectral order. -/
instance instStarOrderedRing : StarOrderedRing (LinkingAlgebra X) :=
  CStarAlgebra.spectralOrderedRing _

/-! ### Corner identifications -/

section CornerIdentifications

variable [DecidableEq ι] (X)

/-- The matrix unit `single X i j f` has the same norm as its entry `f`. -/
@[simp] theorem norm_single (i j : ι) (f : X j ⟶ X i) : ‖single X i j f‖ = ‖f‖ :=
  le_antisymm
    (norm_le_of_forall_gnsRep (norm_nonneg f) fun k φ => norm_gnsRep_single_le X k φ i j f)
    (by simpa only [single_entry_self] using norm_entry_le (single X i j f) i j)

/-- The `(i, j)` matrix-unit embedding as a linear isometry
`(X j ⟶ X i) →ₗᵢ[ℂ] LinkingAlgebra X`. -/
def singleLinearIsometry (i j : ι) : (X j ⟶ X i) →ₗᵢ[ℂ] LinkingAlgebra X where
  toFun := single X i j
  map_add' := single_add X i j
  map_smul' := single_smul X i j
  norm_map' := norm_single X i j

@[simp] theorem singleLinearIsometry_apply (i j : ι) (f : X j ⟶ X i) :
    singleLinearIsometry X i j f = single X i j f := (rfl)

/-- The `(i, j)` corner `cornerSubmodule X ℂ i j` is linearly isometrically equivalent to the Hom
space `X j ⟶ X i`. -/
def cornerLinearIsometryEquiv (i j : ι) :
    cornerSubmodule X ℂ i j ≃ₗᵢ[ℂ] (X j ⟶ X i) where
  toFun A := A.1.entry i j
  invFun f := ⟨single X i j f, by simp⟩
  left_inv A := by
    apply Subtype.ext
    simpa only [mem_cornerSubmodule, proj_mul_mul_proj] using A.2
  right_inv f := single_entry_self X i j f
  map_add' A B := add_entry A.1 B.1 i j
  map_smul' c A := smul_entry c A.1 i j
  norm_map' A := by
    have hA : A.1 = single X i j (A.1.entry i j) := by
      simpa only [mem_cornerSubmodule, proj_mul_mul_proj] using A.2.symm
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    conv_rhs => rw [← Submodule.norm_coe, hA]
    exact (norm_single X i j (A.1.entry i j)).symm

@[simp] theorem cornerLinearIsometryEquiv_apply (i j : ι) (A : cornerSubmodule X ℂ i j) :
    cornerLinearIsometryEquiv X i j A = A.1.entry i j := (rfl)

@[simp] theorem cornerLinearIsometryEquiv_symm_apply (i j : ι) (f : X j ⟶ X i) :
    ((cornerLinearIsometryEquiv X i j).symm f).1 = single X i j f := (rfl)

/-- The diagonal embedding `diagHom X ℂ i : End (X i) →⋆ₙₐ[ℂ] LinkingAlgebra X` preserves norms. -/
theorem norm_diagHom (i : ι) (a : End (X i)) : ‖diagHom X ℂ i a‖ = ‖a‖ :=
  norm_single X i i a.asHom

/-- The diagonal embedding `diagHom X ℂ i` is an isometry. -/
theorem isometry_diagHom (i : ι) : Isometry (diagHom X ℂ i) :=
  NonUnitalStarAlgHom.isometry (φ := diagHom X ℂ i) (diagHom_injective X i)

/-- The diagonal embedding `diagHom X ℂ i` preserves and reflects the spectral order. -/
theorem diagHom_le_iff (i : ι) {a b : End (X i)} :
    diagHom X ℂ i a ≤ diagHom X ℂ i b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (f := diagHom X ℂ i) (diagHom_injective X i)

/-- An endomorphism `a : End (X i)` is positive if and only if its image under `diagHom X ℂ i` is
positive in `LinkingAlgebra X`. -/
theorem diagHom_nonneg_iff (i : ι) {a : End (X i)} :
    0 ≤ diagHom X ℂ i a ↔ 0 ≤ a := by
  simpa only [map_zero] using diagHom_le_iff X i (a := 0) (b := a)

end CornerIdentifications

/-! ### Matrix positivity characterization -/

/-- A positive element `A` of `LinkingAlgebra X` defines a positive quadratic form
`v ↦ ∑ i, ∑ j, v j ≫ A.entry i j ≫ dagger (v i)` in `End Z` for every object `Z : C` and every
column `v : (j : ι) → (Z ⟶ X j)`. -/
theorem sum_comp_entry_comp_dagger_nonneg {A : LinkingAlgebra X} (hA : 0 ≤ A) {Z : C}
    (v : (j : ι) → (Z ⟶ X j)) :
    0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  have hsum : ∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i) =
      ∑ m : ι, (∑ j : ι, v j ≫ B.entry m j) ≫ dagger (∑ i : ι, v i ≫ B.entry m i) := by
    have hentry (i j : ι) : A.entry i j = ∑ m : ι, B.entry m j ≫ dagger (B.entry m i) := by
      simpa only [mul_entry, star_entry] using
        congrArg (fun M : LinkingAlgebra X => M.entry i j) hB
    simp only [hentry, dagger_sum, dagger_comp, Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hsum, End.of_sum]
  exact Finset.sum_nonneg fun m _ => CStarCategory.self_comp_dagger_nonneg _

/-- The family of GNS representations `gnsRep X k φ` is jointly faithful: an element that vanishes
under every `gnsRep X k φ` is zero. -/
theorem eq_zero_of_forall_gnsRep {A : LinkingAlgebra X}
    (h : ∀ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), gnsRep X k φ A = 0) : A = 0 := by
  rw [← norm_eq_zero]
  refine le_antisymm (norm_le_of_forall_gnsRep le_rfl fun k φ => ?_) (norm_nonneg _)
  rw [h k φ, norm_zero]

/-- An element of `LinkingAlgebra X` is positive in the spectral order if its image under every GNS
representation `gnsRep X k φ` is positive. -/
theorem nonneg_of_forall_gnsRep {A : LinkingAlgebra X}
    (h : ∀ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), 0 ≤ gnsRep X k φ A) : 0 ≤ A := by
  -- First show `A` is self-adjoint, then show its negative part `A⁻` vanishes in every GNS rep.
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, ← sub_eq_zero]
    refine eq_zero_of_forall_gnsRep fun k φ => ?_
    simp only [map_sub, map_star, (h k φ).isSelfAdjoint.star_eq, sub_self]
  have hneg : A⁻ = 0 := by
    refine eq_zero_of_forall_gnsRep fun k φ => ?_
    have hmap : gnsRep X k φ (A⁻) = (gnsRep X k φ A)⁻ := by
      rw [CFC.negPart_def, CFC.negPart_def]
      exact NonUnitalStarAlgHomClass.map_cfcₙ (gnsRep X k φ) (·⁻ : ℝ → ℝ) A
    rw [hmap, (CFC.negPart_eq_zero_iff (gnsRep X k φ A)).mpr (h k φ)]
  exact (CFC.negPart_eq_zero_iff A hsa).mp hneg

private theorem gnsRep_nonneg_of_forall_sum_nonneg {A : LinkingAlgebra X}
    (hquad : ∀ (k : ι) (v : (j : ι) → (X k ⟶ X j)),
      0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)))
    (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) : 0 ≤ gnsRep X k φ A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hnn : 0 ≤ ⟪gnsRep X k φ A x, x⟫_ℂ := by
    refine (denseRange_gnsClassMap X k φ).induction_on x
      (isClosed_le continuous_const (by fun_prop)) fun B => ?_
    have h0 : 0 ≤ ⟪gnsClassMap X k φ B, gnsRep X k φ A (gnsClassMap X k φ B)⟫_ℂ := by
      simp only [gnsRep_gnsClassMap, inner_gnsClassMap, cornerFunctional_apply,
        mul_entry, star_entry, Preadditive.sum_comp, Category.assoc]
      exact φ.map_nonneg (hquad k fun j => B.entry j k)
    rw [← inner_conj_symm, ← Complex.star_def, h0.isSelfAdjoint.star_eq]
    exact h0
  obtain ⟨hre, him⟩ := Complex.le_def.mp hnn
  exact ⟨Complex.ext rfl (by simpa using him), hre⟩

/-- Matrix positivity in a C*-category: an element `A : LinkingAlgebra X` is positive in the
spectral order if and only if every quadratic form
`∑ i, ∑ j, v j ≫ A.entry i j ≫ dagger (v i)` is positive in `End (X k)` for all `k : ι` and
`v : (j : ι) → (X k ⟶ X j)`. -/
theorem nonneg_iff {A : LinkingAlgebra X} :
    0 ≤ A ↔ ∀ (k : ι) (v : (j : ι) → (X k ⟶ X j)),
      0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)) :=
  -- Forward: factor `A = star B * B`. Backward: positivity of quadratic forms makes every GNS
  -- representation `gnsRep X k φ A` positive, which forces `0 ≤ A` via `nonneg_of_forall_gnsRep`.
  ⟨fun hA _ v => sum_comp_entry_comp_dagger_nonneg hA v,
   fun hquad => nonneg_of_forall_gnsRep (gnsRep_nonneg_of_forall_sum_nonneg hquad)⟩

/-! ### Recovery of Hom norm and endomorphism positivity from two-object corners -/

/-- The Hom norm of `f : X ⟶ Y` is recovered as the C*-norm of the off-diagonal corner element
`single ![X, Y] 1 0 f` in the two-object linking algebra `LinkingAlgebra ![X, Y]`. -/
theorem norm_single_pair {X Y : C} (f : X ⟶ Y) :
    ‖single ![X, Y] (1 : Fin 2) 0 f‖ = ‖f‖ :=
  norm_single ![X, Y] 1 0 f

/-- Positivity in `End X` is recovered from positivity of its `(0, 0)` corner image in the
two-object linking algebra `LinkingAlgebra ![X, Y]`. -/
theorem end_nonneg_iff_diagHom_pair (X Y : C) (a : End X) :
    0 ≤ a ↔ 0 ≤ diagHom ![X, Y] ℂ 0 a :=
  (diagHom_nonneg_iff ![X, Y] 0).symm

end CStar

end LinkingAlgebra

end TauCeti
