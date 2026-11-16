/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.StarAlgebra.GNS.Bounded
public import TauCeti.CategoryTheory.CStar.Basic

import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TauCeti.Analysis.CStarAlgebra.State.Spectrum

/-!
# Finite linking algebras of C*-categories

Given a finite family of objects `X : ι → C` (in particular `L.get : Fin L.length → C` for a list
`L : List C`), the finite linking algebra `TauCeti.LinkingAlgebra X` consists of matrices whose
`(i, j)` entry is a morphism `X j ⟶ X i`, with operator-order matrix multiplication
`(A * B).entry i k = ∑ j, B.entry j k ≫ A.entry i j` and conjugate-transpose involution
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
`LinkingAlgebra.nonneg_iff`, and recovery of the Hom norm and positivity from two-object corners
`LinkingAlgebra ![X, Y]`.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109,
  Section 1.
-/

public section

open CategoryTheory
open scoped ComplexOrder InnerProductSpace

universe w r v u

namespace TauCeti

/-- The linking algebra associated to a family of objects `X : ι → C`: matrices whose `(i, j)`
entry is a morphism `X j ⟶ X i`, equipped with operator-order multiplication and conjugate-
transpose involution. -/
@[ext]
structure LinkingAlgebra {C : Type u} [Category.{v} C] {ι : Type w} (X : ι → C) where
  /-- The `(i, j)` matrix entry, a morphism `X j ⟶ X i`. -/
  entry : (i j : ι) → (X j ⟶ X i)

namespace LinkingAlgebra

/-! ### Entrywise star, additive, and module structures -/

section Star

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {ι : Type w} {X : ι → C}

instance instStar : Star (LinkingAlgebra X) where
  star A := ⟨fun i j => dagger (A.entry j i)⟩

@[simp] theorem star_entry (A : LinkingAlgebra X) (i j : ι) :
    (star A).entry i j = dagger (A.entry j i) := (rfl)

instance instInvolutiveStar : InvolutiveStar (LinkingAlgebra X) where
  star_involutive A := by ext i j; simp

end Star

section Additive

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type w} {X : ι → C}

instance instZero : Zero (LinkingAlgebra X) where
  zero := ⟨fun _ _ => 0⟩

instance instAdd : Add (LinkingAlgebra X) where
  add A B := ⟨fun i j => A.entry i j + B.entry i j⟩

instance instNeg : Neg (LinkingAlgebra X) where
  neg A := ⟨fun i j => -A.entry i j⟩

instance instSub : Sub (LinkingAlgebra X) where
  sub A B := ⟨fun i j => A.entry i j - B.entry i j⟩

instance instAddCommGroup : AddCommGroup (LinkingAlgebra X) where
  add_assoc _ _ _ := by ext; exact add_assoc _ _ _
  zero_add _ := by ext; exact zero_add _
  add_zero _ := by ext; exact add_zero _
  nsmul n A := ⟨fun i j => n • A.entry i j⟩
  nsmul_zero _ := by ext; exact zero_nsmul _
  nsmul_succ _ _ := by ext; exact succ_nsmul _ _
  zsmul n A := ⟨fun i j => n • A.entry i j⟩
  zsmul_zero' _ := by ext; exact zero_zsmul _
  zsmul_succ' _ _ := by ext; exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' _ _ := by ext; exact SubNegMonoid.zsmul_neg' _ _
  neg_add_cancel _ := by ext; exact neg_add_cancel _
  add_comm _ _ := by ext; exact add_comm _ _
  sub_eq_add_neg _ _ := by ext; exact sub_eq_add_neg _ _

@[simp] theorem zero_entry (i j : ι) : (0 : LinkingAlgebra X).entry i j = 0 := (rfl)
@[simp] theorem add_entry (A B : LinkingAlgebra X) (i j : ι) :
    (A + B).entry i j = A.entry i j + B.entry i j := (rfl)
@[simp] theorem neg_entry (A : LinkingAlgebra X) (i j : ι) : (-A).entry i j = -A.entry i j := (rfl)
@[simp] theorem sub_entry (A B : LinkingAlgebra X) (i j : ι) :
    (A - B).entry i j = A.entry i j - B.entry i j := (rfl)
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

private theorem end_of_sum {Z : C} {κ : Type*} (s : Finset κ) (f : κ → (Z ⟶ Z)) :
    End.of (∑ a ∈ s, f a) = ∑ a ∈ s, End.of (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

instance instStarAddMonoid [DaggerCategory C] [DaggerPreadditive C] :
    StarAddMonoid (LinkingAlgebra X) where
  star_add A B := by ext i j; simp

section Linear

variable {R : Type r} [Semiring R] [CategoryTheory.Linear R C]

instance instSMul : SMul R (LinkingAlgebra X) where
  smul c A := ⟨fun i j => c • A.entry i j⟩

@[simp] theorem smul_entry (c : R) (A : LinkingAlgebra X) (i j : ι) :
    (c • A).entry i j = c • A.entry i j := (rfl)

instance instModule : Module R (LinkingAlgebra X) where
  one_smul _ := by ext; exact one_smul R _
  mul_smul _ _ _ := by ext; exact mul_smul _ _ _
  smul_zero _ := by ext; exact smul_zero _
  smul_add _ _ _ := by ext; exact smul_add _ _ _
  add_smul _ _ _ := by ext; exact add_smul _ _ _
  zero_smul _ := by ext; exact zero_smul R _

instance instStarModule [Star R] [DaggerCategory C] [DaggerLinear R C] :
    StarModule R (LinkingAlgebra X) where
  star_smul c A := by ext i j; simp

end Linear

end Additive

/-! ### Identity, matrix units, and corner projections -/

section OneAndSingle

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type w} [DecidableEq ι] {X : ι → C}

instance instOne : One (LinkingAlgebra X) where
  one := ⟨fun i j => if h : i = j then eqToHom (congrArg X h.symm) else 0⟩

@[simp] theorem one_entry (i j : ι) :
    (1 : LinkingAlgebra X).entry i j =
      if h : i = j then eqToHom (congrArg X h.symm) else 0 := (rfl)

variable (X)

/-- The matrix unit with entry `f : X j ⟶ X i` at position `(i, j)` and `0` elsewhere. -/
def single (i j : ι) (f : X j ⟶ X i) : LinkingAlgebra X where
  entry i' j' :=
    if hi : i' = i then
      if hj : j' = j then eqToHom (congrArg X hj) ≫ f ≫ eqToHom (congrArg X hi.symm) else 0
    else 0

/-- The `(i, j)` entry of `single X i j f` is `f`. -/
@[simp] theorem single_entry_self (i j : ι) (f : X j ⟶ X i) :
    (single X i j f).entry i j = f := by simp [single]

/-- Off-row entries of `single X i j f` vanish. -/
theorem single_entry_of_ne_left {i j i' j' : ι} (hi : i' ≠ i) (f : X j ⟶ X i) :
    (single X i j f).entry i' j' = 0 := by simp [single, hi]

/-- Off-column entries of `single X i j f` vanish. -/
theorem single_entry_of_ne_right {i j i' j' : ι} (hj : j' ≠ j) (f : X j ⟶ X i) :
    (single X i j f).entry i' j' = 0 := by simp [single, hj]

/-- `single X i j` sends `0` to `0`. -/
@[simp] theorem single_zero (i j : ι) : single X i j 0 = 0 := by
  ext i' j'; simp only [single, zero_entry]; split_ifs <;> simp

/-- `single X i j` is additive. -/
@[simp] theorem single_add (i j : ι) (f g : X j ⟶ X i) :
    single X i j (f + g) = single X i j f + single X i j g := by
  ext i' j'; simp only [single, add_entry]; split_ifs <;> simp

/-- `single X i j` preserves negation. -/
@[simp] theorem single_neg (i j : ι) (f : X j ⟶ X i) :
    single X i j (-f) = -single X i j f := by
  ext i' j'; simp only [single, neg_entry]; split_ifs <;> simp

/-- `single X i j` preserves subtraction. -/
@[simp] theorem single_sub (i j : ι) (f g : X j ⟶ X i) :
    single X i j (f - g) = single X i j f - single X i j g := by
  rw [sub_eq_add_neg, single_add, single_neg, ← sub_eq_add_neg]

/-- `single X i j` is linear with respect to scalar multiplication. -/
@[simp] theorem single_smul {R : Type r} [Semiring R] [CategoryTheory.Linear R C]
    (i j : ι) (c : R) (f : X j ⟶ X i) :
    single X i j (c • f) = c • single X i j f := by
  ext i' j'; simp only [single, smul_entry]; split_ifs <;> simp

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

/-- The `i`-th diagonal corner projection `single X i i (𝟙 (X i))` in `LinkingAlgebra X`. -/
def proj (i : ι) : LinkingAlgebra X := single X i i (𝟙 (X i))

@[simp] theorem proj_entry_self (i : ι) : (proj X i).entry i i = 𝟙 (X i) :=
  single_entry_self X i i (𝟙 (X i))

@[simp] theorem star_proj [DaggerCategory C] [DaggerPreadditive C] (i : ι) :
    star (proj X i) = proj X i := by simp [proj]

/-- Each diagonal corner projection is self-adjoint. -/
theorem isSelfAdjoint_proj [DaggerCategory C] [DaggerPreadditive C] (i : ι) :
    IsSelfAdjoint (proj X i) := star_proj X i

end OneAndSingle

/-! ### Finite linking ring, star-algebra, and diagonal embeddings -/

section Mul

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type w} [Fintype ι] {X : ι → C}

instance instMul : Mul (LinkingAlgebra X) where
  mul A B := ⟨fun i k => ∑ j : ι, B.entry j k ≫ A.entry i j⟩

@[simp] theorem mul_entry (A B : LinkingAlgebra X) (i k : ι) :
    (A * B).entry i k = ∑ j : ι, B.entry j k ≫ A.entry i j := (rfl)

end Mul

section Ring

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] {X : ι → C}

private theorem sum_comp_one_entry {Z : C} (f : (j : ι) → (Z ⟶ X j)) (i : ι) :
    (∑ j : ι, f j ≫ (1 : LinkingAlgebra X).entry i j) = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem sum_one_entry_comp {Z : C} (f : (j : ι) → (X j ⟶ Z)) (k : ι) :
    (∑ j : ι, (1 : LinkingAlgebra X).entry j k ≫ f j) = f k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · intro hk; exact absurd (Finset.mem_univ k) hk

instance instRing : Ring (LinkingAlgebra X) where
  toAddCommGroup := instAddCommGroup
  mul_assoc A B D := by
    ext i l
    simp only [mul_entry, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    exact Finset.sum_comm
  one_mul A := by ext i k; exact sum_comp_one_entry (fun j => A.entry j k) i
  mul_one A := by ext i k; exact sum_one_entry_comp (fun j => A.entry i j) k
  left_distrib A B D := by ext i k; simp [Preadditive.add_comp, Finset.sum_add_distrib]
  right_distrib A B D := by ext i k; simp [Preadditive.comp_add, Finset.sum_add_distrib]
  zero_mul A := by ext i k; simp
  mul_zero A := by ext i k; simp

section Algebra

variable {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]

instance instAlgebra : Algebra R (LinkingAlgebra X) where
  algebraMap :=
    { toFun := fun c => c • (1 : LinkingAlgebra X)
      map_one' := one_smul R _
      map_mul' := fun a b => by
        ext i k
        simp only [smul_entry, mul_entry, Linear.comp_smul, Linear.smul_comp, ← Finset.smul_sum]
        rw [sum_comp_one_entry (fun j => (1 : LinkingAlgebra X).entry j k) i, mul_smul]
      map_zero' := zero_smul R _
      map_add' := fun a b => add_smul a b _ }
  commutes' c A := by
    ext i k
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_entry, smul_entry,
      Linear.comp_smul, Linear.smul_comp, ← Finset.smul_sum]
    rw [sum_comp_one_entry (fun j => A.entry j k) i, sum_one_entry_comp (fun j => A.entry i j) k]
  smul_def' c A := by
    ext i k
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_entry, smul_entry,
      Linear.comp_smul, ← Finset.smul_sum]
    rw [sum_comp_one_entry (fun j => A.entry j k) i]

@[simp] theorem algebraMap_entry (c : R) (i j : ι) :
    (algebraMap R (LinkingAlgebra X) c).entry i j =
      if h : i = j then c • eqToHom (congrArg X h.symm) else 0 := by
  change (c • (1 : LinkingAlgebra X)).entry i j = _
  simp only [smul_entry, one_entry]
  split_ifs <;> simp

end Algebra

instance instStarRing [DaggerCategory C] [DaggerPreadditive C] : StarRing (LinkingAlgebra X) where
  star_mul A B := by ext i k; simp [dagger_sum]
  star_add := star_add

variable (X)

/-- Multiplying compatible matrix units composes their entries in operator order. -/
@[simp] theorem single_mul_single_same (i j k : ι) (f : X j ⟶ X i) (g : X k ⟶ X j) :
    single X i j f * single X j k g = single X i k (g ≫ f) := by
  ext i' k'
  by_cases hi : i' = i
  · subst hi
    by_cases hk : k' = k
    · subst hk
      simp only [mul_entry, single_entry_self]
      rw [Finset.sum_eq_single j]
      · simp
      · intro m _ hm; simp [single_entry_of_ne_right X hm]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    · simp only [mul_entry, single_entry_of_ne_right X hk]
      simp
  · simp only [mul_entry, single_entry_of_ne_left X hi]
    simp

/-- Multiplying incompatible matrix units gives `0`. -/
theorem single_mul_single_of_ne {i j j' k : ι} (h : j ≠ j') (f : X j ⟶ X i) (g : X k ⟶ X j') :
    single X i j f * single X j' k g = 0 := by
  ext i' k'
  simp only [mul_entry, zero_entry]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m = j
  · subst hm; simp [single_entry_of_ne_left X h]
  · simp [single_entry_of_ne_right X hm]

/-- Every element of `LinkingAlgebra X` decomposes as the sum of its matrix units. -/
theorem eq_sum_single (A : LinkingAlgebra X) :
    A = ∑ i : ι, ∑ j : ι, single X i j (A.entry i j) := by
  ext i k
  simp only [sum_entry]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; exact single_entry_of_ne_right X (Ne.symm hj) _
    · intro hk; exact absurd (Finset.mem_univ k) hk
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun j _ => single_entry_of_ne_left X (Ne.symm hi') _
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Corner projections are mutually orthogonal idempotents. -/
theorem proj_mul_proj (i j : ι) :
    proj X i * proj X j = if i = j then proj X i else 0 := by
  by_cases h : i = j
  · subst h; simp [proj]
  · simp [proj, h, single_mul_single_of_ne X h]

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
    rw [dite_eq_left rfl, Finset.sum_eq_single i]
    · simp [proj]
    · intro k _ hk; exact single_entry_of_ne_left X (Ne.symm hk) _
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · rw [dite_eq_right hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk; exact single_entry_of_ne_right X (Ne.symm hij) _
    · exact single_entry_of_ne_left X (Ne.symm hk) _

/-- Left-right compression by `proj X i` and `proj X j` extracts the `(i, j)` matrix unit. -/
@[simp] theorem proj_mul_mul_proj (A : LinkingAlgebra X) (i j : ι) :
    proj X i * A * proj X j = single X i j (A.entry i j) := by
  conv_lhs => rw [eq_sum_single X A]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [proj]
    · intro j' _ hj'
      simp [proj, single_mul_single_of_ne X hj']
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun j' _ => by
      simp [proj, single_mul_single_of_ne X (Ne.symm hi')]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The non-unital star-algebra embedding of the `i`-th endomorphism algebra `End (X i)` into
`LinkingAlgebra X` as the `(i, i)` diagonal corner. -/
def diagHom (R : Type r) [CommSemiring R] [CategoryTheory.Linear R C]
    [DaggerCategory C] [DaggerPreadditive C] (i : ι) :
    End (X i) →⋆ₙₐ[R] LinkingAlgebra X where
  toFun a := single X i i a.asHom
  map_zero' := single_zero X i i
  map_add' a b := single_add X i i a.asHom b.asHom
  map_smul' c a := single_smul X i i c a.asHom
  map_mul' a b := by
    change single X i i (b.asHom ≫ a.asHom) = single X i i a.asHom * single X i i b.asHom
    exact (single_mul_single_same X i i i a.asHom b.asHom).symm
  map_star' a := (star_single X i i a.asHom).symm

@[simp] theorem diagHom_apply {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]
    [DaggerCategory C] [DaggerPreadditive C] (i : ι) (a : End (X i)) :
    diagHom X R i a = single X i i a.asHom := (rfl)

/-- The diagonal embedding `diagHom X R i` is injective. -/
theorem diagHom_injective {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]
    [DaggerCategory C] [DaggerPreadditive C] (i : ι) :
    Function.Injective (diagHom X R i) := by
  intro a b h
  exact End.ext (single_injective X i i h)

/-- An element of `LinkingAlgebra X` lies in the range of `diagHom X R i` if and only if it is
fixed by compression by `proj X i`. -/
theorem mem_range_diagHom_iff {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]
    [DaggerCategory C] [DaggerPreadditive C] (i : ι) (A : LinkingAlgebra X) :
    A ∈ Set.range (diagHom X R i) ↔ proj X i * A * proj X i = A := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [diagHom]
  · intro h
    refine ⟨End.of (A.entry i i), ?_⟩
    simpa only [diagHom_apply, ← proj_mul_mul_proj] using h

/-- The `(i, j)` corner submodule `{ A : LinkingAlgebra X | proj X i * A * proj X j = A }`. -/
def cornerSubmodule (R : Type r) [CommSemiring R] [CategoryTheory.Linear R C] (i j : ι) :
    Submodule R (LinkingAlgebra X) where
  carrier := { A : LinkingAlgebra X | proj X i * A * proj X j = A }
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    change proj X i * A * proj X j = A at hA
    change proj X i * B * proj X j = B at hB
    change proj X i * (A + B) * proj X j = A + B
    rw [mul_add, add_mul, hA, hB]
  smul_mem' c {A} hA := by
    change proj X i * A * proj X j = A at hA
    change proj X i * (c • A) * proj X j = c • A
    rw [mul_smul_comm, smul_mul_assoc, hA]

@[simp] theorem mem_cornerSubmodule {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]
    (i j : ι) (A : LinkingAlgebra X) :
    A ∈ cornerSubmodule X R i j ↔ proj X i * A * proj X j = A :=
  Iff.rfl

end Ring

/-- Multiplying the `(1, 0)` corner element `single ![X, Y] 1 0 f` on the left by its star yields
the diagonal embedding of `End.of (f ≫ dagger f)` in `LinkingAlgebra ![X, Y]`. -/
theorem star_mul_single_pair {C : Type u} [Category.{v} C] [Preadditive C]
    {R : Type r} [CommSemiring R] [CategoryTheory.Linear R C]
    [DaggerCategory C] [DaggerPreadditive C] {X Y : C} (f : X ⟶ Y) :
    star (single ![X, Y] (1 : Fin 2) 0 f) * single ![X, Y] (1 : Fin 2) 0 f =
      diagHom ![X, Y] R 0 (End.of (f ≫ dagger f)) :=
  (congrArg (· * single ![X, Y] (1 : Fin 2) 0 f) (star_single ![X, Y] (1 : Fin 2) 0 f)).trans
    (single_mul_single_same ![X, Y] 0 1 0 (dagger f) f)

/-! ### Corner positive functionals, GNS representations, and C*-algebra structure -/

section CStar

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

variable (X : ι → C)

/-- The `StarPositiveFunctional` on `LinkingAlgebra X` obtained by composing a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ` with extraction of the `(k, k)` diagonal corner. -/
def cornerFunctional (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) :
    StarPositiveFunctional (LinkingAlgebra X) where
  toLinearMap :=
    { toFun A := φ (End.of (A.entry k k))
      map_add' A B := by simp only [add_entry, End.of_add, map_add]
      map_smul' c A := by simp only [smul_entry, End.of_smul, map_smul, RingHom.id_apply] }
  square_nonneg A := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_entry, star_entry, end_of_sum, map_sum]
    exact Finset.sum_nonneg fun j _ =>
      φ.map_nonneg (CStarCategory.self_comp_dagger_nonneg (A.entry j k))

@[simp] theorem cornerFunctional_apply (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) (A : LinkingAlgebra X) :
    cornerFunctional X k φ A = φ (End.of (A.entry k k)) := (rfl)

private theorem cornerFunctional_single_bound (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ)
    (i j : ι) (f : X j ⟶ X i) (B : LinkingAlgebra X) :
    cornerFunctional X k φ (star B * star (single X i j f) * single X i j f * B) ≤
      (‖f‖ : ℂ) ^ 2 * cornerFunctional X k φ (star B * B) := by
  have hprod_entry (m : ι) :
      (single X i j f * B).entry m k =
        if hm : m = i then B.entry j k ≫ f ≫ eqToHom (congrArg X hm.symm) else 0 := by
    simp only [mul_entry]
    by_cases hm : m = i
    · subst hm
      rw [dite_eq_left rfl, Finset.sum_eq_single j]
      · simp
      · intro l _ hl; simp [single_entry_of_ne_right X hl]
      · intro hj; exact absurd (Finset.mem_univ j) hj
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
    rw [Finset.sum_eq_single i]
    · have hi := hprod_entry i
      simp only [↓reduceDIte, eqToHom_refl, Category.comp_id] at hi
      rw [hi]
    · intro m _ hm
      rw [hprod_entry m, dite_eq_right hm]
      simp
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hrhs :
      End.of ((star B * B).entry k k) =
        ∑ m : ι, End.of (B.entry m k ≫ dagger (B.entry m k)) := by
    simp only [mul_entry, star_entry, end_of_sum]
  have hle_end :
      End.of ((star B * star (single X i j f) * single X i j f * B).entry k k) ≤
        (‖f‖ ^ 2 : ℝ) • End.of ((star B * B).entry k k) := by
    rw [hlhs, hrhs]
    refine (CStarCategory.comp_self_comp_dagger_le (B.entry j k) f).trans ?_
    refine smul_le_smul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum
      (fun m _ => CStarCategory.self_comp_dagger_nonneg (B.entry m k)) (Finset.mem_univ j)
  have hφ := OrderHomClass.mono φ hle_end
  rw [LinearMapClass.map_smul_of_tower, Complex.real_smul, Complex.ofReal_pow] at hφ
  exact hφ

private theorem continuous_leftMul_single (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ)
    (i j : ι) (f : X j ⟶ X i) :
    Continuous ((cornerFunctional X k φ).leftMul (single X i j f)) :=
  ((cornerFunctional X k φ).continuous_leftMul_iff _).mpr
    ⟨‖f‖, norm_nonneg f, cornerFunctional_single_bound X k φ i j f⟩

/-- Every element of `LinkingAlgebra X` acts continuously on the algebraic GNS space of
`cornerFunctional X k φ`. -/
theorem continuous_leftMul_cornerFunctional (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ)
    (A : LinkingAlgebra X) :
    Continuous ((cornerFunctional X k φ).leftMul A) := by
  rw [← (cornerFunctional X k φ).mem_boundedSubalgebra, eq_sum_single X A]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  rw [(cornerFunctional X k φ).mem_boundedSubalgebra]
  exact continuous_leftMul_single X k φ i j (A.entry i j)

/-- The completed GNS Hilbert space of `LinkingAlgebra X` associated to a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ`. -/
def GNS (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) : Type (max v w) :=
  (cornerFunctional X k φ).HilbertGNS

noncomputable instance instGNSNormedAddCommGroup (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) :
    NormedAddCommGroup (GNS X k φ) :=
  inferInstanceAs (NormedAddCommGroup (cornerFunctional X k φ).HilbertGNS)

noncomputable instance instGNSInnerProductSpace (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) :
    InnerProductSpace ℂ (GNS X k φ) :=
  inferInstanceAs (InnerProductSpace ℂ (cornerFunctional X k φ).HilbertGNS)

instance instGNSCompleteSpace (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) :
    CompleteSpace (GNS X k φ) :=
  inferInstanceAs (CompleteSpace (cornerFunctional X k φ).HilbertGNS)

/-- The canonical unital GNS star-representation of `LinkingAlgebra X` induced by a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ`, built via
`TauCeti.StarPositiveFunctional.boundedRepresentation`. -/
noncomputable def gnsRep (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) :
    LinkingAlgebra X →⋆ₐ[ℂ] (GNS X k φ →L[ℂ] GNS X k φ) :=
  (cornerFunctional X k φ).boundedRepresentation (continuous_leftMul_cornerFunctional X k φ)

/-- Each matrix unit acts on `gnsRep X k φ` with operator norm at most the norm of its entry. -/
theorem norm_gnsRep_single_le (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) (i j : ι) (f : X j ⟶ X i) :
    ‖gnsRep X k φ (single X i j f)‖ ≤ ‖f‖ := by
  change ‖(cornerFunctional X k φ).boundedRepresentation
    (continuous_leftMul_cornerFunctional X k φ) (single X i j f)‖ ≤ ‖f‖
  rw [StarPositiveFunctional.boundedRepresentation_apply]
  exact ((cornerFunctional X k φ).norm_hilbertLeftMul_le_iff
    (continuous_leftMul_cornerFunctional X k φ (single X i j f)) (norm_nonneg f)).mpr
    (cornerFunctional_single_bound X k φ i j f)

/-- Each GNS representation is bounded by the entrywise `ℓ¹` norm. -/
theorem norm_gnsRep_le_sum (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) (A : LinkingAlgebra X) :
    ‖gnsRep X k φ A‖ ≤ ∑ i : ι, ∑ j : ι, ‖A.entry i j‖ :=
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

/-- The C*-norm on `LinkingAlgebra X`, defined as the supremum of operator norms over all GNS
representations induced by positive linear functionals on `End (X k)`. -/
noncomputable instance instNorm : Norm (LinkingAlgebra X) where
  norm A := ⨆ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖

variable {X}

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
    let ψ : StarPositiveFunctional (LinkingAlgebra X) := cornerFunctional X j φ
    have hψ1 : ψ 1 = 1 := by
      change φ (End.of ((1 : LinkingAlgebra X).entry j j)) = 1
      simpa [one_entry, φ] using hφ1
    have hcyc : ‖ψ.hilbertCyclicVector‖ = 1 := ψ.norm_hilbertCyclicVector hψ1
    have hge : ‖A.entry i j‖ ^ 2 ≤ ‖gnsRep X j φ A ψ.hilbertCyclicVector‖ ^ 2 := by
      change ‖A.entry i j‖ ^ 2 ≤
        ‖ψ.boundedRepresentation (continuous_leftMul_cornerFunctional X j φ) A
          ψ.hilbertCyclicVector‖ ^ 2
      rw [StarPositiveFunctional.boundedRepresentation_hilbertCyclicVector,
        ψ.norm_hilbertClassMap_sq]
      have hre : (ψ (star A * A)).re =
          ∑ m : ι, (φ (End.of (A.entry m j ≫ dagger (A.entry m j)))).re := by
        simp only [ψ, cornerFunctional_apply, mul_entry, star_entry, end_of_sum, map_sum]
        exact map_sum Complex.reAddGroupHom _ _
      rw [hre]
      have hterm : ‖A.entry i j‖ ^ 2 = (φ (End.of (A.entry i j ≫ dagger (A.entry i j)))).re := by
        simpa only [a, φ, PositiveContinuousLinearMap.coe_toPositiveLinearMap, End.norm_of,
          CStarCategory.norm_self_comp_dagger, Complex.ofReal_re] using
          (congrArg Complex.re hφa).symm
      rw [hterm]
      exact Finset.single_le_sum (fun m _ =>
        (RCLike.nonneg_iff.mp (φ.map_nonneg
          (CStarCategory.self_comp_dagger_nonneg (A.entry m j)))).1) (Finset.mem_univ i)
    have hle : ‖gnsRep X j φ A ψ.hilbertCyclicVector‖ ≤ ‖A‖ :=
      calc ‖gnsRep X j φ A ψ.hilbertCyclicVector‖
          ≤ ‖gnsRep X j φ A‖ * ‖(ψ.hilbertCyclicVector : GNS X j φ)‖ :=
            (gnsRep X j φ A).le_opNorm _
        _ = ‖gnsRep X j φ A‖ := by rw [hcyc, mul_one]
        _ ≤ ‖A‖ := norm_gnsRep_le j φ A
    exact (sq_le_sq₀ (norm_nonneg _) hA_nn).mp
      (hge.trans (pow_le_pow_left₀ (norm_nonneg _) hle 2))

private theorem norm_nonneg_aux (A : LinkingAlgebra X) : 0 ≤ ‖A‖ := by
  by_cases hι : Nonempty ι
  · obtain ⟨k⟩ := hι; exact (norm_nonneg (gnsRep X k 0 A)).trans (norm_gnsRep_le k 0 A)
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    change 0 ≤ ⨆ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖; simp

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
    have hsub : A - D = (A - B) + (B - D) := by abel
    rw [hsub]; exact norm_add_le_aux (A - B) (B - D)
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
      have hd := hN m hm n hn
      rw [dist_eq_norm] at hd
      exact (norm_entry_le (u m - u n) i j).trans_lt hd
    choose L hL using fun i j => cauchySeq_tendsto_of_complete (hcoord i j)
    refine ⟨⟨L⟩, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
    have hsum : Filter.Tendsto (fun n => ∑ i : ι, ∑ j : ι, ‖(u n).entry i j - L i j‖)
        Filter.atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
          tendsto_finsetSum (Finset.univ : Finset ι) fun j _ =>
            tendsto_iff_norm_sub_tendsto_zero.mp (hL i j)
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hsum) ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have hle := norm_le_sum_norm_entry (u n - ⟨L⟩)
    have h0 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h0
    exact hle.trans_lt (by simpa only [sub_entry] using h0)

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

variable (X)

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
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' A := by
    have hA : A.1 = single X i j (A.1.entry i j) := by
      simpa only [mem_cornerSubmodule, proj_mul_mul_proj] using A.2.symm
    change ‖A.1.entry i j‖ = ‖A.1‖
    conv_rhs => rw [hA]
    exact (norm_single X i j _).symm

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

/-! ### Matrix positivity characterization -/

variable {X}

/-- A positive element `A` of `LinkingAlgebra X` defines a positive quadratic form
`v ↦ ∑ i, ∑ j, v j ≫ A.entry i j ≫ dagger (v i)` in `End Z` for every object `Z : C` and every
column `v : (j : ι) → (Z ⟶ X j)`. -/
theorem nonneg_quadratic {A : LinkingAlgebra X} (hA : 0 ≤ A) {Z : C}
    (v : (j : ι) → (Z ⟶ X j)) :
    0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)) := by
  let B : LinkingAlgebra X := CFC.sqrt A
  have hB : star B * B = A := by
    rw [(CFC.sqrt_nonneg A).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self A hA]
  have hsum : ∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i) =
      ∑ m : ι, (∑ j : ι, v j ≫ B.entry m j) ≫ dagger (∑ i : ι, v i ≫ B.entry m i) := by
    have hentry (i j : ι) : A.entry i j = ∑ m : ι, B.entry m j ≫ dagger (B.entry m i) := by
      simpa only [mul_entry, star_entry] using
        congrArg (fun M : LinkingAlgebra X => M.entry i j) hB.symm
    simp only [hentry, dagger_sum, dagger_comp, Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hsum, end_of_sum]
  exact Finset.sum_nonneg fun m _ => CStarCategory.self_comp_dagger_nonneg _

/-- Matrix positivity in a C*-category: an element `A : LinkingAlgebra X` is positive in the
spectral order if and only if every quadratic form
`∑ i, ∑ j, v j ≫ A.entry i j ≫ dagger (v i)` is positive in `End (X k)` for all `k : ι` and
`v : (j : ι) → (X k ⟶ X j)`. -/
theorem nonneg_iff {A : LinkingAlgebra X} :
    0 ≤ A ↔ ∀ (k : ι) (v : (j : ι) → (X k ⟶ X j)),
      0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)) := by
  refine ⟨fun hA k v => nonneg_quadratic hA v, fun hquad => ?_⟩
  have hrep_pos (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) : 0 ≤ gnsRep X k φ A := by
    let ψ := cornerFunctional X k φ
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ← ContinuousLinearMap.isPositive_toLinearMap_iff,
      LinearMap.isPositive_iff_complex]
    have hinner_nn (x : GNS X k φ) : 0 ≤ ⟪x, gnsRep X k φ A x⟫_ℂ := by
      have hclosed : IsClosed { x : GNS X k φ | 0 ≤ ⟪x, gnsRep X k φ A x⟫_ℂ } := by
        have hC : IsClosed { z : ℂ | 0 ≤ z } := by
          have heq : { z : ℂ | 0 ≤ z } = { z : ℂ | 0 ≤ z.re } ∩ { z : ℂ | z.im = 0 } := by
            ext z; simp [Complex.le_def, eq_comm]
          rw [heq]
          exact (isClosed_le continuous_const Complex.continuous_re).inter
            (isClosed_eq Complex.continuous_im continuous_const)
        exact hC.preimage (by fun_prop)
      have hsub : Set.range (ψ.hilbertClassMap : LinkingAlgebra X → GNS X k φ) ⊆
          { x : GNS X k φ | 0 ≤ ⟪x, gnsRep X k φ A x⟫_ℂ } := by
        rintro _ ⟨B, rfl⟩
        change 0 ≤ ⟪ψ.hilbertClassMap B,
          ψ.boundedRepresentation (continuous_leftMul_cornerFunctional X k φ) A
            (ψ.hilbertClassMap B)⟫_ℂ
        simp only [StarPositiveFunctional.boundedRepresentation_hilbertClassMap,
          ψ.inner_hilbertClassMap, ψ, cornerFunctional_apply, mul_entry, star_entry,
          Preadditive.sum_comp, Category.assoc]
        exact φ.map_nonneg (hquad k fun j => B.entry j k)
      have hmem : x ∈ closure (Set.range (ψ.hilbertClassMap : LinkingAlgebra X → GNS X k φ)) := by
        rw [ψ.denseRange_hilbertClassMap.closure_eq]; trivial
      exact hclosed.closure_subset_iff.mpr hsub hmem
    intro x
    have hconj : 0 ≤ ⟪gnsRep X k φ A x, x⟫_ℂ := by
      have hnn := hinner_nn x
      rw [← inner_conj_symm (x := gnsRep X k φ A x) (y := x),
        Complex.conj_eq_iff_im.mpr (Complex.le_def.mp hnn).2.symm]
      exact hnn
    obtain ⟨hre, him⟩ := Complex.le_def.mp hconj
    exact ⟨Complex.ext rfl (by simpa using him), hre⟩
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, ← sub_eq_zero, ← norm_eq_zero]
    refine le_antisymm (norm_le_of_forall_gnsRep le_rfl fun k φ => ?_) (norm_nonneg _)
    simp [map_sub, map_star, (hrep_pos k φ).isSelfAdjoint.star_eq]
  have hneg : A⁻ = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm (norm_le_of_forall_gnsRep le_rfl fun k φ => ?_) (norm_nonneg _)
    have hcont : Continuous (gnsRep X k φ) :=
      AddMonoidHomClass.continuous_of_bound (gnsRep X k φ) 1 fun B => by
        simpa only [one_mul] using norm_gnsRep_le k φ B
    have hmap : gnsRep X k φ (A⁻) = (gnsRep X k φ A)⁻ := by
      rw [CFC.negPart_def, CFC.negPart_def]
      exact NonUnitalStarAlgHomClass.map_cfcₙ (gnsRep X k φ) (·⁻ : ℝ → ℝ) A (hφ := hcont)
    rw [hmap, (CFC.negPart_eq_zero_iff (gnsRep X k φ A)).mpr (hrep_pos k φ), norm_zero]
  exact (CFC.negPart_eq_zero_iff A hsa).mp hneg

/-! ### Recovery of Hom norm and positivity from two-object corners -/

/-- The Hom norm of `f : X ⟶ Y` is recovered as the C*-norm of the off-diagonal corner element
`single ![X, Y] 1 0 f` in the two-object linking algebra `LinkingAlgebra ![X, Y]`. -/
theorem norm_single_pair {X Y : C} (f : X ⟶ Y) :
    ‖single ![X, Y] (1 : Fin 2) 0 f‖ = ‖f‖ :=
  norm_single ![X, Y] 1 0 f

/-- Positivity of `f ≫ dagger f` in `End X` is recovered from positivity of `b⋆ * b` in the
two-object linking algebra `LinkingAlgebra ![X, Y]`. -/
theorem self_comp_dagger_nonneg_iff_pair {X Y : C} (f : X ⟶ Y) :
    0 ≤ End.of (f ≫ dagger f) ↔
      0 ≤ star (single ![X, Y] (1 : Fin 2) 0 f) * single ![X, Y] (1 : Fin 2) 0 f := by
  rw [star_mul_single_pair (R := ℂ), diagHom_nonneg_iff]
  rfl

/-- Positivity in `End X` is recovered from positivity of its `(0, 0)` corner image in the
two-object linking algebra `LinkingAlgebra ![X, Y]`. -/
theorem end_nonneg_iff_diagHom_pair (X Y : C) (a : End X) :
    0 ≤ a ↔ 0 ≤ diagHom ![X, Y] ℂ 0 a :=
  (diagHom_nonneg_iff ![X, Y] 0).symm

end CStar

end LinkingAlgebra

end TauCeti
