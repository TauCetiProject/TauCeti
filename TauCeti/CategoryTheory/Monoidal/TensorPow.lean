/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Tensor powers of an object of a monoidal category

For an object `X` of a monoidal category `C`, `TauCeti.tensorPow X n` is the `n`-fold tensor power
of `X`, nested to the right: `tensorPow X 0 = 𝟙_ C` and `tensorPow X (n + 1) = X ⊗ tensorPow X n`.

Splitting a tensor power into two blocks is the isomorphism
`TauCeti.tensorPowAddIso X m n : tensorPow X m ⊗ tensorPow X n ≅ tensorPow X (n + m)`, defined by
recursion on `m`. The index `n + m` is the one for which this recursion is definitional; comparing
with other ways of writing the same exponent goes through `eqToHom`. The comparison is associative
(`TauCeti.tensorPowAddIso_assoc`) and unital. Appending a factor on the right is the isomorphism
`TauCeti.tensorPowSuccIso X n : tensorPow X n ⊗ X ≅ tensorPow X (n + 1)`, which is compatible
with the block decompositions on either side.

These comparisons are what is needed to move factors of a tensor power from one end to the other,
for example to state that rotating the factors of `tensorPow X n` one at a time `n` times is the
identity.

## Main declarations

* `TauCeti.tensorPow`: the tensor powers of an object;
* `TauCeti.tensorPowAddIso` and `TauCeti.tensorPowAddIso_assoc`: the block decomposition
  isomorphisms and their associativity;
* `TauCeti.tensorPowSuccIso`: appending a factor on the right, with its compatibilities
  `TauCeti.tensorPowSuccIso_hom_whiskerRight_tensorPowAddIso_hom` and
  `TauCeti.tensorPowAddIso_hom_whiskerRight_tensorPowSuccIso_hom`.
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

-- Exposed and reducible: statements about morphisms into `tensorPow X (n + 1)` use it as
-- `X ⊗ tensorPow X n`, and `tensorPow X 0` as `𝟙_ C`, without rewriting the objects.
/-- The `n`-th tensor power of `X`, nested to the right: `tensorPow X 0 = 𝟙_ C` and
`tensorPow X (n + 1) = X ⊗ tensorPow X n`. -/
@[expose, reducible]
def tensorPow (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => X ⊗ tensorPow X n

/-- The zeroth tensor power is the unit. -/
theorem tensorPow_zero (X : C) : tensorPow X 0 = 𝟙_ C :=
  (rfl)

/-- The tensor power `tensorPow X (n + 1)` is `X ⊗ tensorPow X n`. -/
theorem tensorPow_succ (X : C) (n : ℕ) : tensorPow X (n + 1) = X ⊗ tensorPow X n :=
  (rfl)

/-- The block decomposition `tensorPow X m ⊗ tensorPow X n ≅ tensorPow X (n + m)` of a tensor
power, built from associators and the left unitor by recursion on `m`. -/
def tensorPowAddIso (X : C) : (m n : ℕ) → tensorPow X m ⊗ tensorPow X n ≅ tensorPow X (n + m)
  | 0, n => λ_ (tensorPow X n)
  | m + 1, n => α_ X (tensorPow X m) (tensorPow X n) ≪≫ whiskerLeftIso X (tensorPowAddIso X m n)

/-- The block decomposition with an empty first block is the left unitor. -/
@[simp]
theorem tensorPowAddIso_zero (X : C) (n : ℕ) : tensorPowAddIso X 0 n = λ_ (tensorPow X n) :=
  (rfl)

/-- The recursive step of the block decomposition. -/
theorem tensorPowAddIso_succ (X : C) (m n : ℕ) :
    tensorPowAddIso X (m + 1) n =
      α_ X (tensorPow X m) (tensorPow X n) ≪≫ whiskerLeftIso X (tensorPowAddIso X m n) :=
  (rfl)

/-- The recursive step of the block decomposition, on morphisms. -/
theorem tensorPowAddIso_succ_hom (X : C) (m n : ℕ) :
    (tensorPowAddIso X (m + 1) n).hom =
      (α_ X (tensorPow X m) (tensorPow X n)).hom ≫ X ◁ (tensorPowAddIso X m n).hom :=
  (rfl)

/-- The recursive step of the inverse block decomposition. -/
theorem tensorPowAddIso_succ_inv (X : C) (m n : ℕ) :
    (tensorPowAddIso X (m + 1) n).inv =
      X ◁ (tensorPowAddIso X m n).inv ≫ (α_ X (tensorPow X m) (tensorPow X n)).inv :=
  (rfl)

/-- The block decomposition with an empty second block is the right unitor. -/
theorem tensorPowAddIso_zero_right_hom (X : C) (m : ℕ) :
    (tensorPowAddIso X m 0).hom =
      (ρ_ (tensorPow X m)).hom ≫ eqToHom (congrArg (tensorPow X) (Nat.zero_add m).symm) := by
  induction m with
  | zero => exact (unitors_equal).trans (Category.comp_id _).symm
  | succ m ih =>
    rw [tensorPowAddIso_succ_hom, ih]
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_eqToHom]
    simp only [MonoidalCategory.whiskerLeft_rightUnitor, Category.assoc, Nat.zero_add,
      eqToHom_iso_hom_naturality, Iso.hom_inv_id_assoc]
    -- Both sides are an `eqToHom` cast followed by the right unitor of the same object.
    congr 1

/-- The inverse of the block decomposition with an empty second block is the inverse of the right
unitor. -/
theorem tensorPowAddIso_zero_right_inv (X : C) (m : ℕ) :
    (tensorPowAddIso X m 0).inv =
      eqToHom (congrArg (tensorPow X) (Nat.zero_add m)) ≫ (ρ_ (tensorPow X m)).inv :=
  Iso.inv_ext (by simp [tensorPowAddIso_zero_right_hom])

/-- **Associativity of the block decompositions**: splitting `tensorPow X (c + (b + a))` into
three blocks of lengths `a`, `b`, `c` does not depend on the order of the two splittings. -/
theorem tensorPowAddIso_assoc (X : C) (a b c : ℕ) :
    (tensorPowAddIso X a b).hom ▷ tensorPow X c ≫ (tensorPowAddIso X (b + a) c).hom =
      (α_ (tensorPow X a) (tensorPow X b) (tensorPow X c)).hom ≫
        tensorPow X a ◁ (tensorPowAddIso X b c).hom ≫ (tensorPowAddIso X a (c + b)).hom ≫
          eqToHom (congrArg (tensorPow X) (Nat.add_assoc c b a)) := by
  induction a with
  | zero => simp [tensorPowAddIso_zero, leftUnitor_whiskerRight]
  | succ a ih =>
    calc _ = (α_ X (tensorPow X a) (tensorPow X b)).hom ▷ tensorPow X c ≫
          (α_ X (tensorPow X a ⊗ tensorPow X b) (tensorPow X c)).hom ≫
          X ◁ ((tensorPowAddIso X a b).hom ▷ tensorPow X c ≫
            (tensorPowAddIso X (b + a) c).hom) := by
          -- `b + (a + 1)` is definitionally `b + a + 1`, the index of the recursive step.
          rw [show (tensorPowAddIso X (b + (a + 1)) c).hom = _ from
            tensorPowAddIso_succ_hom X (b + a) c, tensorPowAddIso_succ_hom]
          monoidal
      _ = _ := by
          rw [ih]
          simp only [tensorPowAddIso_succ_hom, MonoidalCategory.whiskerLeft_comp,
            MonoidalCategory.whiskerLeft_eqToHom]
          rw [← cancel_mono (eqToHom (congrArg (tensorPow X) (Nat.add_assoc c b (a + 1))).symm)]
          simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          monoidal

/-- The block decomposition is natural in the length of the first block. -/
@[reassoc]
theorem eqToHom_whiskerRight_tensorPowAddIso_hom (X : C) {m m' : ℕ} (h : m = m') (n : ℕ) :
    eqToHom (congrArg (tensorPow X) h) ▷ tensorPow X n ≫ (tensorPowAddIso X m' n).hom =
      (tensorPowAddIso X m n).hom ≫ eqToHom (congrArg (fun k ↦ tensorPow X (n + k)) h) := by
  subst h; simp

/-- The block decomposition is natural in the length of the second block. -/
@[reassoc]
theorem whiskerLeft_eqToHom_tensorPowAddIso_hom (X : C) (m : ℕ) {n n' : ℕ} (h : n = n') :
    tensorPow X m ◁ eqToHom (congrArg (tensorPow X) h) ≫ (tensorPowAddIso X m n').hom =
      (tensorPowAddIso X m n).hom ≫ eqToHom (congrArg (fun k ↦ tensorPow X (k + m)) h) := by
  subst h; simp

/-- Appending a factor on the right: `tensorPow X n ⊗ X ≅ tensorPow X (n + 1)`, the block
decomposition with a second block of length one. -/
def tensorPowSuccIso (X : C) (n : ℕ) : tensorPow X n ⊗ X ≅ tensorPow X (n + 1) :=
  whiskerLeftIso (tensorPow X n) (ρ_ X).symm ≪≫ tensorPowAddIso X n 1 ≪≫
    eqToIso (congrArg (tensorPow X) (Nat.add_comm 1 n))

/-- The formula for appending a factor on the right. -/
theorem tensorPowSuccIso_hom (X : C) (n : ℕ) :
    (tensorPowSuccIso X n).hom = tensorPow X n ◁ (ρ_ X).inv ≫ (tensorPowAddIso X n 1).hom ≫
      eqToHom (congrArg (tensorPow X) (Nat.add_comm 1 n)) :=
  (rfl)

/-- Appending a factor to the first of two blocks and then joining them is joining the factor to
the second block. -/
@[reassoc]
theorem tensorPowSuccIso_hom_whiskerRight_tensorPowAddIso_hom (X : C) (m n : ℕ) :
    (tensorPowSuccIso X m).hom ▷ tensorPow X n ≫ (tensorPowAddIso X (m + 1) n).hom =
      (α_ (tensorPow X m) X (tensorPow X n)).hom ≫ (tensorPowAddIso X m (n + 1)).hom ≫
        eqToHom (congrArg (tensorPow X) (by omega)) := by
  have h := tensorPowAddIso_assoc X m 1 n
  rw [tensorPowSuccIso_hom, comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    eqToHom_whiskerRight_tensorPowAddIso_hom X (Nat.add_comm 1 m), reassoc_of% h]
  rw [← cancel_mono (eqToHom (congrArg (tensorPow X) (by omega : n + (m + 1) = n + 1 + m)))]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [tensorPowAddIso_succ_hom, tensorPowAddIso_zero]
  monoidal

/-- Joining two blocks and then appending a factor is appending the factor to the second block and
then joining. -/
@[reassoc]
theorem tensorPowAddIso_hom_whiskerRight_tensorPowSuccIso_hom (X : C) (m n : ℕ) :
    (tensorPowAddIso X m n).hom ▷ X ≫ (tensorPowSuccIso X (n + m)).hom =
      (α_ (tensorPow X m) (tensorPow X n) X).hom ≫ tensorPow X m ◁ (tensorPowSuccIso X n).hom ≫
        (tensorPowAddIso X m (n + 1)).hom ≫ eqToHom (congrArg (tensorPow X) (by omega)) := by
  have h := tensorPowAddIso_assoc X m n 1
  rw [tensorPowSuccIso_hom, tensorPowSuccIso_hom, ← whisker_exchange_assoc,
    reassoc_of% h, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Category.assoc,
    whiskerLeft_eqToHom_tensorPowAddIso_hom_assoc X m (Nat.add_comm 1 n)]
  rw [← cancel_mono (eqToHom (congrArg (tensorPow X) (by omega : n + m + 1 = 1 + n + m)))]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  monoidal

section Map

/-- The `n`-th tensor power `f ⊗ₘ ⋯ ⊗ₘ f` of a morphism `f : X ⟶ Y`. -/
def tensorPowMap {X Y : C} (f : X ⟶ Y) : (n : ℕ) → tensorPow X n ⟶ tensorPow Y n
  | 0 => 𝟙 (𝟙_ C)
  | n + 1 => f ⊗ₘ tensorPowMap f n

/-- The zeroth tensor power of a morphism is the identity of the unit. -/
@[simp]
theorem tensorPowMap_zero {X Y : C} (f : X ⟶ Y) : tensorPowMap f 0 = 𝟙 (𝟙_ C) :=
  (rfl)

/-- The tensor power `tensorPowMap f (n + 1)` is `f ⊗ₘ tensorPowMap f n`. -/
theorem tensorPowMap_succ {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorPowMap f (n + 1) = f ⊗ₘ tensorPowMap f n :=
  (rfl)

/-- The tensor powers of an identity are identities. -/
@[simp]
theorem tensorPowMap_id (X : C) (n : ℕ) : tensorPowMap (𝟙 X) n = 𝟙 (tensorPow X n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tensorPowMap_succ, ih, id_tensorHom_id]

/-- The tensor powers of a composite are the composites of the tensor powers. -/
@[simp, reassoc]
theorem tensorPowMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    tensorPowMap (f ≫ g) n = tensorPowMap f n ≫ tensorPowMap g n := by
  induction n with
  | zero => exact (Category.comp_id _).symm
  | succ n ih => simp only [tensorPowMap_succ, ih, tensorHom_comp_tensorHom]

/-- The tensor powers of an isomorphism, as an isomorphism. -/
def tensorPowMapIso {X Y : C} (e : X ≅ Y) (n : ℕ) : tensorPow X n ≅ tensorPow Y n where
  hom := tensorPowMap e.hom n
  inv := tensorPowMap e.inv n
  hom_inv_id := by rw [← tensorPowMap_comp, e.hom_inv_id, tensorPowMap_id]
  inv_hom_id := by rw [← tensorPowMap_comp, e.inv_hom_id, tensorPowMap_id]

/-- The tensor powers of an isomorphism, on morphisms. -/
@[simp]
theorem tensorPowMapIso_hom {X Y : C} (e : X ≅ Y) (n : ℕ) :
    (tensorPowMapIso e n).hom = tensorPowMap e.hom n :=
  (rfl)

/-- The tensor powers of an isomorphism, on inverses. -/
@[simp]
theorem tensorPowMapIso_inv {X Y : C} (e : X ≅ Y) (n : ℕ) :
    (tensorPowMapIso e n).inv = tensorPowMap e.inv n :=
  (rfl)

/-- The block decompositions are natural. -/
@[reassoc]
theorem tensorPowAddIso_hom_naturality {X Y : C} (f : X ⟶ Y) (m n : ℕ) :
    (tensorPowMap f m ⊗ₘ tensorPowMap f n) ≫ (tensorPowAddIso Y m n).hom =
      (tensorPowAddIso X m n).hom ≫ tensorPowMap f (n + m) := by
  induction m with
  | zero => simp [tensorPowAddIso_zero, tensorPowMap_zero]
  | succ m ih =>
    -- `n + (m + 1)` is definitionally `n + m + 1`, so `tensorPowMap_succ` applies up to `rfl`;
    -- rewriting the exponent instead would change the type of `tensorPowMap f`.
    rw [tensorPowAddIso_succ_hom, tensorPowAddIso_succ_hom, tensorPowMap_succ,
      show tensorPowMap f (n + (m + 1)) = f ⊗ₘ tensorPowMap f (n + m) from rfl]
    calc _ = (α_ X (tensorPow X m) (tensorPow X n)).hom ≫
          (f ⊗ₘ ((tensorPowMap f m ⊗ₘ tensorPowMap f n) ≫ (tensorPowAddIso Y m n).hom)) := by
          monoidal
      _ = _ := by
          -- After the induction step, split `f ⊗ₘ -` into whiskerings so `monoidal` sees them.
          rw [ih, tensorHom_def', tensorHom_def' f]
          monoidal

/-- Transporting along an equality of exponents commutes with the tensor powers of a morphism. -/
@[reassoc]
theorem tensorPowMap_eqToHom {X Y : C} (f : X ⟶ Y) {m n : ℕ} (h : m = n) :
    tensorPowMap f m ≫ eqToHom (congrArg (tensorPow Y) h) =
      eqToHom (congrArg (tensorPow X) h) ≫ tensorPowMap f n := by
  subst h; simp

/-- Appending a factor on the right is natural. -/
@[reassoc]
theorem tensorPowSuccIso_hom_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (tensorPowMap f n ⊗ₘ f) ≫ (tensorPowSuccIso Y n).hom =
      (tensorPowSuccIso X n).hom ≫ tensorPowMap f (n + 1) := by
  have h : (tensorPowMap f n ⊗ₘ f) ≫ tensorPow Y n ◁ (ρ_ Y).inv =
      tensorPow X n ◁ (ρ_ X).inv ≫ (tensorPowMap f n ⊗ₘ tensorPowMap f 1) := by
    rw [tensorPowMap_succ, tensorPowMap_zero]
    monoidal
  rw [tensorPowSuccIso_hom, tensorPowSuccIso_hom, reassoc_of% h,
    tensorPowAddIso_hom_naturality_assoc, tensorPowMap_eqToHom f (Nat.add_comm 1 n),
    Category.assoc, Category.assoc]

end Map

end TauCeti
