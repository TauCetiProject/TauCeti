/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic
public import TauCeti.CategoryTheory.Pi.InsertNth

/-!
# Tensor powers of a functor

For a functor `F : C ⥤ D` into a monoidal category, `F.tensorPow n : (Fin n → C) ⥤ D` is the
`n`-fold tensor functor of `F`. It sends `(X₀, …, X_{n-1})` to
`F X₀ ⊗ (F X₁ ⊗ (⋯ ⊗ F X_{n-1}))`, nested to the right, and the empty tuple to `𝟙_ D`. The
identification `F ⊗ F.tensorPow n ≅ F.tensorPow (n + 1)`, pointwise in Mathlib's monoidal structure
on functor categories, is `Functor.tensorPowSuccIso'`, and holds by definition.

When `C` is monoidal and `F` is a monoidal functor, the tensor powers are compatible with the
two operations on tuples that the Davydov–Yetter cochain complex is built from:

* `TauCeti.piContractNth C i : (Fin (n + 1) → C) ⥤ (Fin n → C)` tensors the entries `i` and
  `i + 1` of a tuple together (Mathlib's `Fin.contractNth` with `⊗` as the operation), and
  `Functor.tensorPowContractNthIso F i` identifies `F.tensorPow n` at the contracted tuple with
  `F.tensorPow (n + 1)` at the original one, through the tensorator of `F` and associators of `D`;
* inserting the monoidal unit at position `i` (the contraction of an empty block) is identified
  with the identity of `F.tensorPow n` by `Functor.tensorPowInsertUnitIso F i`, through the unit
  isomorphism of `F` and the left unitor.

Finally, varying one entry of the tuple and fixing the others (through `TauCeti.piInsertNth`),
the tensor power of an additive or `R`-linear functor is additive or `R`-linear in that slot,
provided the tensor product of `D` is.

## References

* A. M. Gainutdinov, J. Haferkamp and C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. 414 (2023), arXiv:1910.06094, §3.1, (3.4) and (3.5).
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace TauCeti

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

-- Exposed: tensor powers compute on the image of this functor without rewriting its objects.
/-- The functor `(Fin (n + 1) → C) ⥤ (Fin n → C)` tensoring the entries `i` and `i + 1` of a
tuple together: `(X₀, …, Xₙ) ↦ (X₀, …, X_{i-1}, X_i ⊗ X_{i+1}, X_{i+2}, …, Xₙ)`. On objects it
agrees entry by entry with Mathlib's `Fin.contractNth` for the operation `⊗`. -/
def piContractNth {n : ℕ} (i : Fin n) : (Fin (n + 1) → C) ⥤ (Fin n → C) :=
  go i.val i.isLt
where
  /-- The recursion behind `piContractNth`, on the value of the position. -/
  go : (k : ℕ) → {n : ℕ} → k < n → (Fin (n + 1) → C) ⥤ (Fin n → C)
    | _, 0, h => absurd h (by omega)
    | 0, _ + 1, _ => Functor.pi' (Fin.cons
        ((Pi.eval _ 0).prod' (Pi.eval _ 1) ⋙ tensor C) fun j ↦ Pi.eval _ j.succ.succ)
    | k + 1, _ + 1, h => Functor.pi' (Fin.cons (Pi.eval _ 0)
        fun j ↦ Pi.comap _ Fin.succ ⋙ go k (by omega) ⋙ Pi.eval _ j)
  termination_by structural k => k

variable {C}

/-- Contracting at position `0` tensors the first two entries. -/
theorem piContractNth_zero_obj {n : ℕ} (X : Fin (n + 2) → C) :
    (piContractNth C 0).obj X = Fin.cons (X 0 ⊗ X 1) fun j ↦ X j.succ.succ := by
  funext j
  cases j using Fin.cases <;> rfl

/-- Contracting at position `i.succ` keeps the first entry and contracts the others at
position `i`. -/
theorem piContractNth_succ_obj {n : ℕ} (i : Fin (n + 1)) (X : Fin (n + 3) → C) :
    (piContractNth C i.succ).obj X = Fin.cons (X 0) ((piContractNth C i).obj fun j ↦ X j.succ) := by
  funext j
  cases j using Fin.cases <;> rfl

/-- Before the contracted position, contracting keeps the entries of the tuple. -/
@[simp]
theorem piContractNth_obj_of_lt {n : ℕ} {i j : Fin n} (h : j < i) (X : Fin (n + 1) → C) :
    (piContractNth C i).obj X j = X j.castSucc := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero j)
    | succ i =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact ih (Fin.succ_lt_succ_iff.mp h) _

/-- At the contracted position, contracting tensors the two entries `i` and `i + 1` together. -/
@[simp]
theorem piContractNth_obj_self {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    (piContractNth C i).obj X i = X i.castSucc ⊗ X i.succ := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i _

/-- After the contracted position, contracting shifts the entries of the tuple down by one. -/
@[simp]
theorem piContractNth_obj_of_gt {n : ℕ} {i j : Fin n} (h : i < j) (X : Fin (n + 1) → C) :
    (piContractNth C i).obj X j = X j.succ := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero i)
    | succ j =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih (Fin.succ_lt_succ_iff.mp h) _

/-- Contracting at position `0`, the first entry of the morphism is the tensor product of the first
two. -/
@[simp]
theorem piContractNth_zero_map_zero {n : ℕ} {X Y : Fin (n + 2) → C} (f : X ⟶ Y) :
    (piContractNth C 0).map f 0 = f 0 ⊗ₘ f 1 :=
  (rfl)

/-- Contracting at position `0`, the later entries of the morphism are shifted down by one. -/
@[simp]
theorem piContractNth_zero_map_succ {n : ℕ} {X Y : Fin (n + 2) → C} (f : X ⟶ Y) (j : Fin n) :
    (piContractNth C 0).map f j.succ = f j.succ.succ :=
  (rfl)

/-- Contracting at position `i.succ`, the first entry of the morphism is kept. -/
@[simp]
theorem piContractNth_succ_map_zero {n : ℕ} (i : Fin (n + 1)) {X Y : Fin (n + 3) → C} (f : X ⟶ Y) :
    (piContractNth C i.succ).map f 0 = f 0 :=
  (rfl)

/-- Contracting at position `i.succ`, the later entries of the morphism are those of the
contraction at position `i` of the remaining entries. -/
@[simp]
theorem piContractNth_succ_map_succ {n : ℕ} (i : Fin (n + 1)) {X Y : Fin (n + 3) → C} (f : X ⟶ Y)
    (j : Fin (n + 1)) :
    (piContractNth C i.succ).map f j.succ = (piContractNth C i).map (fun k ↦ f k.succ) j :=
  (rfl)

end TauCeti

namespace CategoryTheory.Functor

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D)

-- Exposed and implicitly reducible: morphisms out of `(F.tensorPow (n + 1)).obj X` are used as
-- morphisms out of `F.obj (X 0) ⊗ (F.tensorPow n).obj _` without rewriting the objects.
/-- The `n`-fold tensor functor of `F`, sending `(X₀, …, X_{n-1})` to
`F X₀ ⊗ (F X₁ ⊗ (⋯ ⊗ F X_{n-1}))` and the empty tuple to `𝟙_ D`. -/
@[implicit_reducible]
def tensorPow : (n : ℕ) → (Fin n → C) ⥤ D
  | 0 => (Functor.const _).obj (𝟙_ D)
  | n + 1 =>
    { obj X := F.obj (X 0) ⊗ (tensorPow n).obj fun j ↦ X j.succ
      map f := F.map (f 0) ⊗ₘ (tensorPow n).map fun j ↦ f j.succ
      map_id X := by
        rw [Pi.id_apply, F.map_id]
        exact (congrArg (𝟙 _ ⊗ₘ ·) ((tensorPow n).map_id _)).trans (id_tensorHom_id _ _)
      map_comp f g := by
        rw [Pi.comp_apply, F.map_comp, tensorHom_comp_tensorHom]
        exact congrArg (_ ⊗ₘ ·) ((tensorPow n).map_comp _ _) }

@[simp]
theorem tensorPow_zero_obj (X : Fin 0 → C) : (F.tensorPow 0).obj X = 𝟙_ D :=
  (rfl)

@[simp]
theorem tensorPow_succ_obj {n : ℕ} (X : Fin (n + 1) → C) :
    (F.tensorPow (n + 1)).obj X = F.obj (X 0) ⊗ (F.tensorPow n).obj fun j ↦ X j.succ :=
  (rfl)

@[simp]
theorem tensorPow_zero_map {X Y : Fin 0 → C} (f : X ⟶ Y) : (F.tensorPow 0).map f = 𝟙 (𝟙_ D) :=
  (rfl)

@[simp]
theorem tensorPow_succ_map {n : ℕ} {X Y : Fin (n + 1) → C} (f : X ⟶ Y) :
    (F.tensorPow (n + 1)).map f = F.map (f 0) ⊗ₘ (F.tensorPow n).map fun j ↦ f j.succ :=
  (rfl)

/-- The pointwise tensor product of `F`, applied to the first entry, with the `n`-fold tensor
functor, applied to the others, is the `(n + 1)`-fold tensor functor. The new factor is on the
left, unlike in the object-level `TauCeti.tensorPowSuccIso`, as in `pow_succ'`. -/
def tensorPowSuccIso' (n : ℕ) :
    (Pi.eval (fun _ ↦ C) 0 ⋙ F) ⊗ (Pi.comap (fun _ ↦ C) Fin.succ ⋙ F.tensorPow n) ≅
      F.tensorPow (n + 1) :=
  Iso.refl _

@[simp]
theorem tensorPowSuccIso'_hom_app (n : ℕ) (X : Fin (n + 1) → C) :
    (F.tensorPowSuccIso' n).hom.app X = 𝟙 _ :=
  (rfl)

@[simp]
theorem tensorPowSuccIso'_inv_app (n : ℕ) (X : Fin (n + 1) → C) :
    (F.tensorPowSuccIso' n).inv.app X = 𝟙 _ :=
  (rfl)

/-- On a constant tuple, the tensor functor gives the tensor powers of `F.obj X`. -/
theorem tensorPow_obj_const (X : C) (n : ℕ) :
    (F.tensorPow n).obj (fun _ ↦ X) = TauCeti.tensorPow (F.obj X) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (F.obj X ⊗ ·) ih

/-- Varying the first entry of the tuple, the tensor functor whiskers `F` on the right. -/
theorem prod'_comp_piInsertNth_zero_comp_tensorPow_map {n : ℕ} (y : Fin n → C) {X X' : C}
    (f : X ⟶ X') :
    ((𝟭 C).prod' ((Functor.const C).obj y) ⋙ piInsertNth C 0 ⋙ F.tensorPow (n + 1)).map f =
      F.map f ▷ (F.tensorPow n).obj y := by
  -- The composite computes definitionally on `f`, through the recursions defining
  -- `piInsertNth` and `tensorPow`; `change` exposes the computed form. Rewriting with the map
  -- lemmas of `piInsertNth` instead leaves morphisms whose endpoints, such as
  -- `(piInsertNth C 0).obj p 0`, are only definitionally the expected objects, which `rw` rejects.
  change F.map f ⊗ₘ (F.tensorPow n).map (𝟙 y) = _
  rw [Functor.map_id, tensorHom_id]

/-- Varying the entry in slot `i.succ`, the tensor functor whiskers the slot-`i` functor of the
remaining entries on the left by `F` applied to the first entry. -/
theorem prod'_comp_piInsertNth_succ_comp_tensorPow_map {n : ℕ} (i : Fin (n + 1))
    (y : Fin (n + 1) → C) {X X' : C} (f : X ⟶ X') :
    ((𝟭 C).prod' ((Functor.const C).obj y) ⋙ piInsertNth C i.succ ⋙ F.tensorPow (n + 2)).map f =
      F.obj (y 0) ◁ ((𝟭 C).prod' ((Functor.const C).obj fun j ↦ y j.succ) ⋙ piInsertNth C i ⋙
        F.tensorPow (n + 1)).map f := by
  -- As above, `change` exposes the definitional computation of the composite on `f`.
  change F.map (𝟙 (y 0)) ⊗ₘ _ = _
  rw [Functor.map_id, id_tensorHom]
  -- Both sides are now `F.obj (y 0) ◁ _` of the same morphism, whose tuple is written once
  -- through the slot functor and once through its unfolding.
  rfl

/-- Varying the first entry of the tuple, the tensor functor is `F` followed by tensoring on the
right with the tensor power of the fixed entries. -/
private def tensorPowSlotZeroIso {n : ℕ} (y : Fin n → C) :
    F ⋙ tensorRight ((F.tensorPow n).obj y) ≅
      (𝟭 C).prod' ((Functor.const C).obj y) ⋙ piInsertNth C 0 ⋙ F.tensorPow (n + 1) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    rw [prod'_comp_piInsertNth_zero_comp_tensorPow_map]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Varying the entry in slot `i.succ`, the tensor functor is the slot-`i` functor of the remaining
entries followed by tensoring on the left with `F` applied to the first entry. -/
private def tensorPowSlotSuccIso {n : ℕ} (i : Fin (n + 1))
    (y : Fin (n + 1) → C) :
    ((𝟭 C).prod' ((Functor.const C).obj fun j ↦ y j.succ) ⋙ piInsertNth C i ⋙
        F.tensorPow (n + 1)) ⋙ tensorLeft (F.obj (y 0)) ≅
      (𝟭 C).prod' ((Functor.const C).obj y) ⋙ piInsertNth C i.succ ⋙ F.tensorPow (n + 2) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    rw [prod'_comp_piInsertNth_succ_comp_tensorPow_map]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

section Linear

variable [Preadditive C] [Preadditive D] [MonoidalPreadditive D]

/-- The tensor functor of an additive functor is additive in each slot. -/
instance additive_prod'_comp_piInsertNth_comp_tensorPow [F.Additive] {n : ℕ}
    (i : Fin (n + 1)) (y : Fin n → C) :
    ((𝟭 C).prod' ((Functor.const C).obj y) ⋙ piInsertNth C i ⋙ F.tensorPow (n + 1)).Additive := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact Functor.additive_of_iso (tensorPowSlotZeroIso F y)
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact Functor.additive_of_iso (tensorPowSlotZeroIso F y)
    | succ k =>
      have := ih k fun j ↦ y j.succ
      exact Functor.additive_of_iso (tensorPowSlotSuccIso F k y)

variable {R : Type*} [Semiring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [MonoidalLinear R D]

/-- The tensor functor of an `R`-linear functor is `R`-linear in each slot. -/
instance linear_prod'_comp_piInsertNth_comp_tensorPow [F.Linear R] {n : ℕ}
    (i : Fin (n + 1)) (y : Fin n → C) :
    ((𝟭 C).prod' ((Functor.const C).obj y) ⋙ piInsertNth C i ⋙ F.tensorPow (n + 1)).Linear R := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact Functor.linear_of_iso R (tensorPowSlotZeroIso F y)
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact Functor.linear_of_iso R (tensorPowSlotZeroIso F y)
    | succ k =>
      have := ih k fun j ↦ y j.succ
      exact Functor.linear_of_iso R (tensorPowSlotSuccIso F k y)

end Linear

section Monoidal

variable [MonoidalCategory C] [F.Monoidal]

/-- For a monoidal functor `F`, the tensor functor at a tuple whose entries `i` and `i + 1` have
been contracted is isomorphic to the tensor functor at the original tuple: the component at
`(X₀, …, Xₙ)` is `F X₀ ⊗ ⋯ ⊗ F (X_i ⊗ X_{i+1}) ⊗ ⋯ ≅ F X₀ ⊗ ⋯ ⊗ F X_i ⊗ F X_{i+1} ⊗ ⋯`,
given by the inverse tensorator of `F` followed by an associator. -/
def tensorPowContractNthIso :
    {n : ℕ} → (i : Fin n) → piContractNth C i ⋙ F.tensorPow n ≅ F.tensorPow (n + 1)
  | 0, i => i.elim0
  | m + 1, i => Fin.cases
      (motive := fun i ↦ piContractNth C i ⋙ F.tensorPow (m + 1) ≅ F.tensorPow (m + 2))
      (NatIso.ofComponents
        (fun X ↦ whiskerRightIso (Monoidal.μIso F (X 0) (X 1)).symm _ ≪≫ α_ _ _ _)
        fun {X Y} f ↦ by
          -- `change` exposes the definitional computation of both functors on `f`.
          change (F.map (f 0 ⊗ₘ f 1) ⊗ₘ (F.tensorPow m).map fun j ↦ f j.succ.succ) ≫
              (Monoidal.μIso F (Y 0) (Y 1)).inv ▷ _ ≫ (α_ _ _ _).hom =
            ((Monoidal.μIso F (X 0) (X 1)).inv ▷ _ ≫ (α_ _ _ _).hom) ≫
              (F.map (f 0) ⊗ₘ F.map (f 1) ⊗ₘ (F.tensorPow m).map fun j ↦ f j.succ.succ)
          -- Move the associator to the right; what remains is the naturality of `δ` tensored
          -- with `(F.tensorPow m).map _`.
          rw [Category.assoc, ← associator_naturality, ← Category.assoc, ← Category.assoc]
          congr 1
          simp only [Monoidal.μIso_inv, ← tensorHom_id, tensorHom_comp_tensorHom,
            OplaxMonoidal.δ_natural, Category.comp_id, Category.id_comp])
      (fun k ↦ NatIso.ofComponents
        (fun X ↦ whiskerLeftIso (F.obj (X 0)) ((tensorPowContractNthIso k).app fun j ↦ X j.succ))
        fun {X Y} f ↦ by
          have h := (tensorPowContractNthIso k).hom.naturality fun j ↦ f j.succ
          -- `change` exposes the definitional computation of both functors on `f`.
          change (F.map (f 0) ⊗ₘ (F.tensorPow m).map ((piContractNth C k).map fun j ↦ f j.succ)) ≫
              F.obj (Y 0) ◁ (tensorPowContractNthIso k).hom.app (fun j ↦ Y j.succ) =
            F.obj (X 0) ◁ (tensorPowContractNthIso k).hom.app (fun j ↦ X j.succ) ≫
              (F.map (f 0) ⊗ₘ (F.tensorPow (m + 1)).map fun j ↦ f j.succ)
          rw [tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom]
          exact congrArg (F.map (f 0) ⊗ₘ ·) h) i

/-- Contracting the first two entries is the inverse tensorator of `F` followed by an associator. -/
@[simp]
theorem tensorPowContractNthIso_zero_hom_app {n : ℕ} (X : Fin (n + 2) → C) :
    (F.tensorPowContractNthIso 0).hom.app X =
      OplaxMonoidal.δ F (X 0) (X 1) ▷ (F.tensorPow n).obj (fun j ↦ X j.succ.succ) ≫
        (α_ (F.obj (X 0)) (F.obj (X 1)) ((F.tensorPow n).obj fun j ↦ X j.succ.succ)).hom :=
  (rfl)

@[simp]
theorem tensorPowContractNthIso_zero_inv_app {n : ℕ} (X : Fin (n + 2) → C) :
    (F.tensorPowContractNthIso 0).inv.app X =
      (α_ (F.obj (X 0)) (F.obj (X 1)) ((F.tensorPow n).obj fun j ↦ X j.succ.succ)).inv ≫
        LaxMonoidal.μ F (X 0) (X 1) ▷ (F.tensorPow n).obj (fun j ↦ X j.succ.succ) :=
  (rfl)

/-- Contracting at position `i.succ` whiskers the contraction at position `i` of the remaining
entries. -/
@[simp]
theorem tensorPowContractNthIso_succ_hom_app {n : ℕ} (i : Fin (n + 1)) (X : Fin (n + 3) → C) :
    (F.tensorPowContractNthIso i.succ).hom.app X =
      F.obj (X 0) ◁ (F.tensorPowContractNthIso i).hom.app fun j ↦ X j.succ :=
  (rfl)

@[simp]
theorem tensorPowContractNthIso_succ_inv_app {n : ℕ} (i : Fin (n + 1)) (X : Fin (n + 3) → C) :
    (F.tensorPowContractNthIso i.succ).inv.app X =
      F.obj (X 0) ◁ (F.tensorPowContractNthIso i).inv.app fun j ↦ X j.succ :=
  (rfl)

/-- For a monoidal functor `F`, inserting the monoidal unit into a tuple at position `i` does not
change its tensor power up to isomorphism: the component at `(X₀, …, X_{n-1})` removes
`F (𝟙_ C)` through the unit isomorphism of `F` and the left unitor. This is the contraction of an
empty block, whose value is the zero-fold tensor product `𝟙_ C`. -/
def tensorPowInsertUnitIso : {n : ℕ} → (i : Fin (n + 1)) →
    ((Functor.const _).obj (𝟙_ C)).prod' (𝟭 _) ⋙ piInsertNth C i ⋙ F.tensorPow (n + 1) ≅
      F.tensorPow n
  | n, i => Fin.cases (motive := fun i ↦
      ((Functor.const _).obj (𝟙_ C)).prod' (𝟭 _) ⋙ piInsertNth C i ⋙ F.tensorPow (n + 1) ≅
        F.tensorPow n)
      (NatIso.ofComponents (fun y ↦ whiskerRightIso (Monoidal.εIso F).symm _ ≪≫ λ_ _)
        fun {y y'} g ↦ by
          -- `change` exposes the definitional computation of both functors on `g`.
          change (F.map (𝟙 (𝟙_ C)) ⊗ₘ (F.tensorPow n).map g) ≫
              (Monoidal.εIso F).inv ▷ _ ≫ (λ_ _).hom =
            ((Monoidal.εIso F).inv ▷ _ ≫ (λ_ _).hom) ≫ (F.tensorPow n).map g
          simp [tensorHom_def, whisker_exchange_assoc])
      (match n with
        | 0 => fun k ↦ k.elim0
        | m + 1 => fun k ↦ NatIso.ofComponents
          (fun y ↦ whiskerLeftIso (F.obj (y 0)) ((tensorPowInsertUnitIso k).app fun j ↦ y j.succ))
          fun {y y'} g ↦ by
            have h := (tensorPowInsertUnitIso k).hom.naturality fun j ↦ g j.succ
            -- `change` exposes the definitional computation of both functors on `g`.
            change (F.map (g 0) ⊗ₘ (F.tensorPow (m + 1)).map
                  ((piInsertNth C k).map (𝟙 (𝟙_ C), fun j ↦ g j.succ))) ≫
                F.obj (y' 0) ◁ (tensorPowInsertUnitIso k).hom.app (fun j ↦ y' j.succ) =
              F.obj (y 0) ◁ (tensorPowInsertUnitIso k).hom.app (fun j ↦ y j.succ) ≫
                (F.map (g 0) ⊗ₘ (F.tensorPow m).map fun j ↦ g j.succ)
            rw [tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom]
            exact congrArg (F.map (g 0) ⊗ₘ ·) h) i

/-- Removing a unit inserted in front is the inverse unit isomorphism of `F` followed by the left
unitor. -/
@[simp]
theorem tensorPowInsertUnitIso_zero_hom_app {n : ℕ} (y : Fin n → C) :
    (F.tensorPowInsertUnitIso 0).hom.app y =
      OplaxMonoidal.η F ▷ (F.tensorPow n).obj y ≫ (λ_ ((F.tensorPow n).obj y)).hom := by
  -- The definition matches on `n` to rule out positions in `Fin 0`; splitting `n` lets that match
  -- reduce, after which both sides agree by definition.
  cases n <;> rfl

@[simp]
theorem tensorPowInsertUnitIso_zero_inv_app {n : ℕ} (y : Fin n → C) :
    (F.tensorPowInsertUnitIso 0).inv.app y =
      (λ_ ((F.tensorPow n).obj y)).inv ≫ LaxMonoidal.ε F ▷ (F.tensorPow n).obj y := by
  -- As above, splitting `n` lets the match in the definition reduce.
  cases n <;> rfl

/-- Removing a unit inserted at position `i.succ` whiskers the removal at position `i` from the
remaining entries. -/
@[simp]
theorem tensorPowInsertUnitIso_succ_hom_app {n : ℕ} (i : Fin (n + 1)) (y : Fin (n + 1) → C) :
    (F.tensorPowInsertUnitIso i.succ).hom.app y =
      F.obj (y 0) ◁ (F.tensorPowInsertUnitIso i).hom.app fun j ↦ y j.succ :=
  (rfl)

@[simp]
theorem tensorPowInsertUnitIso_succ_inv_app {n : ℕ} (i : Fin (n + 1)) (y : Fin (n + 1) → C) :
    (F.tensorPowInsertUnitIso i.succ).inv.app y =
      F.obj (y 0) ◁ (F.tensorPowInsertUnitIso i).inv.app fun j ↦ y j.succ :=
  (rfl)

end Monoidal

end CategoryTheory.Functor
