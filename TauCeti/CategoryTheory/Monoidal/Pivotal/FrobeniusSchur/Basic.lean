/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Tensor
public import TauCeti.CategoryTheory.Monoidal.TensorPow

/-!
# Frobenius–Schur indicators of pivotal categories

In a pivotal category `C`, a morphism `f : 𝟙_ C ⟶ X ⊗ Y` can be *rotated* to a morphism
`pivotalRotate f : 𝟙_ C ⟶ Y ⊗ X` by bending the strand `X` around to the right: close it up
against `Xᘁ` with the evaluation `ε_ X Xᘁ`, and reopen it on the right with the coevaluation of
the pivotal pairing `TauCeti.pivotalExactPairing X : ExactPairing Xᘁ X`. This is the map `E_{X,Y}`
of Ng and Schauenburg; with the pivotal isomorphism `φ_X : X ≅ Xᘁᘁ` written out, it is
`(ε_ X Xᘁ ⊗ 𝟙 ⊗ φ_X⁻¹) ∘ (𝟙 ⊗ f ⊗ 𝟙) ∘ η_ Xᘁ Xᘁᘁ`, up to associators and unitors.

The rotation is natural in `Y` and dinatural in `X`. Rotating a block `X ⊗ X'` is rotating `X` and
then `X'` (`TauCeti.pivotalRotate_tensor`), which is where the monoidality of the pivotal structure
enters, and rotating the unit object, on either side, changes nothing but unitors.

For an object `V` and `n : ℕ`, rotating the first factor of `V^⊗(n+1) = V ⊗ V^⊗n` to the end and
re-bracketing is the endomorphism `TauCeti.frobeniusSchurRotate V n` of `𝟙_ C ⟶ V^⊗(n+1)`, the
operator `E_V^{(n+1)}` of Ng and Schauenburg. Its `(n + 1)`-st iterate is the identity
(`TauCeti.iterate_frobeniusSchurRotate_eq_id`): by the block rule, rotating the factors one at a
time `n + 1` times is rotating the whole of `V^⊗(n+1)` past the unit, which is trivial.

In a `k`-linear pivotal category the operator is `k`-linear, and the `n`-th *Frobenius–Schur
indicator* of `V`, for a positive integer `n`, is its trace
`TauCeti.frobeniusSchurIndicator k V n = tr (E_V^{(n)}) ∈ k`. This is the Ng–Schauenburg indicator
when `𝟙_ C ⟶ V^⊗n` is finite and free over `k` (for example over a field, with finite-dimensional
hom spaces); otherwise it is `0`, by the convention of `LinearMap.trace`. It is invariant under
isomorphism, and `ν_1(V)` is the rank of `𝟙_ C ⟶ V` when that module is finite and free.

## Main declarations

* `TauCeti.pivotalRotate`: the rotation `(𝟙_ C ⟶ X ⊗ Y) → (𝟙_ C ⟶ Y ⊗ X)`, with
  `TauCeti.pivotalRotate_comp_whiskerLeft`, `TauCeti.pivotalRotate_comp_whiskerRight`,
  `TauCeti.pivotalRotate_tensor`, `TauCeti.pivotalRotate_unit_left` and
  `TauCeti.pivotalRotate_unit_right`;
* `TauCeti.frobeniusSchurRotate`: the operator `E_V^{(n+1)}` on `𝟙_ C ⟶ tensorPow V (n + 1)`, with
  `TauCeti.iterate_frobeniusSchurRotate_eq_id` and its naturality
  `TauCeti.frobeniusSchurRotate_comp_tensorPowMap`;
* `TauCeti.frobeniusSchurEnd`: the same operator as a `k`-linear endomorphism, of order dividing
  `n + 1` (`TauCeti.frobeniusSchurEnd_pow_eq_one`);
* `TauCeti.frobeniusSchurIndicator`: the indicator `ν_n(V)`, with
  `TauCeti.frobeniusSchurIndicator_congr`, `TauCeti.frobeniusSchurIndicator_one`, and
  `TauCeti.frobeniusSchurIndicator_two`.

## References

* S.-H. Ng, P. Schauenburg, *Higher Frobenius–Schur indicators for pivotal categories*, in
  *Hopf algebras and generalizations*, Contemp. Math. **441** (2007), 63–90, §§4–5, for the
  rotation `E_{X,Y}`, the operator `E_V^{(n)}`, the identity `(E_V^{(n)})^n = id` and the
  indicators
* S.-H. Ng, P. Schauenburg, *Frobenius–Schur indicators and exponents of spherical categories*,
  Adv. Math. **211** (2007), 34–71, §5
-/

public section

open CategoryTheory MonoidalCategory ExactPairing

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-- The *rotation* of a morphism `f : 𝟙_ C ⟶ X ⊗ Y` in a pivotal category to a morphism
`𝟙_ C ⟶ Y ⊗ X`: the strand `X` is closed up against `Xᘁ` by the evaluation `ε_ X Xᘁ` and reopened
on the right by the coevaluation of the pivotal pairing `pivotalExactPairing X`. -/
noncomputable def pivotalRotate {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) : 𝟙_ C ⟶ Y ⊗ X :=
  @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) ⊗≫ Xᘁ ◁ f ▷ X ⊗≫ ε_ X Xᘁ ▷ Y ▷ X ⊗≫ 𝟙 _

/-- The defining formula of the rotation. -/
theorem pivotalRotate_def {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) :
    pivotalRotate f = @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) ⊗≫ Xᘁ ◁ f ▷ X ⊗≫
      ε_ X Xᘁ ▷ Y ▷ X ⊗≫ 𝟙 _ :=
  (rfl)

/-- Rotating the coevaluation `η_ X Xᘁ : 𝟙_ C ⟶ X ⊗ Xᘁ` yields the coevaluation of
`pivotalExactPairing X`. -/
@[simp]
theorem pivotalRotate_coevaluation (X : C) :
    pivotalRotate (η_ X Xᘁ) = @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) := by
  rw [pivotalRotate_def]
  calc _ = @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) ⊗≫
        (Xᘁ ◁ η_ X Xᘁ ⊗≫ ε_ X Xᘁ ▷ Xᘁ) ▷ X ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

/-- The rotation is natural in the second factor. -/
theorem pivotalRotate_comp_whiskerLeft {X Y Y' : C} (f : 𝟙_ C ⟶ X ⊗ Y) (g : Y ⟶ Y') :
    pivotalRotate (f ≫ X ◁ g) = pivotalRotate f ≫ g ▷ X := by
  rw [pivotalRotate_def, pivotalRotate_def]
  calc _ = @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) ⊗≫ Xᘁ ◁ f ▷ X ⊗≫
        ((Xᘁ ⊗ X) ◁ g ≫ ε_ X Xᘁ ▷ Y') ▷ X ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- The rotation is dinatural in the first factor: for `a : X ⟶ X'`, rotating `f ≫ a ▷ Y` past
`X'` is rotating `f` past `X` and then applying `a`. -/
theorem pivotalRotate_comp_whiskerRight {X X' Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) (a : X ⟶ X') :
    pivotalRotate (f ≫ a ▷ Y) = pivotalRotate f ≫ Y ◁ a := by
  rw [pivotalRotate_def, pivotalRotate_def]
  calc _ = @coevaluation C _ _ X'ᘁ X' (pivotalExactPairing X') ⊗≫ X'ᘁ ◁ f ▷ X' ⊗≫
        (X'ᘁ ◁ a ≫ ε_ X' X'ᘁ) ▷ Y ▷ X' ⊗≫ 𝟙 _ := by monoidal
    _ = @coevaluation C _ _ X'ᘁ X' (pivotalExactPairing X') ⊗≫ (X'ᘁ ◁ f ≫ aᘁ ▷ (X ⊗ Y)) ▷ X' ⊗≫
        ε_ X Xᘁ ▷ Y ▷ X' ⊗≫ 𝟙 _ := by
      rw [← rightAdjointMate_comp_evaluation]; monoidal
    _ = (@coevaluation C _ _ X'ᘁ X' (pivotalExactPairing X') ≫ aᘁ ▷ X') ⊗≫ Xᘁ ◁ f ▷ X' ⊗≫
        ε_ X Xᘁ ▷ Y ▷ X' ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; monoidal
    _ = @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) ≫ Xᘁ ◁ a ≫
        ((ρ_ (Xᘁ : C)).inv ≫ Xᘁ ◁ f ≫ (α_ _ _ _).inv ≫ ε_ X Xᘁ ▷ Y ≫ (λ_ Y).hom) ▷ X' := by
      rw [pivotalExactPairing_coevaluation_comp_rightAdjointMate_whiskerRight]; monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- **Rotating a tensor product**: rotating the block `X ⊗ X'` to the end is rotating `X` and then
`X'`, up to associators. -/
theorem pivotalRotate_tensor {X X' Y : C} (f : 𝟙_ C ⟶ (X ⊗ X') ⊗ Y) :
    pivotalRotate f = pivotalRotate (pivotalRotate (f ≫ (α_ X X' Y).hom) ≫
      (α_ X' Y X).hom) ≫ (α_ Y X X').hom := by
  have hε := rightDualTensorIso_hom_whiskerRight_evaluation X X'
  have hη := pivotalExactPairing_tensor_coevaluation X X'
  rw [@ExactPairing.tensor_coevaluation C _ _ _ _ _ _ (pivotalExactPairing X')
    (pivotalExactPairing X)] at hη
  calc pivotalRotate f = @coevaluation C _ _ (X ⊗ X')ᘁ (X ⊗ X') (pivotalExactPairing (X ⊗ X')) ⊗≫
        ((X ⊗ X')ᘁ ◁ f ≫ (rightDualTensorIso X X').hom ▷ ((X ⊗ X') ⊗ Y)) ▷ (X ⊗ X') ⊗≫
        ε_ (X ⊗ X') ((X'ᘁ : C) ⊗ (Xᘁ : C)) ▷ Y ▷ (X ⊗ X') ⊗≫ 𝟙 _ := by
        rw [pivotalRotate_def, ← hε]; monoidal
    _ = (@coevaluation C _ _ (X ⊗ X')ᘁ (X ⊗ X') (pivotalExactPairing (X ⊗ X')) ≫
          (rightDualTensorIso X X').hom ▷ (X ⊗ X')) ⊗≫
        ((X'ᘁ : C) ⊗ (Xᘁ : C)) ◁ f ▷ (X ⊗ X') ⊗≫
        ε_ (X ⊗ X') ((X'ᘁ : C) ⊗ (Xᘁ : C)) ▷ Y ▷ (X ⊗ X') ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
    _ = _ := by
        rw [hη, tensor_evaluation]; simp only [pivotalRotate_def]; monoidal

/-- Rotating the unit past the unit is trivial. This is the left dimension of the unit. -/
private theorem pivotalRotate_leftUnitor_inv :
    pivotalRotate (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv :=
  calc pivotalRotate (λ_ (𝟙_ C)).inv = leftTrace (𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).inv := by
        rw [leftTrace_def, pivotalRotate_def]; monoidal
    _ = _ := by rw [leftTrace_id, leftDim_unit, Category.id_comp]

/-- Rotating the unit object to the end changes only unitors. -/
theorem pivotalRotate_unit_left {Y : C} (f : 𝟙_ C ⟶ 𝟙_ C ⊗ Y) :
    pivotalRotate f = f ≫ (λ_ Y).hom ≫ (ρ_ Y).inv := by
  obtain ⟨g, rfl⟩ : ∃ g : 𝟙_ C ⟶ Y, f = g ≫ (λ_ Y).inv := ⟨f ≫ (λ_ Y).hom, by simp⟩
  rw [leftUnitor_inv_naturality, pivotalRotate_comp_whiskerLeft, pivotalRotate_leftUnitor_inv]
  simp

/-- Rotating an object past the unit object changes only unitors. -/
theorem pivotalRotate_unit_right {X : C} (f : 𝟙_ C ⟶ X ⊗ 𝟙_ C) :
    pivotalRotate f = f ≫ (ρ_ X).hom ≫ (λ_ X).inv := by
  obtain ⟨g, rfl⟩ : ∃ g : 𝟙_ C ⟶ X, f = g ≫ (ρ_ X).inv := ⟨f ≫ (ρ_ X).hom, by simp⟩
  rw [rightUnitor_inv_naturality, ← unitors_inv_equal, pivotalRotate_comp_whiskerRight,
    pivotalRotate_leftUnitor_inv, unitors_inv_equal]
  simp [← unitors_equal]

section TensorPow

variable (V : C)

/-- The operator `E_V^{(n+1)}` of Ng and Schauenburg on `𝟙_ C ⟶ V^⊗(n+1)`: rotate the first factor
of `V^⊗(n+1) = V ⊗ V^⊗n` to the end, then re-bracket `V^⊗n ⊗ V` as `V^⊗(n+1)`. -/
noncomputable def frobeniusSchurRotate (n : ℕ) (f : 𝟙_ C ⟶ tensorPow V (n + 1)) :
    𝟙_ C ⟶ tensorPow V (n + 1) :=
  pivotalRotate f ≫ (tensorPowSuccIso V n).hom

/-- The defining formula of `E_V^{(n+1)}`. -/
theorem frobeniusSchurRotate_def (n : ℕ) (f : 𝟙_ C ⟶ tensorPow V (n + 1)) :
    frobeniusSchurRotate V n f = pivotalRotate f ≫ (tensorPowSuccIso V n).hom :=
  (rfl)

/-- Rotating the first block of length `a` of `V^⊗(b+a)` to the end. -/
private noncomputable def blockRotate (a b : ℕ) (f : 𝟙_ C ⟶ tensorPow V (b + a)) :
    𝟙_ C ⟶ tensorPow V (a + b) :=
  pivotalRotate (f ≫ (tensorPowAddIso V a b).inv) ≫ (tensorPowAddIso V b a).hom

/-- Rotating an empty block is trivial. -/
private theorem blockRotate_zero (b : ℕ) (f : 𝟙_ C ⟶ tensorPow V b) :
    blockRotate V 0 b f = f ≫ eqToHom (congrArg (tensorPow V) (Nat.zero_add b).symm) := by
  rw [blockRotate, tensorPowAddIso_zero, pivotalRotate_unit_left, tensorPowAddIso_zero_right_hom]
  simp

/-- Rotating a block of length `j + 1` is rotating one factor and then a block of length `j`. -/
private theorem blockRotate_succ (j b : ℕ) (f : 𝟙_ C ⟶ tensorPow V (b + j + 1)) :
    blockRotate V (j + 1) b f =
      blockRotate V j (b + 1) (frobeniusSchurRotate V (b + j) f ≫
        eqToHom (congrArg (tensorPow V) (by omega))) ≫
        eqToHom (congrArg (tensorPow V) (by omega)) := by
  have key : (tensorPowSuccIso V (b + j)).hom ≫
      eqToHom (congrArg (tensorPow V) (by omega : b + j + 1 = b + 1 + j)) ≫
        (tensorPowAddIso V j (b + 1)).inv =
      (tensorPowAddIso V j b).inv ▷ V ≫ (α_ _ _ _).hom ≫
        tensorPow V j ◁ (tensorPowSuccIso V b).hom := by
    rw [← cancel_epi ((tensorPowAddIso V j b).hom ▷ V),
      tensorPowAddIso_hom_whiskerRight_tensorPowSuccIso_hom_assoc]
    simp
  rw [blockRotate, blockRotate, tensorPowAddIso_succ_inv, pivotalRotate_tensor]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, pivotalRotate_comp_whiskerLeft,
    frobeniusSchurRotate_def, key]
  have h := pivotalRotate_comp_whiskerLeft (pivotalRotate f ≫ (tensorPowAddIso V j b).inv ▷ V ≫
    (α_ _ _ _).hom) (tensorPowSuccIso V b).hom
  simp only [Category.assoc] at h
  rw [h, Category.assoc, tensorPowSuccIso_hom_whiskerRight_tensorPowAddIso_hom_assoc]
  simp

/-- The `j`-th iterate of `E_V^{(N+1)}` rotates the first block of length `j`. -/
private theorem iterate_frobeniusSchurRotate_eq_blockRotate (j : ℕ) :
    ∀ (b N : ℕ) (h : b + j = N + 1) (f : 𝟙_ C ⟶ tensorPow V (N + 1)),
      (frobeniusSchurRotate V N)^[j] f =
        blockRotate V j b (f ≫ eqToHom (congrArg (tensorPow V) h.symm)) ≫
          eqToHom (congrArg (tensorPow V) (by omega)) := by
  induction j with
  | zero => intro b N h f; simp [blockRotate_zero]
  | succ j ih =>
    intro b N h f
    obtain rfl : N = b + j := by omega
    rw [Function.iterate_succ_apply, ih (b + 1) (b + j) (by omega), eqToHom_refl,
      Category.comp_id, blockRotate_succ]
    simp

/-- **Ng–Schauenburg**: the `(n + 1)`-st iterate of `E_V^{(n+1)}` is the identity. -/
theorem iterate_frobeniusSchurRotate_eq_id (n : ℕ) :
    (frobeniusSchurRotate V n)^[n + 1] = id := by
  funext f
  rw [iterate_frobeniusSchurRotate_eq_blockRotate V (n + 1) 0 n (by omega), blockRotate,
    pivotalRotate_unit_right, tensorPowAddIso_zero]
  simp [tensorPowAddIso_zero_right_inv]

/-- `E_V^{(n+1)}` is natural in `V`: it commutes with the tensor powers of a morphism. -/
theorem frobeniusSchurRotate_comp_tensorPowMap {W : C} (a : V ⟶ W) (n : ℕ)
    (f : 𝟙_ C ⟶ tensorPow V (n + 1)) :
    frobeniusSchurRotate W n (f ≫ tensorPowMap a (n + 1)) =
      frobeniusSchurRotate V n f ≫ tensorPowMap a (n + 1) := by
  rw [frobeniusSchurRotate_def, frobeniusSchurRotate_def, Category.assoc,
    ← tensorPowSuccIso_hom_naturality, tensorPowMap_succ, tensorHom_def, ← Category.assoc,
    pivotalRotate_comp_whiskerLeft, pivotalRotate_comp_whiskerRight, tensorHom_def']
  simp

end TensorPow

section Linear

/-- The rotation is additive. -/
@[simp]
theorem pivotalRotate_add [Preadditive C] [MonoidalPreadditive C] {X Y : C}
    (f g : 𝟙_ C ⟶ X ⊗ Y) : pivotalRotate (f + g) = pivotalRotate f + pivotalRotate g := by
  simp [pivotalRotate_def, monoidalComp]

/-- The rotation is `k`-linear. -/
@[simp]
theorem pivotalRotate_smul {k : Type*} [Semiring k] [Preadditive C] [Linear k C]
    [MonoidalPreadditive C] [MonoidalLinear k C] {X Y : C} (c : k) (f : 𝟙_ C ⟶ X ⊗ Y) :
    pivotalRotate (c • f) = c • pivotalRotate f := by
  simp [pivotalRotate_def, monoidalComp]

variable (k : Type*) [Preadditive C] [MonoidalPreadditive C] (V : C)

section Semiring

variable [Semiring k] [Linear k C] [MonoidalLinear k C]

/-- The operator `E_V^{(n+1)}` as a `k`-linear endomorphism of `𝟙_ C ⟶ V^⊗(n+1)`. -/
noncomputable def frobeniusSchurEnd (n : ℕ) : Module.End k (𝟙_ C ⟶ tensorPow V (n + 1)) where
  toFun := frobeniusSchurRotate V n
  map_add' f g := by simp [frobeniusSchurRotate_def, pivotalRotate_add]
  map_smul' c f := by simp [frobeniusSchurRotate_def, pivotalRotate_smul]

/-- The linear operator `frobeniusSchurEnd k V n` is `frobeniusSchurRotate V n`. -/
theorem coe_frobeniusSchurEnd (n : ℕ) : ⇑(frobeniusSchurEnd k V n) = frobeniusSchurRotate V n :=
  (rfl)

/-- The `(n + 1)`-st power of `E_V^{(n+1)}` is the identity. -/
theorem frobeniusSchurEnd_pow_eq_one (n : ℕ) : frobeniusSchurEnd k V n ^ (n + 1) = 1 := by
  ext f
  rw [pow_apply_eq_iterate, one_apply_eq_self, coe_frobeniusSchurEnd,
    iterate_frobeniusSchurRotate_eq_id, id]

end Semiring

section CommRing

variable [CommRing k] [Linear k C] [MonoidalLinear k C]

/-- The `n`-th *Frobenius–Schur indicator* `ν_n(V)` of an object `V` of a `k`-linear pivotal
category, for a positive integer `n`: the trace of the operator `E_V^{(n)}` on `𝟙_ C ⟶ V^⊗n`.

This is the Ng–Schauenburg indicator when `𝟙_ C ⟶ V^⊗n` is finite and free over `k` (for example
when `k` is a field and the hom spaces are finite-dimensional). Otherwise it is `0`, by the
convention of `LinearMap.trace`. -/
noncomputable def frobeniusSchurIndicator (n : ℕ+) : k :=
  LinearMap.trace k _ (frobeniusSchurEnd k V n.natPred)

/-- The indicator `ν_{n+1}(V)` is the trace of `frobeniusSchurEnd k V n`. -/
theorem frobeniusSchurIndicator_succPNat (n : ℕ) :
    frobeniusSchurIndicator k V n.succPNat = LinearMap.trace k _ (frobeniusSchurEnd k V n) :=
  (rfl)

/-- The second Frobenius–Schur indicator `ν₂(V)` is the trace of `frobeniusSchurEnd k V 1`. -/
theorem frobeniusSchurIndicator_two :
    frobeniusSchurIndicator k V 2 = LinearMap.trace k _ (frobeniusSchurEnd k V 1) :=
  (rfl)

/-- The first Frobenius–Schur indicator is the dimension of `𝟙_ C ⟶ V`, since `E_V^{(1)}` is the
identity. -/
theorem frobeniusSchurIndicator_one [Module.Free k (𝟙_ C ⟶ V)] [Module.Finite k (𝟙_ C ⟶ V)] :
    frobeniusSchurIndicator k V 1 = Module.finrank k (𝟙_ C ⟶ V) := by
  let e : (𝟙_ C ⟶ tensorPow V 1) ≃ₗ[k] (𝟙_ C ⟶ V) := Linear.homCongr k (Iso.refl _) (ρ_ V)
  have : Module.Free k (𝟙_ C ⟶ tensorPow V 1) := Module.Free.of_equiv e.symm
  have : Module.Finite k (𝟙_ C ⟶ tensorPow V 1) := Module.Finite.equiv e.symm
  have h1 : frobeniusSchurEnd k V 0 = 1 := by simpa using frobeniusSchurEnd_pow_eq_one k V 0
  -- `(1 : ℕ+)` is `⟨1, _⟩`, which is `Nat.succPNat 0` by definition; restating it this way puts
  -- the indicator in the form of `frobeniusSchurIndicator_succPNat`.
  rw [show (1 : ℕ+) = Nat.succPNat 0 from rfl, frobeniusSchurIndicator_succPNat, h1,
    LinearMap.trace_one, e.finrank_eq]

/-- The Frobenius–Schur indicators of isomorphic objects agree. -/
theorem frobeniusSchurIndicator_congr {W : C} (e : V ≅ W) (n : ℕ+) :
    frobeniusSchurIndicator k V n = frobeniusSchurIndicator k W n := by
  let L := Linear.homCongr k (Iso.refl (𝟙_ C)) (tensorPowMapIso e (n.natPred + 1))
  have hL : L.conj (frobeniusSchurEnd k V n.natPred) = frobeniusSchurEnd k W n.natPred := by
    ext f
    simp only [L, LinearEquiv.conj_apply_apply, Linear.homCongr_apply,
      Linear.homCongr_symm_apply, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
      tensorPowMapIso_hom, tensorPowMapIso_inv]
    rw [coe_frobeniusSchurEnd, coe_frobeniusSchurEnd,
      ← frobeniusSchurRotate_comp_tensorPowMap, Category.assoc, ← tensorPowMap_comp, Iso.inv_hom_id,
      tensorPowMap_id, Category.comp_id]
  rw [frobeniusSchurIndicator, frobeniusSchurIndicator, ← hL, LinearMap.trace_conj']

end CommRing

end Linear

end TauCeti
