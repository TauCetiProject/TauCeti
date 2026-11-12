/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Tensor

/-!
# Central weight twists of normal crystals

A weight annihilating the simple coroots can be added to every weight of a normal crystal
without changing its root operators or string lengths. `NormalCrystal.weightTwist` constructs
this twist on the same carrier. The zero, addition and duality laws make the offsets explicit;
strict morphisms can be twisted by the same offset on source and target.

These twists retain the central characters of reductive root data. In particular, translating
a highest weight by a central character changes its weighted crystal even though the root
operators and their strings stay the same. The construction needs no finiteness or
semisimplicity assumption on the root datum.

`NormalCrystal.central` is the one-element crystal of a central weight. Tensoring with it
realizes the weight twist: projection and insertion are mutually inverse strict morphisms,
with the same result for either tensor-factor order, including the tie case where both relevant
string lengths vanish.

## References

* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7 (crystals and tensor products).
-/

public section

namespace TauCeti.NormalCrystal

variable {ι X Y B B' B'' : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}

variable (c : NormalCrystal P b B) (χ : X)
  (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)

/-- Add a weight annihilating the simple coroots to every weight of a normal crystal.
The root operators and string lengths are unchanged. -/
def weightTwist : NormalCrystal P b B where
  wt x := c.wt x + χ
  e := c.e
  f := c.f
  ε := c.ε
  φ := c.φ
  f_eq_some_iff := c.f_eq_some_iff
  wt_of_e_eq_some h := by rw [c.wt_of_e_eq_some h]; abel
  ε_eq_zero_iff := c.ε_eq_zero_iff
  ε_of_e_eq_some := c.ε_of_e_eq_some
  φ_eq_zero_iff := c.φ_eq_zero_iff
  φ_sub_ε i x := by simpa [map_add, hχ] using c.φ_sub_ε i x

@[simp]
theorem weightTwist_wt (x : B) : (c.weightTwist χ hχ).wt x = c.wt x + χ := (rfl)

@[simp]
theorem weightTwist_e : (c.weightTwist χ hχ).e = c.e := (rfl)

@[simp]
theorem weightTwist_f : (c.weightTwist χ hχ).f = c.f := (rfl)

@[simp]
theorem weightTwist_eIter : (c.weightTwist χ hχ).eIter = c.eIter := by
  funext i n x
  induction n generalizing x with
  | zero => simp only [eIter_zero]
  | succ n ih => simp only [eIter_succ, weightTwist_e, ih]

@[simp]
theorem weightTwist_fIter : (c.weightTwist χ hχ).fIter = c.fIter := by
  funext i n x
  induction n generalizing x with
  | zero => simp only [fIter_zero]
  | succ n ih => simp only [fIter_succ, weightTwist_f, ih]

@[simp]
theorem weightTwist_ε : (c.weightTwist χ hχ).ε = c.ε := (rfl)

@[simp]
theorem weightTwist_φ : (c.weightTwist χ hχ).φ = c.φ := (rfl)

/-- Twisting by zero leaves a normal crystal unchanged. -/
@[simp]
theorem weightTwist_zero : c.weightTwist 0 (by simp) = c := by
  apply NormalCrystal.ext
  · funext x; simp
  · simp

/-- Successive central weight twists add their offsets. -/
@[simp]
theorem weightTwist_weightTwist (ψ : X)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0) :
    (c.weightTwist χ hχ).weightTwist ψ hψ =
      c.weightTwist (χ + ψ) (by simp [map_add, hχ, hψ]) := by
  apply NormalCrystal.ext
  · funext x; simp [add_assoc]
  · simp

/-- Duality negates the central offset. -/
@[simp]
theorem dual_weightTwist : (c.weightTwist χ hχ).dual =
    c.dual.weightTwist (-χ) (by simp [hχ]) := by
  apply NormalCrystal.ext
  · funext x; simp [add_comm]
  · simp

/-- Central offsets in both tensor factors add. -/
theorem weightTwist_tensor_weightTwist (d : NormalCrystal P b B') (ψ : X)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0) :
    (c.weightTwist χ hχ).tensor (d.weightTwist ψ hψ) =
      (c.tensor d).weightTwist (χ + ψ) (by simp [map_add, hχ, hψ]) := by
  apply NormalCrystal.ext
  · funext x; simp [add_add_add_comm]
  · funext i x; simp [tensor_e]

namespace StrictHom

variable {c : NormalCrystal P b B} {d : NormalCrystal P b B'}
  {g : NormalCrystal P b B''}

/-- Twist the source and target of a strict morphism by the same central weight. -/
def weightTwist (f : StrictHom c d) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    StrictHom (c.weightTwist χ hχ) (d.weightTwist χ hχ) where
  toFun := f
  wt_toFun x := by simp
  e_toFun i x := by simp

@[simp]
theorem weightTwist_apply (f : StrictHom c d) (χ : X) (hχ) (x : B) :
    f.weightTwist χ hχ x = f x := (rfl)

@[simp]
theorem weightTwist_id : (StrictHom.id c).weightTwist χ hχ =
    StrictHom.id (c.weightTwist χ hχ) := by
  apply StrictHom.ext
  intro x
  simp

@[simp]
theorem weightTwist_comp (f : StrictHom c d) (f' : StrictHom d g) :
    (f'.comp f).weightTwist χ hχ = (f'.weightTwist χ hχ).comp (f.weightTwist χ hχ) := by
  apply StrictHom.ext
  intro x
  simp

end StrictHom

/-- The one-element normal crystal of a weight annihilating the simple coroots. -/
def central : NormalCrystal P b PUnit where
  wt _ := χ
  e _ _ := none
  f _ _ := none
  ε _ _ := 0
  φ _ _ := 0
  f_eq_some_iff := by simp
  wt_of_e_eq_some := by simp
  ε_eq_zero_iff := by simp
  ε_of_e_eq_some := by simp
  φ_eq_zero_iff := by simp
  φ_sub_ε i _ := by simp [hχ]

@[simp]
theorem central_wt (x : PUnit) : (central χ hχ).wt x = χ := (rfl)

@[simp]
theorem central_e : (central χ hχ).e = fun _ _ ↦ none := (rfl)

@[simp]
theorem central_f : (central χ hχ).f = fun _ _ ↦ none := (rfl)

@[simp]
theorem central_ε : (central χ hχ).ε = fun _ _ ↦ 0 := (rfl)

@[simp]
theorem central_φ : (central χ hχ).φ = fun _ _ ↦ 0 := (rfl)

/-- Projection identifies tensoring on the right with the central weight twist. -/
def tensorCentral : StrictHom (c.tensor (central χ hχ)) (c.weightTwist χ hχ) where
  toFun := Prod.fst
  wt_toFun x := by simp
  e_toFun i x := by
    simp [tensor_e, Option.map_map, Function.comp_def]

/-- Insert the unique central element in the right tensor factor. -/
def tensorCentralInv : StrictHom (c.weightTwist χ hχ) (c.tensor (central χ hχ)) where
  toFun x := (x, PUnit.unit)
  wt_toFun x := by simp
  e_toFun i x := by simp [tensor_e]

/-- Projection identifies tensoring on the left with the central weight twist. -/
def centralTensor : StrictHom ((central χ hχ).tensor c) (c.weightTwist χ hχ) where
  toFun := Prod.snd
  wt_toFun x := by simp [add_comm]
  e_toFun i x := by
    by_cases h : c.ε i x.2 = 0
    · simp only [weightTwist_e, tensor_e, h, central_e, Option.map_none]
      exact c.ε_eq_zero_iff.mp h
    · simp [tensor_e, h, Option.map_map]

/-- Insert the unique central element in the left tensor factor. -/
def centralTensorInv : StrictHom (c.weightTwist χ hχ) ((central χ hχ).tensor c) where
  toFun x := (PUnit.unit, x)
  wt_toFun x := by simp [add_comm]
  e_toFun i x := by
    by_cases h : c.ε i x = 0
    · simp [tensor_e, h, c.ε_eq_zero_iff.mp h]
    · simp [tensor_e, h]

@[simp]
theorem tensorCentral_apply (x : B × PUnit) : c.tensorCentral χ hχ x = x.1 := (rfl)

@[simp]
theorem tensorCentralInv_apply (x : B) : c.tensorCentralInv χ hχ x = (x, PUnit.unit) := (rfl)

@[simp]
theorem centralTensor_apply (x : PUnit × B) : c.centralTensor χ hχ x = x.2 := (rfl)

@[simp]
theorem centralTensorInv_apply (x : B) : c.centralTensorInv χ hχ x = (PUnit.unit, x) := (rfl)

@[simp]
theorem tensorCentral_comp_tensorCentralInv :
    (c.tensorCentral χ hχ).comp (c.tensorCentralInv χ hχ) =
      StrictHom.id (c.weightTwist χ hχ) := by
  apply StrictHom.ext
  intro x
  simp

@[simp]
theorem tensorCentralInv_comp_tensorCentral :
    (c.tensorCentralInv χ hχ).comp (c.tensorCentral χ hχ) =
      StrictHom.id (c.tensor (central χ hχ)) := by
  apply StrictHom.ext
  intro x
  simp

@[simp]
theorem centralTensor_comp_centralTensorInv :
    (c.centralTensor χ hχ).comp (c.centralTensorInv χ hχ) =
      StrictHom.id (c.weightTwist χ hχ) := by
  apply StrictHom.ext
  intro x
  simp

@[simp]
theorem centralTensorInv_comp_centralTensor :
    (c.centralTensorInv χ hχ).comp (c.centralTensor χ hχ) =
      StrictHom.id ((central χ hχ).tensor c) := by
  apply StrictHom.ext
  intro x
  simp

end TauCeti.NormalCrystal
