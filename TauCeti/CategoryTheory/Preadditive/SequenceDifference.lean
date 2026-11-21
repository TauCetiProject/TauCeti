/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The sequence–difference map of a sequence

Let `X : ℕ ⥤ T` be a sequence `X₀ → X₁ → X₂ → ⋯` in a preadditive category whose terms admit a
countable coproduct `∐ X.obj`. The *sequence–difference map* is the endomorphism
`1 - s : ∐ X.obj ⟶ ∐ X.obj` (`CategoryTheory.Functor.sequenceDifference`) sending the `n`-th
summand `Xₙ` to `ιₙ - φₙ ≫ ιₙ₊₁`. A morphism out of `∐ X.obj` annihilates `sequenceDifference` if
and only if its components form a cocone over `X`
(`CategoryTheory.Functor.sequenceDifference_comp_eq_zero_iff`,
`CategoryTheory.Functor.coconeOfSequenceDifference`).

This is the sequential dual of `TauCeti.CategoryTheory.Preadditive.TowerDifference`.

## Main declarations

* `CategoryTheory.Functor.sequenceDifference`: the difference map `1 - s : ∐ X.obj ⟶ ∐ X.obj`.
* `CategoryTheory.Functor.ι_sequenceDifference`: its restriction to the `n`-th summand.
* `CategoryTheory.Functor.sequenceDifference_comp_eq_zero_iff`: compatibility criterion for
  morphisms out of `∐ X.obj`.
* `CategoryTheory.Functor.coconeOfSequenceDifference`: the cocone over `X` attached to a morphism
  annihilating `sequenceDifference`.
* `CategoryTheory.Functor.sequenceDifference_naturality`: naturality in morphisms of sequences.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor

section SequenceDifference

variable {T : Type u} [Category.{v} T] [Preadditive T]
variable (X : ℕ ⥤ T) [HasCoproduct X.obj]

/-- The *sequence–difference map* `1 - s` of a sequence `X₀ → X₁ → ⋯`: the endomorphism
of `∐ X.obj` sending the `n`-th summand `Xₙ` to `ιₙ - φₙ ≫ ιₙ₊₁` (`ι_sequenceDifference`).
Its cone in a pretriangulated category is a Milnor homotopy colimit of `X`. -/
def sequenceDifference : (∐ X.obj) ⟶ (∐ X.obj) :=
  Sigma.desc fun n ↦
    Sigma.ι X.obj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1)

@[reassoc (attr := simp)]
lemma ι_sequenceDifference (n : ℕ) :
    Sigma.ι X.obj n ≫ X.sequenceDifference =
      Sigma.ι X.obj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1) := by
  simp [sequenceDifference]

/-- A morphism `ψ` out of `∐ X.obj` annihilates the sequence–difference map if and only if
its components `Sigma.ι X.obj n ≫ ψ` are compatible with the transition maps `Xₙ ⟶ Xₙ₊₁`. -/
lemma sequenceDifference_comp_eq_zero_iff {Y : T} (ψ : (∐ X.obj) ⟶ Y) :
    X.sequenceDifference ≫ ψ = 0 ↔
      ∀ n, X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι X.obj (n + 1) ≫ ψ =
        Sigma.ι X.obj n ≫ ψ := by
  refine ⟨fun h n ↦ ?_, fun h ↦ Sigma.hom_ext _ _ fun n ↦ ?_⟩
  · have h' := Sigma.ι X.obj n ≫= h
    simp only [ι_sequenceDifference_assoc, Preadditive.sub_comp, Category.assoc, comp_zero] at h'
    exact (sub_eq_zero.1 h').symm
  · simp [Preadditive.sub_comp, Category.assoc, h n]

variable {X} in
/-- A morphism out of `∐ X.obj` annihilating the sequence–difference map defines a cocone over
`X`, with components `Sigma.ι X.obj n ≫ ψ`. -/
@[expose, simps pt]
def coconeOfSequenceDifference {Y : T} (ψ : (∐ X.obj) ⟶ Y)
    (w : X.sequenceDifference ≫ ψ = 0) : Cocone X where
  pt := Y
  ι := NatTrans.ofSequence (fun n ↦ Sigma.ι X.obj n ≫ ψ) fun n ↦ by
    simp [(X.sequenceDifference_comp_eq_zero_iff ψ).1 w n]

@[simp]
lemma coconeOfSequenceDifference_ι_app {Y : T} (ψ : (∐ X.obj) ⟶ Y)
    (w : X.sequenceDifference ≫ ψ = 0) (n : ℕ) :
    (coconeOfSequenceDifference ψ w).ι.app n = Sigma.ι X.obj n ≫ ψ := (rfl)

/-- If `X.sequenceDifference ≫ ψ = 0`, then the components `Sigma.ι X.obj n ≫ ψ` are
compatible with every composite transition `Xₙ ⟶ Xₘ` (`n ≤ m`). -/
lemma map_homOfLE_comp_ι_of_sequenceDifference_comp_eq_zero {Y : T} {ψ : (∐ X.obj) ⟶ Y}
    (w : X.sequenceDifference ≫ ψ = 0) {n m : ℕ} (hnm : n ≤ m) :
    X.map (homOfLE hnm) ≫ Sigma.ι X.obj m ≫ ψ = Sigma.ι X.obj n ≫ ψ :=
  (coconeOfSequenceDifference ψ w).w (homOfLE hnm)

/-- The legs of any cocone over `X` annihilate the sequence–difference map. -/
@[reassoc (attr := simp)]
lemma sequenceDifference_desc_ι_app (c : Cocone X) :
    X.sequenceDifference ≫ Sigma.desc (fun n : ℕ ↦ c.ι.app n) = 0 :=
  (X.sequenceDifference_comp_eq_zero_iff _).2 fun n ↦ by simp

/-- The sequence–difference map is natural in morphisms of sequences `α : X ⟶ Y`. -/
@[reassoc]
lemma sequenceDifference_naturality {X Y : ℕ ⥤ T} [HasCoproduct X.obj] [HasCoproduct Y.obj]
    (α : X ⟶ Y) :
    X.sequenceDifference ≫ Limits.Sigma.map (fun n ↦ α.app n) =
      Limits.Sigma.map (fun n ↦ α.app n) ≫ Y.sequenceDifference :=
  Sigma.hom_ext _ _ fun n ↦ by
    simp only [ι_sequenceDifference_assoc, Sigma.ι_map_assoc, ι_sequenceDifference,
      Preadditive.sub_comp, Preadditive.comp_sub, Sigma.ι_map, Category.assoc,
      α.naturality_assoc]

end SequenceDifference

end CategoryTheory.Functor
