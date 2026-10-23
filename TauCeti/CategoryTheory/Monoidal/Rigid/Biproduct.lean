/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive

/-!
# Exact pairings of finite biproducts

In a monoidal preadditive category, the tensor product distributes over finite biproducts. As a
consequence, dualizable objects are closed under finite biproducts: if `Y i` is a right dual of
`X i` for every `i` in a finite index type, then `⨁ Y` is a right dual of `⨁ X`. The
coevaluation is the sum of the coevaluations of the summands and the evaluation is the sum of the
evaluations of the summands:

```
η = ∑ i, η_ (X i) (Y i) ≫ (biproduct.ι X i ⊗ₘ biproduct.ι Y i)
ε = ∑ i, (biproduct.π Y i ⊗ₘ biproduct.π X i) ≫ ε_ (X i) (Y i)
```

In a category of modules or of sheaves of modules this shows that finite free objects, which are
finite biproducts of copies of the unit, are dualizable.

In the other direction, the right dual of a binary biproduct is the biproduct of the right duals,
`(X ⊞ Y)ᘁ ≅ Xᘁ ⊞ Yᘁ`: the projections of `(X ⊞ Y)ᘁ` are the mates of the inclusions of `X ⊞ Y`,
and its inclusions are the mates of the projections.

## Main declarations

* `TauCeti.ExactPairing.biproduct`: the exact pairing between `⨁ X` and `⨁ Y` induced by exact
  pairings between `X i` and `Y i`;
* `TauCeti.ExactPairing.biproduct_ι_tensorHom_biproduct_ι_evaluation` and
  `TauCeti.ExactPairing.coevaluation_biproduct_π_tensorHom_biproduct_π`, with their `_of_ne`
  variants: the evaluation and coevaluation are, componentwise, those of the summands on the
  diagonal and zero off it;
* `TauCeti.rightDualBiprodIso`: the right dual of a binary biproduct is the biproduct of the right
  duals.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Naturality

/-- Moving a tensor product of morphisms past the inverse associator: the two middle factors
compose. -/
@[reassoc]
theorem whiskerLeft_tensorHom_associator_inv_tensorHom_whiskerRight {Z Z' A B X Y D : C}
    (a : A ⟶ X) (b : B ⟶ Y) (c : Z ⟶ Z') (d : X ⟶ D) :
    Z ◁ (a ⊗ₘ b) ≫ (α_ Z X Y).inv ≫ (c ⊗ₘ d) ▷ Y =
      (α_ Z A B).inv ≫ ((c ⊗ₘ (a ≫ d)) ⊗ₘ b) := by
  rw [← id_tensorHom, associator_inv_naturality_assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- Moving a tensor product of morphisms past the associator: the two middle factors compose. -/
@[reassoc]
theorem tensorHom_whiskerRight_associator_hom_whiskerLeft_tensorHom {Z Z' A B X Y D : C}
    (a : A ⟶ X) (b : B ⟶ Y) (c : Y ⟶ D) (d : Z ⟶ Z') :
    (a ⊗ₘ b) ▷ Z ≫ (α_ X Y Z).hom ≫ X ◁ (c ⊗ₘ d) =
      (α_ A B Z).hom ≫ (a ⊗ₘ ((b ≫ c) ⊗ₘ d)) := by
  rw [← tensorHom_id, associator_naturality_assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- The first zigzag identity of an exact pairing, with morphisms `c` and `b` inserted on the outer
factors. -/
theorem coevaluation_evaluation_tensorHom {Z X Y W : C} [ExactPairing X Y] (c : Z ⟶ Y)
    (b : Y ⟶ W) :
    Z ◁ η_ X Y ≫ (α_ Z X Y).inv ≫ ((c ⊗ₘ 𝟙 X) ⊗ₘ b) ≫ ε_ X Y ▷ W =
      (ρ_ Z).hom ≫ c ≫ b ≫ (λ_ W).inv := by
  rw [tensorHom_id, tensorHom_def, Category.assoc, whisker_exchange,
    ← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
    ExactPairing.coevaluation_evaluation_assoc, rightUnitor_naturality_assoc,
    leftUnitor_inv_naturality]

/-- The second zigzag identity of an exact pairing, with morphisms `d` and `a` inserted on the
outer factors. -/
theorem evaluation_coevaluation_tensorHom {Z X Y W : C} [ExactPairing X Y] (a : X ⟶ W)
    (d : Z ⟶ X) :
    η_ X Y ▷ Z ≫ (α_ X Y Z).hom ≫ (a ⊗ₘ (𝟙 Y ⊗ₘ d)) ≫ W ◁ ε_ X Y =
      (λ_ Z).hom ≫ d ≫ a ≫ (ρ_ W).inv := by
  rw [id_tensorHom, tensorHom_def', Category.assoc, ← whisker_exchange,
    ← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    ExactPairing.evaluation_coevaluation_assoc, leftUnitor_naturality_assoc,
    rightUnitor_inv_naturality]

end Naturality

section BinaryBiproduct

variable [Preadditive C] [MonoidalPreadditive C] (X Y : C) [HasBinaryBiproduct X Y]
  [HasRightDual X] [HasRightDual Y] [HasRightDual (X ⊞ Y)] [HasBinaryBiproduct Xᘁ Yᘁ]

/-- The right dual of `X ⊞ Y` as a binary bicone over `Xᘁ` and `Yᘁ`: its projections are the
mates of the inclusions of `X ⊞ Y`, and its inclusions are the mates of the projections. -/
private noncomputable def rightDualBinaryBicone : BinaryBicone Xᘁ Yᘁ where
  pt := (X ⊞ Y)ᘁ
  fst := (biprod.inl : X ⟶ X ⊞ Y)ᘁ
  snd := (biprod.inr : Y ⟶ X ⊞ Y)ᘁ
  inl := (biprod.fst : X ⊞ Y ⟶ X)ᘁ
  inr := (biprod.snd : X ⊞ Y ⟶ Y)ᘁ
  inl_fst := by rw [← comp_rightAdjointMate, biprod.inl_fst, rightAdjointMate_id]
  inl_snd := by rw [← comp_rightAdjointMate, biprod.inr_fst, rightAdjointMate_zero]
  inr_fst := by rw [← comp_rightAdjointMate, biprod.inl_snd, rightAdjointMate_zero]
  inr_snd := by rw [← comp_rightAdjointMate, biprod.inr_snd, rightAdjointMate_id]

/-- The right dual of a binary biproduct is the biproduct of the right duals. The components of
the isomorphism are the mates of the inclusions of `X ⊞ Y`, and the components of its inverse
are the mates of the projections. -/
noncomputable def rightDualBiprodIso : (X ⊞ Y)ᘁ ≅ Xᘁ ⊞ Yᘁ :=
  biprod.uniqueUpToIso _ _ <| isBinaryBilimitOfTotal (rightDualBinaryBicone X Y) <| by
    -- The total identity of the bicone is the mate of the total identity of `X ⊞ Y`.
    have h := congrArg rightAdjointMate (biprod.total (X := X) (Y := Y))
    rw [rightAdjointMate_add, comp_rightAdjointMate, comp_rightAdjointMate,
      rightAdjointMate_id] at h
    exact h

/-- The first component of `rightDualBiprodIso` is the mate of the first inclusion. -/
@[reassoc (attr := simp)]
theorem rightDualBiprodIso_hom_fst :
    (rightDualBiprodIso X Y).hom ≫ biprod.fst = (biprod.inl : X ⟶ X ⊞ Y)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

/-- The second component of `rightDualBiprodIso` is the mate of the second inclusion. -/
@[reassoc (attr := simp)]
theorem rightDualBiprodIso_hom_snd :
    (rightDualBiprodIso X Y).hom ≫ biprod.snd = (biprod.inr : Y ⟶ X ⊞ Y)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

/-- The first component of the inverse of `rightDualBiprodIso` is the mate of the first
projection. -/
@[reassoc (attr := simp)]
theorem inl_rightDualBiprodIso_inv :
    biprod.inl ≫ (rightDualBiprodIso X Y).inv = (biprod.fst : X ⊞ Y ⟶ X)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

/-- The second component of the inverse of `rightDualBiprodIso` is the mate of the second
projection. -/
@[reassoc (attr := simp)]
theorem inr_rightDualBiprodIso_inv :
    biprod.inr ≫ (rightDualBiprodIso X Y).inv = (biprod.snd : X ⊞ Y ⟶ Y)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

end BinaryBiproduct

variable [Preadditive C] [MonoidalPreadditive C] {ι : Type w} [Finite ι]
  (X Y : ι → C) [HasBiproduct X] [HasBiproduct Y] [∀ i, ExactPairing (X i) (Y i)]

/-- Exact pairings are closed under finite biproducts: if `Y i` is a right dual of `X i` for each
`i`, then `⨁ Y` is a right dual of `⨁ X`, with coevaluation and evaluation the sums of those of
the summands. -/
noncomputable instance ExactPairing.biproduct : ExactPairing (⨁ X) (⨁ Y) :=
  let _ : Fintype ι := Fintype.ofFinite ι
  { coevaluation' := ∑ i, η_ (X i) (Y i) ≫ (biproduct.ι X i ⊗ₘ biproduct.ι Y i)
    evaluation' := ∑ i, (biproduct.π Y i ⊗ₘ biproduct.π X i) ≫ ε_ (X i) (Y i)
    coevaluation_evaluation' := by
      classical
      -- Expand into a double sum over the coevaluation index `k` and the evaluation index `i`;
      -- only the diagonal terms survive, and they are the zigzags of the summands.
      simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
        MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc,
        whiskerLeft_tensorHom_associator_inv_tensorHom_whiskerRight_assoc]
      rw [← Category.id_comp (λ_ (⨁ Y)).inv, ← IsBilimit.total (biproduct.isBilimit Y),
        Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [biproduct.bicone_π, biproduct.bicone_ι]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i (fun k _ hk ↦ by
          rw [biproduct.ι_π_ne _ hk, MonoidalPreadditive.tensor_zero,
            MonoidalPreadditive.zero_tensor, Limits.zero_comp, Limits.comp_zero,
            Limits.comp_zero]) (by simp),
        biproduct.ι_π_self, coevaluation_evaluation_tensorHom, Category.assoc]
    evaluation_coevaluation' := by
      classical
      -- As above, only the diagonal terms of the double sum survive.
      simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
        MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc,
        tensorHom_whiskerRight_associator_hom_whiskerLeft_tensorHom_assoc]
      rw [← Category.id_comp (ρ_ (⨁ X)).inv, ← IsBilimit.total (biproduct.isBilimit X),
        Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [biproduct.bicone_π, biproduct.bicone_ι]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i (fun k _ hk ↦ by
          rw [biproduct.ι_π_ne _ hk, MonoidalPreadditive.zero_tensor,
            MonoidalPreadditive.tensor_zero, Limits.zero_comp, Limits.comp_zero,
            Limits.comp_zero]) (by simp),
        biproduct.ι_π_self, evaluation_coevaluation_tensorHom, Category.assoc] }

namespace ExactPairing

/-- The coevaluation of the biproduct pairing is the sum of the coevaluations of the summands. -/
theorem biproduct_coevaluation [Fintype ι] :
    η_ (⨁ X) (⨁ Y) = ∑ i, η_ (X i) (Y i) ≫ (biproduct.ι X i ⊗ₘ biproduct.ι Y i) :=
  by
    obtain rfl : ‹Fintype ι› = Fintype.ofFinite ι := Subsingleton.elim _ _
    rfl

/-- The evaluation of the biproduct pairing is the sum of the evaluations of the summands. -/
theorem biproduct_evaluation [Fintype ι] :
    ε_ (⨁ X) (⨁ Y) = ∑ i, (biproduct.π Y i ⊗ₘ biproduct.π X i) ≫ ε_ (X i) (Y i) :=
  by
    obtain rfl : ‹Fintype ι› = Fintype.ofFinite ι := Subsingleton.elim _ _
    rfl

variable {X Y}

/-- On the summand `Y i ⊗ X i`, the evaluation of the biproduct pairing is the evaluation of the
`i`-th summand. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_tensorHom_biproduct_ι_evaluation (i : ι) :
    (biproduct.ι Y i ⊗ₘ biproduct.ι X i) ≫ ε_ (⨁ X) (⨁ Y) = ε_ (X i) (Y i) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [biproduct_evaluation, Preadditive.comp_sum,
    Finset.sum_eq_single i (fun k _ hk ↦ by
      rw [← Category.assoc, tensorHom_comp_tensorHom, biproduct.ι_π_ne _ hk.symm,
        MonoidalPreadditive.zero_tensor, Limits.zero_comp]) (by simp),
    ← Category.assoc, tensorHom_comp_tensorHom, biproduct.ι_π_self, biproduct.ι_π_self,
    tensorHom_id, id_whiskerRight, Category.id_comp]

/-- On the summand `Y i ⊗ X j` with `i ≠ j`, the evaluation of the biproduct pairing vanishes. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_tensorHom_biproduct_ι_evaluation_of_ne {i j : ι} (h : i ≠ j) :
    (biproduct.ι Y i ⊗ₘ biproduct.ι X j) ≫ ε_ (⨁ X) (⨁ Y) = 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [biproduct_evaluation, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  obtain rfl | hk := eq_or_ne i k
  · rw [biproduct.ι_π_ne _ h.symm, MonoidalPreadditive.tensor_zero, Limits.zero_comp]
  · rw [biproduct.ι_π_ne _ hk, MonoidalPreadditive.zero_tensor, Limits.zero_comp]

/-- The coevaluation of the biproduct pairing, projected to `X i ⊗ Y i`, is the coevaluation of
the `i`-th summand. -/
@[reassoc (attr := simp)]
theorem coevaluation_biproduct_π_tensorHom_biproduct_π (i : ι) :
    η_ (⨁ X) (⨁ Y) ≫ (biproduct.π X i ⊗ₘ biproduct.π Y i) = η_ (X i) (Y i) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [biproduct_coevaluation, Preadditive.sum_comp,
    Finset.sum_eq_single i (fun k _ hk ↦ by
      rw [Category.assoc, tensorHom_comp_tensorHom, biproduct.ι_π_ne _ hk,
        MonoidalPreadditive.zero_tensor, Limits.comp_zero]) (by simp),
    Category.assoc, tensorHom_comp_tensorHom, biproduct.ι_π_self, biproduct.ι_π_self,
    tensorHom_id, id_whiskerRight, Category.comp_id]

/-- The coevaluation of the biproduct pairing, projected to `X i ⊗ Y j` with `i ≠ j`, vanishes. -/
@[reassoc (attr := simp)]
theorem coevaluation_biproduct_π_tensorHom_biproduct_π_of_ne {i j : ι} (h : i ≠ j) :
    η_ (⨁ X) (⨁ Y) ≫ (biproduct.π X i ⊗ₘ biproduct.π Y j) = 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [biproduct_coevaluation, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [Category.assoc, tensorHom_comp_tensorHom]
  obtain rfl | hk := eq_or_ne k i
  · rw [biproduct.ι_π_ne _ h, MonoidalPreadditive.tensor_zero, Limits.comp_zero]
  · rw [biproduct.ι_π_ne _ hk, MonoidalPreadditive.zero_tensor, Limits.comp_zero]

end ExactPairing

end TauCeti
