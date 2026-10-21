/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Retract

/-!
# The Eilenberg swindle

Let `X` be a retract of an object `Y` of a preadditive category, and let `Y^(ℕ)` be the
coproduct of countably many copies of `Y`. Then `X ⊞ Y^(ℕ) ≅ Y^(ℕ)`. Writing `e` for the
idempotent of `Y` determined by the retraction, if `1 - e` splits with image `X'`, one can picture
`Y` as `X ⊕ X'`: the isomorphism moves the extra copy of `X` into slot `0` and moves the copy of
`X` in slot `n` to slot `n + 1`, leaving the copies of `X'` in place. The actual construction uses
only `e` and `1 - e`, so no splitting of `1 - e` has to exist.

This is the categorical form of the Eilenberg swindle. Its main use is that a triangulated
subcategory closed under countable coproducts is closed under direct summands.

## Main definitions

* `CategoryTheory.Retract.biprodSigmaIso`: the isomorphism `X ⊞ ∐ (fun _ : ℕ ↦ Y) ≅
  ∐ (fun _ : ℕ ↦ Y)` for a retract `X` of `Y`. Its components on the summands are
  `CategoryTheory.Retract.inl_biprodSigmaIso_hom`,
  `CategoryTheory.Retract.ι_inr_biprodSigmaIso_hom`,
  `CategoryTheory.Retract.ι_zero_biprodSigmaIso_inv` and
  `CategoryTheory.Retract.ι_succ_biprodSigmaIso_inv`.

## References

* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Proposition 1.6.8.
-/

public section

universe v u

namespace CategoryTheory.Retract

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C} (h : Retract X Y)
  [HasCoproduct fun _ : ℕ ↦ Y] [HasBinaryBiproduct X (∐ fun _ : ℕ ↦ Y)]

/-- The `n`-th component of the inverse of the swindle isomorphism `h.biprodSigmaIso`: slot `0`
sends its copy of `X` to the extra summand, and slot `n + 1` sends its copy of `X` to slot
`n`; the complementary part `1 - e` of every slot stays in place. -/
private noncomputable def biprodSigmaInvComponent : ℕ → (Y ⟶ X ⊞ ∐ fun _ : ℕ ↦ Y)
  | 0 => biprod.lift h.r ((𝟙 Y - h.r ≫ h.i) ≫ Sigma.ι (fun _ : ℕ ↦ Y) 0)
  | n + 1 => biprod.lift 0
      ((𝟙 Y - h.r ≫ h.i) ≫ Sigma.ι (fun _ : ℕ ↦ Y) (n + 1) + h.r ≫ h.i ≫ Sigma.ι (fun _ : ℕ ↦ Y) n)

/-- The Eilenberg swindle: if `X` is a retract of `Y`, then adding one copy of `X` to the
countable coproduct of copies of `Y` does not change it up to isomorphism. -/
noncomputable def biprodSigmaIso : (X ⊞ ∐ fun _ : ℕ ↦ Y) ≅ ∐ fun _ : ℕ ↦ Y where
  hom := biprod.desc (h.i ≫ Sigma.ι (fun _ : ℕ ↦ Y) 0)
    (Sigma.desc fun n ↦ (𝟙 Y - h.r ≫ h.i) ≫ Sigma.ι (fun _ : ℕ ↦ Y) n +
      h.r ≫ h.i ≫ Sigma.ι (fun _ : ℕ ↦ Y) (n + 1))
  inv := Sigma.desc h.biprodSigmaInvComponent
  hom_inv_id := by
    have hi : h.i ≫ (𝟙 Y - h.r ≫ h.i) = 0 := by simp [Preadditive.comp_sub]
    have hr : (𝟙 Y - h.r ≫ h.i) ≫ h.r = 0 := by simp [Preadditive.sub_comp]
    have hir : h.r ≫ h.i ≫ (𝟙 Y - h.r ≫ h.i) = 0 := by rw [hi, comp_zero]
    have hii : (𝟙 Y - h.r ≫ h.i) ≫ (𝟙 Y - h.r ≫ h.i) = 𝟙 Y - h.r ≫ h.i := by
      simp [Preadditive.sub_comp, Preadditive.comp_sub]
    refine biprod.hom_ext' _ _ ?_ (Sigma.hom_ext _ _ fun n ↦ ?_)
    · simp [biprodSigmaInvComponent, biprod.lift_eq]
    -- Expand the composite on slot `n` without unfolding `1 - e`, then cancel with the
    -- idempotent identities above.
    · cases n <;>
        simp only [biprod.inr_desc_assoc, Sigma.ι_comp_desc_assoc, Preadditive.add_comp,
          Category.assoc, Sigma.ι_comp_desc, biprodSigmaInvComponent, biprod.lift_eq,
          Preadditive.comp_add, reassoc_of% hr, reassoc_of% hii, reassoc_of% hir,
          Retract.retract_assoc, zero_comp, zero_add, add_zero, Category.comp_id] <;>
        simp
  inv_hom_id := by
    have hri : (𝟙 Y - h.r ≫ h.i) ≫ h.r ≫ h.i = 0 := by simp [Preadditive.sub_comp]
    have hir : h.r ≫ h.i ≫ (𝟙 Y - h.r ≫ h.i) = 0 := by simp [Preadditive.comp_sub]
    have hii : (𝟙 Y - h.r ≫ h.i) ≫ (𝟙 Y - h.r ≫ h.i) = 𝟙 Y - h.r ≫ h.i := by
      simp [Preadditive.sub_comp, Preadditive.comp_sub]
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    cases n <;>
      simp only [Sigma.ι_comp_desc_assoc, biprodSigmaInvComponent, biprod.lift_desc,
        Category.assoc, Sigma.ι_comp_desc, Preadditive.add_comp, Preadditive.comp_add,
        reassoc_of% hii, reassoc_of% hri, reassoc_of% hir, Retract.retract_assoc, zero_comp,
        zero_add, add_zero, Category.comp_id] <;>
      simp

@[reassoc (attr := simp)]
lemma inl_biprodSigmaIso_hom :
    biprod.inl ≫ h.biprodSigmaIso.hom = h.i ≫ Sigma.ι (fun _ : ℕ ↦ Y) 0 := by
  simp [biprodSigmaIso]

@[reassoc (attr := simp)]
lemma ι_inr_biprodSigmaIso_hom (n : ℕ) :
    Sigma.ι (fun _ : ℕ ↦ Y) n ≫ biprod.inr ≫ h.biprodSigmaIso.hom =
      (𝟙 Y - h.r ≫ h.i) ≫ Sigma.ι (fun _ : ℕ ↦ Y) n +
        h.r ≫ h.i ≫ Sigma.ι (fun _ : ℕ ↦ Y) (n + 1) := by
  simp [biprodSigmaIso]

@[reassoc (attr := simp)]
lemma ι_zero_biprodSigmaIso_inv :
    Sigma.ι (fun _ : ℕ ↦ Y) 0 ≫ h.biprodSigmaIso.inv =
      biprod.lift h.r ((𝟙 Y - h.r ≫ h.i) ≫ Sigma.ι (fun _ : ℕ ↦ Y) 0) := by
  simp [biprodSigmaIso, biprodSigmaInvComponent]

@[reassoc (attr := simp)]
lemma ι_succ_biprodSigmaIso_inv (n : ℕ) :
    Sigma.ι (fun _ : ℕ ↦ Y) (n + 1) ≫ h.biprodSigmaIso.inv =
      biprod.lift 0 ((𝟙 Y - h.r ≫ h.i) ≫ Sigma.ι (fun _ : ℕ ↦ Y) (n + 1) +
        h.r ≫ h.i ≫ Sigma.ι (fun _ : ℕ ↦ Y) n) := by
  simp [biprodSigmaIso, biprodSigmaInvComponent]

end CategoryTheory.Retract
