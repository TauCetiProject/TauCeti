/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Nilpotence of the radical from an additive generator

Suppose every object `X` of a preadditive category is a direct summand of a finite sum of copies of
one object `G`, in the form of morphisms `a j : X ⟶ G` and `b j : G ⟶ X` with
`∑ j, a j ≫ b j = 𝟙 X`. Then every power of the radical of the category is detected in the ring
`End G`: if the `N`-th power of the Jacobson radical of `End G` vanishes, so does the `N`-th power
of the radical of the category (`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_of_jacobson_pow_eq_bot`).
In particular the radical is nilpotent when `End G` is semiprimary, for instance Artinian
(`TauCeti.exists_jacobsonRadicalIdeal_pow_eq_bot`).

The proof composes a morphism `f : X ⟶ Y` with maps `a : G ⟶ X` and `b : Y ⟶ G`. For a radical
`f` the composite `a ≫ f ≫ b` lies in the Jacobson radical of `End G`, and for a composite of `n`
radical morphisms it lies in the `n`-th power, after inserting the decomposition of the identity
at each intermediate object (`TauCeti.comp_comp_mem_jacobson_pow`). A morphism `f` with
`a ≫ f ≫ b = 0` for all such `a` and `b` is zero (`TauCeti.eq_zero_of_forall_comp_comp_eq_zero`).

This is the form in which nilpotence of the radical is used for the module category of a
representation-finite algebra, where `G` is the sum of the indecomposable modules.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A morphism `f : X ⟶ Y` in the `n`-th power of the radical, composed with maps `G ⟶ X`
and `Y ⟶ G`, lies in the `n`-th power of the Jacobson radical of `End G`, provided every object
is a direct summand of a finite sum of copies of `G`. -/
theorem comp_comp_mem_jacobson_pow (G : C)
    (hG : ∀ X : C, ∃ (n : ℕ) (a : Fin n → (X ⟶ G)) (b : Fin n → (G ⟶ X)),
      ∑ j, a j ≫ b j = 𝟙 X) :
    ∀ (n : ℕ) {X Y : C} {f : X ⟶ Y}, f ∈ (jacobsonRadicalIdeal C ^ n).hom X Y →
      ∀ (a : G ⟶ X) (b : Y ⟶ G), End.of (a ≫ f ≫ b) ∈ Ring.jacobson (End G) ^ n
  | 0, _, _, _, _, _, _ => by
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | n + 1, X, Y, f, hf, a, b => by
    rw [pow_succ] at hf
    -- The map `f ↦ a ≫ f ≫ b` is additive, so it suffices to treat one composite.
    let φ : (X ⟶ Y) →+ End G :=
      AddMonoidHom.mk' (fun f ↦ End.of (a ≫ f ≫ b)) fun _ _ ↦ by ext; simp
    refine MorphismIdeal.mul_hom_le_iff
      (K := (Ring.jacobson (End G) ^ (n + 1)).toAddSubgroup.comap φ) |>.mpr ?_ hf
    intro Z g f hg hf
    rw [jacobsonRadicalIdeal_hom] at hg
    obtain ⟨m, a', b', hab⟩ := hG Z
    -- Insert the decomposition of `𝟙 Z` between the two factors.
    have hsum : φ (g ≫ f) = ∑ j, End.of (b' j ≫ f ≫ b) * End.of (a ≫ g ≫ a' j) := by
      ext
      have h : a ≫ g ≫ f ≫ b = a ≫ g ≫ (∑ j, a' j ≫ b' j) ≫ f ≫ b := by
        rw [hab, Category.id_comp]
      simpa [φ, Preadditive.sum_comp, Preadditive.comp_sum] using h
    rw [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, hsum, Submodule.pow_succ]
    refine sum_mem fun j _ ↦ Ideal.mul_mem_mul (comp_comp_mem_jacobson_pow G hG n hf (b' j) b) ?_
    exact mem_jacobsonRadical_self_iff_mem_jacobson.mp
      (comp_mem_jacobsonRadical_left a (comp_mem_jacobsonRadical_right hg (a' j)))

/-- If every object is a direct summand of a finite sum of copies of `G`, a morphism all of whose
composites `a ≫ f ≫ b` with `a : G ⟶ X` and `b : Y ⟶ G` vanish is zero. -/
theorem eq_zero_of_forall_comp_comp_eq_zero (G : C)
    (hG : ∀ X : C, ∃ (n : ℕ) (a : Fin n → (X ⟶ G)) (b : Fin n → (G ⟶ X)),
      ∑ j, a j ≫ b j = 𝟙 X)
    {X Y : C} {f : X ⟶ Y} (hf : ∀ (a : G ⟶ X) (b : Y ⟶ G), a ≫ f ≫ b = 0) : f = 0 := by
  obtain ⟨m, a, b, hab⟩ := hG X
  obtain ⟨m', a', b', hab'⟩ := hG Y
  calc f = (∑ i, a i ≫ b i) ≫ f ≫ ∑ j, a' j ≫ b' j := by
        rw [hab, hab', Category.id_comp, Category.comp_id]
    _ = ∑ j, ∑ i, a i ≫ (b i ≫ f ≫ a' j) ≫ b' j := by
      simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
    _ = 0 := by
      simp only [hf, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero]

/-- **The radical is nilpotent with the exponent of `End G`**: if every object is a direct summand
of a finite sum of copies of `G` and the `N`-th power of the Jacobson radical of `End G` vanishes,
then the `N`-th power of the radical of the category vanishes. -/
theorem jacobsonRadicalIdeal_pow_eq_bot_of_jacobson_pow_eq_bot (G : C)
    (hG : ∀ X : C, ∃ (n : ℕ) (a : Fin n → (X ⟶ G)) (b : Fin n → (G ⟶ X)),
      ∑ j, a j ≫ b j = 𝟙 X)
    {N : ℕ} (hN : Ring.jacobson (End G) ^ N = ⊥) : jacobsonRadicalIdeal C ^ N = ⊥ := by
  refine le_antisymm (MorphismIdeal.le_def.mpr fun X Y f hf ↦ ?_) bot_le
  rw [MorphismIdeal.mem_bot]
  refine eq_zero_of_forall_comp_comp_eq_zero G hG fun a b ↦ ?_
  have h := comp_comp_mem_jacobson_pow G hG N hf a b
  rw [hN, Ideal.mem_bot] at h
  exact congrArg End.asHom h

/-- **The radical is nilpotent** when every object is a direct summand of a finite sum of copies
of an object `G` whose endomorphism ring is semiprimary, for instance Artinian. -/
theorem exists_jacobsonRadicalIdeal_pow_eq_bot (G : C) [IsSemiprimaryRing (End G)]
    (hG : ∀ X : C, ∃ (n : ℕ) (a : Fin n → (X ⟶ G)) (b : Fin n → (G ⟶ X)),
      ∑ j, a j ≫ b j = 𝟙 X) :
    ∃ N : ℕ, jacobsonRadicalIdeal C ^ N = ⊥ := by
  obtain ⟨N, hN⟩ := IsSemiprimaryRing.isNilpotent (R := End G)
  exact ⟨N, jacobsonRadicalIdeal_pow_eq_bot_of_jacobson_pow_eq_bot G hG hN⟩

end TauCeti
