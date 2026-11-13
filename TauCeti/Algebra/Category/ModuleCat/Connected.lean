/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Hom-orthogonal splittings of the regular module over a connected ring

A ring `A` is connected when its only central idempotents are `0` and `1`. If the regular module of
`A` is a finite biproduct of nonzero modules, any splitting of the summands into two groups with no
nonzero morphisms between them gives an idempotent endomorphism of the regular module commuting
with every endomorphism, that is, right multiplication by a central idempotent. Over a connected
ring such a splitting is therefore trivial (`TauCeti.forall_or_forall_of_forall_hom_eq_zero`).

Every nonzero module receives a nonzero morphism from one of the summands of such a biproduct
decomposition of the regular module (`TauCeti.exists_hom_ne_zero_of_iso_biproduct`).

This is the connectedness step in Auslander's theorem on classes of bounded length closed under
irreducible maps, `TauCeti/Algebra/Category/ModuleCat/AuslanderReiten/Component.lean`.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace TauCeti

variable {A : Type v} [Ring A]

/-- **Every nonzero module receives a nonzero morphism from a summand of the regular module.**
If the regular module of `A` is a biproduct of modules `P j`, then every nonzero module `M` admits
a nonzero morphism `P j ⟶ M` for some `j`. -/
theorem exists_hom_ne_zero_of_iso_biproduct {J : Type*} {P : J → ModuleCat.{max v w} A}
    [HasBiproduct P] (e : ModuleCat.of A (ULift.{w} A) ≅ ⨁ P) {M : ModuleCat.{max v w} A}
    (hM : ¬ IsZero M) : ∃ (j : J) (f : P j ⟶ M), f ≠ 0 := by
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.mp fun h ↦ hM (ModuleCat.isZero_iff_subsingleton.mpr h)
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  -- The morphism out of the regular module sending `1` to `x`.
  let t : ModuleCat.of A (ULift.{w} A) ⟶ M := ModuleCat.ofHom
    (LinearMap.toSpanSingleton A M x ∘ₗ (ULift.moduleEquiv (R := A) (M := A)).toLinearMap)
  have ht : e.inv ≫ t ≠ 0 := fun h ↦ hx <| by
    have h₀ : t = 0 := by simpa using congrArg (e.hom ≫ ·) h
    simpa [t] using ConcreteCategory.congr_hom h₀ (ULift.up 1 : ULift.{w} A)
  obtain ⟨j, hj⟩ : ∃ j, biproduct.ι P j ≫ e.inv ≫ t ≠ 0 := by
    by_contra! hzero
    exact ht (biproduct.hom_ext' _ _ fun j ↦ by rw [hzero j, comp_zero])
  exact ⟨j, _, hj⟩

/-- **Connected rings admit no Hom-orthogonal splitting of the regular module.** Let the regular
module of a ring `A` without central idempotents other than `0` and `1` be a finite biproduct of
nonzero modules `P j`. If no nonzero morphism, in either direction, joins a summand satisfying a
predicate `p` to one that does not, then either all summands satisfy `p` or none does. -/
theorem forall_or_forall_of_forall_hom_eq_zero (hA : centralIdempotents A ⊆ {0, 1}) {n : ℕ}
    {P : Fin n → ModuleCat.{max v w} A} (e : ModuleCat.of A (ULift.{w} A) ≅ ⨁ P)
    (hP : ∀ j, ¬ IsZero (P j)) (p : Fin n → Prop)
    (hp : ∀ a b, p a → ¬ p b → (∀ f : P a ⟶ P b, f = 0) ∧ ∀ f : P b ⟶ P a, f = 0) :
    (∀ j, p j) ∨ ∀ j, ¬ p j := by
  classical
  let G := ModuleCat.of A (ULift.{w} A)
  -- Every endomorphism of the regular module is right multiplication by the image of `1`.
  have hom_apply_up_down (φ : G ⟶ G) (a : A) :
      (φ.hom (ULift.up a)).down = a * (φ.hom (ULift.up 1)).down := by
    have h : (ULift.up a : ULift.{w} A) = a • ULift.up 1 := by ext; simp
    rw [h, map_smul, ULift.smul_down, smul_eq_mul]
  -- The projection onto the summands satisfying `p`.
  let d (j : Fin n) : P j ⟶ P j := if p j then 𝟙 _ else 0
  let σ : ⨁ P ⟶ ⨁ P := biproduct.map d
  have hσ (ψ : ⨁ P ⟶ ⨁ P) : ψ ≫ σ = σ ≫ ψ := by
    refine biproduct.hom_ext' _ _ fun a ↦ biproduct.hom_ext _ _ fun b ↦ ?_
    simp only [σ, Category.assoc, biproduct.map_π, biproduct.ι_map_assoc, d]
    by_cases ha : p a <;> by_cases hb : p b <;>
      simp only [ha, hb, ↓reduceIte, Category.comp_id, Category.id_comp, comp_zero, zero_comp]
    · exact ((hp a b ha hb).1 _).symm
    · exact (hp b a hb ha).2 _
  have hσσ : σ ≫ σ = σ := by
    refine biproduct.hom_ext' _ _ fun a ↦ ?_
    by_cases ha : p a <;> simp [σ, d, ha]
  -- Transported to the regular module, `σ` is right multiplication by a central idempotent.
  let E : G ⟶ G := e.hom ≫ σ ≫ e.inv
  have hE (φ : G ⟶ G) : φ ≫ E = E ≫ φ := by
    have h := hσ (e.inv ≫ φ ≫ e.hom)
    simp only [Category.assoc] at h
    simp only [E, ← Category.assoc, ← cancel_mono e.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← cancel_epi e.inv]
    simpa using h
  let ε : A := (E.hom (ULift.up 1)).down
  have hE1 : E.hom (ULift.up 1) = ULift.up ε := rfl
  have hcentral : ε ∈ centralIdempotents A := by
    refine mem_centralIdempotents.mpr ⟨?_, Subring.mem_center_iff.mpr fun x ↦ ?_⟩
    · have hEE : E ≫ E = E := by simp [E, reassoc_of% hσσ]
      have h := congrArg (fun φ : G ⟶ G ↦ (φ.hom (ULift.up 1)).down) hEE
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hE1] at h
      exact (hom_apply_up_down E ε).symm.trans h
    · -- Compare `E` with right multiplication by `x`.
      let φ : G ⟶ G := ModuleCat.ofHom (LinearMap.toSpanSingleton A G (ULift.up x) ∘ₗ
        (ULift.moduleEquiv (R := A) (M := A)).toLinearMap)
      have hφ (a : A) : φ.hom (ULift.up a) = ULift.up (a * x) := rfl
      have h := congrArg (fun ψ : G ⟶ G ↦ (ψ.hom (ULift.up 1)).down) (hE φ)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hφ, one_mul, hE1] at h
      exact (hom_apply_up_down E x).symm.trans h
  -- Then `σ` is `0` or the identity, which pins down `p` on the summands.
  have hσE : σ = e.inv ≫ E ≫ e.hom := by simp [E]
  rcases hA hcentral with h0 | h1
  · right
    intro j hj
    have hE0 : E = 0 := by
      ext x
      exact (hom_apply_up_down E x.down).trans (by simp [ε] at h0; simp [h0])
    have hσ0 : σ = 0 := by rw [hσE, hE0, zero_comp, comp_zero]
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [σ, d, hj] using congrArg (biproduct.ι P j ≫ · ≫ biproduct.π P j) hσ0
  · left
    intro j
    by_contra hj
    have hE1 : E = 𝟙 G := by
      ext x
      exact (hom_apply_up_down E x.down).trans (by simp [ε] at h1; simp [h1])
    have hσ1 : σ = 𝟙 _ := by rw [hσE, hE1, Category.id_comp, Iso.inv_hom_id]
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [σ, d, hj] using (congrArg (biproduct.ι P j ≫ · ≫ biproduct.π P j) hσ1).symm

end TauCeti
