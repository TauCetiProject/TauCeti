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

A ring `A` is connected when its only central idempotents are `0` and `1`. If a module isomorphic to
the regular module of `A` is a biproduct of nonzero modules, any splitting of the summands into two
groups with no nonzero morphisms between them gives an idempotent endomorphism of the regular module
commuting with every endomorphism, that is, right multiplication by a central idempotent. Over a
connected ring such a splitting is therefore trivial
(`TauCeti.forall_or_forall_of_forall_hom_eq_zero`).

This is the connectedness step in Auslander's theorem on classes of bounded length closed under
irreducible maps, `TauCeti/Algebra/Category/ModuleCat/AuslanderReiten/Component.lean`.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace TauCeti

variable {A : Type v} [Ring A]

/-- **Connected rings admit no Hom-orthogonal splitting of the regular module.** Let `A` be a ring
without central idempotents other than `0` and `1`, and let a module `G` isomorphic to the regular
module of `A` be a biproduct of nonzero modules `P j`. If no nonzero morphism, in either direction,
joins a summand satisfying a predicate `p` to one that does not, then either all summands satisfy
`p` or none does. -/
theorem forall_or_forall_of_forall_hom_eq_zero (hA : centralIdempotents A ⊆ {0, 1})
    {G : ModuleCat.{w} A} (eG : A ≃ₗ[A] G) {J : Type*} {P : J → ModuleCat.{w} A} [HasBiproduct P]
    (e : G ≅ ⨁ P) (hP : ∀ j, ¬ IsZero (P j)) (p : J → Prop)
    (hp : ∀ a b, p a → ¬ p b → (∀ f : P a ⟶ P b, f = 0) ∧ ∀ f : P b ⟶ P a, f = 0) :
    (∀ j, p j) ∨ ∀ j, ¬ p j := by
  classical
  -- Every endomorphism of `G` is right multiplication by the element corresponding to the image
  -- of `eG 1`.
  have hom_apply (φ : G ⟶ G) (a : A) : φ.hom (eG a) = eG (a * eG.symm (φ.hom (eG 1))) := by
    have h : eG a = a • eG 1 := by simpa using eG.map_smul a 1
    rw [h, map_smul, ← smul_eq_mul, map_smul, LinearEquiv.apply_symm_apply]
  -- The projection onto the summands satisfying `p`.
  let d (j : J) : P j ⟶ P j := if p j then 𝟙 _ else 0
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
  obtain ⟨ε, hE1⟩ : ∃ ε, E.hom (eG 1) = eG ε := ⟨_, (eG.apply_symm_apply _).symm⟩
  have hEa (a : A) : E.hom (eG a) = eG (a * ε) := by
    rw [hom_apply, hE1, LinearEquiv.symm_apply_apply]
  have hcentral : ε ∈ centralIdempotents A := by
    refine mem_centralIdempotents.mpr ⟨?_, Subring.mem_center_iff.mpr fun x ↦ ?_⟩
    · have hEE : E ≫ E = E := by simp [E, reassoc_of% hσσ]
      have h := congrArg (fun φ : G ⟶ G ↦ φ.hom (eG 1)) hEE
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hE1, hEa] at h
      exact eG.injective h
    · -- Compare `E` with right multiplication by `x`.
      let φ : G ⟶ G := ModuleCat.ofHom (LinearMap.toSpanSingleton A G (eG x) ∘ₗ
        eG.symm.toLinearMap)
      have hφ (a : A) : φ.hom (eG a) = eG (a * x) := by
        simp [φ, ← smul_eq_mul]
      have h := congrArg (fun ψ : G ⟶ G ↦ ψ.hom (eG 1)) (hE φ)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hφ, one_mul, hE1, hEa] at h
      exact eG.injective h
  -- Then `σ` is `0` or the identity, which pins down `p` on the summands.
  have hσE : σ = e.inv ≫ E ≫ e.hom := by simp [E]
  rcases hA hcentral with h0 | h1
  · right
    intro j hj
    have hE0 : E = 0 := by
      ext y
      obtain ⟨a, rfl⟩ := eG.surjective y
      simp [hEa, h0]
    have hσ0 : σ = 0 := by rw [hσE, hE0, zero_comp, comp_zero]
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [σ, d, hj] using congrArg (biproduct.ι P j ≫ · ≫ biproduct.π P j) hσ0
  · left
    intro j
    by_contra hj
    have hE1 : E = 𝟙 G := by
      ext y
      obtain ⟨a, rfl⟩ := eG.surjective y
      simp [hEa, Set.mem_singleton_iff.mp h1]
    have hσ1 : σ = 𝟙 _ := by rw [hσE, hE1, Category.id_comp, Iso.inv_hom_id]
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [σ, d, hj] using (congrArg (biproduct.ι P j ≫ · ≫ biproduct.π P j) hσ1).symm

end TauCeti
