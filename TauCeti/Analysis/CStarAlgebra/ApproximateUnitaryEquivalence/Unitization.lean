/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Approximate unitary equivalence in the minimal unitization

For possibly nonunital C⋆-algebras, `UnitizationApproximatelyUnitarilyEquivalent` uses
unitaries of the minimal unitization of the target. This is the relation used in uniqueness
of maps between nonunital AF algebras. It is an equivalence relation, is functorial for
arbitrary star homomorphisms on both sides, and has a sequential characterization for
separable sources. Unlike multiplier-unitary equivalence, postcomposition here needs no
nondegeneracy assumption: every map extends unitally to the minimal unitizations.

We also identify this relation with target-unitary equivalence of the unital extensions.
The key observation is that conjugation fixes the scalar summand of a unitization, so
finite-set estimates on its ideal summand suffice.

The convention follows Rørdam, *Classification of Nuclear C*-Algebras* (2002), §1.3,
and Blackadar, *K-Theory for Operator Algebras*, Chapter 7.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Approximate unitary equivalence with implementing unitaries in the minimal unitization
of the target. Neither algebra nor either map is required to be unital. -/
def UnitizationApproximatelyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ApproximatelyUnitarilyEquivalent
    ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
    ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ)

/-- Finite-set characterization with unitaries of the minimal unitization. -/
theorem unitizationApproximatelyUnitarilyEquivalent_def {φ ψ : A →⋆ₙₐ[ℂ] B} :
    UnitizationApproximatelyUnitarilyEquivalent φ ψ ↔
      ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ u : unitary (Unitization ℂ B),
        ∀ a ∈ F, ‖(u : Unitization ℂ B) * (φ a : Unitization ℂ B) *
          star (u : Unitization ℂ B) - (ψ a : Unitization ℂ B)‖ < ε :=
  approximatelyUnitarilyEquivalent_def _ _

namespace ApproximatelyUnitarilyEquivalent

variable [CStarAlgebra C] {φ ψ : A →⋆ₙₐ[ℂ] C}

/-- Extending both maps unitally preserves target-unitary approximate equivalence.
The scalar summand is fixed by every implementing conjugation. -/
theorem starLift (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent (Unitization.starLift φ).toNonUnitalStarAlgHom
      (Unitization.starLift ψ).toNonUnitalStarAlgHom := by
  classical
  rw [approximatelyUnitarilyEquivalent_def] at h ⊢
  intro F ε hε
  obtain ⟨u, hu⟩ := h (F.image (fun x : Unitization ℂ A ↦ x.snd)) ε hε
  refine ⟨u, fun x hx ↦ ?_⟩
  have hs := hu x.snd (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hi (f : A →⋆ₙₐ[ℂ] C) (a : A) :
      (Unitization.starLift f) (a : Unitization ℂ A) = f a := by
    rw [← Unitization.starLift_symm_apply_apply, Equiv.symm_apply_apply]
  have he : (u : C) * (Unitization.starLift φ) x * star (u : C) -
      (Unitization.starLift ψ) x = (u : C) * φ x.snd * star (u : C) - ψ x.snd := by
    induction x using Unitization.ind with
    | inl_add_inr r a =>
      simp only [Unitization.snd_add, Unitization.snd_inr, map_add, hi,
        ← Unitization.algebraMap_eq_inl, AlgHomClass.commutes]
      simp [Algebra.algebraMap_eq_smul_one, mul_add, add_mul]
  simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom, he] using hs

end ApproximatelyUnitarilyEquivalent

namespace UnitizationApproximatelyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- A fixed conjugacy by a unitization unitary gives approximate unitary equivalence. -/
theorem of_unitary (u : unitary (Unitization ℂ B))
    (h : ∀ a, (u : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u : Unitization ℂ B) = (ψ a : Unitization ℂ B)) :
    UnitizationApproximatelyUnitarilyEquivalent φ ψ :=
  ApproximatelyUnitarilyEquivalent.of_unitary u h

/-- Unitization-unitary approximate equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : UnitizationApproximatelyUnitarilyEquivalent φ φ :=
  ApproximatelyUnitarilyEquivalent.refl _

/-- Unitization-unitary approximate equivalence is symmetric. -/
@[symm]
theorem symm (h : UnitizationApproximatelyUnitarilyEquivalent φ ψ) :
    UnitizationApproximatelyUnitarilyEquivalent ψ φ :=
  ApproximatelyUnitarilyEquivalent.symm h

/-- Unitization-unitary approximate equivalence is transitive. -/
@[trans]
theorem trans (h₁ : UnitizationApproximatelyUnitarilyEquivalent φ ψ)
    (h₂ : UnitizationApproximatelyUnitarilyEquivalent ψ χ) :
    UnitizationApproximatelyUnitarilyEquivalent φ χ :=
  ApproximatelyUnitarilyEquivalent.trans h₁ h₂

/-- The unitization-unitary relation is an equivalence relation. -/
theorem equivalence :
    Equivalence (UnitizationApproximatelyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Precomposition, in particular restriction to a subalgebra, preserves the relation. -/
theorem precomp [NonUnitalCStarAlgebra C]
    (h : UnitizationApproximatelyUnitarilyEquivalent φ ψ) (ρ : C →⋆ₙₐ[ℂ] A) :
    UnitizationApproximatelyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) :=
  ApproximatelyUnitarilyEquivalent.precomp h ρ

/-- Unitization-unitary approximate equivalence is exactly target-unitary approximate
equivalence of the unital extensions to the minimal unitizations. -/
theorem iff_starMap : UnitizationApproximatelyUnitarilyEquivalent φ ψ ↔
    ApproximatelyUnitarilyEquivalent (Unitization.starMap φ).toNonUnitalStarAlgHom
      (Unitization.starMap ψ).toNonUnitalStarAlgHom := by
  constructor
  · exact ApproximatelyUnitarilyEquivalent.starLift
  · intro h
    have hi (f : A →⋆ₙₐ[ℂ] B) :
        (Unitization.starMap f).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ A) =
        (Unitization.inrNonUnitalStarAlgHom ℂ B).comp f := by
      ext a : 1
      simp only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
        Unitization.inrNonUnitalStarAlgHom_apply, Unitization.starMap_inr]
    simpa only [hi, UnitizationApproximatelyUnitarilyEquivalent] using
      h.precomp (Unitization.inrNonUnitalStarAlgHom ℂ A)

/-- Every star homomorphism preserves unitization-unitary approximate equivalence,
without a nondegeneracy assumption. -/
theorem postcomp [NonUnitalCStarAlgebra C]
    (h : UnitizationApproximatelyUnitarilyEquivalent φ ψ) (ρ : B →⋆ₙₐ[ℂ] C) :
    UnitizationApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hp := ApproximatelyUnitarilyEquivalent.postcomp h (Unitization.starMap ρ)
  have hi (f : A →⋆ₙₐ[ℂ] B) :
      (Unitization.starMap ρ).toNonUnitalStarAlgHom.comp
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp f) =
      (Unitization.inrNonUnitalStarAlgHom ℂ C).comp (ρ.comp f) := by
    ext a : 1
    simp only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      Unitization.inrNonUnitalStarAlgHom_apply, Unitization.starMap_inr]
  simpa only [hi, UnitizationApproximatelyUnitarilyEquivalent] using hp

/-- Equivalent maps have the same pointwise norm, even for nonunital targets. -/
theorem norm_eq (h : UnitizationApproximatelyUnitarilyEquivalent φ ψ) (a : A) :
    ‖φ a‖ = ‖ψ a‖ := by
  simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
    Unitization.norm_inr] using ApproximatelyUnitarilyEquivalent.norm_eq h a

/-- Unitization-unitary approximate equivalence preserves injectivity. -/
theorem injective_iff (h : UnitizationApproximatelyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ := by
  rw [injective_iff_map_eq_zero φ, injective_iff_map_eq_zero ψ]
  exact forall_congr' fun a ↦ by
    rw [← norm_eq_zero (a := φ a), ← norm_eq_zero (a := ψ a), h.norm_eq]

/-- Any convergent net of unitization conjugacies gives approximate unitary equivalence. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → unitary (Unitization ℂ B))
    (h : ∀ a, Tendsto (fun i ↦ (u i : Unitization ℂ B) * (φ a : Unitization ℂ B) *
      star (u i : Unitization ℂ B)) l (𝓝 (ψ a : Unitization ℂ B))) :
    UnitizationApproximatelyUnitarilyEquivalent φ ψ :=
  ApproximatelyUnitarilyEquivalent.of_tendsto u h

/-- For a separable source, one sequence of unitization unitaries implements the relation. -/
theorem iff_exists_unitary_seq [TopologicalSpace.SeparableSpace A] :
    UnitizationApproximatelyUnitarilyEquivalent φ ψ ↔
      ∃ u : ℕ → unitary (Unitization ℂ B), ∀ a,
        Tendsto (fun n ↦ (u n : Unitization ℂ B) * (φ a : Unitization ℂ B) *
          star (u n : Unitization ℂ B)) atTop (𝓝 (ψ a : Unitization ℂ B)) :=
  ApproximatelyUnitarilyEquivalent.iff_exists_unitary_seq

end UnitizationApproximatelyUnitarilyEquivalent

end TauCeti
