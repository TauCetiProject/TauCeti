/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Algebra.Star.Unitary
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Approximate unitary equivalence in a unital target

Two possibly nonunital star homomorphisms into a unital C⋆-algebra are approximately
unitarily equivalent when conjugation by target unitaries approximates one by the other
on every finite set. This file proves the equivalence-relation laws and compatibility
with composition. Postcomposition is by a map preserving the unit, so implementing unitaries
remain unitaries. The relation preserves pointwise norms, hence injectivity, and for a unital
source it preserves unitality of the maps.

The convention is that of Kirchberg–Phillips, *Embedding of exact C*-algebras in the
Cuntz algebra O₂*, Definition 0.5, extended to possibly nonunital source maps.
This is the target-unitary relation, not the multiplier- or unitization-unitary relation.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

/-- Approximate unitary equivalence, implemented by unitaries of the unital target itself.
The source and the two maps need not be unital. -/
def ApproximatelyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ u : unitary B, ∀ a ∈ F, ‖(u : B) * φ a * star (u : B) - ψ a‖ < ε

/-- Finite-set characterization of approximate unitary equivalence with target unitaries. -/
theorem approximatelyUnitarilyEquivalent_def (φ ψ : A →⋆ₙₐ[ℂ] B) :
    ApproximatelyUnitarilyEquivalent φ ψ ↔
      ∀ (F : Finset A) (ε : ℝ), 0 < ε →
        ∃ u : unitary B, ∀ a ∈ F, ‖(u : B) * φ a * star (u : B) - ψ a‖ < ε :=
  Iff.rfl

namespace ApproximatelyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- A fixed unitary conjugacy gives approximate unitary equivalence. -/
theorem of_unitary (u : unitary B)
    (h : ∀ a, (u : B) * φ a * star (u : B) = ψ a) :
    ApproximatelyUnitarilyEquivalent φ ψ := by
  intro F ε hε
  exact ⟨u, fun a _ ↦ by simpa [h a] using hε⟩

/-- Approximate unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : ApproximatelyUnitarilyEquivalent φ φ :=
  of_unitary 1 (by simp)

/-- Approximate unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent ψ φ := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨star u, fun a ha ↦ ?_⟩
  have heq : ‖(star u : B) * ψ a * (u : B) - φ a‖ =
      ‖(u : B) * φ a * star (u : B) - ψ a‖ := by
    let e := Unitary.conjStarAlgAut ℂ B u
    have hn := (StarAlgEquiv.isometry e.symm).dist_eq (ψ a) (e (φ a))
    rw [e.symm_apply_apply] at hn
    simpa only [e, dist_eq_norm, Unitary.conjStarAlgAut_symm_apply,
      Unitary.conjStarAlgAut_apply, norm_sub_rev] using hn
  simpa only [Unitary.coe_star, star_star] using heq.trans_lt (hu a ha)

/-- Approximate unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : ApproximatelyUnitarilyEquivalent φ ψ)
    (h₂ : ApproximatelyUnitarilyEquivalent ψ χ) : ApproximatelyUnitarilyEquivalent φ χ := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h₁ F (ε / 2) (by positivity)
  obtain ⟨v, hv⟩ := h₂ F (ε / 2) (by positivity)
  refine ⟨v * u, fun a ha ↦ ?_⟩
  have heq : (v : B) * ((u : B) * φ a * star (u : B) - ψ a) * star (v : B) +
      ((v : B) * ψ a * star (v : B) - χ a) =
      ((v * u : unitary B) : B) * φ a * star ((v * u : unitary B) : B) - χ a := by
    simp [mul_sub, sub_mul, mul_assoc]
  rw [← heq]
  calc
    _ ≤ ‖(v : B) * ((u : B) * φ a * star (u : B) - ψ a) * star (v : B)‖ +
        ‖(v : B) * ψ a * star (v : B) - χ a‖ := norm_add_le _ _
    _ = ‖(u : B) * φ a * star (u : B) - ψ a‖ +
        ‖(v : B) * ψ a * star (v : B) - χ a‖ := by
      simpa only [Unitary.coe_star] using congrArg
        (fun x : ℝ ↦ x + ‖(v : B) * ψ a * star (v : B) - χ a‖)
        ((CStarRing.norm_mul_coe_unitary _ (star v)).trans
          (CStarRing.norm_coe_unitary_mul v _))
    _ < ε / 2 + ε / 2 := add_lt_add (hu a ha) (hv a ha)
    _ = ε := by ring

/-- The target-unitary relation is an equivalence relation. -/
theorem equivalence : Equivalence (ApproximatelyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Precomposition preserves approximate unitary equivalence, without a unitality condition. -/
theorem precomp [NonUnitalCStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : C →⋆ₙₐ[ℂ] A) : ApproximatelyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  classical
  intro F ε hε
  obtain ⟨u, hu⟩ := h (F.image ρ) ε hε
  exact ⟨u, fun a ha ↦ hu (ρ a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)⟩

/-- Postcomposition with a star homomorphism preserving the unit preserves approximate
unitary equivalence. -/
theorem postcomp_of_map_one [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₙₐ[ℂ] C) (hρ : ρ 1 = 1) :
    ApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨⟨ρ u, Unitary.map_mem_of_map_one ρ hρ u.prop⟩, fun a ha ↦ ?_⟩
  simpa only [NonUnitalStarAlgHom.comp_apply, ← map_star, ← map_mul, ← map_sub] using
    (NonUnitalStarAlgHom.norm_apply_le ρ
      ((u : B) * φ a * star (u : B) - ψ a)).trans_lt (hu a ha)

/-- Unital postcomposition preserves approximate unitary equivalence. -/
theorem postcomp [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₐ[ℂ] C) : ApproximatelyUnitarilyEquivalent
      (ρ.toNonUnitalStarAlgHom.comp φ) (ρ.toNonUnitalStarAlgHom.comp ψ) :=
  h.postcomp_of_map_one _ (map_one ρ)

/-- Unital postcomposition along a factorization `ρ ∘ ι = κ` carries approximate unitary
equivalence of the composites with `ι` to approximate unitary equivalence of the composites
with `κ`. -/
theorem postcomp_of_comp_eq [CStarAlgebra C] {D : Type*} [NonUnitalCStarAlgebra D]
    {φ ψ : A →⋆ₙₐ[ℂ] D} {ι : D →⋆ₙₐ[ℂ] B} {κ : D →⋆ₙₐ[ℂ] C}
    (h : ApproximatelyUnitarilyEquivalent (ι.comp φ) (ι.comp ψ)) (ρ : B →⋆ₐ[ℂ] C)
    (hρ : ρ.toNonUnitalStarAlgHom.comp ι = κ) :
    ApproximatelyUnitarilyEquivalent (κ.comp φ) (κ.comp ψ) := by
  subst hρ
  simpa only [NonUnitalStarAlgHom.comp_assoc] using h.postcomp ρ

/-- Approximately unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : ApproximatelyUnitarilyEquivalent φ ψ) (a : A) : ‖φ a‖ = ‖ψ a‖ := by
  have hle {φ ψ : A →⋆ₙₐ[ℂ] B} (h : ApproximatelyUnitarilyEquivalent φ ψ) :
      ‖φ a‖ ≤ ‖ψ a‖ := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨u, hu⟩ := h {a} ε hε
    have hn := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ B u) (φ a)
    have ht := norm_le_norm_add_norm_sub (ψ a) ((u : B) * φ a * star (u : B))
    rw [Unitary.conjStarAlgAut_apply] at hn
    rw [hn, norm_sub_rev] at ht
    linarith [hu a (Finset.mem_singleton_self a)]
  exact le_antisymm (hle h) (hle h.symm)

/-- Approximate unitary equivalence preserves injectivity. -/
theorem injective_iff (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ := by
  rw [injective_iff_map_eq_zero φ, injective_iff_map_eq_zero ψ]
  exact forall_congr' fun a ↦ by rw [← norm_eq_zero (a := φ a),
    ← norm_eq_zero (a := ψ a), h.norm_eq]

/-- For a unital source, approximately unitarily equivalent maps are unital together: the
image of the unit is a projection, and a projection within distance less than `1` of the unit
is the unit. -/
theorem map_one_eq_one_iff {D : Type*} [CStarAlgebra D] {f g : D →⋆ₙₐ[ℂ] B}
    (h : ApproximatelyUnitarilyEquivalent f g) : f 1 = 1 ↔ g 1 = 1 := by
  suffices key : ∀ {f g : D →⋆ₙₐ[ℂ] B}, ApproximatelyUnitarilyEquivalent f g → g 1 = 1 →
      f 1 = 1 from ⟨key h.symm, key h⟩
  intro f g h hg
  obtain ⟨u, hu⟩ := h {1} 1 one_pos
  have hlt : ‖1 - f 1‖ < 1 := by
    have heq : (u : B) * f 1 * star (u : B) - g 1 =
        Unitary.conjStarAlgAut ℂ B u (f 1 - 1) := by
      simp [hg, mul_sub, sub_mul]
    simpa only [heq, StarAlgEquiv.norm_map, norm_sub_rev] using
      hu 1 (Finset.mem_singleton_self 1)
  have hidem : IsIdempotentElem (1 - f 1) :=
    IsIdempotentElem.one_sub (by rw [IsIdempotentElem, ← map_mul, one_mul])
  by_contra hne
  exact hlt.not_ge (hidem.one_le_norm (sub_ne_zero.mpr (Ne.symm hne)))

/-- If `g ∘ f` is approximately unitarily equivalent to the identity of a unital C⋆-algebra,
then `g` is unital. -/
theorem map_one_of_comp {D : Type*} [CStarAlgebra D] {f : D →⋆ₙₐ[ℂ] B} {g : B →⋆ₙₐ[ℂ] D}
    (h : ApproximatelyUnitarilyEquivalent (g.comp f) (NonUnitalStarAlgHom.id ℂ D)) :
    g 1 = 1 := by
  have hgf : g (f 1) = 1 := h.map_one_eq_one_iff.mpr rfl
  rw [← mul_one (g 1), ← hgf, ← map_mul, one_mul, hgf]

end ApproximatelyUnitarilyEquivalent

end TauCeti
