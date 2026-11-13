/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import TauCeti.Algebra.Star.Basic
public import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Approximate unitary equivalence in a unital target

Two possibly nonunital star homomorphisms into a unital C⋆-algebra are approximately
unitarily equivalent when conjugation by target unitaries approximates one by the other
on every finite set. This file proves the equivalence-relation laws and compatibility
with composition. Postcomposition is by a unital map, so implementing unitaries remain
unitaries. The relation preserves pointwise norms, injectivity, and unitality; in
particular, if `ψ.comp φ` is approximately unitarily equivalent to the identity on a unital
C⋆-algebra, then `ψ` must preserve `1`.

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

/-- Conjugating a map by a target unitary gives an approximately unitarily equivalent map. -/
theorem conjStarAlgAut_comp (u : unitary B) (φ : A →⋆ₙₐ[ℂ] B) :
    ApproximatelyUnitarilyEquivalent
      ((Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ) φ :=
  (of_unitary u fun a ↦ by simp [Unitary.conjStarAlgAut_apply]).symm

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

/-- Unital postcomposition preserves approximate unitary equivalence. -/
theorem postcomp [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₐ[ℂ] C) : ApproximatelyUnitarilyEquivalent
      (ρ.toNonUnitalStarAlgHom.comp φ) (ρ.toNonUnitalStarAlgHom.comp ψ) := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨Unitary.map (StarMonoidHom.ofClass ρ) u, fun a ha ↦ ?_⟩
  -- The class-to-bundled star-monoid hom has no coercion simp lemma.
  have hρ (b : B) : (StarMonoidHom.ofClass ρ) b = ρ b := rfl
  simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
    Unitary.coe_map, hρ, ← map_star, ← map_mul, ← map_sub] using
    (NonUnitalStarAlgHom.norm_apply_le ρ
      ((u : B) * φ a * star (u : B) - ψ a)).trans_lt (hu a ha)

/-- Postcomposition by a non-unital `⋆`-homomorphism preserving `1` preserves approximate unitary
equivalence. -/
theorem postcomp_of_map_one [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₙₐ[ℂ] C) (hρ : ρ 1 = 1) :
    ApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  simpa using h.postcomp (StarAlgHom.ofNonUnitalStarAlgHom ρ hρ)

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

section UnitalSource

/-- Between unital C⋆-algebras, approximate unitary equivalence preserves unitality (`φ 1 = 1`). -/
theorem map_one_eq_one_iff {A : Type*} [CStarAlgebra A] {φ ψ : A →⋆ₙₐ[ℂ] B}
    (h : ApproximatelyUnitarilyEquivalent φ ψ) : φ 1 = 1 ↔ ψ 1 = 1 := by
  suffices ∀ {φ ψ : A →⋆ₙₐ[ℂ] B}, ApproximatelyUnitarilyEquivalent φ ψ → ψ 1 = 1 → φ 1 = 1 from
    ⟨fun hφ ↦ this h.symm hφ, this h⟩
  intro φ ψ h hψ
  obtain ⟨u, hu⟩ := h {1} 1 zero_lt_one
  let e := Unitary.conjStarAlgAut ℂ B u
  have hproj : IsStarProjection (e (φ 1)) := ((IsStarProjection.one A).map φ).map e
  have hlt : ‖e (φ 1) - 1‖ < 1 := by
    simpa only [e, Unitary.conjStarAlgAut_apply, hψ] using hu 1 (Finset.mem_singleton_self 1)
  exact e.injective <| (hproj.eq_one_of_norm_sub_one_lt_one hlt).trans (map_one e).symm

/-- If `ψ.comp φ` is approximately unitarily equivalent to the identity on a unital C⋆-algebra `A`,
then `ψ` preserves `1`. -/
theorem map_one_of_comp_id {A : Type*} [CStarAlgebra A] {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (h : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (.id ℂ A)) : ψ 1 = 1 := by
  have h1 : ψ (φ 1) = 1 := h.map_one_eq_one_iff.mpr rfl
  calc
    ψ 1 = ψ (φ 1) * ψ 1 := by rw [h1, one_mul]
    _ = ψ (φ 1 * 1) := (map_mul ψ _ _).symm
    _ = ψ (φ 1) := by rw [mul_one]
    _ = 1 := h1

/-- If `ψ.comp φ` is approximately unitarily equivalent to `.id ℂ A` and a `⋆`-isomorphism
`θ : A ≃⋆ₐ[ℂ] B` is approximately unitarily equivalent to `φ`, then `θ.symm` is approximately
unitarily equivalent to `ψ`. -/
theorem symm_of_comp_id {A : Type*} [CStarAlgebra A] {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    {θ : A ≃⋆ₐ[ℂ] B}
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (.id ℂ A))
    (hθ : ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ) :
    ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  have h1 : ApproximatelyUnitarilyEquivalent (ψ.comp θ.toNonUnitalStarAlgHom) (.id ℂ A) :=
    (hθ.postcomp_of_map_one ψ hψφ.map_one_of_comp_id).trans hψφ
  have h2 := h1.precomp θ.symm.toNonUnitalStarAlgHom
  have hcomp : (ψ.comp θ.toNonUnitalStarAlgHom).comp θ.symm.toNonUnitalStarAlgHom = ψ := by
    ext b
    simp
  rw [hcomp, NonUnitalStarAlgHom.id_comp] at h2
  exact h2.symm

end UnitalSource

end ApproximatelyUnitarilyEquivalent

end TauCeti
