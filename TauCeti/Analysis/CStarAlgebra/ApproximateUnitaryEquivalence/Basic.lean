/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Approximate unitary equivalence in a unital target

Two possibly nonunital star homomorphisms into a unital C⋆-algebra are approximately
unitarily equivalent when conjugation by target unitaries approximates one by the other
on every finite set. This file proves the equivalence-relation laws and compatibility
with composition: postcomposition by a unital map pushes unitaries directly, and
postcomposition by a nonunital map `ρ` between unital C⋆-algebras uses the corner-unitized
unitary `ρ u + (1 - ρ 1)`. The relation preserves pointwise norms, hence injectivity, as well as
the condition of mapping an idempotent (in particular, a source unit) to the target unit;
consequently, approximate unitary equivalence of `ψ ∘ φ` with `id` forces `ψ` to be unital.

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

/-- Postcomposing with the inner `⋆`-automorphism of a target unitary gives an approximately
unitarily equivalent map. -/
theorem conjStarAlgAut_comp (u : unitary B) (φ : A →⋆ₙₐ[ℂ] B) :
    ApproximatelyUnitarilyEquivalent
      ((Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ) φ :=
  (of_unitary (ψ := (Unitary.conjStarAlgAut ℂ B u).toNonUnitalStarAlgHom.comp φ) u
    fun a ↦ by simp [Unitary.conjStarAlgAut_apply]).symm

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

/-- Postcomposition with a possibly nonunital `⋆`-homomorphism between unital C⋆-algebras preserves
approximate unitary equivalence, implemented by the corner-unitized unitary `ρ u + (1 - ρ 1)`. -/
theorem postcomp_nonUnital [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₙₐ[ℂ] C) : ApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  have h1l (b : B) : ρ 1 * ρ b = ρ b := by rw [← map_mul, one_mul]
  have h1r (b : B) : ρ b * ρ 1 = ρ b := by rw [← map_mul, mul_one]
  have h0l (b : B) : (1 - ρ 1) * ρ b = 0 := by rw [sub_mul, one_mul, h1l, sub_self]
  have h0r (b : B) : ρ b * (1 - ρ 1) = 0 := by rw [mul_sub, mul_one, h1r, sub_self]
  have hstar1 : star (ρ 1) = ρ 1 := by rw [← map_star, star_one]
  have hidem : (1 - ρ 1) * (1 - ρ 1) = 1 - ρ 1 := by rw [mul_sub, mul_one, h0l, sub_zero]
  let w : C := ρ u + (1 - ρ 1)
  have hw_star : star w = ρ (star (u : B)) + (1 - ρ 1) := by
    simp [w, map_star, hstar1]
  have hw_mem : w ∈ unitary C := by
    rw [Unitary.mem_iff, hw_star]
    constructor
    · calc
        (ρ (star (u : B)) + (1 - ρ 1)) * (ρ u + (1 - ρ 1))
          = ρ (star (u : B)) * ρ u + ρ (star (u : B)) * (1 - ρ 1) +
              ((1 - ρ 1) * ρ u + (1 - ρ 1) * (1 - ρ 1)) := by
            rw [add_mul, mul_add, mul_add]
        _ = ρ (star (u : B) * (u : B)) + (1 - ρ 1) := by
            rw [← map_mul, h0r, h0l, hidem, add_zero, zero_add]
        _ = 1 := by rw [Unitary.star_mul_self_of_mem u.prop, add_sub_cancel]
    · calc
        (ρ u + (1 - ρ 1)) * (ρ (star (u : B)) + (1 - ρ 1))
          = ρ u * ρ (star (u : B)) + ρ u * (1 - ρ 1) +
              ((1 - ρ 1) * ρ (star (u : B)) + (1 - ρ 1) * (1 - ρ 1)) := by
            rw [add_mul, mul_add, mul_add]
        _ = ρ ((u : B) * star (u : B)) + (1 - ρ 1) := by
            rw [← map_mul, h0r, h0l, hidem, add_zero, zero_add]
        _ = 1 := by rw [Unitary.mul_star_self_of_mem u.prop, add_sub_cancel]
  refine ⟨⟨w, hw_mem⟩, fun a ha ↦ ?_⟩
  have hconj (b : B) : w * ρ b * star w = ρ ((u : B) * b * star (u : B)) := by
    rw [hw_star]
    calc
      (ρ u + (1 - ρ 1)) * ρ b * (ρ (star (u : B)) + (1 - ρ 1))
        = (ρ u * ρ b + (1 - ρ 1) * ρ b) * (ρ (star (u : B)) + (1 - ρ 1)) := by rw [add_mul]
      _ = ρ ((u : B) * b) * (ρ (star (u : B)) + (1 - ρ 1)) := by rw [h0l, add_zero, ← map_mul]
      _ = ρ ((u : B) * b) * ρ (star (u : B)) + ρ ((u : B) * b) * (1 - ρ 1) := by rw [mul_add]
      _ = ρ ((u : B) * b * star (u : B)) := by rw [h0r, add_zero, ← map_mul]
  change ‖w * ρ (φ a) * star w - ρ (ψ a)‖ < ε
  rw [hconj, ← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le ρ _).trans_lt (hu a ha)

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

/-- Approximate unitary equivalence preserves whether an idempotent is sent to `1`, since any
idempotent within norm distance `1` of `1` equals `1`. -/
theorem map_eq_one_iff_of_isIdempotentElem (h : ApproximatelyUnitarilyEquivalent φ ψ) {e : A}
    (he : IsIdempotentElem e) : φ e = 1 ↔ ψ e = 1 := by
  have himp {φ ψ : A →⋆ₙₐ[ℂ] B} (h : ApproximatelyUnitarilyEquivalent φ ψ) (hφ : φ e = 1) :
      ψ e = 1 := by
    obtain ⟨u, hu⟩ := h {e} 1 zero_lt_one
    have hu' := hu e (Finset.mem_singleton_self e)
    rw [hφ, mul_one, Unitary.mul_star_self_of_mem u.prop, norm_sub_rev] at hu'
    exact (he.map ψ).eq_one_of_norm_sub_one_lt_one hu'
  exact ⟨himp h, himp h.symm⟩

/-- For a unital source, approximate unitary equivalence preserves unitality (`φ 1 = 1`). -/
theorem map_one_eq_one_iff {D : Type*} [CStarAlgebra D] {φ ψ : D →⋆ₙₐ[ℂ] B}
    (h : ApproximatelyUnitarilyEquivalent φ ψ) : φ 1 = 1 ↔ ψ 1 = 1 :=
  h.map_eq_one_iff_of_isIdempotentElem .one

/-- If `ψ ∘ φ` is approximately unitarily equivalent to a map `χ` sending `1` to `1` between unital
C⋆-algebras, then `ψ` maps `1` to `1`. -/
theorem map_one_of_comp {D E F : Type*} [CStarAlgebra D] [CStarAlgebra E] [CStarAlgebra F]
    {φ : D →⋆ₙₐ[ℂ] E} {ψ : E →⋆ₙₐ[ℂ] F} {χ : D →⋆ₙₐ[ℂ] F}
    (h : ApproximatelyUnitarilyEquivalent (ψ.comp φ) χ) (hχ : χ 1 = 1) : ψ 1 = 1 := by
  have h1 : ψ (φ 1) = 1 := h.map_one_eq_one_iff.mpr hχ
  calc
    ψ 1 = ψ 1 * 1 := (mul_one _).symm
    _ = ψ 1 * ψ (φ 1) := by rw [h1]
    _ = ψ (1 * φ 1) := (map_mul ψ 1 (φ 1)).symm
    _ = ψ (φ 1) := by rw [one_mul]
    _ = 1 := h1

/-- If `ψ ∘ φ` is approximately unitarily equivalent to the identity on a unital C⋆-algebra `D`,
then `ψ` maps `1` to `1`. -/
theorem map_one_of_comp_id {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]
    {φ : D →⋆ₙₐ[ℂ] E} {ψ : E →⋆ₙₐ[ℂ] D}
    (h : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (.id ℂ D)) : ψ 1 = 1 :=
  h.map_one_of_comp rfl

/-- If a `⋆`-isomorphism `θ : D ≃⋆ₐ[ℂ] E` between unital C⋆-algebras is approximately unitarily
equivalent to `φ` and `φ ∘ ψ` is approximately unitarily equivalent to `id`, then `θ.symm` is
approximately unitarily equivalent to `ψ`. -/
theorem symm_of_comp_id {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]
    {θ : D ≃⋆ₐ[ℂ] E} {φ : D →⋆ₙₐ[ℂ] E} {ψ : E →⋆ₙₐ[ℂ] D}
    (hθ : ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ)
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (.id ℂ E)) :
    ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  have h := ((hθ.precomp ψ).trans hφψ).postcomp_nonUnital θ.symm.toNonUnitalStarAlgHom
  have hcomp : θ.symm.toNonUnitalStarAlgHom.comp (θ.toNonUnitalStarAlgHom.comp ψ) = ψ := by
    ext b
    simp
  rw [hcomp, NonUnitalStarAlgHom.comp_id] at h
  exact h.symm

end ApproximatelyUnitarilyEquivalent

end TauCeti
