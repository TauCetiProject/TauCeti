/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Algebra.Star.MonoidHom
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Approximate unitary equivalence in a unital target

Two possibly nonunital star homomorphisms into a unital C⋆-algebra are approximately
unitarily equivalent when conjugation by target unitaries approximates one by the other
on every finite set. This file proves the equivalence-relation laws and compatibility
with composition: precomposition preserves the relation unconditionally, and postcomposition
by any possibly nonunital map `ρ` between unital C⋆-algebras pushes unitaries along the
corner-unitized `⋆`-monoid homomorphism `ρ u + (1 - ρ 1)`. The relation preserves pointwise
norms, hence injectivity, as well as the condition of mapping an idempotent (in particular, a
source unit) to the target unit; consequently, approximate unitary equivalence of `ψ ∘ φ` with
`id` forces `ψ` to be unital.

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

/-- Postcomposition with a possibly nonunital `⋆`-homomorphism between unital C⋆-algebras preserves
approximate unitary equivalence, implemented by pushing unitaries along
`NonUnitalStarAlgHom.unitizeStarMonoidHom` (`u ↦ ρ u + (1 - ρ 1)`). -/
theorem postcomp [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₙₐ[ℂ] C) : ApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨Unitary.map ρ.unitizeStarMonoidHom u, fun a ha ↦ ?_⟩
  simp only [NonUnitalStarAlgHom.comp_apply, Unitary.coe_map,
    ρ.unitizeStarMonoidHom_mul_apply_mul_star, ← map_sub]
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

private theorem symm_comp_of_comp {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]
    (θ : D ≃⋆ₐ[ℂ] E) {ξ : A →⋆ₙₐ[ℂ] D} {η : A →⋆ₙₐ[ℂ] E}
    (h : ApproximatelyUnitarilyEquivalent (θ.toNonUnitalStarAlgHom.comp ξ) η) :
    ApproximatelyUnitarilyEquivalent (θ.symm.toNonUnitalStarAlgHom.comp η) ξ := by
  have h' := (h.postcomp θ.symm.toNonUnitalStarAlgHom).symm
  have hcomp : θ.symm.toNonUnitalStarAlgHom.comp (θ.toNonUnitalStarAlgHom.comp ξ) = ξ := by
    ext a
    simp
  rwa [hcomp] at h'

/-- Postcomposing by `θ.symm` moves a `⋆`-isomorphism `θ : D ≃⋆ₐ[ℂ] E` between unital C⋆-algebras
across approximate unitary equivalence. -/
theorem symm_comp_iff {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]
    (θ : D ≃⋆ₐ[ℂ] E) {ξ : A →⋆ₙₐ[ℂ] D} {η : A →⋆ₙₐ[ℂ] E} :
    ApproximatelyUnitarilyEquivalent (θ.symm.toNonUnitalStarAlgHom.comp η) ξ ↔
      ApproximatelyUnitarilyEquivalent (θ.toNonUnitalStarAlgHom.comp ξ) η :=
  ⟨symm_comp_of_comp θ.symm, symm_comp_of_comp θ⟩

/-- If a `⋆`-isomorphism `θ : D ≃⋆ₐ[ℂ] E` between unital C⋆-algebras is approximately unitarily
equivalent to `φ` and `φ ∘ ψ` is approximately unitarily equivalent to `id`, then `θ.symm` is
approximately unitarily equivalent to `ψ`. -/
theorem symm_of_comp_id {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]
    {θ : D ≃⋆ₐ[ℂ] E} {φ : D →⋆ₙₐ[ℂ] E} {ψ : E →⋆ₙₐ[ℂ] D}
    (hθ : ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ)
    (hφψ : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (.id ℂ E)) :
    ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  simpa only [NonUnitalStarAlgHom.comp_id] using
    (symm_comp_iff θ).mpr ((hθ.precomp ψ).trans hφψ)

end ApproximatelyUnitarilyEquivalent

end TauCeti
