/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Approximate unitary equivalence in a unital target

Two possibly nonunital star homomorphisms into a unital C⋆-algebra are approximately
unitarily equivalent when conjugation by target unitaries approximates one by the other
on every finite set. This file proves the equivalence-relation laws, compatibility
with pre- and postcomposition (neither requiring unitality: postcomposing by a nonunital
star homomorphism `ρ : B →⋆ₙₐ[ℂ] C` pads implementing unitaries by the complementary
projection `1 - ρ 1`), norm and injectivity invariance, rigidity on central elements and
into commutative targets, automatic unitality from one-sided approximate invertibility,
and transfer of approximate unitary equivalence to the inverse of a star isomorphism.

The convention is that of Kirchberg–Phillips, *Embedding of exact C*-algebras in the
Cuntz algebra O₂*, Definition 0.5, extended to possibly nonunital source maps.
This is the target-unitary relation, not the multiplier- or unitization-unitary relation.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

section Basic

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

/-- Postcomposition into a unital C⋆-algebra preserves approximate unitary equivalence, without
assuming `ρ` is unital. -/
theorem postcomp [CStarAlgebra C] (h : ApproximatelyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₙₐ[ℂ] C) : ApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  -- Lift the implementing unitary `u` of `B` via the corner padding `ρ u + (1 - ρ 1) ∈ unitary C`.
  have hv : ρ (u : B) + (1 - ρ 1) ∈ unitary C := by
    obtain ⟨hu₁, hu₂⟩ := Unitary.mem_iff.mp u.prop
    rw [Unitary.mem_iff]
    refine ⟨?_, ?_⟩
    · simp only [star_add, star_sub, star_one, ← map_star, add_mul, mul_add, mul_sub, sub_mul,
        mul_one, one_mul, ← map_mul, hu₁]
      abel
    · simp only [star_add, star_sub, star_one, ← map_star, add_mul, mul_add, mul_sub, sub_mul,
        mul_one, one_mul, ← map_mul, hu₂]
      abel
  refine ⟨⟨ρ (u : B) + (1 - ρ 1), hv⟩, fun a ha ↦ ?_⟩
  have hconj (a : A) : (ρ (u : B) + (1 - ρ 1)) * ρ (φ a) * star (ρ (u : B) + (1 - ρ 1)) =
      ρ ((u : B) * φ a * star (u : B)) := by
    simp only [star_add, star_sub, star_one, ← map_star, add_mul, mul_add, mul_sub, sub_mul,
      mul_one, one_mul, ← map_mul, mul_assoc]
    abel
  simpa only [NonUnitalStarAlgHom.comp_apply, hconj, ← map_sub] using
    (NonUnitalStarAlgHom.norm_apply_le ρ ((u : B) * φ a * star (u : B) - ψ a)).trans_lt (hu a ha)

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

/-- If `ψ a` commutes with every unitary of `B`, then any map `φ` approximately unitarily
equivalent to `ψ` satisfies `φ a = ψ a`. -/
theorem apply_eq_of_forall_unitary_commute (h : ApproximatelyUnitarilyEquivalent φ ψ) {a : A}
    (hcomm : ∀ u : unitary B, Commute (u : B) (ψ a)) : φ a = ψ a := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨u, hu⟩ := h.symm {a} ε hε
  have hconj : (u : B) * ψ a * star (u : B) = ψ a := by
    rw [(hcomm u).eq, mul_assoc, (Unitary.mem_iff.mp u.prop).2, mul_one]
  have hlt := hu a (Finset.mem_singleton_self a)
  rw [hconj, norm_sub_rev, ← dist_eq_norm] at hlt
  exact hlt.le

/-- If `ψ a` lies in the center of `B`, then any map `φ` approximately unitarily equivalent to `ψ`
satisfies `φ a = ψ a`. -/
theorem apply_eq_of_mem_center (h : ApproximatelyUnitarilyEquivalent φ ψ) {a : A}
    (ha : ψ a ∈ Subalgebra.center ℂ B) : φ a = ψ a :=
  h.apply_eq_of_forall_unitary_commute fun u ↦ Subalgebra.mem_center_iff.mp ha u

/-- Into a commutative unital C⋆-algebra, approximate unitary equivalence reduces to equality. -/
@[simp]
theorem iff_eq [IsMulCommutative B] : ApproximatelyUnitarilyEquivalent φ ψ ↔ φ = ψ :=
  ⟨fun h ↦ DFunLike.ext _ _ fun a ↦
      h.apply_eq_of_forall_unitary_commute fun u ↦ mul_comm' (u : B) (ψ a),
    fun h ↦ h ▸ refl φ⟩

/-- Approximate unitary equivalence preserves the preimage of `1`. -/
theorem apply_eq_one_iff (h : ApproximatelyUnitarilyEquivalent φ ψ) (a : A) :
    φ a = 1 ↔ ψ a = 1 :=
  ⟨fun ha ↦ (h.symm.apply_eq_of_forall_unitary_commute fun _ ↦ ha ▸ Commute.one_right _).trans ha,
    fun ha ↦ (h.apply_eq_of_forall_unitary_commute fun _ ↦ ha ▸ Commute.one_right _).trans ha⟩

end ApproximatelyUnitarilyEquivalent

end Basic

namespace ApproximatelyUnitarilyEquivalent

/-- If `φ.comp ψ` is approximately unitarily equivalent to `.id ℂ B`, then `φ` preserves `1`
(`φ 1 = 1`), without assuming `φ` or `ψ` is unital in advance. -/
theorem map_one_of_comp_id {A B : Type*} [NonAssocSemiring A] [DistribMulAction ℂ A] [Star A]
    [CStarAlgebra B] {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (h : ApproximatelyUnitarilyEquivalent (φ.comp ψ) (.id ℂ B)) : φ 1 = 1 := by
  have h1 : φ (ψ 1) = 1 :=
    h.apply_eq_of_forall_unitary_commute fun u ↦ Commute.one_right (u : B)
  calc
    φ 1 = φ 1 * φ (ψ 1) := by rw [h1, mul_one]
    _ = φ (1 * ψ 1) := (map_mul φ 1 (ψ 1)).symm
    _ = 1 := by rw [one_mul, h1]

/-- If a star isomorphism `θ : A ≃⋆ₐ[ℂ] B` is approximately unitarily equivalent to `φ` and
`ψ.comp φ` is approximately unitarily equivalent to `.id ℂ A`, then `θ.symm` is approximately
unitarily equivalent to `ψ`. -/
theorem symm_starAlgEquiv_of_comp_id {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {θ : A ≃⋆ₐ[ℂ] B} {φ : A →⋆ₙₐ[ℂ] B} {ψ : B →⋆ₙₐ[ℂ] A}
    (hθφ : ApproximatelyUnitarilyEquivalent θ.toNonUnitalStarAlgHom φ)
    (hψφ : ApproximatelyUnitarilyEquivalent (ψ.comp φ) (.id ℂ A)) :
    ApproximatelyUnitarilyEquivalent θ.symm.toNonUnitalStarAlgHom ψ := by
  have hid : ApproximatelyUnitarilyEquivalent (.id ℂ A) (ψ.comp θ.toNonUnitalStarAlgHom) :=
    hψφ.symm.trans (hθφ.symm.postcomp ψ)
  have hpre := hid.precomp θ.symm.toNonUnitalStarAlgHom
  have hcomp : (ψ.comp θ.toNonUnitalStarAlgHom).comp θ.symm.toNonUnitalStarAlgHom = ψ := by
    ext b; simp
  rwa [NonUnitalStarAlgHom.id_comp, hcomp] at hpre

end ApproximatelyUnitarilyEquivalent

end TauCeti
