/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Algebra.Unitization

/-!
# Approximate unitary equivalence with unitaries of the unitization

For star homomorphisms `φ ψ : A → B` into a possibly nonunital C⋆-algebra `B`, approximate
unitary equivalence with unitaries of the minimal unitization `B⁺ = Unitization ℂ B` is the
target-unitary relation `TauCeti.ApproximatelyUnitarilyEquivalent` for the composites of `φ` and
`ψ` with the inclusion `B → B⁺`: on every finite set some unitary `w` of `B⁺` has
`‖w φ(a) w⋆ - ψ(a)‖ < ε`, the norm being that of `B` since the inclusion is isometric. The laws
of the target-unitary relation, including the sequential criterion for separable sources, apply
to it verbatim.

This file compares the unitization relation with the target-unitary one. For a unital target
the two relations agree: a unitary `w` of `B⁺` maps to a unitary of `B` under the unital map
`B⁺ → B` extending the identity, and a unitary `u` of `B` gives the unitary
`u + (1 - 1_B)` of `B⁺`, which acts on `B` by the same conjugation. Unlike the target-unitary
relation, the unitization relation is preserved by postcomposition with every star
homomorphism, since star homomorphisms extend unitally to unitizations.

For maps into a unital target, extending the source to its minimal unitization preserves
and reflects approximate unitary equivalence. The extensions send the scalar summand of
`Unitization ℂ A` to central scalars in the target, so the finite-set estimates only depend
on the `A` coordinates. In particular, for a possibly nonunital target `B`, the unitization
relation is equivalent to approximate unitary equivalence of the unital extensions
`Unitization ℂ A → Unitization ℂ B`.

The unitization relation is the one in which approximate unitary equivalence of
*-homomorphisms between AF algebras is characterized by K-theory.

## References

* M. Rørdam, *Classification of nuclear, simple C*-algebras*, in *Classification of Nuclear
  C*-Algebras. Entropy in Operator Algebras*, Encyclopaedia Math. Sci. 126, Springer, 2002,
  Definition 1.1.15.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998,
  Chapter 7 (unitization conventions).
-/

public section

open scoped CStarAlgebra

namespace TauCeti.ApproximatelyUnitarilyEquivalent

variable {A B C : Type*} [NonUnitalCStarAlgebra A]

/-- Approximate unitary equivalence into a unital target is preserved and reflected by
extending both maps to the minimal unitization of the source. -/
@[simp]
theorem starLift_iff [CStarAlgebra B] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent (Unitization.starLift φ).toNonUnitalStarAlgHom
        (Unitization.starLift ψ).toNonUnitalStarAlgHom ↔
      ApproximatelyUnitarilyEquivalent φ ψ := by
  constructor
  · intro h
    simpa only [Unitization.starLift_comp_inr] using
      h.precomp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  · classical
    rw [approximatelyUnitarilyEquivalent_def, approximatelyUnitarilyEquivalent_def]
    intro h F ε hε
    obtain ⟨u, hu⟩ := h (F.image (fun x : Unitization ℂ A ↦ x.snd)) ε hε
    refine ⟨u, fun x hx ↦ ?_⟩
    -- Conjugation fixes the common scalar image of `x.fst`.
    have he : (u : B) * (Unitization.starLift φ) x * star (u : B) -
        (Unitization.starLift ψ) x = (u : B) * φ x.snd * star (u : B) - ψ x.snd := by
      simp [Algebra.algebraMap_eq_smul_one, mul_add, add_mul]
    simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom, he] using
      hu x.snd (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

section Unital

variable [CStarAlgebra B]

/-- For a unital target, approximate unitary equivalence with unitaries of the unitization is
approximate unitary equivalence with unitaries of the target. -/
theorem unitization_iff {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ) ↔
      ApproximatelyUnitarilyEquivalent φ ψ := by
  constructor
  · intro h
    simpa only [NonUnitalStarAlgHom.id_comp] using
      h.postcomp_of_comp_eq (κ := NonUnitalStarAlgHom.id ℂ B)
        (Unitization.starLift (NonUnitalStarAlgHom.id ℂ B)).toNonUnitalStarAlgHom
        (Unitization.starLift_comp_inr _)
  · intro h
    rw [approximatelyUnitarilyEquivalent_def] at h ⊢
    intro F ε hε
    obtain ⟨u, hu⟩ := h F ε hε
    refine ⟨Unitary.map (Unitization.oneAddInrSubOne (R := ℂ)) u, fun a ha ↦ ?_⟩
    have hconj :
        (Unitary.map (Unitization.oneAddInrSubOne (R := ℂ) (B := B)) u : Unitization ℂ B) *
          ((φ a : B) : Unitization ℂ B) *
          star (Unitary.map (Unitization.oneAddInrSubOne (R := ℂ) (B := B)) u : Unitization ℂ B) =
          (((u : B) * φ a * star (u : B) : B) : Unitization ℂ B) := by
      rw [Unitary.coe_map, ← map_star, Unitization.oneAddInrSubOne_mul_inr,
        Unitization.inr_mul_oneAddInrSubOne]
    simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply, hconj,
      ← Unitization.inr_sub, Unitization.norm_inr] using hu a ha

end Unital

variable [NonUnitalCStarAlgebra B] {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- The unital extensions are approximately unitarily equivalent exactly when the original
maps are approximately unitarily equivalent with unitaries of the target unitization. -/
@[simp]
theorem starMap_iff :
    ApproximatelyUnitarilyEquivalent (Unitization.starMap φ).toNonUnitalStarAlgHom
        (Unitization.starMap ψ).toNonUnitalStarAlgHom ↔
      ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ) := by
  simpa only [Unitization.starMap] using starLift_iff

variable [NonUnitalCStarAlgebra C]

/-- Approximate unitary equivalence with unitaries of the unitization is preserved by
postcomposition with any star homomorphism, unital or not. -/
theorem unitization_postcomp
    (h : ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
      ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ))
    (ρ : B →⋆ₙₐ[ℂ] C) :
    ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ C).comp (ρ.comp φ))
      ((Unitization.inrNonUnitalStarAlgHom ℂ C).comp (ρ.comp ψ)) := by
  simpa only [NonUnitalStarAlgHom.comp_assoc] using
    h.postcomp_of_comp_eq (κ := (Unitization.inrNonUnitalStarAlgHom ℂ C).comp ρ)
      (Unitization.starMap ρ).toNonUnitalStarAlgHom (Unitization.starLift_comp_inr _)

end TauCeti.ApproximatelyUnitarilyEquivalent
