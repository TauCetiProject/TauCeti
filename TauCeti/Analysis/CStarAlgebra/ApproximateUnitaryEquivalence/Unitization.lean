/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
public import Mathlib.Analysis.CStarAlgebra.Unitization

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

The unitization relation is the one in which approximate unitary equivalence of
*-homomorphisms between AF algebras is characterized by K-theory.

## References

* M. Rørdam, *Classification of nuclear, simple C*-algebras*, in *Classification of Nuclear
  C*-Algebras. Entropy in Operator Algebras*, Encyclopaedia Math. Sci. 126, Springer, 2002,
  Definition 1.1.15.
-/

public section

open scoped CStarAlgebra

namespace TauCeti.ApproximatelyUnitarilyEquivalent

variable {A B C : Type*} [NonUnitalCStarAlgebra A]

section Unital

variable [CStarAlgebra B]

/-- For a unital algebra `B`, the unital multiplicative map `B → B⁺` sending `x` to
`1 + (x - 1_B)`. It maps unitaries of `B` to unitaries of `B⁺` acting on `B` by the same
conjugation. -/
private noncomputable def toUnitization : B →⋆* Unitization ℂ B where
  toFun x := 1 + ((x - 1 : B) : Unitization ℂ B)
  map_one' := by simp
  map_mul' x y := by
    ext
    · simp
    · simp only [Unitization.snd_mul, Unitization.fst_add, Unitization.snd_add,
        Unitization.fst_one, Unitization.snd_one, Unitization.fst_inr, Unitization.snd_inr]
      simp only [add_zero, zero_add, one_smul]
      noncomm_ring
  map_star' x := by simp [← Unitization.inr_star]

private theorem toUnitization_mul_inr (x c : B) :
    toUnitization x * (c : Unitization ℂ B) = ((x * c : B) : Unitization ℂ B) := by
  simp [toUnitization, add_mul, sub_mul, ← Unitization.inr_mul]

private theorem inr_mul_toUnitization (c x : B) :
    (c : Unitization ℂ B) * toUnitization x = ((c * x : B) : Unitization ℂ B) := by
  simp [toUnitization, mul_add, mul_sub, ← Unitization.inr_mul]

/-- For a unital target, approximate unitary equivalence with unitaries of the unitization is
approximate unitary equivalence with unitaries of the target. -/
theorem unitization_iff {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ) ↔
      ApproximatelyUnitarilyEquivalent φ ψ := by
  constructor
  · intro h
    have hlift (χ : A →⋆ₙₐ[ℂ] B) :
        (Unitization.starLift (NonUnitalStarAlgHom.id ℂ B)).toNonUnitalStarAlgHom.comp
          ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp χ) = χ :=
      NonUnitalStarAlgHom.ext fun a ↦ by
        rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply,
          StarAlgHom.coe_toNonUnitalStarAlgHom, Unitization.inrNonUnitalStarAlgHom_apply,
          ← Unitization.starLift_symm_apply_apply, Equiv.symm_apply_apply,
          NonUnitalStarAlgHom.coe_id, id_eq]
    simpa only [hlift] using h.postcomp (Unitization.starLift (NonUnitalStarAlgHom.id ℂ B))
  · intro h
    rw [approximatelyUnitarilyEquivalent_def] at h ⊢
    intro F ε hε
    obtain ⟨u, hu⟩ := h F ε hε
    refine ⟨Unitary.map toUnitization u, fun a ha ↦ ?_⟩
    have hconj : (Unitary.map toUnitization u : Unitization ℂ B) * ((φ a : B) : Unitization ℂ B) *
        star (Unitary.map toUnitization u : Unitization ℂ B) =
          (((u : B) * φ a * star (u : B) : B) : Unitization ℂ B) := by
      rw [Unitary.coe_map, ← map_star, toUnitization_mul_inr, inr_mul_toUnitization]
    simpa only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply, hconj,
      ← Unitization.inr_sub, Unitization.norm_inr] using hu a ha

end Unital

variable [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C] {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- Approximate unitary equivalence with unitaries of the unitization is preserved by
postcomposition with any star homomorphism, unital or not. -/
theorem unitization_postcomp
    (h : ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
      ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ))
    (ρ : B →⋆ₙₐ[ℂ] C) :
    ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ C).comp (ρ.comp φ))
      ((Unitization.inrNonUnitalStarAlgHom ℂ C).comp (ρ.comp ψ)) := by
  have hmap (χ : A →⋆ₙₐ[ℂ] B) :
      (Unitization.starMap ρ).toNonUnitalStarAlgHom.comp
        ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp χ) =
      (Unitization.inrNonUnitalStarAlgHom ℂ C).comp (ρ.comp χ) :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  simpa only [hmap] using h.postcomp (Unitization.starMap ρ)

end TauCeti.ApproximatelyUnitarilyEquivalent
