/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Unitization
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate

/-!
# Approximate unitary equivalence with unitaries of the multiplier algebra

For star homomorphisms `φ ψ : A → B` into a possibly nonunital C⋆-algebra `B`, approximate
unitary equivalence with unitaries of the multiplier algebra `𝓜(ℂ, B)` is the target-unitary
relation `TauCeti.ApproximatelyUnitarilyEquivalent` for the composites of `φ` and `ψ` with the
canonical inclusion `B → 𝓜(ℂ, B)`. Since `B` is an ideal of `𝓜(ℂ, B)` and the inclusion is
isometric, this says that on every finite set some unitary multiplier `u` has
`‖u φ(a) u⋆ - ψ(a)‖ < ε`, with `u φ(a) u⋆` computed in `B`
(`multiplier_iff_conjStarAlgAut`). This is the general definition of approximate unitary
equivalence; the laws of the target-unitary relation, including the sequential criterion for
separable sources, apply to it verbatim.

The file compares the multiplier relation with the other two versions. It is implied by the
unitization relation, through the unital extension `B⁺ → 𝓜(ℂ, B)` of the inclusion, and for a
unital target it agrees with the target-unitary relation, since a unital C⋆-algebra is its own
multiplier algebra (`DoubleCentralizer.coeStarAlgEquiv`). The multiplier relation is preserved by
postcomposition with nondegenerate star homomorphisms `B → 𝓜(ℂ, C)`, which extend unitally to
`𝓜(ℂ, B)`; without nondegeneracy unitary multipliers of `B` need not induce unitaries of
`𝓜(ℂ, C)`.

## References

* M. Rørdam, *Classification of nuclear, simple C*-algebras*, in *Classification of Nuclear
  C*-Algebras. Entropy in Operator Algebras*, Encyclopaedia Math. Sci. 126, Springer, 2002,
  Definition 1.1.15.
-/

public section

open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti.ApproximatelyUnitarilyEquivalent

variable {A B C : Type*} [NonUnitalCStarAlgebra A]

section Unital

variable [CStarAlgebra B] {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- For a unital target, approximate unitary equivalence with unitaries of the multiplier algebra
is approximate unitary equivalence with unitaries of the target. -/
theorem multiplier_iff :
    ApproximatelyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
        ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) ↔
      ApproximatelyUnitarilyEquivalent φ ψ := by
  have hcoe (χ : A →⋆ₙₐ[ℂ] B) :
      (DoubleCentralizer.coeStarAlgEquiv ℂ B).toStarAlgHom.toNonUnitalStarAlgHom.comp χ =
        (DoubleCentralizer.coeHom (𝕜 := ℂ)).comp χ :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  have hsymm (χ : A →⋆ₙₐ[ℂ] B) :
      (DoubleCentralizer.coeStarAlgEquiv ℂ B).symm.toStarAlgHom.toNonUnitalStarAlgHom.comp
        ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp χ) = χ :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  constructor
  · intro h
    simpa only [hsymm] using h.postcomp (DoubleCentralizer.coeStarAlgEquiv ℂ B).symm.toStarAlgHom
  · intro h
    simpa only [hcoe] using h.postcomp (DoubleCentralizer.coeStarAlgEquiv ℂ B).toStarAlgHom

end Unital

variable [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C] {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- Approximate unitary equivalence with unitaries of the multiplier algebra, stated in `B`: on
every finite set, conjugation by some unitary multiplier approximates `ψ` by `φ`. -/
theorem multiplier_iff_conjStarAlgAut :
    ApproximatelyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
        ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) ↔
      ∀ (F : Finset A) (ε : ℝ), 0 < ε → ∃ u : unitary 𝓜(ℂ, B), ∀ a ∈ F,
        ‖DoubleCentralizer.conjStarAlgAut u (φ a) - ψ a‖ < ε := by
  have hnorm (u : unitary 𝓜(ℂ, B)) (a : A) :
      ‖(u : 𝓜(ℂ, B)) * DoubleCentralizer.coeHom (𝕜 := ℂ) (φ a) * star (u : 𝓜(ℂ, B)) -
          DoubleCentralizer.coeHom (𝕜 := ℂ) (ψ a)‖ =
        ‖DoubleCentralizer.conjStarAlgAut u (φ a) - ψ a‖ := by
    rw [DoubleCentralizer.coeHom_apply, DoubleCentralizer.coeHom_apply,
      ← DoubleCentralizer.coe_conjStarAlgAut_apply, ← DoubleCentralizer.coe_sub,
      DoubleCentralizer.norm_coe]
  simp only [approximatelyUnitarilyEquivalent_def, NonUnitalStarAlgHom.comp_apply, hnorm]

/-- Approximate unitary equivalence with unitaries of the unitization implies approximate unitary
equivalence with unitaries of the multiplier algebra. -/
theorem multiplier_of_unitization
    (h : ApproximatelyUnitarilyEquivalent ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp φ)
      ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp ψ)) :
    ApproximatelyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
      ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) := by
  let ι := Unitization.starLift (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B))
  have hι (χ : A →⋆ₙₐ[ℂ] B) : ι.toNonUnitalStarAlgHom.comp
      ((Unitization.inrNonUnitalStarAlgHom ℂ B).comp χ) =
        (DoubleCentralizer.coeHom (𝕜 := ℂ)).comp χ := by
    rw [← NonUnitalStarAlgHom.comp_assoc, Unitization.starLift_comp_inr]
  simpa only [hι] using h.postcomp ι

/-- Approximate unitary equivalence with unitaries of the multiplier algebra is preserved by
postcomposition with a nondegenerate star homomorphism into a multiplier algebra. -/
theorem multiplier_postcomp
    (h : ApproximatelyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
      ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ))
    {ρ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)} (hρ : ρ.IsMultiplierNondegenerate) :
    ApproximatelyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hext (χ : A →⋆ₙₐ[ℂ] B) : (ρ.extendToMultiplier hρ).toNonUnitalStarAlgHom.comp
      ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp χ) = ρ.comp χ :=
    NonUnitalStarAlgHom.ext fun _ ↦ by simp
  simpa only [hext] using h.postcomp (ρ.extendToMultiplier hρ)

end TauCeti.ApproximatelyUnitarilyEquivalent
