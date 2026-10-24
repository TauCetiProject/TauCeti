/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# The induced action on the multiplier algebra

A point-norm continuous action `α` of `G` on a C⋆-algebra `A` extends to an action
`α.multiplier : G →* (𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A))` on the multiplier algebra, where `g` acts by
the unique extension `DoubleCentralizer.congr (α g)` of `α g`. On a multiplier `(L, R)` it is
given by `(α g ∘ L ∘ α g⁻¹, α g ∘ R ∘ α g⁻¹)`, and it restricts to `α` on `A`.

The extended action is generally not point-norm continuous; for instance, translation on
`C₀(ℝ)` does not act norm-continuously on `C_b(ℝ)`. It is strictly continuous: for every
multiplier `m` and every `a : A`, both `g ↦ α.multiplier g m * a` and
`g ↦ a * α.multiplier g m` are norm continuous.
Mathlib has no strict topology on `𝓜(ℂ, A)`, so this continuity is stated pointwise. No
continuity of inversion in `G` is assumed. This is the form in which multiplier-valued
covariant homomorphisms and unitary group maps into multiplier algebras are compared with
actions. An operator implements an action on the multiplier extension of a nondegenerate
representation exactly when it does so on the coefficient algebra, `mul_multiplierExtension_iff`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for the extension of
  dynamical systems to multiplier algebras and its strict continuity.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-- The action induced on the multiplier algebra: `g` acts by the unique extension of `α g`. -/
def multiplier (α : CStarAction G A) : G →* (𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)) :=
  DoubleCentralizer.congrAut.comp α.toMonoidHom

theorem multiplier_apply (α : CStarAction G A) (g : G) :
    α.multiplier g = DoubleCentralizer.congr (α g) :=
  DoubleCentralizer.congrAut_apply (α g)

@[simp]
theorem multiplier_apply_fst (α : CStarAction G A) (g : G) (m : 𝓜(ℂ, A)) (a : A) :
    (α.multiplier g m).fst a = α g (m.fst (α g⁻¹ a)) := by
  simp [multiplier_apply]

@[simp]
theorem multiplier_apply_snd (α : CStarAction G A) (g : G) (m : 𝓜(ℂ, A)) (a : A) :
    (α.multiplier g m).snd a = α g (m.snd (α g⁻¹ a)) := by
  simp [multiplier_apply]

/-- The inverse of an automorphism of the induced action is the action of the inverse element. -/
@[simp]
theorem multiplier_symm_apply (α : CStarAction G A) (g : G) (m : 𝓜(ℂ, A)) :
    (α.multiplier g).symm m = α.multiplier g⁻¹ m := by
  rw [map_inv, StarAlgEquiv.aut_inv]

/-- The induced action restricts to the original action on `A`. -/
@[simp]
theorem multiplier_coe (α : CStarAction G A) (g : G) (a : A) :
    α.multiplier g (a : 𝓜(ℂ, A)) = (α g a : 𝓜(ℂ, A)) := by
  simp [multiplier_apply]

/-- The induced action is the unique action on `𝓜(ℂ, A)` by star-algebra automorphisms that
restricts to `α` on `A`. -/
theorem eq_multiplier_of_apply_coe (α : CStarAction G A)
    (β : G →* (𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A))) (hβ : ∀ g (a : A), β g a = (α g a : 𝓜(ℂ, A))) :
    β = α.multiplier :=
  MonoidHom.ext fun g => StarAlgEquiv.ext <| congrFun <| multiplier_apply α g ▸
    DoubleCentralizer.eq_congr_of_apply_coe (α g) (β g) (hβ g)

/-- Strict continuity of the induced action, for the left centralizer. -/
theorem continuous_multiplier_apply_fst (α : CStarAction G A) (m : 𝓜(ℂ, A)) (a : A) :
    Continuous fun g => (α.multiplier g m).fst a := by
  simp only [multiplier_apply_fst]
  exact α.continuous_apply continuous_id (m.fst.continuous.comp (α.continuous_inv_apply a))

/-- Strict continuity of the induced action, for the right centralizer. -/
theorem continuous_multiplier_apply_snd (α : CStarAction G A) (m : 𝓜(ℂ, A)) (a : A) :
    Continuous fun g => (α.multiplier g m).snd a := by
  simp only [multiplier_apply_snd]
  exact α.continuous_apply continuous_id (m.snd.continuous.comp (α.continuous_inv_apply a))

/-- Strict continuity of the induced action: right products with elements of `A` vary norm
continuously. -/
theorem continuous_multiplier_apply_mul_coe (α : CStarAction G A) (m : 𝓜(ℂ, A)) (a : A) :
    Continuous fun g => α.multiplier g m * (a : 𝓜(ℂ, A)) := by
  simp only [DoubleCentralizer.mul_coe_eq_coe_fst]
  exact DoubleCentralizer.isometry_coe.continuous.comp
    (α.continuous_multiplier_apply_fst m a)

/-- Strict continuity of the induced action: left products with elements of `A` vary norm
continuously. -/
theorem continuous_coe_mul_multiplier_apply (α : CStarAction G A) (m : 𝓜(ℂ, A)) (a : A) :
    Continuous fun g => (a : 𝓜(ℂ, A)) * α.multiplier g m := by
  simp only [DoubleCentralizer.coe_mul_eq_coe_snd]
  exact DoubleCentralizer.isometry_coe.continuous.comp
    (α.continuous_multiplier_apply_snd m a)

/-- An operator implements an action automorphism on the multiplier extension of a nondegenerate
representation exactly when it implements it on the coefficient algebra. -/
theorem mul_multiplierExtension_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (α : CStarAction G A)
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate) (g : G) (T : H →L[ℂ] H) :
    (∀ m : 𝓜(ℂ, A), T * π.multiplierExtension hπ m =
      π.multiplierExtension hπ (α.multiplier g m) * T) ↔
      ∀ a : A, T * π a = π (α g a) * T := by
  constructor
  · intro h a
    simpa using h (a : 𝓜(ℂ, A))
  · intro h m
    apply hπ.ext
    intro a
    simp only [mul_assoc, NonUnitalStarAlgHom.multiplierExtension_mul_eq_fst, h]
    rw [← mul_assoc, NonUnitalStarAlgHom.multiplierExtension_mul_eq_fst]
    simp

end TauCeti.CStarAction
