/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import TauCeti.Analysis.CStarAlgebra.Multiplier

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
actions.

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
def multiplier (α : CStarAction G A) : G →* (𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)) where
  toFun g := DoubleCentralizer.congr (α g)
  map_one' := by
    ext m : 1
    exact DoubleCentralizer.ext _ _ _ _ <| Prod.ext
      (ContinuousLinearMap.ext fun _ => by simp) (ContinuousLinearMap.ext fun _ => by simp)
  map_mul' g h := by
    ext m : 1
    exact DoubleCentralizer.ext _ _ _ _ <| Prod.ext
      (ContinuousLinearMap.ext fun _ => by simp [mul_apply])
      (ContinuousLinearMap.ext fun _ => by simp [mul_apply])

theorem multiplier_apply (α : CStarAction G A) (g : G) :
    α.multiplier g = DoubleCentralizer.congr (α g) :=
  (rfl)

@[simp]
theorem multiplier_apply_fst (α : CStarAction G A) (g : G) (m : 𝓜(ℂ, A)) (a : A) :
    (α.multiplier g m).fst a = α g (m.fst (α g⁻¹ a)) := by
  simp [multiplier_apply]

@[simp]
theorem multiplier_apply_snd (α : CStarAction G A) (g : G) (m : 𝓜(ℂ, A)) (a : A) :
    (α.multiplier g m).snd a = α g (m.snd (α g⁻¹ a)) := by
  simp [multiplier_apply]

/-- The induced action restricts to the original action on `A`. -/
@[simp]
theorem multiplier_coe (α : CStarAction G A) (g : G) (a : A) :
    α.multiplier g (a : 𝓜(ℂ, A)) = (α g a : 𝓜(ℂ, A)) :=
  DoubleCentralizer.congr_coe (α g) a

/-- The induced action is the unique action on `𝓜(ℂ, A)` by multiplicative maps that restricts
to `α` on `A`. -/
theorem eq_multiplier_of_apply_coe (α : CStarAction G A)
    (β : G →* (𝓜(ℂ, A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A))) (hβ : ∀ g (a : A), β g a = (α g a : 𝓜(ℂ, A))) :
    β = α.multiplier :=
  MonoidHom.ext fun g => StarAlgEquiv.ext <| congrFun <|
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

end TauCeti.CStarAction
