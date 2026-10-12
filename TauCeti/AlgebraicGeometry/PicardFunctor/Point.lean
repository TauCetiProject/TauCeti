/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Rigidified

/-!
# The distinguished point of the rigidified Picard functor

The trivial line bundle has a canonical trivialization along every section. Its rigidified
isomorphism class is preserved by base change, giving the rigidified Picard functor a natural
distinguished point. This is the identity used by the tensor-product group law on rigidified
classes.

## Reference

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)

/-- The class of the canonically rigidified trivial line bundle over a base change of `X`. -/
def rigidifiedPicardPoint (T : (Over S)ᵒᵖ) :
    (rigidifiedPicardFunctor f x₀ hx₀).obj T :=
  RigidifiedLineBundleClass.mk
    (RigidifiedLineBundle.trivial (baseChangeSection f x₀ hx₀ T.unop))

/-- The distinguished point is represented by the canonically rigidified structure sheaf. -/
@[simp]
lemma rigidifiedPicardPoint_eq (T : (Over S)ᵒᵖ) :
    rigidifiedPicardPoint f x₀ hx₀ T =
      RigidifiedLineBundleClass.mk
        (RigidifiedLineBundle.trivial (baseChangeSection f x₀ hx₀ T.unop)) := (rfl)

/-- Forgetting the distinguished rigidification gives the identity line-bundle class. -/
lemma toLineBundleClass_rigidifiedPicardPoint (T : (Over S)ᵒᵖ) :
    RigidifiedLineBundleClass.toLineBundleClass (rigidifiedPicardPoint f x₀ hx₀ T) = 1 := by
  rw [rigidifiedPicardPoint_eq]
  exact RigidifiedLineBundleClass.toLineBundleClass_trivial

/-- Pullback along a morphism over `S` preserves the distinguished rigidified class. -/
lemma rigidifiedPicardPoint_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (rigidifiedPicardFunctor f x₀ hx₀).map φ (rigidifiedPicardPoint f x₀ hx₀ T) =
      rigidifiedPicardPoint f x₀ hx₀ T' := by
  rw [rigidifiedPicardPoint_eq, rigidifiedPicardPoint_eq,
    rigidifiedPicardFunctor_map]
  exact RigidifiedLineBundleClass.pullback_trivial _

end

end AlgebraicGeometry

end TauCeti
