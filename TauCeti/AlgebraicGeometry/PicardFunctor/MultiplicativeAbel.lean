/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Monoid
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Additivity of the Abel map

For relative effective Cartier divisors, addition multiplies ideal sheaves. The ideal sheaf
of the sum is the tensor product of the individual ideal sheaves, so the Abel map sends the
sum to the product of their classes in the relative Picard presheaf. This identifies the
group law that the Abel maps from symmetric powers must respect.

The construction follows Kleiman, *The Picard scheme*, Section 9.3, and the Stacks Project,
*Divisors*, Section "Effective Cartier divisors".
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The Abel map sends a sum of relative effective Cartier divisors to the tensor product of
their line-bundle classes in the relative Picard presheaf. -/
theorem abelMap_app_mul (T : (Over S)ᵒᵖ)
    (D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
    (abelMap f).app T (ULift.up (D * E)) =
      (abelMap f).app T (ULift.up D) * (abelMap f).app T (ULift.up E) := by
  have hD := ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp D.2).isEffectiveCartier
  have hE := ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp E.2).isEffectiveCartier
  rw [abelMap_app_apply, abelMap_app_apply, abelMap_app_apply]
  rw [LineBundleClass.mk_toInvertibleSheaf_mul hD hE]
  simp only [QuotientGroup.mk_mul, mul_inv_rev, mul_comm]
  -- The two sides now differ only in proofs that the same ideals are Cartier.
  rfl

/-- At every base change, the Abel map is a monoid homomorphism from effective Cartier divisors
under addition to the relative Picard group under tensor product. -/
def abelMapMonoidHom (T : (Over S)ᵒᵖ) :
    (relativeEffectiveCartierSubfunctor f).toFunctor.obj T →*
      (relativePicardPresheaf f).obj T where
  toFun D := (abelMap f).app T (ULift.up D)
  map_one' := by
    exact abelMap_app_top f T
  map_mul' D E := abelMap_app_mul f T D E

/-- The monoid homomorphism agrees pointwise with the Abel map. -/
lemma abelMapMonoidHom_apply (T : (Over S)ᵒᵖ)
    (D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
    abelMapMonoidHom f T D = (abelMap f).app T (ULift.up D) := by
  unfold abelMapMonoidHom
  rfl

end

end TauCeti.AlgebraicGeometry
