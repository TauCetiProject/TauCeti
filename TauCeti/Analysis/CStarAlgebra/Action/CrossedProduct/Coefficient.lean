/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Fourier

/-!
# Coefficients inside discrete regular crossed products

For a discrete group the canonical coefficient operators belong to the concrete regular
crossed product itself, not just its multiplier algebra. We construct this inclusion and
prove that Fourier coefficients intertwine left and right multiplication by coefficients.
In particular, the identity Fourier coefficient is a contractive bimodule retraction onto
the coefficient algebra. Together with the positivity and faithfulness results in
`CrossedProduct.Expectation`, this gives the canonical conditional expectation, also for
nonunital coefficients and possibly degenerate faithful inducing representations.

The construction retains the inducing representation as a parameter; independence of the
regular norm is not asserted.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 7, for the coefficient inclusion
and the canonical conditional expectation of a discrete reduced crossed product.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported CStarAlgebra

namespace TauCeti.CStarAction.RegularCrossedProduct

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

open scoped Classical in
/-- The compactly supported coefficient concentrated at the group identity. -/
private def identitySupported (a : A) : C_c(G, A) where
  toFun := fun g => if g = 1 then a else 0
  continuous_toFun := continuous_of_discreteTopology
  hasCompactSupport' := HasCompactSupport.intro
    (isCompact_singleton (x := (1 : G))) fun g hg => by
    simp only [Set.mem_singleton_iff] at hg
    simp [hg]

open scoped Classical in
omit [MeasurableSpace G] [BorelSpace G] in
private theorem identitySupported_apply (a : A) (g : G) :
    identitySupported (G := G) a g = if g = 1 then a else 0 := rfl

private theorem integratedOperator_identitySupported (a : A) :
    (CovariantRepresentation.regular α ρ Measure.count).integratedOperator Measure.count
      (identitySupported a) =
      (CovariantRepresentation.regular α ρ Measure.count).coefficient a := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  rw [CovariantRepresentation.integratedOperator_apply]
  have h (g : G) :
      (CovariantRepresentation.regular α ρ Measure.count).coefficient
        (identitySupported a g) ((CovariantRepresentation.regular α ρ Measure.count).group g v) =
      ({1} : Set G).indicator
        (fun _ => (CovariantRepresentation.regular α ρ Measure.count).coefficient a v) g := by
    by_cases hg : g = 1 <;> simp [identitySupported_apply, hg]
  simp_rw [h]
  rw [integral_indicator (measurableSet_singleton _), integral_singleton]
  simp only [count_real_singleton]
  exact one_smul ℝ _

/-- The coefficient inclusion into the discrete concrete regular crossed product. -/
def coefficient : A →⋆ₙₐ[ℂ] regularAlgebra α ρ Measure.count :=
  (CovariantRepresentation.regular α ρ Measure.count).coefficient.codRestrict _ fun a => by
    rw [← integratedOperator_identitySupported α ρ a]
    simpa only [coe_of, CovariantRepresentation.integratedStarAlgHom_apply,
      ConvolutionAlgebra.ofConv_toConv] using
      (of α ρ Measure.count (ConvolutionAlgebra.toConv (identitySupported a))).property

/-- The inclusion acts by the coefficient representation of the regular covariant pair. -/
@[simp]
theorem coe_coefficient (a : A) :
    (coefficient α ρ a : Lp H 2 Measure.count →L[ℂ] Lp H 2 Measure.count) =
      (CovariantRepresentation.regular α ρ Measure.count).coefficient a := (rfl)

private theorem coefficient_eq_of (a : A) :
    coefficient α ρ a = of α ρ Measure.count (ConvolutionAlgebra.toConv (identitySupported a)) := by
  apply Subtype.ext
  simpa only [coe_coefficient, coe_of, CovariantRepresentation.integratedStarAlgHom_apply,
    ConvolutionAlgebra.ofConv_toConv] using (integratedOperator_identitySupported α ρ a).symm

open scoped Classical in
/-- Fourier coefficients of an included coefficient vanish off the identity. -/
@[simp]
theorem fourierCoeff_coefficient (hρ : Function.Injective ρ) (g : G) (a : A) :
    fourierCoeff α ρ hρ g (coefficient α ρ a) = if g = 1 then a else 0 := by
  rw [coefficient_eq_of, fourierCoeff_of]
  exact identitySupported_apply a g

/-- Faithfulness of the inducing representation makes the coefficient inclusion isometric. -/
theorem isometry_coefficient (hρ : Function.Injective ρ) : Isometry (coefficient α ρ) := by
  have h : Function.LeftInverse (fourierCoeff α ρ hρ 1) (coefficient α ρ) := fun a => by simp
  exact NonUnitalStarAlgHom.isometry (coefficient α ρ) h.injective

/-- Left multiplication by an included coefficient `a` on the image of a compactly supported
function `f` is the image of the pointwise product `a • f.ofConv`. -/
theorem coefficient_mul_of (a : A) (f : ConvolutionAlgebra α Measure.count) :
    coefficient α ρ a * of α ρ Measure.count f =
      of α ρ Measure.count (ConvolutionAlgebra.toConv (a • f.ofConv)) := by
  apply Subtype.ext
  simpa only [MulMemClass.coe_mul, coe_coefficient, coe_of,
    CovariantRepresentation.integratedStarAlgHom_apply, ConvolutionAlgebra.ofConv_toConv] using
    ((CovariantRepresentation.regular α ρ Measure.count).integratedOperator_smul
      Measure.count a f.ofConv).symm

/-- Fourier coefficients are left linear over the included coefficient algebra. -/
@[simp]
theorem fourierCoeff_coefficient_mul (hρ : Function.Injective ρ) (g : G) (a : A)
    (x : regularAlgebra α ρ Measure.count) :
    fourierCoeff α ρ hρ g (coefficient α ρ a * x) = a * fourierCoeff α ρ hρ g x := by
  induction x using induction_on α ρ Measure.count with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f => simp [coefficient_mul_of]

/-- Right multiplication by a coefficient twists its Fourier coefficient by the group action. -/
@[simp]
theorem fourierCoeff_mul_coefficient (hρ : Function.Injective ρ) (g : G) (a : A)
    (x : regularAlgebra α ρ Measure.count) :
    fourierCoeff α ρ hρ g (x * coefficient α ρ a) =
      fourierCoeff α ρ hρ g x * α g a := by
  have h := fourierCoeff_star α ρ hρ g (star x)
  rw [star_star] at h
  rw [← star_star (x * coefficient α ρ a), star_mul, ← map_star,
    fourierCoeff_star, fourierCoeff_coefficient_mul]
  simp only [star_mul, star_star, map_mul]
  rw [← h]

/-- The coefficient algebra consists exactly of the elements whose nonidentity Fourier
coefficients vanish. -/
theorem mem_range_coefficient_iff (hρ : Function.Injective ρ)
    (x : regularAlgebra α ρ Measure.count) :
    x ∈ Set.range (coefficient α ρ) ↔ ∀ g ≠ 1, fourierCoeff α ρ hρ g x = 0 := by
  constructor
  · rintro ⟨a, rfl⟩ g hg
    simp [hg]
  · intro hx
    refine ⟨fourierCoeff α ρ hρ 1 x, ?_⟩
    apply fourierCoeff_ext α ρ hρ
    intro g
    by_cases hg : g = 1
    · simp [hg]
    · simp [hg, hx g hg]

/-- Including the identity Fourier coefficient back into the crossed product fixes precisely
the coefficient algebra. Thus it is a projection onto that algebra. -/
theorem coefficient_fourierCoeff_one_eq_self_iff (hρ : Function.Injective ρ)
    (x : regularAlgebra α ρ Measure.count) :
    coefficient α ρ (fourierCoeff α ρ hρ 1 x) = x ↔ x ∈ Set.range (coefficient α ρ) := by
  constructor
  · intro hx
    exact ⟨fourierCoeff α ρ hρ 1 x, hx⟩
  · rintro ⟨a, rfl⟩
    simp

end TauCeti.CStarAction.RegularCrossedProduct
