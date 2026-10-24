/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Basic
public import TauCeti.MeasureTheory.Function.Lp.OperatorMultiplication
public import TauCeti.RepresentationTheory.Continuous.LeftRegular

/-!
# Regular covariant representations

Let `α` be a point-norm continuous action of a topological group `G` on a possibly nonunital
C⋆-algebra `A`, let `ρ` be a representation of `A` on a Hilbert space `H`, and let `μ` be a
left-invariant measure on `G`, typically a left Haar measure. The *regular covariant
representation* induced by `ρ` acts on `L²(G, H)` by

`ρ̃(a) ξ (r) = ρ (α_{r⁻¹}(a)) (ξ r)` and `λ_s ξ (r) = ξ (s⁻¹ r)`.

The coefficient representation `ρ̃` is multiplication by the bounded continuous operator-valued
function `r ↦ ρ (α_{r⁻¹}(a))`, so it is a ⋆-homomorphism; the group representation `λ` is the left
regular representation, which is unitary and strongly continuous. The pair is covariant:
`λ_s ρ̃(a) λ_s⁻¹ = ρ̃(α_s(a))`. Integrating it gives the regular representations of the convolution
algebra, whose norms define the reduced crossed product.

The representation `ρ` need not be nondegenerate or faithful, and no separability, second
countability, or σ-finiteness is assumed: the measure need only be left invariant, locally finite,
and inner regular with respect to compact sets on sets of finite measure, as the Haar measure
`MeasureTheory.Measure.haar` of a locally compact group is.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.

## Main definitions

* `TauCeti.CStarAction.CovariantRepresentation.regular`: the regular covariant representation
  `(ρ̃, λ)` on `L²(G, H)` induced by `ρ`.

## Main statements

* `TauCeti.CStarAction.CovariantRepresentation.coeFn_regular_coefficient`: the coefficient
  representation is `ρ̃(a) ξ (r) = ρ (α_{r⁻¹}(a)) (ξ r)` almost everywhere.
* `TauCeti.CStarAction.CovariantRepresentation.regular_group`: the group representation is the
  left regular representation `MeasureTheory.Measure.leftRegular`.
-/

public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction CStarAlgebra

namespace TauCeti.CStarAction

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded continuous operator-valued function `r ↦ ρ (α_{r⁻¹}(a))` by which `a` acts in the
regular covariant representation, as a ⋆-homomorphism in `a`. -/
private def regularSymbol (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₙₐ[ℂ] (G →ᵇ (H →L[ℂ] H)) where
  toFun a := .ofNormedAddCommGroup (fun r => ρ (α r⁻¹ a))
    ((map_continuous ρ).comp (α.continuous_inv_apply a)) ‖a‖
    fun r => (NonUnitalStarAlgHom.norm_apply_le ρ _).trans (StarAlgEquiv.norm_map _ _).le
  map_smul' c a := by ext1 r; simp
  map_zero' := by ext1 r; simp
  map_add' a b := by ext1 r; simp
  map_mul' a b := by ext1 r; simp
  map_star' a := by ext1 r; simp [map_star]

private theorem regularSymbol_apply (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (r : G) : regularSymbol α ρ a r = ρ (α r⁻¹ a) :=
  (rfl)

namespace CovariantRepresentation

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]

omit [IsLocallyFiniteMeasure μ] in
/-- Left translation intertwines multiplication by `r ↦ ρ (α_{r⁻¹}(a))` with multiplication by
`r ↦ ρ (α_{r⁻¹}(α_g(a)))`; this is the covariance of the regular covariant representation. -/
private theorem leftRegular_mulL2_regularSymbol (g : G) (a : A) (ξ : Lp H 2 μ) :
    μ.leftRegular ℂ H 2 g ((regularSymbol α ρ a).mulL2 μ ξ) =
      (regularSymbol α ρ (α g a)).mulL2 μ (μ.leftRegular ℂ H 2 g ξ) := by
  refine (BoundedContinuousFunction.mulL2_eq_iff.2 ?_).symm
  -- Both sides are `r ↦ ρ (α_{r⁻¹ g}(a)) (ξ (g⁻¹ r))` almost everywhere.
  have hcomp := (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
    ((regularSymbol α ρ a).coeFn_mulL2 (μ := μ) ξ)
  filter_upwards [μ.coeFn_leftRegular (𝕜 := ℂ) 2 g ξ, hcomp,
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 g ((regularSymbol α ρ a).mulL2 μ ξ)] with r hξ hcomp hL
  rw [Function.comp_apply, Function.comp_apply] at hcomp
  rw [hξ, hL, hcomp, regularSymbol_apply, regularSymbol_apply, mul_inv_rev, inv_inv, mul_apply]

/-- The regular covariant representation on `L²(G, H)` induced by a representation `ρ` of `A` on
`H`: `a` acts by `ξ ↦ (r ↦ ρ (α_{r⁻¹}(a)) (ξ r))` and `s` by left translation
`ξ ↦ (r ↦ ξ (s⁻¹ r))`. -/
def regular : CovariantRepresentation α (Lp H 2 μ) where
  coefficient :=
    (BoundedContinuousFunction.mulL2StarAlgHom μ).toNonUnitalStarAlgHom.comp (regularSymbol α ρ)
  group := μ.leftRegular ℂ H 2
  isUnitary := μ.isUnitary_leftRegular
  continuous_orbit := μ.continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top
  covariance g a ξ := by
    simp only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      BoundedContinuousFunction.mulL2StarAlgHom_apply]
    exact leftRegular_mulL2_regularSymbol α ρ μ g a ξ

private theorem regular_coefficient_apply (a : A) :
    (regular α ρ μ).coefficient a = (regularSymbol α ρ a).mulL2 μ := by
  simp only [regular, NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
    BoundedContinuousFunction.mulL2StarAlgHom_apply]

/-- The group representation of the regular covariant representation is the left regular
representation. -/
@[simp]
theorem regular_group : (regular α ρ μ).group = μ.leftRegular ℂ H 2 :=
  (rfl)

/-- The coefficient representation of the regular covariant representation acts by
`ρ̃(a) ξ (r) = ρ (α_{r⁻¹}(a)) (ξ r)` almost everywhere. -/
theorem coeFn_regular_coefficient (a : A) (ξ : Lp H 2 μ) :
    (regular α ρ μ).coefficient a ξ =ᵐ[μ] fun r => ρ (α r⁻¹ a) (ξ r) := by
  rw [regular_coefficient_apply]
  exact (regularSymbol α ρ a).coeFn_mulL2 ξ

/-- The coefficient representation of the regular covariant representation is determined by its
pointwise formula: an `L²` class equal almost everywhere to `r ↦ ρ (α_{r⁻¹}(a)) (ξ r)` is
`ρ̃(a) ξ`. -/
theorem regular_coefficient_eq_iff {a : A} {ξ η : Lp H 2 μ} :
    (regular α ρ μ).coefficient a ξ = η ↔ (fun r => ρ (α r⁻¹ a) (ξ r)) =ᵐ[μ] η := by
  rw [regular_coefficient_apply]
  exact BoundedContinuousFunction.mulL2_eq_iff

end CovariantRepresentation

end TauCeti.CStarAction
