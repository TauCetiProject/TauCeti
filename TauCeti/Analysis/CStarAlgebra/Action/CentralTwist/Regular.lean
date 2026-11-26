/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Covariant
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular
import TauCeti.Analysis.Normed.Operator.Basic
/-!
# Twisted regular covariant pairs

The regular covariant pair induced by a nondegenerate representation `ρ` has the ordinary
regular coefficient representation and the projective translations
`U_s ξ(r) = ρ'(α.multiplier r⁻¹ (ω(s, s⁻¹r))) ξ(s⁻¹r)`.
Here `ρ'` is the multiplier extension. The multiplier field is continuous after evaluation
at each fixed vector. The construction applies to arbitrary locally compact groups with
inner-regular Haar measure.

The construction uses `CovariantRepresentation.regular` and the left regular representation.
Its multiplier extension acts pointwise by `ρ'(α.multiplier r⁻¹ m)`.

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*,
  Math. Proc. Cambridge Philos. Soc. 106 (1989), 293–311, Section 2.
* The untwisted regular construction in `TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular`.
-/

public section

noncomputable section

open MeasureTheory
open scoped MultiplierAlgebra

namespace TauCeti.CStarAction.CentralCovariantPair

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (α : CStarAction G A) (ω : CentralCocycle α)
  (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hρ : ρ.IsNondegenerate)

private def regularTwist (s r : G) : 𝓜(ℂ, A) :=
  α.multiplier r⁻¹ (ω.value s (s⁻¹ * r) : 𝓜(ℂ, A))

private theorem continuous_regularTwist_fst (a : A) :
    Continuous fun p : G × G => (regularTwist α ω p.1 p.2).fst a := by
  simp only [regularTwist, multiplier_apply_fst, inv_inv]
  exact α.continuous_apply continuous_snd.inv
    (ω.continuous_fst_apply continuous_fst (continuous_fst.inv.mul continuous_snd)
      (α.continuous_apply continuous_snd continuous_const))

omit [IsTopologicalGroup G] in
private theorem regularTwist_mem_unitary (s r : G) :
    regularTwist α ω s r ∈ unitary 𝓜(ℂ, A) :=
  Unitary.map_mem (α.multiplier r⁻¹) (ω.value s (s⁻¹ * r)).property

private theorem continuous_regularTwist_apply (v : H) :
    Continuous fun p : G × G => ρ.multiplierExtension hρ (regularTwist α ω p.1 p.2) v :=
  ρ.continuous_multiplierExtension_apply hρ (continuous_regularTwist_fst α ω)
    (fun p => DoubleCentralizer.norm_coe_unitary_le_one ⟨_, regularTwist_mem_unitary α ω p.1 p.2⟩) v

omit [IsTopologicalGroup G] in
private theorem norm_regularTwist_apply_le (s r : G) :
    ‖ρ.multiplierExtension hρ (regularTwist α ω s r)‖ ≤ 1 :=
  (NonUnitalStarAlgHom.norm_apply_le (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom _).trans
    (DoubleCentralizer.norm_coe_unitary_le_one ⟨_, regularTwist_mem_unitary α ω s r⟩)

omit [IsTopologicalGroup G] in
private theorem regularTwist_mul (s t r : G) :
    regularTwist α ω s r * regularTwist α ω t (s⁻¹ * r) =
      α.multiplier r⁻¹ (ω.value s t : 𝓜(ℂ, A)) * regularTwist α ω (s * t) r := by
  have h := congrArg (α.multiplier r⁻¹)
    (ω.multiplier_value_mul_value s t ((s * t)⁻¹ * r))
  simp only [map_mul, mul_inv_rev, mul_assoc,
    mul_inv_cancel_left] at h
  simp only [regularTwist, mul_inv_rev]
  rw [← multiplier_apply_multiplier_apply]
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv] using
    ((ω.commute_multiplier_value r⁻¹ s (s⁻¹ * r) _).eq.trans h)

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]

private def regularTwistOperator (s : G) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  Lp.strongOperatorMultiplication μ ENNReal.ofNat_ne_top
    (fun r => ρ.multiplierExtension hρ (regularTwist α ω s r))
    (fun v => (continuous_regularTwist_apply α ω ρ hρ v).comp
      (continuous_const.prodMk continuous_id))
    ⟨1, norm_regularTwist_apply_le α ω ρ hρ s⟩

omit [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] in
private theorem coeFn_regularTwistOperator (s : G) (ξ : Lp H 2 μ) :
    regularTwistOperator α ω ρ hρ μ s ξ =ᵐ[μ]
      fun r => ρ.multiplierExtension hρ (regularTwist α ω s r) (ξ r) :=
  Lp.strongOperatorMultiplication_ae μ ENNReal.ofNat_ne_top _ _ _ ξ

omit [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] in
private theorem regularTwistOperator_mem_unitary (s : G) :
    regularTwistOperator α ω ρ hρ μ s ∈ unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  Lp.strongOperatorMultiplication_mem_unitary μ _ _ _ fun r =>
    Unitary.map_mem (ρ.multiplierExtension hρ) (regularTwist_mem_unitary α ω s r)

/-- The projective unitary translation in the twisted regular pair. -/
private def regularUnitary (s : G) : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  ⟨regularTwistOperator α ω ρ hρ μ s * μ.leftRegular ℂ H 2 s,
    mul_mem (regularTwistOperator_mem_unitary α ω ρ hρ μ s)
      (μ.isUnitary_leftRegular.mem_unitary s)⟩

omit [IsLocallyFiniteMeasure μ] in
/-- The characteristic almost-everywhere formula for the twisted regular translation. -/
private theorem coeFn_regularUnitary (s : G) (ξ : Lp H 2 μ) :
    (regularUnitary α ω ρ hρ μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ =ᵐ[μ]
      fun r => ρ.multiplierExtension hρ
        (α.multiplier r⁻¹ (ω.value s (s⁻¹ * r) : 𝓜(ℂ, A))) (ξ (s⁻¹ * r)) := by
  filter_upwards [coeFn_regularTwistOperator α ω ρ hρ μ s (μ.leftRegular ℂ H 2 s ξ),
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 s ξ] with r h₁ h₂
  exact h₁.trans (congrArg _ h₂)

omit [IsLocallyFiniteMeasure μ] in
private theorem regularUnitary_one : regularUnitary α ω ρ hρ μ 1 = 1 := by
  apply Subtype.ext
  ext ξ
  filter_upwards [coeFn_regularUnitary α ω ρ hρ μ 1 ξ] with r hr
  simpa using hr

private theorem regularUnitary_mul (s t : G) :
    (regularUnitary α ω ρ hρ μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
        (regularUnitary α ω ρ hρ μ t : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (CovariantRepresentation.regular α ρ μ).coefficient.multiplierExtension
          (CovariantRepresentation.isNondegenerate_regular_coefficient hρ)
          (ω.value s t : 𝓜(ℂ, A)) *
        (regularUnitary α ω ρ hρ μ (s * t) : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  ext ξ
  simp only [mul_apply_eq_comp]
  have hcomp := (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving.ae_eq_comp
    (coeFn_regularUnitary α ω ρ hρ μ t ξ)
  filter_upwards [coeFn_regularUnitary α ω ρ hρ μ s
      ((regularUnitary α ω ρ hρ μ t : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ), hcomp,
    CovariantRepresentation.coeFn_regular_multiplierExtension α ρ μ hρ (ω.value s t : 𝓜(ℂ, A))
      ((regularUnitary α ω ρ hρ μ (s * t) : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ),
    coeFn_regularUnitary α ω ρ hρ μ (s * t) ξ] with r h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃, h₄]
  simpa only [regularTwist, ← mul_apply_eq_comp, ← map_mul, mul_inv_rev, mul_assoc]
    using congrArg (fun m => ρ.multiplierExtension hρ m (ξ (t⁻¹ * (s⁻¹ * r))))
      (regularTwist_mul α ω s t r)

private theorem regularUnitary_mul_coefficient (s : G) (a : A) :
    (regularUnitary α ω ρ hρ μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
        (CovariantRepresentation.regular α ρ μ).coefficient a =
      (CovariantRepresentation.regular α ρ μ).coefficient (α s a) *
        (regularUnitary α ω ρ hρ μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  ext ξ
  simp only [mul_apply_eq_comp]
  have hcomp := (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving.ae_eq_comp
    (CovariantRepresentation.coeFn_regular_coefficient α ρ μ a ξ)
  filter_upwards [coeFn_regularUnitary α ω ρ hρ μ s
      ((CovariantRepresentation.regular α ρ μ).coefficient a ξ), hcomp,
    CovariantRepresentation.coeFn_regular_coefficient α ρ μ (α s a)
      ((regularUnitary α ω ρ hρ μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ),
    coeFn_regularUnitary α ω ρ hρ μ s ξ] with r h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃, h₄]
  have hc := ω.commute_multiplier_value r⁻¹ s (s⁻¹ * r)
    (α r⁻¹ (α s a) : 𝓜(ℂ, A))
  have he := congrArg (ρ.multiplierExtension hρ) hc.eq
  simp only [map_mul, ρ.multiplierExtension_coe] at he
  simpa only [regularTwist, mul_inv_rev, inv_inv, mul_apply,
    mul_apply_eq_comp] using congrArg (fun T : H →L[ℂ] H => T (ξ (s⁻¹ * r))) he

variable [WeaklyLocallyCompactSpace G]

private theorem continuous_regularUnitary_apply (ξ : Lp H 2 μ) :
    Continuous fun s => (regularUnitary α ω ρ hρ μ s : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ := by
  apply AddMonoidHomClass.continuous_apply_of_bound
    (T := fun s => regularTwistOperator α ω ρ hρ μ s)
    (C := 1)
  · intro η
    exact Lp.continuous_strongOperatorMultiplication_apply μ ENNReal.ofNat_ne_top
      (fun s r => ρ.multiplierExtension hρ (regularTwist α ω s r))
      (continuous_regularTwist_apply α ω ρ hρ)
      (norm_regularTwist_apply_le α ω ρ hρ) η
  · intro s η
    simpa using (Unitary.norm_map
      (⟨_, regularTwistOperator_mem_unitary α ω ρ hρ μ s⟩ :
        unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ)) η).le
  · exact μ.continuous_leftRegular_apply 2 ENNReal.ofNat_ne_top ξ

/-- The twisted regular covariant pair on `L²(G,H)` induced by a nondegenerate coefficient
representation. The coefficient is the ordinary regular coefficient representation. -/
def regular : CentralCovariantPair (Lp H 2 μ) α ω where
  pi := (CovariantRepresentation.regular α ρ μ).coefficient
  nondegenerate := CovariantRepresentation.isNondegenerate_regular_coefficient hρ
  unitaryMap := regularUnitary α ω ρ hρ μ
  at_one := regularUnitary_one α ω ρ hρ μ
  strong_continuous := continuous_regularUnitary_apply α ω ρ hρ μ
  covariance s a := by
    rw [regularUnitary_mul_coefficient α ω ρ hρ μ, mul_assoc,
      Unitary.mul_star_self_of_mem (regularUnitary α ω ρ hρ μ s).property, mul_one]
  projective := regularUnitary_mul α ω ρ hρ μ

/-- The coefficient representation of the twisted regular pair is the untwisted one. -/
@[simp]
theorem regular_pi : (regular α ω ρ hρ μ).pi =
    (CovariantRepresentation.regular α ρ μ).coefficient :=
  (rfl)

/-- Almost-everywhere projective translation formula for the twisted regular pair. -/
theorem coeFn_regular_unitaryMap (s : G) (ξ : Lp H 2 μ) :
    ((regular α ω ρ hρ μ).unitaryMap s : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ =ᵐ[μ]
      fun r => ρ.multiplierExtension hρ
        (α.multiplier r⁻¹ (ω.value s (s⁻¹ * r) : 𝓜(ℂ, A))) (ξ (s⁻¹ * r)) :=
  coeFn_regularUnitary α ω ρ hρ μ s ξ

/-- At the trivial cocycle, the twisted regular pair recovers the ordinary regular
covariant representation. -/
@[simp]
theorem toCovariantRepresentation_regular_one :
    (regular α 1 ρ hρ μ).toCovariantRepresentation =
      CovariantRepresentation.regular α ρ μ := by
  refine CovariantRepresentation.ext (by simp) ?_
  apply DFunLike.coe_injective
  funext s
  simp only [toCovariantRepresentation_group_apply, CovariantRepresentation.regular_group]
  ext ξ
  filter_upwards [coeFn_regular_unitaryMap α 1 ρ hρ μ s ξ,
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 s ξ] with r h₁ h₂
  simpa using h₁.trans (by simpa using h₂.symm)

end TauCeti.CStarAction.CentralCovariantPair
