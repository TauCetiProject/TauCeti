/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The right regular representation on vector-valued `Lᵖ`

Let `μ` be a right-invariant measure on a group `G`, and `E` a normed space. Parallel to
`MeasureTheory.Measure.leftRegular`, the group `G` acts on `Lᵖ(G, E)` by right translation,
`(ρ g f) x = f (x * g)`. Because `(f (· * g)) (x * h) = f (x * (g * h))`, no inverse is needed in
the group argument for `g ↦ ρ g` to be a homomorphism. Each right translation is an isometry, so
the action is unitary on `L²(G, E)` for an inner product space `E`. When `μ` is bi-invariant, every
left translation `μ.leftRegular 𝕜 E p g` commutes with every right translation
`μ.rightRegular 𝕜 E p h` by associativity of multiplication in `G`.

On the counting measure of a group with measurable singletons, `leftRegular` sends the singleton
indicator at `h` to that at `g * h`, while `rightRegular` sends it to that at `h * g⁻¹`.

## Main definitions

* `MeasureTheory.Measure.rightRegular`: the right regular representation of `G` on `Lp E p μ`.

## Main statements

* `MeasureTheory.Measure.rightRegular_apply` and `MeasureTheory.Measure.coeFn_rightRegular`:
  `ρ g` is `Lp.compMeasurePreserving (· * g)`, represented by `x ↦ f (x * g)`.
* `MeasureTheory.Measure.isUnitary_rightRegular`: the action on `L²(G, E)` is unitary.
* `MeasureTheory.Measure.commute_leftRegular_rightRegular`: left and right regular operators
  commute for any bi-invariant measure.
* `MeasureTheory.Measure.leftRegular_count_indicatorConstLp_singleton` and
  `MeasureTheory.Measure.rightRegular_count_indicatorConstLp_singleton`: actions on point masses.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {G 𝕜 E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [NormedRing 𝕜]
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  (μ : Measure G) [μ.IsMulRightInvariant] (p : ℝ≥0∞) [Fact (1 ≤ p)]

variable (𝕜 E) in
/-- **The right regular representation** of `G` on `Lᵖ(G, E)` for a right-invariant measure `μ`:
the element `g` acts by `f ↦ (x ↦ f (x * g))`. -/
noncomputable def rightRegular : ContRepresentation 𝕜 G (Lp E p μ) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (· * g)
        (measurePreserving_mul_right μ g)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun f => by
        simp only [one_apply_eq_self, LinearIsometry.coe_toContinuousLinearMap,
          Lp.compMeasurePreservingₗᵢ_apply, mul_one, ← Function.id_def]
        exact Lp.compMeasurePreserving_id_apply f
      map_mul' g h := ContinuousLinearMap.ext fun f => by
        have hfun : (fun x : G => x * (g * h)) =
            (fun x : G => x * h) ∘ (fun x : G => x * g) := by
          funext x
          simp only [Function.comp_apply, mul_assoc]
        simp only [mul_apply_eq_comp, LinearIsometry.coe_toContinuousLinearMap,
          Lp.compMeasurePreservingₗᵢ_apply, hfun]
        exact Lp.compMeasurePreserving_comp_apply f
          (measurePreserving_mul_right μ h) (measurePreserving_mul_right μ g) }

/-- Right translation on `Lᵖ(G, E)`, unfolded to `Lp.compMeasurePreserving`. -/
theorem rightRegular_apply (g : G) (f : Lp E p μ) :
    μ.rightRegular 𝕜 E p g f =
      Lp.compMeasurePreserving (· * g) (measurePreserving_mul_right μ g) f :=
  (rfl)

/-- Right translation on `Lᵖ(G, E)` is represented by right translation of functions. -/
theorem coeFn_rightRegular (g : G) (f : Lp E p μ) :
    μ.rightRegular 𝕜 E p g f =ᵐ[μ] fun x => f (x * g) := by
  rw [rightRegular_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- Right translation preserves the `Lᵖ` norm. -/
@[simp]
theorem norm_rightRegular_apply (g : G) (f : Lp E p μ) : ‖μ.rightRegular 𝕜 E p g f‖ = ‖f‖ := by
  rw [rightRegular_apply]
  exact Lp.norm_compMeasurePreserving f _

/-- **The right regular representation on `L²(G, E)` is unitary.** -/
theorem isUnitary_rightRegular {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : (μ.rightRegular 𝕜 E 2).IsUnitary := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  exact norm_rightRegular_apply μ 2

/-- For a bi-invariant measure, every left regular operator commutes with every right regular
operator. -/
theorem commute_leftRegular_rightRegular [μ.IsMulLeftInvariant] (g h : G) :
    Commute (μ.leftRegular 𝕜 E p g) (μ.rightRegular 𝕜 E p h) := by
  have hfun : ((· * h) ∘ (g⁻¹ * ·) : G → G) = (g⁻¹ * ·) ∘ (· * h) :=
    funext fun x => mul_assoc g⁻¹ x h
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [mul_apply_eq_comp, leftRegular_apply, rightRegular_apply]
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  simp only [hfun]

section Count

variable [MeasurableSingletonClass G]

/-- Left translation by `g` on counting-measure `Lᵖ` sends the point mass at `h` to that at
`g * h`. -/
@[simp]
theorem leftRegular_count_indicatorConstLp_singleton (g h : G) (c : E) :
    (count : Measure G).leftRegular 𝕜 E p g
      (indicatorConstLp p (measurableSet_singleton h) (by simp) c) =
      indicatorConstLp p (measurableSet_singleton (g * h)) (by simp) c := by
  refine Lp.ext (ae_count_iff.2 fun x => ?_)
  have h1 := ae_count_iff.1 (coeFn_leftRegular (𝕜 := 𝕜) count p g
    (indicatorConstLp p (measurableSet_singleton h) (by simp) c)) x
  have h2 := ae_count_iff.1 (indicatorConstLp_coeFn (p := p) (μ := (count : Measure G))
    (hs := measurableSet_singleton h) (hμs := by simp) (c := c)) (g⁻¹ * x)
  have h3 := ae_count_iff.1 (indicatorConstLp_coeFn (p := p) (μ := (count : Measure G))
    (hs := measurableSet_singleton (g * h)) (hμs := by simp) (c := c)) x
  refine (h1.trans h2).trans (Eq.trans ?_ h3.symm)
  by_cases hx : x = g * h
  · simp [hx]
  · have hx' : g⁻¹ * x ≠ h := fun e => hx (eq_mul_of_inv_mul_eq e)
    simp [hx, hx']

/-- Right translation by `g` on counting-measure `Lᵖ` sends the point mass at `h` to that at
`h * g⁻¹`. -/
@[simp]
theorem rightRegular_count_indicatorConstLp_singleton (g h : G) (c : E) :
    (count : Measure G).rightRegular 𝕜 E p g
      (indicatorConstLp p (measurableSet_singleton h) (by simp) c) =
      indicatorConstLp p (measurableSet_singleton (h * g⁻¹)) (by simp) c := by
  refine Lp.ext (ae_count_iff.2 fun x => ?_)
  have h1 := ae_count_iff.1 (coeFn_rightRegular (𝕜 := 𝕜) count p g
    (indicatorConstLp p (measurableSet_singleton h) (by simp) c)) x
  have h2 := ae_count_iff.1 (indicatorConstLp_coeFn (p := p) (μ := (count : Measure G))
    (hs := measurableSet_singleton h) (hμs := by simp) (c := c)) (x * g)
  have h3 := ae_count_iff.1 (indicatorConstLp_coeFn (p := p) (μ := (count : Measure G))
    (hs := measurableSet_singleton (h * g⁻¹)) (hμs := by simp) (c := c)) x
  refine (h1.trans h2).trans (Eq.trans ?_ h3.symm)
  by_cases hx : x = h * g⁻¹
  · simp [hx]
  · have hx' : x * g ≠ h := fun e => hx (eq_mul_inv_of_mul_eq e)
    simp [hx, hx']

end Count

end MeasureTheory.Measure
