/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# The left regular representation on vector-valued `Lᵖ`

Let `μ` be a left-invariant measure on a group `G`, and `E` a normed space. The group `G` acts on
`Lᵖ(G, E)` by left translation, `(λ g f) x = f (g⁻¹ * x)`; the inverse makes this a
representation rather than an antirepresentation. Each translation is an isometry, so the action
is unitary on `L²(G, E)` for an inner product space `E`. For a topological group, `1 ≤ p < ∞`, and
a locally finite measure that is inner regular with respect to compact sets on sets of finite
measure, for instance the Haar measure `MeasureTheory.Measure.haar` of a locally compact group,
the action is *strongly* continuous: each orbit `g ↦ λ g f` is continuous. Operator-norm
continuity is neither claimed nor true in general.

No σ-finiteness, second countability, or compactness of `G` is assumed. The left regular
representation on `L²(G, H)` is the group part of the regular covariant representation of a
C⋆-dynamical system. For a compact group with normalized Haar measure and scalar coefficients,
`TauCeti.leftRegularLp` is the same action.

## Main definitions

* `MeasureTheory.Measure.leftRegular`: the left regular representation of `G` on `Lp E p μ`.

## Main statements

* `MeasureTheory.Measure.leftRegular_apply` and `MeasureTheory.Measure.coeFn_leftRegular`:
  `λ g` is `Lp.compMeasurePreserving (g⁻¹ * ·)`, represented by `x ↦ f (g⁻¹ * x)`.
* `MeasureTheory.Measure.isUnitary_leftRegular`: the action on `L²(G, E)` is unitary.
* `MeasureTheory.Measure.continuous_leftRegular_apply`: the action is strongly continuous.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {G 𝕜 E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [NormedRing 𝕜]
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  (μ : Measure G) [μ.IsMulLeftInvariant] (p : ℝ≥0∞) [Fact (1 ≤ p)]

variable (𝕜 E) in
/-- **The left regular representation** of `G` on `Lᵖ(G, E)` for a left-invariant measure `μ`:
the element `g` acts by `f ↦ (x ↦ f (g⁻¹ * x))`. -/
noncomputable def leftRegular : ContRepresentation 𝕜 G (Lp E p μ) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (g⁻¹ * ·)
        (measurePreserving_mul_left μ g⁻¹)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun f => by
        simp only [one_apply_eq_self, LinearIsometry.coe_toContinuousLinearMap,
          Lp.compMeasurePreservingₗᵢ_apply, inv_one, one_mul, ← Function.id_def]
        exact Lp.compMeasurePreserving_id_apply f
      map_mul' g h := ContinuousLinearMap.ext fun f => by
        have hfun : (fun x : G => (g * h)⁻¹ * x) =
            (fun x : G => h⁻¹ * x) ∘ (fun x : G => g⁻¹ * x) := by
          funext x
          simp only [Function.comp_apply, mul_inv_rev, mul_assoc]
        simp only [mul_apply_eq_comp, hfun]
        exact Lp.compMeasurePreserving_comp_apply f
          (measurePreserving_mul_left μ h⁻¹) (measurePreserving_mul_left μ g⁻¹) }

/-- Left translation on `Lᵖ(G, E)`, unfolded to the underlying `Lp.compMeasurePreserving`. -/
theorem leftRegular_apply (g : G) (f : Lp E p μ) :
    μ.leftRegular 𝕜 E p g f =
      Lp.compMeasurePreserving (g⁻¹ * ·) (measurePreserving_mul_left μ g⁻¹) f :=
  (rfl)

/-- Left translation on `Lᵖ(G, E)` is represented by left translation of functions. -/
theorem coeFn_leftRegular (g : G) (f : Lp E p μ) :
    μ.leftRegular 𝕜 E p g f =ᵐ[μ] fun x => f (g⁻¹ * x) := by
  rw [leftRegular_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- Left translation preserves the `Lᵖ` norm. -/
@[simp]
theorem norm_leftRegular_apply (g : G) (f : Lp E p μ) : ‖μ.leftRegular 𝕜 E p g f‖ = ‖f‖ := by
  rw [leftRegular_apply]
  exact Lp.norm_compMeasurePreserving f _

/-- **The left regular representation on `L²(G, E)` is unitary**, because left translation
preserves the left-invariant measure. -/
theorem isUnitary_leftRegular {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : (μ.leftRegular 𝕜 E 2).IsUnitary := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  exact norm_leftRegular_apply μ 2

/-- **The left regular representation is strongly continuous** for `p < ∞` and a locally finite
measure that is inner regular with respect to compact sets on sets of finite measure: every orbit
map `g ↦ λ g f` is continuous. -/
theorem continuous_leftRegular_apply [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
    [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g : G => μ.leftRegular 𝕜 E p g f := by
  have hg : Continuous fun g : G => ContinuousMap.mulLeft (X := G) g⁻¹ :=
    (ContinuousMap.curry
      ⟨fun q : G × G => q.1⁻¹ * q.2, continuous_fst.inv.mul continuous_snd⟩).continuous
  simp only [leftRegular_apply]
  exact continuous_const.compMeasurePreservingLp hg _ hp

end MeasureTheory.Measure
