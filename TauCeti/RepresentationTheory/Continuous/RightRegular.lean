/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# The right regular representation on vector-valued `Lᵖ`

Let `μ` be a right-invariant measure on a group `G`, and `E` a normed space. Parallel to
`MeasureTheory.Measure.leftRegular`, the group `G` acts on `Lᵖ(G, E)` by right translation,
`(ρ g f) x = f (x * g)`. Because `(f (· * h)) (x * g) = f (x * (g * h))`, we have
`ρ g (ρ h f) = ρ (g * h) f`, so no inverse is needed in the group argument for `g ↦ ρ g` to be a
homomorphism. Each right translation is an isometry, so the action is unitary on `L²(G, E)` for an
inner product space `E`. For a topological group, `1 ≤ p < ∞`, and a locally finite measure that is
inner regular with respect to compact sets on sets of finite measure, the action is strongly
continuous (`MeasureTheory.Measure.continuous_rightRegular_apply`). When `μ` is bi-invariant, every
left translation `μ.leftRegular 𝕜 E p g` commutes with every right translation
`μ.rightRegular 𝕜 E p h` by associativity of multiplication in `G`.

On singleton indicators of finite measure (and on the point-mass Hilbert basis of counting-measure
`L²`), `rightRegular` sends the indicator at `h` to that at `h * g⁻¹`.

## Main definitions

* `MeasureTheory.Measure.rightRegular`: the right regular representation of `G` on `Lp E p μ`.

## Main statements

* `MeasureTheory.Measure.rightRegular_apply` and `MeasureTheory.Measure.coeFn_rightRegular`:
  `ρ g` is `Lp.compMeasurePreserving (· * g)`, represented by `x ↦ f (x * g)`.
* `MeasureTheory.Measure.rightRegular_toLp`: on a compact group with a finite measure, `ρ g` acts
  on the `Lp` class of a continuous function by right translation.
* `MeasureTheory.Measure.isUnitary_rightRegular` and `MeasureTheory.Measure.star_rightRegular`: the
  action on `L²(G, E)` is unitary and `star (ρ g) = ρ g⁻¹`.
* `MeasureTheory.Measure.continuous_rightRegular_apply`: the action is strongly continuous.
* `MeasureTheory.Measure.commute_leftRegular_rightRegular`: left and right regular operators
  commute for any bi-invariant measure.
* `MeasureTheory.Measure.rightRegular_indicatorConstLp_singleton` and
  `MeasureTheory.Measure.rightRegular_countHilbertBasis`: action on singleton indicators and
  point-mass basis vectors.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

section RightInvariant

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

/-- On a compact group with a finite right-invariant Borel measure, right translation sends the
`Lp` class of a continuous function `F` to the class of `x ↦ F (x * g)`. -/
@[simp]
theorem rightRegular_toLp [TopologicalSpace G] [ContinuousMul G] [CompactSpace G] [BorelSpace G]
    [SecondCountableTopologyEither G E] [IsFiniteMeasure μ] (F : C(G, E)) (g : G) :
    μ.rightRegular 𝕜 E p g (ContinuousMap.toLp p μ 𝕜 F) =
      ContinuousMap.toLp p μ 𝕜 (F.comp (.mulRight g)) := by
  rw [rightRegular_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F (.mulRight g) (measurePreserving_mul_right μ g)

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

/-- On a Hilbert space `E`, the operator `star` of right translation by `g` is right translation by
`g⁻¹`. -/
@[simp]
theorem star_rightRegular {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (g : G) :
    star (μ.rightRegular 𝕜 E 2 g) = μ.rightRegular 𝕜 E 2 g⁻¹ :=
  (isUnitary_rightRegular μ).star_eq_inv g

/-- **The right regular representation is strongly continuous** for `p < ∞` and a locally finite
measure that is inner regular with respect to compact sets on sets of finite measure: every orbit
map `g ↦ ρ g f` is continuous. -/
theorem continuous_rightRegular_apply [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
    [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g : G => μ.rightRegular 𝕜 E p g f := by
  have hg : Continuous fun g : G => ContinuousMap.mulRight (X := G) g :=
    (ContinuousMap.curry
      ⟨fun q : G × G => q.2 * q.1, continuous_snd.mul continuous_fst⟩).continuous
  simp only [rightRegular_apply]
  exact continuous_const.compMeasurePreservingLp hg _ hp

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

/-- Right translation by `g` on `Lᵖ(G, E)` sends the singleton indicator at `h` to that at
`h * g⁻¹`. -/
@[simp]
theorem rightRegular_indicatorConstLp_singleton (g h : G)
    (hs : MeasurableSet ({h} : Set G)) (hμ : μ {h} ≠ ∞) (c : E) :
    μ.rightRegular 𝕜 E p g (indicatorConstLp p hs hμ c) =
      indicatorConstLp (s := ({h * g⁻¹} : Set G)) p
        (by simpa using hs.preimage (measurable_mul_const g))
        (by simpa using
          ((measurePreserving_mul_right μ g).measure_preimage hs.nullMeasurableSet).trans_ne hμ)
        c := by
  rw [rightRegular_apply, Lp.indicatorConstLp_compMeasurePreserving]
  congr! 1
  simp

end RightInvariant

/-- Right translation by `g` on counting-measure `L²(G)` sends the `h`-th point-mass basis vector
to the `(h * g⁻¹)`-th. -/
@[simp]
theorem rightRegular_countHilbertBasis {G 𝕜 : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [MeasurableSingletonClass G] [RCLike 𝕜] (g h : G) :
    (count : Measure G).rightRegular 𝕜 𝕜 2 g (L2.countHilbertBasis 𝕜 G h) =
      L2.countHilbertBasis 𝕜 G (h * g⁻¹) := by
  simp [L2.countHilbertBasis_apply]

end MeasureTheory.Measure
