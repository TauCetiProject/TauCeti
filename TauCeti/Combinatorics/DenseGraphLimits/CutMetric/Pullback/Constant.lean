/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.FiniteGraph
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Pullback.Basic
import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Pullback
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.UnitIntervalMap

/-!
# The map form of the cut distance to constant and point-mass graphons

This file evaluates the map form `cutDistPullback` of the cut distance exactly in the cases where
the coupling form `cutDist` is evaluated in `CutMetric.Constant` and `CutMetric.FiniteGraph`:
against a constant graphon, against a graphon on a point mass, and for the complete graph on the
uniform two-point carrier against the constant `1/2`.

The values are computed from the definition of the map form, not read off from the agreement
`cutDist_eq_cutDistPullback`. Against a constant graphon every pair of measure-preserving maps out
of `(I, volume)` contributes the same cut norm: the pulled-back difference is the pullback of
`U - p` along the first map alone, and pulling back along a measure-preserving map does not change
the cut norm. A graphon on a point mass is almost everywhere constant, and the map form only sees
almost-everywhere classes (`cutDistPullback_congr_ae_left`). So every value here agrees with the
corresponding value of `cutDist` independently of the equivalence. That agreement is an
independent check of `cutDist_eq_cutDistPullback` on carriers with atoms: a point mass, the
two-point carrier, and couplings mixing an atomic and a continuous direction.

The values are in general nonzero. On standard Borel carriers with atoms, there are no
measure-preserving *bijections* with `(I, volume)`. A map form indexed by that empty family
would be the junk value `0` there and would contradict these values.

## Main results

* `cutDistPullback_const_right`, `cutDistPullback_const_left`, `cutDistPullback_const_const` — the
  map form to a constant graphon is the cut norm of the difference with that constant;
* `cutDistPullback_dirac_right`, `cutDistPullback_dirac_left`, `cutDistPullback_dirac_dirac` — the
  corresponding values for graphons on point masses, with no hypothesis on a point-mass carrier;
* `cutDistPullback_finiteGraphGraphonOnFin_top_two_const_half` — the complete graph on the uniform
  two-point carrier is at map-form distance `1/8` from the constant `1/2` on any standard Borel
  probability carrier.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Thm 6.9 and Thm A.9.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §8.2.
-/

public section

noncomputable section

open MeasureTheory TauCeti.MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-! ### Constant graphons -/

/-- Along any one pair of measure-preserving maps out of `(I, volume)`, the map form of the cut
distance to a constant graphon `p` is `‖U - p‖□`, the cut norm being taken on `(Ω₁, μ₁)`. -/
private theorem cutDistPullback_const_right_of_measurePreserving (U : Graphon Ω₁ μ₁) (p : I)
    {f₀ : I → Ω₁} {g₀ : I → Ω₂} (hf₀ : MeasurePreserving f₀ volume μ₁)
    (hg₀ : MeasurePreserving g₀ volume μ₂) :
    cutDistPullback U (Graphon.const μ₂ p) =
      cutNorm μ₁ (U.toSymmKernel - (Graphon.const μ₁ p).toSymmKernel) := by
  -- Every pair of maps `f, g` contributes this same value: the difference of the two pullbacks is
  -- the pullback of `U - p` along `f` alone. The pair `f₀, g₀` makes the infimum a genuine one.
  have hval (f : I → Ω₁) (g : I → Ω₂) (hf : MeasurePreserving f volume μ₁)
      (hg : MeasurePreserving g volume μ₂) :
      cutNorm volume (U.toSymmKernel.comap f hf.measurable volume
        - (Graphon.const μ₂ p).toSymmKernel.comap g hg.measurable volume) =
      cutNorm μ₁ (U.toSymmKernel - (Graphon.const μ₁ p).toSymmKernel) := by
    rw [← cutNorm_comap hf]
    congr 1
    ext x y
    simp
  refine le_antisymm ((cutDistPullback_le U _ hf₀ hg₀).trans_eq (hval f₀ g₀ hf₀ hg₀)) ?_
  rw [cutDistPullback_def]
  exact le_csInf ⟨_, f₀, g₀, hf₀, hg₀, rfl⟩ fun r ⟨f, g, hf, hg, hr⟩ => hr ▸ (hval f g hf hg).ge

/-- **The map form of the cut distance to a constant graphon is a cut norm.** For a graphon `U` on
a standard Borel `(Ω₁, μ₁)` and the constant graphon `p` on a standard Borel `(Ω₂, μ₂)`, the map
form is `‖U - p‖□`, the cut norm being taken on `(Ω₁, μ₁)`. -/
theorem cutDistPullback_const_right [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂]
    (U : Graphon Ω₁ μ₁) (p : I) :
    cutDistPullback U (Graphon.const μ₂ p) =
      cutNorm μ₁ (U.toSymmKernel - (Graphon.const μ₁ p).toSymmKernel) := by
  -- The standard Borel hypotheses provide one pair of maps (Thm A.9, on each carrier separately).
  obtain ⟨f, hf⟩ := Measure.exists_measurePreserving_from_unitInterval μ₁
  obtain ⟨g, hg⟩ := Measure.exists_measurePreserving_from_unitInterval μ₂
  exact cutDistPullback_const_right_of_measurePreserving U p hf hg

/-- **The map form of the cut distance from a constant graphon is a cut norm**: it is `‖p - W‖□`,
the cut norm being taken on the carrier of `W`. -/
theorem cutDistPullback_const_left [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] (p : I)
    (W : Graphon Ω₂ μ₂) :
    cutDistPullback (Graphon.const μ₁ p) W =
      cutNorm μ₂ ((Graphon.const μ₂ p).toSymmKernel - W.toSymmKernel) := by
  -- By symmetry, from `cutDistPullback_const_right`.
  rw [cutDistPullback_comm, cutDistPullback_const_right, cutNorm_sub_rev]

/-- **Two constant graphons are at map-form cut distance `|p - q|`**, on standard Borel
probability carriers. -/
@[simp]
theorem cutDistPullback_const_const [StandardBorelSpace Ω₁] [StandardBorelSpace Ω₂] (p q : I) :
    cutDistPullback (Graphon.const μ₁ p) (Graphon.const μ₂ q) = |(p : ℝ) - q| := by
  rw [cutDistPullback_const_right]
  exact cutNorm_eq_abs_of_forall_eq μ₁ fun x y => by simp

/-! ### Graphons on point masses -/

/-- **The map form of the cut distance to a graphon on a point mass** `(Ω₂, δ_b)` is the cut norm
of the difference with the constant `W b b`, taken on the carrier of the other graphon. Only that
other carrier needs to be standard Borel. -/
theorem cutDistPullback_dirac_right [StandardBorelSpace Ω₁] {b : Ω₂} (U : Graphon Ω₁ μ₁)
    (W : Graphon Ω₂ (Measure.dirac b)) :
    cutDistPullback U W =
      cutNorm μ₁ (U.toSymmKernel - (Graphon.const μ₁ ⟨W b b, W.mem_Icc b b⟩).toSymmKernel) := by
  obtain ⟨f, hf⟩ := Measure.exists_measurePreserving_from_unitInterval μ₁
  rw [cutDistPullback_congr_ae_right W.ae_eq_const_of_dirac,
    cutDistPullback_const_right_of_measurePreserving U _ hf (measurePreserving_const_dirac b)]

/-- **The map form of the cut distance from a graphon on a point mass** `(Ω₁, δ_a)` is the cut norm
of the difference of the constant `U a a` with the other graphon, taken on the carrier of that
graphon. Only that other carrier needs to be standard Borel. -/
theorem cutDistPullback_dirac_left [StandardBorelSpace Ω₂] {a : Ω₁}
    (U : Graphon Ω₁ (Measure.dirac a)) (W : Graphon Ω₂ μ₂) :
    cutDistPullback U W =
      cutNorm μ₂ ((Graphon.const μ₂ ⟨U a a, U.mem_Icc a a⟩).toSymmKernel - W.toSymmKernel) := by
  rw [cutDistPullback_comm, cutDistPullback_dirac_right, cutNorm_sub_rev]

/-- **Two graphons on point masses are at map-form cut distance `|U a a - W b b|`**, on arbitrary
measurable carriers. -/
@[simp]
theorem cutDistPullback_dirac_dirac {a : Ω₁} {b : Ω₂} (U : Graphon Ω₁ (Measure.dirac a))
    (W : Graphon Ω₂ (Measure.dirac b)) : cutDistPullback U W = |U a a - W b b| := by
  rw [cutDistPullback_congr_ae_left U.ae_eq_const_of_dirac,
    cutDistPullback_congr_ae_right W.ae_eq_const_of_dirac,
    cutDistPullback_const_right_of_measurePreserving _ _ (measurePreserving_const_dirac a)
      (measurePreserving_const_dirac b)]
  exact cutNorm_eq_abs_of_forall_eq _ fun x y => by simp

/-! ### The complete graph on two points -/

/-- **The complete graph on the uniform two-point carrier is at map-form cut distance `1/8` from
the constant graphon `1/2`**, whatever the standard Borel probability carrier of the constant
graphon — a Bernoulli law, say, or `(I, volume)`.

The difference kernel is `1/2` on the two off-diagonal cells and `-1/2` on the two diagonal cells,
each of mass `1/4`; an off-diagonal cell attains `1/8`, and no rectangle does better. -/
@[simp]
theorem cutDistPullback_finiteGraphGraphonOnFin_top_two_const_half {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    cutDistPullback (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const μ ⟨2⁻¹, by norm_num, by norm_num⟩) = 1 / 8 := by
  -- The cut norm of the difference kernel is the value computed for the coupling form.
  rw [cutDistPullback_const_right, ← cutDist_const_right (μ₂ := μ),
    cutDist_finiteGraphGraphonOnFin_top_two_const_half]

end DenseGraphLimits

end TauCeti
