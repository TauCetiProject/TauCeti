/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Damping
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Complete adapted pseudo-gradients of proper functions

On a noncompact manifold an adapted pseudo-gradient of a Morse function need not be complete, even
when the function is proper and bounded below: the negative Euclidean gradient of `x² + x⁴` on
`ℝ` has a trajectory escaping in finite backward time
(`TauCeti.NoncompactLineExample.exists_isIntegralCurveOn_Icc_iff`), and so does any adapted
pseudo-gradient that agrees with it outside a bounded neighbourhood of `0`. This file shows that
every adapted pseudo-gradient of a smooth proper function can be rescaled to a complete one,
without changing it near the critical points.

The rescaled field is the damped field `TauCeti.rateDampedField 𝓘(ℝ, E) f X`, the positive
multiple `rateDamping (df(X)) • X` of `X` from `TauCeti.Geometry.Manifold.Flow.Damping`. It is
again a pseudo-gradient adapted to `f` (`TauCeti.IsAdaptedPseudoGradient.rateDampedField`): it is
smooth, `df` stays negative on it away from the critical points because the factor is positive,
and near each critical point, where `|df(X)| ≤ 1`, it equals `X`, so a Morse chart in which `X`
is linear, restricted to the open set where `|df(X)| < 1`, is a Morse chart in which the damped
field is linear. Along the damped field `f` changes at rate at most `2`, so when `f` is proper the
damped field is complete (`TauCeti.IsAdaptedPseudoGradient.isCompleteVectorField_rateDampedField`).
No lower bound on `f` is needed for completeness.

So whenever a proper Morse function on a noncompact manifold is given an adapted
pseudo-gradient `X`, the global flow used for stable and unstable manifolds and trajectory spaces
is available for the damped field of `X`. The existence of adapted pseudo-gradients on
noncompact manifolds is not provided here. The damped field has the same oriented trajectories
as `X`, since it is a positive multiple of it.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.rateDampedField`: the damped field of an adapted
  pseudo-gradient of a smooth function is an adapted pseudo-gradient.
* `TauCeti.IsAdaptedPseudoGradient.isCompleteVectorField_rateDampedField`: for a proper smooth
  function it is complete.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (pseudo-gradient fields).
* J. Milnor, *Morse theory*, Annals of Mathematics Studies **51**, Princeton University Press,
  1963, the proof of Theorem 3.1 (rescaling a gradient field to control its flow).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-- **Damping an adapted pseudo-gradient keeps it adapted.** For a smooth function `f`, the damped
field `rateDamping (df(X)) • X` of a pseudo-gradient `X` adapted to `f` is again adapted to `f`.
It agrees with `X` on the open set where `|df(X)| < 1`, which contains the critical points, so the
Morse charts of `X` restricted to that set serve for it. -/
protected theorem rateDampedField (hX : IsAdaptedPseudoGradient f X)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    IsAdaptedPseudoGradient f (rateDampedField 𝓘(ℝ, E) f X) where
  contMDiff := contMDiff_rateDampedField (n := ⊤) (hf.of_le (by simp)) hX.contMDiff
  mvfderiv_apply_lt_zero x hx := by
    rw [mvfderiv_rateDampedField]
    exact mul_neg_of_pos_of_neg (rateDamping_pos _) (hX.mvfderiv_apply_lt_zero x hx)
  exists_morseChart x hx := by
    obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
    -- On the open set where `|df(X)| < 1`, which contains `x`, the two fields agree.
    have hdf : Continuous fun y ↦ mvfderiv 𝓘(ℝ, E) f y (X y) :=
      ((hf.contMDiff_mvfderiv_apply (m := 0) (by simp)).comp
        (hX.contMDiff.of_le (by simp))).continuous
    have hs : IsOpen {y | |mvfderiv 𝓘(ℝ, E) f y (X y)| < 1} :=
      isOpen_lt (continuous_abs.comp hdf) continuous_const
    have hxs : x ∈ {y | |mvfderiv 𝓘(ℝ, E) f y (X y)| < 1} := by
      simp [mvfderiv, hx]
    refine ⟨φ.restr hs hxs, fun y hy ↦ ?_⟩
    rw [MorseChart.restr_source] at hy
    rw [MorseChart.restr_toChart, OpenPartialHomeomorph.restr_apply, MorseChart.restr_coord,
      MorseChart.restr_weight, rateDampedField_of_abs_le_one hy.2.le]
    exact hφ y hy.1

/-- **The damped pseudo-gradient of a proper function is complete.** If `f` is smooth and proper
and `X` is a pseudo-gradient adapted to `f`, the adapted pseudo-gradient
`rateDamping (df(X)) • X` is complete. -/
theorem isCompleteVectorField_rateDampedField [CompleteSpace E] [T2Space M]
    (hX : IsAdaptedPseudoGradient f X) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hfp : IsProperMap f) :
    IsCompleteVectorField (rateDampedField 𝓘(ℝ, E) f X) :=
  _root_.TauCeti.isCompleteVectorField_rateDampedField hfp (hf.of_le (by simp))
    (hX.contMDiff.of_le (by simp))

end IsAdaptedPseudoGradient

end TauCeti
