/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Composition

/-!
# Coordinate independence and inverses of canonical metric transports

Canonical transport between two positive metrics commutes with arbitrary continuous linear
changes of coordinates, not just isometries of the reference inner product. In particular, the
inverse-square-root construction in different bundle frames gives the same fibre map. The
coordinate maps need not preserve either metric: both metrics are pulled back together.

`ContinuousLinearMap.metricChangeBetween_bilinearComp` is the coordinate-change equation.
`ContinuousLinearMap.metricChangeBetweenEquiv` bundles the existing transport as a continuous
linear equivalence. Its inverse is exactly the canonical transport with the two metrics
exchanged, even when their Riesz operators do not commute. These statements include dimension
zero. They do not assert a strict composition law for three metrics.

The proofs use the uniqueness characterization of the positive source-self-adjoint isometry
in `ContinuousLinearMap.metricChangeBetween_eq_iff`, rather than covariance of a square root
under arbitrary congruence (which is false for the reference inner product).

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007, Chapter 1
  (positive square roots and congruences of metrics).
* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974,
  §§2, 9 (Euclidean bundles and orientations).
-/

public noncomputable section

open InnerProductSpace
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- Canonical transport between two positive metrics, as a continuous linear equivalence.
Its isometry property compares the two metrics, not the reference inner product. -/
def metricChangeBetweenEquiv (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) : E ≃L[ℝ] E :=
  (h.metricChangeEquiv hH).symm.trans
    (((k.bilinearComp h.metricChangeTransport h.metricChangeTransport).metricChangeEquiv
      (isStrictlyPositive_bilinearComp_metricChangeTransport h k hH hK)).trans
        (h.metricChangeEquiv hH))

/-- The bundled transport has the existing canonical transport as its underlying operator. -/
@[simp]
theorem coe_metricChangeBetweenEquiv (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    (h.metricChangeBetweenEquiv k hH hK : E →L[ℝ] E) = h.metricChangeBetween k := by
  ext x
  simp [metricChangeBetweenEquiv, metricChangeBetween_def, mul_apply_eq_comp]

/-- Evaluation of the bundled transport. -/
@[simp]
theorem metricChangeBetweenEquiv_apply (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (x : E) :
    h.metricChangeBetweenEquiv k hH hK x = h.metricChangeBetween k x :=
  congr($(coe_metricChangeBetweenEquiv h k hH hK) x)

/-- Transport from a positive metric to itself is the identity equivalence. -/
@[simp]
theorem metricChangeBetweenEquiv_self (h : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) :
    h.metricChangeBetweenEquiv h hH hH = ContinuousLinearEquiv.refl ℝ E := by
  ext x
  simp [hH]

/-- Transport from the reference inner product agrees with the inverse-square-root
equivalence of the target metric. -/
@[simp]
theorem metricChangeBetweenEquiv_innerSL (k : E →L[ℝ] E →L[ℝ] ℝ)
    (hR : IsStrictlyPositive (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)♯)
    (hK : IsStrictlyPositive k♯) :
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).metricChangeBetweenEquiv k hR hK =
      k.metricChangeEquiv hK := by
  ext x
  simp

/-- The inverse of transport from `h` to `k` is the canonical transport from `k` to `h`.
This holds without any commutation assumption on the two Riesz operators. -/
@[simp]
theorem metricChangeBetweenEquiv_symm (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    (h.metricChangeBetweenEquiv k hH hK).symm = k.metricChangeBetweenEquiv h hK hH := by
  let T := h.metricChangeBetweenEquiv k hH hK
  obtain ⟨hsym, hpos, hiso⟩ := (metricChangeBetween_eq_iff h k hH hK
    (T : E →L[ℝ] E)).1 (coe_metricChangeBetweenEquiv h k hH hK).symm
  simp only [ContinuousLinearEquiv.coe_coe] at hsym hpos hiso
  have hinv (u v : E) : h (T.symm u) (T.symm v) = k u v := by
    simpa using (hiso (T.symm u) (T.symm v)).symm
  have hsymInv (u v : E) : h (T.symm u) v = h u (T.symm v) := by
    simpa using (hsym (T.symm u) (T.symm v)).symm
  have heq : k.metricChangeBetween h = (T.symm : E →L[ℝ] E) := by
    apply (metricChangeBetween_eq_iff k h hK hH _).2
    simp only [ContinuousLinearEquiv.coe_coe]
    refine ⟨fun u v ↦ ?_, fun u ↦ ?_, hinv⟩
    · rw [← hinv, ← hinv, hsymInv]
    · rw [← hinv, hsymInv]
      -- Positivity of the inverse in the target metric is positivity of the forward
      -- transport in the source metric, evaluated at the twice-inverse image.
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hpos (T.symm (T.symm u))
  ext x
  simpa only [metricChangeBetweenEquiv_apply, ContinuousLinearEquiv.coe_coe, T] using
    (congr($(heq) x)).symm

/-- Reversing the metrics undoes the canonical transport. -/
@[simp]
theorem metricChangeBetween_apply_metricChangeBetween (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (x : E) :
    k.metricChangeBetween h (h.metricChangeBetween k x) = x := by
  simpa only [metricChangeBetweenEquiv_symm, metricChangeBetweenEquiv_apply] using
    (h.metricChangeBetweenEquiv k hH hK).symm_apply_apply x

section Coordinates

variable [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Canonical transport commutes with arbitrary linear changes of coordinates, with both
metrics pulled back together. This is the chart-independence equation for metric transport. -/
theorem metricChangeBetween_bilinearComp (h k : F →L[ℝ] F →L[ℝ] ℝ)
    (e : E ≃L[ℝ] F) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) (x : E) :
    (h.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)).metricChangeBetween
        (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)) x =
      e.symm (h.metricChangeBetween k (e x)) := by
  let h' := h.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)
  let k' := k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)
  let S : E →L[ℝ] E := (e.symm : F →L[ℝ] E).comp
    ((h.metricChangeBetween k).comp (e : E →L[ℝ] F))
  have hS (u : E) : e (S u) = h.metricChangeBetween k (e u) := by simp [S]
  obtain ⟨hsym, hpos, hiso⟩ := (metricChangeBetween_eq_iff h k hH hK _).1 rfl
  -- Conjugating the canonical transport satisfies the same intrinsic characterization.
  have heq : h'.metricChangeBetween k' = S := by
    apply (metricChangeBetween_eq_iff h' k'
      (isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp h _ hH e.injective)
      (isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp k _ hK e.injective) S).2
    simp only [h', k', bilinearComp_apply, ContinuousLinearEquiv.coe_coe, hS]
    exact ⟨fun u v ↦ hsym (e u) (e v), fun u ↦ hpos (e u), fun u v ↦ hiso (e u) (e v)⟩
  exact congr($(heq) x)

/-- The bundled transport is conjugated by a coordinate equivalence when both metrics are
pulled back. This comparison supplies both forward and inverse coordinate equations. -/
theorem metricChangeBetweenEquiv_bilinearComp (h k : F →L[ℝ] F →L[ℝ] ℝ)
    (e : E ≃L[ℝ] F) (hH : IsStrictlyPositive h♯)
    (hK : IsStrictlyPositive k♯) :
    (h.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)).metricChangeBetweenEquiv
        (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F))
        (isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp h _ hH e.injective)
        (isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp k _ hK e.injective) =
      e.trans ((h.metricChangeBetweenEquiv k hH hK).trans e.symm) := by
  ext x
  simp only [metricChangeBetweenEquiv_apply, ContinuousLinearEquiv.trans_apply,
    metricChangeBetween_bilinearComp h k e hH hK]

end Coordinates

end ContinuousLinearMap
