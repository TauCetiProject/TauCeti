/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Quadratic actions and weak minimizers

The quadratic kinetic-plus-potential integral accepts a specified weak velocity. A minimizer
is itself an integral primitive with square-integrable velocity and values in the spatial
domain, on an ordered interval, and compares its action with all endpoint-fixed paths of this kind.
Its named projections give the admissibility conditions, action inequality, and path continuity.

## References

* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section
noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quadratic kinetic-plus-potential action with a specified weak velocity. -/
def quadraticAction (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (u w : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, G (t, u t) (w t) (w t) / 2 + V (t, u t)

/-- Admissibility and minimality of the actual quadratic integral among endpoint-fixed primitives
with square-integrable velocities and values in the specified spatial domain. -/
def IsQuadraticActionMinimizerOn (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (V : ℝ × E → ℝ) (U : Set E) (u w : ℝ → E) (a b : ℝ) : Prop :=
  a ≤ b ∧ MapsTo u (Icc a b) U ∧ MemLp w 2 (volume.restrict (Icc a b)) ∧
    (∀ t ∈ Icc a b, u t = u a + ∫ r in a..t, w r) ∧
    ∀ v z : ℝ → E, MemLp z 2 (volume.restrict (Icc a b)) →
      MapsTo v (Icc a b) U → v a = u a → v b = u b →
      (∀ t ∈ Icc a b, v t = v a + ∫ r in a..t, z r) →
      quadraticAction G V u w a b ≤ quadraticAction G V v z a b

/-- The defining integral of the quadratic action. -/
theorem quadraticAction_def (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (V : ℝ × E → ℝ) (u w : ℝ → E) (a b : ℝ) :
    quadraticAction G V u w a b = ∫ t in a..b,
      G (t, u t) (w t) (w t) / 2 + V (t, u t) := by
  rfl

/-- The candidate admissibility and comparison properties of a quadratic action minimizer. -/
theorem isQuadraticActionMinimizerOn_iff (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (V : ℝ × E → ℝ) (U : Set E) (u w : ℝ → E) (a b : ℝ) :
    IsQuadraticActionMinimizerOn G V U u w a b ↔
      a ≤ b ∧ MapsTo u (Icc a b) U ∧ MemLp w 2 (volume.restrict (Icc a b)) ∧
        (∀ t ∈ Icc a b, u t = u a + ∫ r in a..t, w r) ∧
        ∀ v z : ℝ → E, MemLp z 2 (volume.restrict (Icc a b)) →
          MapsTo v (Icc a b) U → v a = u a → v b = u b →
          (∀ t ∈ Icc a b, v t = v a + ∫ r in a..t, z r) →
          quadraticAction G V u w a b ≤ quadraticAction G V v z a b := by
  rfl

namespace IsQuadraticActionMinimizerOn

variable {G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {V : ℝ × E → ℝ} {U : Set E}
  {u w : ℝ → E} {a b : ℝ} (hmin : IsQuadraticActionMinimizerOn G V U u w a b)

include hmin

/-- The endpoints of a quadratic action minimizer are ordered. -/
theorem le : a ≤ b := hmin.1

/-- A quadratic action minimizer stays in its spatial domain. -/
theorem mapsTo : MapsTo u (Icc a b) U := hmin.2.1

/-- The weak velocity of a quadratic action minimizer is square integrable. -/
theorem memLp : MemLp w 2 (volume.restrict (Icc a b)) := hmin.2.2.1

/-- A quadratic action minimizer is the integral primitive of its weak velocity. -/
theorem eq_add_integral {t : ℝ} (ht : t ∈ Icc a b) :
    u t = u a + ∫ r in a..t, w r :=
  hmin.2.2.2.1 t ht

/-- The action of a minimizer is bounded by the action of every admissible competitor. -/
theorem quadraticAction_le {v z : ℝ → E} (hz : MemLp z 2 (volume.restrict (Icc a b)))
    (hv : MapsTo v (Icc a b) U) (hva : v a = u a) (hvb : v b = u b)
    (hprimitive : ∀ t ∈ Icc a b, v t = v a + ∫ r in a..t, z r) :
    quadraticAction G V u w a b ≤ quadraticAction G V v z a b :=
  hmin.2.2.2.2 v z hz hv hva hvb hprimitive

/-- The position path of a quadratic action minimizer is continuous on its interval. -/
theorem continuousOn : ContinuousOn u (Icc a b) :=
  intervalIntegral.continuousOn_of_forall_eq_add_integral hmin.le u
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hmin.le).mpr
      (hmin.memLp.integrable (by norm_num))) (fun _ ht ↦ hmin.eq_add_integral ht)

end IsQuadraticActionMinimizerOn

/-- Pointwise equal position paths on the integration interval have equal quadratic actions. -/
theorem quadraticAction_congr {G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {V : ℝ × E → ℝ}
    {u v w : ℝ → E} {a b : ℝ} (huv : EqOn u v (uIcc a b)) :
    quadraticAction G V u w a b = quadraticAction G V v w a b := by
  simp only [quadraticAction_def]
  exact intervalIntegral.integral_congr fun t ht ↦ by rw [huv ht]

end TauCeti
