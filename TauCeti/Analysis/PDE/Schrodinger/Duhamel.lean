/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Basic
public import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous

/-!
# The inhomogeneous Schrödinger equation on `L²`

On a finite-dimensional real inner product space `E`, the inhomogeneous free Schrödinger equation

`i ∂ₜu + Δu = G`, `u(0) = f`,

with initial value `f ∈ L²(E, F)` and a forcing term `G : ℝ → L²(E, F)` that is locally
integrable in time, is solved by **Duhamel's formula**

`u(t) = S(t) f - i ∫_{(0,t]} S(t - s) G(s) ds`

(`TauCeti.schrodingerDuhamel`), where `S(t) = exp(itΔ)` is the Schrödinger propagator
`TauCeti.schrodingerPropagator`. Written as `∂ₜu = iΔ u - i G`, the equation is the
inhomogeneous Cauchy problem for the generator `A` of the Schrödinger group, formally `iΔ`,
with forcing `-i G`. Its solution concept is that of mild solutions
(`TauCeti.Semigroups.IsForcedMildSolution`): `u` is continuous with values in `L²`, and
`A (∫_{(0,t]} u) = u(t) - f + i ∫_{(0,t]} G` for every `t ≥ 0`. Duhamel's formula is such a
solution (`TauCeti.isForcedMildSolution_schrodingerDuhamel`) and the only one
(`TauCeti.Semigroups.IsForcedMildSolution.eq_schrodingerDuhamel`).

Since `S(t)` is unitary, the solution satisfies the energy estimate

`‖u(t)‖₂ ≤ ‖f‖₂ + ∫_{(0,t]} ‖G(s)‖₂ ds`

(`TauCeti.norm_schrodingerDuhamel_le`) with constant `1`, with no integrability hypothesis on
`G`. Together with the continuity of `u` in time (`TauCeti.continuous_schrodingerDuhamel`), this
is the Strichartz estimate at the energy pair `(∞, 2)`: the solution lies in `C([0, T]; L²)` with
`sup_{t ≤ T} ‖u(t)‖₂ ≤ ‖f‖₂ + ‖G‖_{L¹([0,T]; L²)}`. The constant cannot be lowered, since for
`G = 0` the solution is `S(t) f`, whose norm is `‖f‖₂`.

## Main declarations

* `TauCeti.schrodingerDuhamel`: Duhamel's formula.
* `TauCeti.continuous_schrodingerDuhamel` and `TauCeti.norm_schrodingerDuhamel_le`: continuity in
  time and the energy estimate.
* `TauCeti.isForcedMildSolution_schrodingerDuhamel` and
  `TauCeti.Semigroups.IsForcedMildSolution.eq_schrodingerDuhamel`: Duhamel's formula is the
  unique mild solution.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Section 4.2.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {f : Lp F 2 (volume : Measure E)} {G : ℝ → Lp F 2 (volume : Measure E)}

/-- **Duhamel's formula** for the inhomogeneous Schrödinger equation `i ∂ₜu + Δu = G`,
`u(0) = f`: `u(t) = S(t) f - i ∫_{(0,t]} S(t - s) G(s) ds`, where `S(t) = exp(itΔ)`. -/
def schrodingerDuhamel (f : Lp F 2 (volume : Measure E)) (G : ℝ → Lp F 2 (volume : Measure E))
    (t : ℝ) : Lp F 2 (volume : Measure E) :=
  schrodingerPropagator F t f - Complex.I • ∫ s in Ioc 0 t, schrodingerPropagator F (t - s) (G s)

/-- Unfold Duhamel's formula. -/
theorem schrodingerDuhamel_def (f : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    schrodingerDuhamel f G t =
      schrodingerPropagator F t f -
        Complex.I • ∫ s in Ioc 0 t, schrodingerPropagator F (t - s) (G s) :=
  (rfl)

/-- Duhamel's formula takes the initial value `f` at time `0`. -/
@[simp]
theorem schrodingerDuhamel_apply_zero (f : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) : schrodingerDuhamel f G 0 = f := by
  simp [schrodingerDuhamel_def, phasePropagator_zero]

/-- Without forcing, Duhamel's formula is the free evolution `S(t) f`. -/
@[simp]
theorem schrodingerDuhamel_zero_forcing (f : Lp F 2 (volume : Measure E)) (t : ℝ) :
    schrodingerDuhamel f 0 t = schrodingerPropagator F t f := by
  simp [schrodingerDuhamel_def]

/-- The Duhamel integral of the Schrödinger group is `∫_{(0,t]} S(t - s) G(s) ds`. -/
private theorem duhamel_schrodinger (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    (phaseGroup E F laplacianSymbol).toSemigroup.duhamel G t =
      ∫ s in Ioc 0 t, schrodingerPropagator F (t - s) (G s) := by
  rw [Semigroups.StronglyContinuousSemigroup.duhamel_def]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [Semigroups.StronglyContinuousGroup.toSemigroup_realOperator_of_nonneg _
    (by linarith [hs.2] : 0 ≤ t - s), phaseGroup_apply]

/-- Duhamel's formula through the Schrödinger group and its Duhamel integral, at nonnegative
times. -/
private theorem schrodingerDuhamel_eq_realOperator_add_duhamel {t : ℝ} (ht : 0 ≤ t) :
    schrodingerDuhamel f G t =
      (phaseGroup E F laplacianSymbol).toSemigroup.realOperator t f +
        (phaseGroup E F laplacianSymbol).toSemigroup.duhamel ((-Complex.I) • G) t := by
  rw [Semigroups.StronglyContinuousGroup.toSemigroup_realOperator_of_nonneg _ ht, phaseGroup_apply,
    duhamel_schrodinger, schrodingerDuhamel_def, sub_eq_add_neg, ← neg_smul, ← integral_smul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  simp only [Pi.smul_apply, map_smul]

/-- Duhamel's formula is continuous in time, with values in `L²`. -/
theorem continuous_schrodingerDuhamel (f : Lp F 2 (volume : Measure E))
    (hG : LocallyIntegrableOn G (Ici 0)) : Continuous (schrodingerDuhamel f G) := by
  have h : schrodingerDuhamel f G = fun t => schrodingerPropagator F t f -
      Complex.I • (phaseGroup E F laplacianSymbol).toSemigroup.duhamel G t := by
    ext1 t
    rw [duhamel_schrodinger, schrodingerDuhamel_def]
  rw [h]
  exact (continuous_phasePropagator_apply laplacianSymbol f).sub
    (((phaseGroup E F laplacianSymbol).toSemigroup.continuous_duhamel hG).const_smul Complex.I)

/-- **The energy estimate** for the inhomogeneous Schrödinger equation:
`‖u(t)‖₂ ≤ ‖f‖₂ + ∫_{(0,t]} ‖G(s)‖₂ ds`. -/
theorem norm_schrodingerDuhamel_le (f : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    ‖schrodingerDuhamel f G t‖ ≤ ‖f‖ + ∫ s in Ioc 0 t, ‖G s‖ := by
  rw [schrodingerDuhamel_def]
  refine (norm_sub_le _ _).trans (add_le_add (norm_phasePropagator_apply laplacianSymbol t f).le ?_)
  rw [norm_smul, Complex.norm_I, one_mul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioc fun s _ =>
    norm_phasePropagator_apply laplacianSymbol (t - s) (G s)

/-- **Duhamel's formula is a mild solution** of the inhomogeneous Schrödinger equation: of
`∂ₜu = A u - i G`, `u(0) = f`, where `A` is the generator of the Schrödinger group. -/
theorem isForcedMildSolution_schrodingerDuhamel (f : Lp F 2 (volume : Measure E))
    (hG : LocallyIntegrableOn G (Ici 0)) :
    Semigroups.IsForcedMildSolution (phaseGroup E F laplacianSymbol).toSemigroup.generator
      ((-Complex.I) • G) f (schrodingerDuhamel f G) :=
  ((phaseGroup E F laplacianSymbol).toSemigroup.isForcedMildSolution_realOperator_add_duhamel
    (hG.smul (-Complex.I)) f).congr fun _ ht =>
      (schrodingerDuhamel_eq_realOperator_add_duhamel (mem_Ici.1 ht)).symm

/-- **Uniqueness for the inhomogeneous Schrödinger equation.** Every mild solution of
`∂ₜu = A u - i G`, `u(0) = f`, where `A` is the generator of the Schrödinger group, is given by
Duhamel's formula at every nonnegative time. -/
theorem Semigroups.IsForcedMildSolution.eq_schrodingerDuhamel {u : ℝ → Lp F 2 (volume : Measure E)}
    (hu : Semigroups.IsForcedMildSolution (phaseGroup E F laplacianSymbol).toSemigroup.generator
      ((-Complex.I) • G) f u)
    (hG : LocallyIntegrableOn G (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    u t = schrodingerDuhamel f G t :=
  hu.unique (isForcedMildSolution_schrodingerDuhamel f hG) (hG.smul (-Complex.I)) ht

end TauCeti
