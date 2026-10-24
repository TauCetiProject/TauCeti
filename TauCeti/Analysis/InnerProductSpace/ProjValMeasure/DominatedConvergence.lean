/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Null

/-!
# Almost-everywhere invariance and dominated convergence for projection-valued integrals

Let `P` be a projection-valued measure on `X` acting on a complex Hilbert space `H`, with
diagonal measures `P.diag ξ`. The operator integral `P.integral f = ∫ f dP` of a bounded Borel
symbol `f` satisfies the vector norm identity `ProjValMeasure.norm_sq_integral_apply`,
`‖(∫ f dP) ξ‖ ^ 2 = ∫ ‖f x‖ ^ 2 d(P.diag ξ)(x)`.
It identifies the map `f ↦ (∫ f dP) ξ` as an isometry from the symbols, with the `L²` norm of
`P.diag ξ`, into `H`, and transfers scalar integration theory to the operator integral:

* the integral only sees the symbol `P`-almost everywhere, and in fact two symbols have the
  same integral exactly when they agree `P`-almost everywhere;
* uniformly bounded symbols converging `P`-almost everywhere have integrals converging strongly,
  that is on every vector, by Lebesgue's dominated convergence theorem.

Strong convergence is the right conclusion here: the indicators of `(0, 1 / (n + 1))` converge
pointwise to `0` on `ℝ`, but the norm of their integral is `1` against any projection-valued
measure that charges every such interval.

## Main declarations

* `ProjValMeasure.integral_eq_integral_iff`: `∫ f dP = ∫ g dP` iff `f = g` `P`-almost everywhere.
* `ProjValMeasure.integral_congr_ae`: symbols equal `P`-almost everywhere have equal integrals.
* `ProjValMeasure.tendsto_integral_apply_filter_of_dominated_convergence`: bounded `P`-almost
  everywhere convergence of symbols gives strong convergence of their integrals.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill, 1991, Theorem 12.21.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The integral of `f` against `P` vanishes exactly when `f` vanishes `P`-almost everywhere. -/
theorem integral_eq_zero_iff (P : ProjValMeasure X H) (f : BoundedBorelFunction X) :
    P.integral f = 0 ↔ ⇑f =ᶠ[P.ae] 0 := by
  simp only [ContinuousLinearMap.ext_iff, zero_apply, integral_apply_eq_zero_iff, EventuallyEq,
    P.eventually_ae_iff]

/-- Two bounded Borel symbols have the same integral against `P` exactly when they agree
`P`-almost everywhere. -/
theorem integral_eq_integral_iff (P : ProjValMeasure X H) (f g : BoundedBorelFunction X) :
    P.integral f = P.integral g ↔ ⇑f =ᶠ[P.ae] g := by
  rw [← sub_eq_zero, ← map_sub, integral_eq_zero_iff, BoundedBorelFunction.coe_sub]
  exact eventuallyEq_iff_sub.symm

/-- Bounded Borel symbols that agree `P`-almost everywhere have the same integral against `P`. -/
theorem integral_congr_ae (P : ProjValMeasure X H) {f g : BoundedBorelFunction X}
    (h : ⇑f =ᶠ[P.ae] g) : P.integral f = P.integral g :=
  (P.integral_eq_integral_iff f g).2 h

/-- **Dominated convergence** for the integral against a projection-valued measure: if bounded
Borel symbols `F n` are eventually bounded by a common constant `P`-almost everywhere and
converge to `f` `P`-almost everywhere, then their integrals converge to the integral of `f`
strongly, that is on every vector. -/
theorem tendsto_integral_apply_filter_of_dominated_convergence (P : ProjValMeasure X H)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {F : ι → BoundedBorelFunction X}
    {f : BoundedBorelFunction X} {M : ℝ} (h_bound : ∀ᶠ n in l, ∀ᶠ x in P.ae, ‖F n x‖ ≤ M)
    (h_lim : ∀ᶠ x in P.ae, Tendsto (fun n => F n x) l (𝓝 (f x))) (ξ : H) :
    Tendsto (fun n => P.integral (F n) ξ) l (𝓝 (P.integral f ξ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- `‖(∫ F n dP - ∫ f dP) ξ‖ ^ 2 = ∫ ‖F n - f‖ ^ 2 d(P.diag ξ)`, which tends to `0` by scalar
  -- dominated convergence with the constant bound `(M + ‖f‖) ^ 2`.
  have hsq : Tendsto (fun n => ‖P.integral (F n) ξ - P.integral f ξ‖ ^ 2) l (𝓝 0) := by
    simp_rw [← sub_apply, ← map_sub, norm_sq_integral_apply,
      BoundedBorelFunction.sub_apply]
    simpa using tendsto_integral_filter_of_dominated_convergence (f := fun _ => (0 : ℝ))
      (fun _ => (M + ‖f‖) ^ 2)
      (Eventually.of_forall fun n =>
        (((F n).measurable.sub f.measurable).norm.pow_const 2).aestronglyMeasurable)
      (h_bound.mono fun n hn => by
        filter_upwards [P.ae_diag_of_ae ξ hn] with x hx
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_sub_le _ _).trans (add_le_add hx (f.norm_coe_le_norm x))) 2)
      (integrable_const _)
      ((P.ae_diag_of_ae ξ h_lim).mono fun x hx => by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hx).pow 2)
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

end ProjValMeasure
end TauCeti
