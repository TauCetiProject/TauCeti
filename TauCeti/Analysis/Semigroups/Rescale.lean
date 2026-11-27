/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Identity

import TauCeti.Topology.Algebra.Order.Field

/-!
# Time rescaling of strongly continuous semigroups

For a C₀-semigroup `S` and a speed `c ≥ 0`, the **rescaled semigroup** `S.rescale c` runs `S` at
speed `c`: `(S.rescale c) t = S (c * t)`. For `c ≠ 0` it has the same generator domain as `S`, and
its generator is `c • A`, where `A` is the generator of `S`: the difference quotient of the rescaled
semigroup at time `t` is `c` times that of `S` at time `c t`. Rescaling by `0` gives the identity
semigroup, whose generator is `0` on the whole space.

Rescaling is how a change of time unit acts on an evolution equation: if `S` solves `∂ₜu = A u`,
then `S.rescale c` solves `∂ₜu = c A u`. For example, a semigroup of Fourier multipliers with
symbol `exp (-c t ‖ξ‖²)` is a rescaled heat semigroup, and its generator is a multiple of the
Laplacian.

The C₀-group version, which allows negative speeds, is
`TauCeti.Semigroups.StronglyContinuousGroup.rescale`.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.rescale`: the C₀-semigroup `t ↦ S (c * t)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.realOperator_rescale`: in real time,
  `(S.rescale c).realOperator t = S.realOperator (c * t)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.rescale_rescale`: rescaling twice multiplies the
  speeds.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.rescale_zero`: rescaling by `0` gives the
  identity semigroup.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.rescale_domain`: for `c ≠ 0`, rescaling does not
  change the generator domain.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.rescale_generator`: for `c ≠ 0`, the generator
  of `t ↦ S (c * t)` is `c • A`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.2 (rescaled semigroups).
-/

public section

noncomputable section

open Filter
open scoped NNReal Topology

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The C₀-semigroup `t ↦ S (c * t)`: the semigroup `S` run at speed `c`. -/
def rescale (S : StronglyContinuousSemigroup X) (c : ℝ≥0) : StronglyContinuousSemigroup X where
  toFun t := S (c * t)
  map_zero' := by rw [mul_zero, S.map_zero]
  map_add' a b := by rw [mul_add, S.map_add]
  continuousAt_zero' x :=
    ContinuousAt.comp_of_eq (S.continuousAt_zero x)
      (by fun_prop : Continuous fun t : ℝ≥0 => c * t).continuousAt (mul_zero c)

@[simp]
theorem rescale_apply (S : StronglyContinuousSemigroup X) (c t : ℝ≥0) :
    S.rescale c t = S (c * t) := by
  rw [rescale]
  rfl

/-- In real time the rescaled semigroup is `t ↦ S (c * t)` as well. -/
@[simp]
theorem realOperator_rescale (S : StronglyContinuousSemigroup X) (c : ℝ≥0) (t : ℝ) :
    (S.rescale c).realOperator t = S.realOperator (c * t) := by
  rw [realOperator_def, realOperator_def, rescale_apply, Real.toNNReal_mul c.coe_nonneg,
    Real.toNNReal_coe]

/-- Rescaling by `1` does nothing. -/
@[simp]
theorem rescale_one (S : StronglyContinuousSemigroup X) : S.rescale 1 = S :=
  ext fun t => by rw [rescale_apply, one_mul]

/-- Rescaling twice multiplies the speeds. -/
@[simp]
theorem rescale_rescale (S : StronglyContinuousSemigroup X) (c d : ℝ≥0) :
    (S.rescale c).rescale d = S.rescale (c * d) :=
  ext fun t => by rw [rescale_apply, rescale_apply, rescale_apply, mul_assoc]

/-- Rescaling by `0` gives the identity semigroup. -/
@[simp]
theorem rescale_zero (S : StronglyContinuousSemigroup X) :
    S.rescale 0 = StronglyContinuousSemigroup.id X :=
  ext fun t => by rw [rescale_apply, zero_mul, S.map_zero, id_apply]

/-- If the difference quotient of `S` at `x` tends to `y`, then that of `S.rescale c` tends to
`c • y`, for `c ≠ 0`. -/
private theorem tendsto_rescale_genQuot (S : StronglyContinuousSemigroup X) {c : ℝ≥0}
    (hc : c ≠ 0) {x y : X}
    (h : Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t x - x)) (𝓝[>] 0) (𝓝 y)) :
    Tendsto (fun t : ℝ => (1 / t) • ((S.rescale c).realOperator t x - x)) (𝓝[>] 0)
      (𝓝 ((c : ℝ) • y)) := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  refine ((h.comp (tendsto_const_mul_nhdsGT_zero hc')).const_smul (c : ℝ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Function.comp_apply, realOperator_rescale, smul_smul]
  congr 1
  field_simp

/-- For `c ≠ 0`, the operator `c • A` is a restriction of the generator of `S.rescale c`. -/
private theorem smul_generator_le_generator_rescale (S : StronglyContinuousSemigroup X)
    {c : ℝ≥0} (hc : c ≠ 0) : (c : ℝ) • S.generator ≤ (S.rescale c).generator :=
  (S.rescale c).le_generator_of_forall_tendsto fun x =>
    tendsto_rescale_genQuot S hc (S.generator_tendsto ⟨x, by
      rw [← generator_domain, ← LinearPMap.smul_domain (c : ℝ)]
      exact x.property⟩)

/-- **Rescaling by a nonzero speed does not change the generator domain.** -/
@[simp]
theorem rescale_domain (S : StronglyContinuousSemigroup X) {c : ℝ≥0} (hc : c ≠ 0) :
    (S.rescale c).domain = S.domain := by
  refine le_antisymm ?_ ?_
  · have h := (smul_generator_le_generator_rescale (S.rescale c) (inv_ne_zero hc)).1
    rwa [LinearPMap.smul_domain, generator_domain, generator_domain, rescale_rescale,
      mul_inv_cancel₀ hc, rescale_one] at h
  · have h := (smul_generator_le_generator_rescale S hc).1
    rwa [LinearPMap.smul_domain, generator_domain, generator_domain] at h

/-- **The generator of a rescaled semigroup.** For `c ≠ 0` the generator of `t ↦ S (c * t)` is
`c • A`, on the domain of the generator `A` of `S`. -/
@[simp]
theorem rescale_generator (S : StronglyContinuousSemigroup X) {c : ℝ≥0} (hc : c ≠ 0) :
    (S.rescale c).generator = (c : ℝ) • S.generator :=
  (LinearPMap.eq_of_le_of_domain_eq (smul_generator_le_generator_rescale S hc) (by
    rw [LinearPMap.smul_domain, generator_domain, generator_domain, S.rescale_domain hc])).symm

end TauCeti.Semigroups.StronglyContinuousSemigroup
