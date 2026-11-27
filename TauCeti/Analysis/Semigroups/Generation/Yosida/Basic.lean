/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.LinearPMap.Yosida
public import TauCeti.Analysis.Semigroups.BoundedGenerator.Perturbation
public import TauCeti.Analysis.Semigroups.Dissipative.Basic
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Yosida approximations

The generic Yosida definition, algebraic laws and convergence criteria come from
`TauCeti.Analysis.Normed.Operator.LinearPMap.Yosida`. This file develops their real-parameter
semigroup consequences.
For an operator `A` whose resolvent at `lambda > 0` satisfies the
contraction bound, its Yosida approximation is

`A_lambda = lambda ^ 2 R(lambda, A) - lambda I = lambda A R(lambda, A)`.

The resolvent estimate `lambda ‖R(lambda, A)‖ ≤ 1` makes `lambda R(lambda, A)` a contraction.
Splitting the exponential of `t A_lambda` into the commuting scalar and resolvent parts then proves
that `exp (t A_lambda)` is a contraction for every `t ≥ 0`. Thus each approximation generates a
uniformly continuous contraction semigroup. This is the bounded stage of the Yosida construction.

The real `_atTop` convergence statements specialize the criteria from
`TauCeti.Analysis.Normed.Operator.LinearPMap.Yosida` to `lambda → +∞`, using the bound
`‖R(lambda, A)‖ ≤ M / lambda` rather than assuming dissipativity, because the Hille--Yosida
generation theorem needs the same estimates at a growth constant larger than one: for a densely
defined operator with that bound, `lambda R(lambda, A)` converges strongly to the identity, hence
`A_lambda x` converges to `A x` on `D(A)`.

The compact-time Cauchy property of the associated semigroups needs a second, independent
hypothesis: a uniform bound `‖exp (s A_lambda)‖ ≤ M` on the Yosida exponentials, which the
Duhamel comparison contributes squared, as the factor `M ^ 2`. Those two statements therefore
carry two constants, the resolvent constant, written `K` there, and the exponential constant `M`.
An m-dissipative operator supplies both hypotheses with `K = M = 1`, its exponential bound being
the contraction estimate
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le_one`; under the Hille--Yosida bounds on
all resolvent powers the exponential bound is instead
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le`. The later generation argument defines
the limit of the approximating semigroups.

## Main results

* `TauCeti.Semigroups.yosidaSemigroup`: the uniformly continuous contraction semigroup generated
  by `A_lambda`.
* `TauCeti.Semigroups.tendsto_smul_resolvent_apply_atTop`: the strong convergence
  `lambda R(lambda, A) x -> x` for a densely defined operator obeying the resolvent bound.
* `TauCeti.Semigroups.tendsto_yosidaApproximation_apply_atTop`: the convergence
  `A_lambda x -> A x` on the domain of `A`.
* `TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact` and
  `TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem`: the Yosida
  semigroups are uniformly Cauchy on compact time intervals, on every vector and on domain
  vectors.
* `TauCeti.Semigroups.IsMDissipative.tendsto_smul_resolvent_apply_atTop`,
  `TauCeti.Semigroups.IsMDissipative.tendsto_yosidaApproximation_apply_atTop` and
  `TauCeti.Semigroups.IsMDissipative.exp_yosidaApproximation_uniformCauchySeqOn_compact`: the
  three convergence statements for an m-dissipative operator, the case `K = M = 1`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

open _root_.LinearPMap (yosidaApproximation)

noncomputable section

namespace TauCeti.Semigroups

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section

variable [CompleteSpace X]

/-- Split the exponential of a Yosida approximation into its commuting scalar and resolvent
factors:
`exp (t A_lambda) = exp (-t lambda I) exp (t lambda² R(lambda, A))`. -/
theorem exp_yosidaApproximation {A : X →ₗ.[ℝ] X} (lambda t : ℝ) :
    exp (t • yosidaApproximation A lambda) =
      exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
        exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda) := by
  have hsplit : t • yosidaApproximation A lambda =
      (-(t * lambda)) • (1 : X →L[ℝ] X) +
        (t * lambda ^ 2) • LinearPMap.resolvent A lambda := by
    rw [LinearPMap.yosidaApproximation_def, smul_sub]
    module
  rw [hsplit]
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  exact exp_add_of_commute (Commute.one_left _ |>.smul_left _ |>.smul_right _)

/-- The exponential of a positive-time multiple of a Yosida approximation is contractive. -/
theorem norm_exp_smul_yosidaApproximation_le_one {A : X →ₗ.[ℝ] X} {lambda t : ℝ}
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) (ht : 0 ≤ t) :
    ‖exp (t • yosidaApproximation A lambda)‖ ≤ 1 := by
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  calc
    ‖exp (t • yosidaApproximation A lambda)‖ =
        ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
          exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := by
      rw [exp_yosidaApproximation]
    _ ≤ ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ *
          ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := norm_mul_le _ _
    _ ≤ Real.exp (-(t * lambda)) *
          Real.exp ‖(t * lambda ^ 2) • LinearPMap.resolvent A lambda‖ := by
      gcongr
      · exact TauCeti.norm_exp_smul_one_le ContinuousLinearMap.norm_id_le _
      · exact TauCeti.norm_exp_le_exp_norm ContinuousLinearMap.norm_id_le _
    _ ≤ Real.exp (-(t * lambda)) * Real.exp (t * lambda) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t * lambda ^ 2)]
      calc
        t * lambda ^ 2 * ‖LinearPMap.resolvent A lambda‖
            = t * lambda * (lambda * ‖LinearPMap.resolvent A lambda‖) := by ring
        _ ≤ t * lambda * 1 := by gcongr
        _ = t * lambda := mul_one _
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The uniformly continuous contraction semigroup generated by the Yosida approximation. -/
def yosidaSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1)
    (hlambda : 0 < lambda) : ContractionSemigroup X where
  toStronglyContinuousSemigroup := StronglyContinuousSemigroup.ofBounded
    (yosidaApproximation A lambda)
  contracting t := by
    -- The `contracting` field exposes the raw `toFun`; it is definitionally the same function
    -- as the semigroup coercion used by `ofBounded_apply`.
    calc
      ‖(StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda)).toFun t‖ =
          ‖exp ((t : ℝ) • yosidaApproximation A lambda)‖ :=
        congrArg norm (StronglyContinuousSemigroup.ofBounded_apply _ t)
      _ ≤ 1 := norm_exp_smul_yosidaApproximation_le_one hres hlambda t.property

/-- The C₀-semigroup underlying the Yosida semigroup is the bounded-generator semigroup of the
Yosida approximation. -/
@[simp]
theorem yosidaSemigroup_toStronglyContinuousSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    (yosidaSemigroup A lambda hres hlambda).toStronglyContinuousSemigroup =
      StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda) := by
  simp [yosidaSemigroup]

/-- The Yosida semigroup is the exponential of the Yosida approximation. -/
@[simp]
theorem yosidaSemigroup_apply (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) (t : NNReal) :
    yosidaSemigroup A lambda hres hlambda t = exp ((t : ℝ) • yosidaApproximation A lambda) := by
  rw [← ContractionSemigroup.toStronglyContinuousSemigroup_apply,
    yosidaSemigroup_toStronglyContinuousSemigroup, StronglyContinuousSemigroup.ofBounded_apply]

/-- The Yosida semigroup is continuous in operator norm, not merely strongly continuous. -/
theorem continuous_yosidaSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    Continuous fun t : NNReal => yosidaSemigroup A lambda hres hlambda t := by
  refine (StronglyContinuousSemigroup.ofBounded_continuous
    (yosidaApproximation A lambda)).congr fun t => ?_
  exact (StronglyContinuousSemigroup.ofBounded_apply _ t).trans
    (yosidaSemigroup_apply A lambda hres hlambda t).symm

/-- The generator of the Yosida semigroup is the everywhere-defined Yosida approximation. -/
theorem yosidaSemigroup_generator (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    (yosidaSemigroup A lambda hres hlambda).toStronglyContinuousSemigroup.generator =
      (yosidaApproximation A lambda : X →ₗ[ℝ] X).toPMap ⊤ := by
  rw [yosidaSemigroup_toStronglyContinuousSemigroup,
    StronglyContinuousSemigroup.ofBounded_generator]

end

/-! ## Strong convergence of the approximations

The estimates of this section carry the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda` as an
explicit hypothesis rather than assuming dissipativity, since the Hille--Yosida generation theorem
needs them at a growth constant `M` larger than one. An m-dissipative operator is the case
`M = 1`, recorded by the `IsMDissipative` specializations at the end of the file. -/

/-- On the domain of `A`, the scaled resolvent differs from the identity by at most
`M ‖A x‖ / lambda`:

`‖lambda R(lambda, A) x - x‖ ≤ M ‖A x‖ / lambda`,

whenever `lambda` is a resolvent point with `‖R(lambda, A)‖ ≤ M / lambda`. This is the
quantitative core of the strong convergence `lambda R(lambda, A) -> I`. -/
theorem norm_smul_resolvent_apply_sub_self_le {A : X →ₗ.[ℝ] X} {lambda M : ℝ}
    (hlambda : lambda ∈ LinearPMap.resolventSet A)
    (hbound : ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda) (x : A.domain) :
    ‖lambda • LinearPMap.resolvent A lambda (x : X) - (x : X)‖ ≤ M * ‖A x‖ / lambda := by
  have hresolvent :
      lambda • LinearPMap.resolvent A lambda (x : X) - (x : X) =
        LinearPMap.resolvent A lambda (A x) := by
    exact ((LinearPMap.resolvent_apply_comm hlambda x).trans
      (LinearPMap.apply_resolvent hlambda (x : X))).symm
  rw [hresolvent]
  calc
    ‖LinearPMap.resolvent A lambda (A x)‖
        ≤ ‖LinearPMap.resolvent A lambda‖ * ‖A x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ M / lambda * ‖A x‖ := by gcongr
    _ = M * ‖A x‖ / lambda := by ring

/-- Under the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda` at a positive `lambda`, the scaled
resolvent `lambda R(lambda, A)` has norm at most `M`. -/
theorem norm_smul_resolvent_le {A : X →ₗ.[ℝ] X} {lambda M : ℝ} (hlambda : 0 < lambda)
    (hbound : ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda) :
    ‖lambda • LinearPMap.resolvent A lambda‖ ≤ M := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  calc
    lambda * ‖LinearPMap.resolvent A lambda‖ ≤ lambda * (M / lambda) := by gcongr
    _ = M := by field_simp

/-- For a densely defined operator obeying the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda`, the
scaled resolvents converge strongly to the identity on the whole Banach space:

`lambda R(lambda, A) x -> x` as `lambda -> +∞`.

The uniform bound `‖lambda R(lambda, A)‖ ≤ M` extends the domain estimate to all vectors by
density. -/
theorem tendsto_smul_resolvent_apply_atTop {A : X →ₗ.[ℝ] X} {M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda)
    (hdense : Dense (A.domain : Set X)) (x : X) :
    Filter.Tendsto (fun lambda : ℝ => lambda • LinearPMap.resolvent A lambda x)
      Filter.atTop (nhds x) := by
  apply LinearPMap.tendsto_smul_resolvent_apply
    (Filter.eventually_gt_atTop 0 |>.mono fun lambda hlambda => hres lambda hlambda) _
    (Filter.eventually_gt_atTop 0 |>.mono fun lambda hlambda =>
      norm_smul_resolvent_le hlambda (hbound lambda hlambda)) hdense x
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _
    (tendsto_const_nhds.div_atTop Filter.tendsto_id :
      Filter.Tendsto (fun lambda : ℝ => M / lambda) Filter.atTop (nhds 0))
  filter_upwards [Filter.eventually_gt_atTop 0] with lambda hlambda
  exact hbound lambda hlambda

/-- Under the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda` and density of the domain, the Yosida
approximations converge strongly to the original operator on its domain: `A_lambda x -> A x` for
every `x ∈ D(A)`. -/
theorem tendsto_yosidaApproximation_apply_atTop {A : X →ₗ.[ℝ] X} {M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) :
    Filter.Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X))
      Filter.atTop (nhds (A x)) := by
  apply LinearPMap.tendsto_yosidaApproximation_apply
    (Filter.eventually_gt_atTop 0 |>.mono fun lambda hlambda => hres lambda hlambda) x
  exact tendsto_smul_resolvent_apply_atTop hres hbound hdense (A x)

/-! ## Compact-time Cauchy convergence of the approximating semigroups

The two statements below take independent resolvent and exponential bounds, with constants `K`
and `M` respectively. For a dissipative operator the exponential bound is the contraction estimate
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le_one`; under the Hille--Yosida resolvent
power bounds for a general growth constant it is
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le`. -/

variable [CompleteSpace X]

/-- The bounded Yosida semigroups are Cauchy on domain vectors, uniformly on every compact time
interval. Explicitly, for `T ≥ 0`, the vectors `exp (t A_lambda) x` are uniformly Cauchy for
`0 ≤ t ≤ T` as `lambda -> +∞`, whenever `x ∈ D(A)`.

The resolvent bound has constant `K`, while the independent exponential bound has constant `M`.
The comparison estimate reduces the result to the convergence `A_lambda x -> A x` proved above,
at the cost of the factor `M ^ 2` from the two exponential factors of the Duhamel formula. -/
theorem exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem {A : X →ₗ.[ℝ] X} {K M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ K / lambda)
    (hexp : ∀ lambda : ℝ, 0 < lambda → ∀ s : ℝ, 0 ≤ s →
      ‖exp (s • yosidaApproximation A lambda)‖ ≤ M)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) {T : ℝ} :
    UniformCauchySeqOn
      (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) (x : X))
      Filter.atTop (Set.Icc 0 T) := by
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using
    uniformCauchySeqOn_exp_smul_apply_of_tendsto
      (𝕜 := ℝ) (S := Set.Icc 0 T) (M := M) (R := max T 0)
      (by
        filter_upwards [(Filter.eventually_gt_atTop (0 : ℝ)).prod_mk
            (Filter.eventually_gt_atTop (0 : ℝ))] with p hp
        exact LinearPMap.yosidaApproximation_comm (hres p.1 hp.1) (hres p.2 hp.2))
      (tendsto_yosidaApproximation_apply_atTop hres hbound hdense x)
      (by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lambda hlambda t ht s hs
        simpa only [RCLike.ofReal_real_eq_id, id_eq] using
          hexp lambda hlambda (s * t) (mul_nonneg hs.1 ht.1))
      (by
        intro t ht
        rw [abs_of_nonneg ht.1]
        exact ht.2.trans (le_max_left T 0))

/-- The bounded Yosida semigroups are Cauchy uniformly on every compact time interval, on every
vector of the Banach space.

This is the compact-time Cauchy estimate from which a candidate pointwise limit family is defined;
later arguments establish its semigroup structure and identify its generator as `A`. The domain
case is `TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem`; the uniform
bound `‖exp (s A_lambda)‖ ≤ M` extends it to the whole space by density of `D(A)`, independently
of the resolvent-bound constant `K`. -/
theorem exp_yosidaApproximation_uniformCauchySeqOn_compact {A : X →ₗ.[ℝ] X} {K M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ K / lambda)
    (hexp : ∀ lambda : ℝ, 0 < lambda → ∀ s : ℝ, 0 ≤ s →
      ‖exp (s • yosidaApproximation A lambda)‖ ≤ M)
    (hdense : Dense (A.domain : Set X)) (x : X) {T : ℝ} :
    UniformCauchySeqOn
      (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      Filter.atTop (Set.Icc 0 T) := by
  refine ContinuousLinearMap.uniformCauchySeqOn_apply_of_dense (𝕜 := ℝ)
    (f := fun lambda t => exp (t • yosidaApproximation A lambda)) (C := M) hdense ?_ ?_ x
  · filter_upwards [Filter.eventually_gt_atTop 0] with lambda hlambda t ht
    exact hexp lambda hlambda t ht.1
  · intro y hy
    exact exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem hres hbound hexp hdense
      (⟨y, hy⟩ : A.domain)

/-! ## The m-dissipative case

An m-dissipative operator has every positive `lambda` in its resolvent set with
`‖R(lambda, A)‖ ≤ 1 / lambda`, and its Yosida exponentials are contractions, so it supplies the
hypotheses of the results above with both constants equal to one. -/

namespace IsMDissipative

variable {A : X →ₗ.[ℝ] X}

/-- For a densely defined m-dissipative operator, the scaled resolvents converge strongly to the
identity on the whole Banach space: `lambda R(lambda, A) x -> x` as `lambda -> +∞`. -/
theorem tendsto_smul_resolvent_apply_atTop (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : X) :
    Filter.Tendsto (fun lambda : ℝ => lambda • LinearPMap.resolvent A lambda x)
      Filter.atTop (nhds x) :=
  _root_.TauCeti.Semigroups.tendsto_smul_resolvent_apply_atTop (M := 1)
    (fun _ h => hA.mem_resolventSet h)
    (fun _ h => by simpa [one_div] using hA.norm_resolvent_le h) hdense x

/-- For a densely defined m-dissipative operator, the Yosida approximations converge strongly to
the original operator on its domain: `A_lambda x -> A x` for every `x ∈ D(A)`. -/
theorem tendsto_yosidaApproximation_apply_atTop (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) :
    Filter.Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X))
      Filter.atTop (nhds (A x)) :=
  _root_.TauCeti.Semigroups.tendsto_yosidaApproximation_apply_atTop (M := 1)
    (fun _ h => hA.mem_resolventSet h)
    (fun _ h => by simpa [one_div] using hA.norm_resolvent_le h) hdense x

/-- For a densely defined m-dissipative operator, the bounded Yosida semigroups are Cauchy
uniformly on every compact time interval, on every vector of the Banach space. This is the
compact-time Cauchy estimate from which the contraction semigroup generated by `A` is built. -/
theorem exp_yosidaApproximation_uniformCauchySeqOn_compact (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : X) {T : ℝ} :
    UniformCauchySeqOn
      (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      Filter.atTop (Set.Icc 0 T) :=
  _root_.TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact (K := 1) (M := 1)
    (fun _ h => hA.mem_resolventSet h)
    (fun _ h => by simpa [one_div] using hA.norm_resolvent_le h)
    (fun _ h _ hs => norm_exp_smul_yosidaApproximation_le_one
      (hA.mul_norm_resolvent_le_one h) h hs)
    hdense x

end IsMDissipative

end TauCeti.Semigroups

end
