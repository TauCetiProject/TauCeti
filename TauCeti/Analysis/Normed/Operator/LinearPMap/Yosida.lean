/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic
public import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Yosida approximations of partial linear operators

For a partial linear map `A` over a nontrivially normed field, the bounded Yosida approximation
at `z` is `z² R(z) - z I`. At a resolvent point it factors through `A` and the normalized
resolvent, and approximations at two resolvent points commute. A contractive normalized
resolvent gives the estimate `‖A_z‖ ≤ 2 * ‖z‖`.

For a densely defined operator, norm decay of the resolvents and a uniform bound on the
normalized resolvents imply strong convergence of the normalized resolvents to the identity.
The Yosida approximations then converge to `A` on its domain. These criteria apply to any
scalar family and filter; they do not require completeness or a semigroup structure.

The algebraic construction and estimates are developed in the semigroup literature below.

## References

* Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.5.
* Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1.
-/

public section

noncomputable section

namespace LinearPMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The **Yosida approximation** of an unbounded operator `A` at `lambda`:
`A_lambda = lambda ^ 2 R(lambda, A) - lambda I`.

The definition is meaningful when `lambda` belongs to the resolvent set of `A`; its algebraic API
carries that membership explicitly, while the norm estimates carry the resolvent bound they use. -/
def yosidaApproximation (A : X →ₗ.[𝕜] X) (lambda : 𝕜) : X →L[𝕜] X :=
  lambda ^ 2 • LinearPMap.resolvent A lambda - lambda • 1

/-- The operator formula for the Yosida approximation. -/
theorem yosidaApproximation_def (A : X →ₗ.[𝕜] X) (lambda : 𝕜) :
    yosidaApproximation A lambda =
      lambda ^ 2 • LinearPMap.resolvent A lambda - lambda • 1 := (rfl)

/-- Pointwise form of the definition of the Yosida approximation. -/
@[simp]
theorem yosidaApproximation_apply (A : X →ₗ.[𝕜] X) (lambda : 𝕜) (x : X) :
    yosidaApproximation A lambda x =
      lambda ^ 2 • LinearPMap.resolvent A lambda x - lambda • x := by
  simp [yosidaApproximation]

/-- At a point of the resolvent set, the Yosida approximation is `lambda A R(lambda, A)`
pointwise. -/
theorem yosidaApproximation_apply_eq_smul_apply_resolvent {A : X →ₗ.[𝕜] X} {lambda : 𝕜}
    (hlambda : lambda ∈ LinearPMap.resolventSet A) (x : X) :
    yosidaApproximation A lambda x = lambda • A ⟨LinearPMap.resolvent A lambda x,
      LinearPMap.resolvent_mem_domain hlambda x⟩ := by
  rw [yosidaApproximation_apply, LinearPMap.apply_resolvent hlambda]
  module

/-- Yosida approximations at two resolvent points commute. -/
theorem yosidaApproximation_comm {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜}
    (hlambda : lambda ∈ LinearPMap.resolventSet A)
    (hmu : mu ∈ LinearPMap.resolventSet A) :
    Commute (yosidaApproximation A lambda) (yosidaApproximation A mu) := by
  have hRR : Commute
      (lambda ^ 2 • LinearPMap.resolvent A lambda)
      (mu ^ 2 • LinearPMap.resolvent A mu) :=
    let h : Commute (LinearPMap.resolvent A lambda) (LinearPMap.resolvent A mu) :=
      _root_.LinearPMap.resolvent_comm hlambda hmu
    h.smul_left (lambda ^ 2) |>.smul_right (mu ^ 2)
  have hR_one : Commute
      (lambda ^ 2 • LinearPMap.resolvent A lambda)
      (mu • (1 : X →L[𝕜] X)) :=
    (Commute.one_right _).smul_right mu
  have hone_R : Commute
      (lambda • (1 : X →L[𝕜] X))
      (mu ^ 2 • LinearPMap.resolvent A mu) :=
    (Commute.one_left _).smul_left lambda
  have hone_one : Commute
      (lambda • (1 : X →L[𝕜] X))
      (mu • (1 : X →L[𝕜] X)) :=
    (Commute.refl (1 : X →L[𝕜] X)).smul_left lambda |>.smul_right mu
  rw [yosidaApproximation, yosidaApproximation]
  exact (hRR.sub_left hone_R).sub_right (hR_one.sub_left hone_one)

/-- At a resolvent point, the Yosida approximation acts on `x ∈ D(A)` as
`A_lambda x = lambda R(lambda, A) (A x)`. -/
theorem yosidaApproximation_apply_eq_smul_resolvent_apply {A : X →ₗ.[𝕜] X} {lambda : 𝕜}
    (hlambda : lambda ∈ LinearPMap.resolventSet A) (x : A.domain) :
    yosidaApproximation A lambda (x : X) =
      lambda • LinearPMap.resolvent A lambda (A x) := by
  rw [yosidaApproximation_apply_eq_smul_apply_resolvent hlambda]
  exact congrArg (lambda • ·) (LinearPMap.resolvent_apply_comm hlambda x).symm

/-- On the domain, normalized resolvents converge to the identity whenever the resolvent
norm tends to zero along a family of resolvent points. -/
theorem tendsto_smul_resolvent_apply_of_mem {ι : Type*} {l : Filter ι} {z : ι → 𝕜}
    {A : X →ₗ.[𝕜] X}
    (hres : ∀ᶠ i in l, z i ∈ A.resolventSet)
    (hzero : Filter.Tendsto (fun i => ‖A.resolvent (z i)‖) l (nhds 0))
    (x : A.domain) :
    Filter.Tendsto (fun i => z i • A.resolvent (z i) (x : X)) l (nhds (x : X)) := by
  have hRzero : Filter.Tendsto (fun i => A.resolvent (z i) (A x)) l (nhds 0) := by
    apply squeeze_zero_norm' (Filter.Eventually.of_forall fun i =>
      ContinuousLinearMap.le_opNorm (A.resolvent (z i)) (A x))
    simpa using hzero.mul_const ‖A x‖
  have heq : (fun i => (x : X) + A.resolvent (z i) (A x)) =ᶠ[l]
      (fun i => z i • A.resolvent (z i) (x : X)) := by
    filter_upwards [hres] with i hi
    rw [(LinearPMap.resolvent_apply_comm hi x).trans
      (LinearPMap.apply_resolvent hi (x : X))]
    abel
  simpa only [add_zero] using (tendsto_const_nhds.add hRzero).congr' heq

/-- Uniformly bounded normalized resolvents converge strongly to the identity if their
resolvents tend to zero in operator norm and the operator has dense domain. -/
theorem tendsto_smul_resolvent_apply {ι : Type*} {l : Filter ι} {z : ι → 𝕜}
    {A : X →ₗ.[𝕜] X} {M : ℝ}
    (hres : ∀ᶠ i in l, z i ∈ A.resolventSet)
    (hzero : Filter.Tendsto (fun i => ‖A.resolvent (z i)‖) l (nhds 0))
    (hbound : ∀ᶠ i in l, ‖z i • A.resolvent (z i)‖ ≤ M)
    (hdense : Dense (A.domain : Set X)) (x : X) :
    Filter.Tendsto (fun i => z i • A.resolvent (z i) x) l (nhds x) := by
  apply ContinuousLinearMap.tendsto_apply_of_dense (g := (1 : X →L[𝕜] X))
    hdense hbound _ x
  intro y hy
  simpa only [_root_.smul_apply, one_apply_eq_self] using
    tendsto_smul_resolvent_apply_of_mem hres hzero ⟨y, hy⟩

/-- Convergence of normalized resolvents at `A x` gives convergence of Yosida approximations
on the domain of `A`. -/
theorem tendsto_yosidaApproximation_apply {ι : Type*} {l : Filter ι} {z : ι → 𝕜}
    {A : X →ₗ.[𝕜] X} (hres : ∀ᶠ i in l, z i ∈ A.resolventSet) (x : A.domain)
    (hlim : Filter.Tendsto (fun i => z i • A.resolvent (z i) (A x)) l (nhds (A x))) :
    Filter.Tendsto (fun i => yosidaApproximation A (z i) x) l (nhds (A x)) := by
  apply hlim.congr'
  filter_upwards [hres] with i hi
  exact (yosidaApproximation_apply_eq_smul_resolvent_apply hi x).symm

/-- The Yosida approximation has norm at most twice the parameter norm when its normalized
resolvent is contractive. -/
theorem norm_yosidaApproximation_le {A : X →ₗ.[𝕜] X} {lambda : 𝕜}
    (hres : ‖lambda‖ * ‖LinearPMap.resolvent A lambda‖ ≤ 1) :
    ‖yosidaApproximation A lambda‖ ≤ 2 * ‖lambda‖ := by
  have hscaled : ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖ ≤ ‖lambda‖ := by
    simpa only [norm_smul, mul_one] using
      mul_le_mul_of_nonneg_left hres (norm_nonneg lambda)
  have hone : ‖lambda • (1 : X →L[𝕜] X)‖ ≤ ‖lambda‖ := by
    simpa only [norm_smul, ContinuousLinearMap.one_def, mul_one] using
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := X))
        (norm_nonneg lambda)
  calc
    ‖yosidaApproximation A lambda‖
        = ‖lambda • (lambda • LinearPMap.resolvent A lambda) - lambda • (1 : X →L[𝕜] X)‖ := by
          rw [yosidaApproximation, smul_smul, pow_two]
    _ ≤ ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖ + ‖lambda • (1 : X →L[𝕜] X)‖ :=
      norm_sub_le _ _
    _ ≤ ‖lambda‖ + ‖lambda‖ := add_le_add hscaled hone
    _ = 2 * ‖lambda‖ := (two_mul _).symm


end LinearPMap
