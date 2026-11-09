/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Analysis.SpecialFunctions.Exponential
public import TauCeti.Analysis.SpecialFunctions.Exponential.BilinForm
public import TauCeti.Analysis.Normed.Operator.Exponential
public import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Exponential paths of tame and compatible almost complex structures

Let `J` be a linear complex structure on a finite-dimensional real vector space `V` with
symplectic form `ω`. The variations of `J` through tame, respectively compatible, structures are
the endomorphisms `Y` with `Y J + J Y = 0` (`TauCeti.AlmostComplexStructure.tangentSpace`),
respectively those that are moreover skew-adjoint for `ω`
(`TauCeti.SymplecticForm.compatibleTangentSpace`); see
`TauCeti.Geometry.Symplectic.Cayley.Tangent`. This file gives one explicit path realizing each
such variation, depending smoothly on `J`, `Y` and time jointly.

For `Y` anticommuting with `J` put `B = ½ J Y`. Then `t ↦ exp(t B) J exp(-t B)` is a smooth path
of complex structures through `J` with velocity `Y`
(`TauCeti.AlmostComplexStructure.tangentPath` and
`TauCeti.AlmostComplexStructure.hasDerivAt_tangentPath`). If `J` is `ω`-compatible and `Y` lies
in the compatible tangent space, then `B` is infinitesimally symplectic, so every `exp(t B)` is a
linear symplectomorphism and the whole path consists of `ω`-compatible structures
(`TauCeti.SymplecticForm.Compatible.tangentPath`). Tameness is an open condition
(`TauCeti.SymplecticForm.Tames.eventually_of_continuousAt`), so for a tame `J` the path is
`ω`-tame for small `t` (`TauCeti.SymplecticForm.Tames.eventually_tangentPath`).

The path depends smoothly on `J`, `Y` and the time parameter jointly
(`TauCeti.AlmostComplexStructure.contMDiffAt_tangentPath`), so a smooth family of structures and
a smooth family of tangent vectors over a manifold of parameters, such as the points of a
Floer domain, give a smooth family of variations.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.2 (the tangent space of the space of compatible
  almost complex structures).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.5.
-/

public section

noncomputable section

open NormedSpace Filter Topology Metric Manifold

namespace TauCeti

variable {V : Type*}

section Normed

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace AlmostComplexStructure

/-- The complex structure `exp(B) J exp(-B)`: the transport of `J` along the linear automorphism
`exp B` of `V`. -/
def expConj (J : AlmostComplexStructure V) (B : V →L[ℝ] V) :
    AlmostComplexStructure V :=
  J.transport B.expEquiv.toLinearEquiv

@[simp]
theorem expConj_toLinearMap (J : AlmostComplexStructure V) (B : V →L[ℝ] V) :
    (J.expConj B).toLinearMap =
      (exp B * LinearMap.toContinuousLinearMap J.toLinearMap * exp (-B)).toLinearMap :=
  LinearMap.ext fun v => by simp [expConj, mul_apply_eq_comp]

theorem expConj_apply (J : AlmostComplexStructure V) (B : V →L[ℝ] V) (v : V) :
    J.expConj B v = exp B (J (exp (-B) v)) := by
  simp [expConj]

@[simp]
theorem expConj_zero (J : AlmostComplexStructure V) : J.expConj 0 = J := by
  apply toLinearMap_injective
  simp [expConj_toLinearMap]

/-- The path `t ↦ exp(t B) J exp(-t B)` with `B = ½ J Y`. When `Y` anticommutes with `J` it is a
smooth path of complex structures through `J` with velocity `Y`
(`TauCeti.AlmostComplexStructure.hasDerivAt_tangentPath`). -/
def tangentPath (J : AlmostComplexStructure V) (Y : V →L[ℝ] V) (t : ℝ) :
    AlmostComplexStructure V :=
  J.expConj (t • (2⁻¹ : ℝ) • (LinearMap.toContinuousLinearMap J.toLinearMap * Y))

/-- In operator-norm coordinates the tangent path is `exp(t B) J exp(-t B)` with `B = ½ J Y`. -/
theorem toContinuousLinearMap_tangentPath (J : AlmostComplexStructure V) (Y : V →L[ℝ] V)
    (t : ℝ) :
    LinearMap.toContinuousLinearMap (J.tangentPath Y t).toLinearMap =
      exp (t • (2⁻¹ : ℝ) • (LinearMap.toContinuousLinearMap J.toLinearMap * Y)) *
        LinearMap.toContinuousLinearMap J.toLinearMap *
        exp (-(t • (2⁻¹ : ℝ) • (LinearMap.toContinuousLinearMap J.toLinearMap * Y))) :=
  ContinuousLinearMap.ext fun v => by simp only [tangentPath, LinearMap.coe_toContinuousLinearMap',
    expConj_apply, mul_apply_eq_comp]

@[simp]
theorem tangentPath_zero (J : AlmostComplexStructure V) (Y : V →L[ℝ] V) :
    J.tangentPath Y 0 = J := by
  simp [tangentPath]

/-- The path `TauCeti.AlmostComplexStructure.tangentPath` has velocity `Y` at `t = 0` whenever
`Y` anticommutes with `J`. -/
theorem hasDerivAt_tangentPath {J : AlmostComplexStructure V} {Y : V →L[ℝ] V}
    (hY : (Y : Module.End ℝ V) ∈ J.tangentSpace) :
    HasDerivAt (fun t => LinearMap.toContinuousLinearMap (J.tangentPath Y t).toLinearMap) Y 0 := by
  set j := LinearMap.toContinuousLinearMap J.toLinearMap
  set B : V →L[ℝ] V := (2⁻¹ : ℝ) • (j * Y)
  have hjj : j * j = -1 := J.toContinuousLinearMap_mul_self
  have hjY : j * Y = -(Y * j) := ContinuousLinearMap.coe_injective <| by
    simpa [j] using eq_neg_of_add_eq_zero_right (mem_tangentSpace.1 hY)
  have hd := hasDerivAt_exp_mul_const_mul_exp_neg B j
  have hBj : B * j - j * B = Y := by
    have h1 : j * Y * j = Y := by rw [hjY, neg_mul, mul_assoc, hjj, mul_neg_one, neg_neg]
    have h2 : j * (j * Y) = -Y := by rw [← mul_assoc, hjj, neg_one_mul]
    simp only [B, smul_mul_assoc, mul_smul_comm, h1, h2, smul_neg, sub_neg_eq_add]
    rw [← add_smul]
    norm_num
  rw [hBj] at hd
  refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [toContinuousLinearMap_tangentPath, smul_neg]

end AlmostComplexStructure

namespace AlmostComplexStructure

/-- The tangent path is smooth in time, structure and tangent vector jointly: for families
`J`, `Y` and times `τ` that are `C^n` at a point `p` of a manifold, so is the family of
structures `(J p).tangentPath (Y p) (τ p)`. -/
theorem contMDiffAt_tangentPath {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
    {J : N → AlmostComplexStructure V} {Y : N → V →L[ℝ] V} {τ : N → ℝ} {n : WithTop ℕ∞} {p : N}
    (hJ : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) p)
    (hY : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n Y p) (hτ : ContMDiffAt I 𝓘(ℝ) n τ p) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap ((J y).tangentPath (Y y) (τ y)).toLinearMap)
      p := by
  -- In operator-norm coordinates the path is a smooth expression in `(τ, J, Y)`.
  have hF : ContDiff ℝ n fun q : ℝ × (V →L[ℝ] V) × (V →L[ℝ] V) =>
      exp (q.1 • (2⁻¹ : ℝ) • (q.2.1 * q.2.2)) * q.2.1 *
        exp (-(q.1 • (2⁻¹ : ℝ) • (q.2.1 * q.2.2))) := by
    have hexp : ContDiff ℝ n (exp : (V →L[ℝ] V) → V →L[ℝ] V) :=
      contDiff_iff_contDiffAt.2 fun x => (exp_analytic (𝕂 := ℝ) x).contDiffAt
    have hB : ContDiff ℝ n fun q : ℝ × (V →L[ℝ] V) × (V →L[ℝ] V) =>
        q.1 • (2⁻¹ : ℝ) • (q.2.1 * q.2.2) := by
      fun_prop
    exact ((hexp.comp hB).mul (contDiff_fst.comp contDiff_snd)).mul (hexp.comp hB.neg)
  have h := hF.contDiffAt.comp_contMDiffAt (hτ.prodMk_space (hJ.prodMk_space hY))
  simp only [Function.comp_def] at h
  simpa only [toContinuousLinearMap_tangentPath] using h

/-- The tangent path is smooth in time. -/
theorem contDiff_tangentPath (J : AlmostComplexStructure V) (Y : V →L[ℝ] V) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun t => LinearMap.toContinuousLinearMap (J.tangentPath Y t).toLinearMap :=
  contMDiff_iff_contDiff.1 fun _ =>
    contMDiffAt_tangentPath (J := fun _ => J) (Y := fun _ => Y) contMDiffAt_const
      contMDiffAt_const contMDiffAt_id

end AlmostComplexStructure

namespace SymplecticForm

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The exponential of an infinitesimally symplectic endomorphism is a linear
symplectomorphism. -/
theorem isSymplectomorphism_expEquiv {B : V →L[ℝ] V} (hB : ω.toBilinForm.IsSkewAdjoint B) :
    IsSymplectomorphism ω ω B.expEquiv.toLinearEquiv :=
  isSymplectomorphism_iff.2 fun v w => by simpa using hB.apply_exp_apply_exp v w

/-- Conjugating an `ω`-compatible structure by the exponential of an infinitesimally symplectic
endomorphism gives an `ω`-compatible structure. -/
theorem Compatible.expConj (hJ : ω.Compatible J) {B : V →L[ℝ] V}
    (hB : ω.toBilinForm.IsSkewAdjoint B) : ω.Compatible (J.expConj B) := by
  have h := hJ.transport B.expEquiv.toLinearEquiv
  rwa [isSymplectomorphism_iff_transport_eq.1 (isSymplectomorphism_expEquiv hB)] at h

/-- The tangent path of an `ω`-compatible structure in a direction satisfying the compatible
tangent condition consists of `ω`-compatible structures. -/
theorem Compatible.tangentPath (hJ : ω.Compatible J) {Y : V →L[ℝ] V}
    (hY : (Y : Module.End ℝ V) ∈ ω.compatibleTangentSpace J) (t : ℝ) :
    ω.Compatible (J.tangentPath Y t) := by
  refine hJ.expConj ((LinearMap.mem_skewAdjointSubmodule _).1 ?_)
  rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_mul, LinearMap.coe_toContinuousLinearMap]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    ((LinearMap.mem_skewAdjointSubmodule _).2
      (hJ.invariant.isSkewAdjoint_mul_of_mem_compatibleTangentSpace hY)))

/-- The tangent path of an `ω`-tame structure is `ω`-tame for small times, in every direction. -/
theorem Tames.eventually_tangentPath (hJ : ω.Tames J) (Y : V →L[ℝ] V) :
    ∀ᶠ t in 𝓝 0, ω.Tames (J.tangentPath Y t) :=
  Tames.eventually_of_continuousAt ((J.contDiff_tangentPath Y (n := 0)).continuous.continuousAt)
    (by simpa using hJ)

end SymplecticForm

end Normed

end TauCeti
