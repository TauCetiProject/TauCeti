/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The asymptotic operator of a Hamiltonian orbit

Let `(V, ω)` be a symplectic vector space, `x` an orbit of a time-dependent Hamiltonian `H`, and
`J_t(y)` a family of almost complex structures. At the stationary cylinder `u(s, t) = x(t)` the
Floer operator `∂s u + J(∂t u - X_{H_t}(u))` has linearization

`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`,  `S_t = dX_{H_t}(x(t))`,  `J_t = J_t(x(t))`

(`SymplecticForm.floerLinearization_eq_stationaryCylinderOperator`). The target derivative of
`J` drops out, because it multiplies `∂t u - X_H(u)`, which vanishes along the orbit. On each
slice `s = const` the operator `D = TauCeti.Floer.stationaryCylinderOperator` is `∂s + A` for the
asymptotic operator `A ζ = J_t (ζ' - S_t ζ)` acting on loops
(`TauCeti.Floer.asymptoticOperator`, `Floer.stationaryCylinderOperator_eq_add_asymptoticOperator`).
These are the operators which describe the linearized Floer equation on cylindrical ends
asymptotic to `x`.

The basic identity is that for an `ω`-invariant `J_t` the associated form `g_t = ω(·, J_t ·)`
pairs `A ζ` with a vector `v` as `g_t(A ζ, v) = ω(ζ' - S_t ζ, v)`
(`Floer.associatedBilinForm_asymptoticOperator`): the almost complex structure cancels.
Consequently, if every `S_t` is infinitesimally symplectic, as `dX_{H_t}` is, then `A` is
symmetric for the `L²` pairing `∫₀¹ g_t(·, ·) dt` on one-periodic loops
(`Floer.integral_associatedBilinForm_asymptoticOperator_comm`), even when `J_t` depends on `t`.

The kernel of `A` consists of the solutions of the linearized Hamiltonian equation
`ζ' = S_t ζ` (`Floer.asymptoticOperator_eq_zero_iff`). Every such solution is `ζ(t) = Ψ(t) ζ(0)`
for the propagator `Ψ = TauCeti.dysonSeriesLeft S` of that equation, so `A` has a nonzero
one-periodic kernel element exactly when `Ψ(1)` fixes a nonzero vector, that is, when
`det (1 - Ψ(1)) = 0`
(`Floer.exists_ne_zero_asymptoticOperator_eq_zero_iff_exists_ne_zero_dysonSeriesLeft_apply_eq_self`
and `Floer.exists_ne_zero_asymptoticOperator_eq_zero_iff_det_eq_zero`).

For an actual orbit, with `S_t = dX_{H_t}(x(t))`, the variational equation of the Hamiltonian
evolution `φ` identifies the propagator with its derivative along the orbit,
`Ψ(t) = dφ(0, t)(x(0))` (`SymplecticForm.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`).
So `Ψ(1)` is the derivative of the time-one map at `x(0)`, and for a one-periodic orbit of a
one-periodic Hamiltonian the asymptotic operator has no nonzero one-periodic kernel element
exactly when the orbit is nondegenerate, that is, when `x(0)` is a nondegenerate fixed point of
the time-one map
(`SymplecticForm.isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero`).
This holds for every family `J_t`, compatible or not.

Operators on cylindrical ends act on maps decaying like `e^{-δ s}`. Conjugation by the weight
turns `D` into the operator `∂s + A - δ` (`Floer.stationaryCylinderOperator_exp_smul`), and
`A - δ` is the asymptotic operator of `S_t - δ J_t` (`Floer.asymptoticOperator_sub_smul`). For
continuous one-periodic `S` and `J` the weights `δ` at which `A - δ` has a nonzero one-periodic
kernel element form a closed set (`Floer.isClosed_setOf_exists_asymptoticOperator_eq_smul`),
because the return map of `S_t - δ J_t` depends continuously on `δ`. In particular, if `A` is
injective on one-periodic loops, then so is `A - δ` for all small `δ`; at a nondegenerate
orbit this is `SymplecticForm.eventually_eq_zero_of_asymptoticOperator_eq_smul`.

On the cylinder, the same cancellation gives the integrated form of `D* D = -∂s² + A²` over
`[a, b] × [0, 1]`, in which the cross term only contributes the slice pairings
`∫₀¹ ω(∂t ξ - S_t ξ, ξ) dt` at `s = a` and `s = b`
(`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator`). For compatible `J_t` it
shows that a solution of `D ξ = 0` which decays at both ends together with `∂t ξ` vanishes
(`Floer.eq_zero_of_stationaryCylinderOperator_eq_zero`), with no nondegeneracy assumption.

These are statements in a symplectic vector space with a constant form, matching the
local-coordinate linearization `TauCeti.SymplecticForm.floerLinearization`; the Sobolev
realization of `A` and `D` and their Fredholm theory are not treated here. For an actual orbit,
the continuity hypothesis on `S` is
`TauCeti.SymplecticForm.continuous_fderiv_hamiltonianVectorField_comp`. The model case of a
constant orthogonal complex structure on an inner product space is the operator
`TauCeti.orbitTorusOperator`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. 45 (1992), 1303–1360.
-/

public section

open Function Filter Set MeasureTheory Topology
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V} {ζ η : ℝ → V} {t : ℝ}

/-- The asymptotic operator `A ζ (t) = J_t (ζ'(t) - S_t ζ(t))` of the Floer equation along a
Hamiltonian orbit, with `S_t` the linearized Hamiltonian vector field along the orbit. The
linearized Floer operator at the stationary cylinder over the orbit is `∂s + A`. -/
noncomputable def asymptoticOperator (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (ζ : ℝ → V) (t : ℝ) : V :=
  J t (deriv ζ t - S t (ζ t))

/-- The defining formula of the asymptotic operator. -/
theorem asymptoticOperator_def (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (ζ : ℝ → V) (t : ℝ) :
    asymptoticOperator J S ζ t = J t (deriv ζ t - S t (ζ t)) :=
  (rfl)

/-- The asymptotic operator vanishes on the zero loop. -/
@[simp]
theorem asymptoticOperator_zero : asymptoticOperator J S 0 = 0 := by
  funext t
  simp [asymptoticOperator_def]

/-- The asymptotic operator commutes with real scaling. -/
@[simp]
theorem asymptoticOperator_smul (c : ℝ) :
    asymptoticOperator J S (c • ζ) = c • asymptoticOperator J S ζ := by
  funext t
  simp only [asymptoticOperator_def, deriv_const_smul_field, Pi.smul_apply, map_sub, map_smul,
    smul_sub]

/-- The asymptotic operator is additive on loops differentiable at the point. -/
theorem asymptoticOperator_add (hζ : DifferentiableAt ℝ ζ t) (hη : DifferentiableAt ℝ η t) :
    asymptoticOperator J S (ζ + η) t =
      asymptoticOperator J S ζ t + asymptoticOperator J S η t := by
  simp only [asymptoticOperator_def, deriv_add hζ hη, Pi.add_apply, map_add, map_sub]
  abel

/-- A loop lies in the kernel of the asymptotic operator at `t` exactly when it solves the
linearized Hamiltonian equation `ζ' = S_t ζ` there. -/
theorem asymptoticOperator_eq_zero_iff (hζ : DifferentiableAt ℝ ζ t) :
    asymptoticOperator J S ζ t = 0 ↔ HasDerivAt ζ (S t (ζ t)) t := by
  rw [asymptoticOperator_def, AlmostComplexStructure.map_eq_zero_iff, sub_eq_zero]
  exact ⟨fun h ↦ h ▸ hζ.hasDerivAt, HasDerivAt.deriv⟩

/-- **The almost complex structure cancels.** For a `J_t`-invariant symplectic form, the
associated form `g_t = ω(·, J_t ·)` pairs `A ζ` with `v` as `ω(ζ' - S_t ζ, v)`. -/
theorem associatedBilinForm_asymptoticOperator {ω : SymplecticForm V}
    (hJ : ω.Invariant (J t)) (v : V) :
    ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t) v =
      ω (deriv ζ t - S t (ζ t)) v := by
  rw [SymplecticForm.associatedBilinForm_apply, asymptoticOperator_def,
    (ω.invariant_iff (J t)).mp hJ]

/-- **Symmetry of the asymptotic operator.** Let each `J_t` leave `ω` invariant and let each
`S_t` be infinitesimally symplectic, `ω(S_t v, w) + ω(v, S_t w) = 0`. Then for one-periodic
`C¹` loops `ζ` and `η` the asymptotic operator is symmetric for the `L²` pairing
`∫₀¹ ω(·, J_t ·) dt`. No regularity of `J` in `t` is needed. -/
theorem integral_associatedBilinForm_asymptoticOperator_comm [FiniteDimensional ℝ V]
    {ω : SymplecticForm V}
    (hJ : ∀ t, ω.Invariant (J t)) (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0)
    (hSc : Continuous S) (hζ : ContDiff ℝ 1 ζ) (hη : ContDiff ℝ 1 η) (hζp : Periodic ζ 1)
    (hηp : Periodic η 1) :
    ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t) (η t) =
      ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (ζ t) (asymptoticOperator J S η t) := by
  have hζ' : Continuous (deriv ζ) := hζ.continuous_deriv le_rfl
  have hη' : Continuous (deriv η) := hη.continuous_deriv le_rfl
  -- Both integrands are `J`-free after cancelling the almost complex structure.
  have hl : ∀ t, ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t) (η t) =
      ω (deriv ζ t) (η t) - ω (S t (ζ t)) (η t) := fun t ↦ by
    rw [associatedBilinForm_asymptoticOperator (hJ t)]
    simp only [map_sub, LinearMap.sub_apply]
  have hr : ∀ t, ω.associatedBilinForm (J t) (ζ t) (asymptoticOperator J S η t) =
      -ω (ζ t) (deriv η t) - ω (S t (ζ t)) (η t) := fun t ↦ by
    have h₁ := ω.neg_eq (ζ t) (deriv η t)
    have h₂ := ω.neg_eq (ζ t) (S t (η t))
    have h₃ := hS t (ζ t) (η t)
    rw [(hJ t).associatedBilinForm_isSymm.eq, associatedBilinForm_asymptoticOperator (hJ t)]
    simp only [map_sub, LinearMap.sub_apply] at h₁ h₂ h₃ ⊢
    linarith
  have hc₁ : Continuous fun t ↦ ω (S t (ζ t)) (η t) :=
    ω.continuous_apply_comp (hSc.clm_apply hζ.continuous) hη.continuous
  have hc₂ : Continuous fun t ↦ ω (deriv ζ t) (η t) := ω.continuous_apply_comp hζ' hη.continuous
  have hc₃ : Continuous fun t ↦ ω (ζ t) (deriv η t) := ω.continuous_apply_comp hζ.continuous hη'
  have hL : ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t) (η t) =
      (∫ t in (0 : ℝ)..1, ω (deriv ζ t) (η t)) - ∫ t in (0 : ℝ)..1, ω (S t (ζ t)) (η t) := by
    rw [intervalIntegral.integral_congr (fun t _ ↦ hl t)]
    exact intervalIntegral.integral_sub (hc₂.intervalIntegrable _ _) (hc₁.intervalIntegrable _ _)
  have hR : ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (ζ t) (asymptoticOperator J S η t) =
      -(∫ t in (0 : ℝ)..1, ω (ζ t) (deriv η t)) - ∫ t in (0 : ℝ)..1, ω (S t (ζ t)) (η t) := by
    rw [intervalIntegral.integral_congr (fun t _ ↦ hr t), ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_sub (hc₃.neg.intervalIntegrable _ _)
      (hc₁.intervalIntegrable _ _)
  -- The remaining integrand is the derivative of the periodic function `ω(ζ, η)`.
  have hd : ∀ t, HasDerivAt (fun t ↦ ω (ζ t) (η t))
      (ω (deriv ζ t) (η t) + ω (ζ t) (deriv η t)) t := fun t ↦
    ω.hasDerivAt_apply_comp (hζ.differentiable one_ne_zero t).hasDerivAt
      (hη.differentiable one_ne_zero t).hasDerivAt
  have hI : (∫ t in (0 : ℝ)..1, ω (deriv ζ t) (η t)) +
      ∫ t in (0 : ℝ)..1, ω (ζ t) (deriv η t) = 0 := by
    rw [← intervalIntegral.integral_add (hc₂.intervalIntegrable _ _) (hc₃.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
        ((hc₂.add hc₃).intervalIntegrable _ _)]
    simp [show ζ 1 = ζ 0 by simpa using hζp 0, show η 1 = η 0 by simpa using hηp 0]
  linarith

section Kernel

variable [CompleteSpace V]

/-- **The kernel is given by the propagator.** A differentiable loop in the kernel of the
asymptotic operator is `ζ(t) = Ψ(t) ζ(0)`, where `Ψ = dysonSeriesLeft S` is the propagator of
the linearized Hamiltonian equation `ζ' = S_t ζ`. -/
theorem apply_eq_dysonSeriesLeft_apply_of_asymptoticOperator_eq_zero (hSc : Continuous S)
    (hζ : Differentiable ℝ ζ) (h : ∀ t, asymptoticOperator J S ζ t = 0) (t : ℝ) :
    ζ t = dysonSeriesLeft S t (ζ 0) :=
  eq_dysonSeriesLeft_apply hSc (fun t ↦ (asymptoticOperator_eq_zero_iff (hζ t)).mp (h t)) t

/-- The propagator applied to a vector lies in the kernel of the asymptotic operator. -/
theorem asymptoticOperator_dysonSeriesLeft_apply_eq_zero (hSc : Continuous S) (v : V) (t : ℝ) :
    asymptoticOperator J S (fun t ↦ dysonSeriesLeft S t v) t = 0 :=
  (asymptoticOperator_eq_zero_iff (hasDerivAt_dysonSeriesLeft_apply hSc v t).differentiableAt).mpr
    (hasDerivAt_dysonSeriesLeft_apply hSc v t)

end Kernel

/-- **The kernel of the asymptotic operator and the return map.** For a continuous one-periodic
family `S`, the asymptotic operator has a nonzero differentiable one-periodic kernel element
exactly when the return map `Ψ(1)` of the linearized Hamiltonian equation `ζ' = S_t ζ` fixes a
nonzero vector. -/
theorem exists_ne_zero_asymptoticOperator_eq_zero_iff_exists_ne_zero_dysonSeriesLeft_apply_eq_self
    [CompleteSpace V] (hSc : Continuous S) (hSp : Periodic S 1) :
    (∃ ζ : ℝ → V, Differentiable ℝ ζ ∧ Periodic ζ 1 ∧ ζ ≠ 0 ∧
      ∀ t, asymptoticOperator J S ζ t = 0) ↔
      ∃ v ≠ 0, dysonSeriesLeft S 1 v = v := by
  constructor
  · rintro ⟨ζ, hζ, hζp, hne, h⟩
    have heq := apply_eq_dysonSeriesLeft_apply_of_asymptoticOperator_eq_zero hSc hζ h
    refine ⟨ζ 0, fun h0 ↦ hne (funext fun t ↦ by rw [heq, h0, map_zero, Pi.zero_apply]), ?_⟩
    rw [← heq, ← zero_add (1 : ℝ), hζp 0]
  · rintro ⟨v, hne, hΨv⟩
    refine ⟨fun t ↦ dysonSeriesLeft S t v,
      fun t ↦ (hasDerivAt_dysonSeriesLeft_apply hSc v t).differentiableAt, fun t ↦ ?_,
      fun h ↦ hne (by simpa using congrFun h 0),
      asymptoticOperator_dysonSeriesLeft_apply_eq_zero hSc v⟩
    dsimp only
    rw [dysonSeriesLeft_add_of_periodic hSc hSp t, mul_apply_eq_comp, hΨv]

/-- **Nondegeneracy and the kernel of the asymptotic operator.** For a continuous one-periodic
family `S`, the asymptotic operator has a nonzero differentiable one-periodic kernel element
exactly when `1` is an eigenvalue of the return map `Ψ(1)` of the linearized Hamiltonian
equation `ζ' = S_t ζ`, that is, when `det (1 - Ψ(1)) = 0`. -/
theorem exists_ne_zero_asymptoticOperator_eq_zero_iff_det_eq_zero [FiniteDimensional ℝ V]
    (hSc : Continuous S) (hSp : Periodic S 1) :
    (∃ ζ : ℝ → V, Differentiable ℝ ζ ∧ Periodic ζ 1 ∧ ζ ≠ 0 ∧
      ∀ t, asymptoticOperator J S ζ t = 0) ↔
      LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) = 0 := by
  rw [exists_ne_zero_asymptoticOperator_eq_zero_iff_exists_ne_zero_dysonSeriesLeft_apply_eq_self
      hSc hSp, LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self,
    sub_eq_zero]
  exact ⟨fun ⟨v, h0, hv⟩ ↦ ⟨v, hv.symm, h0⟩, fun ⟨v, hv, h0⟩ ↦ ⟨v, h0, hv.symm⟩⟩

section Weight

/-! ### Weighted operators

Floer operators on cylindrical ends act on maps decaying like `e^{-δ s}`. Conjugating by the
weight shifts the asymptotic operator `A` to `A - δ`, and `A - δ` is again an asymptotic
operator, for the linearized field `S_t - δ J_t`. -/

variable [FiniteDimensional ℝ V]

/-- **Shifting the asymptotic operator by a weight.** Replacing `S_t` by `S_t - δ J_t` shifts the
asymptotic operator by `-δ`. -/
theorem asymptoticOperator_sub_smul (δ : ℝ) (ζ : ℝ → V) (t : ℝ) :
    asymptoticOperator J
        (fun t ↦ S t - δ • LinearMap.toContinuousLinearMap (J t).toLinearMap) ζ t =
      asymptoticOperator J S ζ t - δ • ζ t := by
  have h : J t (J t (ζ t)) = -ζ t := AlmostComplexStructure.apply_apply _ _
  simp only [asymptoticOperator_def, sub_apply, smul_apply, LinearMap.coe_toContinuousLinearMap',
    sub_sub_eq_add_sub, map_add, map_sub, map_smul] at h ⊢
  rw [h]
  module

/-- **The periodic spectrum of the asymptotic operator is closed.** For continuous one-periodic
families `S` and `J`, the real weights `δ` for which `A ζ = δ ζ` has a nonzero differentiable
one-periodic solution form a closed set: the zero set of `δ ↦ det (1 - Ψ_δ(1))`, where `Ψ_δ`
is the propagator of `ζ' = (S_t - δ J_t) ζ`. -/
theorem isClosed_setOf_exists_asymptoticOperator_eq_smul (hSc : Continuous S)
    (hSp : Periodic S 1) (hJc : Continuous J) (hJp : Periodic J 1) :
    IsClosed {δ : ℝ | ∃ ζ : ℝ → V, Differentiable ℝ ζ ∧ Periodic ζ 1 ∧ ζ ≠ 0 ∧
      ∀ t, asymptoticOperator J S ζ t = δ • ζ t} := by
  set Jc : ℝ → V →L[ℝ] V := fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap
  have hJc' : Continuous Jc := AlmostComplexStructure.continuous_iff.1 hJc
  have hp : Continuous (Function.uncurry fun (δ : ℝ) t ↦ S t - δ • Jc t) :=
    (hSc.comp continuous_snd).sub (continuous_fst.smul (hJc'.comp continuous_snd))
  have hset : {δ : ℝ | ∃ ζ : ℝ → V, Differentiable ℝ ζ ∧ Periodic ζ 1 ∧ ζ ≠ 0 ∧
      ∀ t, asymptoticOperator J S ζ t = δ • ζ t} =
      (fun δ ↦ LinearMap.det
        ((1 - dysonSeriesLeft (fun t ↦ S t - δ • Jc t) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V)) ⁻¹' {0} := by
    ext δ
    refine Iff.trans ?_ (exists_ne_zero_asymptoticOperator_eq_zero_iff_det_eq_zero (J := J)
      (S := fun t ↦ S t - δ • Jc t) (hSc.sub (hJc'.const_smul δ))
      fun t ↦ by simp only [Jc, hSp t, hJp t])
    simp only [Jc, asymptoticOperator_sub_smul, sub_eq_zero]
    exact Iff.rfl
  rw [hset]
  exact isClosed_singleton.preimage <| ContinuousLinearMap.continuous_det.comp <|
    continuous_const.sub <| (continuous_parametric_dysonSeriesLeft hp).comp <|
      continuous_id.prodMk continuous_const

end Weight

section Cylinder

variable {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}

/-- The translation-invariant operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` on maps of the cylinder
`ℝ × ℝ`, with `s` the first and `t` the second coordinate. It is the linearized Floer operator at
the stationary cylinder over a Hamiltonian orbit, and on each slice `s = const` it is `∂s + A`
for the asymptotic operator `A`. -/
noncomputable def stationaryCylinderOperator (J : ℝ → AlmostComplexStructure V)
    (S : ℝ → V →L[ℝ] V) (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ ξ z stdComplexLineReal + J z.2 (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))

/-- The defining formula of the stationary cylinder operator. -/
theorem stationaryCylinderOperator_def (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    stationaryCylinderOperator J S ξ z =
      fderiv ℝ ξ z stdComplexLineReal + J z.2 (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)) :=
  (rfl)

/-- The stationary cylinder operator vanishes on the zero map. -/
@[simp]
theorem stationaryCylinderOperator_zero : stationaryCylinderOperator J S 0 = 0 := by
  funext z
  simp [stationaryCylinderOperator_def]

/-- The stationary cylinder operator commutes with real scaling. -/
@[simp]
theorem stationaryCylinderOperator_smul (c : ℝ) :
    stationaryCylinderOperator J S (c • ξ) = c • stationaryCylinderOperator J S ξ := by
  funext z
  simp only [stationaryCylinderOperator_def, fderiv_const_smul_field, Pi.smul_apply, smul_apply,
    map_sub, map_smul, smul_sub, smul_add]

/-- The stationary cylinder operator is additive on maps differentiable at the point. -/
theorem stationaryCylinderOperator_add {η : ℝ × ℝ → V} (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderOperator J S (ξ + η) z =
      stationaryCylinderOperator J S ξ z + stationaryCylinderOperator J S η z := by
  simp only [stationaryCylinderOperator_def, fderiv_add hξ hη, Pi.add_apply, add_apply, map_add,
    map_sub]
  abel

/-- On a map differentiable at `z`, the stationary cylinder operator is `∂s` plus the asymptotic
operator applied to the loop `t ↦ ξ(s, t)`. -/
theorem stationaryCylinderOperator_eq_add_asymptoticOperator (hξ : DifferentiableAt ℝ ξ z) :
    stationaryCylinderOperator J S ξ z =
      fderiv ℝ ξ z stdComplexLineReal + asymptoticOperator J S (fun t ↦ ξ (z.1, t)) z.2 := by
  obtain ⟨s, t⟩ := z
  have hξt : deriv (fun t ↦ ξ (s, t)) t = fderiv ℝ ξ (s, t) stdComplexLineImag := by
    rw [stdComplexLineImag_eq]
    exact (hξ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_prodMk_right s t)).deriv
  rw [stationaryCylinderOperator_def, asymptoticOperator_def, hξt]

/-- A map of period one in the second coordinate has a derivative of period one in it. -/
private theorem fderiv_add_one_snd (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (s t : ℝ) :
    fderiv ℝ ξ (s, t + 1) = fderiv ℝ ξ (s, t) := by
  have hp : Periodic ξ ((0 : ℝ), (1 : ℝ)) := fun ⟨p, q⟩ ↦ by simpa using hper p q
  simpa using hp.fderiv (s, t)

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V}

/-- **The weighted end operator.** Conjugating the stationary cylinder operator by the weight
`e^{δ s}` shifts it by `-δ`: `D(e^{-δ s} ξ) = e^{-δ s} (D - δ) ξ`, where `D - δ` is the stationary
cylinder operator of `S_t - δ J_t`. Hence `D` on maps of the form `e^{-δ s} ξ` is the operator
`∂s + A - δ` on `ξ`. -/
theorem stationaryCylinderOperator_exp_smul (δ : ℝ) (hξ : DifferentiableAt ℝ ξ z) :
    stationaryCylinderOperator J S (fun w ↦ Real.exp (-(δ * w.1)) • ξ w) z =
      Real.exp (-(δ * z.1)) • stationaryCylinderOperator J
        (fun t ↦ S t - δ • LinearMap.toContinuousLinearMap (J t).toLinearMap) ξ z := by
  have hc : HasFDerivAt (fun w : ℝ × ℝ ↦ Real.exp (-(δ * w.1)))
      (Real.exp (-(δ * z.1)) • -(δ • ContinuousLinearMap.fst ℝ ℝ ℝ)) z := by
    simpa using ((hasFDerivAt_fst (p := z)).const_smul δ).neg.exp
  have h : J z.2 (J z.2 (ξ z)) = -ξ z := AlmostComplexStructure.apply_apply _ _
  have hd : HasFDerivAt (fun w ↦ Real.exp (-(δ * w.1)) • ξ w) _ z := hc.smul hξ.hasFDerivAt
  rw [stationaryCylinderOperator_def, hd.fderiv, stationaryCylinderOperator_def]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, neg_apply,
    ContinuousLinearMap.coe_fst', stdComplexLineReal_fst, stdComplexLineImag_fst,
    sub_apply, LinearMap.coe_toContinuousLinearMap', map_add, map_sub,
    map_smul, sub_sub_eq_add_sub, smul_eq_mul, mul_zero, mul_one, neg_zero, zero_smul,
    add_zero] at h ⊢
  rw [h]
  module

/-- For continuously varying `J_t`, the norm `g_t(f, f)` of a continuous map `f` of the cylinder
for `g_t = ω(·, J_t ·)` is continuous. -/
private theorem continuous_associatedBilinForm_apply_self
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) {f : ℝ × ℝ → V} (hf : Continuous f) :
    Continuous fun z ↦ ω.associatedBilinForm (J z.2) (f z) (f z) :=
  ω.continuous_apply_comp hf (hJc.comp (continuous_snd.prodMk hf))

/-- For continuously varying `J_t` and `S_t` and a `C¹` map `ξ`, the energy density
`g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ)` of the cylinder is continuous, where
`g_t = ω(·, J_t ·)`. -/
private theorem continuous_associatedBilinForm_add_apply_self
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S) (hξ : ContDiff ℝ 1 ξ) :
    Continuous fun z : ℝ × ℝ ↦
      ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
          (fderiv ℝ ξ z stdComplexLineReal) +
        ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
          (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)) := by
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv one_ne_zero
  have hw : Continuous fun z : ℝ × ℝ ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z) :=
    (hdξ.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply hξ.continuous)
  have hs : Continuous fun z : ℝ × ℝ ↦ fderiv ℝ ξ z stdComplexLineReal :=
    hdξ.clm_apply continuous_const
  exact (continuous_associatedBilinForm_apply_self hJc hs).add
    (continuous_associatedBilinForm_apply_self hJc hw)

omit [FiniteDimensional ℝ V] in
/-- The pointwise form of the energy identity: for `ω`-invariant `J` and infinitesimally
symplectic `T`, with `w = y - T x`, the norm `g(u + J w, u + J w)` for `g = ω(·, J ·)` is
`g(u, u) + g(w, w)` plus twice `ω(w, u)`, written as the sum of the two partial derivatives
`ω(w, u) + ω(m - T u, x)` and `ω(x, m) + ω(y, u)` used in the cylinder computation. -/
private theorem associatedBilinForm_add_apply_self {J : AlmostComplexStructure V}
    {T : V →L[ℝ] V} (hJ : ω.Invariant J) (hT : ∀ v w, ω (T v) w + ω v (T w) = 0)
    (x y u m : V) :
    ω.associatedBilinForm J (u + J (y - T x)) (u + J (y - T x)) =
      (ω.associatedBilinForm J u u + ω.associatedBilinForm J (y - T x) (y - T x)) +
        ((ω (y - T x) u + ω (m - T u) x) + (ω x m + ω y u)) := by
  have hinv := (ω.invariant_iff J).mp hJ
  have h₁ := hinv (y - T x) u
  have h₂ := hinv (y - T x) (J (y - T x))
  have h₃ := ω.neg_eq u (y - T x)
  have h₄ := ω.neg_eq x m
  have h₅ := ω.neg_eq u (T x)
  have h₆ := hT u x
  simp only [SymplecticForm.associatedBilinForm_apply, AlmostComplexStructure.apply_apply,
    map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply] at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  linarith

/-- The `s`-derivative of the slice pairing integrand `ω(∂t ξ - S_t ξ, ξ)`. -/
private theorem hasDerivAt_slicePairing_fst (hξ : ContDiff ℝ 2 ξ) (s t : ℝ) :
    HasDerivAt (fun s ↦ ω (fderiv ℝ ξ (s, t) (0, 1) - S t (ξ (s, t))) (ξ (s, t)))
      (ω (fderiv ℝ ξ (s, t) (0, 1) - S t (ξ (s, t))) (fderiv ℝ ξ (s, t) (1, 0)) +
        ω (fderiv ℝ (fderiv ℝ ξ) (s, t) (1, 0) (0, 1) - S t (fderiv ℝ ξ (s, t) (1, 0)))
          (ξ (s, t))) s := by
  have hus : HasDerivAt (fun s ↦ ξ (s, t)) (fderiv ℝ ξ (s, t) (1, 0)) s :=
    (hξ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_prodMk_left s t)
  have hws : HasDerivAt (fun s ↦ fderiv ℝ ξ (s, t) (0, 1) - S t (ξ (s, t)))
      (fderiv ℝ (fderiv ℝ ξ) (s, t) (1, 0) (0, 1) - S t (fderiv ℝ ξ (s, t) (1, 0))) s :=
    (hasDerivAt_fderiv_apply_fst
    ((hξ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero (s, t)) (0, 1)).sub
      ((S t).hasFDerivAt.comp_hasDerivAt s hus)
  simpa only [add_comm] using ω.hasDerivAt_apply_comp hws hus

/-- The `t`-derivative of `ω(ξ, ∂s ξ)`, using the symmetry of the second derivative. -/
private theorem hasDerivAt_apply_fderiv_fst_snd (hξ : ContDiff ℝ 2 ξ) (s t : ℝ) :
    HasDerivAt (fun t ↦ ω (ξ (s, t)) (fderiv ℝ ξ (s, t) (1, 0)))
      (ω (ξ (s, t)) (fderiv ℝ (fderiv ℝ ξ) (s, t) (1, 0) (0, 1)) +
        ω (fderiv ℝ ξ (s, t) (0, 1)) (fderiv ℝ ξ (s, t) (1, 0))) t := by
  have hut : HasDerivAt (fun t ↦ ξ (s, t)) (fderiv ℝ ξ (s, t) (0, 1)) t :=
    (hξ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_prodMk_right s t)
  have hsym : fderiv ℝ (fderiv ℝ ξ) (s, t) (0, 1) (1, 0) =
      fderiv ℝ (fderiv ℝ ξ) (s, t) (1, 0) (0, 1) :=
    (hξ.contDiffAt.isSymmSndFDerivAt (by simp) (1, 0) (0, 1)).symm
  simpa only [hsym, add_comm] using ω.hasDerivAt_apply_comp hut
    (hasDerivAt_fderiv_apply_snd
      ((hξ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero (s, t)) (1, 0))

/-- The `t`-derivative `∂t ω(ξ, ∂s ξ)` of a map of period one in `t` integrates to zero over
`[a, b] × [0, 1]`. -/
private theorem setIntegral_rect_apply_fderiv_fst_snd_eq_zero (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ}
    (hφ : Continuous fun z : ℝ × ℝ ↦
      ω (ξ z) (fderiv ℝ (fderiv ℝ ξ) z (1, 0) (0, 1)) +
        ω (fderiv ℝ ξ z (0, 1)) (fderiv ℝ ξ z (1, 0))) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
      (ω (ξ z) (fderiv ℝ (fderiv ℝ ξ) z (1, 0) (0, 1)) +
        ω (fderiv ℝ ξ z (0, 1)) (fderiv ℝ ξ z (1, 0))) = 0 := by
  have hχp (s : ℝ) : ω (ξ (s, 1)) (fderiv ℝ ξ (s, 1) (1, 0)) =
      ω (ξ (s, 0)) (fderiv ℝ ξ (s, 0) (1, 0)) := by
    have h1 := fderiv_add_one_snd hper s 0
    rw [zero_add] at h1
    have hξ1 : ξ (s, 1) = ξ (s, 0) := by simpa using hper s 0
    simp only [h1, hξ1]
  exact setIntegral_rect_eq_zero_of_hasDerivAt_snd hφ
    (Φ := fun z ↦ ω (ξ z) (fderiv ℝ ξ z (1, 0))) (hasDerivAt_apply_fderiv_fst_snd hξ) hχp

/-- **The energy identity of the stationary cylinder operator.** Let each `J_t` leave `ω`
invariant, depend continuously on `t`, and let each `S_t` be infinitesimally symplectic. For a
`C²` map `ξ` of period one in `t` and `a ≤ b`, the `L²` norm of `D ξ` over `[a, b] × [0, 1]`
for `g_t = ω(·, J_t ·)` splits as

`∫ g(D ξ, D ξ) = ∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ)) + Φ(b) - Φ(a)`,

where `Φ(s) = ∫₀¹ ω(∂t ξ - S_t ξ, ξ) dt` is the pairing of the slice at `s` with its image under
the asymptotic operator. This is the integrated form of `D* D = -∂s² + A²`; only the boundary
slices contribute to the cross term. -/
theorem setIntegral_associatedBilinForm_stationaryCylinderOperator
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ} (hab : a ≤ b) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
        (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z) =
      (∫ z in Icc a b ×ˢ Icc 0 1,
        (ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
            (fderiv ℝ ξ z stdComplexLineReal) +
          ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
            (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)))) +
        ((∫ t in (0 : ℝ)..1,
            ω (fderiv ℝ ξ (b, t) stdComplexLineImag - S t (ξ (b, t))) (ξ (b, t))) -
          ∫ t in (0 : ℝ)..1,
            ω (fderiv ℝ ξ (a, t) stdComplexLineImag - S t (ξ (a, t))) (ξ (a, t))) := by
  simp only [stationaryCylinderOperator_def, stdComplexLineReal_eq, stdComplexLineImag_eq]
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv (by norm_num)
  have hddξ : Continuous (fderiv ℝ (fderiv ℝ ξ)) :=
    (hξ.fderiv_right (m := 1) le_rfl).continuous_fderiv one_ne_zero
  have hS' {f : ℝ × ℝ → V} (hf : Continuous f) : Continuous fun z ↦ S z.2 (f z) :=
    (hSc.comp continuous_snd).clm_apply hf
  -- Partial derivatives of `ξ` and the remainder `w = ∂t ξ - S ξ`.
  set ξs : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z (1, 0)
  set ξt : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z (0, 1)
  set w : ℝ × ℝ → V := fun z ↦ ξt z - S z.2 (ξ z)
  set M : ℝ × ℝ → V := fun z ↦ fderiv ℝ (fderiv ℝ ξ) z (1, 0) (0, 1)
  have hξs : Continuous ξs := hdξ.clm_apply continuous_const
  have hξt : Continuous ξt := hdξ.clm_apply continuous_const
  have hw : Continuous w := hξt.sub (hS' hξ.continuous)
  have hM : Continuous M := (hddξ.clm_apply continuous_const).clm_apply continuous_const
  -- The cross term `2 ω(w, ∂s ξ)` is `∂s ψ + ∂t χ` with `ψ = ω(w, ξ)` and `χ = ω(ξ, ∂s ξ)`.
  set φ₁ : ℝ × ℝ → ℝ := fun z ↦ ω (w z) (ξs z) + ω (M z - S z.2 (ξs z)) (ξ z)
  set φ₂ : ℝ × ℝ → ℝ := fun z ↦ ω (ξ z) (M z) + ω (ξt z) (ξs z)
  have hφ₁ : Continuous φ₁ :=
    (ω.continuous_apply_comp hw hξs).add (ω.continuous_apply_comp (hM.sub (hS' hξs)) hξ.continuous)
  have hφ₂ : Continuous φ₂ :=
    (ω.continuous_apply_comp hξ.continuous hM).add (ω.continuous_apply_comp hξt hξs)
  have hR : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hc₁ : Continuous fun z : ℝ × ℝ ↦ ω.associatedBilinForm (J z.2) (ξs z) (ξs z) +
      ω.associatedBilinForm (J z.2) (w z) (w z) :=
    continuous_associatedBilinForm_add_apply_self hJc hSc (hξ.of_le (by norm_num))
  have hc₂ : Continuous fun z ↦ φ₁ z + φ₂ z := hφ₁.add hφ₂
  have hψc (s : ℝ) : Continuous fun t ↦ ω (w (s, t)) (ξ (s, t)) :=
    (ω.continuous_apply_comp hw hξ.continuous).comp (Continuous.prodMk_right s)
  have hpt : ∀ z : ℝ × ℝ, ω.associatedBilinForm (J z.2) (ξs z + J z.2 (w z))
      (ξs z + J z.2 (w z)) =
      (ω.associatedBilinForm (J z.2) (ξs z) (ξs z) +
        ω.associatedBilinForm (J z.2) (w z) (w z)) + (φ₁ z + φ₂ z) := fun z ↦
    associatedBilinForm_add_apply_self (hJ z.2) (hS z.2) (ξ z) (ξt z) (ξs z) (M z)
  -- `χ` has period one in `t`, so `∂t χ` integrates to zero.
  have h₂ : ∫ z in Icc a b ×ˢ Icc 0 1, φ₂ z = 0 :=
    setIntegral_rect_apply_fderiv_fst_snd_eq_zero hξ hper hφ₂
  -- `∂s ψ` integrates to the difference of the boundary slice pairings.
  have h₁ : ∫ z in Icc a b ×ˢ Icc 0 1, φ₁ z =
      (∫ t in (0 : ℝ)..1, ω (w (b, t)) (ξ (b, t))) -
        ∫ t in (0 : ℝ)..1, ω (w (a, t)) (ξ (a, t)) := by
    rw [setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_fst (Φ := fun z ↦ ω (w z) (ξ z)) hφ₁
        (hasDerivAt_slicePairing_fst hξ) hab,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_sub ((hψc b).intervalIntegrable _ _)
      ((hψc a).intervalIntegrable _ _)
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (hc₁.continuousOn.integrableOn_compact hR)
      (hc₂.continuousOn.integrableOn_compact hR),
    integral_add (hφ₁.continuousOn.integrableOn_compact hR)
      (hφ₂.continuousOn.integrableOn_compact hR), h₁, h₂, add_zero]

/-- The slice pairing `s ↦ ∫₀¹ ω(∂t ξ - S_t ξ, ξ) dt` tends to zero as `|s| → ∞` when `ξ` and
`∂t ξ` do, uniformly in `t`. -/
private theorem tendsto_integral_slicePairing (hSc : Continuous S)
    (hdecay : Tendsto (fun z ↦ (ξ z, fderiv ℝ ξ z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0)) :
    Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1,
      ω (fderiv ℝ ξ (s, t) stdComplexLineImag - S t (ξ (s, t))) (ξ (s, t))) (cocompact ℝ)
        (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hSc.continuousOn (s := Icc (0 : ℝ) 1))
  set F := comap Prod.fst (cocompact ℝ) ⊓ 𝓟 (univ ×ˢ Icc (0 : ℝ) 1)
  have hξ0 : Tendsto ξ F (𝓝 0) :=
    ((continuous_fst.tendsto (0 : V × V)).comp hdecay).mono_left inf_le_left
  have hξt0 : Tendsto (fun z ↦ fderiv ℝ ξ z stdComplexLineImag) F (𝓝 0) :=
    ((continuous_snd.tendsto (0 : V × V)).comp hdecay).mono_left inf_le_left
  have hS0 : Tendsto (fun z : ℝ × ℝ ↦ S z.2 (ξ z)) F (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun z ↦ C * ‖ξ z‖) ?_ (by simpa using hξ0.norm.const_mul C)
    exact eventually_inf_principal.2 (Eventually.of_forall fun z hz ↦
      ((S z.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC z.2 hz.2) (norm_nonneg _)))
  have hψ0 : Tendsto (fun z : ℝ × ℝ ↦
      ω (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)) (ξ z)) F (𝓝 0) := by
    have hw0 : Tendsto (fun z : ℝ × ℝ ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)) F
        (𝓝 0) := by simpa using hξt0.sub hS0
    simpa only [Function.comp_def, map_zero, LinearMap.zero_apply] using
      ((ω.continuous_apply_comp continuous_fst continuous_snd).tendsto (0, 0)).comp
        (hw0.prodMk_nhds hξ0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := Metric.tendsto_nhds.1 hψ0 (ε / 2) (by positivity)
  rw [eventually_inf_principal, eventually_comap] at h
  filter_upwards [h] with s hs
  rw [dist_zero_right]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2) fun t ht ↦ ?_).trans_lt
    (by norm_num; linarith)
  rw [uIoc_of_le zero_le_one] at ht
  simpa [dist_zero_right] using (hs (s, t) rfl ⟨mem_univ _, Ioc_subset_Icc_self ht⟩).le

/-- **Decaying solutions of the stationary cylinder equation vanish.** Let each `J_t` be
`ω`-compatible and depend continuously on `t`, and let each `S_t` be infinitesimally
symplectic. A `C²` solution `ξ` of `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ) = 0` of period one in `t`,
which tends to zero together with `∂t ξ` as `|s| → ∞`, uniformly in `t`, is identically zero.
No nondegeneracy of the orbit is needed for this injectivity statement. -/
theorem eq_zero_of_stationaryCylinderOperator_eq_zero (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hD : ∀ z, stationaryCylinderOperator J S ξ z = 0)
    (hdecay : Tendsto (fun z ↦ (ξ z, fderiv ℝ ξ z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0)) :
    ξ = 0 := by
  have hξ1 : Differentiable ℝ ξ := hξ.differentiable (by norm_num)
  have hg0 (t : ℝ) (v : V) : 0 ≤ ω v (J t v) := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((hJ t).associated_pos hv).le
  set Φ : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..1,
    ω (fderiv ℝ ξ (s, t) stdComplexLineImag - S t (ξ (s, t))) (ξ (s, t))
  set f : ℝ × ℝ → ℝ := fun z ↦
    ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
        (fderiv ℝ ξ z stdComplexLineReal) +
      ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
        (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
  have hf0 : 0 ≤ f := fun z ↦ add_nonneg (hg0 _ _) (hg0 _ _)
  have hfc : Continuous f :=
    continuous_associatedBilinForm_add_apply_self hJc hSc (hξ.of_le (by norm_num))
  -- The energy identity with `D ξ = 0`.
  have hid {a b : ℝ} (hab : a ≤ b) : ∫ z in Icc a b ×ˢ Icc 0 1, f z = Φ a - Φ b := by
    have h := setIntegral_associatedBilinForm_stationaryCylinderOperator
      (fun t ↦ (hJ t).invariant) hJc hS hSc hξ hper hab
    simp only [hD, map_zero, integral_zero] at h
    simp only [f, Φ]
    linarith
  have hanti {a b : ℝ} (hab : a ≤ b) : Φ b ≤ Φ a := by
    have h := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
      (fun z (_ : z ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) ↦ hf0 z)
    rw [hid hab] at h
    linarith
  -- The slice pairing `Φ` is nonincreasing by the energy identity and tends to zero at both
  -- ends, so it vanishes; then the energy identity forces `∂s ξ = 0`.
  have hlim : Tendsto Φ (cocompact ℝ) (𝓝 0) := tendsto_integral_slicePairing hSc hdecay
  have hΦ (s : ℝ) : Φ s = 0 := le_antisymm
    (ge_of_tendsto (hlim.mono_left atBot_le_cocompact)
      ((eventually_le_atBot s).mono fun _ ha ↦ hanti ha))
    (le_of_tendsto (hlim.mono_left atTop_le_cocompact)
      ((eventually_ge_atTop s).mono fun _ hb ↦ hanti hb))
  -- Hence `∂s ξ` vanishes on every slice `[0, 1]`, and by periodicity everywhere.
  have hs0 (s t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : fderiv ℝ ξ (s, t) stdComplexLineReal = 0 := by
    have hz := eqOn_zero_of_setIntegral_rect_eq_zero (show s - 1 < s + 1 by linarith)
      zero_lt_one hfc hf0 (by rw [hid (by linarith), hΦ, hΦ, sub_self])
      (show (s, t) ∈ Icc (s - 1) (s + 1) ×ˢ Icc 0 1 from ⟨⟨by linarith, by linarith⟩, ht⟩)
    by_contra hne
    have h₁ := (hJ t).associated_pos hne
    have h₂ := hg0 t (fderiv ℝ ξ (s, t) stdComplexLineImag - S t (ξ (s, t)))
    simp only [f, Pi.zero_apply, SymplecticForm.associatedBilinForm_apply] at hz
    linarith
  have hs (z : ℝ × ℝ) : fderiv ℝ ξ z (1, 0) = 0 := by
    obtain ⟨s, t⟩ := z
    have hp : Periodic (fun t ↦ fderiv ℝ ξ (s, t) (1, 0)) 1 := fun t ↦ by
      simp only [fderiv_add_one_snd hper]
    obtain ⟨t₀, ht₀, h⟩ := hp.exists_mem_Ico₀ one_pos t
    simpa [h, stdComplexLineReal_eq] using hs0 s t₀ (Ico_subset_Icc_self ht₀)
  -- A map independent of `s` which decays as `s → ∞` vanishes.
  exact eq_zero_of_fderiv_fst_eq_zero_of_tendsto hξ1 hs
    ((continuous_fst.tendsto (0 : V × V)).comp hdecay)

end Cylinder

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The linearization at a stationary cylinder.** Let `x` be an orbit of the time-dependent
Hamiltonian `H`, `x' = X_{H_t}(x)`, and let `u(s, t) = x(t)` be the stationary cylinder over it,
a solution of the Floer equation for `K = H_t dt`. For an almost complex structure `J_t(y)`
depending on time and the target point, the linearized Floer operator at `u` is the stationary
cylinder operator `∂s + J_t(x(t)) (∂t - S_t)` with `S_t = dX_{H_t}(x(t))`; the target derivative
of `J` does not contribute. -/
theorem floerLinearization_eq_stationaryCylinderOperator (ω : SymplecticForm V)
    (J : ℝ → V → AlmostComplexStructure V) (H : ℝ → V → ℝ) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (ξ : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) ξ z =
      Floer.stationaryCylinderOperator (fun t ↦ J t (x t))
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z := by
  obtain ⟨s, t⟩ := z
  have hxt : fderiv ℝ (fun w : ℝ × ℝ ↦ x w.2) (s, t) stdComplexLineImag =
      ω.hamiltonianVectorField (H t) (x t) := by
    have h : HasFDerivAt (fun w : ℝ × ℝ ↦ x w.2) _ (s, t) :=
      (hx t).hasFDerivAt.comp (s, t) (hasFDerivAt_snd (p := (s, t)))
    rw [h.fderiv]
    simp [stdComplexLineImag_eq]
  rw [floerLinearization_def, Floer.stationaryCylinderOperator_def, hxt, sub_self, map_zero,
    hamiltonianVectorField_const]
  simp

/-- **Nondegenerate orbits are those whose asymptotic operator has no periodic kernel.** Let `x`
be a one-periodic orbit of a one-periodic, jointly `C²` time-dependent Hamiltonian `H` whose
suspended vector field is globally Lipschitz, and let `J_t` be any family of almost complex
structures. Then `x(0)` is a nondegenerate fixed point of the time-one map of `H` exactly when the
asymptotic operator `A ζ = J_t (ζ' - S_t ζ)` along `x`, with `S_t = dX_{H_t}(x(t))`, has no
nonzero differentiable one-periodic kernel element. -/
theorem isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (J : ℝ → AlmostComplexStructure V) :
    IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) ↔
      ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
        (∀ t, Floer.asymptoticOperator J
          (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ζ t = 0) → ζ = 0 := by
  set S := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)
  have hSc : Continuous S := ω.continuous_fderiv_hamiltonianVectorField_comp hH
    (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt)
  have hSp : Periodic S 1 := fun t ↦ by simp only [S, hHp t, hxp t]
  -- The time-one map fixes `x(0)`, with derivative the return map `Ψ(1)` there.
  have hfix : IsFixedPt (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0) := by
    rw [IsFixedPt, ← ω.eq_timeDependentHamiltonianFlow H hX hx 0 1, ← zero_add (1 : ℝ), hxp 0]
  have hD :=
    (ω.differentiable_timeDependentHamiltonianFlow hX hH 0 1 (x 0)).hasFDerivAt.hasMFDerivAt
  rw [isNondegenerateFixedPt_iff, hD.mfderiv,
    ω.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft hX hH hx 0 1]
  simp only [zero_add, sub_zero, hfix, hD.mdifferentiableAt, true_and]
  -- Both sides say that there is no nonzero periodic solution of `ζ' = S_t ζ`.
  have hker :=
    Floer.exists_ne_zero_asymptoticOperator_eq_zero_iff_exists_ne_zero_dysonSeriesLeft_apply_eq_self
      (J := J) hSc hSp
  constructor
  · intro h ζ hζ hζp hA
    by_contra hne
    obtain ⟨v, hv0, hv⟩ := hker.1 ⟨ζ, hζ, hζp, hne, hA⟩
    exact hv0 (h v hv)
  · intro h v hv
    by_contra hv0
    obtain ⟨ζ, hζ, hζp, hne, hA⟩ := hker.2 ⟨v, hv0, hv⟩
    exact hne (h ζ hζ hζp hA)

/-- **Small weights preserve nondegeneracy.** At a nondegenerate one-periodic orbit `x` of a
one-periodic, jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field is globally
Lipschitz, and for continuous one-periodic almost complex structures `J_t`, the weighted
asymptotic operator `A - δ` along `x` has no nonzero differentiable one-periodic kernel element
for every weight `δ` close enough to `0`. -/
theorem eventually_eq_zero_of_asymptoticOperator_eq_smul
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → AlmostComplexStructure V} (hJc : Continuous J) (hJp : Periodic J 1) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ζ : ℝ → V, Differentiable ℝ ζ → Periodic ζ 1 →
      (∀ t, Floer.asymptoticOperator J
        (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ζ t = δ • ζ t) → ζ = 0 := by
  have hSc : Continuous fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) :=
    ω.continuous_fderiv_hamiltonianVectorField_comp hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt)
  have hSp : Periodic (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 :=
    fun t ↦ by simp only [hHp t, hxp t]
  have hclosed := Floer.isClosed_setOf_exists_asymptoticOperator_eq_smul hSc hSp hJc hJp
  have h₀ :=
    (isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero ω hX hH hHp hx hxp
      J).1 hnd
  refine Eventually.mono (hclosed.isOpen_compl.mem_nhds fun ⟨ζ, hζ, hζp, hne, hA⟩ ↦
    hne (h₀ ζ hζ hζp fun t ↦ by simpa using hA t)) fun δ hδ ζ hζ hζp hA ↦ ?_
  by_contra hne
  exact hδ ⟨ζ, hζ, hζp, hne, hA⟩

end SymplecticForm

end TauCeti
