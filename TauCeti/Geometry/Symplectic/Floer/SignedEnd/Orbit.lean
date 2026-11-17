/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Periodic
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.SignedEnd.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Dynamics.Flow.Periodic.Basic

/-!
# Orbits, actions, isolation, and linearized nondegeneracy for signed-end Hamiltonians

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a time-dependent Hamiltonian, and
`ε : ℝ` a sign satisfying `ε * ε = 1`. Reading an end of sign `ε` in positive end coordinates
replaces `H` by the signed-end Hamiltonian `H'(t, x) = ε H(ε t, x)`
(`TauCeti.Floer.signedHamiltonian`). This file establishes the symplectic dictionary between `H`
and `H'` shared across punctured surfaces (`PairOfPants.End`) and PSS planes (`Plane`):

* `X_{H'(ε t)} = ε X_{H(t)}` (`hamiltonianVectorField_signedHamiltonian_mul`), so `t ↦ x(ε t)`
  bijects orbits of `H'` with orbits of `H` (`hasDerivAt_comp_mul_of_signedHamiltonian`,
  `hasDerivAt_comp_mul_signedHamiltonian`), and scales the `1`-periodic Hamiltonian action by `ε`
  (`hamiltonianAction_signedHamiltonian`);
* uniform orbit isolation transfers between `H` and `H'` without any global Lipschitz assumption
  (`exists_pos_forall_periodic_eq_signedHamiltonian_of_isolated`), and holds in particular when
  `x(0)` is a nondegenerate fixed point of the time-one map of `H`
  (`exists_pos_forall_periodic_eq_signedHamiltonian_of_isNondegenerateFixedPt`);
* fixed vectors of the linearized return map (`TauCeti.dysonSeriesLeft`) along `t ↦ x(ε t)` for
  `H'` coincide with fixed vectors of the linearized return map along `x` for `H`
  (`dysonSeriesLeft_signedHamiltonian_apply_eq_self_iff`), again without global Lipschitz
  hypotheses;
* multiplying a derivative map by `ε` matches the derivative defect from `dt ⊗ X_{H(t)}` to `ε`
  times the defect from `dt ⊗ X_{H'(ε t)}` (`smul_sub_smulRight_hamiltonianVectorField`,
  `norm_smul_sub_smulRight_hamiltonianVectorField`).
-/

public section

open Function Set
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ω : SymplecticForm V}

/-- The action of a `1`-periodic loop for `signedHamiltonian ε H` is `ε` times the action, for `H`,
of the loop read with time `ε * t`. -/
theorem hamiltonianAction_signedHamiltonian {ε : ℝ} (hε : ε * ε = 1) {H : ℝ → V → ℝ}
    (hH : Periodic H 1) {x : ℝ → V} (hx : Periodic x 1) :
    ω.hamiltonianAction (signedHamiltonian ε H) x =
      ε * ω.hamiltonianAction H (fun t ↦ x (ε * t)) := by
  rcases eq_one_or_eq_neg_one_of_mul_self_eq_one hε with rfl | rfl
  · simp
  · have hx' : Periodic (fun t ↦ x (-t)) 1 := hx.comp_neg
    have h' := ω.hamiltonianAction_comp_neg hH hx'
    simp only [neg_neg] at h'
    simpa [signedHamiltonian_neg_one] using h'

variable [FiniteDimensional ℝ V]

/-- At the signed time `ε * t`, the Hamiltonian vector field of `signedHamiltonian ε H` is `ε`
times that of `H` at `t`. -/
theorem hamiltonianVectorField_signedHamiltonian_mul {ε : ℝ} (hε : ε * ε = 1) (H : ℝ → V → ℝ)
    (t : ℝ) :
    ω.hamiltonianVectorField (signedHamiltonian ε H (ε * t)) =
      ε • ω.hamiltonianVectorField (H t) := by
  funext y
  rw [Pi.smul_apply, ← hamiltonianVectorField_const_mul]
  congr 1
  funext x
  rw [signedHamiltonian_apply, ← mul_assoc, hε, one_mul]

/-- Reading an orbit of `signedHamiltonian ε H` with time `ε * t` gives an orbit of `H`. -/
theorem hasDerivAt_comp_mul_of_signedHamiltonian {ε : ℝ} (hε : ε * ε = 1) {H : ℝ → V → ℝ}
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (signedHamiltonian ε H t) (x t)) t)
    (t : ℝ) :
    HasDerivAt (fun t ↦ x (ε * t)) (ω.hamiltonianVectorField (H t) (x (ε * t))) t := by
  have h := (hx (ε * t)).scomp t ((hasDerivAt_id' t).const_mul ε)
  rw [hamiltonianVectorField_signedHamiltonian_mul hε, mul_one, Pi.smul_apply, smul_smul, hε,
    one_smul] at h
  exact h

/-- Reading an orbit of `H` with time `ε * t` gives an orbit of `signedHamiltonian ε H`. -/
theorem hasDerivAt_comp_mul_signedHamiltonian {ε : ℝ} (hε : ε * ε = 1) {H : ℝ → V → ℝ}
    {y : ℝ → V} (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) (t : ℝ) :
    HasDerivAt (fun t ↦ y (ε * t))
      (ω.hamiltonianVectorField (signedHamiltonian ε H t) (y (ε * t))) t :=
  hasDerivAt_comp_mul_of_signedHamiltonian hε
    (by simpa only [signedHamiltonian_signedHamiltonian hε] using hy) t

/-- Uniform isolation of `1`-periodic orbits in `B` transfers from `H` to `signedHamiltonian ε H`
under `t ↦ x (ε * t)`. -/
theorem exists_pos_forall_periodic_eq_signedHamiltonian_of_isolated {ε : ℝ} (hε : ε * ε = 1)
    {H : ℝ → V → ℝ} {B : Set V}
    (hiso : ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) → (∀ t, y t ∈ B) →
      ∃ δ > 0, ∀ z : ℝ → V, Periodic z 1 →
        (∀ t, HasDerivAt z (ω.hamiltonianVectorField (H t) (z t)) t) → (∀ t, z t ∈ B) →
        (∀ t, dist (z t) (y t) < δ) → z = y)
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (signedHamiltonian ε H t) (x t)) t)
    (hxB : ∀ t, x t ∈ B) :
    ∃ δ > 0, ∀ z : ℝ → V, Periodic z 1 →
      (∀ t, HasDerivAt z (ω.hamiltonianVectorField (signedHamiltonian ε H t) (z t)) t) →
      (∀ t, z t ∈ B) → (∀ t, dist (z t) (x t) < δ) → z = x := by
  obtain ⟨δ, hδ, h⟩ := hiso (fun t ↦ x (ε * t))
    (periodic_comp_mul_of_mul_self_eq_one hε hxper)
    (hasDerivAt_comp_mul_of_signedHamiltonian hε hx) fun t ↦ hxB (ε * t)
  refine ⟨δ, hδ, fun z hzper hz hzB hzx ↦ funext fun t ↦ ?_⟩
  have hzx' := congrFun (h (fun s ↦ z (ε * s))
    (periodic_comp_mul_of_mul_self_eq_one hε hzper)
    (hasDerivAt_comp_mul_of_signedHamiltonian hε hz) (fun s ↦ hzB (ε * s))
    fun s ↦ hzx (ε * s)) (ε * t)
  simpa only [← mul_assoc, hε, one_mul] using hzx'

/-- An orbit of `signedHamiltonian ε H` whose initial point `x 0` is a nondegenerate fixed point of
the time-one map of `H` is isolated among `1`-periodic orbits of `signedHamiltonian ε H`. -/
theorem exists_pos_forall_periodic_eq_signedHamiltonian_of_isNondegenerateFixedPt {ε : ℝ}
    (hε : ε * ε = 1) {H : ℝ → V → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (signedHamiltonian ε H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ δ > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (signedHamiltonian ε H t) (y t)) t) →
      dist (y 0) (x 0) < δ → y = x := by
  have hiso := hnd.eventually_not_isFixedPt
  rw [timeDependentHamiltonianFlow_eq, ← zero_add (1 : ℝ)] at hiso
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_periodic_eq_of_eventually_not_isFixedPt _
    (hasDerivAt_comp_mul_of_signedHamiltonian hε hx) (s := 0) (by simpa only [mul_zero] using hiso)
  refine ⟨δ, hδ, fun y hyper hy hyx ↦ funext fun t ↦ ?_⟩
  have hxy := congrFun (h _ (hasDerivAt_comp_mul_of_signedHamiltonian hε hy)
    (periodic_comp_mul_of_mul_self_eq_one hε hyper) (by simpa only [mul_zero] using hyx)) (ε * t)
  simpa only [← mul_assoc, hε, one_mul] using hxy

/-- Forward implication of `dysonSeriesLeft_signedHamiltonian_apply_eq_self_iff`. -/
private theorem dysonSeriesLeft_apply_eq_self_of_signedHamiltonian {ε : ℝ} (hε : ε * ε = 1)
    {H : ℝ → V → ℝ} (hHs : ContDiff ℝ 2 (uncurry H)) (hH : Periodic H 1) {x : ℝ → V}
    (hxc : Continuous x) (hxper : Periodic x 1) {v : V}
    (hv : dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (signedHamiltonian ε H t)) (x (ε * t))) 1 v = v) :
    dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v := by
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)
  set S' : ℝ → V →L[ℝ] V := fun t ↦
    fderiv ℝ (ω.hamiltonianVectorField (signedHamiltonian ε H t)) (x (ε * t))
  have hSc : Continuous S := ω.continuous_fderiv_hamiltonianVectorField_comp hHs hxc
  have hS'c : Continuous S' := ω.continuous_fderiv_hamiltonianVectorField_comp
    (contDiff_uncurry_signedHamiltonian ε hHs) (hxc.comp (continuous_const.mul continuous_id))
  have hS'p : Periodic S' 1 := fun t ↦ by
    simp only [S', periodic_signedHamiltonian hε hH t]
    exact congrArg _ (periodic_comp_mul_of_mul_self_eq_one hε hxper t)
  have hS' (t : ℝ) : S' (ε * t) = ε • S t := by
    simp only [S', S, hamiltonianVectorField_signedHamiltonian_mul hε, fderiv_const_smul_field,
      Pi.smul_apply, ← mul_assoc, hε, one_mul]
  -- Read the `1`-periodic solution `Ψ'(t) v` of `ζ' = S'_t ζ` at time `ε * t`.
  set ζ : ℝ → V := fun t ↦ dysonSeriesLeft S' (ε * t) v
  have hζ (t : ℝ) : HasDerivAt ζ (S t (ζ t)) t := by
    have h := (hasDerivAt_dysonSeriesLeft_apply hS'c v (ε * t)).scomp t
      ((hasDerivAt_id' t).const_mul ε)
    rw [hS', mul_one, smul_apply, smul_smul, hε, one_smul] at h
    exact h
  have hζp : Periodic ζ 1 :=
    periodic_comp_mul_of_mul_self_eq_one hε ((periodic_dysonSeriesLeft_apply_iff hS'c hS'p v).2 hv)
  have hζ0 : ζ 0 = v := by simp [ζ, dysonSeriesLeft_zero]
  rw [← hζ0, ← eq_dysonSeriesLeft_apply hSc hζ, ← zero_add (1 : ℝ), hζp 0]

/-- **Linearized return-map fixed vectors under signed time reflection.** For a `1`-periodic `C²`
Hamiltonian `H` and a continuous `1`-periodic loop `x`, a vector `v` is fixed by the time-one
propagator of `signedHamiltonian ε H` along `t ↦ x(ε t)` if and only if it is fixed by the time-one
propagator of `H` along `x`. -/
theorem dysonSeriesLeft_signedHamiltonian_apply_eq_self_iff {ε : ℝ} (hε : ε * ε = 1)
    {H : ℝ → V → ℝ} (hHs : ContDiff ℝ 2 (uncurry H)) (hH : Periodic H 1) {x : ℝ → V}
    (hxc : Continuous x) (hxper : Periodic x 1) {v : V} :
    dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (signedHamiltonian ε H t)) (x (ε * t))) 1 v = v ↔
      dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v := by
  refine ⟨dysonSeriesLeft_apply_eq_self_of_signedHamiltonian hε hHs hH hxc hxper, fun hv ↦ ?_⟩
  have hv' : dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (signedHamiltonian ε (signedHamiltonian ε H) t))
      ((fun s ↦ x (ε * s)) (ε * t))) 1 v = v := by
    simpa only [signedHamiltonian_signedHamiltonian hε, ← mul_assoc, hε, one_mul] using hv
  exact dysonSeriesLeft_apply_eq_self_of_signedHamiltonian hε
    (contDiff_uncurry_signedHamiltonian ε hHs) (periodic_signedHamiltonian hε hH)
    (hxc.comp (continuous_const.mul continuous_id))
    (periodic_comp_mul_of_mul_self_eq_one hε hxper) hv'

/-- If `x` is an orbit of a `C²` Hamiltonian `H` whose initial point `x 0` is a nondegenerate fixed
point of the time-one map of `H`, then the linearized return map of `H` along `x` has no nonzero
fixed vector. -/
theorem eq_zero_of_dysonSeriesLeft_apply_eq_self_of_isNondegenerateFixedPt {H : ℝ → V → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hHs : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {v : V}
    (hv : dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v) :
    v = 0 := by
  have hD := (ω.differentiable_timeDependentHamiltonianFlow hL hHs 0 1 (x 0)).hasFDerivAt
  refine (isNondegenerateFixedPt_iff.1 hnd).2.2 v ?_
  rw [hD.hasMFDerivAt.mfderiv, fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft ω hL hHs hx]
  simp only [zero_add, sub_zero]
  exact hv

/-- If `x` is a `1`-periodic orbit of a `1`-periodic `C²` Hamiltonian `H` and `x 0` is a
nondegenerate fixed point of the time-one map of `H`, then the linearized return map of
`signedHamiltonian ε H` along `t ↦ x(ε t)` has no nonzero fixed vector. -/
theorem eq_zero_of_dysonSeriesLeft_signedHamiltonian_apply_eq_self {ε : ℝ} (hε : ε * ε = 1)
    {H : ℝ → V → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hHs : ContDiff ℝ 2 (uncurry H)) (hH : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {v : V} (hv : dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (signedHamiltonian ε H t)) (x (ε * t))) 1 v = v) :
    v = 0 :=
  eq_zero_of_dysonSeriesLeft_apply_eq_self_of_isNondegenerateFixedPt hL hHs hx hnd <|
    (dysonSeriesLeft_signedHamiltonian_apply_eq_self_iff hε hHs hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt) hxper).1 hv

/-- Scaling a linear map `A : ℝ × ℝ →L[ℝ] V` by `ε` (`ε * ε = 1`) identifies its difference from
`dt ⊗ X_{H(t)}(x)` with `ε` times the difference of `A` from `dt ⊗ X_{H'(ε t)}(x)`. -/
theorem smul_sub_smulRight_hamiltonianVectorField {ε : ℝ} (hε : ε * ε = 1)
    (A : ℝ × ℝ →L[ℝ] V) (H : ℝ → V → ℝ) (x : V) (t : ℝ) :
    ε • A - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) x) =
      ε • (A - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (signedHamiltonian ε H (ε * t)) x)) := by
  rw [hamiltonianVectorField_signedHamiltonian_mul hε]
  ext <;> simp [smul_sub, smul_smul, hε]

/-- Norm form of `smul_sub_smulRight_hamiltonianVectorField`. -/
theorem norm_smul_sub_smulRight_hamiltonianVectorField {ε : ℝ} (hε : ε * ε = 1)
    (A : ℝ × ℝ →L[ℝ] V) (H : ℝ → V → ℝ) (x : V) (t : ℝ) :
    ‖ε • A - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) x)‖ =
      ‖A - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (signedHamiltonian ε H (ε * t)) x)‖ := by
  rw [smul_sub_smulRight_hamiltonianVectorField hε, norm_smul, Real.norm_eq_abs,
    abs_eq_one_of_mul_self_eq_one hε, one_mul]

end NormedSpace

end TauCeti.SymplecticForm
