/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The orbits of the isotropic harmonic oscillator

Let `V` be a real inner product space. The isotropic harmonic oscillator of mass `m` and angular
frequency `ν` is the central force with potential `U(r) = m ν² r² / 2`, with Hamiltonian
`H(q, p) = ‖p‖² / (2m) + m ν² ‖q‖² / 2` on the phase space `V × V`. Unlike a general central
force, it is smooth on the whole phase space, including the collision set `q = 0`, and Hamilton's
equations `q' = p / m`, `p' = -m ν² q` hold everywhere
(`TauCeti.stdSymplecticForm_hamiltonianVectorField_isotropicOscillator`).

For `m ν ≠ 0` they are solved by the linear evolution

`q(t) = cos (ν t) q + sin (ν t) / (m ν) p`,  `p(t) = -m ν sin (ν t) q + cos (ν t) p`

(`TauCeti.isotropicOscillatorEvolution`), which is jointly smooth in time and initial point,
satisfies the flow law, preserves the standard symplectic form, the energy and the squared angular
momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`, and is the only solution: every integral curve of the
Hamiltonian vector field defined for all times is an orbit of it
(`TauCeti.eq_isotropicOscillatorEvolution_of_hasDerivAt`). In finite dimension it is therefore the
generic Hamiltonian flow `TauCeti.SymplecticForm.hamiltonianFlow`
(`TauCeti.hamiltonianFlow_isotropicOscillator`).

This describes all orbits of the isotropic oscillator. They are closed and bounded:

* every orbit is periodic with period `2π / ν`, independent of the energy, and away from the
  equilibrium at the origin it returns to its starting point exactly at the integer multiples of
  `2π / ν` (`TauCeti.isotropicOscillatorEvolution_eq_self_iff`);
* every orbit has compact range (`TauCeti.isCompact_range_isotropicOscillatorEvolution`).

An orbit avoids the collision set `q = 0` for all times exactly when its squared angular momentum
`ℓ²` is nonzero, that is, when position and momentum are linearly independent
(`TauCeti.forall_fst_isotropicOscillatorEvolution_ne_zero_iff`); when `ℓ² = 0` the orbit reaches
the origin. Thus the orbits with nonzero angular momentum are exactly the closed bounded
noncollision orbits. The radial quadratures of the same potential, with radial period `π / ν`,
half the period of the orbit, are computed in
`TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.RadialAction`.

## Main declarations

* `TauCeti.stdSymplecticForm_hamiltonianVectorField_isotropicOscillator`: Hamilton's equations.
* `TauCeti.isotropicOscillatorVelocity m ν`: the Hamiltonian vector field as a continuous linear
  map, globally Lipschitz (`TauCeti.lipschitzWith_hamiltonianVectorField_isotropicOscillator`).
* `TauCeti.isotropicOscillatorEvolution m ν t`: the time-`t` evolution.
* `TauCeti.hasDerivAt_isotropicOscillatorEvolution`: the evolution solves Hamilton's equations.
* `TauCeti.eq_isotropicOscillatorEvolution_of_hasDerivAt`: every global integral curve is an orbit
  of the evolution.
* `TauCeti.hamiltonianFlow_isotropicOscillator`: the evolution is the Hamiltonian flow.
* `TauCeti.isotropicOscillatorEvolution_add`: the flow law.
* `TauCeti.stdSymplecticForm_isotropicOscillatorEvolution`: the evolution is symplectic.
* `TauCeti.centralForceHamiltonian_isotropicOscillatorEvolution`,
  `TauCeti.sq_sub_inner_sq_isotropicOscillatorEvolution`: conservation of energy and of `ℓ²`.
* `TauCeti.periodic_isotropicOscillatorEvolution`,
  `TauCeti.isotropicOscillatorEvolution_eq_self_iff`: the orbits are periodic, with period lattice
  `(2π / ν) ℤ` away from the origin.
* `TauCeti.isCompact_range_isotropicOscillatorEvolution`: the orbits are bounded.
* `TauCeti.forall_fst_isotropicOscillatorEvolution_ne_zero_iff`: an orbit avoids collision exactly
  when `ℓ² ≠ 0`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 5 and 8.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Sections 3.6 and 10.8.
-/

public section

noncomputable section

namespace TauCeti

open Real Set
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m ν : ℝ}

/-- The Hamiltonian vector field `(q, p) ↦ (p / m, -m ν² q)` of the isotropic harmonic oscillator
of mass `m` and angular frequency `ν`, a continuous linear map
(`TauCeti.hamiltonianVectorField_isotropicOscillator`). -/
def isotropicOscillatorVelocity (m ν : ℝ) : (V × V) →L[ℝ] V × V :=
  (m⁻¹ • ContinuousLinearMap.snd ℝ V V).prod (-((m * ν ^ 2) • ContinuousLinearMap.fst ℝ V V))

@[simp]
theorem isotropicOscillatorVelocity_apply (m ν : ℝ) (x : V × V) :
    isotropicOscillatorVelocity m ν x = (m⁻¹ • x.2, -((m * ν ^ 2) • x.1)) :=
  (rfl)

/-- The time-`t` evolution of the isotropic harmonic oscillator of mass `m` and angular frequency
`ν`, the linear map
`(q, p) ↦ (cos (ν t) q + sin (ν t) / (m ν) p, -m ν sin (ν t) q + cos (ν t) p)`. For `m ν ≠ 0` its
orbits are the integral curves of Hamilton's equations `q' = p / m`, `p' = -m ν² q`
(`TauCeti.hasDerivAt_isotropicOscillatorEvolution`,
`TauCeti.eq_isotropicOscillatorEvolution_of_hasDerivAt`). -/
def isotropicOscillatorEvolution (m ν t : ℝ) : (V × V) →L[ℝ] V × V :=
  (Real.cos (ν * t) • ContinuousLinearMap.fst ℝ V V +
      (Real.sin (ν * t) / (m * ν)) • ContinuousLinearMap.snd ℝ V V).prod
    ((-(m * ν * Real.sin (ν * t))) • ContinuousLinearMap.fst ℝ V V +
      Real.cos (ν * t) • ContinuousLinearMap.snd ℝ V V)

theorem isotropicOscillatorEvolution_apply (m ν t : ℝ) (x : V × V) :
    isotropicOscillatorEvolution m ν t x =
      (Real.cos (ν * t) • x.1 + (Real.sin (ν * t) / (m * ν)) • x.2,
        (-(m * ν * Real.sin (ν * t))) • x.1 + Real.cos (ν * t) • x.2) :=
  (rfl)

@[simp]
theorem isotropicOscillatorEvolution_apply_fst (m ν t : ℝ) (x : V × V) :
    (isotropicOscillatorEvolution m ν t x).1 =
      Real.cos (ν * t) • x.1 + (Real.sin (ν * t) / (m * ν)) • x.2 :=
  (rfl)

@[simp]
theorem isotropicOscillatorEvolution_apply_snd (m ν t : ℝ) (x : V × V) :
    (isotropicOscillatorEvolution m ν t x).2 =
      (-(m * ν * Real.sin (ν * t))) • x.1 + Real.cos (ν * t) • x.2 :=
  (rfl)

@[simp]
theorem isotropicOscillatorEvolution_zero (m ν : ℝ) (x : V × V) :
    isotropicOscillatorEvolution m ν 0 x = x := by
  simp [isotropicOscillatorEvolution_apply]

/-- The evolution is jointly smooth in time and initial point. -/
theorem contDiff_isotropicOscillatorEvolution (m ν : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun y : ℝ × (V × V) ↦ isotropicOscillatorEvolution m ν y.1 y.2 := by
  simp only [isotropicOscillatorEvolution_apply]
  fun_prop

/-- Each orbit `t ↦ Φ_t(x)` of the evolution is continuous. -/
theorem continuous_isotropicOscillatorEvolution (m ν : ℝ) (x : V × V) :
    Continuous fun t ↦ isotropicOscillatorEvolution m ν t x := by
  simp only [isotropicOscillatorEvolution_apply]
  fun_prop

/-- **The flow law**: evolution for successive times is evolution for their sum. -/
theorem isotropicOscillatorEvolution_add (hm : m ≠ 0) (hν : ν ≠ 0) (s t : ℝ) (x : V × V) :
    isotropicOscillatorEvolution m ν (s + t) x =
      isotropicOscillatorEvolution m ν s (isotropicOscillatorEvolution m ν t x) := by
  simp only [isotropicOscillatorEvolution_apply, mul_add, Real.cos_add, Real.sin_add, smul_add,
    smul_smul, Prod.mk.injEq]
  constructor <;> match_scalars <;> field_simp <;> ring

/-- Reversing time inverts the evolution. -/
@[simp]
theorem isotropicOscillatorEvolution_neg_apply (hm : m ≠ 0) (hν : ν ≠ 0) (t : ℝ) (x : V × V) :
    isotropicOscillatorEvolution m ν (-t) (isotropicOscillatorEvolution m ν t x) = x := by
  rw [← isotropicOscillatorEvolution_add hm hν, neg_add_cancel, isotropicOscillatorEvolution_zero]

/-- The coefficient matrix of the evolution has determinant `cos² (ν t) + sin² (ν t) = 1`. -/
private theorem det_isotropicOscillatorEvolution (hm : m ≠ 0) (hν : ν ≠ 0) (t : ℝ) :
    Real.cos (ν * t) * Real.cos (ν * t) -
      Real.sin (ν * t) / (m * ν) * -(m * ν * Real.sin (ν * t)) = 1 := by
  field_simp
  linear_combination Real.cos_sq_add_sin_sq (ν * t)

/-- The evolution preserves the standard symplectic form of `V × V`. -/
theorem stdSymplecticForm_isotropicOscillatorEvolution (hm : m ≠ 0) (hν : ν ≠ 0) (t : ℝ)
    (u w : V × V) :
    stdSymplecticForm (isotropicOscillatorEvolution m ν t u)
        (isotropicOscillatorEvolution m ν t w) = stdSymplecticForm u w := by
  have hdet := det_isotropicOscillatorEvolution hm hν t
  simp only [stdSymplecticForm_apply, isotropicOscillatorEvolution_apply, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right]
  linear_combination (⟪u.1, w.2⟫_ℝ - ⟪u.2, w.1⟫_ℝ) * hdet

/-- The evolution preserves the squared angular momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²`, at every
point of the phase space, including the collision set. -/
theorem sq_sub_inner_sq_isotropicOscillatorEvolution (hm : m ≠ 0) (hν : ν ≠ 0) (t : ℝ)
    (x : V × V) :
    ‖(isotropicOscillatorEvolution m ν t x).1‖ ^ 2 *
          ‖(isotropicOscillatorEvolution m ν t x).2‖ ^ 2 -
        ⟪(isotropicOscillatorEvolution m ν t x).1,
          (isotropicOscillatorEvolution m ν t x).2⟫_ℝ ^ 2 =
      ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 := by
  have hdet := det_isotropicOscillatorEvolution hm hν t
  rw [isotropicOscillatorEvolution_apply, sq_sub_inner_sq_smul_add_smul, hdet, one_pow, one_mul]

/-- **Conservation of energy**: the evolution preserves the Hamiltonian
`‖p‖² / (2m) + m ν² ‖q‖² / 2` of the isotropic oscillator. -/
theorem centralForceHamiltonian_isotropicOscillatorEvolution (hm : m ≠ 0) (hν : ν ≠ 0) (t : ℝ)
    (x : V × V) :
    centralForceHamiltonian m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2)
        (isotropicOscillatorEvolution m ν t x) =
      centralForceHamiltonian m (fun r ↦ m * ν ^ 2 * r ^ 2 / 2) x := by
  obtain ⟨q, p⟩ := x
  simp only [isotropicOscillatorEvolution_apply, centralForceHamiltonian_apply,
    ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm q p]
  field_simp
  linear_combination (m ^ 2 * ν ^ 2 * ⟪q, q⟫_ℝ + ⟪p, p⟫_ℝ) * Real.cos_sq_add_sin_sq (ν * t)

/-! ### Closed orbits -/

/-- Every orbit of the isotropic oscillator is periodic with period `2π / ν`, independent of the
energy. -/
theorem periodic_isotropicOscillatorEvolution (hν : ν ≠ 0) (x : V × V) :
    Function.Periodic (fun t ↦ isotropicOscillatorEvolution m ν t x) (2 * π / ν) := by
  intro t
  have h : ν * (t + 2 * π / ν) = ν * t + 2 * π := by field_simp
  simp only [isotropicOscillatorEvolution_apply, h, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **The period lattice of the isotropic oscillator** is `(2π / ν) ℤ`: an orbit starting away from
the equilibrium at the origin is back at its starting point at time `t` exactly when `t` is an
integer multiple of `2π / ν`. -/
theorem isotropicOscillatorEvolution_eq_self_iff (hm : m ≠ 0) (hν : ν ≠ 0) {x : V × V}
    (hx : x ≠ 0) (t : ℝ) :
    isotropicOscillatorEvolution m ν t x = x ↔ t ∈ AddSubgroup.zmultiples (2 * π / ν) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨q, p⟩ := x
    rw [isotropicOscillatorEvolution_apply, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    dsimp only at h₁ h₂
    set c := Real.cos (ν * t)
    set s := Real.sin (ν * t)
    -- Eliminating `p`, respectively `q`, from the two linear equations satisfied by the starting
    -- point gives `((c - 1)² + s²) q = 0` and `((c - 1)² + s²) p = 0`.
    have hq : ((c - 1) ^ 2 + s ^ 2) • q =
        (c - 1) • (c • q + (s / (m * ν)) • p - q) -
          (s / (m * ν)) • ((-(m * ν * s)) • q + c • p - p) := by
      match_scalars <;> field_simp <;> ring
    have hp : ((c - 1) ^ 2 + s ^ 2) • p =
        (m * ν * s) • (c • q + (s / (m * ν)) • p - q) +
          (c - 1) • ((-(m * ν * s)) • q + c • p - p) := by
      match_scalars <;> field_simp <;> ring
    simp only [h₁, h₂, sub_self, smul_zero, add_zero] at hq hp
    have hcs : (c - 1) ^ 2 + s ^ 2 = 0 := by
      by_contra hne
      exact hx (Prod.ext ((smul_eq_zero.1 hq).resolve_left hne)
        ((smul_eq_zero.1 hp).resolve_left hne))
    have hc1 : c = 1 := by nlinarith [sq_nonneg (c - 1), sq_nonneg s]
    obtain ⟨n, hn⟩ := Real.cos_eq_one_iff (ν * t) |>.1 hc1
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨n, ?_⟩
    rw [zsmul_eq_mul]
    field_simp
    linarith
  · obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    simpa using (periodic_isotropicOscillatorEvolution (m := m) hν x).zsmul n 0

/-- Every orbit of the isotropic oscillator is bounded: it has compact range. -/
theorem isCompact_range_isotropicOscillatorEvolution (hν : ν ≠ 0) (x : V × V) :
    IsCompact (range fun t ↦ isotropicOscillatorEvolution m ν t x) :=
  (periodic_isotropicOscillatorEvolution hν x).compact_of_continuous
    (div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hν)
    (continuous_isotropicOscillatorEvolution m ν x)

/-- **Noncollision of the isotropic oscillator.** An orbit avoids the collision set `q = 0` for all
times exactly when its squared angular momentum `ℓ² = ‖q‖² ‖p‖² - ⟪q, p⟫²` is nonzero, that is,
when `q` and `p` are linearly independent. When `ℓ² = 0`, the orbit reaches the origin. -/
theorem forall_fst_isotropicOscillatorEvolution_ne_zero_iff (hm : m ≠ 0) (hν : ν ≠ 0)
    (x : V × V) :
    (∀ t, (isotropicOscillatorEvolution m ν t x).1 ≠ 0) ↔
      ‖x.1‖ ^ 2 * ‖x.2‖ ^ 2 - ⟪x.1, x.2⟫_ℝ ^ 2 ≠ 0 := by
  refine ⟨fun h hℓ ↦ ?_, fun hℓ t ht ↦ hℓ ?_⟩
  · obtain ⟨q, p⟩ := x
    -- By the equality case of the Cauchy–Schwarz inequality, `q = 0` or `p = k q`.
    have hcs : ‖⟪q, p⟫_ℝ‖ = ‖q‖ * ‖p‖ := by
      rw [Real.norm_eq_abs, ← sq_eq_sq₀ (abs_nonneg _) (by positivity), sq_abs]
      linear_combination -hℓ
    obtain hq | ⟨k, hp⟩ := ((norm_inner_eq_norm_tfae (𝕜 := ℝ) q p).out 1 3).1 hcs
    · exact h 0 (by simpa using hq)
    -- If `p = k q`, the position at time `t` is `f t • q` for the scalar function
    -- `f t = cos (ν t) + k sin (ν t) / (m ν)`, which changes sign between `0` and `π / ν`.
    set f : ℝ → ℝ := fun t ↦ Real.cos (ν * t) + Real.sin (ν * t) / (m * ν) * k with hf
    have hfc : Continuous f := by fun_prop
    have hf0 : f 0 = 1 := by simp [hf]
    have hfπ : f (π / ν) = -1 := by
      simp [hf, mul_div_cancel₀ π hν]
    obtain ⟨t, ht⟩ : (0 : ℝ) ∈ range f :=
      intermediate_value_univ (π / ν) 0 hfc ⟨by rw [hfπ]; norm_num, by rw [hf0]; norm_num⟩
    refine h t ?_
    rw [isotropicOscillatorEvolution_apply, hp, smul_smul, ← add_smul]
    exact smul_eq_zero_of_left ht q
  · rw [← sq_sub_inner_sq_isotropicOscillatorEvolution hm hν t x, ht]
    simp

/-! ### Hamilton's equations -/

variable [FiniteDimensional ℝ V]

/-- **Hamilton's equations of the isotropic oscillator** `H(q, p) = ‖p‖² / (2m) + m ν² ‖q‖² / 2`:
`q' = p / m` and `p' = -m ν² q`. Unlike the general central-force formula
`TauCeti.stdSymplecticForm_hamiltonianVectorField_centralForceHamiltonian`, this holds at every
point, including the collision set `q = 0`. -/
theorem stdSymplecticForm_hamiltonianVectorField_isotropicOscillator (m ν : ℝ) (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2) x =
      isotropicOscillatorVelocity m ν x := by
  have hH : HasFDerivAt (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2 : V × V → ℝ)
      ((innerSL ℝ ((m * ν ^ 2) • x.1)).coprod (innerSL ℝ (m⁻¹ • x.2))) x := by
    have h := ((hasFDerivAt_snd (p := x)).norm_sq.mul_const (2 * m)⁻¹).add
      (((hasFDerivAt_fst (p := x)).norm_sq.const_mul (m * ν ^ 2)).mul_const 2⁻¹)
    refine (h.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv
      (ContinuousLinearMap.ext fun u ↦ ?_)
    · obtain ⟨q, p⟩ := y
      simp only [centralForceHamiltonian_apply, div_eq_mul_inv, Pi.add_apply]
    · simp
      ring
  simpa using stdSymplecticForm_hamiltonianVectorField hH

/-- The Hamiltonian vector field of the isotropic oscillator is the continuous linear map
`TauCeti.isotropicOscillatorVelocity`. -/
theorem hamiltonianVectorField_isotropicOscillator (m ν : ℝ) :
    (stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2) =
      ⇑(isotropicOscillatorVelocity (V := V) m ν) :=
  funext fun x ↦ stdSymplecticForm_hamiltonianVectorField_isotropicOscillator m ν x

/-- The Hamiltonian vector field of the isotropic oscillator is globally Lipschitz, being linear. -/
theorem lipschitzWith_hamiltonianVectorField_isotropicOscillator (m ν : ℝ) :
    LipschitzWith ‖isotropicOscillatorVelocity (V := V) m ν‖₊
      ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2)) := by
  rw [hamiltonianVectorField_isotropicOscillator]
  exact ContinuousLinearMap.lipschitzWith _

/-- The evolution solves Hamilton's equations of the isotropic oscillator: `t ↦ Φ_t(x)` is an
integral curve of its Hamiltonian vector field through `x`. -/
theorem hasDerivAt_isotropicOscillatorEvolution (hm : m ≠ 0) (hν : ν ≠ 0) (x : V × V) (t : ℝ) :
    HasDerivAt (fun s ↦ isotropicOscillatorEvolution m ν s x)
      ((stdSymplecticForm (V := V)).hamiltonianVectorField
        (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2)
        (isotropicOscillatorEvolution m ν t x)) t := by
  have hlin : HasDerivAt (fun s ↦ ν * s) ν t := by simpa using (hasDerivAt_id t).const_mul ν
  have hc := hlin.cos
  have hs := hlin.sin
  have h := ((hc.smul_const x.1).fun_add ((hs.div_const (m * ν)).smul_const x.2)).prodMk
    (((hs.const_mul (m * ν)).fun_neg.smul_const x.1).fun_add (hc.smul_const x.2))
  have hfun : (fun s ↦ isotropicOscillatorEvolution m ν s x) = fun s ↦
      (Real.cos (ν * s) • x.1 + (Real.sin (ν * s) / (m * ν)) • x.2,
        (-(m * ν * Real.sin (ν * s))) • x.1 + Real.cos (ν * s) • x.2) :=
    funext fun s ↦ isotropicOscillatorEvolution_apply m ν s x
  rw [stdSymplecticForm_hamiltonianVectorField_isotropicOscillator, hfun]
  refine HasDerivAt.congr_deriv h ?_
  simp only [isotropicOscillatorVelocity_apply, isotropicOscillatorEvolution_apply, Prod.mk.injEq,
    smul_add, smul_smul]
  constructor <;> match_scalars <;> field_simp

/-- **Uniqueness of the motion.** Every integral curve `γ` of the Hamiltonian vector field of the
isotropic oscillator defined for all times is an orbit of the evolution:
`γ t = Φ_(t - t₀)(γ t₀)` for all `t₀` and `t`. -/
theorem eq_isotropicOscillatorEvolution_of_hasDerivAt (hm : m ≠ 0) (hν : ν ≠ 0) {γ : ℝ → V × V}
    (hγ : ∀ t, HasDerivAt γ ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2) (γ t)) t) (t₀ t : ℝ) :
    γ t = isotropicOscillatorEvolution m ν (t - t₀) (γ t₀) := by
  -- The Hamiltonian vector field is a continuous linear map, so it is globally Lipschitz and the
  -- ODE has unique solutions.
  rw [hamiltonianVectorField_isotropicOscillator] at hγ
  have hg (s : ℝ) : HasDerivAt (fun s ↦ isotropicOscillatorEvolution m ν (s - t₀) (γ t₀))
      (isotropicOscillatorVelocity m ν (isotropicOscillatorEvolution m ν (s - t₀) (γ t₀))) s := by
    rw [← hamiltonianVectorField_isotropicOscillator]
    exact (hasDerivAt_isotropicOscillatorEvolution hm hν (γ t₀) (s - t₀)).comp_sub_const s t₀
  have h := ODE_solution_unique_univ (v := fun _ ↦ isotropicOscillatorVelocity m ν)
    (s := fun _ ↦ univ) (t₀ := t₀)
    (fun _ ↦ (isotropicOscillatorVelocity (V := V) m ν).lipschitzWith.lipschitzOnWith)
    (fun s ↦ ⟨hγ s, mem_univ _⟩) (fun s ↦ ⟨hg s, mem_univ _⟩) (by simp)
  exact congrFun h t

/-- The Hamiltonian flow of the isotropic oscillator is its explicit evolution. -/
theorem hamiltonianFlow_isotropicOscillator (hm : m ≠ 0) (hν : ν ≠ 0) {K : NNReal}
    (hX : LipschitzWith K ((stdSymplecticForm (V := V)).hamiltonianVectorField
      (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2)))
    (t : ℝ) (x : V × V) :
    (stdSymplecticForm (V := V)).hamiltonianFlow
        (centralForceHamiltonian m fun r ↦ m * ν ^ 2 * r ^ 2 / 2) hX t x =
      isotropicOscillatorEvolution m ν t x := by
  have h := eq_flowOfLipschitz hX (γ := fun s ↦ isotropicOscillatorEvolution m ν s x)
    (hasDerivAt_isotropicOscillatorEvolution hm hν x) t
  simpa [SymplecticForm.hamiltonianFlow_eq] using h.symm

end TauCeti
