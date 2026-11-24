/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EulerLagrange
public import TauCeti.Geometry.Symplectic.Hamiltonian.ExtendedPhaseSpace

/-!
# The Legendre transform of a time-dependent Lagrangian

Let `E` be a real normed space, the configuration space of a mechanical system, and let
`L : ℝ → E × E → ℝ` be a time-dependent Lagrangian, a function `L t (q, v)` of time, positions and
velocities. Write `∂_t L` for its derivative in time,
`TauCeti.timeFDeriv (Function.uncurry L) t (q, v)`. At each time the Legendre map
`FL_t(q, v) = (q, ∂_v L(t, q, v))` takes values in the linear cotangent space `E × E'`, and a
family of maps `w t` solving the momentum for the velocity, `∂_v L(t, q, w t (q, p)) = p`, gives
the time-dependent Hamiltonian

`H(t, q, p) = p(w) - L(t, q, w)`, `w = w t (q, p)`,

the family `fun t ↦ TauCeti.legendreHamiltonian (L t) (w t)`. This file relates the
time-dependent Euler–Lagrange equations `d/dt ∂_v L(t, q, v) = ∂_q L(t, q, v)` to the
nonautonomous Hamilton equations of `H` and to the autonomous Hamiltonian
`K(x, t, e) = e + H(t, x)` on the extended phase space `(E × E') × T*ℝ` of
`TauCeti.Geometry.Symplectic.Hamiltonian.ExtendedPhaseSpace`, the linear model of `T*(Q × ℝ)`.

* **The time derivative of the Hamiltonian.** At a fixed point `z = (q, p)` of phase space, the
  derivative of `w` drops out of the derivative of `t ↦ H(t, z)`, which is
  `∂_t H(t, z) = -∂_t L(t, q, w t z)` (`TauCeti.hasDerivAt_legendreHamiltonian`,
  `TauCeti.timeFDeriv_uncurry_legendreHamiltonian`).
* **The extended Hamiltonian vector field.** Hence the Hamiltonian vector field of `K` at
  `(z, t, e)` is `((w, ∂_q L(t, q, w)), (1, ∂_t L(t, q, w)))`
  (`TauCeti.hamiltonianVectorField_extendedHamiltonian_legendreHamiltonian`): the position moves
  with the velocity `w`, the momentum by the force `∂_q L`, the time at unit speed, and the
  momentum `e` conjugate to the time by `∂_t L`.
* **Energy balance.** Along a solution of the time-dependent Euler–Lagrange equations the energy
  `E_L(t, q, v) = ∂_v L(t, q, v)(v) - L(t, q, v)` changes at the rate `-∂_t L`
  (`TauCeti.hasDerivAt_energy_of_eulerLagrange`, proved in
  `TauCeti.Geometry.Symplectic.Hamiltonian.EulerLagrange`, where conservation of energy
  `TauCeti.energy_eq_of_eulerLagrange` is derived from it).
* **Euler–Lagrange versus Hamilton.** A curve `q` with velocity `v` solves the time-dependent
  Euler–Lagrange equations at `t` exactly when its Legendre lift `s ↦ FL_s(q s, v s)` solves the
  nonautonomous Hamilton equations `x' = X_{H_t}(x)` at `t`
  (`TauCeti.hasDerivAt_timeDependent_linearLegendreMap_iff`, also proved in
  `TauCeti.Geometry.Symplectic.Hamiltonian.EulerLagrange`). Conversely, along a solution `γ` of
  the nonautonomous Hamilton equations, the position and the velocity `w t (γ t)` recovered from
  the momentum solve the Euler–Lagrange equations
  (`TauCeti.eulerLagrange_of_hasDerivAt_timeDependent_hamiltonianVectorField`).
* **The extended Legendre transform.** The map
  `(t, q, v) ↦ (FL_t(q, v), t, -E_L(t, q, v))` (`TauCeti.extendedLegendreMap`) lands in the zero
  level of `K` (`TauCeti.extendedHamiltonian_extendedLegendreMap`), and the lift
  `s ↦ (FL_s(q s, v s), s, -E_L(s, q s, v s))` of a curve with differentiable velocity is an
  integral curve of `X_K` at `t` exactly when the curve solves the Euler–Lagrange equations at `t`
  (`TauCeti.hasDerivAt_extendedLegendreMap_iff`). The momentum conjugate to the time is minus the
  energy, and its equation of motion is the energy balance.

For a Lagrangian that does not depend on time, `∂_t L = 0` and these statements reduce to those of
`TauCeti.Geometry.Symplectic.Hamiltonian.EulerLagrange`. As there, all statements are pointwise in
time and along the curve: no convexity or global invertibility of the Legendre maps is assumed,
only that `w t` recovers the velocity at the points considered.

## Main definitions

* `TauCeti.extendedLegendreMap L t`: the Legendre transform `(q, v) ↦ (FL_t(q, v), t, -E_L)` of a
  time-dependent Lagrangian into the extended phase space.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 14, 15 and 45.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 7.4 and 8.1.
-/

public section

namespace TauCeti

open Function ContinuousLinearMap Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : ℝ → E × E → ℝ} {w : ℝ → E × StrongDual ℝ E → E}

/-! ### The time derivative of the Hamiltonian -/

/-- **The time derivative of the Hamiltonian.** Let `w` solve the momentum `p` for the velocity
at time `t` and the point `z = (q, p)`, that is `∂_v L(t, q, w t z) = p`. Then the time-dependent
Hamiltonian `H(s, z) = p(w s z) - L(s, q, w s z)` has time derivative `-∂_t L(t, q, w t z)` at
`t`. The time derivative of `w` does not contribute. -/
theorem hasDerivAt_legendreHamiltonian {z : E × StrongDual ℝ E} {t : ℝ} {w' : E}
    (hw : HasDerivAt (fun s ↦ w s z) w' t)
    (hL : DifferentiableAt ℝ (uncurry L) (t, (z.1, w t z)))
    (hp : fderiv ℝ (fun v ↦ L t (z.1, v)) (w t z) = z.2) :
    HasDerivAt (fun s ↦ legendreHamiltonian (L s) (w s) z)
      (-timeFDeriv (uncurry L) t (z.1, w t z)) t := by
  have hLc := hasDerivAt_timeDependent_comp_prodMk (q := fun _ ↦ z.1) (v := fun s ↦ w s z) hL
    (hasDerivAt_const t z.1) hw
  simp only [map_zero, add_zero, hp] at hLc
  have hfun : (fun s ↦ legendreHamiltonian (L s) (w s) z) =
      fun s ↦ z.2 (w s z) - L s (z.1, w s z) := by
    ext s
    simp [legendreHamiltonian_apply]
  rw [hfun]
  exact ((z.2.hasFDerivAt.comp_hasDerivAt t hw).sub hLc).congr_deriv (by simp)

/-- The time-dependent Hamiltonian is jointly differentiable in time and phase space where `w` and
`L` are. -/
theorem differentiableAt_uncurry_legendreHamiltonian {z : E × StrongDual ℝ E} {t : ℝ}
    (hw : DifferentiableAt ℝ (uncurry w) (t, z))
    (hL : DifferentiableAt ℝ (uncurry L) (t, (z.1, w t z))) :
    DifferentiableAt ℝ (uncurry fun s ↦ legendreHamiltonian (L s) (w s)) (t, z) := by
  have hfun : (uncurry fun s ↦ legendreHamiltonian (L s) (w s)) =
      fun y : ℝ × (E × StrongDual ℝ E) ↦
        y.2.2 (uncurry w y) - uncurry L (y.1, (y.2.1, uncurry w y)) := by
    ext ⟨s, y⟩
    simp [legendreHamiltonian_apply]
  rw [hfun]
  exact (differentiableAt_snd.snd.clm_apply hw).sub
    (hL.comp (t, z) (differentiableAt_fst.prodMk (differentiableAt_snd.fst.prodMk hw)))

/-- **The time derivative of the Hamiltonian**, as the parameter velocity of the jointly
differentiable time-dependent Hamiltonian: `∂_t H(t, z) = -∂_t L(t, q, w t z)` where `w` solves
the momentum `p` of `z = (q, p)` for the velocity. -/
theorem timeFDeriv_uncurry_legendreHamiltonian {z : E × StrongDual ℝ E} {t : ℝ}
    (hw : DifferentiableAt ℝ (uncurry w) (t, z))
    (hL : DifferentiableAt ℝ (uncurry L) (t, (z.1, w t z)))
    (hp : fderiv ℝ (fun v ↦ L t (z.1, v)) (w t z) = z.2) :
    timeFDeriv (uncurry fun s ↦ legendreHamiltonian (L s) (w s)) t z =
      -timeFDeriv (uncurry L) t (z.1, w t z) :=
  (hasDerivAt_parameterCurve (differentiableAt_uncurry_legendreHamiltonian hw hL)).unique
    (hasDerivAt_legendreHamiltonian (hasDerivAt_parameterCurve_uncurry hw) hL hp)

/-! ### Euler–Lagrange equations and the nonautonomous Hamilton equations -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Solutions of the nonautonomous Hamilton equations satisfy the Euler–Lagrange equations.**
Let `γ` solve the Hamilton equations `γ' = X_{H_t}(γ)` of the time-dependent Hamiltonian
`H_t = p(w t) - L(t, q, w t)` at `t`, and let `w s` solve the momentum for the velocity along `γ`
for `s` near `t`. Write `q = γ.1` for the position curve and `v s = w s (γ s)` for the velocity
recovered from the momentum. Then `q'(t) = v(t)`, the Legendre lift `FL_t(q t, v t)` equals `γ t`,
and the time-dependent Euler–Lagrange equation `d/dt ∂_v L(t, q, v) = ∂_q L(t, q, v)` holds at
`t`. -/
theorem eulerLagrange_of_hasDerivAt_timeDependent_hamiltonianVectorField
    {γ : ℝ → E × StrongDual ℝ E} {t : ℝ}
    (hγ : HasDerivAt γ ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
      (legendreHamiltonian (L t) (w t)) (γ t)) t)
    (hw : DifferentiableAt ℝ (w t) (γ t)) (hL : DifferentiableAt ℝ (L t) ((γ t).1, w t (γ t)))
    (hp : ∀ᶠ s in 𝓝 t, fderiv ℝ (fun v ↦ L s ((γ s).1, v)) (w s (γ s)) = (γ s).2) :
    HasDerivAt (fun s ↦ (γ s).1) (w t (γ t)) t ∧
      linearLegendreMap (L t) ((γ t).1, w t (γ t)) = γ t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L s ((γ s).1, u)) (w s (γ s)))
        (fderiv ℝ (fun y ↦ L t (y, w t (γ t))) (γ t).1) t := by
  have hlift : (fun s ↦ linearLegendreMap (L s) ((γ s).1, w s (γ s))) =ᶠ[𝓝 t] γ :=
    hp.mono fun s hs ↦
      Prod.ext (linearLegendreMap_fst _ _) ((linearLegendreMap_snd _ _).trans hs)
  have hlift_t : linearLegendreMap (L t) ((γ t).1, w t (γ t)) = γ t := hlift.self_of_nhds
  have hγ' : HasDerivAt (fun s ↦ linearLegendreMap (L s) ((γ s).1, w s (γ s)))
      ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
        (legendreHamiltonian (L t) (w t)) (linearLegendreMap (L t) ((γ t).1, w t (γ t)))) t := by
    rw [hlift_t]
    exact hγ.congr_of_eventuallyEq hlift
  have h := (hasDerivAt_timeDependent_linearLegendreMap_iff (q := fun s ↦ (γ s).1)
    (v := fun s ↦ w s (γ s)) (by rw [hlift_t]; exact hw) hL (by rw [hlift_t])).1 hγ'
  exact ⟨h.1, hlift_t, h.2⟩

end FiniteDimensional

/-! ### The extended phase space -/

/-- **The Legendre transform into the extended phase space** of a time-dependent Lagrangian `L`,
`(q, v) ↦ (FL_t(q, v), t, -E_L(t, q, v))` at time `t`: the Legendre image `(q, ∂_v L(t, q, v))`,
the time `t`, and as momentum conjugate to the time minus the energy
`E_L(t, q, v) = ∂_v L(t, q, v)(v) - L(t, q, v)`. -/
noncomputable def extendedLegendreMap (L : ℝ → E × E → ℝ) (t : ℝ) (x : E × E) :
    (E × StrongDual ℝ E) × (ℝ × ℝ) :=
  (linearLegendreMap (L t) x, (t, L t x - fderiv ℝ (fun v ↦ L t (x.1, v)) x.2 x.2))

theorem extendedLegendreMap_def (L : ℝ → E × E → ℝ) (t : ℝ) (x : E × E) :
    extendedLegendreMap L t x =
      (linearLegendreMap (L t) x, (t, L t x - fderiv ℝ (fun v ↦ L t (x.1, v)) x.2 x.2)) :=
  (rfl)

@[simp]
theorem extendedLegendreMap_fst (L : ℝ → E × E → ℝ) (t : ℝ) (x : E × E) :
    (extendedLegendreMap L t x).1 = linearLegendreMap (L t) x :=
  (rfl)

@[simp]
theorem extendedLegendreMap_snd (L : ℝ → E × E → ℝ) (t : ℝ) (x : E × E) :
    (extendedLegendreMap L t x).2 = (t, L t x - fderiv ℝ (fun v ↦ L t (x.1, v)) x.2 x.2) :=
  (rfl)

/-- **The extended Legendre transform lands in the zero level of the extended Hamiltonian**
`K(x, t, e) = e + H(t, x)`, provided `w t` recovers the velocity: the energy `H(t, FL_t(q, v))`
cancels the momentum `-E_L(t, q, v)` conjugate to the time. -/
theorem extendedHamiltonian_extendedLegendreMap {t : ℝ} {x : E × E}
    (hw : w t (linearLegendreMap (L t) x) = x.2) :
    extendedHamiltonian (fun s ↦ legendreHamiltonian (L s) (w s)) (extendedLegendreMap L t x) =
      0 := by
  rw [extendedHamiltonian_apply, extendedLegendreMap_snd, extendedLegendreMap_fst,
    legendreHamiltonian_linearLegendreMap hw]
  ring

variable [FiniteDimensional ℝ E]

/-- **The extended Hamiltonian vector field of a time-dependent Lagrangian system.** Let `w` and
`L` be jointly differentiable, and let `w` solve the momentum `p` of `z = (q, p)` for the velocity
at time `t`. Then the Hamiltonian vector field of `K(x, t, e) = e + H(t, x)` on the extended phase
space at `(z, t, e)` is `((w t z, ∂_q L(t, q, w t z)), (1, ∂_t L(t, q, w t z)))`. -/
theorem hamiltonianVectorField_extendedHamiltonian_legendreHamiltonian
    {z : E × StrongDual ℝ E} {t : ℝ} (hw : DifferentiableAt ℝ (uncurry w) (t, z))
    (hL : DifferentiableAt ℝ (uncurry L) (t, (z.1, w t z)))
    (hp : fderiv ℝ (fun v ↦ L t (z.1, v)) (w t z) = z.2) (e : ℝ) :
    (strongDualCotangentSymplecticForm (V := E)).extended.hamiltonianVectorField
        (extendedHamiltonian fun s ↦ legendreHamiltonian (L s) (w s)) (z, (t, e)) =
      ((w t z, fderiv ℝ (fun q ↦ L t (q, w t z)) z.1),
        (1, timeFDeriv (uncurry L) t (z.1, w t z))) := by
  rw [SymplecticForm.hamiltonianVectorField_extendedHamiltonian _
      (differentiableAt_uncurry_legendreHamiltonian hw hL) e,
    hamiltonianVectorField_legendreHamiltonian (L := L t) (w := w t)
      (hasFDerivAt_timeSlice hw).differentiableAt (hasFDerivAt_timeSlice hL).differentiableAt hp,
    timeFDeriv_uncurry_legendreHamiltonian hw hL hp, neg_neg]

/-- **Euler–Lagrange equations versus the extended Hamiltonian flow.** Let `q` be a curve with
velocity field `v` differentiable at `t`, let `w` and `L` be jointly differentiable at the points
over time `t`, and let `w t` recover the velocity from the Legendre lift at `t`. Then the extended
Legendre lift `s ↦ (FL_s(q s, v s), s, -E_L(s, q s, v s))` is an integral curve at `t` of the
Hamiltonian vector field of `K(x, t, e) = e + H(t, x)` exactly when `v` is the velocity of `q` at
`t` and the time-dependent Euler–Lagrange equation `d/dt ∂_v L(t, q, v) = ∂_q L(t, q, v)` holds at
`t`. -/
theorem hasDerivAt_extendedLegendreMap_iff {q v : ℝ → E} {t : ℝ}
    (hw : DifferentiableAt ℝ (uncurry w) (t, linearLegendreMap (L t) (q t, v t)))
    (hL : DifferentiableAt ℝ (uncurry L) (t, (q t, v t)))
    (hwv : w t (linearLegendreMap (L t) (q t, v t)) = v t) (hv : DifferentiableAt ℝ v t) :
    HasDerivAt (fun s ↦ extendedLegendreMap L s (q s, v s))
        ((strongDualCotangentSymplecticForm (V := E)).extended.hamiltonianVectorField
          (extendedHamiltonian fun s ↦ legendreHamiltonian (L s) (w s))
          (extendedLegendreMap L t (q t, v t))) t ↔
      HasDerivAt q (v t) t ∧
        HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L s (q s, u)) (v s))
          (fderiv ℝ (fun y ↦ L t (y, v t)) (q t)) t := by
  have hfun : (fun s ↦ extendedLegendreMap L s (q s, v s)) = fun s ↦
      ((q s, fderiv ℝ (fun u ↦ L s (q s, u)) (v s)),
        (s, L s (q s, v s) - fderiv ℝ (fun u ↦ L s (q s, u)) (v s) (v s))) :=
    funext fun s ↦ by simp [extendedLegendreMap_def, Prod.ext_iff]
  rw [hfun, extendedLegendreMap_def,
    hamiltonianVectorField_extendedHamiltonian_legendreHamiltonian hw (by simpa [hwv] using hL)
      (by simp [hwv])]
  simp only [linearLegendreMap_fst, hwv]
  refine ⟨fun h ↦ ⟨h.fst.fst, h.fst.snd⟩, fun h ↦ ?_⟩
  refine (h.1.prodMk h.2).prodMk ((hasDerivAt_id t).prodMk ?_)
  have hE := (hasDerivAt_energy_of_eulerLagrange h.1 h.2 hL hv).neg
  rw [neg_neg] at hE
  convert hE using 1
  ext s
  simp

end TauCeti
