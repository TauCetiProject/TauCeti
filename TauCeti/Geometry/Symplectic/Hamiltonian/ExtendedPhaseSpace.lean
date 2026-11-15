/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# The extended phase space of a time-dependent Hamiltonian

Let `(V, ω)` be a finite-dimensional symplectic vector space and `H : ℝ → V → ℝ` a time-dependent
Hamiltonian, with the conventions `ι_{X_H} ω = dH` and `{F, G} = ω(X_F, X_G) = dF(X_G)`. The
**extended phase space** is `V × T*ℝ`, where the cotangent space `T*ℝ = ℝ × ℝ` of the time axis
has coordinates the time `t` and its conjugate momentum `e`, and carries the form `dt ∧ de`. Its
symplectic form is the direct sum `ω ⊕ (dt ∧ de)` (`TauCeti.SymplecticForm.extended`). When `V` is
the linear cotangent space of a configuration space `Q`, this is the linear model of the cotangent
space of `Q × ℝ`. The **extended Hamiltonian** is the autonomous Hamiltonian

`K(x, t, e) = e + H(t, x)`

(`TauCeti.extendedHamiltonian`). Where `H` is differentiable, its Hamiltonian vector field is
`X_K(x, t, e) = (X_{H_t}(x), 1, -∂_t H(t, x))`
(`TauCeti.SymplecticForm.hamiltonianVectorField_extendedHamiltonian`): along the flow of `K` the
time advances at unit speed, the point of `V` moves by the time-dependent Hamiltonian vector field,
and the momentum `e` of the time absorbs the change of energy. Accordingly:

* the time and the point of an integral curve of `X_K` form a solution of the nonautonomous
  equation `x' = X_{H_t}(x)`, in the form of an integral curve of the suspended field
  `TauCeti.SymplecticForm.timeDependentHamiltonianSuspension`
  (`TauCeti.SymplecticForm.hasDerivAt_timeDependentHamiltonianSuspension_of_hasDerivAt_extended`);
* conversely every solution `x` of the nonautonomous equation lifts to the integral curve
  `s ↦ (x s, s, c - H(s, x s))` of `X_K`, on which `K` has the constant value `c`
  (`TauCeti.SymplecticForm.hasDerivAt_extended_hamiltonianVectorField_of_hasDerivAt`).

A time-dependent function `F(t, x)` becomes an autonomous function on the extended phase space,
and its Poisson bracket with `K` there is `∂_t F + {F, H}`
(`TauCeti.SymplecticForm.extended_poissonBracket_extendedHamiltonian`). This is also the derivative
of `F` along any solution of the nonautonomous equation
(`TauCeti.SymplecticForm.hasDerivAt_apply_of_hasDerivAt_hamiltonianVectorField`, in
`TauCeti.Geometry.Symplectic.Hamiltonian.TimeDependent`), which characterises the conserved
quantities of the time-dependent evolution
(`TauCeti.SymplecticForm.forall_apply_timeDependentHamiltonianFlow_eq_iff`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 45.
* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in
  Applied Mathematics 17, Springer, 1999, Sections 5.5 and 8.1.
-/

public section

namespace TauCeti

open Function ContinuousLinearMap

variable {V : Type*}

/-- The **extended Hamiltonian** `K(x, t, e) = e + H(t, x)` of a time-dependent Hamiltonian `H`
on the extended phase space `V × T*ℝ`, whose last two coordinates are the time `t` and its
conjugate momentum `e`. -/
def extendedHamiltonian (H : ℝ → V → ℝ) (y : V × (ℝ × ℝ)) : ℝ :=
  y.2.2 + H y.2.1 y.1

@[simp]
theorem extendedHamiltonian_apply (H : ℝ → V → ℝ) (y : V × (ℝ × ℝ)) :
    extendedHamiltonian H y = y.2.2 + H y.2.1 y.1 :=
  (rfl)

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The derivative of the extended Hamiltonian:
`dK(x, t, e) = de + ∂_t H(t, x) dt + d(H t)(x) dx`. -/
theorem hasFDerivAt_extendedHamiltonian {H : ℝ → V → ℝ} {t : ℝ} {x : V}
    (hH : DifferentiableAt ℝ (uncurry H) (t, x)) (e : ℝ) :
    HasFDerivAt (extendedHamiltonian H)
      ((snd ℝ ℝ ℝ).comp (snd ℝ V (ℝ × ℝ)) +
        (timeFDeriv (uncurry H) t x • (fst ℝ ℝ ℝ).comp (snd ℝ V (ℝ × ℝ)) +
          (fderiv ℝ (H t) x).comp (fst ℝ V (ℝ × ℝ)))) (x, (t, e)) :=
  ((snd ℝ ℝ ℝ).comp (snd ℝ V (ℝ × ℝ))).hasFDerivAt.add (hasFDerivAt_apply_snd_fst hH e)

/-- The derivative of the extended Hamiltonian, evaluated on a tangent vector:
`dK(x, t, e)(δx, δt, δe) = δe + ∂_t H(t, x) δt + d(H t)(x) δx`. -/
theorem fderiv_extendedHamiltonian_apply {H : ℝ → V → ℝ} {t : ℝ} {x : V}
    (hH : DifferentiableAt ℝ (uncurry H) (t, x)) (e : ℝ) (w : V × (ℝ × ℝ)) :
    fderiv ℝ (extendedHamiltonian H) (x, (t, e)) w =
      w.2.2 + timeFDeriv (uncurry H) t x * w.2.1 + fderiv ℝ (H t) x w.1 := by
  rw [(hasFDerivAt_extendedHamiltonian hH e).fderiv]
  simp [add_assoc]

namespace SymplecticForm

/-- The symplectic form `ω ⊕ (dt ∧ de)` of the **extended phase space** `V × T*ℝ` of `(V, ω)`. -/
noncomputable def extended (ω : SymplecticForm V) : SymplecticForm (V × (ℝ × ℝ)) :=
  ω.prod stdSymplecticForm

@[simp]
theorem extended_apply (ω : SymplecticForm V) (a b : V × (ℝ × ℝ)) :
    ω.extended a b = ω a.1 b.1 + (a.2.1 * b.2.2 - a.2.2 * b.2.1) := by
  simp [extended, mul_comm]

variable [FiniteDimensional ℝ V]

/-- **The extended Hamiltonian vector field.** Where `H` is differentiable, the Hamiltonian vector
field of `K(x, t, e) = e + H(t, x)` on the extended phase space is
`X_K(x, t, e) = (X_{H_t}(x), 1, -∂_t H(t, x))`. -/
theorem hamiltonianVectorField_extendedHamiltonian (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    {t : ℝ} {x : V} (hH : DifferentiableAt ℝ (uncurry H) (t, x)) (e : ℝ) :
    ω.extended.hamiltonianVectorField (extendedHamiltonian H) (x, (t, e)) =
      (ω.hamiltonianVectorField (H t) x, (1, -timeFDeriv (uncurry H) t x)) := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro w
  rw [fderiv_extendedHamiltonian_apply hH, extended_apply, apply_hamiltonianVectorField]
  ring

/-- **Integral curves of the extended Hamiltonian solve the nonautonomous equation.** If `y` is an
integral curve at `s` of the extended Hamiltonian vector field, then its time and point
`s ↦ (t(s), x(s))` form an integral curve at `s` of the suspended time-dependent Hamiltonian
vector field `(t, x) ↦ (1, X_{H_t}(x))`. -/
theorem hasDerivAt_timeDependentHamiltonianSuspension_of_hasDerivAt_extended
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {y : ℝ → V × (ℝ × ℝ)} {s : ℝ}
    (hH : DifferentiableAt ℝ (uncurry H) ((y s).2.1, (y s).1))
    (hy : HasDerivAt y (ω.extended.hamiltonianVectorField (extendedHamiltonian H) (y s)) s) :
    HasDerivAt (fun u ↦ ((y u).2.1, (y u).1))
      (ω.timeDependentHamiltonianSuspension H ((y s).2.1, (y s).1)) s := by
  -- Expose the coordinates `(x, (t, e))` of `y s`, so that the vector field formula applies.
  rw [← Prod.mk.eta (p := y s), ← Prod.mk.eta (p := (y s).2),
    hamiltonianVectorField_extendedHamiltonian ω hH] at hy
  rw [timeDependentHamiltonianSuspension_apply]
  exact ((hasFDerivAt_fst.comp_hasDerivAt s (hasFDerivAt_snd.comp_hasDerivAt s hy))).prodMk
    (hasFDerivAt_fst.comp_hasDerivAt s hy)

/-- **Solutions of the nonautonomous equation lift to the extended phase space.** If `x` solves
`x' = X_{H_s}(x)` at `s`, and `H` is differentiable at `(s, x s)`, then for every constant `c` the
curve `u ↦ (x u, u, c - H(u, x u))`, on which the extended Hamiltonian takes the value `c`, is an
integral curve at `s` of the extended Hamiltonian vector field. -/
theorem hasDerivAt_extended_hamiltonianVectorField_of_hasDerivAt (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} {x : ℝ → V} {s : ℝ} (hH : DifferentiableAt ℝ (uncurry H) (s, x s))
    (hx : HasDerivAt x (ω.hamiltonianVectorField (H s) (x s)) s) (c : ℝ) :
    HasDerivAt (fun u ↦ (x u, (u, c - H u (x u))))
      (ω.extended.hamiltonianVectorField (extendedHamiltonian H) (x s, (s, c - H s (x s)))) s := by
  rw [hamiltonianVectorField_extendedHamiltonian ω hH]
  have hE : HasDerivAt (fun u ↦ c - H u (x u)) (-timeFDeriv (uncurry H) s (x s)) s := by
    simpa using (ω.hasDerivAt_apply_of_hasDerivAt_hamiltonianVectorField_self hH hx).const_sub c
  exact hx.prodMk ((hasDerivAt_id s).prodMk hE)

/-- **The bracket with the extended Hamiltonian is the total time derivative.** A time-dependent
function `F(t, x)`, viewed as an autonomous function on the extended phase space, has Poisson
bracket `∂_t F + {F_t, H_t}` with the extended Hamiltonian. -/
theorem extended_poissonBracket_extendedHamiltonian (ω : SymplecticForm V) {F H : ℝ → V → ℝ}
    {t : ℝ} {x : V} (hF : DifferentiableAt ℝ (uncurry F) (t, x))
    (hH : DifferentiableAt ℝ (uncurry H) (t, x)) (e : ℝ) :
    ω.extended.poissonBracket (fun y ↦ F y.2.1 y.1) (extendedHamiltonian H) (x, (t, e)) =
      timeFDeriv (uncurry F) t x + ω.poissonBracket (F t) (H t) x := by
  rw [poissonBracket_eq_fderiv, hamiltonianVectorField_extendedHamiltonian ω hH,
    (hasFDerivAt_apply_snd_fst hF e).fderiv, poissonBracket_eq_fderiv]
  simp

end SymplecticForm

end TauCeti
