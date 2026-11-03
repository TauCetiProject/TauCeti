/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
import TauCeti.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Euler–Lagrange equations and Hamilton's equations

Let `E` be a real normed space, the configuration space of a mechanical system, and let
`L : E × E → ℝ` be a Lagrangian, a function of positions `q` and velocities `v`. Its
**Legendre map** `FL(q, v) = (q, ∂_v L(q, v))` (`TauCeti.linearLegendreMap`) takes values in the
linear cotangent space `E × E'`, with `E'` the continuous dual, which carries the canonical
symplectic form `ω((q, p), (q', p')) = p'(q) - p(q')`
(`TauCeti.strongDualCotangentSymplecticForm`). This is the bundle-chart description of the
Legendre map `TM → T*M` of a Lagrangian on a manifold (`TauCeti.legendreMap`), whose charts
identify the canonical symplectic form of `T*M` with this linear one.

Suppose the momentum `p = ∂_v L(q, v)` can be solved for the velocity, by a map `w` with
`∂_v L(q, w(q, p)) = p`; for a hyperregular Lagrangian, whose Legendre map is a bijection,
`w(q, p)` is the velocity component of `FL⁻¹(q, p)`. The **Hamiltonian** of `L` is then

`H(q, p) = p(w(q, p)) - L(q, w(q, p))` (`TauCeti.legendreHamiltonian`),

the energy `E_L(q, v) = ∂_v L(q, v)(v) - L(q, v)` expressed in the momentum
(`TauCeti.legendreHamiltonian_linearLegendreMap`). At a point where `w` and `L` are
differentiable and `w` solves for the velocity, the derivative of `w` drops out of the derivative
of `H`, which is `(δq, δp) ↦ -∂_q L(q, w) δq + δp(w)`
(`TauCeti.hasFDerivAt_legendreHamiltonian`). These results, and energy conservation below, hold
for an arbitrary real normed space `E`. The Hamiltonian vector field and the trajectory results
that follow assume in addition that `E` is finite-dimensional, as the Hamiltonian vector field
API on `E × E'` does. With the convention `ι_{X_H} ω = dH`, the Hamiltonian vector field of `H` is
therefore

`X_H(q, p) = (w(q, p), ∂_q L(q, w(q, p)))`

(`TauCeti.hamiltonianVectorField_legendreHamiltonian`): Hamilton's equations `q' = ∂_p H`,
`p' = -∂_q H` read `q' = w(q, p)` and `p' = ∂_q L(q, w(q, p))`.

For finite-dimensional `E`, this gives the equivalence of the Lagrangian and Hamiltonian
descriptions of the motion. A curve `q` with velocity `v` satisfies the **Euler–Lagrange
equations**

`d/dt ∂_v L(q, v) = ∂_q L(q, v)`

exactly when its Legendre lift `t ↦ FL(q t, v t)` is an integral curve of `X_H`
(`TauCeti.hasDerivAt_linearLegendreMap_iff`). Conversely, the first equation of Hamilton is the
**second-order property**: along an integral curve of `X_H` the position moves with the velocity
`w(q, p)` (`TauCeti.hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField`). Hence, if `w` solves
the momentum for the velocity along an integral curve `γ = (q, p)` of `X_H` near a time `t`, then
the velocity field `v = w ∘ γ` satisfies `q'(t) = v(t)`, the Legendre lift `FL(q t, v t)` is
`γ t`, and the Euler–Lagrange equation for `q` and `v` holds at `t`
(`TauCeti.eulerLagrange_of_hasDerivAt_hamiltonianVectorField`). The energy `E_L`, which
is `H` along the Legendre lift, is conserved along every solution of the Euler–Lagrange equations
with differentiable velocity (`TauCeti.energy_eq_of_eulerLagrange`); this needs neither an
inverse `w` nor finite dimensionality.

No convexity or global invertibility of the Legendre map is assumed: all statements are pointwise
along the curve, so they apply equally to a local inverse of the Legendre map of a regular
Lagrangian.

For the Lagrangian `L(q, v) = (m / 2) ‖v‖² - U(q)` of a particle of nonzero mass `m` in a
potential `U` on an inner product space, the momentum is `m ⟪v, ·⟫`, the velocity is recovered as
`m⁻¹ p♯` from the Riesz representative `p♯` of `p`, and the Hamiltonian is the total energy
`‖p‖² / (2 m) + U(q)` (`TauCeti.legendreHamiltonian_kinetic_sub_potential`).

## Main definitions

* `TauCeti.linearLegendreMap L`: the Legendre map `(q, v) ↦ (q, ∂_v L(q, v))`.
* `TauCeti.legendreHamiltonian L w`: the Hamiltonian `(q, p) ↦ p(w(q, p)) - L(q, w(q, p))`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 12, 14 and 15.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 7.3 and 7.4.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The Legendre map and the Hamiltonian -/

/-- The **Legendre map** of a Lagrangian `L : E × E → ℝ` on a linear configuration space,
`(q, v) ↦ (q, ∂_v L(q, v))`, with values in the linear cotangent space `E × E'`. -/
noncomputable def linearLegendreMap (L : E × E → ℝ) (x : E × E) : E × StrongDual ℝ E :=
  (x.1, fderiv ℝ (fun v ↦ L (x.1, v)) x.2)

@[simp]
theorem linearLegendreMap_fst (L : E × E → ℝ) (x : E × E) : (linearLegendreMap L x).1 = x.1 :=
  (rfl)

@[simp]
theorem linearLegendreMap_snd (L : E × E → ℝ) (x : E × E) :
    (linearLegendreMap L x).2 = fderiv ℝ (fun v ↦ L (x.1, v)) x.2 :=
  (rfl)

/-- The **Hamiltonian** of a Lagrangian `L`, given a map `w` solving the momentum for the velocity:
`H(q, p) = p(w(q, p)) - L(q, w(q, p))`. When `∂_v L(q, w(q, p)) = p`, this is the energy of `L`
at the velocity `w(q, p)` (`TauCeti.legendreHamiltonian_linearLegendreMap`). -/
noncomputable def legendreHamiltonian (L : E × E → ℝ) (w : E × StrongDual ℝ E → E)
    (z : E × StrongDual ℝ E) : ℝ :=
  z.2 (w z) - L (z.1, w z)

theorem legendreHamiltonian_apply (L : E × E → ℝ) (w : E × StrongDual ℝ E → E)
    (z : E × StrongDual ℝ E) : legendreHamiltonian L w z = z.2 (w z) - L (z.1, w z) :=
  (rfl)

/-- On the image of the Legendre map, the Hamiltonian is the energy
`E_L(q, v) = ∂_v L(q, v)(v) - L(q, v)`, provided `w` recovers the velocity. -/
theorem legendreHamiltonian_linearLegendreMap {L : E × E → ℝ} {w : E × StrongDual ℝ E → E}
    {x : E × E} (hw : w (linearLegendreMap L x) = x.2) :
    legendreHamiltonian L w (linearLegendreMap L x) =
      fderiv ℝ (fun v ↦ L (x.1, v)) x.2 x.2 - L x := by
  simp [legendreHamiltonian_apply, hw]

/-- **The derivative of the Hamiltonian.** If `w` solves the momentum `p` for the velocity at
`z = (q, p)`, that is `∂_v L(q, w z) = p`, then the derivative of the Hamiltonian at `z` is
`(δq, δp) ↦ -∂_q L(q, w z) δq + δp(w z)`. The derivative of `w` does not contribute. -/
theorem hasFDerivAt_legendreHamiltonian {L : E × E → ℝ} {w : E × StrongDual ℝ E → E}
    {z : E × StrongDual ℝ E} (hw : DifferentiableAt ℝ w z)
    (hL : DifferentiableAt ℝ L (z.1, w z))
    (hp : fderiv ℝ (fun v ↦ L (z.1, v)) (w z) = z.2) :
    HasFDerivAt (legendreHamiltonian L w)
      ((-fderiv ℝ (fun q ↦ L (q, w z)) z.1).coprod (apply ℝ ℝ (w z))) z := by
  have h₁ := (hasFDerivAt_snd (p := z)).clm_apply hw.hasFDerivAt
  have h₂ : HasFDerivAt (fun y : E × StrongDual ℝ E ↦ L (y.1, w y))
      ((fderiv ℝ L (z.1, w z)).comp ((fst ℝ E (StrongDual ℝ E)).prod (fderiv ℝ w z))) z :=
    hL.hasFDerivAt.comp z (hasFDerivAt_fst.prodMk hw.hasFDerivAt)
  unfold legendreHamiltonian
  refine (h₁.sub h₂).congr_fderiv (ContinuousLinearMap.ext fun δ ↦ ?_)
  -- Split the derivative of `L` into its slices; the fibre slice at `w z` is `p = z.2`.
  have hr := congrArg (fun f : E →L[ℝ] ℝ ↦ f (fderiv ℝ w z δ)) (fderiv_slice_right hL)
  have hl := congrArg (fun f : E →L[ℝ] ℝ ↦ f δ.1) (fderiv_slice_left hL)
  simp only [hp, coe_comp, Function.comp_apply, inr_apply, inl_apply] at hr hl
  have hsplit : fderiv ℝ L (z.1, w z) (δ.1, fderiv ℝ w z δ) =
      fderiv ℝ L (z.1, w z) (δ.1, 0) + fderiv ℝ L (z.1, w z) (0, fderiv ℝ w z δ) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  simp only [sub_apply, add_apply, coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, coe_fst', flip_apply, coe_snd', apply_apply, coprod_apply,
    neg_apply, hsplit, ← hr, hl]
  ring

/-! ### Conservation of energy -/

/-- **Conservation of energy.** Let `q` solve the Euler–Lagrange equations with a differentiable
velocity `v` at every time, with `L` differentiable along the curve. Then the energy
`E_L(q, v) = ∂_v L(q, v)(v) - L(q, v)` is constant along the curve. -/
theorem energy_eq_of_eulerLagrange {L : E × E → ℝ} {q v : ℝ → E}
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hEL : ∀ t, HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L (q s, u)) (v s))
      (fderiv ℝ (fun y ↦ L (y, v t)) (q t)) t)
    (hL : ∀ t, DifferentiableAt ℝ L (q t, v t)) (hv : ∀ t, DifferentiableAt ℝ v t) (s t : ℝ) :
    fderiv ℝ (fun u ↦ L (q s, u)) (v s) (v s) - L (q s, v s) =
      fderiv ℝ (fun u ↦ L (q t, u)) (v t) (v t) - L (q t, v t) := by
  -- `d/dt E_L = (d/dt ∂_v L)(v) + ∂_v L(v') - ∂_q L(v) - ∂_v L(v')`, which vanishes by the
  -- Euler–Lagrange equation.
  have hderiv (r : ℝ) : HasDerivAt
      (fun s ↦ fderiv ℝ (fun u ↦ L (q s, u)) (v s) (v s) - L (q s, v s)) 0 r := by
    have hp := (hEL r).clm_apply (hv r).hasDerivAt
    have hLc := (hL r).hasFDerivAt.comp_hasDerivAt r ((hq r).prodMk (hv r).hasDerivAt)
    refine (hp.sub hLc).congr_deriv ?_
    have hsplit : fderiv ℝ L (q r, v r) (v r, deriv v r) =
        fderiv ℝ L (q r, v r) (v r, 0) + fderiv ℝ L (q r, v r) (0, deriv v r) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [hsplit, fderiv_slice_left (hL r), fderiv_slice_right (hL r)]
    simp
  exact is_const_of_deriv_eq_zero (fun r ↦ (hderiv r).differentiableAt)
    (fun r ↦ (hderiv r).deriv) s t

/-! ### Hamilton's equations

From here on `E` is finite-dimensional, as the Hamiltonian vector field API requires. -/

variable [FiniteDimensional ℝ E]

/-- **Hamilton's equations of a Lagrangian system.** If `w` solves the momentum for the velocity at
`z = (q, p)`, the Hamiltonian vector field of `H(q, p) = p(w) - L(q, w)` at `z`, for the canonical
symplectic form of `E × E'`, is `(w z, ∂_q L(q, w z))`: the position moves with the velocity `w z`,
and the momentum changes by the force `∂_q L`. -/
theorem hamiltonianVectorField_legendreHamiltonian {L : E × E → ℝ} {w : E × StrongDual ℝ E → E}
    {z : E × StrongDual ℝ E} (hw : DifferentiableAt ℝ w z)
    (hL : DifferentiableAt ℝ L (z.1, w z))
    (hp : fderiv ℝ (fun v ↦ L (z.1, v)) (w z) = z.2) :
    (strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
        (legendreHamiltonian L w) z = (w z, fderiv ℝ (fun q ↦ L (q, w z)) z.1) := by
  rw [eq_comm, SymplecticForm.eq_hamiltonianVectorField_iff,
    (hasFDerivAt_legendreHamiltonian hw hL hp).fderiv]
  intro δ
  simp only [strongDualCotangentSymplecticForm_apply, coprod_apply, neg_apply, apply_apply]
  ring

/-- **Euler–Lagrange equations versus Hamilton's equations.** Let `q` be a curve with velocity
field `v`, and suppose that `w` recovers the velocity from the Legendre lift at time `t`. Then
the Legendre lift `s ↦ FL(q s, v s)` solves Hamilton's equations at `t` exactly when `v` is the
velocity of `q` at `t` and the Euler–Lagrange equation `d/dt ∂_v L(q, v) = ∂_q L(q, v)` holds
at `t`. -/
theorem hasDerivAt_linearLegendreMap_iff {L : E × E → ℝ} {w : E × StrongDual ℝ E → E}
    {q v : ℝ → E} {t : ℝ} (hw : DifferentiableAt ℝ w (linearLegendreMap L (q t, v t)))
    (hL : DifferentiableAt ℝ L (q t, v t)) (hwv : w (linearLegendreMap L (q t, v t)) = v t) :
    HasDerivAt (fun s ↦ linearLegendreMap L (q s, v s))
        ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
          (legendreHamiltonian L w) (linearLegendreMap L (q t, v t))) t ↔
      HasDerivAt q (v t) t ∧
        HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L (q s, u)) (v s))
          (fderiv ℝ (fun y ↦ L (y, v t)) (q t)) t := by
  rw [hamiltonianVectorField_legendreHamiltonian hw (by simpa [hwv] using hL)
    (by simp [hwv])]
  simp only [linearLegendreMap_fst, hwv]
  refine ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

/-- **The second-order property.** Along an integral curve `γ = (q, p)` of the Hamiltonian vector
field of a Lagrangian system, the position `q` moves with the velocity `w(q, p)` recovered from
the momentum. -/
theorem hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField {L : E × E → ℝ}
    {w : E × StrongDual ℝ E → E} {γ : ℝ → E × StrongDual ℝ E} {t : ℝ}
    (hγ : HasDerivAt γ ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
      (legendreHamiltonian L w) (γ t)) t)
    (hw : DifferentiableAt ℝ w (γ t)) (hL : DifferentiableAt ℝ L ((γ t).1, w (γ t)))
    (hp : fderiv ℝ (fun v ↦ L ((γ t).1, v)) (w (γ t)) = (γ t).2) :
    HasDerivAt (fun s ↦ (γ s).1) (w (γ t)) t := by
  rw [hamiltonianVectorField_legendreHamiltonian hw hL hp] at hγ
  exact hγ.fst

/-- **Hamiltonian trajectories satisfy the Euler–Lagrange equation.** Let `γ` be an integral
curve of the Hamiltonian vector field of a Lagrangian system at time `t`, and let `w` solve the
momentum for the velocity along `γ` near `t`. Write `q = γ.1` for the position curve and
`v = w ∘ γ` for the velocity field recovered from the momentum. Then `q'(t) = v(t)`, the Legendre
lift `FL(q t, v t)` equals `γ t`, and the momentum `s ↦ ∂_v L(q s, v s)` has derivative
`∂_q L(q t, v t)` at `t`: the Euler–Lagrange equation `d/dt ∂_v L(q, v) = ∂_q L(q, v)` holds
at `t`. -/
theorem eulerLagrange_of_hasDerivAt_hamiltonianVectorField {L : E × E → ℝ}
    {w : E × StrongDual ℝ E → E} {γ : ℝ → E × StrongDual ℝ E} {t : ℝ}
    (hγ : HasDerivAt γ ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
      (legendreHamiltonian L w) (γ t)) t)
    (hw : DifferentiableAt ℝ w (γ t)) (hL : DifferentiableAt ℝ L ((γ t).1, w (γ t)))
    (hp : ∀ᶠ s in 𝓝 t, fderiv ℝ (fun v ↦ L ((γ s).1, v)) (w (γ s)) = (γ s).2) :
    HasDerivAt (fun s ↦ (γ s).1) (w (γ t)) t ∧
      linearLegendreMap L ((γ t).1, w (γ t)) = γ t ∧
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L ((γ s).1, u)) (w (γ s)))
        (fderiv ℝ (fun y ↦ L (y, w (γ t))) (γ t).1) t := by
  have hlift : (fun s ↦ linearLegendreMap L ((γ s).1, w (γ s))) =ᶠ[𝓝 t] γ :=
    hp.mono fun s hs ↦ Prod.ext rfl hs
  have hlift_t : linearLegendreMap L ((γ t).1, w (γ t)) = γ t := hlift.self_of_nhds
  refine ⟨hasDerivAt_fst_of_hasDerivAt_hamiltonianVectorField hγ hw hL hp.self_of_nhds,
    hlift_t, ?_⟩
  have hγ' : HasDerivAt (fun s ↦ linearLegendreMap L ((γ s).1, w (γ s)))
      ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
        (legendreHamiltonian L w) (linearLegendreMap L ((γ t).1, w (γ t)))) t := by
    rw [hlift_t]
    exact hγ.congr_of_eventuallyEq hlift
  exact ((hasDerivAt_linearLegendreMap_iff (q := fun s ↦ (γ s).1) (v := fun s ↦ w (γ s))
    (by rw [hlift_t]; exact hw) hL (by rw [hlift_t])).1 hγ').2

/-! ### Kinetic minus potential energy -/

section KineticSubPotential

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Legendre map of the Lagrangian `L(q, v) = (m / 2) ‖v‖² - U(q)` of a particle of mass `m`
in a potential `U` is `(q, v) ↦ (q, m ⟪v, ·⟫)`. -/
theorem linearLegendreMap_kinetic_sub_potential (m : ℝ) (U : F → ℝ) (x : F × F) :
    linearLegendreMap (fun y ↦ m / 2 * ‖y.2‖ ^ 2 - U y.1) x = (x.1, m • innerSL ℝ x.2) := by
  refine Prod.ext rfl ?_
  rw [linearLegendreMap_snd,
    (((hasStrictFDerivAt_norm_sq x.2).hasFDerivAt.const_mul (m / 2)).sub_const (U x.1)).fderiv]
  ext u
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

variable [CompleteSpace F]

/-- For a nonzero mass, the momentum `p = m ⟪v, ·⟫` of the Lagrangian
`L(q, v) = (m / 2) ‖v‖² - U(q)` is solved for the velocity by `v = m⁻¹ p♯`, where `p♯` is the
Riesz representative of `p`. -/
theorem linearLegendreMap_kinetic_sub_potential_toDual_symm {m : ℝ} (hm : m ≠ 0) (U : F → ℝ)
    (z : F × StrongDual ℝ F) :
    linearLegendreMap (fun y ↦ m / 2 * ‖y.2‖ ^ 2 - U y.1) (z.1, m⁻¹ • (toDual ℝ F).symm z.2) =
      z := by
  rw [linearLegendreMap_kinetic_sub_potential]
  refine Prod.ext rfl (ContinuousLinearMap.ext fun u ↦ ?_)
  simp [toDual_symm_apply, hm]

/-- The Hamiltonian of the Lagrangian `L(q, v) = (m / 2) ‖v‖² - U(q)`, for a nonzero mass `m`,
is the total energy `H(q, p) = ‖p‖² / (2 m) + U(q)`. -/
theorem legendreHamiltonian_kinetic_sub_potential {m : ℝ} (hm : m ≠ 0) (U : F → ℝ)
    (z : F × StrongDual ℝ F) :
    legendreHamiltonian (fun y ↦ m / 2 * ‖y.2‖ ^ 2 - U y.1)
        (fun z ↦ m⁻¹ • (toDual ℝ F).symm z.2) z = ‖z.2‖ ^ 2 / (2 * m) + U z.1 := by
  have hp : z.2 ((toDual ℝ F).symm z.2) = ‖z.2‖ ^ 2 := by
    rw [← toDual_symm_apply, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  rw [legendreHamiltonian_apply, map_smul, smul_eq_mul, hp, norm_smul,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

end KineticSubPotential

end TauCeti
