/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EulerLagrange
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Geodesics are the motions of the kinetic Lagrangian

Let `g : E → E →L[ℝ] E →L[ℝ] ℝ` be a field of symmetric nondegenerate bilinear forms on a
finite-dimensional real normed space `E`, as a (pseudo-)Riemannian metric reads in a chart, and
let `Γ` be its Christoffel symbols of the second kind (`TauCeti.Manifold.christoffelSecondKind`).
The **kinetic Lagrangian** of `g` (`TauCeti.kineticLagrangian`) is

`L(q, v) = g_q(v, v) / 2`.

Its momentum is the covector `∂_v L(q, v) = g_q(v, ·)`
(`TauCeti.fderiv_kineticLagrangian_snd`), and its derivative in the position is
`∂_q L(q, v)(u) = Dg_q(u)(v, v) / 2` (`TauCeti.fderiv_kineticLagrangian_fst`). Along a curve `q`
with velocity `v` and acceleration `a`, the momentum changes at the rate
`Dg_q(v)(v, ·) + g_q(a, ·)`, and `Dg_q(v)(v, ·) - ∂_q L` is the Christoffel symbol of the first
kind `Γ₁(v, v)`. So, by nondegeneracy of `g`, **the Euler–Lagrange equation of `L` is the geodesic
equation**

`a = -Γ(v, v)` (`TauCeti.eulerLagrange_kineticLagrangian_iff`).

With the inverse `w(q, p) = g_q⁻¹ p` of the Legendre map, the Hamiltonian of `L` is the kinetic
energy of covectors `H(q, p) = p(g_q⁻¹ p) / 2`
(`TauCeti.legendreHamiltonian_kineticLagrangian`), and the Euler–Lagrange equations are Hamilton's
equations for `H` (`TauCeti.hasDerivAt_linearLegendreMap_iff`). Hence **the Legendre lift
`s ↦ (q s, g_(q s)(v s, ·))` of a curve solves Hamilton's equations for the kinetic Hamiltonian
exactly when `q` solves the geodesic equation `q'' = -Γ(q', q')`**
(`TauCeti.hasDerivAt_linearLegendreMap_kineticLagrangian_iff`): in coordinates, at each time, the
geodesic equation is Hamilton's equation for the kinetic energy, transported by the Legendre map.

The Euler–Lagrange and Hamilton statements are pointwise along the curve: they assume `E`
finite-dimensional and the metric differentiable at the current position, symmetric near it and
nondegenerate there. No positivity is assumed, so pseudo-Riemannian metrics are included.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 45 (geodesics as motions of a free particle).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.5 (the geodesic spray of a metric Lagrangian).
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Topology TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → E →L[ℝ] E →L[ℝ] ℝ}

/-! ### The kinetic Lagrangian and its derivatives -/

/-- The **kinetic Lagrangian** `L(q, v) = g_q(v, v) / 2` of a field `g` of bilinear forms on `E`,
as a function on positions and velocities `E × E`. -/
noncomputable def kineticLagrangian (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E × E) : ℝ :=
  g x.1 x.2 x.2 / 2

/-- The kinetic Lagrangian is half the quadratic form of `g_q` at `v`. -/
theorem kineticLagrangian_apply (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E × E) :
    kineticLagrangian g x = g x.1 x.2 x.2 / 2 :=
  (rfl)

/-- The momentum of the kinetic Lagrangian `L(q, v) = g_q(v, v) / 2` of a symmetric bilinear form
`g_q` is the covector `g_q(v, ·)`. -/
@[simp]
theorem fderiv_kineticLagrangian_snd {q : E} (hsymm : (g q).toBilinForm.IsSymm) (v : E) :
    fderiv ℝ (fun u ↦ kineticLagrangian g (q, u)) v = g q v := by
  simp_rw [kineticLagrangian_apply, div_eq_mul_inv]
  refine (((g q).hasFDerivAt_apply_self v).mul_const (2⁻¹ : ℝ)).fderiv.trans
    (ContinuousLinearMap.ext fun w ↦ ?_)
  simp [isSymm_toBilinForm_iff.1 hsymm w v]
  ring

/-- The derivative in the position of the kinetic Lagrangian `L(q, v) = g_q(v, v) / 2` is
`u ↦ Dg_q(u)(v, v) / 2`. -/
@[simp]
theorem fderiv_kineticLagrangian_fst {q : E} (hg : DifferentiableAt ℝ g q) (v u : E) :
    fderiv ℝ (fun y ↦ kineticLagrangian g (y, v)) q u = fderiv ℝ g q u v v / 2 := by
  simp_rw [kineticLagrangian_apply, div_eq_mul_inv]
  rw [fderiv_mul_const ((hg.clm_apply (differentiableAt_const v)).clm_apply
    (differentiableAt_const v)), smul_apply, fderiv_clm_apply_const_apply₂ hg, smul_eq_mul,
    mul_comm]

/-- The kinetic Lagrangian `L(q, v) = g_q(v, v) / 2` is differentiable wherever `g` is
differentiable at the position. -/
theorem _root_.DifferentiableAt.kineticLagrangian {x : E × E} (hg : DifferentiableAt ℝ g x.1) :
    DifferentiableAt ℝ (kineticLagrangian g) x := by
  simp_rw [funext (kineticLagrangian_apply g), div_eq_mul_inv]
  have h : DifferentiableAt ℝ (fun y : E × E ↦ g y.1) x := hg.comp x differentiableAt_fst
  exact ((h.clm_apply differentiableAt_snd).clm_apply differentiableAt_snd).mul_const _

/-- The Legendre map of the kinetic Lagrangian `L(q, v) = g_q(v, v) / 2` of a symmetric bilinear
form `g_q` sends `(q, v)` to `(q, g_q(v, ·))`. -/
@[simp]
theorem linearLegendreMap_kineticLagrangian {q : E} (hsymm : (g q).toBilinForm.IsSymm) (v : E) :
    linearLegendreMap (kineticLagrangian g) (q, v) = (q, g q v) :=
  Prod.ext (linearLegendreMap_fst _ _) (by
    rw [linearLegendreMap_snd]; exact fderiv_kineticLagrangian_snd hsymm v)

/-! ### The Euler–Lagrange equation -/

variable {q v : ℝ → E} {t : ℝ} {a : E}

/-- **The Euler–Lagrange equation of the kinetic Lagrangian is the geodesic equation.** Let `q` be
a curve with velocity `v` and acceleration `a` at time `t`, and let `g` be differentiable at
`q t`, symmetric near `q t` and nondegenerate at `q t`. Then the Euler–Lagrange equation
`d/dt ∂_v L(q, v) = ∂_q L(q, v)` of `L(q, v) = g_q(v, v) / 2` holds at `t` exactly when
`a = -Γ(v, v)`. -/
theorem eulerLagrange_kineticLagrangian_iff [FiniteDimensional ℝ E]
    (hsymm : ∀ᶠ y in 𝓝 (q t), (g y).toBilinForm.IsSymm)
    (hnd : (g (q t)).toBilinForm.Nondegenerate) (hg : DifferentiableAt ℝ g (q t))
    (hq : HasDerivAt q (v t) t) (hv : HasDerivAt v a t) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ kineticLagrangian g (q s, u)) (v s))
        (fderiv ℝ (fun y ↦ kineticLagrangian g (y, v t)) (q t)) t ↔
      a = -christoffelSecondKind g (q t) (v t) (v t) := by
  -- Near `t` the momentum is `g_q(v, ·)`, which changes at the rate `Dg_q(v)(v, ·) + g_q(a, ·)`.
  have hev : (fun s ↦ fderiv ℝ (fun u ↦ kineticLagrangian g (q s, u)) (v s)) =ᶠ[𝓝 t]
      fun s ↦ g (q s) (v s) :=
    (hq.continuousAt.eventually hsymm).mono fun s hs ↦ fderiv_kineticLagrangian_snd hs (v s)
  have hgq : HasDerivAt (fun s ↦ g (q s)) (fderiv ℝ g (q t) (v t)) t :=
    hg.hasFDerivAt.comp_hasDerivAt (l := g) t hq
  have hp := hgq.clm_apply hv
  rw [hev.hasDerivAt_iff]
  refine ⟨fun h ↦ eq_neg_of_add_eq_zero_left (hnd.1 _ fun w ↦ ?_), fun ha ↦ ?_⟩
  · have hw := congrArg (fun φ : E →L[ℝ] ℝ ↦ φ w) (h.unique hp)
    simp only [fderiv_kineticLagrangian_fst hg, add_apply] at hw
    simp only [map_add, LinearMap.add_apply, ContinuousLinearMap.toBilinForm_apply,
      apply_christoffelSecondKind hnd, christoffelFirstKind_apply]
    linarith
  · convert hp using 1
    ext w
    simp only [fderiv_kineticLagrangian_fst hg, add_apply, ha, map_neg, neg_apply,
      apply_christoffelSecondKind hnd, christoffelFirstKind_apply]
    ring

/-! ### The kinetic Hamiltonian -/

/-- With the velocity recovered from the momentum by `w(q, p) = g_q⁻¹ p`, the Hamiltonian of the
kinetic Lagrangian `L(q, v) = g_q(v, v) / 2` is the kinetic energy of covectors
`H(q, p) = p(g_q⁻¹ p) / 2`. Where `g_q` is not invertible both sides vanish, since the inverse is
then zero by convention. -/
@[simp]
theorem legendreHamiltonian_kineticLagrangian (z : E × StrongDual ℝ E) :
    legendreHamiltonian (kineticLagrangian g) (fun z ↦ (g z.1).inverse z.2) z =
      z.2 ((g z.1).inverse z.2) / 2 := by
  rw [legendreHamiltonian_apply, kineticLagrangian_apply]
  by_cases h : (g z.1).IsInvertible
  · rw [h.self_apply_inverse]
    ring
  · simp [inverse_of_not_isInvertible h]

/-- **The geodesic equation is Hamilton's equation for the kinetic energy.** Let `q` be a curve,
`v` a velocity field with derivative `a` at time `t`, and let `g` be differentiable at `q t`,
symmetric near `q t` and nondegenerate at `q t`. Then the Legendre lift
`s ↦ (q s, g_(q s)(v s, ·))` solves Hamilton's equations for the kinetic Hamiltonian
`H(q, p) = p(g_q⁻¹ p) / 2` at `t` exactly when `v` is the velocity of `q` at `t` and the geodesic
equation `a = -Γ(v, v)` holds there. -/
theorem hasDerivAt_linearLegendreMap_kineticLagrangian_iff [FiniteDimensional ℝ E]
    (hsymm : ∀ᶠ y in 𝓝 (q t), (g y).toBilinForm.IsSymm)
    (hnd : (g (q t)).toBilinForm.Nondegenerate) (hg : DifferentiableAt ℝ g (q t))
    (hv : HasDerivAt v a t) :
    HasDerivAt (fun s ↦ linearLegendreMap (kineticLagrangian g) (q s, v s))
        ((strongDualCotangentSymplecticForm (V := E)).hamiltonianVectorField
          (legendreHamiltonian (kineticLagrangian g) (fun z ↦ (g z.1).inverse z.2))
          (linearLegendreMap (kineticLagrangian g) (q t, v t))) t ↔
      HasDerivAt q (v t) t ∧ a = -christoffelSecondKind g (q t) (v t) (v t) := by
  have hinv := isInvertible_of_separatingLeft hnd.1
  -- The inverse of the Legendre map is differentiable at the Legendre lift `(q, g_q(v, ·))`.
  have hz : linearLegendreMap (kineticLagrangian g) (q t, v t) = (q t, g (q t) (v t)) :=
    linearLegendreMap_kineticLagrangian hsymm.self_of_nhds (v t)
  have hw : DifferentiableAt ℝ (fun z : E × StrongDual ℝ E ↦ (g z.1).inverse z.2)
      (linearLegendreMap (kineticLagrangian g) (q t, v t)) := by
    rw [hz]
    have h₁ : DifferentiableAt ℝ (fun z : E × StrongDual ℝ E ↦ g z.1) (q t, g (q t) (v t)) :=
      hg.comp (q t, g (q t) (v t)) differentiableAt_fst
    have hi : DifferentiableAt ℝ inverse (g (q t)) :=
      (hinv.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero
    have h₂ : DifferentiableAt ℝ (inverse ∘ fun z : E × StrongDual ℝ E ↦ g z.1)
        (q t, g (q t) (v t)) :=
      DifferentiableAt.comp (g := inverse) (f := fun z : E × StrongDual ℝ E ↦ g z.1)
        (q t, g (q t) (v t)) hi h₁
    exact h₂.clm_apply differentiableAt_snd
  rw [hasDerivAt_linearLegendreMap_iff hw hg.kineticLagrangian
    (by rw [hz]; exact hinv.inverse_apply_self _)]
  exact and_congr_right fun hq ↦ eulerLagrange_kineticLagrangian_iff hsymm hnd hg hq hv

end TauCeti
