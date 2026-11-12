/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Covariance of the Euler–Lagrange equations under changes of coordinates

Let `E` and `F` be real normed spaces, the configuration spaces of a mechanical system in two sets
of coordinates, and let `φ : E → F` be a change of coordinates. A point `(q, v)` of the velocity
phase space `E × E` is carried to `(φ q, Dφ_q v)` by the tangent map of `φ`. Let `L : ℝ → E × E → ℝ`
and `L' : ℝ → F × F → ℝ` be possibly time-dependent Lagrangians describing the same system in the
two coordinates, so that

`L(t, q, v) = L'(t, φ q, Dφ_q v)`

near the points considered. A curve `q` with velocity field `v` solves the **Euler–Lagrange
equations** of `L` when `d/dt ∂_v L(t, q, v) = ∂_q L(t, q, v)`, in the form of the hypothesis of
Noether's theorem `TauCeti.hasDerivAt_noetherCharge`. This file proves that these equations do
not depend on the coordinates.

The momentum is a covector that transforms by the derivative of `φ`,
`∂_v L(t, q, v) = ∂_v L'(t, φ q, Dφ_q v) ∘ Dφ_q` (`TauCeti.momentum_eq_comp_of_comp`), while the
force picks up a second-order term,

`∂_q L(t, q, v) = ∂_q L'(t, φ q, Dφ_q v) ∘ Dφ_q + ∂_v L'(t, φ q, Dφ_q v) ∘ D²φ_q(·, v)`

(`TauCeti.force_eq_of_comp`). Differentiating the momentum along the curve produces the same
second-order term `∂_v L' ∘ D²φ_q(v, ·)`, and for a `C²` change of coordinates the two agree by
the symmetry of second derivatives. Hence the **Euler–Lagrange expression** `p' - ∂_q L` is a
covector along the curve that transforms by `Dφ_q`
(`TauCeti.hasDerivAt_momentum_of_comp`):

`d/dt ∂_v L(t, q, v) - ∂_q L(t, q, v) =`
`  (d/dt ∂_v L'(t, φ q, Dφ_q v) - ∂_q L'(t, φ q, Dφ_q v)) ∘ Dφ_q`.

Consequently, if the image curve `φ ∘ q` with velocity field `Dφ_q v` solves the Euler–Lagrange
equations of `L'`, then `q` solves those of `L` (`TauCeti.eulerLagrange_of_comp`), for an arbitrary
`C²` map `φ`. When `Dφ_q` is invertible, as for the transition maps between charts of a manifold,
the converse holds (`TauCeti.eulerLagrange_iff_of_comp`): `q` solves the Euler–Lagrange equations
of `L` at a time exactly when `φ ∘ q` solves those of `L'` there. For a curve that is
differentiable near that time, the same holds with the velocities `q'` and `(φ ∘ q)'`
(`TauCeti.eulerLagrange_deriv_iff_of_comp`), which is the form of the equations in Hamilton's
principle `TauCeti.isActionStationary_iff_eulerLagrange`.

All statements are pointwise in time, and the relation between `L` and `L'` is only needed near
the curve, so they apply equally to local solutions and to local changes of coordinates.

## Main results

* `TauCeti.momentum_eq_comp_of_comp`, `TauCeti.force_eq_of_comp`: the transformation laws of the
  momentum and of the force.
* `TauCeti.hasDerivAt_momentum_of_comp`: the Euler–Lagrange expression transforms by `Dφ_q`.
* `TauCeti.eulerLagrange_of_comp`, `TauCeti.eulerLagrange_iff_of_comp`,
  `TauCeti.eulerLagrange_deriv_iff_of_comp`: invariance of the Euler–Lagrange equations under
  changes of configuration coordinates.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 12.
* I. M. Gelfand, S. V. Fomin, *Calculus of Variations*, Prentice–Hall, 1963, Section 6 (the
  invariance of Euler's equation).
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### Momentum and force -/

/-- **The momentum transforms as a covector.** Let `φ : E → F` be a map of configuration spaces,
and let `ℓ` and `ℓ'` be Lagrangians on `E` and `F` with `ℓ(q, u) = ℓ'(φ q, Dφ_q u)` for velocities
`u` near `v`, where `u ↦ ℓ'(φ q, u)` is differentiable at `Dφ_q v`. Then the momentum of `ℓ` at
`(q, v)` is the momentum of `ℓ'` at `(φ q, Dφ_q v)` composed with `Dφ_q`. -/
theorem momentum_eq_comp_of_comp {ℓ : E × E → ℝ} {ℓ' : F × F → ℝ} {φ : E → F} {x : E × E}
    (hL : (fun u ↦ ℓ (x.1, u)) =ᶠ[𝓝 x.2] fun u ↦ ℓ' (φ x.1, fderiv ℝ φ x.1 u))
    (hL' : DifferentiableAt ℝ (fun u ↦ ℓ' (φ x.1, u)) (fderiv ℝ φ x.1 x.2)) :
    fderiv ℝ (fun u ↦ ℓ (x.1, u)) x.2 =
      (fderiv ℝ (fun u ↦ ℓ' (φ x.1, u)) (fderiv ℝ φ x.1 x.2)).comp (fderiv ℝ φ x.1) := by
  rw [hL.fderiv_eq]
  exact (hL'.hasFDerivAt.comp x.2 (fderiv ℝ φ x.1).hasFDerivAt).fderiv

/-- **The transformation law of the force.** Let `φ : E → F` be differentiable at `q`, with
`Dφ` differentiable at `q`, and let `ℓ` and `ℓ'` be Lagrangians on `E` and `F` with
`ℓ(y, v) = ℓ'(φ y, Dφ_y v)` for positions `y` near `q`, where `ℓ'` is differentiable at
`(φ q, Dφ_q v)`. Then the force of `ℓ` at `(q, v)` is

`∂_q ℓ(q, v) = ∂_q ℓ'(φ q, Dφ_q v) ∘ Dφ_q + ∂_v ℓ'(φ q, Dφ_q v) ∘ D²φ_q(·, v)`. -/
theorem force_eq_of_comp {ℓ : E × E → ℝ} {ℓ' : F × F → ℝ} {φ : E → F} {x : E × E}
    (hL : (fun y ↦ ℓ (y, x.2)) =ᶠ[𝓝 x.1] fun y ↦ ℓ' (φ y, fderiv ℝ φ y x.2))
    (hL' : DifferentiableAt ℝ ℓ' (φ x.1, fderiv ℝ φ x.1 x.2)) (hφ : DifferentiableAt ℝ φ x.1)
    (hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x.1) :
    fderiv ℝ (fun y ↦ ℓ (y, x.2)) x.1 =
      (fderiv ℝ (fun y ↦ ℓ' (y, fderiv ℝ φ x.1 x.2)) (φ x.1)).comp (fderiv ℝ φ x.1) +
        (fderiv ℝ (fun u ↦ ℓ' (φ x.1, u)) (fderiv ℝ φ x.1 x.2)).comp
          ((fderiv ℝ (fderiv ℝ φ) x.1).flip x.2) := by
  -- The map `y ↦ (φ y, Dφ_y v)` has derivative `a ↦ (Dφ_q a, D²φ_q a v)` at `q`.
  have hT : HasFDerivAt (fun y ↦ (φ y, fderiv ℝ φ y x.2))
      ((fderiv ℝ φ x.1).prod ((fderiv ℝ (fderiv ℝ φ) x.1).flip x.2)) x.1 :=
    hφ.hasFDerivAt.prodMk ((hDφ.hasFDerivAt.clm_apply (hasFDerivAt_const x.2 x.1)).congr_fderiv
      (by simp))
  have hd : HasFDerivAt (fun y ↦ ℓ' (φ y, fderiv ℝ φ y x.2))
      ((fderiv ℝ ℓ' (φ x.1, fderiv ℝ φ x.1 x.2)).comp
        ((fderiv ℝ φ x.1).prod ((fderiv ℝ (fderiv ℝ φ) x.1).flip x.2))) x.1 :=
    hL'.hasFDerivAt.comp x.1 hT
  rw [hL.fderiv_eq, hd.fderiv]
  ext a
  simp [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hL']

/-! ### The Euler–Lagrange expression -/

variable {L : ℝ → E × E → ℝ} {L' : ℝ → F × F → ℝ} {φ : E → F} {q v : ℝ → E} {t : ℝ}

/-- **The Euler–Lagrange expression transforms as a covector.** Let `q` have velocity `v t` at `t`,
let `φ : E → F` be `C²` at `q t`, and let the Lagrangians be related by
`L(s, y, u) = L'(s, φ y, Dφ_y u)` near `(q s, v s)` for times `s` near `t`, with `L' s`
differentiable at `(φ (q s), Dφ_{q s} (v s))`. If the momentum `∂_v L'` along the image curve
`(φ ∘ q, Dφ_q v)` has derivative `P` at `t`, then the momentum `∂_v L` along `(q, v)` has
derivative `∂_q L(t, q, v) + (P - ∂_q L'(t, φ q, Dφ_q v)) ∘ Dφ_q` at `t`. -/
theorem hasDerivAt_momentum_of_comp (hq : HasDerivAt q (v t) t) (hφ : ContDiffAt ℝ 2 φ (q t))
    (hL : ∀ᶠ s in 𝓝 t, L s =ᶠ[𝓝 (q s, v s)] fun y ↦ L' s (φ y.1, fderiv ℝ φ y.1 y.2))
    (hL' : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (L' s) (φ (q s), fderiv ℝ φ (q s) (v s)))
    {P : StrongDual ℝ F}
    (hp : HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (fderiv ℝ φ (q s) (v s))) P t) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L s (q s, u)) (v s))
      (fderiv ℝ (fun y ↦ L t (y, v t)) (q t) +
        (P - fderiv ℝ (fun y ↦ L' t (y, fderiv ℝ φ (q t) (v t))) (φ (q t))).comp
          (fderiv ℝ φ (q t))) t := by
  have hφd : DifferentiableAt ℝ φ (q t) := hφ.differentiableAt (by norm_num)
  have hDφ : DifferentiableAt ℝ (fderiv ℝ φ) (q t) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℝ φ (q t) := hφ.isSymmSndFDerivAt (by simp)
  -- Near `t`, the momentum of `L` is that of `L'` composed with `Dφ_{q s}`.
  have hmom : (fun s ↦ fderiv ℝ (fun u ↦ L s (q s, u)) (v s)) =ᶠ[𝓝 t] fun s ↦
      (fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (fderiv ℝ φ (q s) (v s))).comp
        (fderiv ℝ φ (q s)) := by
    filter_upwards [hL, hL'] with s hs hs'
    exact momentum_eq_comp_of_comp (ℓ := L s) (ℓ' := L' s) (φ := φ) (x := (q s, v s))
      (hs.comp_tendsto (tendsto_const_nhds.prodMk_nhds tendsto_id))
      (hs'.comp (fderiv ℝ φ (q s) (v s)) (hasFDerivAt_prodMk_right _ _).differentiableAt)
  have hA : HasDerivAt (fun s ↦ fderiv ℝ φ (q s)) (fderiv ℝ (fderiv ℝ φ) (q t) (v t)) t :=
    hDφ.hasFDerivAt.comp_hasDerivAt t hq
  have hforce := force_eq_of_comp (ℓ := L t) (ℓ' := L' t) (φ := φ) (x := (q t, v t))
    (hL.self_of_nhds.comp_tendsto (tendsto_id.prodMk_nhds tendsto_const_nhds))
    hL'.self_of_nhds hφd hDφ
  refine ((hp.clm_comp hA).congr_of_eventuallyEq hmom).congr_deriv ?_
  rw [hforce]
  ext w
  simp [hsymm (v t) w]
  ring

/-- **Euler–Lagrange equations pull back along changes of coordinates.** Let `q` have velocity
`v t` at `t`, let `φ : E → F` be `C²` at `q t`, and let the Lagrangians be related by
`L(s, y, u) = L'(s, φ y, Dφ_y u)` near `(q s, v s)` for times `s` near `t`, with `L' s`
differentiable at `(φ (q s), Dφ_{q s} (v s))`. If the image curve `φ ∘ q` with velocity field
`Dφ_q v` satisfies the Euler–Lagrange equation of `L'` at `t`, then `q` with velocity field `v`
satisfies the Euler–Lagrange equation of `L` at `t`. No invertibility of `Dφ` is needed. -/
theorem eulerLagrange_of_comp (hq : HasDerivAt q (v t) t) (hφ : ContDiffAt ℝ 2 φ (q t))
    (hL : ∀ᶠ s in 𝓝 t, L s =ᶠ[𝓝 (q s, v s)] fun y ↦ L' s (φ y.1, fderiv ℝ φ y.1 y.2))
    (hL' : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (L' s) (φ (q s), fderiv ℝ φ (q s) (v s)))
    (hEL : HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (fderiv ℝ φ (q s) (v s)))
      (fderiv ℝ (fun y ↦ L' t (y, fderiv ℝ φ (q t) (v t))) (φ (q t))) t) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L s (q s, u)) (v s))
      (fderiv ℝ (fun y ↦ L t (y, v t)) (q t)) t := by
  simpa using hasDerivAt_momentum_of_comp hq hφ hL hL' hEL

/-- **Invariance of the Euler–Lagrange equations under changes of coordinates.** Let `q` have
velocity `v t` at `t`, and let `φ : E → F` be `C²` at `q t` with invertible derivative there, as
for the transition map between two charts of a manifold. Let the Lagrangians be related by
`L(s, y, u) = L'(s, φ y, Dφ_y u)` near `(q s, v s)` for times `s` near `t`, with `L' s`
differentiable at `(φ (q s), Dφ_{q s} (v s))`. Then `q` with velocity field `v` satisfies the
Euler–Lagrange equation of `L` at `t` exactly when `φ ∘ q` with velocity field `Dφ_q v` satisfies
the Euler–Lagrange equation of `L'` at `t`. -/
theorem eulerLagrange_iff_of_comp [CompleteSpace E] (hq : HasDerivAt q (v t) t)
    (hφ : ContDiffAt ℝ 2 φ (q t)) (hinv : (fderiv ℝ φ (q t)).IsInvertible)
    (hL : ∀ᶠ s in 𝓝 t, L s =ᶠ[𝓝 (q s, v s)] fun y ↦ L' s (φ y.1, fderiv ℝ φ y.1 y.2))
    (hL' : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (L' s) (φ (q s), fderiv ℝ φ (q s) (v s))) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L s (q s, u)) (v s))
        (fderiv ℝ (fun y ↦ L t (y, v t)) (q t)) t ↔
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (fderiv ℝ φ (q s) (v s)))
        (fderiv ℝ (fun y ↦ L' t (y, fderiv ℝ φ (q t) (v t))) (φ (q t))) t := by
  refine ⟨fun hEL ↦ ?_, eulerLagrange_of_comp hq hφ hL hL'⟩
  have hDφ : DifferentiableAt ℝ (fderiv ℝ φ) (q t) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : HasDerivAt (fun s ↦ fderiv ℝ φ (q s)) (fderiv ℝ (fderiv ℝ φ) (q t) (v t)) t :=
    hDφ.hasFDerivAt.comp_hasDerivAt t hq
  -- Near `t`, `Dφ_{q s}` stays invertible, and the momentum of `L'` is that of `L` composed with
  -- its inverse; so it is differentiable at `t`.
  have hinvs : ∀ᶠ s in 𝓝 t, (fderiv ℝ φ (q s)).IsInvertible :=
    hA.continuousAt.eventually hinv.eventually_nhds
  have hmom : (fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (fderiv ℝ φ (q s) (v s))) =ᶠ[𝓝 t]
      fun s ↦ (fderiv ℝ (fun u ↦ L s (q s, u)) (v s)).comp (fderiv ℝ φ (q s)).inverse := by
    filter_upwards [hL, hL', hinvs] with s hs hs' hs''
    rw [momentum_eq_comp_of_comp (ℓ := L s) (ℓ' := L' s) (φ := φ) (x := (q s, v s))
      (hs.comp_tendsto (tendsto_const_nhds.prodMk_nhds tendsto_id))
      (hs'.comp (fderiv ℝ φ (q s) (v s)) (hasFDerivAt_prodMk_right _ _).differentiableAt),
      comp_assoc, hs''.self_comp_inverse, comp_id]
  have hinvd : HasDerivAt (fun s ↦ (fderiv ℝ φ (q s)).inverse)
      (fderiv ℝ inverse (fderiv ℝ φ (q t)) (fderiv ℝ (fderiv ℝ φ) (q t) (v t))) t :=
    HasFDerivAt.comp_hasDerivAt (l := inverse) t
      ((hinv.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).hasFDerivAt hA
  obtain ⟨P, hP⟩ : ∃ P, HasDerivAt
      (fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (fderiv ℝ φ (q s) (v s))) P t :=
    ⟨_, (hEL.clm_comp hinvd).congr_of_eventuallyEq hmom⟩
  -- By the transformation law, `(P - ∂_q L') ∘ Dφ_q = 0`, and `Dφ_q` is surjective.
  have hzero := (hasDerivAt_momentum_of_comp hq hφ hL hL' hP).unique hEL
  rw [add_eq_left] at hzero
  obtain ⟨e, he⟩ := hinv
  have hP' : P = fderiv ℝ (fun y ↦ L' t (y, fderiv ℝ φ (q t) (v t))) (φ (q t)) := by
    refine sub_eq_zero.1 (ContinuousLinearMap.ext fun w ↦ ?_)
    simpa [← he] using congrArg (fun f ↦ f (e.symm w)) hzero
  exact hP' ▸ hP

/-- **Invariance of the Euler–Lagrange equations, with the velocities of the curves.** Let `q` be
differentiable near `t`, and let `φ : E → F` be `C²` at `q t` with invertible derivative there.
Let the Lagrangians be related by `L(s, y, u) = L'(s, φ y, Dφ_y u)` near `(q s, q'(s))` for times
`s` near `t`, with `L' s` differentiable at `(φ (q s), (φ ∘ q)'(s))`. Then `q` satisfies the
Euler–Lagrange equation `d/dt ∂_v L(t, q, q') = ∂_q L(t, q, q')` at `t` exactly when `φ ∘ q`
satisfies `d/dt ∂_v L'(t, φ ∘ q, (φ ∘ q)') = ∂_q L'(t, φ ∘ q, (φ ∘ q)')` at `t`. -/
theorem eulerLagrange_deriv_iff_of_comp [CompleteSpace E] (hq : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ q s)
    (hφ : ContDiffAt ℝ 2 φ (q t)) (hinv : (fderiv ℝ φ (q t)).IsInvertible)
    (hL : ∀ᶠ s in 𝓝 t, L s =ᶠ[𝓝 (q s, deriv q s)] fun y ↦ L' s (φ y.1, fderiv ℝ φ y.1 y.2))
    (hL' : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (L' s) (φ (q s), deriv (fun r ↦ φ (q r)) s)) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L s (q s, u)) (deriv q s))
        (fderiv ℝ (fun y ↦ L t (y, deriv q t)) (q t)) t ↔
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (deriv (fun r ↦ φ (q r)) s))
        (fderiv ℝ (fun y ↦ L' t (y, deriv (fun r ↦ φ (q r)) t)) (φ (q t))) t := by
  -- Near `t`, the velocity of `φ ∘ q` is `Dφ_q q'`.
  have hφq : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ φ (q s) :=
    hq.self_of_nhds.continuousAt.eventually
      ((hφ.eventually (by simp)).mono fun _ h ↦ h.differentiableAt (by norm_num))
  have hvel : ∀ᶠ s in 𝓝 t, deriv (fun r ↦ φ (q r)) s = fderiv ℝ φ (q s) (deriv q s) := by
    filter_upwards [hq, hφq] with s hs hs'
    exact (hs'.hasFDerivAt.comp_hasDerivAt s hs.hasDerivAt).deriv
  have hmom : (fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (deriv (fun r ↦ φ (q r)) s)) =ᶠ[𝓝 t]
      fun s ↦ fderiv ℝ (fun u ↦ L' s (φ (q s), u)) (fderiv ℝ φ (q s) (deriv q s)) :=
    hvel.mono fun s hs ↦ congrArg (fderiv ℝ fun u ↦ L' s (φ (q s), u)) hs
  rw [hmom.hasDerivAt_iff, hvel.self_of_nhds]
  exact eulerLagrange_iff_of_comp hq.self_of_nhds.hasDerivAt hφ hinv hL
    (hL'.and hvel |>.mono fun s ⟨h, h'⟩ ↦ h' ▸ h)

end TauCeti
