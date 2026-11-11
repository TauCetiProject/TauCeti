/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Geometry.Symplectic.Complex.Line
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Radial Hamiltonian twists of the plane

On the complex line with its standard area form `ω(z, w) = Re z Im w - Im z Re w`
(`TauCeti.stdComplexSymplecticForm`), a function of the squared distance to a point `p`,

`H(w) = -G(‖w - p‖²) / 2`  (`TauCeti.radialHamiltonian G p`),

has the Hamiltonian vector field `X_H(w) = i G'(‖w - p‖²) (w - p)`, which rotates each circle
about `p` at the constant angular speed `G'` of its squared radius. Its flow is therefore explicit:

`φ_t(w) = p + exp (i t G'(‖w - p‖²)) (w - p)`

(`TauCeti.hamiltonianFlow_radialHamiltonian`). Such a map is a *twist map*: it fixes `p`, preserves
every circle about `p` and rotates it by an angle depending on its radius.

When `G` is `C²` and vanishes on `[R, ∞)`, `H` is a compactly supported Hamiltonian, so its flow
`TauCeti.SymplecticForm.hamiltonianFlow` exists and its time maps are symplectic
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow`), that is area preserving. They are the
identity outside the disc of radius `√R` about `p` and move no point `w` by more than
`|t G'(‖w - p‖²)| ‖w - p‖`. If moreover `G' = θ` near `0`, every time-`t` map agrees near `p`
with the rotation by the angle `t θ` about `p`, and so has derivative `v ↦ exp (i t θ) v` at `p`.

A smooth `G₁` vanishing on `[R, ∞)` and equal to the identity near `0` is provided by
`ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact` applied to the identity on `(-∞, R)`.
The profiles `θ • G₁` then give, for every angle `θ`, a compactly supported Hamiltonian
perturbation of the identity, localized in a prescribed disc about `p`, whose linearization at
`p` is the rotation by `θ`. Since `G₁'` is bounded, the displacement bound shows that these
perturbations tend uniformly to the identity as `θ → 0`.

This is the local mechanism for perturbing an area-preserving map of a surface so as to change
the linearized return map of a periodic orbit by a rotation. If `p` is a periodic point of `φ`
of period `k` and the twist is supported in a disc about `p` avoiding the other points of the
orbit, the linearized return map of `φ ∘ ψ` at `p` is that of `φ` composed with the rotation
(`HasFDerivAt.iterate_comp_of_eventuallyEq_id`).

## Main definitions

* `TauCeti.radialHamiltonian G p`: the Hamiltonian `w ↦ -G(‖w - p‖²) / 2`.

## Main results

* `TauCeti.hamiltonianVectorField_radialHamiltonian`: `X_H(w) = i G'(‖w - p‖²) (w - p)`.
* `TauCeti.hamiltonianFlow_radialHamiltonian`: the flow is the twist map
  `w ↦ p + exp (i t G'(‖w - p‖²)) (w - p)`.
* `TauCeti.hamiltonianFlow_radialHamiltonian_eventuallyEq`: if `G' = θ` near `0`, the time-`t`
  map is the rotation by `t θ` near `p`, and
  `TauCeti.hasFDerivAt_hamiltonianFlow_radialHamiltonian_center` computes its derivative at `p`.
* `TauCeti.hamiltonianFlow_radialHamiltonian_eq_self_of_lt`: if `G` vanishes on `[R, ∞)`, the
  time maps are the identity outside the disc of radius `√R` about `p`.
* `TauCeti.norm_hamiltonianFlow_radialHamiltonian_sub_le`: the displacement bound
  `‖φ_t(w) - w‖ ≤ |t G'(‖w - p‖²)| ‖w - p‖`.
* `TauCeti.exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian`: a `C²` profile vanishing
  for large arguments gives a compactly supported Hamiltonian with a globally Lipschitz field.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017 (Hamiltonian flows of the standard symplectic plane).
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter Metric Topology
open scoped ContDiff

/-- The **radial Hamiltonian** `w ↦ -G(‖w - p‖²) / 2` on the complex line, a function of the
squared distance to the centre `p`. For the standard area form its Hamiltonian flow rotates each
circle about `p` at the angular speed `G'` of its squared radius
(`TauCeti.hamiltonianFlow_radialHamiltonian`). -/
def radialHamiltonian (G : ℝ → ℝ) (p w : ℂ) : ℝ :=
  -G (‖w - p‖ ^ 2) / 2

@[simp]
theorem radialHamiltonian_apply (G : ℝ → ℝ) (p w : ℂ) :
    radialHamiltonian G p w = -G (‖w - p‖ ^ 2) / 2 := (rfl)

/-- A `Cⁿ` profile gives a `Cⁿ` radial Hamiltonian. -/
theorem contDiff_radialHamiltonian {n : WithTop ℕ∞} {G : ℝ → ℝ} (hG : ContDiff ℝ n G) (p : ℂ) :
    ContDiff ℝ n (radialHamiltonian G p) :=
  ((hG.comp ((contDiff_id.sub contDiff_const).norm_sq ℝ)).neg).div_const 2

/-- A profile vanishing on `[R, ∞)` gives a radial Hamiltonian supported in the closed disc of
radius `√R` about `p`; in particular it has compact support. -/
theorem hasCompactSupport_radialHamiltonian {G : ℝ → ℝ} {R : ℝ} (hG : ∀ s, R ≤ s → G s = 0)
    (p : ℂ) : HasCompactSupport (radialHamiltonian G p) := by
  refine HasCompactSupport.intro (isCompact_closedBall p (Real.sqrt R)) fun w hw ↦ ?_
  have hw' : Real.sqrt R < ‖w - p‖ := by simpa [mem_closedBall, dist_eq_norm] using hw
  have hR := (Real.sqrt_lt' ((Real.sqrt_nonneg R).trans_lt hw')).1 hw'
  simp [radialHamiltonian_apply, hG _ hR.le]

/-- The derivative of the radial Hamiltonian: `dH(w) v = -G'(‖w - p‖²) ⟪w - p, v⟫`. -/
theorem hasFDerivAt_radialHamiltonian {G : ℝ → ℝ} {g : ℝ} {p w : ℂ}
    (hG : HasDerivAt G g (‖w - p‖ ^ 2)) :
    HasFDerivAt (radialHamiltonian G p) (-g • innerSL ℝ (w - p)) w := by
  have hn : HasFDerivAt (fun w : ℂ ↦ ‖w - p‖ ^ 2) (2 • innerSL ℝ (w - p)) w :=
    ((hasFDerivAt_id w).sub_const p).norm_sq
  convert (hG.hasFDerivAt.comp w hn).const_mul (-(1 / 2) : ℝ) using 1
  · ext w'
    simp only [radialHamiltonian_apply, Function.comp_apply]
    ring
  · ext v
    simp
    ring

/-- **The Hamiltonian vector field of a radial Hamiltonian** is the infinitesimal rotation
`X_H(w) = i G'(‖w - p‖²) (w - p)` about `p`. -/
theorem hamiltonianVectorField_radialHamiltonian {G : ℝ → ℝ} {p w : ℂ}
    (hG : DifferentiableAt ℝ G (‖w - p‖ ^ 2)) :
    stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p) w =
      I * deriv G (‖w - p‖ ^ 2) * (w - p) := by
  refine ((stdComplexSymplecticForm.eq_hamiltonianVectorField_iff (radialHamiltonian G p) w
    _).2 fun v ↦ ?_).symm
  rw [(hasFDerivAt_radialHamiltonian hG.hasDerivAt).fderiv, stdComplexSymplecticForm_apply]
  simp [Complex.inner]
  ring

/-- **The flow of a radial Hamiltonian is a twist map**: the orbit of `w` turns about `p` at the
constant angular speed `G'(‖w - p‖²)`. Only differentiability of `G` at the squared radius of `w`
is needed, since the orbit stays on the circle through `w`. -/
theorem hamiltonianFlow_radialHamiltonian {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {w : ℂ} (hG : DifferentiableAt ℝ G (‖w - p‖ ^ 2)) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t w =
      p + exp (I * ↑(t * deriv G (‖w - p‖ ^ 2))) * (w - p) := by
  set g := deriv G (‖w - p‖ ^ 2)
  set γ : ℝ → ℂ := fun s ↦ p + exp (I * ↑(s * g)) * (w - p)
  have hnorm (s : ℝ) : ‖γ s - p‖ = ‖w - p‖ := by
    rw [add_sub_cancel_left, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  have hγ (s : ℝ) : HasDerivAt γ
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p) (γ s)) s := by
    rw [hamiltonianVectorField_radialHamiltonian (by rwa [hnorm s]), hnorm s]
    have hs : HasDerivAt (fun s : ℝ ↦ I * ↑(s * g)) (I * g) s := by
      simpa using (((hasDerivAt_id s).mul_const g).ofReal_comp).const_mul I
    convert (hs.cexp.mul_const (w - p)).const_add p using 1
    simp only [γ, add_sub_cancel_left]
    ring
  have h := eq_flowOfLipschitz hX hγ t
  have h0 : γ 0 = w := by simp [γ]
  rw [h0] at h
  rw [SymplecticForm.hamiltonianFlow_eq]
  exact h.symm

/-- The centre is a fixed point of every time map. -/
@[simp]
theorem hamiltonianFlow_radialHamiltonian_center {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    (hG : DifferentiableAt ℝ G 0) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t p = p := by
  rw [hamiltonianFlow_radialHamiltonian hX (by simpa using hG)]
  simp

/-- The time maps fix every point at whose squared radius `G` has zero derivative. -/
theorem hamiltonianFlow_radialHamiltonian_eq_self_of_hasDerivAt_zero {G : ℝ → ℝ} {p : ℂ}
    {K : NNReal} (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {w : ℂ} (hG : HasDerivAt G 0 (‖w - p‖ ^ 2)) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t w = w := by
  rw [hamiltonianFlow_radialHamiltonian hX hG.differentiableAt, hG.deriv]
  simp

/-- **The time maps are the identity outside a disc.** If `G` vanishes on `[R, ∞)`, every point at
distance more than `√R` from `p` is fixed. -/
theorem hamiltonianFlow_radialHamiltonian_eq_self_of_lt {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {R : ℝ} (hG : ∀ s, R ≤ s → G s = 0) {w : ℂ} (hw : R < ‖w - p‖ ^ 2) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t w = w := by
  refine hamiltonianFlow_radialHamiltonian_eq_self_of_hasDerivAt_zero hX ?_ t
  have h : G =ᶠ[𝓝 (‖w - p‖ ^ 2)] fun _ ↦ 0 :=
    (eventually_ge_nhds hw).mono fun s hs ↦ hG s hs
  exact (hasDerivAt_const _ (0 : ℝ)).congr_of_eventuallyEq h

/-- **The time maps are rotations near the centre.** If `G' = θ` near `0`, for instance if
`G(s) = θ s` for small `s`, the time-`t` map agrees near `p` with the rotation
`w ↦ p + exp (i t θ) (w - p)` by the angle `t θ`. -/
theorem hamiltonianFlow_radialHamiltonian_eventuallyEq {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {θ : ℝ} (hG : ∀ᶠ s in 𝓝 0, HasDerivAt G θ s) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t =ᶠ[𝓝 p]
      fun w ↦ p + exp (I * ↑(t * θ)) * (w - p) := by
  have hsq : Tendsto (fun w : ℂ ↦ ‖w - p‖ ^ 2) (𝓝 p) (𝓝 0) := by
    have : Continuous fun w : ℂ ↦ ‖w - p‖ ^ 2 := by fun_prop
    simpa using this.tendsto p
  filter_upwards [hsq.eventually hG] with w hw
  rw [hamiltonianFlow_radialHamiltonian hX hw.differentiableAt, hw.deriv]

/-- **The linearization at the centre is a rotation.** If `G' = θ` near `0`, the derivative of
the time-`t` map at `p` is multiplication by `exp (i t θ)`. -/
theorem hasFDerivAt_hamiltonianFlow_radialHamiltonian_center {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {θ : ℝ} (hG : ∀ᶠ s in 𝓝 0, HasDerivAt G θ s) (t : ℝ) :
    HasFDerivAt (stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t)
      (exp (I * ↑(t * θ)) • ContinuousLinearMap.id ℝ ℂ) p := by
  refine HasFDerivAt.congr_of_eventuallyEq ?_
    (hamiltonianFlow_radialHamiltonian_eventuallyEq hX hG t)
  exact (((hasFDerivAt_id (𝕜 := ℝ) p).sub_const p).const_mul
    (exp (I * ↑(t * θ)))).const_add p

/-- **Displacement bound.** The time-`t` map moves `w` by at most `|t G'(‖w - p‖²)| ‖w - p‖`. In
particular, for the profiles `θ • G₁` the time maps tend uniformly to the identity as `θ → 0`. -/
theorem norm_hamiltonianFlow_radialHamiltonian_sub_le {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {w : ℂ} (hG : DifferentiableAt ℝ G (‖w - p‖ ^ 2)) (t : ℝ) :
    ‖stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t w - w‖ ≤
      |t * deriv G (‖w - p‖ ^ 2)| * ‖w - p‖ := by
  rw [hamiltonianFlow_radialHamiltonian hX hG]
  have h : p + exp (I * ↑(t * deriv G (‖w - p‖ ^ 2))) * (w - p) - w =
      (exp (I * ↑(t * deriv G (‖w - p‖ ^ 2))) - 1) * (w - p) := by
    ring
  rw [h, norm_mul]
  gcongr
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- **Compactly supported radial Hamiltonians have Lipschitz fields.** For a `C²` profile vanishing
on `[R, ∞)`, the radial Hamiltonian is a compactly supported `C²` function, so its Hamiltonian
vector field is globally Lipschitz and its flow is defined for all times. -/
theorem exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) {R : ℝ} (hR : ∀ s, R ≤ s → G s = 0) (p : ℂ) :
    ∃ K, LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)) :=
  stdComplexSymplecticForm.exists_lipschitzWith_hamiltonianVectorField
    (contDiff_radialHamiltonian hG p) (hasCompactSupport_radialHamiltonian hR p)

end TauCeti
