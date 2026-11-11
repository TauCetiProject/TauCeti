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
perturbations tend uniformly to the identity as `θ → 0`: if `|G'| ≤ D` and `G` vanishes on
`[R, ∞)`, no point moves by more than `|t| D √R`.

This is the local mechanism for perturbing an area-preserving map of a surface so as to change
the linearized return map of a periodic orbit by a rotation. If `p` is a periodic point of `φ`
of period `k` and the twist is supported in a disc about `p` avoiding the other points of the
orbit, the linearized return map of `φ ∘ ψ` at `p` is that of `φ` composed with the rotation
(`HasFDerivAt.iterate_comp_of_eventuallyEq_id`).

Twists about several centres combine into one Hamiltonian. The flow of a Hamiltonian depends only
on its values near the orbit, so if the profiles vanish on `[R, ∞)` and the centres are far apart,
the flow of the sum of the radial Hamiltonians turns each point near a centre exactly as the twist
about that centre does, and fixes the points far from all centres. A single Hamiltonian
perturbation can therefore change the return maps of several periodic orbits independently.

## Main definitions

* `TauCeti.radialHamiltonian G p`: the Hamiltonian `w ↦ -G(‖w - p‖²) / 2`.

## Main results

* `TauCeti.hamiltonianVectorField_radialHamiltonian`: `X_H(w) = i G'(‖w - p‖²) (w - p)`.
* `TauCeti.hamiltonianFlow_radialHamiltonian`: the flow is the twist map
  `w ↦ p + exp (i t G'(‖w - p‖²)) (w - p)`, and so is the flow of every Hamiltonian agreeing with
  the radial one near the circle through `w`
  (`TauCeti.hamiltonianFlow_eq_of_forall_eventuallyEq_radialHamiltonian`).
* `TauCeti.hamiltonianFlow_radialHamiltonian_eventuallyEq`: if `G' = θ` near `0`, the time-`t`
  map is the rotation by `t θ` near `p`, and
  `TauCeti.hasFDerivAt_hamiltonianFlow_radialHamiltonian_center` computes its derivative at `p`.
* `TauCeti.hamiltonianFlow_radialHamiltonian_eq_self_of_lt`: if `G` vanishes on `[R, ∞)`, the
  time maps are the identity outside the disc of radius `√R` about `p`.
* `TauCeti.norm_hamiltonianFlow_radialHamiltonian_sub_le`: the displacement bound
  `‖φ_t(w) - w‖ ≤ |t G'(‖w - p‖²)| ‖w - p‖`, and its uniform form
  `TauCeti.norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt`, `‖φ_t(w) - w‖ ≤ |t| D √R`.
* `TauCeti.hamiltonianFlow_sum_radialHamiltonian` and
  `TauCeti.hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id`: a sum of twists about
  well-separated centres acts on each disc as the twist about its centre, and as the identity
  away from the discs.
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

/-- **Flows that are radial twists near a circle.** If a Hamiltonian `H` agrees with the radial
Hamiltonian of `G` about `p` near every point of the circle about `p` through `w`, the orbit of
`w` turns about `p` at the constant angular speed `G'(‖w - p‖²)`. Only differentiability of `G` at
the squared radius of `w` is needed, since the orbit stays on that circle. -/
theorem hamiltonianFlow_eq_of_forall_eventuallyEq_radialHamiltonian {H : ℂ → ℝ} {G : ℝ → ℝ}
    {p : ℂ} {K : NNReal} (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H))
    {w : ℂ} (hG : DifferentiableAt ℝ G (‖w - p‖ ^ 2))
    (hH : ∀ y, ‖y - p‖ = ‖w - p‖ → H =ᶠ[𝓝 y] radialHamiltonian G p) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow H hX t w =
      p + exp (I * ↑(t * deriv G (‖w - p‖ ^ 2))) * (w - p) := by
  set g := deriv G (‖w - p‖ ^ 2)
  set γ : ℝ → ℂ := fun s ↦ p + exp (I * ↑(s * g)) * (w - p)
  have hnorm (s : ℝ) : ‖γ s - p‖ = ‖w - p‖ := by
    rw [add_sub_cancel_left, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  have hγ (s : ℝ) : HasDerivAt γ
      (stdComplexSymplecticForm.hamiltonianVectorField H (γ s)) s := by
    rw [stdComplexSymplecticForm.hamiltonianVectorField_congr_of_eventuallyEq (hH _ (hnorm s)),
      hamiltonianVectorField_radialHamiltonian (by rwa [hnorm s]), hnorm s]
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

/-- **The flow of a radial Hamiltonian is a twist map**: the orbit of `w` turns about `p` at the
constant angular speed `G'(‖w - p‖²)`. Only differentiability of `G` at the squared radius of `w`
is needed, since the orbit stays on the circle through `w`. -/
theorem hamiltonianFlow_radialHamiltonian {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {w : ℂ} (hG : DifferentiableAt ℝ G (‖w - p‖ ^ 2)) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t w =
      p + exp (I * ↑(t * deriv G (‖w - p‖ ^ 2))) * (w - p) :=
  hamiltonianFlow_eq_of_forall_eventuallyEq_radialHamiltonian hX hG (fun _ _ ↦ .rfl) t

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

/-- **Uniform displacement bound.** If `|G'| ≤ D` everywhere and `G` vanishes on `[R, ∞)`, the
time-`t` map moves no point by more than `|t| D √R`: points outside the disc of radius `√R` about
`p` are fixed, and points inside it turn through an angle at most `|t| D`. -/
theorem norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    (hG : Differentiable ℝ G) {D R : ℝ} (hD : ∀ s, |deriv G s| ≤ D)
    (hR : ∀ s, R ≤ s → G s = 0) (w : ℂ) (t : ℝ) :
    ‖stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t w - w‖ ≤
      |t| * D * Real.sqrt R := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  rcases le_or_gt (‖w - p‖ ^ 2) R with hw | hw
  · have hwR : ‖w - p‖ ≤ Real.sqrt R := Real.le_sqrt_of_sq_le hw
    calc _ ≤ |t * deriv G (‖w - p‖ ^ 2)| * ‖w - p‖ :=
          norm_hamiltonianFlow_radialHamiltonian_sub_le hX (hG _) t
      _ ≤ |t| * D * Real.sqrt R := by
        rw [abs_mul]
        gcongr
        exact hD _
  · rw [hamiltonianFlow_radialHamiltonian_eq_self_of_lt hX hR hw t, sub_self, norm_zero]
    positivity

/-- A radial Hamiltonian whose profile vanishes on `[R, ∞)` vanishes near every point at squared
distance more than `R` from its centre. -/
theorem radialHamiltonian_eventuallyEq_zero {G : ℝ → ℝ} {R : ℝ} (hR : ∀ s, R ≤ s → G s = 0)
    {p w : ℂ} (hw : R < ‖w - p‖ ^ 2) : radialHamiltonian G p =ᶠ[𝓝 w] 0 := by
  have hopen : IsOpen {y : ℂ | R < ‖y - p‖ ^ 2} := isOpen_lt continuous_const (by fun_prop)
  filter_upwards [hopen.mem_nhds hw] with y hy
  simp [hR _ (le_of_lt hy)]

/-- **Twists about well-separated centres.** Let the profiles `G i` vanish on `[R, ∞)`, so that
the radial Hamiltonians about the points `p i` are supported in discs of radius `√R`. If `w` is so
close to `p i` that the circle about `p i` through `w` stays at distance more than `√R` from the
other centres, then the flow of the sum of these Hamiltonians turns `w` about `p i` exactly as the
twist about `p i` alone does. -/
theorem hamiltonianFlow_sum_radialHamiltonian {ι : Type*} [Fintype ι] {G : ι → ℝ → ℝ}
    {p : ι → ℂ} {R : ℝ} (hR : ∀ i s, R ≤ s → G i s = 0) {K : NNReal}
    (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField
      fun w ↦ ∑ j, radialHamiltonian (G j) (p j) w))
    {i : ι} {w : ℂ} (hG : DifferentiableAt ℝ (G i) (‖w - p i‖ ^ 2))
    (hw : ∀ j ≠ i, Real.sqrt R + ‖w - p i‖ < ‖p j - p i‖) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (fun w ↦ ∑ j, radialHamiltonian (G j) (p j) w) hX
      t w = p i + exp (I * ↑(t * deriv (G i) (‖w - p i‖ ^ 2))) * (w - p i) := by
  refine hamiltonianFlow_eq_of_forall_eventuallyEq_radialHamiltonian hX hG (fun y hy ↦ ?_) t
  have hev : ∀ᶠ z in 𝓝 y, ∀ j, j ≠ i → radialHamiltonian (G j) (p j) z = 0 := by
    refine eventually_all.2 fun j ↦ ?_
    by_cases hji : j = i
    · exact .of_forall fun _ h ↦ absurd hji h
    refine (radialHamiltonian_eventuallyEq_zero (hR j) (Real.lt_sq_of_sqrt_lt ?_)).mono
      fun z hz _ ↦ hz
    have h3 := norm_sub_le_norm_sub_add_norm_sub (p j) y (p i)
    rw [norm_sub_rev (p j) y] at h3
    linarith [hw j hji]
  filter_upwards [hev] with z hz
  exact Finset.sum_eq_single i (fun j _ hji ↦ hz j hji) (by simp)

/-- **Twists are the identity away from their discs.** If the profiles `G i` vanish on `[R, ∞)`,
the time maps of the sum of the radial Hamiltonians about the points `p i` are the identity near
every point at squared distance more than `R` from all the `p i`. -/
theorem hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id {ι : Type*} [Fintype ι]
    {G : ι → ℝ → ℝ} {p : ι → ℂ} {R : ℝ} (hR : ∀ i s, R ≤ s → G i s = 0) {K : NNReal}
    (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField
      fun w ↦ ∑ j, radialHamiltonian (G j) (p j) w))
    {w : ℂ} (hw : ∀ i, R < ‖w - p i‖ ^ 2) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow (fun w ↦ ∑ j, radialHamiltonian (G j) (p j) w) hX
      t =ᶠ[𝓝 w] id := by
  have hopen : IsOpen {y : ℂ | ∀ i, R < ‖y - p i‖ ^ 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)
  filter_upwards [hopen.mem_nhds hw] with y hy
  -- The Hamiltonian vanishes near `y`, so its vector field vanishes at `y`.
  have hH : (fun w ↦ ∑ j, radialHamiltonian (G j) (p j) w) =ᶠ[𝓝 y] fun _ ↦ 0 := by
    filter_upwards [eventually_all.2 fun i ↦ radialHamiltonian_eventuallyEq_zero (hR i) (hy i)]
      with z hz
    exact Finset.sum_eq_zero fun i _ ↦ hz i
  rw [SymplecticForm.hamiltonianFlow_eq]
  refine (forall_flowOfLipschitz_eq_self_iff hX y).2 ?_ t
  rw [stdComplexSymplecticForm.hamiltonianVectorField_congr_of_eventuallyEq hH,
    stdComplexSymplecticForm.hamiltonianVectorField_const, Pi.zero_apply]

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
