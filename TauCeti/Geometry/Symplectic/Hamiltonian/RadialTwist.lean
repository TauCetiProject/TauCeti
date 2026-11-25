/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Geometry.Symplectic.Complex.Line
public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
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

A finite sum of radial Hamiltonians whose profiles vanish on `[R, ∞)` and whose centres are more
than `2 √R` apart agrees, near each closed disc of radius `√R` about a centre, with the
corresponding term (`TauCeti.sum_radialHamiltonian_eventuallyEq`). Its flow therefore twists each
of these discs as the corresponding term does (`TauCeti.hamiltonianFlow_sum_radialHamiltonian`)
and fixes every point outside them (`TauCeti.hamiltonianFlow_sum_radialHamiltonian_eq_self`). So
its time maps are close to the identity in `C¹` when the twists are: a bound `M` on the profile
derivatives bounds the displacement of the time-`t` map by `|t| M √R`
(`TauCeti.norm_hamiltonianFlow_sum_radialHamiltonian_sub_le`), and a bound `L` on Lipschitz
constants of the fields of the individual twists bounds the distance of its derivative from the
identity by `exp (L |t|) - 1`
(`TauCeti.norm_fderiv_hamiltonianFlow_sum_radialHamiltonian_sub_id_le`). Scaling the profile by
`c` scales the field by `c` (`TauCeti.radialHamiltonian_const_mul`), so twists by small angles are
`C¹`-small.

For every `R > 0` and angle `θ`, `TauCeti.exists_diffeomorph_eventuallyEq_rotation` gives a smooth
diffeomorphism of `ℂ` preserving the area form and the norm, equal to the rotation by `θ` near `0`
and to the identity outside the disc of radius `R`; in this form it can be transported through
Darboux charts.

This is the local mechanism for perturbing an area-preserving map of a surface so as to change
the linearized return map of a periodic orbit by a rotation, independently for finitely many
orbits. If `p` is a periodic point of `φ` of period `k` and the twist is supported in a disc about
`p` avoiding the other points of the orbit, the linearized return map of `φ ∘ ψ` at `p` is that of
`φ` composed with the rotation (`HasFDerivAt.iterate_comp_of_eventuallyEq_id`).

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
  `‖φ_t(w) - w‖ ≤ |t G'(‖w - p‖²)| ‖w - p‖`, and its uniform form
  `TauCeti.norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt`, `‖φ_t(w) - w‖ ≤ |t| D √R`.
* `TauCeti.exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian`: a `C²` profile vanishing
  for large arguments gives a compactly supported Hamiltonian with a globally Lipschitz field.
* `TauCeti.hamiltonianFlow_sum_radialHamiltonian` and
  `TauCeti.hamiltonianFlow_sum_radialHamiltonian_eq_self`: the flow of a sum of radial twists with
  disjoint supports.
* `TauCeti.norm_hamiltonianFlow_sum_radialHamiltonian_sub_le` and
  `TauCeti.norm_fderiv_hamiltonianFlow_sum_radialHamiltonian_sub_id_le`: its time maps are close to
  the identity, in value and in derivative.
* `TauCeti.exists_diffeomorph_eventuallyEq_rotation`: a smooth diffeomorphism of `ℂ` preserving
  the area form, rotating a neighbourhood of `0` by a prescribed angle and fixing every point
  outside a prescribed disc.

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

/-- Scaling the profile scales the radial Hamiltonian. -/
theorem radialHamiltonian_const_mul (c : ℝ) (G : ℝ → ℝ) (p : ℂ) :
    radialHamiltonian (fun s ↦ c * G s) p = fun w ↦ c * radialHamiltonian G p w := by
  funext w
  simp only [radialHamiltonian_apply]
  ring

/-- A profile vanishing on `[R, ∞)` gives a radial Hamiltonian supported in the closed disc of
radius `√R` about `p`; in particular it has compact support. -/
theorem hasCompactSupport_radialHamiltonian {G : ℝ → ℝ} {R : ℝ} (hG : ∀ s, R ≤ s → G s = 0)
    (p : ℂ) : HasCompactSupport (radialHamiltonian G p) := by
  refine HasCompactSupport.intro (isCompact_closedBall p (Real.sqrt R)) fun w hw ↦ ?_
  have hw' : Real.sqrt R < ‖w - p‖ := by simpa [mem_closedBall, dist_eq_norm] using hw
  have hR := (Real.sqrt_lt' ((Real.sqrt_nonneg R).trans_lt hw')).1 hw'
  simp [radialHamiltonian_apply, hG _ hR.le]

/-- A profile vanishing on `[R, ∞)` gives a radial Hamiltonian vanishing near every point at
distance more than `√R` from `p`. -/
theorem radialHamiltonian_eventuallyEq_zero {G : ℝ → ℝ} {R : ℝ} (hG : ∀ s, R ≤ s → G s = 0)
    {p w : ℂ} (hw : R < ‖w - p‖ ^ 2) : radialHamiltonian G p =ᶠ[𝓝 w] 0 := by
  filter_upwards [(isOpen_lt continuous_const
    (by fun_prop : Continuous fun z : ℂ ↦ ‖z - p‖ ^ 2)).mem_nhds hw] with z hz
  simp [hG _ hz.le]

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

/-- The orbit of `w` under the flow of a radial Hamiltonian stays on the circle through `w` about
`p`. -/
theorem norm_hamiltonianFlow_radialHamiltonian_sub_center {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {w : ℂ} (hG : DifferentiableAt ℝ G (‖w - p‖ ^ 2)) (t : ℝ) :
    ‖stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX t w - p‖ = ‖w - p‖ := by
  rw [hamiltonianFlow_radialHamiltonian hX hG, add_sub_cancel_left, norm_mul,
    norm_exp_I_mul_ofReal, one_mul]

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

/-- **Compactly supported radial Hamiltonians have Lipschitz fields.** For a `C²` profile vanishing
on `[R, ∞)`, the radial Hamiltonian is a compactly supported `C²` function, so its Hamiltonian
vector field is globally Lipschitz and its flow is defined for all times. -/
theorem exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) {R : ℝ} (hR : ∀ s, R ≤ s → G s = 0) (p : ℂ) :
    ∃ K, LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)) :=
  stdComplexSymplecticForm.exists_lipschitzWith_hamiltonianVectorField
    (contDiff_radialHamiltonian hG p) (hasCompactSupport_radialHamiltonian hR p)

/-! ### Sums of radial twists with disjoint supports -/

section Sum

variable {ι : Type*} {s : Finset ι} {G : ι → ℝ → ℝ} {p : ι → ℂ} {R : ℝ}

/-- Near every point of the closed disc of radius `√R` about `p i`, a sum of radial Hamiltonians
whose profiles vanish on `[R, ∞)` and whose centres are more than `2 √R` apart is its `i`-th
term. -/
theorem sum_radialHamiltonian_eventuallyEq (hGR : ∀ j ∈ s, ∀ x, R ≤ x → G j x = 0)
    (hp : (s : Set ι).Pairwise fun j l ↦ 4 * R < ‖p j - p l‖ ^ 2) {i : ι} (hi : i ∈ s) {y : ℂ}
    (hy : ‖y - p i‖ ^ 2 ≤ R) :
    (fun w ↦ ∑ j ∈ s, radialHamiltonian (G j) (p j) w) =ᶠ[𝓝 y]
      radialHamiltonian (G i) (p i) := by
  -- The other centres are farther than `√R` from `y`, so their terms vanish near `y`.
  have hfar (j : ι) (hj : j ∈ s) (hji : j ≠ i) : R < ‖y - p j‖ ^ 2 := by
    have htri : ‖p i - p j‖ ≤ ‖y - p i‖ + ‖y - p j‖ := by
      simpa [add_comm] using norm_sub_le (y - p j) (y - p i)
    by_contra! h
    nlinarith [hp hi hj hji.symm, norm_nonneg (y - p i), norm_nonneg (y - p j),
      mul_self_le_mul_self (norm_nonneg _) htri, sq_nonneg (‖y - p i‖ - ‖y - p j‖)]
  filter_upwards [(Filter.eventually_all_finset s).2 fun j hj ↦ (Filter.eventually_imp_distrib_left
    (p := j ≠ i)).2 fun hji ↦ radialHamiltonian_eventuallyEq_zero (hGR j hj) (hfar j hj hji)]
    with w hw
  exact Finset.sum_eq_single_of_mem i hi fun j hj hji ↦ hw j hj hji

/-- **The flow of a sum of disjoint radial twists.** If the profiles vanish on `[R, ∞)` and the
centres are more than `2 √R` apart, then on the closed disc of radius `√R` about `p i` the flow
of the sum agrees with the flow of the `i`-th twist alone. In particular it turns each circle
about `p i` in that disc as the `i`-th twist does (`TauCeti.hamiltonianFlow_radialHamiltonian`). -/
theorem hamiltonianFlow_sum_radialHamiltonian {K K' : NNReal}
    (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField
      fun w ↦ ∑ j ∈ s, radialHamiltonian (G j) (p j) w))
    (hGR : ∀ j ∈ s, ∀ x, R ≤ x → G j x = 0)
    (hp : (s : Set ι).Pairwise fun j l ↦ 4 * R < ‖p j - p l‖ ^ 2) {i : ι} (hi : i ∈ s)
    (hXi : LipschitzWith K'
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian (G i) (p i))))
    {w : ℂ} (hG : DifferentiableAt ℝ (G i) (‖w - p i‖ ^ 2)) (hw : ‖w - p i‖ ^ 2 ≤ R) (t : ℝ) :
    stdComplexSymplecticForm.hamiltonianFlow _ hX t w =
      stdComplexSymplecticForm.hamiltonianFlow _ hXi t w := by
  refine stdComplexSymplecticForm.hamiltonianFlow_apply_eq_of_eventuallyEq _ hX hXi
    fun τ _ ↦ sum_radialHamiltonian_eventuallyEq hGR hp hi ?_
  -- The orbit of the `i`-th twist stays on the circle through `w`.
  rwa [norm_hamiltonianFlow_radialHamiltonian_sub_center hXi hG]

/-- **A sum of radial twists is the identity outside their discs.** If the profiles vanish on
`[R, ∞)`, the flow of the sum is the identity near every point at distance more than `√R` from
all the centres. -/
theorem hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id {K : NNReal}
    (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField
      fun w ↦ ∑ j ∈ s, radialHamiltonian (G j) (p j) w))
    (hGR : ∀ j ∈ s, ∀ x, R ≤ x → G j x = 0) {w : ℂ} (hw : ∀ j ∈ s, R < ‖w - p j‖ ^ 2)
    (t : ℝ) : stdComplexSymplecticForm.hamiltonianFlow _ hX t =ᶠ[𝓝 w] id := by
  -- The sum vanishes near `w`, so `w` is outside its support.
  have h : (fun w ↦ ∑ j ∈ s, radialHamiltonian (G j) (p j) w) =ᶠ[𝓝 w] fun _ ↦ 0 := by
    filter_upwards [(Filter.eventually_all_finset s).2 fun j hj ↦
      radialHamiltonian_eventuallyEq_zero (hGR j hj) (hw j hj)] with z hz
    exact Finset.sum_eq_zero hz
  exact stdComplexSymplecticForm.hamiltonianFlow_eventuallyEq_id_of_notMem_tsupport _ hX
    (notMem_tsupport_iff_eventuallyEq.2 h) t

/-- **A sum of radial twists fixes the points outside their discs.** If the profiles vanish on
`[R, ∞)`, every point at distance more than `√R` from all the centres is fixed by the flow of the
sum. -/
theorem hamiltonianFlow_sum_radialHamiltonian_eq_self {K : NNReal}
    (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField
      fun w ↦ ∑ j ∈ s, radialHamiltonian (G j) (p j) w))
    (hGR : ∀ j ∈ s, ∀ x, R ≤ x → G j x = 0) {w : ℂ} (hw : ∀ j ∈ s, R < ‖w - p j‖ ^ 2)
    (t : ℝ) : stdComplexSymplecticForm.hamiltonianFlow _ hX t w = w :=
  (hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id hX hGR hw t).eq_of_nhds

/-- **Displacement bound for a sum of disjoint radial twists.** If the profiles are
differentiable with `|G_j'| ≤ M`, vanish on `[R, ∞)`, and the centres are more than `2 √R` apart,
the time-`t` map of the flow of the sum moves no point by more than `|t| M √R`: points of the disc
about `p j` turn as under the `j`-th twist, and the other points are fixed. -/
theorem norm_hamiltonianFlow_sum_radialHamiltonian_sub_le {K : NNReal}
    (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField
      fun w ↦ ∑ j ∈ s, radialHamiltonian (G j) (p j) w))
    (hG : ∀ j ∈ s, Differentiable ℝ (G j)) (hGR : ∀ j ∈ s, ∀ x, R ≤ x → G j x = 0)
    (hp : (s : Set ι).Pairwise fun j l ↦ 4 * R < ‖p j - p l‖ ^ 2)
    {K' : ι → NNReal} (hXj : ∀ j ∈ s, LipschitzWith (K' j)
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian (G j) (p j))))
    {M : ℝ} (hM : ∀ j ∈ s, ∀ x, |deriv (G j) x| ≤ M) (hM0 : 0 ≤ M) (t : ℝ) (w : ℂ) :
    ‖stdComplexSymplecticForm.hamiltonianFlow _ hX t w - w‖ ≤ |t| * M * Real.sqrt R := by
  by_cases h : ∃ j ∈ s, ‖w - p j‖ ^ 2 ≤ R
  · obtain ⟨j, hj, hw⟩ := h
    rw [hamiltonianFlow_sum_radialHamiltonian hX hGR hp hj (hXj j hj) (hG j hj _) hw]
    exact norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt (hXj j hj) (hG j hj) (hM j hj)
      (hGR j hj) w t
  · simp only [not_exists, not_and, not_le] at h
    rw [hamiltonianFlow_sum_radialHamiltonian_eq_self hX hGR h, sub_self, norm_zero]
    positivity

/-- **The linearized flow of a sum of disjoint radial twists is close to the identity.** Let the
profiles be `C²` and vanish on `[R, ∞)`, let the centres be more than `2 √R` apart, and let the
field of the `j`-th twist be `K j`-Lipschitz with `K j ≤ L`. Then the derivative of the time-`t`
map of the flow of the sum is within `exp (L |t|) - 1` of the identity at every point: near the
disc about `p j` the flow is that of the `j`-th twist, and away from the discs it is the
identity. -/
theorem norm_fderiv_hamiltonianFlow_sum_radialHamiltonian_sub_id_le {K : NNReal}
    (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField
      fun w ↦ ∑ j ∈ s, radialHamiltonian (G j) (p j) w))
    (hG : ∀ j ∈ s, ContDiff ℝ 2 (G j)) (hGR : ∀ j ∈ s, ∀ x, R ≤ x → G j x = 0)
    (hp : (s : Set ι).Pairwise fun j l ↦ 4 * R < ‖p j - p l‖ ^ 2)
    {K' : ι → NNReal} (hXj : ∀ j ∈ s, LipschitzWith (K' j)
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian (G j) (p j))))
    {L : ℝ} (hL : ∀ j ∈ s, (K' j : ℝ) ≤ L) (hL0 : 0 ≤ L) (t : ℝ) (w : ℂ) :
    ‖fderiv ℝ (stdComplexSymplecticForm.hamiltonianFlow _ hX t) w - ContinuousLinearMap.id ℝ ℂ‖ ≤
      Real.exp (L * |t|) - 1 := by
  -- The finitely many separations leave room for discs of a slightly larger radius `√R'`.
  obtain ⟨R', hRR', hp'⟩ := Filter.Eventually.exists_gt (a := R)
    (p := fun R' ↦ ∀ j ∈ s, ∀ l ∈ s, j ≠ l → 4 * R' < ‖p j - p l‖ ^ 2)
    ((Filter.eventually_all_finset s).2 fun j hj ↦ (Filter.eventually_all_finset s).2 fun l hl ↦
      Filter.eventually_imp_distrib_left.2 fun hjl ↦
        ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (hp hj hl hjl))
  by_cases h : ∃ j ∈ s, ‖w - p j‖ ^ 2 < R'
  · -- Near `w` the flow of the sum is the flow of the `j`-th twist.
    obtain ⟨j, hj, hw⟩ := h
    have hev : stdComplexSymplecticForm.hamiltonianFlow _ hX t =ᶠ[𝓝 w]
        stdComplexSymplecticForm.hamiltonianFlow _ (hXj j hj) t := by
      filter_upwards [(isOpen_lt (by fun_prop : Continuous fun z : ℂ ↦ ‖z - p j‖ ^ 2)
        continuous_const).mem_nhds hw] with z hz
      exact hamiltonianFlow_sum_radialHamiltonian hX
        (fun l hl x hx ↦ hGR l hl x (hRR'.le.trans hx)) hp' hj (hXj j hj)
        ((hG j hj).differentiable (by simp) _) hz.le t
    rw [hev.fderiv_eq]
    refine (stdComplexSymplecticForm.norm_fderiv_hamiltonianFlow_sub_id_le _ (hXj j hj)
      (contDiff_radialHamiltonian (hG j hj) (p j)) t w).trans ?_
    gcongr
    exact hL j hj
  · -- Away from the discs the flow is the identity near `w`.
    simp only [not_exists, not_and, not_lt] at h
    rw [(hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id hX hGR
      (fun j hj ↦ hRR'.trans_le (h j hj)) t).fderiv_eq, fderiv_id, sub_self, norm_zero]
    exact sub_nonneg.2 (Real.one_le_exp (by positivity))

end Sum

/-! ### The radial twist as a diffeomorphism -/

section Diffeomorph

open scoped Manifold

/-- **A compactly supported area-preserving rotation of the plane.** For every radius `R > 0` and
every angle `θ` there is a smooth diffeomorphism `ψ` of `ℂ` which preserves the standard area form,
preserves the norm, is the identity outside the open disc of radius `R` about `0`, and agrees near
`0` with the rotation by `θ`, so that its derivative at `0` is multiplication by `exp (i θ)`. -/
theorem exists_diffeomorph_eventuallyEq_rotation {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ∃ ψ : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ ℂ,
      (∀ x u v, stdComplexSymplecticForm (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) =
        stdComplexSymplecticForm u v) ∧
      (∀ w, ‖ψ w‖ = ‖w‖) ∧ (∀ w, R ≤ ‖w‖ → ψ w = w) ∧
      ⇑ψ =ᶠ[𝓝 0] fun w ↦ exp (I * θ) * w := by
  obtain ⟨k, hk, -, hk_large, hk_deriv⟩ :=
    exists_contDiff_cutoff_id (r := R ^ 2 / 4) (R := R ^ 2 / 2) (by nlinarith)
  -- `ψ` is the time-one map of the radial twist with profile `G`, with inverse the time `-1` map.
  set G : ℝ → ℝ := fun s ↦ θ * k s
  have hG : ContDiff ℝ ∞ G := contDiff_const.mul hk
  have hGR : ∀ s, R ^ 2 / 2 ≤ s → G s = 0 := fun s hs ↦ by
    simp [G, hk_large s (hs.trans (le_abs_self s))]
  obtain ⟨K, hX⟩ := exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian
    (hG.of_le (by simp)) hGR 0
  -- The time-`t` map of the twist is `w ↦ exp (i t G'(‖w‖²)) w`.
  set τ : ℝ → ℂ → ℂ := fun t w ↦ exp (I * ↑(t * deriv G (‖w‖ ^ 2))) * w
  have hflow (t : ℝ) :
      stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G 0) hX t = τ t := by
    funext w
    simpa [τ] using hamiltonianFlow_radialHamiltonian hX
      ((hG.differentiable (by simp)) (‖w - 0‖ ^ 2)) t
  have hnorm (t : ℝ) (w : ℂ) : ‖τ t w‖ = ‖w‖ := by
    simp only [τ, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  have hinv (t : ℝ) (w : ℂ) : τ (-t) (τ t w) = w := by
    simp only [τ, hnorm, ← mul_assoc, ← Complex.exp_add]
    rw [show I * ↑(-t * deriv G (‖w‖ ^ 2)) + I * ↑(t * deriv G (‖w‖ ^ 2)) = 0 by
      push_cast; ring, Complex.exp_zero, one_mul]
  have hsmooth (t : ℝ) : ContDiff ℝ ∞ (τ t) := by
    have hG' : ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.1 hG).2
    exact ((contDiff_const.mul (ofRealCLM.contDiff.comp (contDiff_const.mul
      (hG'.comp (contDiff_norm_sq ℝ))))).cexp).mul contDiff_id
  let ψ : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ ℂ :=
    ⟨⟨τ 1, τ (-1), hinv 1, fun w ↦ by simpa using hinv (-1) w⟩, (hsmooth 1).contMDiff,
      (hsmooth (-1)).contMDiff⟩
  have hψ : ⇑ψ = τ 1 := rfl
  refine ⟨ψ, fun x u v ↦ ?_, hnorm 1, fun w hw ↦ ?_, ?_⟩
  · rw [hψ, ← hflow 1]
    exact stdComplexSymplecticForm.apply_fderiv_hamiltonianFlow _ hX
      ((contDiff_radialHamiltonian hG 0).of_le (by simp)) 1 x u v
  · rw [hψ, ← hflow 1]
    refine hamiltonianFlow_radialHamiltonian_eq_self_of_lt hX hGR ?_ 1
    rw [sub_zero]
    nlinarith [pow_pos hR 2]
  · rw [hψ, ← hflow 1]
    have hG0 : ∀ᶠ s in 𝓝 0, HasDerivAt G θ s := by
      filter_upwards [Ioo_mem_nhds (show -(R ^ 2 / 4) < (0 : ℝ) by
        have := pow_pos hR 2; linarith) (show (0 : ℝ) < R ^ 2 / 4 by positivity)] with s hs
      simpa [G] using (hk_deriv s (abs_lt.2 hs)).const_mul θ
    simpa using hamiltonianFlow_radialHamiltonian_eventuallyEq hX hG0 1

end Diffeomorph

end TauCeti
