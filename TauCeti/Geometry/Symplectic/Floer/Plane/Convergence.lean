/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylindricalEnd
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Dynamics.Flow.Periodic.Basic

/-!
# Convergence of the end of a finite-energy PSS plane to a nondegenerate orbit

Let `𝔎` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from
a period-one Hamiltonian `H` on a symplectic vector space `(V, ω)`, and let `ε = ±1` be the sign
of the end of `p` at `∞`. Let `u` be a finite-energy solution of the Floer equation
`(du - X_𝔎)^{0,1} = 0` on an exterior neighborhood `‖w‖ > r` of `∞`, with image in a compact set
`K`. By `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit`, the boundary loops
`t ↦ u(φ_p(ε R, t))`, where `φ_p` is the end chart `TauCeti.Floer.PSSPlane.endChart`, converge
uniformly to a one-periodic orbit of `H` along some sequence `R_n → ∞`. This file shows that they
converge uniformly as `R → ∞` to a single orbit when every one-periodic orbit of `H` in `K` is
nondegenerate. This is the asymptotic condition under which positive and negative PSS planes meet
a generator of the Floer complex.

**End charts and the positive end Hamiltonian.** The end chart `φ_p`
(`TauCeti.Floer.PSSPlane.endChart`) is the end lift `z ↦ exp (2π ε z)` read in the real coordinates
`ℝ × ℝ ≃ ℂ`. Because `negative.cylindricalEndLift z = positive.cylindricalEndLift (-z)`, the two
end charts satisfy `φ_p(ε s, ε t) = φ_+(s, t)`, so `φ_+ = positive.endChart` serves as the positive
end chart for both planes. Likewise, `p.perturbation H = positive.perturbation H'_p` for the
positive end Hamiltonian `H'_p(t, x) = ε H(ε t, x)`
(`TauCeti.Floer.PSSPlane.positiveEndHamiltonian`). On `s ≥ 2`, `u ∘ φ_+` solves the Floer equation
of a positive half-cylinder for `H'_p`, and the map `φ_+` sends `(a, ∞) × [0, 1)` (resp.
`[a, ∞) × [0, 1)`) bijectively onto `{‖w‖ > exp (2πa)}` (resp. `{‖w‖ ≥ exp (2πa)}`), so the
half-cylinder energy of `u ∘ φ_+` equals the Floer energy of `u` on the exterior of the disc.

**Convergence at nondegenerate ends.** Suppose that on some half-cylinder `s > b` the derivative of
`u ∘ φ_+` is bounded and the almost complex structures `J ∘ φ_+` are uniformly tame, and that every
one-periodic orbit `x` of `H` in `K` is nondegenerate: `x(0)` is a nondegenerate fixed point of the
time-one map of `H`. Time reversal turns the orbits of `H'_-` into those of `H` and preserves
isolation among periodic orbits, so `TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop`
gives uniform convergence of `t ↦ u(φ_p(ε R, t))` as `R → ∞` to a single one-periodic orbit of `H`
(`SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation`).
Consequently, for a `C²` finite-energy solution on the whole plane, the orbit in the energy
identity `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)` is the genuine `R → ∞` uniform limit of the end loops
(`exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isNondegenerateFixedPt`).

**Cylindrical ends.** When `H` and `u` are `C³` and the almost complex structure on the end beyond
some height `T₀` is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic
family `J₀` which is `C²` on an open neighborhood of `ℝ × K` and tamed by `ω` on `ℝ × K`, bubbling
cannot occur along the end (`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_floer`). Thus
`u ∘ φ_+` and `u ∘ φ_p` have bounded derivatives far out on the end, and the structures there are
uniformly tame, so uniform convergence as `R → ∞` and the whole-plane energy identity hold with no
assumed derivative or taming bounds.

## Main definitions

* `TauCeti.Floer.PSSPlane.endChart`: the end lift of a PSS plane in the real coordinates
  `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.PSSPlane.positiveEndHamiltonian`: the Hamiltonian `H'_p(t, x) = ε H(ε t, x)` of a
  PSS plane in the positive end chart `positive.endChart`.

## Main results

* `TauCeti.Floer.PSSPlane.image_endChart_positive_prod_Ico`,
  `TauCeti.Floer.PSSPlane.image_endChart_positive_Ioi_prod_Ico`,
  `TauCeti.Floer.PSSPlane.image_endChart_positive_Ici_prod_Ico`: `positive.endChart` maps
  `P × [0, 1)` onto the nonzero points with `log ‖w‖ / (2π) ∈ P`, and in particular maps
  `(a, ∞) × [0, 1)` and `[a, ∞) × [0, 1)` onto `{‖w‖ > exp (2πa)}` and `{‖w‖ ≥ exp (2πa)}`.
* `TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_eq`,
  `TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ici_eq`: for
  `a ≥ 2`, the half-cylinder energy of `u ∘ positive.endChart` equals the Floer energy of `u` on
  the exterior of the disc of radius `exp (2πa)`.
* `SymplecticForm.exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation`:
  uniform convergence of the end loops of a finite-energy PSS plane to a nondegenerate orbit, under
  a derivative bound and uniform tameness on the end.
* `exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isNondegenerateFixedPt`:
  the whole-plane energy identity `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)` with `x` the `R → ∞` limit of
  the end loops.
* `TauCeti.SymplecticForm.exists_forall_norm_fderiv_comp_endChart_positive_le`,
  `TauCeti.SymplecticForm.exists_forall_norm_fderiv_comp_endChart_le`: bounded derivatives along a
  cylindrical end of a finite-energy PSS plane.
* `exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation_of_cylindrical`,
  `exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical`:
  uniform end convergence and the whole-plane energy identity for PSS planes with cylindrical ends.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits at
  nondegenerate orbits.
-/

public section

open Set Real Function MeasureTheory Filter
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti

namespace Floer.PSSPlane

/-! ### End charts and positive end Hamiltonians -/

/-- The end lift `z ↦ exp (2π ε z)` of a PSS plane, written in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def endChart (p : PSSPlane) : ℝ × ℝ → ℝ × ℝ :=
  realChart p.cylindricalEndLift

theorem endChart_def (p : PSSPlane) : p.endChart = realChart p.cylindricalEndLift :=
  (rfl)

theorem endChart_apply (p : PSSPlane) (z : ℝ × ℝ) :
    p.endChart z =
      Complex.equivRealProdCLM (p.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  realChart_apply _ _

/-- The end chart at `(s, t)` is the end lift at `s + i t`, read in real coordinates. -/
theorem endChart_mk (p : PSSPlane) (s t : ℝ) :
    p.endChart (s, t) =
      Complex.equivRealProdCLM (p.cylindricalEndLift (↑s + ↑t * Complex.I)) := by
  simp [endChart_apply, Complex.equivRealProdCLM_symm_apply]

/-- In complex coordinates, the end chart is the end lift. -/
@[simp]
theorem equivRealProdCLM_symm_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (p.endChart z) =
      p.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The longitudinal coordinate at the image of `(s, t)` under the end chart is `s`. -/
theorem re_endCoord_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    (p.endCoord (Complex.equivRealProdCLM.symm (p.endChart z))).re = z.1 := by
  rw [equivRealProdCLM_symm_endChart, re_endCoord_cylindricalEndLift,
    Complex.equivRealProdCLM_symm_apply_re]

/-- The norm of the image of `(s, t)` under the end chart is `exp (2π ε s)`. -/
theorem norm_symm_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (p.endChart z)‖ =
      Real.exp (2 * π * (p.endSign * z.1)) := by
  rw [equivRealProdCLM_symm_endChart, norm_cylindricalEndLift,
    Complex.equivRealProdCLM_symm_apply_re]

/-- When `log r / (2π) ≤ a`, the half-cylinder `s > a` in `positive.endChart` lies in the exterior
`{‖w‖ > r}`. -/
theorem lt_norm_symm_endChart_positive {r a : ℝ}
    (hr : Real.log r / (2 * π) ≤ a) {z : ℝ × ℝ} (hz : a < z.1) :
    r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ := by
  rw [norm_symm_endChart, endSign_positive, one_mul]
  rcases le_or_gt r 0 with hr₀ | hr₀
  · exact hr₀.trans_lt (Real.exp_pos _)
  · rw [← Real.exp_log hr₀, Real.exp_lt_exp]
    have hlog : Real.log r ≤ 2 * π * a := by
      rwa [div_le_iff₀ Real.two_pi_pos, mul_comm] at hr
    nlinarith [Real.pi_pos]

/-- The end chart is `1`-periodic in the angular coordinate. -/
theorem endChart_add_one (p : PSSPlane) (s t : ℝ) :
    p.endChart (s, t + 1) = p.endChart (s, t) := by
  rw [endChart_mk, endChart_mk]
  exact congrArg Complex.equivRealProdCLM (by exact_mod_cast p.periodic_cylindricalEndLift s t)

/-- The end chart of the negative plane is that of the positive plane composed with negation. -/
theorem endChart_negative (z : ℝ × ℝ) :
    negative.endChart z = positive.endChart (-z) := by
  rw [endChart_apply, endChart_apply, map_neg, cylindricalEndLift_negative]

/-- Scaling by the end sign turns the end chart of either plane into `positive.endChart`. -/
@[simp]
theorem endChart_endSign_smul (p : PSSPlane) (z : ℝ × ℝ) :
    p.endChart (p.endSign • z) = positive.endChart z := by
  cases p
  · simp [endSign_positive]
  · simp [endSign_negative, endChart_negative]

/-- The end chart of a PSS plane is `positive.endChart` composed with `z ↦ ε • z`. -/
theorem endChart_eq_positive_endChart_endSign_smul (p : PSSPlane) (z : ℝ × ℝ) :
    p.endChart z = positive.endChart (p.endSign • z) := by
  rw [← p.endChart_endSign_smul (p.endSign • z), smul_smul, endSign_mul_endSign, one_smul]

/-- The end chart at `(ε s, t)` is the positive end chart at `(s, ε t)`. -/
theorem endChart_endSign_mul (p : PSSPlane) (s t : ℝ) :
    p.endChart (p.endSign * s, t) = positive.endChart (s, p.endSign * t) := by
  rw [p.endChart_eq_positive_endChart_endSign_smul, Prod.smul_mk, smul_eq_mul, smul_eq_mul,
    endSign_mul_endSign_mul]

/-- The end chart is smooth of every order. -/
theorem contDiff_endChart (p : PSSPlane) {n : WithTop ℕ∞} : ContDiff ℝ n p.endChart :=
  contDiff_realChart p.contDiff_cylindricalEndLift

/-- The end chart is a local diffeomorphism: its Jacobian determinant is everywhere positive. -/
theorem det_fderiv_endChart_pos (p : PSSPlane) (z : ℝ × ℝ) :
    0 < (fderiv ℝ p.endChart z).det := by
  rw [endChart_def]
  exact p.det_fderiv_realChart_cylindricalEndLift_pos z

/-- The end chart is holomorphic: its derivative is complex linear everywhere. -/
theorem isComplexLinearMap_fderiv_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ p.endChart z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [endChart_def]
  exact Floer.isComplexLinearMap_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)

/-- The end chart is injective on every horizontal strip `ℝ × [t₀, t₀ + 1)` of angular width
one. -/
theorem injOn_endChart_univ_prod_Ico (p : PSSPlane) (t₀ : ℝ) :
    InjOn p.endChart (univ ×ˢ Ico t₀ (t₀ + 1)) := by
  intro a ha b hb hab
  rw [endChart_apply, endChart_apply] at hab
  have h := p.injOn_cylindricalEndLift t₀
    (by simpa [Complex.equivRealProdCLM_symm_apply_im] using ha.2)
    (by simpa [Complex.equivRealProdCLM_symm_apply_im] using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- A map composed with `p.endChart` is differentiable at `z` whenever its composition with
`positive.endChart` is differentiable at `ε • z`. -/
theorem differentiableAt_comp_endChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : PSSPlane) {u : ℝ × ℝ → E} {z : ℝ × ℝ}
    (hu : DifferentiableAt ℝ (u ∘ positive.endChart) (p.endSign • z)) :
    DifferentiableAt ℝ (u ∘ p.endChart) z := by
  have heq : u ∘ p.endChart = (u ∘ positive.endChart) ∘ fun w : ℝ × ℝ ↦ p.endSign • w := by
    funext w
    simp [comp_apply, p.endChart_eq_positive_endChart_endSign_smul]
  rw [heq]
  exact hu.comp z ((differentiableAt_id).const_smul p.endSign)

/-- The derivative of `u ∘ p.endChart` at `z` is `ε` times the derivative of
`u ∘ positive.endChart` at `ε • z`. -/
theorem fderiv_comp_endChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : PSSPlane) {u : ℝ × ℝ → E} {z : ℝ × ℝ}
    (hu : DifferentiableAt ℝ (u ∘ positive.endChart) (p.endSign • z)) :
    fderiv ℝ (u ∘ p.endChart) z = p.endSign • fderiv ℝ (u ∘ positive.endChart) (p.endSign • z) := by
  have heq : u ∘ p.endChart = (u ∘ positive.endChart) ∘ fun w : ℝ × ℝ ↦ p.endSign • w := by
    funext w
    simp [comp_apply, p.endChart_eq_positive_endChart_endSign_smul]
  have hd : HasFDerivAt (u ∘ p.endChart)
      ((fderiv ℝ (u ∘ positive.endChart) (p.endSign • z)).comp
        (p.endSign • ContinuousLinearMap.id ℝ (ℝ × ℝ))) z := by
    rw [heq]
    exact hu.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul p.endSign)
  rw [hd.fderiv]
  exact ContinuousLinearMap.ext fun v ↦ by simp

/-- For any set `P` of longitudinal coordinates, `positive.endChart` maps `P × [0, 1)` onto the set
of nonzero points `w` with `log ‖w‖ / (2π) ∈ P`. -/
theorem image_endChart_positive_prod_Ico (P : Set ℝ) :
    positive.endChart '' (P ×ˢ Ico 0 1) =
      {z | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Real.log ‖Complex.equivRealProdCLM.symm z‖ / (2 * π) ∈ P} := by
  ext z
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mem_ofPred_eq, equivRealProdCLM_symm_endChart]
    refine ⟨positive.cylindricalEndLift_ne_zero _, ?_⟩
    rw [norm_cylindricalEndLift, endSign_positive, one_mul,
      Complex.equivRealProdCLM_symm_apply_re, Real.log_exp,
      mul_div_cancel_left₀ _ Real.two_pi_pos.ne']
    exact hζ.1
  · rintro ⟨hw₀, hz⟩
    set w := Complex.equivRealProdCLM.symm z
    set ζ := positive.endCoord w
    have hζre : ζ.re = Real.log ‖w‖ / (2 * π) := by
      simpa [ζ, endSign_positive] using positive.endSign_mul_re_endCoord w
    refine ⟨(ζ.re, Int.fract ζ.im), ⟨hζre ▸ hz, Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    have hper := (positive.periodic_cylindricalEndLift ζ.re).sub_int_mul_eq (x := ζ.im) ⌊ζ.im⌋
    rw [mul_one] at hper
    rw [endChart_mk, Int.fract, hper, Complex.re_add_im, positive.cylindricalEndLift_endCoord hw₀,
      ContinuousLinearEquiv.apply_symm_apply]

/-- The positive end chart maps `(a, ∞) × [0, 1)` onto the exterior `{‖w‖ > exp (2πa)}`. -/
theorem image_endChart_positive_Ioi_prod_Ico (a : ℝ) :
    positive.endChart '' (Ioi a ×ˢ Ico 0 1) =
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} := by
  rw [image_endChart_positive_prod_Ico]
  ext z
  simp only [mem_ofPred_eq, mem_Ioi]
  set w := Complex.equivRealProdCLM.symm z
  constructor
  · rintro ⟨hw₀, ha⟩
    rw [lt_div_iff₀ Real.two_pi_pos, mul_comm, ← Real.exp_lt_exp, Real.exp_log (norm_pos_iff.2 hw₀)]
      at ha
    exact ha
  · intro ha
    have hwpos : 0 < ‖w‖ := (Real.exp_pos _).trans ha
    refine ⟨norm_pos_iff.1 hwpos, ?_⟩
    rw [lt_div_iff₀ Real.two_pi_pos, mul_comm, ← Real.log_exp (2 * π * a)]
    exact Real.log_lt_log (Real.exp_pos _) ha

/-- The positive end chart maps `[a, ∞) × [0, 1)` onto the exterior `{‖w‖ ≥ exp (2πa)}`. -/
theorem image_endChart_positive_Ici_prod_Ico (a : ℝ) :
    positive.endChart '' (Ici a ×ˢ Ico 0 1) =
      {z | Real.exp (2 * π * a) ≤ ‖Complex.equivRealProdCLM.symm z‖} := by
  rw [image_endChart_positive_prod_Ico]
  ext z
  simp only [mem_ofPred_eq, mem_Ici]
  set w := Complex.equivRealProdCLM.symm z
  constructor
  · rintro ⟨hw₀, ha⟩
    rw [le_div_iff₀ Real.two_pi_pos, mul_comm, ← Real.exp_le_exp, Real.exp_log (norm_pos_iff.2 hw₀)]
      at ha
    exact ha
  · intro ha
    have hwpos : 0 < ‖w‖ := (Real.exp_pos _).trans_le ha
    refine ⟨norm_pos_iff.1 hwpos, ?_⟩
    rw [le_div_iff₀ Real.two_pi_pos, mul_comm, ← Real.log_exp (2 * π * a)]
    exact Real.log_le_log (Real.exp_pos _) ha

/-- The Hamiltonian of a PSS plane in the positive end chart `positive.endChart`:
`H'_p(t, x) = ε H(ε t, x)`. It is `H` on the positive plane and `(t, x) ↦ -H(-t, x)` on the
negative plane. -/
def positiveEndHamiltonian {X : Type*} (p : PSSPlane) (H : ℝ → X → ℝ) (t : ℝ) (x : X) : ℝ :=
  p.endSign * H (p.endSign * t) x

theorem positiveEndHamiltonian_def {X : Type*} (p : PSSPlane) (H : ℝ → X → ℝ) (t : ℝ) (x : X) :
    p.positiveEndHamiltonian H t x = p.endSign * H (p.endSign * t) x :=
  (rfl)

@[simp]
theorem positiveEndHamiltonian_positive {X : Type*} (H : ℝ → X → ℝ) :
    positive.positiveEndHamiltonian H = H := by
  funext t x
  simp [positiveEndHamiltonian_def]

theorem positiveEndHamiltonian_negative {X : Type*} (H : ℝ → X → ℝ) :
    negative.positiveEndHamiltonian H = fun t x ↦ -H (-t) x := by
  funext t x
  simp [positiveEndHamiltonian_def]

/-- Passing to the positive end Hamiltonian twice recovers the original Hamiltonian. -/
@[simp]
theorem positiveEndHamiltonian_positiveEndHamiltonian {X : Type*} (p : PSSPlane) (H : ℝ → X → ℝ) :
    p.positiveEndHamiltonian (p.positiveEndHamiltonian H) = H := by
  funext t x
  simp [positiveEndHamiltonian_def]

/-- **Both PSS planes are positive PSS planes.** The perturbation of a PSS plane `p` for `H` is
that of the positive plane for `p.positiveEndHamiltonian H`. -/
theorem perturbation_eq_positive_positiveEndHamiltonian {X : Type*} (p : PSSPlane)
    (H : ℝ → X → ℝ) :
    p.perturbation H = positive.perturbation (p.positiveEndHamiltonian H) := by
  cases p
  · simp
  · rw [perturbation_negative, positiveEndHamiltonian_negative]

/-- A `c`-periodic map read with the signed time `ε t` of a PSS plane is `c`-periodic. -/
theorem periodic_comp_endSign_mul {α : Type*} (p : PSSPlane) {x : ℝ → α} {c : ℝ}
    (hx : Periodic x c) : Periodic (fun t ↦ x (p.endSign * t)) c := by
  cases p
  · simpa [endSign_positive] using hx
  · simpa [endSign_negative] using hx.comp_neg

/-- The positive end Hamiltonian of a `c`-periodic Hamiltonian is `c`-periodic. -/
theorem periodic_positiveEndHamiltonian {X : Type*} (p : PSSPlane) {H : ℝ → X → ℝ} {c : ℝ}
    (hH : Periodic H c) : Periodic (p.positiveEndHamiltonian H) c := by
  intro t
  funext x
  simpa [positiveEndHamiltonian_def] using
    congrArg (p.endSign * ·) (congrFun (p.periodic_comp_endSign_mul hH t) x)

/-- The positive end Hamiltonian of a `Cⁿ` Hamiltonian is `Cⁿ`. -/
theorem contDiff_uncurry_positiveEndHamiltonian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : PSSPlane) {H : ℝ → E → ℝ} {n : WithTop ℕ∞}
    (hH : ContDiff ℝ n (uncurry H)) : ContDiff ℝ n (uncurry (p.positiveEndHamiltonian H)) :=
  contDiff_const.mul (hH.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))

end Floer.PSSPlane

namespace SymplecticForm

open Floer Floer.PSSPlane

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V}
  {J : ℝ × ℝ → AlmostComplexStructure V} {K : Set V} {c M : ℝ}

/-! ### Pulling back the end of a PSS plane to the positive end chart -/

/-- At the signed time `ε t`, the Hamiltonian vector field of `p.positiveEndHamiltonian H` is `ε`
times that of `H` at time `t`. -/
theorem hamiltonianVectorField_pssPlane_positiveEndHamiltonian_endSign_mul (p : PSSPlane)
    (H : ℝ → V → ℝ) (t : ℝ) :
    ω.hamiltonianVectorField (p.positiveEndHamiltonian H (p.endSign * t)) =
      p.endSign • ω.hamiltonianVectorField (H t) := by
  funext y
  rw [Pi.smul_apply, ← hamiltonianVectorField_const_mul]
  congr 1
  funext x
  rw [positiveEndHamiltonian_def, endSign_mul_endSign_mul]

/-- Reading an orbit of `p.positiveEndHamiltonian H` with the signed time `ε t` gives an orbit of
`H`. -/
theorem hasDerivAt_comp_pssPlane_endSign_mul {p : PSSPlane} {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t) (x t)) t)
    (t : ℝ) :
    HasDerivAt (fun t ↦ x (p.endSign * t))
      (ω.hamiltonianVectorField (H t) (x (p.endSign * t))) t := by
  have h := (hx (p.endSign * t)).scomp t ((hasDerivAt_id' t).const_mul p.endSign)
  rw [hamiltonianVectorField_pssPlane_positiveEndHamiltonian_endSign_mul, mul_one, Pi.smul_apply,
    smul_smul, endSign_mul_endSign, one_smul] at h
  exact h

/-- Reading an orbit of `H` with the signed time `ε t` gives an orbit of
`p.positiveEndHamiltonian H`. -/
theorem hasDerivAt_comp_pssPlane_endSign_mul_positiveEndHamiltonian {p : PSSPlane} {y : ℝ → V}
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H t) (y t)) t) (t : ℝ) :
    HasDerivAt (fun t ↦ y (p.endSign * t))
      (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t) (y (p.endSign * t))) t :=
  hasDerivAt_comp_pssPlane_endSign_mul (p := p) (H := p.positiveEndHamiltonian H)
    (by simpa only [positiveEndHamiltonian_positiveEndHamiltonian] using hy) t

/-- **The Floer equation in the positive end chart of a PSS plane.** For `s ≥ 2`, if `u` solves
the Floer equation for `p.perturbation H` at `positive.endChart z`, then `u ∘ positive.endChart`
solves the half-cylinder Floer equation for `p.positiveEndHamiltonian H` at `z`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_endChart_positive (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {J : AlmostComplexStructure V}
    {z : ℝ × ℝ} (hz : 2 ≤ z.1) (hu : DifferentiableAt ℝ u (positive.endChart z))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (positive.endChart z) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
        (u ∘ positive.endChart) z : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [p.perturbation_eq_positive_positiveEndHamiltonian] at hfloer
  rw [endChart_def] at hu hfloer ⊢
  exact ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_positive
    (p.periodic_positiveEndHamiltonian hH) (p.contDiff_uncurry_positiveEndHamiltonian hHs) hz hu
    hfloer

/-- From `s = 2` on, the energy density of `u ∘ positive.endChart` for `p.positiveEndHamiltonian H`
is the Jacobian determinant of `positive.endChart` times the energy density of `u` for
`p.perturbation H`. -/
private theorem floerEnergyDensity_comp_endChart_positive (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) {z : ℝ × ℝ} (hz : 2 ≤ z.1)
    (hu : DifferentiableAt ℝ u (positive.endChart z)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
        (u ∘ positive.endChart) z =
      (fderiv ℝ positive.endChart z).det *
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          (positive.endChart z) := by
  have hpull : ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ p.positiveEndHamiltonian H w.2)
      (u ∘ positive.endChart) z =
      ω.perturbedFDeriv
        (perturbationPullback positive.endChart
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback positive.endChart
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag)
        (u ∘ positive.endChart) z := by
    rw [p.perturbation_eq_positive_positiveEndHamiltonian, endChart_def,
      positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineReal,
      positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineImag
        (p.periodic_positiveEndHamiltonian hH)]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [perturbedFDeriv_apply, endSign_positive, one_mul,
      smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ z.1 - 1)]
  rw [floerEnergyDensity_def, hpull, ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    ((positive.contDiff_endChart (n := 1)).differentiable one_ne_zero z) hu
    (differentiableAt_perturbation_target hH hHs _ _ 1)
    (differentiableAt_perturbation_target hH hHs _ _ Complex.I)

/-- For any measurable set `P ⊆ [2, ∞)` of longitudinal coordinates, the half-cylinder energy of
`u ∘ positive.endChart` over `P × [0, 1]` for `p.positiveEndHamiltonian H` equals the Floer energy
of `u` for `p.perturbation H` over `positive.endChart '' (P × [0, 1))`. -/
theorem setLIntegral_floerEnergyDensity_comp_endChart_positive_prod_Icc_eq (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {P : Set ℝ} {U : Set (ℝ × ℝ)}
    (hP : MeasurableSet P) (hP₂ : P ⊆ Ici 2) (hU : IsOpen U)
    (hPU : positive.endChart '' (P ×ˢ Ico 0 1) ⊆ U) (hu : DifferentiableOn ℝ u U) :
    ∫⁻ z in P ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) =
      ∫⁻ z in positive.endChart '' (P ×ˢ Ico 0 1),
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  have hS : MeasurableSet (P ×ˢ Ico (0 : ℝ) 1) := hP.prod measurableSet_Ico
  have hae : (P ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] P ×ˢ Ico 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc.symm
  have hinj : InjOn positive.endChart (P ×ˢ Ico (0 : ℝ) 1) :=
    (positive.injOn_endChart_univ_prod_Ico 0).mono (prod_mono (subset_univ _) (by simp))
  rw [setLIntegral_congr hae]
  refine (lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hS hinj
    (fun z _ ↦ (positive.contDiff_endChart (n := 1)).differentiable one_ne_zero z)
    fun z hz ↦ ?_).symm
  have hud : DifferentiableAt ℝ u (positive.endChart z) :=
    hu.differentiableAt (hU.mem_nhds (hPU (mem_image_of_mem _ hz)))
  rw [floerEnergyDensity_comp_endChart_positive p hH hHs (hP₂ hz.1) hud,
    abs_of_pos (positive.det_fderiv_endChart_pos z)]

/-- **Exact exterior energy on `(a, ∞)`.** For `a ≥ 2`, if `u` is differentiable on
`{‖w‖ > exp (2πa)}`, then the half-cylinder energy of `u ∘ positive.endChart` over
`(a, ∞) × [0, 1]` for `p.positiveEndHamiltonian H` equals the Floer energy of `u` for
`p.perturbation H` over `{‖w‖ > exp (2πa)}`. -/
theorem setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_eq (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {a : ℝ} (ha : 2 ≤ a)
    (hu : DifferentiableOn ℝ u
      {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖}) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) =
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  rw [← image_endChart_positive_Ioi_prod_Ico a]
  exact ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_prod_Icc_eq p hH hHs
    measurableSet_Ioi (fun _ hs ↦ ha.trans hs.le) (isOpen_lt continuous_const (by fun_prop))
    (image_endChart_positive_Ioi_prod_Ico a).subset hu

/-- **Exact exterior energy on `[a, ∞)`.** For `a ≥ 2` and `r < exp (2πa)`, if `u` is
differentiable on `{‖w‖ > r}`, then the half-cylinder energy of `u ∘ positive.endChart` over
`[a, ∞) × [0, 1]` for `p.positiveEndHamiltonian H` equals the Floer energy of `u` for
`p.perturbation H` over `{‖w‖ ≥ exp (2πa)}`. -/
theorem setLIntegral_floerEnergyDensity_comp_endChart_positive_Ici_eq (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r a : ℝ} (ha : 2 ≤ a)
    (hra : r < Real.exp (2 * π * a))
    (hu : DifferentiableOn ℝ u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) :
    ∫⁻ z in Ici a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) =
      ∫⁻ z in {z | Real.exp (2 * π * a) ≤ ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
  rw [← image_endChart_positive_Ici_prod_Ico a]
  exact ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_prod_Icc_eq p hH hHs
    measurableSet_Ici (Ici_subset_Ici.2 ha) (isOpen_lt continuous_const (by fun_prop))
    ((image_endChart_positive_Ici_prod_Ico a).subset.trans fun _ hz ↦ hra.trans_le hz) hu

/-- If `u` is differentiable with finite Floer energy on `{‖w‖ > r}`, then for any
`a ≥ max 2 (log r / (2π))` the half-cylinder energy of `u ∘ positive.endChart` over
`(a, ∞) × [0, 1]` is finite. -/
theorem setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_ne_top (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r a : ℝ} (ha : 2 ≤ a)
    (hr : Real.log r / (2 * π) ≤ a)
    (hu : DifferentiableOn ℝ u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ p.positiveEndHamiltonian H w.2) (u ∘ positive.endChart) z) ≠ ⊤ := by
  have hsub : {z : ℝ × ℝ | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
      {z | r < ‖Complex.equivRealProdCLM.symm z‖} := by
    rw [← image_endChart_positive_Ioi_prod_Ico a]
    rintro _ ⟨z, hz, rfl⟩
    exact lt_norm_symm_endChart_positive hr hz.1
  rw [ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_eq p hH hHs ha (hu.mono hsub)]
  exact ne_top_of_le_ne_top hE (lintegral_mono_set hsub)

/-! ### Uniform convergence at a nondegenerate end -/

/-- An orbit of `p.positiveEndHamiltonian H` whose time-reversed counterpart starts at a
nondegenerate fixed point of the time-one map of `H` is isolated among the `1`-periodic orbits of
`p.positiveEndHamiltonian H`. -/
private theorem exists_pos_forall_eq_of_isNondegenerateFixedPt {p : PSSPlane} {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (p.positiveEndHamiltonian H t) (y t)) t) →
      dist (y 0) (x 0) < ε → y = x := by
  have hiso := hnd.eventually_not_isFixedPt
  rw [timeDependentHamiltonianFlow_eq, ← zero_add (1 : ℝ)] at hiso
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_periodic_eq_of_eventually_not_isFixedPt _
    (hasDerivAt_comp_pssPlane_endSign_mul (p := p) hx) (s := 0)
    (by simpa only [mul_zero] using hiso)
  refine ⟨ε, hε, fun y hyper hy hyx ↦ funext fun t ↦ ?_⟩
  have hxy := congrFun (h _ (hasDerivAt_comp_pssPlane_endSign_mul (p := p) hy)
    (p.periodic_comp_endSign_mul hyper) (by simpa only [mul_zero] using hyx)) (p.endSign * t)
  simpa only [endSign_mul_endSign_mul] using hxy

/-- **The end of a finite-energy PSS plane converges to a nondegenerate orbit.** Let `𝔎` be the
perturbation of a PSS plane `p` given by a `1`-periodic `C¹` Hamiltonian `H`, and let `u` be `C¹`
on `{‖w‖ > r}`, with image in a compact set `K`, solving `(du - X_𝔎)^{0,1} = 0` there with finite
energy. Suppose that on some half-cylinder `s > b` of `positive.endChart` the derivative of
`u ∘ positive.endChart` is bounded and the almost complex structures are uniformly tame,
`c ‖v‖² ≤ ω(v, J v)` and `‖J v‖ ≤ M ‖v‖` with `c > 0`. Suppose moreover that the suspended
Hamiltonian vector field of `H` is globally Lipschitz and that every `1`-periodic orbit `x` of `H`
in `K` is nondegenerate: `x(0)` is a nondegenerate fixed point of the time-one map. Then the end
loops `t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a single `1`-periodic orbit of `H`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop := by
  set a := max (max 2 b) (Real.log r / (2 * π))
  have ha₂ : 2 ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hz
  have hmem (z : ℝ × ℝ) (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) hz
  set H' := p.positiveEndHamiltonian H
  have hH' : ContDiff ℝ 1 (uncurry H') := p.contDiff_uncurry_positiveEndHamiltonian hHs
  have hH'per : Periodic H' 1 := p.periodic_positiveEndHamiltonian hH
  have hfloer' (z : ℝ × ℝ) (hz : z ∈ Ioi a ×ˢ Icc 0 1) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) ((J ∘ positive.endChart) z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H' w.2) (u ∘ positive.endChart) z :
          ℝ × ℝ →ₗ[ℝ] V) :=
    ω.isComplexLinearMap_perturbedFDeriv_comp_endChart_positive p hH hHs (ha₂.trans hz.1.le)
      ((hu.differentiableOn one_ne_zero).differentiableAt
        ((isOpen_lt continuous_const (by fun_prop)).mem_nhds (hmem z hz.1)))
      (hfloer _ (hmem z hz.1))
  have hE' := ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_ne_top p hH hHs ha₂
    (le_max_right _ _) (hu.differentiableOn one_ne_zero) hE
  have hfin := lintegral_norm_sq_sliceDefect_ne_top (measurableSet_Ioi.prod measurableSet_Icc) hc
    (fun z hz v ↦ hJc z (hab z hz.1) v) (fun z hz v ↦ hJM z (hab z hz.1) v) hfloer' hE'
  obtain ⟨y, hyper, hy, huy⟩ := exists_periodic_hasDerivAt_tendstoUniformly_atTop
    (hu.comp (positive.contDiff_endChart (n := 1)).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, endChart_add_one]) hK
    (fun s hs t ↦ huK _ (hmem (s, t) hs))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH')).continuous
    (fun v t ↦ by simp only [hH'per t]) hfin (fun z hz ↦ hC z (hab z hz.1))
    fun y hyper hy hyK ↦ by
      have hnd₀ := hnd _ (p.periodic_comp_endSign_mul hyper)
        (hasDerivAt_comp_pssPlane_endSign_mul (p := p) hy) fun t ↦ hyK _
      rw [mul_zero] at hnd₀
      obtain ⟨ε, hε, h⟩ := exists_pos_forall_eq_of_isNondegenerateFixedPt hL hy hnd₀
      exact ⟨ε, hε, fun y' hy'per hy' _ hy'y ↦ h y' hy'per hy' (hy'y 0)⟩
  refine ⟨fun t ↦ y (p.endSign * t), p.periodic_comp_endSign_mul hyper,
    hasDerivAt_comp_pssPlane_endSign_mul (p := p) hy, ?_⟩
  have hloop (R : ℝ) : (fun t ↦ u (p.endChart (p.endSign * R, t))) =
      (fun t ↦ (u ∘ positive.endChart) (R, t)) ∘ fun t ↦ p.endSign * t := by
    funext t
    simp only [comp_apply, endChart_endSign_mul]
  rw [funext hloop]
  exact huy.comp _

/-- **The energy of a finite-energy PSS plane with a nondegenerate end.** Let `𝔎` be the
perturbation of a PSS plane `p` given by a `1`-periodic `C¹` Hamiltonian `H` whose suspended
Hamiltonian vector field is globally Lipschitz, and let `u` be a `C²` solution of
`(du - X_𝔎)^{0,1} = 0` on the whole plane for tamed almost complex structures `J(z)`, with finite
energy. Suppose that on `{‖w‖ > r}` the image of `u` lies in a compact set `K` in which every
`1`-periodic orbit of `H` is nondegenerate, `c ‖v‖² ≤ ω(v, J(z) v)` and `‖J(z) v‖ ≤ M ‖v‖` with
`c > 0`, and `u ∘ positive.endChart` has bounded derivative on some half-cylinder `s > b`. Then the
end loops `ℓ_R(t) = u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a `1`-periodic orbit `x` of
`H`, their actions `A_H(ℓ_R)` converge to `A_H(x)`, and `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isNondegenerateFixedPt
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K) (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0))
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  obtain ⟨x, hxper, hx, ⟨σ, hσ, hσx⟩, hA, hEx⟩ :=
    exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq p hH hHs hu hK
      huK hc hJc hJM hJ hfloer hE
  set b' := max b (Real.log r / (2 * π))
  have hmem (z : ℝ × ℝ) (hz : b' < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) hz
  obtain ⟨x', -, -, hx'⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation p hH hHs
      (hu.of_le one_le_two).contDiffOn hK huK (fun z _ ↦ hfloer z)
      ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne hL hnd
      (fun z hz ↦ hC z ((le_max_left _ _).trans_lt hz)) hc
      (fun z hz v ↦ hJc _ (hmem z hz) v) (fun z hz v ↦ hJM _ (hmem z hz) v)
  simp_rw [← endChart_mk] at hσx hA
  have hxx' : x = x' := funext fun t ↦
    tendsto_nhds_unique (hσx.tendsto_at t) ((hx'.tendsto_at t).comp hσ)
  exact ⟨x, hxper, hx, hxx' ▸ hx', hA, hEx⟩

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {T₀ : ℝ} {u : ℝ × ℝ → V}
  {J : ℝ × ℝ → AlmostComplexStructure V} {K : Set V} {W : Set (ℝ × V)}
  {J₀ : ℝ → V → AlmostComplexStructure V}

/-! ### Bounded derivatives and convergence on cylindrical ends -/

omit [FiniteDimensional ℝ V] in
/-- An almost complex structure which is `J₀(t)` along the end of `p` beyond `T₀` is `J₀(ε t)` in
`positive.endChart`. -/
private theorem eq_comp_endChart_positive {p : PSSPlane}
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {z : ℝ × ℝ} (hz : T₀ ≤ z.1) :
    J (positive.endChart z) = J₀ (p.endSign * z.2) ((u ∘ positive.endChart) z) := by
  obtain ⟨s, t⟩ := z
  have h := hJ s (p.endSign * t) hz
  rwa [endChart_endSign_mul, endSign_mul_endSign_mul] at h

/-- **Bounded derivative in the positive end chart on a cylindrical end of a PSS plane.** Let `𝔎`
be the perturbation of a PSS plane `p` given by a `1`-periodic `C³` Hamiltonian `H`, and let `u` be
`C³` on `{‖w‖ > r}`, with image in a compact set `K`, solving `(du - X_𝔎)^{0,1} = 0` there with
finite energy. Suppose that for `s ≥ T₀` the almost complex structure is cylindrical,
`J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family `J₀` which is `C²` on an open
set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`. Then for every `b > max (max T₀ 2) (log r / (2π))` the
derivative of `u ∘ positive.endChart` is bounded on `s ≥ b`. -/
theorem exists_forall_norm_fderiv_comp_endChart_positive_le (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {b : ℝ} (hb : max (max T₀ 2) (Real.log r / (2 * π)) < b) :
    ∃ C, ∀ z : ℝ × ℝ, b ≤ z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C := by
  set a := max (max T₀ 2) (Real.log r / (2 * π))
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have ha₂ : 2 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have hmem (z : ℝ × ℝ) (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (positive.endChart z)‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) hz
  set g : ℝ × V → ℝ × V := fun q ↦ (p.endSign * q.1, q.2)
  have hg : ContDiff ℝ 2 g := (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  have hHs1 : ContDiff ℝ 1 (uncurry H) := hHs.of_le (by norm_num)
  exact exists_forall_norm_fderiv_le_of_floer (u := u ∘ positive.endChart)
    (J := fun t x ↦ J₀ (p.endSign * t) x) (W := g ⁻¹' W)
    (p.contDiff_uncurry_positiveEndHamiltonian hHs) (p.periodic_positiveEndHamiltonian hH)
    (hW.preimage hg.continuous) (hJ₀.comp hg.contDiffOn (mapsTo_preimage g W))
    (p.periodic_comp_endSign_mul hJ₀per) hK
    (fun q hq ↦ hKW ⟨mem_univ _, hq.2⟩) (fun t x hx ↦ hJ₀t _ x hx)
    (hu.comp (positive.contDiff_endChart (n := 3)).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, endChart_add_one])
    (fun s hs t ↦ huK _ (hmem (s, t) hs))
    (fun z hz ↦ by
      rw [← eq_comp_endChart_positive hJ (haT.trans hz.1.le)]
      exact ω.isComplexLinearMap_perturbedFDeriv_comp_endChart_positive p hH hHs1
        (ha₂.trans hz.1.le)
        ((hu.differentiableOn (by norm_num)).differentiableAt
          ((isOpen_lt continuous_const (by fun_prop)).mem_nhds (hmem z hz.1)))
        (hfloer _ (hmem z hz.1)))
    (ω.setLIntegral_floerEnergyDensity_comp_endChart_positive_Ioi_ne_top p hH hHs1 ha₂
      (le_max_right _ _) (hu.differentiableOn (by norm_num)) hE)
    hb

/-- **Bounded derivative in the end chart on a cylindrical end of a PSS plane.** Under the
hypotheses of `exists_forall_norm_fderiv_comp_endChart_positive_le`, the derivative of
`u ∘ p.endChart` is bounded on the half-cylinder `ε s ≥ b`. -/
theorem exists_forall_norm_fderiv_comp_endChart_le (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {b : ℝ} (hb : max (max T₀ 2) (Real.log r / (2 * π)) < b) :
    ∃ C, ∀ z : ℝ × ℝ, b ≤ p.endSign * z.1 → ‖fderiv ℝ (u ∘ p.endChart) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_comp_endChart_positive_le p hH hHs hu hK huK hfloer
    hE hW hJ₀ hJ₀per hKW hJ₀t hJ hb
  refine ⟨C, fun z hz ↦ ?_⟩
  have hmem : r < ‖Complex.equivRealProdCLM.symm (positive.endChart (p.endSign • z))‖ :=
    lt_norm_symm_endChart_positive (le_max_right _ _) (hb.trans_le hz)
  have hd : DifferentiableAt ℝ (u ∘ positive.endChart) (p.endSign • z) :=
    ((hu.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hmem)).comp _
      ((positive.contDiff_endChart (n := 1)).differentiable one_ne_zero _)
  rw [p.fderiv_comp_endChart hd, norm_smul, Real.norm_eq_abs, abs_endSign, one_mul]
  exact hC (p.endSign • z) hz

/-- **Derivative and tameness bounds on a cylindrical end of a PSS plane.** Under the hypotheses
of `exists_forall_norm_fderiv_comp_endChart_positive_le`, on some half-cylinder `s > b` of
`positive.endChart` the derivative of `u ∘ positive.endChart` is bounded and the almost complex
structures are uniformly tame. -/
theorem exists_forall_norm_fderiv_comp_endChart_positive_le_and_tame (p : PSSPlane)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t)))) :
    ∃ b C c, 0 < c ∧ ∃ M,
      (∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positive.endChart) z‖ ≤ C) ∧
      (∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positive.endChart z) v)) ∧
      ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positive.endChart z) v‖ ≤ M * ‖v‖ := by
  set a := max (max T₀ 2) (Real.log r / (2 * π))
  set b := a + 1
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_comp_endChart_positive_le p hH hHs hu hK huK hfloer
    hE hW hJ₀ hJ₀per hKW hJ₀t hJ (lt_add_one a)
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJ₀.continuousOn.mono hKW) hJ₀per hJ₀t
  have hbT (z : ℝ × ℝ) (hz : b < z.1) : T₀ ≤ z.1 :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans ((lt_add_one a).trans hz).le
  have huK' (z : ℝ × ℝ) (hz : b < z.1) : (u ∘ positive.endChart) z ∈ K :=
    huK _ (lt_norm_symm_endChart_positive (le_max_right _ _) ((lt_add_one a).trans hz))
  refine ⟨b, C, c, hc, M, fun z hz ↦ hC z hz.le, fun z hz v ↦ ?_, fun z hz v ↦ ?_⟩
  · rw [eq_comp_endChart_positive hJ (hbT z hz)]
    exact (hcM _ _ (huK' z hz) v).1
  · rw [eq_comp_endChart_positive hJ (hbT z hz)]
    exact (hcM _ _ (huK' z hz) v).2

/-- **The cylindrical end of a finite-energy PSS plane converges to a nondegenerate orbit.** Let
`𝔎` be the perturbation of a PSS plane `p` given by a `1`-periodic `C³` Hamiltonian `H` whose
suspended Hamiltonian vector field is globally Lipschitz, and let `u` be `C³` on `{‖w‖ > r}`, with
image in a compact set `K` in which every `1`-periodic orbit of `H` is nondegenerate, solving
`(du - X_𝔎)^{0,1} = 0` there with finite energy. Suppose that for `s ≥ T₀` the almost complex
structure is cylindrical, `J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family
`J₀` which is `C²` on an open set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`. Then the end loops
`t ↦ u(φ_p(ε R, t))` converge uniformly as `R → ∞` to a single `1`-periodic orbit of `H`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation_of_cylindrical
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {r : ℝ}
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖}) (hK : IsCompact K)
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop := by
  obtain ⟨b, C, c, hc, M, hC, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_endChart_positive_le_and_tame p hH hHs hu hK huK hfloer hE hW
      hJ₀ hJ₀per hKW hJ₀t hJ
  exact exists_periodic_hasDerivAt_tendstoUniformly_atTop_pssPlanePerturbation p hH
    (hHs.of_le (by norm_num)) (hu.of_le (by norm_num)) hK huK hfloer hE hL hnd hC hc hJc hJM

/-- **The energy of a finite-energy PSS plane with a cylindrical end.** Let `𝔎` be the perturbation
of a PSS plane `p` given by a `1`-periodic `C³` Hamiltonian `H` whose suspended Hamiltonian vector
field is globally Lipschitz, and let `u` be a `C³` solution of `(du - X_𝔎)^{0,1} = 0` on the whole
plane for tamed almost complex structures `J(z)`, with finite energy. Suppose that on `{‖w‖ > r}`
the image of `u` lies in a compact set `K` in which every `1`-periodic orbit of `H` is
nondegenerate, and that for `s ≥ T₀` the almost complex structure is cylindrical,
`J(φ_p(ε s, t)) = J₀(t, u(φ_p(ε s, t)))`, for a `1`-periodic family `J₀` which is `C²` on an open
set `W ⊇ ℝ × K` and tamed by `ω` on `ℝ × K`. Then the end loops `ℓ_R(t) = u(φ_p(ε R, t))` converge
uniformly as `R → ∞` to a `1`-periodic orbit `x` of `H`, their actions `A_H(ℓ_R)` converge to
`A_H(x)`, and `E(u) = ε A_H(x) - ∫_ℂ R_𝔎(u)`. -/
theorem exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_cylindrical
    (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) (hu : ContDiff ℝ 3 u)
    (hK : IsCompact K) {r : ℝ}
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJ₀ : ContDiffOn ℝ 2 (fun q : ℝ × V ↦ (J₀ q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJ₀per : Periodic J₀ 1) (hKW : univ ×ˢ K ⊆ W) (hJ₀t : ∀ t, ∀ x ∈ K, ω.Tames (J₀ t x))
    (hJcyl : ∀ s t, T₀ ≤ s →
      J (p.endChart (p.endSign * s, t)) = J₀ t (u (p.endChart (p.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      TendstoUniformly (fun R t ↦ u (p.endChart (p.endSign * R, t))) x atTop ∧
      Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (p.endChart (p.endSign * R, t)))) atTop
        (𝓝 (ω.hamiltonianAction H x)) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * ω.hamiltonianAction H x - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  have hE' : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤ :=
    ((setLIntegral_le_lintegral _ _).trans_lt hE.lt_top).ne
  obtain ⟨b, C, c, hc, M, hC, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_endChart_positive_le_and_tame p hH hHs hu.contDiffOn hK huK
      (fun z _ ↦ hfloer z) hE' hW hJ₀ hJ₀per hKW hJ₀t hJcyl
  set r' := max r (Real.exp (2 * π * b))
  have hr'r (z : ℝ × ℝ) (hz : r' < ‖Complex.equivRealProdCLM.symm z‖) :
      r < ‖Complex.equivRealProdCLM.symm z‖ :=
    (le_max_left _ _).trans_lt hz
  have hzb {z : ℝ × ℝ} (hz : r' < ‖Complex.equivRealProdCLM.symm z‖) :
      ∃ ζ ∈ Ioi b ×ˢ Ico (0 : ℝ) 1, positive.endChart ζ = z := by
    have hb' : z ∈ {w | Real.exp (2 * π * b) < ‖Complex.equivRealProdCLM.symm w‖} :=
      (le_max_right _ _).trans_lt hz
    rwa [← image_endChart_positive_Ioi_prod_Ico b] at hb'
  exact exists_lintegral_floerEnergyDensity_pssPlanePerturbation_eq_of_isNondegenerateFixedPt p hH
    (hHs.of_le (by norm_num)) (hu.of_le (by norm_num)) hK (r := r')
    (fun z hz ↦ huK z (hr'r z hz)) hc
    (fun z hz v ↦ by obtain ⟨ζ, hζ, rfl⟩ := hzb hz; exact hJc ζ hζ.1 v)
    (fun z hz v ↦ by obtain ⟨ζ, hζ, rfl⟩ := hzb hz; exact hJM ζ hζ.1 v)
    hJ hfloer hE hL hnd hC

end InnerProductSpace

end SymplecticForm

end TauCeti
