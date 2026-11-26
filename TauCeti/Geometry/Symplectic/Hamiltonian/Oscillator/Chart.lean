/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Hamiltonian
public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.PeriodLattice
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Symplectic.Darboux.Momenta

/-!
# The action–angle chart of uncoupled harmonic oscillators

Consider finitely many uncoupled harmonic oscillators, the `i`-th of mass `m i > 0` and angular
frequency `ν i > 0`, on the phase space `V × V`, `V = EuclideanSpace ℝ ι`, with its standard
symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ` and energies `Eᵢ` (`TauCeti.oscillatorEnergies`). Each phase
plane `(qᵢ, pᵢ)` has the action `Iᵢ = Eᵢ / νᵢ` and the angle `θᵢ ∈ ℝ / 2πℤ` of the single
oscillator (`TauCeti.oscillatorAction`, `TauCeti.oscillatorAngle`). This file shows that these
coordinates form a global action–angle chart, in the form of the Liouville–Arnold theorem
`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`, on the whole region
`U = {x | ∀ i, 0 < Eᵢ x}` where every oscillator is excited.

The chart (`TauCeti.oscillatorActionAngleChart`) sends `x` to the covector `Σⱼ Iⱼ dθⱼ` at the point
`(θⱼ)ⱼ` of the torus `Tⁿ = (ℝ / 2πℤ)^ι`, that is to `κ(θ, I)` for the action–angle covering map
`κ` of the cotangent bundle `T*Tⁿ` (`TauCeti.CotangentBundle.actionAngleCover`). It is injective
(`TauCeti.injective_oscillatorActionAngleChart`), maps `U` onto the covectors with positive actions
(`TauCeti.image_oscillatorActionAngleChart`), is a local diffeomorphism at every point of `U`
(`TauCeti.isLocalDiffeomorphAt_oscillatorActionAngleChart`) and pulls the canonical symplectic form
`ω = -dλ` of `T*Tⁿ` back to `ω₀` on `U`
(`TauCeti.eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart`). The energies are the
functions `Eᵢ = νᵢ Iᵢ` of the actions (`TauCeti.oscillatorEnergies_eq_mul_torusActions`), and the
chart carries the Hamiltonian vector field of `Eᵢ` to `νᵢ ∂_(θᵢ)`
(`TauCeti.mfderiv_oscillatorActionAngleChart_hamiltonianVectorField`). These are the clauses of
the conclusion of `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle` for the period `2π`, the
open sets `U` and `D = (0, ∞)^ι` and the function `h(I) = (νᵢ Iᵢ)ᵢ` of the actions, holding on all
of `U` rather than near a single compact level.

The proof goes through the product of the action–angle parametrizations of the single oscillators,
`Ψ(θ, I) = (oscillatorActionAngle (m i) (ν i) (θᵢ, Iᵢ))ᵢ`
(`TauCeti.oscillatorProductActionAngle`). For positive actions it is smooth and pulls `ω₀` back to
`Σⱼ dθⱼ ∧ dIⱼ` (`TauCeti.stdSymplecticForm_fderiv_oscillatorProductActionAngle`), so it is a local
diffeomorphism, and the chart undoes it: `Φ ∘ Ψ = κ` there
(`TauCeti.oscillatorActionAngleChart_oscillatorProductActionAngle`), while `Ψ` recovers every point
from any lift of its angles and its actions
(`TauCeti.oscillatorProductActionAngle_eq_self`). The local properties of the chart are then those
of `κ` composed with a local inverse of `Ψ`.

## Main definitions

* `TauCeti.oscillatorProductActionAngle m ν`: the product action–angle parametrization.
* `TauCeti.oscillatorActionAngleChart m ν`: the action–angle chart into the cotangent bundle of the
  torus `(ℝ / 2πℤ)^ι`.

## Main results

* `TauCeti.injective_oscillatorActionAngleChart`, `TauCeti.image_oscillatorActionAngleChart`,
  `TauCeti.isLocalDiffeomorphAt_oscillatorActionAngleChart`: the chart is a diffeomorphism of `U`
  onto the covectors with positive actions.
* `TauCeti.eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart`: it is symplectic.
* `TauCeti.oscillatorEnergies_eq_mul_torusActions`,
  `TauCeti.mfderiv_oscillatorActionAngleChart_hamiltonianVectorField`: in the chart, `Eᵢ = νᵢ Iᵢ`
  and the Hamiltonian vector field of `Eᵢ` is `νᵢ ∂_(θᵢ)`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49 and 50.
-/

public section

noncomputable section

open Set Real Function Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] {m ν : ι → ℝ}

local notation "𝕍" => EuclideanSpace ℝ ι

local instance oscillatorChartTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-! ### The product parametrization -/

/-- The **product action–angle parametrization** of uncoupled oscillators: at angles `θ` and
actions `I` in `ℝ^ι`, the `i`-th phase plane `(qᵢ, pᵢ)` of the point of `V × V` is the action–angle
parametrization `oscillatorActionAngle (m i) (ν i) (θᵢ, Iᵢ)` of the `i`-th oscillator. -/
def oscillatorProductActionAngle (m ν : ι → ℝ) (y : (ι → ℝ) × (ι → ℝ)) : 𝕍 × 𝕍 :=
  (WithLp.toLp 2 fun i ↦ (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).1,
    WithLp.toLp 2 fun i ↦ (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).2)

omit [Fintype ι] in
@[simp]
theorem oscillatorProductActionAngle_apply_fst (m ν : ι → ℝ) (y : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (oscillatorProductActionAngle m ν y).1 i =
      (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).1 :=
  (rfl)

omit [Fintype ι] in
@[simp]
theorem oscillatorProductActionAngle_apply_snd (m ν : ι → ℝ) (y : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (oscillatorProductActionAngle m ν y).2 i =
      (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).2 :=
  (rfl)

omit [Fintype ι] in
/-- The `i`-th phase plane of the product parametrization is the parametrization of the `i`-th
oscillator. -/
theorem oscillatorProductActionAngle_phasePlane (m ν : ι → ℝ) (y : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    ((oscillatorProductActionAngle m ν y).1 i, (oscillatorProductActionAngle m ν y).2 i) =
      oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i) :=
  (rfl)

omit [Fintype ι] in
/-- The open set of angles and actions at which every action is positive. -/
private theorem isOpen_setOf_forall_pos_snd [Finite ι] :
    IsOpen {y : (ι → ℝ) × (ι → ℝ) | ∀ i, 0 < y.2 i} := by
  simpa [Set.pi] using (isOpen_set_pi finite_univ fun i (_ : i ∈ univ) ↦ isOpen_Ioi
    (a := (0 : ℝ))).preimage continuous_snd

/-- The phase plane `(θᵢ, Iᵢ)` of a pair of angles and actions, as a continuous linear map. -/
private def phasePlane (i : ι) : (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.proj i).prodMap (ContinuousLinearMap.proj i)

/-- The point of `V × V` with prescribed phase planes, as a continuous linear map. -/
private def ofPhasePlanes : (ι → ℝ × ℝ) →L[ℝ] 𝕍 × 𝕍 :=
  LinearMap.toContinuousLinearMap
    { toFun f := (WithLp.toLp 2 fun i ↦ (f i).1, WithLp.toLp 2 fun i ↦ (f i).2)
      map_add' f g := by ext i <;> simp
      map_smul' a f := by ext i <;> simp }

/-- **The derivative of the product parametrization.** At positive actions it acts on each phase
plane by the derivative of the parametrization of that oscillator. -/
private theorem hasFDerivAt_oscillatorProductActionAngle {y : (ι → ℝ) × (ι → ℝ)}
    (hy : ∀ i, 0 < y.2 i) :
    HasFDerivAt (oscillatorProductActionAngle m ν)
      (ofPhasePlanes.comp (ContinuousLinearMap.pi fun i ↦
        (fderiv ℝ (oscillatorActionAngle (m i) (ν i)) (y.1 i, y.2 i)).comp (phasePlane i))) y := by
  have hG : HasFDerivAt (fun z : (ι → ℝ) × (ι → ℝ) ↦
      fun i ↦ oscillatorActionAngle (m i) (ν i) (phasePlane i z))
      (ContinuousLinearMap.pi fun i ↦
        (fderiv ℝ (oscillatorActionAngle (m i) (ν i)) (y.1 i, y.2 i)).comp (phasePlane i)) y :=
    hasFDerivAt_pi.2 fun i ↦
      ((hasFDerivAt_oscillatorActionAngle (m i) (ν i) (y := (y.1 i, y.2 i)) (hy i)).differentiableAt
        |>.hasFDerivAt).comp y (phasePlane i).hasFDerivAt
  exact ofPhasePlanes.hasFDerivAt.comp y hG

/-- The product parametrization is smooth at positive actions. -/
theorem contDiffOn_oscillatorProductActionAngle :
    ContDiffOn ℝ ∞ (oscillatorProductActionAngle m ν) {y | ∀ i, 0 < y.2 i} := by
  have hG : ContDiffOn ℝ ∞ (fun z : (ι → ℝ) × (ι → ℝ) ↦
      fun i ↦ oscillatorActionAngle (m i) (ν i) (phasePlane i z)) {y | ∀ i, 0 < y.2 i} :=
    contDiffOn_pi.2 fun i ↦ contDiffOn_oscillatorActionAngle.comp
      (phasePlane i).contDiff.contDiffOn fun y hy ↦ hy i
  exact ofPhasePlanes.contDiff.comp_contDiffOn hG

/-- **The product parametrization is symplectic.** At positive actions it pulls the standard
symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ` of `V × V` back to `Σⱼ dθⱼ ∧ dIⱼ`: on tangent vectors `(a, b)`
and `(a', b')` it takes the value `Σⱼ (aⱼ b'ⱼ - a'ⱼ bⱼ)`. -/
theorem stdSymplecticForm_fderiv_oscillatorProductActionAngle (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i)
    (u v : (ι → ℝ) × (ι → ℝ)) :
    stdSymplecticForm (fderiv ℝ (oscillatorProductActionAngle m ν) y u)
        (fderiv ℝ (oscillatorProductActionAngle m ν) y v) =
      ∑ j, (u.1 j * v.2 j - v.1 j * u.2 j) := by
  rw [(hasFDerivAt_oscillatorProductActionAngle hy).fderiv]
  -- Each phase plane contributes the pullback of `dqᵢ ∧ dpᵢ` by the parametrization of the
  -- `i`-th oscillator, which is `dθᵢ ∧ dIᵢ`.
  have h (j : ι) := stdSymplecticForm_fderiv_oscillatorActionAngle (hm j) (hν j)
    (y := (y.1 j, y.2 j)) (hy j) (u.1 j, u.2 j) (v.1 j, v.2 j)
  simp only [stdSymplecticForm_apply, RCLike.inner_apply, conj_trivial] at h
  simp only [stdSymplecticForm_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simpa [ofPhasePlanes, phasePlane, Prod.map, mul_comm] using h j

/-- On the model spaces, the manifold derivative of the product parametrization is its derivative.
-/
private theorem mfderiv_oscillatorProductActionAngle_apply (y : (ι → ℝ) × (ι → ℝ))
    (u : (ι → ℝ) × (ι → ℝ)) :
    mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, 𝕍 × 𝕍) (oscillatorProductActionAngle m ν) y u =
      fderiv ℝ (oscillatorProductActionAngle m ν) y u := by
  rw [mfderiv_eq_fderiv]
  -- The self-model tangent equivalences act as identities.
  rfl

/-- The product parametrization is a local diffeomorphism at positive actions. -/
theorem isLocalDiffeomorphAt_oscillatorProductActionAngle (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i) :
    IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, 𝕍 × 𝕍) ∞
      (oscillatorProductActionAngle m ν) y := by
  refine isLocalDiffeomorphAt_of_injective_mfderiv
    contDiffOn_oscillatorProductActionAngle.contMDiffOn isOpen_setOf_forall_pos_snd hy
    BoundarylessManifold.isInteriorPoint (by simp)
    ((injective_iff_map_eq_zero _).2 fun u hu ↦ ?_) (by simp [Module.finrank_prod])
  have hu' := (mfderiv_oscillatorProductActionAngle_apply (m := m) (ν := ν) y u).symm.trans hu
  -- A vector killed by the differential pairs to zero with every vector under `Σ dθⱼ ∧ dIⱼ`.
  refine eq_of_forall_sum_mul_sub_mul_eq (c := (0 : (ι → ℝ) × (ι → ℝ))) fun w ↦ ?_
  have h := stdSymplecticForm_fderiv_oscillatorProductActionAngle hm hν hy u w
  rw [hu'] at h
  refine h.symm.trans ((LinearMap.map_zero₂ _ _).trans ?_)
  simp

/-! ### Angles, actions and the chart -/

omit [Fintype ι] in
/-- **The parametrization recovers each point.** For positive masses and frequencies, a point is
the image under the product parametrization of any real lifts of its angles together with its
actions. -/
theorem oscillatorProductActionAngle_eq_self (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    {x : 𝕍 × 𝕍} {θ : ι → ℝ}
    (hθ : ∀ i, (θ i : Real.Angle) = oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)) :
    oscillatorProductActionAngle m ν (θ, fun i ↦ oscillatorAction (m i) (ν i) (x.1 i, x.2 i)) =
      x := by
  have h (i : ι) := oscillatorActionAngle_oscillatorAction (hm i) (hν i) (hθ i)
  ext i
  · exact congrArg Prod.fst (h i)
  · exact congrArg Prod.snd (h i)

/-- The **action–angle chart** of uncoupled oscillators: a point `x` of `V × V` goes to the
covector `Σⱼ Iⱼ dθⱼ` of the torus `(ℝ / 2πℤ)^ι` at the angles `θⱼ` of the phase planes of `x`,
where `Iⱼ` are their actions (`TauCeti.oscillatorAngle`, `TauCeti.oscillatorAction`). -/
def oscillatorActionAngleChart (m ν : ι → ℝ) (x : 𝕍 × 𝕍) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle (2 * π)) :=
  CotangentBundle.actionAngleCover (2 * π)
    (fun i ↦ (oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)).toReal,
      fun i ↦ oscillatorAction (m i) (ν i) (x.1 i, x.2 i))

/-- **The chart in angle coordinates.** The chart sends `x` to `κ(θ, I)` for any real lifts `θ` of
the angles of `x`, where `I` are its actions and `κ` is the action–angle covering map of the
cotangent bundle of the torus. -/
theorem actionAngleCover_eq_oscillatorActionAngleChart {x : 𝕍 × 𝕍} {θ : ι → ℝ}
    (hθ : ∀ i, (θ i : Real.Angle) = oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)) :
    CotangentBundle.actionAngleCover (2 * π)
        (θ, fun i ↦ oscillatorAction (m i) (ν i) (x.1 i, x.2 i)) =
      oscillatorActionAngleChart m ν x := by
  refine (CotangentBundle.actionAngleCover_eq_actionAngleCover_iff _).2 ⟨rfl, ?_⟩
  -- Two lifts of the same angle differ by an integer multiple of `2π`.
  have h (i : ι) := (Real.Angle.angle_eq_iff_two_pi_dvd_sub.1
    ((Real.Angle.coe_toReal _).trans (hθ i).symm))
  choose k hk using h
  exact ⟨k, funext fun i ↦ by simp only [Pi.add_apply]; linarith [hk i]⟩

/-- **The chart undoes the parametrization.** At positive actions, the chart of the point with
angles `θ` and actions `I` is `κ(θ, I)`. -/
theorem oscillatorActionAngleChart_oscillatorProductActionAngle (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i) :
    oscillatorActionAngleChart m ν (oscillatorProductActionAngle m ν y) =
      CotangentBundle.actionAngleCover (2 * π) y := by
  rw [← actionAngleCover_eq_oscillatorActionAngleChart (θ := y.1) fun i ↦ by
    rw [oscillatorProductActionAngle_phasePlane, oscillatorAngle_oscillatorActionAngle (hm i) (hν i)
      (hy i)]]
  simp only [oscillatorProductActionAngle_phasePlane]
  congr 2
  funext i
  exact oscillatorAction_oscillatorActionAngle (hm i) (hν i) (hy i).le

variable [DecidableEq ι]

/-- The actions of the chart of `x` are the actions `Iᵢ = Eᵢ / νᵢ` of the phase planes of `x`. -/
@[simp]
theorem torusActions_oscillatorActionAngleChart (x : 𝕍 × 𝕍) :
    CotangentBundle.torusActions (2 * π) (oscillatorActionAngleChart m ν x) =
      fun i ↦ oscillatorAction (m i) (ν i) (x.1 i, x.2 i) :=
  CotangentBundle.torusActions_actionAngleCover _ _

omit [DecidableEq ι] in
/-- **The energies are functions of the actions.** For nonzero frequencies, `Eᵢ = νᵢ Iᵢ` for the
actions `Iᵢ` of the chart. -/
theorem oscillatorEnergies_eq_mul_torusActions [DecidableEq ι] (hν : ∀ i, ν i ≠ 0)
    (x : 𝕍 × 𝕍) :
    oscillatorEnergies m ν x =
      fun i ↦ ν i * CotangentBundle.torusActions (2 * π) (oscillatorActionAngleChart m ν x) i := by
  funext i
  simp only [torusActions_oscillatorActionAngleChart]
  rw [oscillatorAction_apply, oscillatorEnergies_apply, mul_div_cancel₀ _ (hν i)]

omit [DecidableEq ι] in
/-- **The action–angle chart is injective.** A point is determined by its actions and its angles. -/
theorem injective_oscillatorActionAngleChart (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i) :
    Injective (oscillatorActionAngleChart (ι := ι) m ν) := by
  intro x y hxy
  obtain ⟨hI, k, hk⟩ := (CotangentBundle.actionAngleCover_eq_actionAngleCover_iff _).1 hxy
  simp only at hI hk
  -- The angles of `y` are lifts of the angles of `x`, and the actions agree.
  have hθ (i : ι) : ((oscillatorAngle (m i) (ν i) (y.1 i, y.2 i)).toReal : Real.Angle) =
      oscillatorAngle (m i) (ν i) (x.1 i, x.2 i) := by
    rw [congrFun hk i, Pi.add_apply, Real.Angle.coe_add, ← zsmul_eq_mul, Real.Angle.coe_zsmul,
      Real.Angle.coe_two_pi, zsmul_zero, add_zero, Real.Angle.coe_toReal]
  calc x = _ := (oscillatorProductActionAngle_eq_self hm hν hθ).symm
    _ = _ := by rw [hI]
    _ = y := oscillatorProductActionAngle_eq_self hm hν fun i ↦ Real.Angle.coe_toReal _

/-- **The image of the chart.** The chart maps the points at which every energy is positive onto
the covectors of the torus all of whose actions are positive. -/
theorem image_oscillatorActionAngleChart (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i) :
    oscillatorActionAngleChart m ν '' {x | ∀ i, 0 < oscillatorEnergies m ν x i} =
      {z | ∀ i, 0 < CotangentBundle.torusActions (2 * π) z i} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    simp only [torusActions_oscillatorActionAngleChart]
    have h := hx i
    rw [oscillatorEnergies_apply] at h
    rw [oscillatorAction_apply]
    exact div_pos h (hν i)
  · intro hz
    obtain ⟨y, rfl⟩ := CotangentBundle.surjective_actionAngleCover (2 * π) z
    rw [mem_ofPred_eq, CotangentBundle.torusActions_actionAngleCover] at hz
    refine ⟨oscillatorProductActionAngle m ν y, fun i ↦ ?_,
      oscillatorActionAngleChart_oscillatorProductActionAngle hm hν hz⟩
    rw [oscillatorEnergies_apply, oscillatorProductActionAngle_phasePlane,
      oscillatorHamiltonian_oscillatorActionAngle (hm i) (hν i) (hz i).le]
    exact mul_pos (hν i) (hz i)

omit [DecidableEq ι] in
/-- A point at which every energy is positive is the image under the product parametrization of
the real lifts of its angles in `(-π, π]` and of its actions, which are positive. -/
private theorem exists_oscillatorProductActionAngle_eq (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    {x : 𝕍 × 𝕍} (hx : ∀ i, 0 < oscillatorEnergies m ν x i) :
    ∃ y : (ι → ℝ) × (ι → ℝ), (∀ i, 0 < y.2 i) ∧ oscillatorProductActionAngle m ν y = x ∧
      CotangentBundle.actionAngleCover (2 * π) y = oscillatorActionAngleChart m ν x :=
  ⟨_, fun i ↦ by
    dsimp only
    have h := hx i
    rw [oscillatorEnergies_apply] at h
    rw [oscillatorAction_apply]
    exact div_pos h (hν i),
    oscillatorProductActionAngle_eq_self hm hν fun i ↦ Real.Angle.coe_toReal _, rfl⟩

omit [DecidableEq ι] in
/-- Near positive actions, the chart composed with the parametrization is the action–angle covering
map `κ`. -/
private theorem eventuallyEq_oscillatorActionAngleChart_comp (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i) :
    oscillatorActionAngleChart m ν ∘ oscillatorProductActionAngle m ν =ᶠ[nhds y]
      CotangentBundle.actionAngleCover (2 * π) :=
  Filter.eventuallyEq_of_mem (isOpen_setOf_forall_pos_snd.mem_nhds hy) fun _ hz ↦
    oscillatorActionAngleChart_oscillatorProductActionAngle hm hν hz

omit [DecidableEq ι] in
/-- **The chart is a local diffeomorphism** at every point at which every energy is positive. -/
theorem isLocalDiffeomorphAt_oscillatorActionAngleChart (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    {x : 𝕍 × 𝕍} (hx : ∀ i, 0 < oscillatorEnergies m ν x i) :
    IsLocalDiffeomorphAt 𝓘(ℝ, 𝕍 × 𝕍)
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (oscillatorActionAngleChart m ν) x := by
  obtain ⟨y, hy, rfl, -⟩ := exists_oscillatorProductActionAngle_eq hm hν hx
  -- Near `x` the chart is `κ` after a local inverse of the parametrization.
  exact isLocalDiffeomorphAt_of_eqOn_comp isOpen_setOf_forall_pos_snd hy
    BoundarylessManifold.isInteriorPoint (by simp)
    (fun _ hz ↦ oscillatorActionAngleChart_oscillatorProductActionAngle hm hν hz)
    (CotangentBundle.contMDiff_actionAngleCover (2 * π)).contMDiffOn
    ((CotangentBundle.isLocalDiffeomorph_actionAngleCover (2 * π) y).isInvertible_mfderiv
      (by simp)).injective
    (by simp only [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq])
    (isLocalDiffeomorphAt_oscillatorProductActionAngle hm hν hy)

omit [DecidableEq ι] in
/-- **The action–angle chart is symplectic.** At every point at which every energy is positive,
the chart pulls the canonical symplectic form `ω = -dλ` of the cotangent bundle of the torus back
to the standard symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ`. -/
theorem eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {x : 𝕍 × 𝕍} (hx : ∀ i, 0 < oscillatorEnergies m ν x i)
    (v w : TangentSpace 𝓘(ℝ, 𝕍 × 𝕍) x) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (ι → AddCircle (2 * π)))
        (oscillatorActionAngleChart m ν x)
        (mfderiv 𝓘(ℝ, 𝕍 × 𝕍) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (oscillatorActionAngleChart m ν) x v)
        (mfderiv 𝓘(ℝ, 𝕍 × 𝕍) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (oscillatorActionAngleChart m ν) x w) =
      SmoothBundleForm.eval₂ (stdSymplecticForm (V := 𝕍)).constSmooth x v w := by
  have hΦ := isLocalDiffeomorphAt_oscillatorActionAngleChart hm hν hx
  obtain ⟨y, hy, rfl, -⟩ := exists_oscillatorProductActionAngle_eq hm hν hx
  have hΨ := isLocalDiffeomorphAt_oscillatorProductActionAngle hm hν hy
  -- Write `v` and `w` as images under the invertible differential of the parametrization.
  have hsurj := (hΨ.isInvertible_mfderiv (by simp)).surjective
  obtain ⟨v', rfl⟩ := hsurj v
  obtain ⟨w', rfl⟩ := hsurj w
  have hchain := mfderiv_apply_mfderiv_of_eventuallyEq_comp
    (eventuallyEq_oscillatorActionAngleChart_comp hm hν hy) (hΦ.mdifferentiableAt (by simp))
    (hΨ.mdifferentiableAt (by simp))
  rw [hchain, hchain, oscillatorActionAngleChart_oscillatorProductActionAngle hm hν hy,
    CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleCover]
  refine (stdSymplecticForm_fderiv_oscillatorProductActionAngle hm hν hy v' w').symm.trans ?_
  exact (congrArg₂ (fun a b : 𝕍 × 𝕍 ↦ stdSymplecticForm a b)
    (mfderiv_oscillatorProductActionAngle_apply y v').symm
    (mfderiv_oscillatorProductActionAngle_apply y w').symm).trans
    (SymplecticForm.constSmooth_apply _ _ _ _).symm

/-- **The Hamiltonian vector fields in the chart.** At every point at which every energy is
positive, the chart carries the Hamiltonian vector field of the energy `Eᵢ` to `νᵢ ∂_(θᵢ)`: its
image is the image of `(νᵢ eᵢ, 0)` under the differential of the action–angle covering map `κ` at
any angles and actions `(θ, I)` with `κ(θ, I)` the chart of the point. -/
theorem mfderiv_oscillatorActionAngleChart_hamiltonianVectorField (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {x : 𝕍 × 𝕍} (hx : ∀ i, 0 < oscillatorEnergies m ν x i)
    {y : (ι → ℝ) × (ι → ℝ)}
    (hy : CotangentBundle.actionAngleCover (2 * π) y = oscillatorActionAngleChart m ν x) (i : ι) :
    mfderiv 𝓘(ℝ, 𝕍 × 𝕍) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (oscillatorActionAngleChart m ν) x
        ((stdSymplecticForm (V := 𝕍)).constSmooth.hamiltonianVectorField
          (oscillatorEnergies m ν · i) x) =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (CotangentBundle.actionAngleCover (2 * π)) y (Pi.single i (ν i), 0) := by
  -- The energy `Eᵢ` is the function `I ↦ νᵢ Iᵢ` of the actions of the chart.
  have hh : HasFDerivAt (fun I : ι → ℝ ↦ ν i * I i)
      (ν i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) y.2 := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasFDerivAt.const_mul
      (ν i)
  have hE : (oscillatorEnergies m ν · i) =ᶠ[nhds x]
      (fun I : ι → ℝ ↦ ν i * I i) ∘ CotangentBundle.torusActions (2 * π) ∘
        oscillatorActionAngleChart m ν :=
    Filter.Eventually.of_forall fun x' ↦
      congrFun (oscillatorEnergies_eq_mul_torusActions (fun j ↦ (hν j).ne') x') i
  rw [CotangentBundle.mfderiv_hamiltonianVectorField_eq_mfderiv_actionAngleCover (2 * π)
    (SymplecticForm.isSymplectic_constSmooth _).isNondegenerate
    (isLocalDiffeomorphAt_oscillatorActionAngleChart hm hν hx)
    (eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart hm hν hx) hE hy
    hh.differentiableAt, hh.fderiv]
  congr 2
  funext j
  rcases eq_or_ne j i with rfl | hji <;> simp [*]

end TauCeti
