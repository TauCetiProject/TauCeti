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
# Global action–angle coordinates of uncoupled harmonic oscillators

Consider finitely many uncoupled harmonic oscillators, the `i`-th of mass `m i > 0` and angular
frequency `ν i > 0`, on the phase space `V × V`, `V = EuclideanSpace ℝ ι`, with its standard
symplectic form `ω₀ = Σ dqᵢ ∧ dpᵢ` and energies `Eᵢ(q, p) = pᵢ² / (2 mᵢ) + mᵢ νᵢ² qᵢ² / 2`
(`TauCeti.oscillatorEnergies`). This file shows that the action–angle coordinates of the single
oscillators (`TauCeti.oscillatorActionAngle`) assemble into **global action–angle coordinates**
on the region `{x | ∀ i, 0 < Eᵢ x}` where every oscillator is excited.

The model is the cotangent bundle `T*Tⁿ` of the angle torus `Tⁿ = ι → AddCircle (2π)`, with its
canonical symplectic form `ω = ∑ j, dθ_j ∧ dI_j`, in which a covector is read through its angles
and its actions `I_j = ξ(e_j)` (`TauCeti.CotangentBundle.torusActions`). The chart
(`TauCeti.oscillatorActionAngleChart`) sends a point to the covector whose angles are the angles
`TauCeti.oscillatorAngle` of its phase planes and whose actions are the actions
`Iᵢ = Eᵢ / νᵢ` (`TauCeti.oscillatorAction`). It is injective
(`TauCeti.injective_oscillatorActionAngleChart`), maps the excited region onto the covectors with
positive actions (`TauCeti.image_oscillatorActionAngleChart`), is a local diffeomorphism at every
excited point (`TauCeti.isLocalDiffeomorphAt_oscillatorActionAngleChart`) and pulls `ω` back to
`ω₀` there (`TauCeti.eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart`). In these
coordinates the energies are the linear functions `Eᵢ = νᵢ Iᵢ` of the actions
(`TauCeti.oscillatorEnergies_eq_mul_torusActions_oscillatorActionAngleChart`), and the Hamiltonian
vector field of `Eᵢ` is the constant field `νᵢ ∂_θᵢ`
(`TauCeti.mfderiv_oscillatorActionAngleChart_hamiltonianVectorField_oscillatorEnergies`). With
the period lattice
`⊕ᵢ (2π / νᵢ) ℤ` of `TauCeti.hamiltonianFlowStabilizer_oscillatorEnergies`, this is the
Liouville–Arnold normal form of the oscillators with no compactness or locality restriction: the
excited region is one action–angle chart.

The proof reads the chart through the product of the single action–angle parametrizations,
`Ψ(θ, I) = (oscillatorActionAngle (m i) (ν i) (θᵢ, Iᵢ))ᵢ`
(`TauCeti.oscillatorProductActionAngle`). It pulls `ω₀` back to `∑ i, dθᵢ ∧ dIᵢ`
(`TauCeti.stdSymplecticForm_fderiv_oscillatorProductActionAngle`), as the action–angle covering
map `κ` of `T*Tⁿ` (`TauCeti.CotangentBundle.actionAngleCover`) pulls back `ω`, and the chart turns
`Ψ` into `κ` (`TauCeti.oscillatorActionAngleChart_oscillatorProductActionAngle`). Both maps
identify exactly the points whose actions agree and whose angles differ by `2πℤ^ι`, so every
property of the chart is inherited from `κ` through the local diffeomorphism `Ψ`.

## Main definitions

* `TauCeti.oscillatorProductActionAngle m ν`: the product of the action–angle parametrizations of
  the single oscillators.
* `TauCeti.oscillatorActionAngleChart m ν`: the global action–angle chart, valued in the cotangent
  bundle of the torus `ι → AddCircle (2π)`.

## Main results

* `TauCeti.injective_oscillatorActionAngleChart`,
  `TauCeti.image_oscillatorActionAngleChart`,
  `TauCeti.isLocalDiffeomorphAt_oscillatorActionAngleChart`,
  `TauCeti.eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart`: the chart is an injective
  local diffeomorphism from the excited region onto the covectors with positive actions, carrying
  `ω` to `ω₀`.
* `TauCeti.oscillatorEnergies_eq_mul_torusActions_oscillatorActionAngleChart`,
  `TauCeti.mfderiv_oscillatorActionAngleChart_hamiltonianVectorField_oscillatorEnergies`: in the
  chart `Eᵢ = νᵢ Iᵢ` and
  `X_{Eᵢ} = νᵢ ∂_θᵢ`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49 and 50.
-/

public section

noncomputable section

open Set Function Real
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {ι : Type*} [Fintype ι] {m ν : ι → ℝ}

local notation "𝕍" => EuclideanSpace ℝ ι

/-! ### The product of the action–angle parametrizations -/

/-- The **product of the action–angle parametrizations** of uncoupled oscillators: the `i`-th
phase plane of `Ψ(θ, I)` is the point with action–angle coordinates `(θᵢ, Iᵢ)` for the mass `m i`
and the frequency `ν i`. -/
def oscillatorProductActionAngle (m ν : ι → ℝ) (y : (ι → ℝ) × (ι → ℝ)) : 𝕍 × 𝕍 :=
  (WithLp.toLp 2 fun i ↦ (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).1,
    WithLp.toLp 2 fun i ↦ (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).2)

omit [Fintype ι] in
/-- The `i`-th phase plane of `Ψ(θ, I)` has action–angle coordinates `(θᵢ, Iᵢ)`. -/
@[simp]
theorem oscillatorProductActionAngle_apply (m ν : ι → ℝ) (y : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    ((oscillatorProductActionAngle m ν y).1 i, (oscillatorProductActionAngle m ν y).2 i) =
      oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i) :=
  (rfl)

omit [Fintype ι] in
/-- In the product of the action–angle parametrizations, the energy of the `i`-th oscillator is
`νᵢ Iᵢ`. -/
theorem oscillatorEnergies_oscillatorProductActionAngle (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    {y : (ι → ℝ) × (ι → ℝ)} {i : ι} (hy : 0 ≤ y.2 i) :
    oscillatorEnergies m ν (oscillatorProductActionAngle m ν y) i = ν i * y.2 i := by
  rw [oscillatorEnergies_apply, oscillatorProductActionAngle_apply]
  exact oscillatorHamiltonian_oscillatorActionAngle (hm i) (hν i) hy

omit [Fintype ι] in
variable [Finite ι] in
/-- The angles and actions all of whose actions are positive form an open set. -/
private theorem isOpen_setOf_forall_pos : IsOpen {y : (ι → ℝ) × (ι → ℝ) | ∀ i, 0 < y.2 i} := by
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const
    ((continuous_apply i).comp continuous_snd)

omit [Fintype ι] in
variable [Finite ι] in
/-- The derivative of the linear map `(θ, I) ↦ (θᵢ, Iᵢ)`. -/
private theorem hasFDerivAt_apply_prodMk (i : ι) {y : (ι → ℝ) × (ι → ℝ)} :
    HasFDerivAt (fun y : (ι → ℝ) × (ι → ℝ) ↦ (y.1 i, y.2 i))
      (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).prod
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) y := by
  have := Fintype.ofFinite ι
  exact ((hasFDerivAt_apply (𝕜 := ℝ) i y.1).comp y (hasFDerivAt_fst (p := y))).prodMk
      ((hasFDerivAt_apply (𝕜 := ℝ) i y.2).comp y (hasFDerivAt_snd (p := y)))

omit [Fintype ι] in
variable [Finite ι] in
/-- The `i`-th phase plane of `Ψ(θ, I)` is differentiable in `(θ, I)` where `Iᵢ > 0`. -/
private theorem hasFDerivAt_oscillatorActionAngle_apply {y : (ι → ℝ) × (ι → ℝ)} {i : ι}
    (hy : 0 < y.2 i) :
    HasFDerivAt (fun y : (ι → ℝ) × (ι → ℝ) ↦ oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i))
      ((fderiv ℝ (oscillatorActionAngle (m i) (ν i)) (y.1 i, y.2 i)).comp
        (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).prod
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))))) y := by
  have := Fintype.ofFinite ι
  exact (hasFDerivAt_oscillatorActionAngle (m i) (ν i) hy).differentiableAt.hasFDerivAt.comp y
    (hasFDerivAt_apply_prodMk i)

omit [Fintype ι] in
variable [Finite ι] in
/-- The derivative of the product of the action–angle parametrizations at a point of positive
actions acts as the derivative of the single parametrization in each phase plane. -/
private theorem fderiv_oscillatorProductActionAngle_apply {y : (ι → ℝ) × (ι → ℝ)}
    (hy : ∀ i, 0 < y.2 i) (u : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    ((fderiv ℝ (oscillatorProductActionAngle m ν) y u).1 i,
        (fderiv ℝ (oscillatorProductActionAngle m ν) y u).2 i) =
      fderiv ℝ (oscillatorActionAngle (m i) (ν i)) (y.1 i, y.2 i) (u.1 i, u.2 i) := by
  have := Fintype.ofFinite ι
  let e := (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap
  -- The derivative of the single parametrization in the `i`-th phase plane, read on `(θ, I)`.
  let D : ι → ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ℝ × ℝ := fun i ↦
    (fderiv ℝ (oscillatorActionAngle (m i) (ν i)) (y.1 i, y.2 i)).comp
      (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).prod
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))))
  have h₁ : HasFDerivAt (fun y : (ι → ℝ) × (ι → ℝ) ↦
      fun i ↦ (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).1)
      (ContinuousLinearMap.pi fun i ↦ (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (D i)) y :=
    hasFDerivAt_pi.2 fun i ↦ hasFDerivAt_fst.comp y (hasFDerivAt_oscillatorActionAngle_apply (hy i))
  have h₂ : HasFDerivAt (fun y : (ι → ℝ) × (ι → ℝ) ↦
      fun i ↦ (oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)).2)
      (ContinuousLinearMap.pi fun i ↦ (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (D i)) y :=
    hasFDerivAt_pi.2 fun i ↦ hasFDerivAt_snd.comp y (hasFDerivAt_oscillatorActionAngle_apply (hy i))
  have h : HasFDerivAt (oscillatorProductActionAngle m ν)
      ((e.comp (ContinuousLinearMap.pi fun i ↦ (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (D i))).prod
        (e.comp (ContinuousLinearMap.pi fun i ↦ (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (D i)))) y :=
    (e.hasFDerivAt.comp y h₁).prodMk (e.hasFDerivAt.comp y h₂)
  rw [h.fderiv]
  simp [e, D]

/-- The product of the action–angle parametrizations is smooth where every action is positive. -/
theorem contDiffOn_oscillatorProductActionAngle :
    ContDiffOn ℝ ∞ (oscillatorProductActionAngle m ν) {y | ∀ i, 0 < y.2 i} := by
  intro y hy
  have hf (i : ι) : ContDiffAt ℝ ∞ (fun y : (ι → ℝ) × (ι → ℝ) ↦
      oscillatorActionAngle (m i) (ν i) (y.1 i, y.2 i)) y :=
    (contDiffOn_oscillatorActionAngle.contDiffAt
      (isOpen_lt continuous_const continuous_snd |>.mem_nhds (hy i))).comp y
      (by fun_prop : ContDiff ℝ ∞ fun y : (ι → ℝ) × (ι → ℝ) ↦ (y.1 i, y.2 i)).contDiffAt
  exact ((EuclideanSpace.equiv ι ℝ).symm.contDiff.contDiffAt.comp y
      (contDiffAt_pi.2 fun i ↦ contDiffAt_fst.comp y (hf i))).prodMk
    ((EuclideanSpace.equiv ι ℝ).symm.contDiff.contDiffAt.comp y
      (contDiffAt_pi.2 fun i ↦ contDiffAt_snd.comp y (hf i))) |>.contDiffWithinAt

/-- **The product parametrization is symplectic.** At a point of positive actions, the
derivative of the product of the action–angle parametrizations pulls the standard form
`ω₀ = Σ dqᵢ ∧ dpᵢ` back to `∑ i, dθᵢ ∧ dIᵢ`. -/
theorem stdSymplecticForm_fderiv_oscillatorProductActionAngle (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i)
    (u v : (ι → ℝ) × (ι → ℝ)) :
    stdSymplecticForm (fderiv ℝ (oscillatorProductActionAngle m ν) y u)
        (fderiv ℝ (oscillatorProductActionAngle m ν) y v) =
      ∑ i, (u.1 i * v.2 i - v.1 i * u.2 i) := by
  rw [stdSymplecticForm_apply, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- In the `i`-th phase plane this is the symplecticity of the single parametrization.
  have h := stdSymplecticForm_fderiv_oscillatorActionAngle (hm i) (hν i) (y := (y.1 i, y.2 i))
    (hy i) (u.1 i, u.2 i) (v.1 i, v.2 i)
  rw [← fderiv_oscillatorProductActionAngle_apply hy,
    ← fderiv_oscillatorProductActionAngle_apply hy, stdSymplecticForm_apply,
    stdSymplecticForm_apply] at h
  simpa [mul_comm] using h

omit [Fintype ι] in
variable [Finite ι] in
/-- At a point of positive actions the derivative of the product parametrization is injective,
since it pulls `ω₀` back to the nondegenerate form `∑ i, dθᵢ ∧ dIᵢ`. -/
private theorem injective_fderiv_oscillatorProductActionAngle (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i) :
    Injective (fderiv ℝ (oscillatorProductActionAngle m ν) y) := by
  have := Fintype.ofFinite ι
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  refine eq_of_forall_sum_mul_sub_mul_eq (c := 0) fun w ↦ ?_
  rw [← stdSymplecticForm_fderiv_oscillatorProductActionAngle hm hν hy, hu]
  simp

/-- At a point of positive actions the product of the action–angle parametrizations is a local
diffeomorphism. -/
theorem isLocalDiffeomorphAt_oscillatorProductActionAngle (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i) :
    IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, 𝕍 × 𝕍) ∞
      (oscillatorProductActionAngle m ν) y := by
  refine isLocalDiffeomorphAt_of_injective_mfderiv
    contDiffOn_oscillatorProductActionAngle.contMDiffOn isOpen_setOf_forall_pos hy
    BoundarylessManifold.isInteriorPoint (by simp) ?_ ?_
  · rw [mfderiv_eq_fderiv]
    exact injective_fderiv_oscillatorProductActionAngle hm hν hy
  · simp [Module.finrank_prod, finrank_euclideanSpace]

/-! ### The action–angle chart -/

/-- The **global action–angle chart** of uncoupled oscillators: the covector of the torus
`ι → AddCircle (2π)` whose angles are the angles of the phase planes of `x` and whose actions are
their actions `Eᵢ / νᵢ`. -/
def oscillatorActionAngleChart (m ν : ι → ℝ) (x : 𝕍 × 𝕍) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle (2 * π)) :=
  CotangentBundle.actionAngleCover (2 * π)
    (fun i ↦ (oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)).toReal,
      fun i ↦ oscillatorAction (m i) (ν i) (x.1 i, x.2 i))

/-- The base point of the chart is the point of the torus formed by the angles of the phase
planes. -/
@[simp]
theorem proj_oscillatorActionAngleChart (m ν : ι → ℝ) (x : 𝕍 × 𝕍) :
    (oscillatorActionAngleChart m ν x).proj =
      fun i ↦ (oscillatorAngle (m i) (ν i) (x.1 i, x.2 i) : AddCircle (2 * π)) := by
  ext i
  rw [oscillatorActionAngleChart, CotangentBundle.proj_actionAngleCover]
  exact Real.Angle.coe_toReal _

/-- The actions of the chart are the actions `Eᵢ / νᵢ` of the oscillators. -/
@[simp]
theorem torusActions_oscillatorActionAngleChart [DecidableEq ι] (m ν : ι → ℝ) (x : 𝕍 × 𝕍) :
    CotangentBundle.torusActions (2 * π) (oscillatorActionAngleChart m ν x) =
      fun i ↦ oscillatorAction (m i) (ν i) (x.1 i, x.2 i) :=
  CotangentBundle.torusActions_actionAngleCover _ _

/-- **The energies are linear in the actions.** In the action–angle chart the energy of the
`i`-th oscillator is `νᵢ Iᵢ`. -/
theorem oscillatorEnergies_eq_mul_torusActions_oscillatorActionAngleChart [DecidableEq ι]
    (hν : ∀ i, ν i ≠ 0) (x : 𝕍 × 𝕍) (i : ι) :
    oscillatorEnergies m ν x i =
      ν i * CotangentBundle.torusActions (2 * π) (oscillatorActionAngleChart m ν x) i := by
  rw [torusActions_oscillatorActionAngleChart]
  dsimp only
  rw [oscillatorAction_apply, oscillatorEnergies_apply, mul_div_cancel₀ _ (hν i)]

omit [Fintype ι] in
/-- Every point is the image under the product parametrization of the real lifts of its angles
and its actions. -/
private theorem oscillatorProductActionAngle_toReal (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    (x : 𝕍 × 𝕍) :
    oscillatorProductActionAngle m ν
        (fun i ↦ (oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)).toReal,
          fun i ↦ oscillatorAction (m i) (ν i) (x.1 i, x.2 i)) = x := by
  have h (i : ι) := oscillatorActionAngle_oscillatorAction (hm i) (hν i) (x := (x.1 i, x.2 i))
    (Real.Angle.coe_toReal _)
  ext i
  · exact congrArg Prod.fst (h i)
  · exact congrArg Prod.snd (h i)

/-- **The chart turns the product parametrization into the action–angle covering map.** At angles
`θ` and positive actions `I`, the chart sends `Ψ(θ, I)` to the covector `∑ j, I_j dθ_j` at `[θ]`. -/
theorem oscillatorActionAngleChart_oscillatorProductActionAngle (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i) :
    oscillatorActionAngleChart m ν (oscillatorProductActionAngle m ν y) =
      CotangentBundle.actionAngleCover (2 * π) y := by
  rw [oscillatorActionAngleChart, CotangentBundle.actionAngleCover_eq_actionAngleCover_iff]
  refine ⟨funext fun i ↦ ?_, ?_⟩
  · dsimp only
    rw [oscillatorProductActionAngle_apply]
    exact (oscillatorAction_oscillatorActionAngle (hm i) (hν i) (y := (y.1 i, y.2 i))
      (hy i).le).symm
  · -- The real lifts of the angles of `Ψ(θ, I)` agree with `θ` modulo `2π`.
    have h (i : ι) : ((oscillatorAngle (m i) (ν i)
        ((oscillatorProductActionAngle m ν y).1 i, (oscillatorProductActionAngle m ν y).2 i)).toReal
          : Real.Angle) = y.1 i := by
      rw [Real.Angle.coe_toReal, oscillatorProductActionAngle_apply,
        oscillatorAngle_oscillatorActionAngle (hm i) (hν i) (hy i)]
    choose k hk using fun i ↦ Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (h i).symm
    refine ⟨k, funext fun i ↦ ?_⟩
    simp only [Pi.add_apply]
    linarith [hk i]

/-- **The action–angle chart is injective.** A point of the phase space is determined by the
actions and the angles of its phase planes. -/
theorem injective_oscillatorActionAngleChart (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i) :
    Injective (oscillatorActionAngleChart m ν) := by
  intro x x' h
  rw [oscillatorActionAngleChart, oscillatorActionAngleChart,
    CotangentBundle.actionAngleCover_eq_actionAngleCover_iff] at h
  obtain ⟨hI, k, hθ⟩ := h
  -- In each phase plane the actions agree and the real lifts of the angles agree modulo `2π`, so
  -- both points are the image of the same action–angle coordinates.
  have h (i : ι) : (x.1 i, x.2 i) = (x'.1 i, x'.2 i) := by
    have hθi : (oscillatorAngle (m i) (ν i) (x'.1 i, x'.2 i)).toReal =
        (oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)).toReal + k i * (2 * π) := congrFun hθ i
    have hcoe : ((oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)).toReal : Real.Angle) =
        (oscillatorAngle (m i) (ν i) (x'.1 i, x'.2 i)).toReal :=
      Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨-k i, by rw [hθi]; push_cast; ring⟩
    have hIi : oscillatorAction (m i) (ν i) (x'.1 i, x'.2 i) =
        oscillatorAction (m i) (ν i) (x.1 i, x.2 i) := congrFun hI i
    calc (x.1 i, x.2 i)
        = oscillatorActionAngle (m i) (ν i) ((oscillatorAngle (m i) (ν i) (x.1 i, x.2 i)).toReal,
            oscillatorAction (m i) (ν i) (x.1 i, x.2 i)) :=
          (oscillatorActionAngle_oscillatorAction (hm i) (hν i) (Real.Angle.coe_toReal _)).symm
      _ = oscillatorActionAngle (m i) (ν i) ((oscillatorAngle (m i) (ν i) (x'.1 i, x'.2 i)).toReal,
            oscillatorAction (m i) (ν i) (x'.1 i, x'.2 i)) := by
          rw [hIi]
          exact oscillatorActionAngle_eq_of_coe_eq hcoe _
      _ = (x'.1 i, x'.2 i) :=
          oscillatorActionAngle_oscillatorAction (hm i) (hν i) (Real.Angle.coe_toReal _)
  exact Prod.ext (PiLp.ext fun i ↦ congrArg Prod.fst (h i))
    (PiLp.ext fun i ↦ congrArg Prod.snd (h i))

/-- **The image of the excited region.** The action–angle chart maps the points at which every
oscillator has positive energy onto the covectors of the torus all of whose actions are
positive. -/
theorem image_oscillatorActionAngleChart [DecidableEq ι] (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i) :
    oscillatorActionAngleChart m ν '' {x | ∀ i, 0 < oscillatorEnergies m ν x i} =
      {z | ∀ i, 0 < CotangentBundle.torusActions (2 * π) z i} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [torusActions_oscillatorActionAngleChart]
    dsimp only
    rw [oscillatorAction_apply, ← oscillatorEnergies_apply]
    exact div_pos (hx i) (hν i)
  · intro hz
    obtain ⟨y, rfl⟩ := CotangentBundle.surjective_actionAngleCover (2 * π) z
    rw [mem_ofPred_eq, CotangentBundle.torusActions_actionAngleCover] at hz
    refine ⟨oscillatorProductActionAngle m ν y, fun i ↦ ?_,
      oscillatorActionAngleChart_oscillatorProductActionAngle hm hν hz⟩
    rw [oscillatorEnergies_oscillatorProductActionAngle hm hν (hz i).le]
    exact mul_pos (hν i) (hz i)

omit [Fintype ι] in
/-- An excited point is the image under the product parametrization of a point of positive
actions, namely the real lifts of its angles together with its actions. -/
private theorem exists_eq_oscillatorProductActionAngle (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    {x : 𝕍 × 𝕍} (hx : ∀ i, 0 < oscillatorEnergies m ν x i) :
    ∃ y : (ι → ℝ) × (ι → ℝ), (∀ i, 0 < y.2 i) ∧ oscillatorProductActionAngle m ν y = x :=
  ⟨_, fun i ↦ by
    dsimp only
    rw [oscillatorAction_apply, ← oscillatorEnergies_apply]
    exact div_pos (hx i) (hν i),
    oscillatorProductActionAngle_toReal hm hν x⟩

/-- Near a point of positive actions the chart composed with the product parametrization is the
action–angle covering map. -/
private theorem oscillatorActionAngleChart_comp_eventuallyEq (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {y : (ι → ℝ) × (ι → ℝ)} (hy : ∀ i, 0 < y.2 i) :
    oscillatorActionAngleChart m ν ∘ oscillatorProductActionAngle m ν =ᶠ[nhds y]
      CotangentBundle.actionAngleCover (2 * π) :=
  Filter.eventuallyEq_of_mem (isOpen_setOf_forall_pos.mem_nhds hy) fun _ hy' ↦
    oscillatorActionAngleChart_oscillatorProductActionAngle hm hν hy'

/-- **The action–angle chart is a local diffeomorphism** at every point at which every
oscillator has positive energy. -/
theorem isLocalDiffeomorphAt_oscillatorActionAngleChart (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i)
    {x : 𝕍 × 𝕍} (hx : ∀ i, 0 < oscillatorEnergies m ν x i) :
    IsLocalDiffeomorphAt 𝓘(ℝ, 𝕍 × 𝕍)
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (oscillatorActionAngleChart m ν) x := by
  obtain ⟨y, hy, rfl⟩ := exists_eq_oscillatorProductActionAngle hm hν hx
  exact isLocalDiffeomorphAt_of_eqOn_comp isOpen_setOf_forall_pos hy
    BoundarylessManifold.isInteriorPoint (by simp)
    (fun _ hy' ↦ oscillatorActionAngleChart_oscillatorProductActionAngle hm hν hy')
    (CotangentBundle.contMDiff_actionAngleCover _).contMDiffOn
    ((CotangentBundle.isLocalDiffeomorph_actionAngleCover _ y).isInvertible_mfderiv
      (by simp)).injective
    (by simp [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq])
    (isLocalDiffeomorphAt_oscillatorProductActionAngle hm hν hy)

/-- **The action–angle chart is symplectic.** At every point at which every oscillator has
positive energy, the chart pulls the canonical symplectic form `ω = ∑ j, dθ_j ∧ dI_j` of the
cotangent bundle of the torus back to the standard form `ω₀ = Σ dqᵢ ∧ dpᵢ`. -/
theorem eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart (hm : ∀ i, 0 < m i)
    (hν : ∀ i, 0 < ν i) {x : 𝕍 × 𝕍} (hx : ∀ i, 0 < oscillatorEnergies m ν x i)
    (v w : TangentSpace 𝓘(ℝ, 𝕍 × 𝕍) x) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (ι → AddCircle (2 * π))) (oscillatorActionAngleChart m ν x)
        (mfderiv 𝓘(ℝ, 𝕍 × 𝕍) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (oscillatorActionAngleChart m ν) x v)
        (mfderiv 𝓘(ℝ, 𝕍 × 𝕍) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (oscillatorActionAngleChart m ν) x w) =
      SmoothBundleForm.eval₂ (stdSymplecticForm (V := 𝕍)).constSmooth x v w := by
  obtain ⟨y, hy, rfl⟩ := exists_eq_oscillatorProductActionAngle hm hν hx
  -- Write `v` and `w` as images under the invertible differential of `Ψ`, and compare the
  -- pullbacks along `Ψ` of `ω₀` and along `Φ ∘ Ψ = κ` of `ω`.
  have hΨ := isLocalDiffeomorphAt_oscillatorProductActionAngle hm hν hy
  have hsurj := (hΨ.isInvertible_mfderiv (by simp)).surjective
  obtain ⟨v', rfl⟩ := hsurj v
  obtain ⟨w', rfl⟩ := hsurj w
  have hchain := mfderiv_apply_mfderiv_of_eventuallyEq_comp
    (oscillatorActionAngleChart_comp_eventuallyEq hm hν hy)
    ((isLocalDiffeomorphAt_oscillatorActionAngleChart hm hν hx).mdifferentiableAt (by simp))
    (hΨ.mdifferentiableAt (by simp))
  rw [CotangentBundle.eval₂_symplecticForm, hchain, hchain,
    ← CotangentBundle.eval₂_symplecticForm (CotangentBundle.actionAngleCover (2 * π) y),
    CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleCover]
  refine Eq.trans ?_ (SymplecticForm.constSmooth_apply _ _ _ _).symm
  rw [mfderiv_eq_fderiv]
  exact (stdSymplecticForm_fderiv_oscillatorProductActionAngle hm hν hy v' w').symm

/-- **Hamilton's equations in the action–angle chart.** At a point at which every oscillator has
positive energy, the chart carries the Hamiltonian vector field of the energy `Eᵢ` to the
constant field `νᵢ ∂_θᵢ`: at `Φ x = κ(θ, I)` it is the image of `(νᵢ eᵢ, 0)` under the
differential of the action–angle covering map `κ`. -/
theorem mfderiv_oscillatorActionAngleChart_hamiltonianVectorField_oscillatorEnergies
    [DecidableEq ι] (hm : ∀ i, 0 < m i) (hν : ∀ i, 0 < ν i) {x : 𝕍 × 𝕍}
    (hx : ∀ i, 0 < oscillatorEnergies m ν x i) (i : ι) {y : (ι → ℝ) × (ι → ℝ)}
    (hy : CotangentBundle.actionAngleCover (2 * π) y = oscillatorActionAngleChart m ν x) :
    mfderiv 𝓘(ℝ, 𝕍 × 𝕍) ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (oscillatorActionAngleChart m ν) x
        ((stdSymplecticForm (V := 𝕍)).constSmooth.hamiltonianVectorField
          (oscillatorEnergies m ν · i) x) =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (CotangentBundle.actionAngleCover (2 * π)) y (Pi.single i (ν i), 0) := by
  -- The energy `Eᵢ` is the linear function `I ↦ νᵢ Iᵢ` of the actions of the chart.
  have hE : (oscillatorEnergies m ν · i) =ᶠ[nhds x]
      (fun I : ι → ℝ ↦ ν i * I i) ∘ CotangentBundle.torusActions (2 * π) ∘
        oscillatorActionAngleChart m ν :=
    Filter.Eventually.of_forall fun x' ↦
      oscillatorEnergies_eq_mul_torusActions_oscillatorActionAngleChart (fun j ↦ (hν j).ne') x' i
  have hlin : HasFDerivAt (fun I : ι → ℝ ↦ ν i * I i)
      (ν i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) y.2 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasFDerivAt.const_mul (ν i)
  rw [CotangentBundle.mfderiv_hamiltonianVectorField_eq_mfderiv_actionAngleCover (2 * π)
    (SymplecticForm.isNondegenerate_constSmooth _)
    (isLocalDiffeomorphAt_oscillatorActionAngleChart hm hν hx)
    (eval₂_symplecticForm_mfderiv_oscillatorActionAngleChart hm hν hx) hE hy
    hlin.differentiableAt, hlin.fderiv]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

end TauCeti
