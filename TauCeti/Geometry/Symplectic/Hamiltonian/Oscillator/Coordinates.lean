/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.ActionAngle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Symplectic.Manifold.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle

/-!
# Smooth oscillator action–angle coordinates

For positive mass and frequency, the positive-action cylinder is diffeomorphic to the
punctured phase plane. The angular coordinate is the actual circle `AddCircle (2 * π)`, with its
quotient smooth structure; it is not a choice of a discontinuous real argument.
The diffeomorphism pulls `dq ∧ dp` back to `dθ ∧ dI`, with `dθ` the time form of the
period-`2π` circle, and carries the Hamiltonian to `ν I`. Its inverse is the circle-valued angle
and the positive action `H / ν`.

The construction uses the action–angle formulas and inverse identities of
`TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.ActionAngle`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, §50.
-/

public noncomputable section

open Set Function Real
open scoped Manifold ContDiff

namespace TauCeti

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The cylinder of angles modulo `2π` and strictly positive actions. -/
def oscillatorActionCylinder : TopologicalSpace.Opens (AddCircle (2 * π) × ℝ) :=
  ⟨{y | 0 < y.2}, isOpen_lt continuous_const continuous_snd⟩

@[simp]
theorem mem_oscillatorActionCylinder {y : AddCircle (2 * π) × ℝ} :
    y ∈ oscillatorActionCylinder ↔ 0 < y.2 := Iff.rfl

/-- The oscillator phase plane with its zero-energy equilibrium removed. -/
def oscillatorPuncturedPlane : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨{x | x ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩

@[simp]
theorem mem_oscillatorPuncturedPlane {x : ℝ × ℝ} :
    x ∈ oscillatorPuncturedPlane ↔ x ≠ 0 := Iff.rfl

/-- The oscillator parametrization on the angle quotient. Its restriction to positive action
is a smooth global coordinate map. -/
def oscillatorCylinderMap (m ν : ℝ) (y : AddCircle (2 * π) × ℝ) : ℝ × ℝ :=
  (periodic_oscillatorActionAngle m ν y.2).lift y.1

/-- On a real angular lift the cylinder map is the existing action–angle parametrization. -/
@[simp]
theorem oscillatorCylinderMap_coe (m ν θ J : ℝ) :
    oscillatorCylinderMap m ν ((θ : AddCircle (2 * π)), J) = oscillatorActionAngle m ν (θ, J) :=
  (periodic_oscillatorActionAngle m ν J).lift_coe θ

variable {m ν : ℝ}

private theorem oscillatorCylinderMap_comp_coe :
    oscillatorCylinderMap m ν ∘ Prod.map ((↑) : ℝ → AddCircle (2 * π)) id =
      oscillatorActionAngle m ν :=
  funext fun y ↦ oscillatorCylinderMap_coe m ν y.1 y.2

/-- The quotient action–angle map is smooth on the whole positive-action cylinder. -/
theorem contMDiffOn_oscillatorCylinderMap :
    ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (oscillatorCylinderMap m ν)
      oscillatorActionCylinder := by
  rintro ⟨a, J⟩ hJ
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  -- Specify the real lift as the base point of the open positive-action half-plane.
  have hs := (contDiffOn_oscillatorActionAngle (m := m) (ν := ν)).contDiffAt
    ((isOpen_lt continuous_const continuous_snd :
      IsOpen {y : ℝ × ℝ | 0 < y.2}).mem_nhds
        (show (θ, J) ∈ {y : ℝ × ℝ | 0 < y.2} from hJ))
  exact ((AddCircle.isLocalDiffeomorph_prodMap_coe_id (2 * π) ∞
    (θ, J)).contMDiffAt_comp_iff le_rfl).1
    (by rw [oscillatorCylinderMap_comp_coe]; exact hs.contMDiffAt) |>.contMDiffWithinAt

/-- The action recovered from the cylinder map is its second coordinate. -/
@[simp]
theorem oscillatorAction_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : 0 ≤ y.2) :
    oscillatorAction m ν (oscillatorCylinderMap m ν y) = y.2 := by
  obtain ⟨⟨θ, J⟩, rfl⟩ : ∃ z : ℝ × ℝ, (↑z.1, z.2) = y := by
    obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective y.1
    exact ⟨(θ, y.2), Prod.ext hθ rfl⟩
  rw [oscillatorCylinderMap_coe]
  exact oscillatorAction_oscillatorActionAngle hm hν hy

/-- The Hamiltonian of the cylinder parametrization is frequency times action. -/
@[simp]
theorem oscillatorHamiltonian_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : 0 ≤ y.2) :
    oscillatorHamiltonian m ν (oscillatorCylinderMap m ν y) = ν * y.2 := by
  obtain ⟨a, J⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [oscillatorCylinderMap_coe]
  exact oscillatorHamiltonian_oscillatorActionAngle hm hν hy

/-- The angle recovered from a point of positive action is its circle coordinate. -/
@[simp]
theorem oscillatorAngle_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : 0 < y.2) :
    (oscillatorAngle m ν (oscillatorCylinderMap m ν y) : AddCircle (2 * π)) = y.1 := by
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective y.1
  obtain ⟨a, J⟩ := y
  dsimp only at hθ hy ⊢
  rw [← hθ, oscillatorCylinderMap_coe]
  exact oscillatorAngle_oscillatorActionAngle hm hν hy

/-- The quotient map reconstructs every phase point from its action and circle-valued angle. -/
@[simp]
theorem oscillatorCylinderMap_angle_action (hm : 0 < m) (hν : 0 < ν) (x : ℝ × ℝ) :
    oscillatorCylinderMap m ν (oscillatorAngle m ν x, oscillatorAction m ν x) = x := by
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective (oscillatorAngle m ν x)
  rw [← hθ, oscillatorCylinderMap_coe]
  exact oscillatorActionAngle_oscillatorAction hm hν hθ

/-- At every positive action the quotient parametrization is a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : y ∈ oscillatorActionCylinder) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (oscillatorCylinderMap m ν) y := by
  obtain ⟨a, J⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hf := isLocalDiffeomorphAt_oscillatorActionAngle hm hν (y := (θ, J)) hy
  rw [← oscillatorCylinderMap_comp_coe] at hf
  exact hf.of_comp_right (AddCircle.isLocalDiffeomorph_prodMap_coe_id (2 * π) ∞ (θ, J))

/-- The coordinate map from the positive-action cylinder into the punctured phase plane. -/
private def oscillatorCoordinates (hm : 0 < m) (hν : 0 < ν)
    (y : oscillatorActionCylinder) : oscillatorPuncturedPlane :=
  ⟨oscillatorCylinderMap m ν y, (oscillatorAction_pos_iff hm hν).1
    ((oscillatorAction_oscillatorCylinderMap hm hν y.property.le).symm ▸ y.property)⟩

/-- The underlying phase point of the coordinate map is the quotient parametrization. -/
@[simp]
private theorem coe_oscillatorCoordinates (hm : 0 < m) (hν : 0 < ν) (y : oscillatorActionCylinder) :
    (oscillatorCoordinates hm hν y : ℝ × ℝ) = oscillatorCylinderMap m ν y := (rfl)

/-- The coordinate map is bijective, with inverse given by the angle and the action `H / ν`. -/
private theorem bijective_oscillatorCoordinates (hm : 0 < m) (hν : 0 < ν) :
    Bijective (oscillatorCoordinates hm hν) := by
  constructor
  · intro y z hyz
    have h := congrArg Subtype.val hyz
    apply Subtype.ext
    apply Prod.ext
    · have ha := congrArg (oscillatorAngle m ν) h
      simp only [coe_oscillatorCoordinates,
        oscillatorAngle_oscillatorCylinderMap hm hν y.property,
        oscillatorAngle_oscillatorCylinderMap hm hν z.property] at ha
      exact ha
    · have ha := congrArg (oscillatorAction m ν) h
      simpa only [coe_oscillatorCoordinates,
        oscillatorAction_oscillatorCylinderMap hm hν y.property.le,
        oscillatorAction_oscillatorCylinderMap hm hν z.property.le] using ha
  · intro x
    refine ⟨⟨(oscillatorAngle m ν x, oscillatorAction m ν x),
      (oscillatorAction_pos_iff hm hν).2 x.property⟩, Subtype.ext ?_⟩
    exact oscillatorCylinderMap_angle_action hm hν x

/-- The coordinate map is a local diffeomorphism, including across the angle seam. -/
private theorem isLocalDiffeomorph_oscillatorCoordinates (hm : 0 < m) (hν : 0 < ν) :
    IsLocalDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (oscillatorCoordinates hm hν) := by
  intro y
  have hf : IsLocalDiffeomorphAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (Subtype.val ∘ oscillatorCoordinates hm hν) y :=
    (isLocalDiffeomorph_subtype_val (I := 𝓘(ℝ).prod 𝓘(ℝ))
    (U := oscillatorActionCylinder) (n := ∞) y).comp
    (hg := isLocalDiffeomorphAt_oscillatorCylinderMap hm hν y.property)
  exact hf.of_comp_left (isLocalDiffeomorph_subtype_val (U := oscillatorPuncturedPlane) _)
    ((Topology.IsInducing.subtypeVal.continuousAt_iff).mpr hf.contMDiffAt.continuousAt)

/-- Global smooth action–angle coordinates for the harmonic oscillator: the positive-action
cylinder is diffeomorphic to the punctured phase plane. -/
def oscillatorActionAngleDiffeomorph (hm : 0 < m) (hν : 0 < ν) :
    oscillatorActionCylinder ≃ₘ⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ oscillatorPuncturedPlane :=
  (isLocalDiffeomorph_oscillatorCoordinates hm hν).diffeomorphOfBijective
    (bijective_oscillatorCoordinates hm hν)

/-- The global diffeomorphism has the quotient action–angle parametrization as forward map. -/
@[simp]
theorem coe_oscillatorActionAngleDiffeomorph (hm : 0 < m) (hν : 0 < ν)
    (y : oscillatorActionCylinder) :
    (oscillatorActionAngleDiffeomorph hm hν y : ℝ × ℝ) = oscillatorCylinderMap m ν y := by
  simp [oscillatorActionAngleDiffeomorph]

/-- Its inverse consists of the circle-valued angle and the positive action. -/
@[simp]
theorem oscillatorActionAngleDiffeomorph_symm_apply (hm : 0 < m) (hν : 0 < ν)
    (x : oscillatorPuncturedPlane) :
    ((oscillatorActionAngleDiffeomorph hm hν).symm x : AddCircle (2 * π) × ℝ) =
      (oscillatorAngle m ν x, oscillatorAction m ν x) := by
  have h := (oscillatorActionAngleDiffeomorph hm hν).symm_apply_apply
    (⟨(oscillatorAngle m ν x, oscillatorAction m ν x),
      (oscillatorAction_pos_iff hm hν).2 x.property⟩ : oscillatorActionCylinder)
  have heq : oscillatorActionAngleDiffeomorph hm hν
      ⟨(oscillatorAngle m ν x, oscillatorAction m ν x),
        (oscillatorAction_pos_iff hm hν).2 x.property⟩ = x := by
    apply Subtype.ext
    simp only [coe_oscillatorActionAngleDiffeomorph]
    exact oscillatorCylinderMap_angle_action hm hν x
  exact congrArg Subtype.val (heq ▸ h)

/-- The Hamiltonian in these global coordinates is `ν` times the action coordinate. -/
theorem oscillatorHamiltonian_oscillatorActionAngleDiffeomorph (hm : 0 < m) (hν : 0 < ν)
    (y : oscillatorActionCylinder) :
    oscillatorHamiltonian m ν (oscillatorActionAngleDiffeomorph hm hν y) = ν * y.val.2 := by
  simpa only [coe_oscillatorActionAngleDiffeomorph] using
    oscillatorHamiltonian_oscillatorCylinderMap hm hν y.property.le

private theorem mfderiv_oscillatorActionAngle (y : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (oscillatorActionAngle m ν) y =
      fderiv ℝ (oscillatorActionAngle m ν) y := by
  -- Read both self-model tangent fibres in the real plane via the canonical equivalences.
  ext v
  simp only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_symm_apply]
  -- The equality of underlying model vectors uses the self-model tangent-space instances.
  rfl

/-- The differential of the quotient parametrization is the existing real-coordinate derivative
when read in a real angular lift. -/
theorem mfderiv_oscillatorCylinderMap_coe (θ J : ℝ) (hJ : 0 < J) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) (oscillatorCylinderMap m ν)
        ((θ : AddCircle (2 * π)), J) = fderiv ℝ (oscillatorActionAngle m ν) (θ, J) := by
  have hy := (mem_oscillatorActionCylinder (y := ((θ : AddCircle (2 * π)), J))).mpr hJ
  have hf := ((contMDiffOn_oscillatorCylinderMap (m := m) (ν := ν)).contMDiffAt
    (oscillatorActionCylinder.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
  have h := mfderiv_comp (θ, J) hf
    ((AddCircle.isLocalDiffeomorph_prodMap_coe_id (2 * π) ∞ (θ, J)).mdifferentiableAt (by simp))
  rw [oscillatorCylinderMap_comp_coe] at h
  ext v
  have hq : mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
      (Prod.map ((↑) : ℝ → AddCircle (2 * π)) id) (θ, J) v = v :=
    DFunLike.congr_fun (AddCircle.mfderiv_prodMap_coe_id (2 * π) (θ, J)) v
  have hq' := congrArg
    (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) (oscillatorCylinderMap m ν)
      ((θ : AddCircle (2 * π)), J)) hq.symm
  exact hq'.trans ((DFunLike.congr_fun h v).symm.trans
    (DFunLike.congr_fun (mfderiv_oscillatorActionAngle (m := m) (ν := ν) (θ, J)) v))

private theorem mfderiv_oscillatorCoordinates_apply (θ J : ℝ) (hJ : 0 < J)
    (v : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ))
      (⟨((θ : AddCircle (2 * π)), J), hJ⟩ : oscillatorActionCylinder)) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (fun z : oscillatorActionCylinder ↦ oscillatorCylinderMap m ν z)
      ⟨((θ : AddCircle (2 * π)), J), hJ⟩ v =
      fderiv ℝ (oscillatorActionAngle m ν) (θ, J) v := by
  have hy := (mem_oscillatorActionCylinder (y := ((θ : AddCircle (2 * π)), J))).mpr hJ
  have hf := ((contMDiffOn_oscillatorCylinderMap (m := m) (ν := ν)).contMDiffAt
    (oscillatorActionCylinder.isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
  exact (Manifold.mfderiv_comp_subtype_val_apply hf v).trans
    (DFunLike.congr_fun (mfderiv_oscillatorCylinderMap_coe (m := m) (ν := ν) θ J hJ) v)

/-- On the positive-action cylinder the oscillator map pulls `dq ∧ dp` back to `dθ ∧ dI`,
where `dθ` is the time form of the period-`2π` circle. -/
private theorem eval₂_mpullback_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : y ∈ oscillatorActionCylinder)
    (v w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) (⟨y, hy⟩ : oscillatorActionCylinder)) :
    SmoothBundleForm.eval₂
      (SmoothForm.mpullback (fun z : oscillatorActionCylinder ↦ oscillatorCylinderMap m ν z)
        ((contMDiffOn_oscillatorCylinderMap).comp_contMDiff contMDiff_subtype_val
          (fun z ↦ z.property)) (stdSymplecticForm (V := ℝ)).constSmooth)
      ⟨y, hy⟩ v w = v.1 * w.2 - w.1 * v.2 := by
  obtain ⟨a, J⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  refine (SmoothForm.eval₂_mpullback _ _ _ _ v w).trans ?_
  simp only [SymplecticForm.constSmooth_apply, mfderiv_oscillatorCoordinates_apply θ J hy]
  have hstd (v w : ℝ × ℝ) :
      (stdSymplecticForm (V := ℝ)) v w = v.1 * w.2 - w.1 * v.2 := by
    simp only [stdSymplecticForm_apply, RCLike.inner_apply, RCLike.conj_to_real]
    ring
  exact (stdSymplecticForm_fderiv_oscillatorActionAngle hm hν (y := (θ, J)) hy v w).trans (hstd v w)

/-- The global oscillator diffeomorphism is symplectic: its pullback of the phase-plane form
is the wedge of the positive angular time form and the differential of the action coordinate. -/
@[simp]
theorem mpullback_oscillatorActionAngleDiffeomorph (hm : 0 < m) (hν : 0 < ν) :
    SmoothForm.mpullback (oscillatorActionAngleDiffeomorph hm hν)
        (oscillatorActionAngleDiffeomorph hm hν).contMDiff
        (SmoothForm.mpullback (Subtype.val : oscillatorPuncturedPlane → ℝ × ℝ)
          contMDiff_subtype_val (stdSymplecticForm (V := ℝ)).constSmooth) =
      SmoothForm.mpullback (Subtype.val : oscillatorActionCylinder → AddCircle (2 * π) × ℝ)
        contMDiff_subtype_val
        (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (2 * π)))
          (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm)) := by
  have hcomp : (Subtype.val : oscillatorPuncturedPlane → ℝ × ℝ) ∘
      oscillatorActionAngleDiffeomorph hm hν =
      fun z : oscillatorActionCylinder ↦ oscillatorCylinderMap m ν z := by
    funext z
    simp only [Function.comp_apply, coe_oscillatorActionAngleDiffeomorph]
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simp only [hcomp]
  apply SmoothBundleForm.ext_eval₂
  intro y v w
  rw [eval₂_mpullback_oscillatorCylinderMap hm hν y.property v w]
  symm
  have h := SmoothForm.eval₂_mpullback (Subtype.val : oscillatorActionCylinder →
    AddCircle (2 * π) × ℝ) contMDiff_subtype_val
    (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (2 * π)))
      (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm)) y v w
  rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] at h
  exact h.trans ((AddCircle.eval₂_wedge_timeForm_realLineCoordForm (2 * π) y
    (Manifold.tangentSpaceOpenEquiv y v) (Manifold.tangentSpaceOpenEquiv y w)).trans
      (by simp only [Manifold.tangentSpaceOpenEquiv_apply]))

end TauCeti
