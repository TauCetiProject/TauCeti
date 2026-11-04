/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.ActionAngle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle

/-!
# Smooth oscillator action–angle coordinates

For positive mass and frequency, the positive-action cylinder is diffeomorphic to the
punctured phase plane. The angular coordinate is the actual circle `Real.Angle`, with its
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

private theorem contDiffOn_oscillatorActionAngle :
    ContDiffOn ℝ ∞ (oscillatorActionAngle m ν) {y | 0 < y.2} := by
  intro y hy
  have hr : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ √(2 * z.2)) y :=
    (contDiffAt_const.mul contDiffAt_snd).sqrt (mul_pos two_pos hy).ne'
  have heq : oscillatorActionAngle m ν = fun z : ℝ × ℝ ↦
      (√(2 * z.2) / √(m * ν) * Real.sin z.1, √(m * ν) * √(2 * z.2) * Real.cos z.1) :=
    funext (oscillatorActionAngle_apply m ν)
  rw [heq]
  exact ((hr.div_const _).mul (Real.contDiff_sin.contDiffAt.comp y contDiffAt_fst)).prodMk
    ((contDiffAt_const.mul hr).mul (Real.contDiff_cos.contDiffAt.comp y contDiffAt_fst))
    |>.contDiffWithinAt

/-- The quotient action–angle map is smooth on the whole positive-action cylinder. -/
theorem contMDiffOn_oscillatorCylinderMap :
    ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (oscillatorCylinderMap m ν)
      oscillatorActionCylinder := by
  rintro ⟨a, J⟩ hJ
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hq := (AddCircle.isLocalDiffeomorph_coe (2 * π) ∞).prodMap
    (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).isLocalDiffeomorph
  have heq : oscillatorCylinderMap m ν ∘ Prod.map ((↑) : ℝ → AddCircle (2 * π)) id =
      oscillatorActionAngle m ν := by
    funext y
    exact oscillatorCylinderMap_coe m ν y.1 y.2
  have hs := (contDiffOn_oscillatorActionAngle (m := m) (ν := ν)).contDiffAt
    ((isOpen_lt continuous_const continuous_snd :
      IsOpen {y : ℝ × ℝ | 0 < y.2}).mem_nhds
        (show (θ, J) ∈ {y : ℝ × ℝ | 0 < y.2} from hJ))
  have hs' : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (oscillatorActionAngle m ν) (θ, J) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hs.contMDiffAt
  exact ((hq (θ, J)).contMDiffAt_comp_iff le_rfl).1
    (heq.symm ▸ hs') |>.contMDiffWithinAt

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

/-- The angle recovered from a point of positive action is its circle coordinate. -/
@[simp]
theorem oscillatorAngle_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : 0 < y.2) :
    oscillatorAngle m ν (oscillatorCylinderMap m ν y) = y.1 := by
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

private theorem isLocalDiffeomorphAt_oscillatorActionAngle (hm : 0 < m) (hν : 0 < ν)
    {y : ℝ × ℝ} (hy : 0 < y.2) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (oscillatorActionAngle m ν) y := by
  let L := fderiv ℝ (oscillatorActionAngle m ν) y
  let ι : (stdSymplecticForm (V := ℝ)).toBilinForm →bᵢ
      (stdSymplecticForm (V := ℝ)).toBilinForm :=
    { toLinearMap := L.toLinearMap
      map_app' := stdSymplecticForm_fderiv_oscillatorActionAngle hm hν hy }
  have hinj : Injective L := ι.injective (stdSymplecticForm (V := ℝ)).nondegenerate.1
  let e := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  refine isLocalDiffeomorphAt_of_mfderiv_eq
    contDiffOn_oscillatorActionAngle.contMDiffOn (isOpen_lt continuous_const continuous_snd)
    hy BoundarylessManifold.isInteriorPoint (by simp)
    (e := (NormedSpace.fromTangentSpace y).trans
      (e.trans (NormedSpace.fromTangentSpace (oscillatorActionAngle m ν y)).symm)) ?_
  rw [mfderiv_eq_fderiv]
  rfl

/-- At every positive action the quotient parametrization is a local diffeomorphism. -/
theorem isLocalDiffeomorphAt_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : y ∈ oscillatorActionCylinder) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (oscillatorCylinderMap m ν) y := by
  obtain ⟨a, J⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hq := (AddCircle.isLocalDiffeomorph_coe (2 * π) ∞).prodMap
    (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).isLocalDiffeomorph
  have heq : oscillatorCylinderMap m ν ∘ Prod.map ((↑) : ℝ → AddCircle (2 * π)) id =
      oscillatorActionAngle m ν := by
    funext z
    exact oscillatorCylinderMap_coe m ν z.1 z.2
  have hf := isLocalDiffeomorphAt_oscillatorActionAngle hm hν (y := (θ, J)) hy
  rw [← heq] at hf
  have hq' : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      (Prod.map ((↑) : ℝ → AddCircle (2 * π)) id) (θ, J) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hq (θ, J)
  exact hf.of_comp_right hq'

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
      -- `Real.Angle` is the type synonym for the period-`2π` additive circle.
      convert! ha
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
@[simp↓]
theorem oscillatorHamiltonian_oscillatorActionAngleDiffeomorph (hm : 0 < m) (hν : 0 < ν)
    (y : oscillatorActionCylinder) :
    oscillatorHamiltonian m ν (oscillatorActionAngleDiffeomorph hm hν y) = ν * y.val.2 := by
  have h := oscillatorAction_oscillatorCylinderMap hm hν y.property.le
  rw [oscillatorAction_apply, div_eq_iff hν.ne'] at h
  simpa only [coe_oscillatorActionAngleDiffeomorph, mul_comm] using h

/-- The differential of the quotient parametrization is the existing real-coordinate derivative
when read in a real angular lift. -/
theorem mfderiv_oscillatorCylinderMap_coe (hm : 0 < m) (hν : 0 < ν)
    (θ J : ℝ) (hJ : 0 < J) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) (oscillatorCylinderMap m ν)
        ((θ : AddCircle (2 * π)), J) = fderiv ℝ (oscillatorActionAngle m ν) (θ, J) := by
  let q := Prod.map ((↑) : ℝ → AddCircle (2 * π)) (id : ℝ → ℝ)
  have hq : MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) q (θ, J) :=
    ((AddCircle.contMDiff_coe (2 * π) ∞).prodMap contMDiff_id).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ)
      (oscillatorCylinderMap m ν) (q (θ, J)) :=
    (isLocalDiffeomorphAt_oscillatorCylinderMap hm hν hJ).contMDiffAt.mdifferentiableAt (by simp)
  have heq : oscillatorCylinderMap m ν ∘ q = oscillatorActionAngle m ν :=
    funext fun y ↦ oscillatorCylinderMap_coe m ν y.1 y.2
  have h := mfderiv_comp (θ, J) hf hq
  rw [heq] at h
  have hq' : mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) q (θ, J) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [mfderiv_prodMap (AddCircle.hasMFDerivAt_coe (2 * π) θ).mdifferentiableAt
      mdifferentiableAt_id, AddCircle.mfderiv_coe, mfderiv_id]
    rfl
  -- Tangent spaces of the product models are the real model plane.
  erw [hq', ContinuousLinearMap.comp_id] at h
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv] at h
  -- For self models, `fromTangentSpace` is the identity; the circle tangent models are also real.
  convert! h.symm using 1

/-- On the positive-action cylinder the oscillator map pulls `dq ∧ dp` back to `dθ ∧ dI`,
where `dθ` is the time form of the period-`2π` circle. -/
private theorem eval₂_mpullback_oscillatorCylinderMap (hm : 0 < m) (hν : 0 < ν)
    {y : AddCircle (2 * π) × ℝ} (hy : y ∈ oscillatorActionCylinder) (v w : ℝ × ℝ) :
    SmoothBundleForm.eval₂
      (SmoothForm.mpullback (fun z : oscillatorActionCylinder ↦ oscillatorCylinderMap m ν z)
        ((contMDiffOn_oscillatorCylinderMap).comp_contMDiff contMDiff_subtype_val
          (fun z ↦ z.property)) (stdSymplecticForm (V := ℝ)).constSmooth)
      ⟨y, hy⟩ v w = v.1 * w.2 - w.1 * v.2 := by
  obtain ⟨a, J⟩ := y
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective a
  -- Read open-submanifold tangent vectors in their real model coordinates.
  erw [SmoothForm.eval₂_mpullback, SymplecticForm.constSmooth_apply]
  have hf := (contMDiffOn_oscillatorCylinderMap (m := m) (ν := ν)).contMDiffAt
    (oscillatorActionCylinder.isOpen.mem_nhds hy)
  erw [mfderiv_comp
    (f := (Subtype.val : oscillatorActionCylinder → AddCircle (2 * π) × ℝ))
    (g := oscillatorCylinderMap m ν) (⟨((θ : AddCircle (2 * π)), J), hy⟩ : oscillatorActionCylinder)
    (hf.mdifferentiableAt (by simp)) ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)),
    Manifold.mfderiv_subtype_val, mfderiv_oscillatorCylinderMap_coe hm hν θ J hy]
  -- The native open-submanifold tangent equivalence reads both vectors in the real model plane.
  erw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply]
  have hstd : (stdSymplecticForm (V := ℝ)) v w = v.1 * w.2 - w.1 * v.2 := by
    simp only [stdSymplecticForm_apply, RCLike.inner_apply, RCLike.conj_to_real]
    ring
  exact (stdSymplecticForm_fderiv_oscillatorActionAngle hm hν (y := (θ, J)) hy v w).trans hstd

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
  -- Native tangent spaces of these open subsets are the real product model.
  erw [eval₂_mpullback_oscillatorCylinderMap hm hν y.property v w,
    SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val,
    SmoothForm.eval₂_wedge_one_one]
  simp only [SmoothForm.mpullback_fst_apply, SmoothForm.mpullback_snd_apply,
    AddCircle.timeForm_apply, SmoothForm.realLineCoordForm_apply,
    Manifold.tangentSpaceProdEquiv_apply, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_apply]
  rfl

end TauCeti
