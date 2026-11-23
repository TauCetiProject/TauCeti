/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Linearization of contact Hamiltonian fields

At a point where a contact Hamiltonian and its differential vanish, its vector field vanishes
and its linearization preserves the contact hyperplane. On that hyperplane the linearization
is determined by the negative Hessian, with the convention
`ι_(X_f) dα = (R_α f) α - df`.

The formulas here are in a normed-space chart; the contact form need not be constant. In
particular, derivatives of its coefficients do not contribute at the stationary point. These
are the local equations used to realize infinitesimal symplectic normal maps by contact
Hamiltonians vanishing to first order.

## References

* H. Geiges, *An Introduction to Contact Topology*, Section 2.5.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {α : SmoothForm 𝓘(ℝ, E) E ℝ 1} {f : E → ℝ} {x : E}

namespace IsContactForm

/-- At a vanishing first jet, the linearization of a contact Hamiltonian field takes values
in the contact hyperplane. -/
theorem fderiv_contactHamiltonianVectorField_mem_kerDistribution
    (hα : α.IsContactForm) (hf : ContDiffAt ℝ 2 f x) (hf₀ : f x = 0)
    (hdf : fderiv ℝ f x = 0) (v : E) :
    (NormedSpace.fromTangentSpace x).symm
      (fderiv ℝ (fun y ↦ NormedSpace.fromTangentSpace y
        (α.contactHamiltonianVectorField f y)) x v) ∈ α.kerDistribution x := by
  let a : E → E [⋀^Fin 1]→L[ℝ] ℝ := α.val
  let X : E → E := fun y ↦ NormedSpace.fromTangentSpace y
    (α.contactHamiltonianVectorField f y)
  have ha : DifferentiableAt ℝ a x :=
    (isSmoothForm_modelSpace_iff.1 α.isSmoothForm).differentiable (by simp) x
  have hX : DifferentiableAt ℝ X x := by
    have h := hα.contMDiffAt_contactHamiltonianVectorField (n := 1) (by simp)
      (contMDiffAt_iff_contDiffAt.2 hf)
    exact (contMDiffAt_iff_contDiffAt.1
      ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).contMDiffAt.comp x h)).differentiableAt
      one_ne_zero
  have heq : (fun y ↦ a y (fun _ ↦ X y)) = f := by
    funext y
    convert hα.apply_contactHamiltonianVectorField f y using 1
    congr 1
    ext i
    fin_cases i
    rfl
  have hcalc := fderiv_continuousAlternatingMap_apply_apply (f := a)
    (g := fun _ ↦ X) ha (fun _ ↦ hX) v
  have hz : X x = 0 := by
    simp only [X, α.contactHamiltonianVectorField_eq_zero_of_jet_eq_zero hf₀
      (by ext w; rw [mvfderiv_eq_fderiv_apply, hdf]; rfl), map_zero]
  rw [heq] at hcalc
  simp only [hz, ← Pi.zero_def, ContinuousAlternatingMap.map_zero, zero_add,
    Fin.sum_univ_one, hdf, zero_apply] at hcalc
  apply mem_kerDistribution.2
  -- The canonical tangent/model identifications are identities on vectors, but carry distinct
  -- normed-space instances, so transport the scalar identity rather than rewriting the goal.
  convert hcalc.symm using 1
  congr 1
  funext i
  fin_cases i
  rfl

/-- At a vanishing first jet, contraction of the linearized contact Hamiltonian field with
`dα`, tested on a contact vector, is the negative Hessian. -/
theorem mextDeriv_fderiv_contactHamiltonianVectorField
    (hα : α.IsContactForm) (hf : ContDiffAt ℝ 2 f x) (hf₀ : f x = 0)
    (hdf : fderiv ℝ f x = 0) (v : E) (w : TangentSpace 𝓘(ℝ, E) x)
    (hw : w ∈ α.kerDistribution x) :
    mextDeriv α.val x ![(NormedSpace.fromTangentSpace x).symm
      (fderiv ℝ (fun y ↦ NormedSpace.fromTangentSpace y
        (α.contactHamiltonianVectorField f y)) x v), w] =
      -fderiv ℝ (fderiv ℝ f) x v (NormedSpace.fromTangentSpace x w) := by
  -- Keep the fiber coefficients in fixed model spaces: their native norm instances differ
  -- from those of the tangent fibers, despite having the same underlying vectors.
  let a : E → E [⋀^Fin 1]→L[ℝ] ℝ := α.val
  let dα : E → E [⋀^Fin 2]→L[ℝ] ℝ := mextDeriv α.val
  let b : E → E →L[ℝ] E →L[ℝ] ℝ := (ContinuousAlternatingMap.flatL ℝ E ℝ) ∘ dα
  let X : E → E := fun y ↦ NormedSpace.fromTangentSpace y
    (α.contactHamiltonianVectorField f y)
  let r : E → ℝ := fun y ↦ mvfderiv 𝓘(ℝ, E) f y (α.reebVectorField y)
  let w' : E := NormedSpace.fromTangentSpace x w
  have ha : DifferentiableAt ℝ a x :=
    (isSmoothForm_modelSpace_iff.1 α.isSmoothForm).differentiable (by simp) x
  have hb : DifferentiableAt ℝ b x := by
    have hdα := (isSmoothForm_modelSpace_iff.1
      (mextDerivₗ _ 1 α).isSmoothForm).differentiable (by simp) x
    simpa only [mextDerivₗ_apply] using
      (ContinuousAlternatingMap.flatL ℝ E ℝ).differentiableAt.comp x hdα
  have hX : DifferentiableAt ℝ X x := by
    have h := hα.contMDiffAt_contactHamiltonianVectorField (n := 1) (by simp)
      (contMDiffAt_iff_contDiffAt.2 hf)
    exact (contMDiffAt_iff_contDiffAt.1
      ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).contMDiffAt.comp x h)).differentiableAt
      one_ne_zero
  have hfm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x := contMDiffAt_iff_contDiffAt.2 hf
  have hrm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 r x :=
    (hfm.contMDiffAt_mvfderiv_apply (p := ⟨x, α.reebVectorField x⟩) le_rfl).comp x
      ((hα.contMDiff_reebVectorField x).of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hr : DifferentiableAt ℝ r x :=
    (contMDiffAt_iff_contDiffAt.1 hrm).differentiableAt one_ne_zero
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt one_ne_zero
  -- Read the contact Hamiltonian equation as an identity of scalar functions.
  have heq : (fun y ↦ b y (X y) w') =
      (r * fun y ↦ a y (fun _ ↦ w')) - (fun y ↦ fderiv ℝ f y w') := by
    funext y
    have h := hα.mextDeriv_contactHamiltonianVectorField_left f y
      ((NormedSpace.fromTangentSpace y).symm w')
    have heval : α.val y ![(NormedSpace.fromTangentSpace y).symm w'] =
        a y (fun _ ↦ w') := by
      apply congrArg (a y)
      ext i
      fin_cases i
      rfl
    rw [heval, mvfderiv_eq_fderiv_apply f y
      ((NormedSpace.fromTangentSpace y).symm w')] at h
    exact (ContinuousAlternatingMap.flatL_apply_apply (dα y) (X y) w').trans h
  have hz : X x = 0 := by
    simp only [X, α.contactHamiltonianVectorField_eq_zero_of_jet_eq_zero hf₀
      (by ext u; rw [mvfderiv_eq_fderiv_apply, hdf]; rfl), map_zero]
  have ha₀ : a x (fun _ ↦ w') = 0 := by
    convert mem_kerDistribution.1 hw using 1
    congr 1
    ext i
    fin_cases i
    rfl
  have hr₀ : r x = 0 := by
    dsimp only [r]
    rw [mvfderiv_eq_fderiv_apply, hdf]
    rfl
  -- Differentiate the identity. The coefficient-derivative terms multiply the stationary
  -- field, the vanishing Reeb derivative, or the contact covector evaluated on `w`.
  have hleft := (hb.hasFDerivAt.clm_apply hX.hasFDerivAt).clm_apply
    (hasFDerivAt_const w' x)
  have hleft' : fderiv ℝ (fun y ↦ b y (X y) w') x v = b x (fderiv ℝ X x v) w' := by
    simpa [hz] using DFunLike.congr_fun hleft.fderiv v
  have hright := (hr.hasFDerivAt.mul
    (ha.hasFDerivAt.continuousAlternatingMap_apply_const (fun _ ↦ w'))).sub
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w' x))
  have hright' : fderiv ℝ ((r * fun y ↦ a y (fun _ ↦ w')) -
      (fun y ↦ fderiv ℝ f y w')) x v =
      -fderiv ℝ (fderiv ℝ f) x v w' := by
    simpa [ha₀, hr₀] using DFunLike.congr_fun hright.fderiv v
  rw [heq] at hleft'
  -- The derivative was computed in the model, while `dα` evaluates tangent vectors.
  exact (ContinuousAlternatingMap.flatL_apply_apply (dα x) (fderiv ℝ X x v) w').symm.trans
    (hleft'.symm.trans hright')

/-- The linearized contact Hamiltonian field at a vanishing first jet is infinitesimally
symplectic on the contact hyperplane. -/
theorem mextDeriv_fderiv_contactHamiltonianVectorField_add_eq_zero
    (hα : α.IsContactForm) (hf : ContDiffAt ℝ 2 f x) (hf₀ : f x = 0)
    (hdf : fderiv ℝ f x = 0) (v w : TangentSpace 𝓘(ℝ, E) x)
    (hv : v ∈ α.kerDistribution x) (hw : w ∈ α.kerDistribution x) :
    mextDeriv α.val x ![(NormedSpace.fromTangentSpace x).symm
      (fderiv ℝ (fun y ↦ NormedSpace.fromTangentSpace y
        (α.contactHamiltonianVectorField f y)) x (NormedSpace.fromTangentSpace x v)), w] +
    mextDeriv α.val x ![v, (NormedSpace.fromTangentSpace x).symm
      (fderiv ℝ (fun y ↦ NormedSpace.fromTangentSpace y
        (α.contactHamiltonianVectorField f y)) x (NormedSpace.fromTangentSpace x w))] = 0 := by
  rw [mextDeriv_apply_swap α.val x v,
    hα.mextDeriv_fderiv_contactHamiltonianVectorField hf hf₀ hdf _ w hw,
    hα.mextDeriv_fderiv_contactHamiltonianVectorField hf hf₀ hdf _ v hv]
  have hs := (hf.isSymmSndFDerivAt (by norm_num)).eq
    (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w)
  linarith

end IsContactForm

end TauCeti.SmoothForm
