/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Action
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic

/-!
# The action of capped loops

On a symplectic manifold that is not weakly exact, such as a closed symplectic manifold with
`ω ≠ 0` on `π₂`, the area of a disc bounding a loop depends on the disc, and the Hamiltonian
action is a function of a loop *together with* a disc bounding it. This file defines this
**capped action** for an arbitrary two-form and proves the laws through which it enters capped
Hamiltonian Floer theory.

A **disc** bounding a loop `γ` is a cylinder `D` (`TauCeti.IsLoopCylinder`) from a constant loop
at its centre `x` to `γ`: `D (0, ·) = x` and `D (1, ·) = γ`, like the cone `(r, t) ↦ r γ(t)` in a
vector space. It is a cap of `γ` (`TauCeti.IsCap`) run backwards. For a two-form `ω` and a
time-dependent Hamiltonian `H`, the action of `γ` capped by `D` is

`A_H(γ, D) = ∫ D^* ω + ∫₀¹ H(t, γ(t)) dt`

(`TauCeti.cappedLoopAction`), the convention of capped Floer theory in which the positive ends of
a Floer solution are its inputs, and the action increases along Floer cylinders. It is the
manifold counterpart of the action `TauCeti.SymplecticForm.hamiltonianAction` of a loop in a
symplectic vector space, which caps the loop by the cone over it.

* **Recapping.** Gluing a sphere `B` from a point `y` to the centre `x` of `D` gives the disc
  `B ⋆ D` (`TauCeti.rectangleTrans B D`) of `γ`, and `A_H(γ, B ⋆ D) = ω(B) + A_H(γ, D)`
  (`TauCeti.cappedLoopAction_rectangleTrans_left`). Conversely, two discs `D` and `D'` of `γ`
  differ by the sphere `D' ⋆ D⁻¹` obtained by gluing them along `γ`, and
  `A_H(γ, D') - A_H(γ, D) = ω(D' ⋆ D⁻¹)` (`TauCeti.cappedLoopAction_sub_cappedLoopAction`). These
  are the recapping laws `A_H(γ, B # D) = A_H(γ, D) + ω(B)` of the abstract cap classes of
  `TauCeti.Geometry.Symplectic.Floer.Cap.Basic`.
* **Homotopy invariance.** For a closed form, the action only depends on the disc up to
  homotopy through discs of `γ` (`TauCeti.cappedLoopAction_eq_of_homotopy`), by Stokes' formula
  for a homotopy (`TauCeti.rectangleIntegral_eq_of_homotopy`).
* **Transport along a cylinder.** For a cylinder `w` from `γ₀` to `γ₁`, the disc `D ⋆ w` caps
  `γ₁`, and `A_H(γ₁, D ⋆ w) - A_H(γ₀, D)` is the area of `w` plus the change of the Hamiltonian
  term (`TauCeti.cappedLoopAction_rectangleTrans_sub_cappedLoopAction`). This is how the energy
  of a Floer cylinder becomes a difference of capped actions, in
  `TauCeti.Geometry.Symplectic.Floer.CylinderAction`.
* **Special cases.** The constant loop capped by the constant disc has action the time average
  of `H` (`TauCeti.cappedLoopAction_const`). For an exact form `ω = dθ` the action is
  `∫_γ θ + ∫₀¹ H(t, γ(t)) dt` for every disc (`TauCeti.cappedLoopAction_mextDeriv`). For a weakly
  exact form the action does not depend on the disc, and it is minus the action
  `TauCeti.contractibleLoopAction` of the standing convention, which caps a loop by a disc
  running from the loop to its centre and subtracts the Hamiltonian term
  (`TauCeti.IsWeaklyExact.cappedLoopAction_eq_neg_contractibleLoopAction`).
* **Cylinder action.** The action `TauCeti.cylinderAction` of a loop `γ` measured
  against a smooth cylinder `u` from `γ` uses the opposite orientation and sign: capping `γ` by `u`
  run backwards gives minus it
  (`TauCeti.cappedLoopAction_comp_prodMap_one_sub_eq_neg_cylinderAction`).

## Main definitions

* `TauCeti.cappedLoopAction`: the Hamiltonian action of a loop capped by a disc.

## Main results

* `TauCeti.cappedLoopAction_rectangleTrans_left`: the recapping law.
* `TauCeti.cappedLoopAction_sub_cappedLoopAction`: two discs of a loop give actions differing by
  the area of the sphere they bound.
* `TauCeti.cappedLoopAction_eq_of_homotopy`: homotopy invariance for closed forms.
* `TauCeti.cappedLoopAction_rectangleTrans_sub_cappedLoopAction`: transport of the disc along a
  cylinder.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops and its recapping law.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (the action functional on the cover of the loop space).
-/

public section

noncomputable section

open Set
open scoped Manifold Interval

namespace TauCeti

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- The **capped action** of a loop `γ` capped by a map `D` of the plane, for a two-form `ω` and a
time-dependent Hamiltonian `H`:
`A_H(γ, D) = ∫ D^* ω + ∫₀¹ H(t, γ(t)) dt`, the area integral over the unit square. It is meant for
a disc `D` bounding `γ`, a cylinder `IsLoopCylinder I D (fun _ ↦ x) γ` from the constant loop at
its centre `x` to `γ`. -/
def cappedLoopAction (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (γ : ℝ → M) (D : ℝ × ℝ → M) : ℝ :=
  rectangleIntegral ω D (0, 0) (1, 1) + ∫ t in 0..1, H t (γ t)

theorem cappedLoopAction_def (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (γ : ℝ → M)
    (D : ℝ × ℝ → M) :
    cappedLoopAction ω H γ D = rectangleIntegral ω D (0, 0) (1, 1) + ∫ t in 0..1, H t (γ t) :=
  (rfl)

/-- The constant loop at `x`, capped by the constant disc, has action the time average
`∫₀¹ H(t, x) dt` of the Hamiltonian at `x`. -/
@[simp]
theorem cappedLoopAction_const (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (x : M) :
    cappedLoopAction ω H (fun _ ↦ x) (fun _ ↦ x) = ∫ t in 0..1, H t x := by
  rw [cappedLoopAction_def, rectangleIntegral_const, zero_add]

section Continuous

variable [IsManifold I 1 M] {ω : RoughForm I M ℝ 2}

/-- **The recapping law.** Gluing a cylinder `B` that ends at the centre `x` of a disc `D` of `γ`
in front of `D` adds the area of `B` to the action. When `B` is a sphere, from a constant loop to
the constant loop at `x`, the glued map `B ⋆ D` is again a disc of `γ`, and this is the law
`A_H(γ, B ⋆ D) = ω(B) + A_H(γ, D)`. -/
theorem cappedLoopAction_rectangleTrans_left (hω : IsSmoothForm I 0 ω) (H : ℝ → M → ℝ)
    {B D : ℝ × ℝ → M} {β γ : ℝ → M} {x : M} (hB : IsLoopCylinder I B β fun _ ↦ x)
    (hD : IsLoopCylinder I D (fun _ ↦ x) γ) :
    cappedLoopAction ω H γ (rectangleTrans B D) =
      rectangleIntegral ω B (0, 0) (1, 1) + cappedLoopAction ω H γ D := by
  rw [cappedLoopAction_def, cappedLoopAction_def,
    rectangleIntegral_rectangleTrans hω (hB.contMDiff.of_le one_le_two)
      (hD.contMDiff.of_le one_le_two) fun t ↦ (hB.apply_one t).trans (hD.apply_zero t).symm,
    add_assoc]

/-- **Two discs differ by a sphere.** For two discs `D` and `D'` of the same loop `γ`, with
centres `x` and `x'`, the difference of the actions is the area of the sphere
`D' ⋆ D⁻¹` from `x'` to `x` obtained by gluing `D'` to `D` run backwards
(`TauCeti.IsLoopCylinder.trans`, `TauCeti.IsLoopCylinder.symm`). -/
theorem cappedLoopAction_sub_cappedLoopAction (hω : IsSmoothForm I 0 ω) (H : ℝ → M → ℝ)
    {D D' : ℝ × ℝ → M} {γ : ℝ → M} {x x' : M} (hD : IsLoopCylinder I D (fun _ ↦ x) γ)
    (hD' : IsLoopCylinder I D' (fun _ ↦ x') γ) :
    cappedLoopAction ω H γ D' - cappedLoopAction ω H γ D =
      rectangleIntegral ω (rectangleTrans D' (D ∘ Prod.map (fun s ↦ 1 - s) id)) (0, 0) (1, 1) := by
  rw [cappedLoopAction_def, cappedLoopAction_def,
    rectangleIntegral_rectangleTrans hω (hD'.contMDiff.of_le one_le_two)
      (hD.symm.contMDiff.of_le one_le_two)
      fun t ↦ (hD'.apply_one t).trans (hD.symm.apply_zero t).symm,
    rectangleIntegral_comp_prodMap_one_sub hω (hD.contMDiff.of_le one_le_two)]
  ring

/-- **Transport of a disc along a cylinder.** For a disc `D` of `γ₀` and a cylinder `w` from `γ₀`
to `γ₁`, the glued map `D ⋆ w` is a disc of `γ₁` (`TauCeti.IsLoopCylinder.trans`), and its action
exceeds that of `(γ₀, D)` by the area of `w` and the change of the Hamiltonian term. -/
theorem cappedLoopAction_rectangleTrans_sub_cappedLoopAction (hω : IsSmoothForm I 0 ω)
    (H : ℝ → M → ℝ) {D w : ℝ × ℝ → M} {γ₀ γ₁ : ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) γ₀) (hw : IsLoopCylinder I w γ₀ γ₁) :
    cappedLoopAction ω H γ₁ (rectangleTrans D w) - cappedLoopAction ω H γ₀ D =
      rectangleIntegral ω w (0, 0) (1, 1) + (∫ t in 0..1, H t (γ₁ t)) -
        ∫ t in 0..1, H t (γ₀ t) := by
  rw [cappedLoopAction_def, cappedLoopAction_def,
    rectangleIntegral_rectangleTrans hω (hD.contMDiff.of_le one_le_two)
      (hw.contMDiff.of_le one_le_two) fun t ↦ (hD.apply_one t).trans (hw.apply_zero t).symm]
  ring

/-- For a continuous weakly exact form, the capped action of a loop `γ` with any disc is minus
its action `TauCeti.contractibleLoopAction` in the standing convention, which caps `γ` by a disc
running from `γ` to its centre and subtracts the Hamiltonian term. In particular the capped action
does not depend on the disc. -/
theorem IsWeaklyExact.cappedLoopAction_eq_neg_contractibleLoopAction (hω : IsSmoothForm I 0 ω)
    (hw : IsWeaklyExact ω) (H : ℝ → M → ℝ) {D : ℝ × ℝ → M} {γ : ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) γ) :
    cappedLoopAction ω H γ D = -contractibleLoopAction ω H γ := by
  rw [hw.contractibleLoopAction_eq hω H hD.symm.isCap, cylinderAction_def,
    rectangleIntegral_comp_prodMap_one_sub hω (hD.contMDiff.of_le one_le_two),
    cappedLoopAction_def]
  simp only [Function.comp_apply, Prod.map_apply, sub_zero, id_eq, hD.apply_one]
  ring

end Continuous

open scoped ContDiff in
/-- The action `TauCeti.cylinderAction` of a loop `γ` measured against a smooth
cylinder `u` from `γ` (for instance a cap of `γ`) is minus the capped action of `γ` with `u` run
backwards, `u ∘ Prod.map (fun s ↦ 1 - s) id`, which is a disc of `γ` when `u` is a cap. -/
theorem cappedLoopAction_comp_prodMap_one_sub_eq_neg_cylinderAction [IsManifold I ∞ M]
    (σ : SmoothTwoForm I M) (H : ℝ → M → ℝ) {γ γ₀ : ℝ → M} {u : ℝ × ℝ → M}
    (hu : IsSmoothCylinder I γ γ₀ u) :
    cappedLoopAction σ.1 H γ (u ∘ Prod.map (fun s ↦ 1 - s) id) = -cylinderAction σ.1 H u := by
  rw [cappedLoopAction_def, SmoothTwoForm.cylinderAction_eq_of_isSmoothCylinder hu,
    rectangleIntegral_comp_prodMap_one_sub (σ.isSmoothForm.of_le (by simp))
      (hu.contMDiff.of_le (by simp))]
  ring


/-- For an exact form `dθ`, the capped action of a loop `γ` with any disc is
`∫_γ θ + ∫₀¹ H(t, γ(t)) dt`, by Green's formula: the line integral along the centre of the disc
vanishes. -/
theorem cappedLoopAction_mextDeriv [IsManifold I 2 M] {θ : RoughForm I M ℝ 1}
    (hθ : IsSmoothForm I 1 θ) (H : ℝ → M → ℝ) {D : ℝ × ℝ → M} {γ : ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) γ) :
    cappedLoopAction (mextDeriv θ) H γ D = pathIntegral θ γ 0 1 + ∫ t in 0..1, H t (γ t) := by
  rw [cappedLoopAction_def, hD.rectangleIntegral_mextDeriv hθ, pathIntegral_const_curve,
    sub_zero]

/-- **Homotopy invariance of the capped action.** Let `ω` be a closed `C¹` two-form and
`Φ : (ℝ × ℝ) × ℝ → M` a `C²` homotopy of maps `Φ(·, c)` of the unit square, through maps that
collapse the edge `s = 0` to a point, keep the edge `s = 1` fixed and agree on the edges
`t = 0` and `t = 1`. For instance `Φ` is a homotopy of discs of `γ`, relative to `γ` but with a
moving centre. Then the capped actions of `γ` with the discs `Φ(·, 0)` and `Φ(·, 1)` agree. -/
theorem cappedLoopAction_eq_of_homotopy [IsManifold I 2 M] {ω : RoughForm I M ℝ 2}
    (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0) (H : ℝ → M → ℝ) (γ : ℝ → M)
    {Φ : (ℝ × ℝ) × ℝ → M} (hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ)
    (hcentre : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, Φ ((0, t), c) = Φ ((0, 0), c))
    (hloop : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, Φ ((1, t), c) = Φ ((1, t), 0))
    (hper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, Φ ((s, 1), c) = Φ ((s, 0), c)) :
    cappedLoopAction ω H γ (fun z ↦ Φ (z, 1)) = cappedLoopAction ω H γ (fun z ↦ Φ (z, 0)) := by
  have h01 : [[(0 : ℝ), 1]] = Icc 0 1 := uIcc_of_le zero_le_one
  rw [cappedLoopAction_def, cappedLoopAction_def,
    rectangleIntegral_eq_of_homotopy hω hdω hΦ (a := (0, 0)) (b := (1, 1))
      (Or.inr (by simpa only [h01] using hcentre)) (Or.inl (by simpa only [h01] using hloop))
      (by simpa only [h01] using hper)]

end TauCeti
