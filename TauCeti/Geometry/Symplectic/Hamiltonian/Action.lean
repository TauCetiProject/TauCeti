/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import TauCeti.Geometry.Manifold.TwoForm.Basic

/-!
# The Hamiltonian action functional on loops in a manifold

Let `σ` be a two-form on a manifold `M` and `H : ℝ → M → ℝ` a time-dependent Hamiltonian. The
action of a loop `γ`, traversed over `t ∈ [0, 1]`, is measured against a reference surface: a
smooth cylinder `Γ` from `γ` to a reference loop (`TauCeti.IsSmoothCylinder`), oriented from `γ`
at `s = 0` to the reference loop at `s = 1`. The action is

`𝒜_H(γ, Γ) = ∫ Γ^* σ - ∫₀¹ H(t, γ(t)) dt`

(`TauCeti.SmoothTwoForm.cylinderAction`), the area term being `TauCeti.rectangleIntegral` over the
unit square. This is the formula of the action functional in Barraud–Damian–Humilière–Oancea,
§3.2, with the reference cylinder running from the loop to the reference loop.

The action depends on the reference cylinder in general. It only depends on the loop:

* on contractible loops, measured against caps, when `σ` vanishes on spheres
  (`TauCeti.VanishesOnSpheres`), the area condition of symplectic asphericity. Caps may end at
  different points. This gives the action functional `TauCeti.SmoothTwoForm.contractibleAction` on
  loops admitting a smooth cap (`TauCeti.SmoothTwoForm.contractibleAction_eq`);
* on loops joined to a fixed reference loop `γ₀`, measured against cylinders to `γ₀`, when `σ`
  vanishes on tori (`TauCeti.VanishesOnTori`), the area condition of symplectic atoroidality. This
  gives the action functional `TauCeti.SmoothTwoForm.referenceAction` relative to `γ₀`
  (`TauCeti.SmoothTwoForm.referenceAction_eq`). Choosing one reference loop in each free homotopy
  class gives the action functional on all loops admitting smooth cylinders to their reference
  loops.

Both area conditions hold for exact forms (`TauCeti.vanishesOnSpheres_mextDeriv`,
`TauCeti.vanishesOnTori_mextDeriv`). Under the respective area condition, a constant loop at `x`
has action `-∫₀¹ H(t, x) dt` (`TauCeti.SmoothTwoForm.contractibleAction_const`), and a smooth
reference loop has action `-∫₀¹ H(t, γ₀(t)) dt` relative to itself
(`TauCeti.SmoothTwoForm.referenceAction_self`).

## Main definitions

* `TauCeti.SmoothTwoForm.cylinderAction σ H u`: the action of the loop `t ↦ u (0, t)` measured
  against the cylinder `u`.
* `TauCeti.SmoothTwoForm.contractibleAction σ H γ`: the action of a loop measured against a smooth
  cap, when one exists.
* `TauCeti.SmoothTwoForm.referenceAction σ H γ₀ γ`: the action of a loop measured against a smooth
  cylinder to the reference loop `γ₀`, when one exists.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff Interval

namespace TauCeti

namespace SmoothTwoForm

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ} {γ γ₀ : ℝ → M} {u v : ℝ × ℝ → M}

/-- The Hamiltonian action of the loop `t ↦ u (0, t)` measured against the cylinder `u`:
`∫ u^* σ - ∫₀¹ H(t, u(0, t)) dt`, the area term being the integral over the unit square oriented
by the coordinates `(s, t)`. -/
def cylinderAction (σ : SmoothTwoForm I M) (H : ℝ → M → ℝ) (u : ℝ × ℝ → M) : ℝ :=
  rectangleIntegral σ.1 u (0, 0) (1, 1) - ∫ t in 0..1, H t (u (0, t))

/-- Unfolding `TauCeti.SmoothTwoForm.cylinderAction`. -/
theorem cylinderAction_def (σ : SmoothTwoForm I M) (H : ℝ → M → ℝ) (u : ℝ × ℝ → M) :
    σ.cylinderAction H u = rectangleIntegral σ.1 u (0, 0) (1, 1) - ∫ t in 0..1, H t (u (0, t)) :=
  (rfl)

/-- The action measured against a cylinder from `γ` is `∫ u^* σ - ∫₀¹ H(t, γ(t)) dt`. -/
theorem cylinderAction_eq_of_isSmoothCylinder (hu : IsSmoothCylinder I γ γ₀ u) :
    σ.cylinderAction H u = rectangleIntegral σ.1 u (0, 0) (1, 1) - ∫ t in 0..1, H t (γ t) := by
  simp only [cylinderAction_def, hu.apply_zero]

/-- **Independence of the cap.** If `σ` vanishes on spheres, the action of a loop is the same
measured against any two smooth caps, even if they end at different points. -/
theorem cylinderAction_eq_of_vanishesOnSpheres (hσ : VanishesOnSpheres σ.1) {x y : M}
    (hu : IsSmoothCylinder I γ (fun _ ↦ x) u) (hv : IsSmoothCylinder I γ (fun _ ↦ y) v) :
    σ.cylinderAction H u = σ.cylinderAction H v := by
  rw [cylinderAction_eq_of_isSmoothCylinder hu, cylinderAction_eq_of_isSmoothCylinder hv,
    hσ.rectangleIntegral_eq (σ.isSmoothForm.of_le (by simp)) hu hv]

/-- **Independence of the cylinder.** If `σ` vanishes on tori, the action of a loop is the same
measured against any two smooth cylinders to the same reference loop. -/
theorem cylinderAction_eq_of_vanishesOnTori (hσ : VanishesOnTori σ.1)
    (hu : IsSmoothCylinder I γ γ₀ u) (hv : IsSmoothCylinder I γ γ₀ v) :
    σ.cylinderAction H u = σ.cylinderAction H v := by
  rw [cylinderAction_eq_of_isSmoothCylinder hu, cylinderAction_eq_of_isSmoothCylinder hv,
    hσ.rectangleIntegral_eq (σ.isSmoothForm.of_le (by simp)) hu hv]

open Classical in
/-- The Hamiltonian action of a contractible loop `γ`, measured against a smooth cap of `γ`; it is
`0` when `γ` has no smooth cap. When `σ` vanishes on spheres it does not depend on the cap
(`TauCeti.SmoothTwoForm.contractibleAction_eq`). -/
def contractibleAction (σ : SmoothTwoForm I M) (H : ℝ → M → ℝ) (γ : ℝ → M) : ℝ :=
  if h : ∃ u : ℝ × ℝ → M, ∃ x : M, IsSmoothCylinder I γ (fun _ ↦ x) u then
    σ.cylinderAction H h.choose
  else 0

/-- If `σ` vanishes on spheres, the action of a contractible loop is its action measured against
any smooth cap. -/
theorem contractibleAction_eq (hσ : VanishesOnSpheres σ.1) {x : M}
    (hu : IsSmoothCylinder I γ (fun _ ↦ x) u) :
    σ.contractibleAction H γ = σ.cylinderAction H u := by
  have h : ∃ u : ℝ × ℝ → M, ∃ x : M, IsSmoothCylinder I γ (fun _ ↦ x) u := ⟨u, x, hu⟩
  simp only [contractibleAction, h, ↓reduceDIte]
  exact cylinderAction_eq_of_vanishesOnSpheres hσ h.choose_spec.choose_spec hu

/-- The action of a loop with no smooth cap is `0`. -/
@[simp]
theorem contractibleAction_eq_zero_of_not_exists
    (h : ¬∃ u : ℝ × ℝ → M, ∃ x : M, IsSmoothCylinder I γ (fun _ ↦ x) u) :
    σ.contractibleAction H γ = 0 :=
  dite_eq_right h

/-- If `σ` vanishes on spheres, the action of the constant loop at `x` is `-∫₀¹ H(t, x) dt`. -/
@[simp]
theorem contractibleAction_const (hσ : VanishesOnSpheres σ.1) (x : M) :
    σ.contractibleAction H (fun _ ↦ x) = -∫ t in 0..1, H t x := by
  have hc : IsSmoothCylinder I (fun _ ↦ x) (fun _ ↦ x) ((fun _ : ℝ ↦ x) ∘ Prod.fst) :=
    ⟨contMDiff_const, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  rw [contractibleAction_eq hσ hc, cylinderAction_eq_of_isSmoothCylinder hc,
    rectangleIntegral_comp_fst, zero_sub]

open Classical in
/-- The Hamiltonian action of a loop `γ` relative to the reference loop `γ₀`, measured against a
smooth cylinder from `γ` to `γ₀`; it is `0` when there is no such cylinder. When `σ` vanishes on
tori it does not depend on the cylinder (`TauCeti.SmoothTwoForm.referenceAction_eq`). -/
def referenceAction (σ : SmoothTwoForm I M) (H : ℝ → M → ℝ) (γ₀ γ : ℝ → M) : ℝ :=
  if h : ∃ u : ℝ × ℝ → M, IsSmoothCylinder I γ γ₀ u then σ.cylinderAction H h.choose else 0

/-- If `σ` vanishes on tori, the action of a loop relative to `γ₀` is its action measured against
any smooth cylinder to `γ₀`. -/
theorem referenceAction_eq (hσ : VanishesOnTori σ.1) (hu : IsSmoothCylinder I γ γ₀ u) :
    σ.referenceAction H γ₀ γ = σ.cylinderAction H u := by
  have h : ∃ u : ℝ × ℝ → M, IsSmoothCylinder I γ γ₀ u := ⟨u, hu⟩
  simp only [referenceAction, h, ↓reduceDIte]
  exact cylinderAction_eq_of_vanishesOnTori hσ h.choose_spec hu

/-- The action of a loop relative to `γ₀` is `0` when there is no smooth cylinder to `γ₀`. -/
@[simp]
theorem referenceAction_eq_zero_of_not_exists (h : ¬∃ u : ℝ × ℝ → M, IsSmoothCylinder I γ γ₀ u) :
    σ.referenceAction H γ₀ γ = 0 :=
  dite_eq_right h

/-- If `σ` vanishes on tori, a smooth reference loop `γ₀` with `γ₀ 1 = γ₀ 0` has action
`-∫₀¹ H(t, γ₀(t)) dt` relative to itself. -/
@[simp]
theorem referenceAction_self (hσ : VanishesOnTori σ.1) (hγ₀ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ₀)
    (hper : γ₀ 1 = γ₀ 0) : σ.referenceAction H γ₀ γ₀ = -∫ t in 0..1, H t (γ₀ t) := by
  have hc : IsSmoothCylinder I γ₀ γ₀ (γ₀ ∘ Prod.snd) :=
    ⟨hγ₀.comp contDiff_snd.contMDiff, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ hper⟩
  rw [referenceAction_eq hσ hc, cylinderAction_eq_of_isSmoothCylinder hc,
    rectangleIntegral_comp_snd, zero_sub]

end SmoothTwoForm

end TauCeti
