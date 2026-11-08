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

(`TauCeti.cylinderAction`), the area term being `TauCeti.rectangleIntegral` over the unit square.
This is the formula of the action functional in Barraud–Damian–Humilière–Oancea, §3.2, with the
reference cylinder running from the loop to the reference loop. Measured against a cap `u` of `γ`,
a map running from `γ` at `s = 0` to a point at `s = 1`, it is the action `A_H(γ, u)` of the
capped loop `(γ, u)`, the action on which capped Hamiltonian Floer theory on a closed symplectic
manifold is built.

The action is defined for an arbitrary two-form and an arbitrary map `u`. For a continuous form
and `C¹` maps it obeys the following laws.

* **Gluing.** Gluing a map `v` to the far end of `u` adds the area of `v`,
  `A_H(γ, u # v) = A_H(γ, u) + ∫ v^* σ` (`TauCeti.cylinderAction_rectangleTrans`); for a cap `u`
  and a sphere `v` at its centre this is the recapping law. Along a cylinder `w` from `γ₀` to
  `γ₁` and a cap `v` of `γ₁`,
  `A_H(γ₀, w # v) - A_H(γ₁, v) = ∫ w^* σ - ∫₀¹ H(t, γ₀(t)) dt + ∫₀¹ H(t, γ₁(t)) dt`
  (`TauCeti.cylinderAction_rectangleTrans_sub`), which identifies the energy of a Floer cylinder
  with the drop of the capped action.
* **Recapping.** Two caps `u`, `v` of the same loop differ by a sphere, obtained by running
  backwards through `u` and then through `v`, and `A_H(γ, v) - A_H(γ, u)` is the area of this
  sphere (`TauCeti.cylinderAction_sub_cylinderAction`).

For a closed `C¹` form the action is moreover unchanged along a `C²` homotopy of caps fixing the
loop (`TauCeti.cylinderAction_eq_of_homotopy`).

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

* `TauCeti.cylinderAction σ H u`: the action of the loop `t ↦ u (0, t)` measured against the map
  `u`.
* `TauCeti.SmoothTwoForm.contractibleAction σ H γ`: the action of a loop measured against a smooth
  cap, when one exists.
* `TauCeti.SmoothTwoForm.referenceAction σ H γ₀ γ`: the action of a loop measured against a smooth
  cylinder to the reference loop `γ₀`, when one exists.

## Main results

* `TauCeti.cylinderAction_rectangleTrans_sub`: the action difference along a cylinder, for caps
  glued along it.
* `TauCeti.cylinderAction_sub_cylinderAction`: recapping changes the action by the area of the
  sphere between the two caps.
* `TauCeti.cylinderAction_eq_of_homotopy`: for a closed `C¹` form, the action is unchanged along a
  `C²` homotopy of caps fixing the loop.

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

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M]

/-! ### The action measured against a surface -/

/-- The Hamiltonian action of the loop `t ↦ u (0, t)` measured against the map `u`, for a
two-form `σ` and a time-dependent Hamiltonian `H`:
`∫ u^* σ - ∫₀¹ H(t, u(0, t)) dt`, the area term being the integral over the unit square oriented
by the coordinates `(s, t)`.

No condition is imposed on `σ` or `u`. For a cylinder `u` to a reference loop this is the action
relative to that loop. For a cap `u` of the loop `γ = u (0, ·)` it is the action `A_H(γ, u)` of
the capped loop `(γ, u)`, which depends on the cap when `σ` does not vanish on spheres
(`TauCeti.cylinderAction_sub_cylinderAction`). -/
def cylinderAction (σ : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (u : ℝ × ℝ → M) : ℝ :=
  rectangleIntegral σ u (0, 0) (1, 1) - ∫ t in 0..1, H t (u (0, t))

/-- Unfolding `TauCeti.cylinderAction`. -/
theorem cylinderAction_def (σ : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (u : ℝ × ℝ → M) :
    cylinderAction σ H u = rectangleIntegral σ u (0, 0) (1, 1) - ∫ t in 0..1, H t (u (0, t)) :=
  (rfl)

/-- The constant map at `x`, a cap of the constant loop at `x`, has action `-∫₀¹ H(t, x) dt`. -/
@[simp]
theorem cylinderAction_const (σ : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (x : M) :
    cylinderAction σ H (fun _ ↦ x) = -∫ t in 0..1, H t x := by
  have h : rectangleIntegral σ (fun _ : ℝ × ℝ ↦ x) (0, 0) (1, 1) = 0 :=
    rectangleIntegral_comp_fst σ (fun _ ↦ x) _ _
  rw [cylinderAction_def, h, zero_sub]

section Continuous

variable [IsManifold I 1 M] {σ : RoughForm I M ℝ 2}

/-- **Gluing at the far end.** For a continuous form and `C¹` maps `u` and `v` with
`u (1, ·) = v (0, ·)`, gluing `v` to the far end of `u` adds the area of `v` to the action of
`u`. If `u` is a cap whose centre is the base of a sphere `v`, then the glued map is again a cap
of the same loop, and this is the recapping law `A_H(γ, u # v) = A_H(γ, u) + σ(v)`. -/
theorem cylinderAction_rectangleTrans (hσ : IsSmoothForm I 0 σ) (H : ℝ → M → ℝ)
    {u v : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (h : ∀ t, u (1, t) = v (0, t)) :
    cylinderAction σ H (rectangleTrans u v) =
      cylinderAction σ H u + rectangleIntegral σ v (0, 0) (1, 1) := by
  simp only [cylinderAction_def, rectangleTrans_apply_zero,
    rectangleIntegral_rectangleTrans hσ hu hv h]
  ring

/-- **The action along a cylinder.** For a continuous form and `C¹` maps `w` and `v` with
`w (1, ·) = v (0, ·)`, the action of the loop `γ₀ = w (0, ·)` measured against `w # v` exceeds
the action of the loop `γ₁ = w (1, ·)` measured against `v` by the area of `w` minus the change of
the Hamiltonian term:
`A_H(γ₀, w # v) - A_H(γ₁, v) = ∫ w^* σ - ∫₀¹ H(t, γ₀(t)) dt + ∫₀¹ H(t, γ₁(t)) dt`. When `v` is a
cap of `γ₁` and `w` a cylinder from `γ₀` to `γ₁`, `w # v` is a cap of `γ₀` and this is the
difference of capped actions. -/
theorem cylinderAction_rectangleTrans_sub (hσ : IsSmoothForm I 0 σ) (H : ℝ → M → ℝ)
    {w v : ℝ × ℝ → M} (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (h : ∀ t, w (1, t) = v (0, t)) :
    cylinderAction σ H (rectangleTrans w v) - cylinderAction σ H v =
      rectangleIntegral σ w (0, 0) (1, 1) - (∫ t in 0..1, H t (w (0, t))) +
        ∫ t in 0..1, H t (w (1, t)) := by
  simp only [cylinderAction_rectangleTrans hσ H hw hv h, cylinderAction_def, h]
  ring

/-- **Recapping.** For a continuous form and two `C¹` maps `u` and `v` starting at the same loop,
`u (0, ·) = v (0, ·)`, the actions differ by the area of the concatenation running backwards
through `u` and then forwards through `v`. When `u` and `v` are caps of the loop, this
concatenation is the sphere by which the caps differ. -/
theorem cylinderAction_sub_cylinderAction (hσ : IsSmoothForm I 0 σ) (H : ℝ → M → ℝ)
    {u v : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (h : ∀ t, u (0, t) = v (0, t)) :
    cylinderAction σ H v - cylinderAction σ H u =
      rectangleIntegral σ (rectangleTrans (u ∘ Prod.map (fun s ↦ 1 - s) id) v) (0, 0) (1, 1) := by
  simp only [cylinderAction_def, rectangleIntegral_rectangleTrans_comp_prodMap_one_sub hσ hu hv h,
    h]
  ring

end Continuous

/-- **Homotopy invariance.** For a closed `C¹` two-form, the action does not change along a `C²`
homotopy `Φ` that fixes the loop `Φ ((0, t), c)`, keeps the far end `Φ ((1, t), c)` a single
point at each time `c` (the point may move), and keeps the maps periodic in `t`. So caps related
by such a homotopy relative to the loop give the same action. -/
theorem cylinderAction_eq_of_homotopy [IsManifold I 2 M] {σ : RoughForm I M ℝ 2}
    (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (H : ℝ → M → ℝ)
    {Φ : (ℝ × ℝ) × ℝ → M} (hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ)
    (hloop : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, Φ ((0, t), c) = Φ ((0, t), 0))
    (hcentre : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, Φ ((1, t), c) = Φ ((1, 0), c))
    (hper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, Φ ((s, 1), c) = Φ ((s, 0), c)) :
    cylinderAction σ H (fun z ↦ Φ (z, 1)) = cylinderAction σ H (fun z ↦ Φ (z, 0)) := by
  have hI : [[(0 : ℝ), 1]] = Icc 0 1 := uIcc_of_le zero_le_one
  have hc1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  -- The loop does not move, so the Hamiltonian terms agree.
  have hH : ∫ t in 0..1, H t (Φ ((0, t), 1)) = ∫ t in 0..1, H t (Φ ((0, t), 0)) :=
    intervalIntegral.integral_congr fun t ht ↦ by rw [hloop t (hI ▸ ht) 1 hc1]
  simp only [cylinderAction_def]
  rw [rectangleIntegral_eq_of_homotopy (a := (0, 0)) (b := (1, 1)) hσ hdσ hΦ
      (.inl fun t ht c hc ↦ hloop t (hI ▸ ht) c hc)
      (.inr fun t ht c hc ↦ (hcentre t (hI ▸ ht) c hc).trans (hcentre 1 hc1 c hc).symm)
      (fun s hs c hc ↦ hper s (hI ▸ hs) c hc), hH]

namespace SmoothTwoForm

variable [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ} {γ γ₀ : ℝ → M} {u v : ℝ × ℝ → M}

/-- The action measured against a cylinder from `γ` is `∫ u^* σ - ∫₀¹ H(t, γ(t)) dt`. -/
theorem cylinderAction_eq_of_isSmoothCylinder (hu : IsSmoothCylinder I γ γ₀ u) :
    cylinderAction σ.1 H u = rectangleIntegral σ.1 u (0, 0) (1, 1) - ∫ t in 0..1, H t (γ t) := by
  simp only [cylinderAction_def, hu.apply_zero]

/-- **Independence of the cap.** If `σ` vanishes on spheres, the action of a loop is the same
measured against any two smooth caps, even if they end at different points. -/
theorem cylinderAction_eq_of_vanishesOnSpheres (hσ : VanishesOnSpheres σ.1) {x y : M}
    (hu : IsSmoothCylinder I γ (fun _ ↦ x) u) (hv : IsSmoothCylinder I γ (fun _ ↦ y) v) :
    cylinderAction σ.1 H u = cylinderAction σ.1 H v := by
  rw [cylinderAction_eq_of_isSmoothCylinder hu, cylinderAction_eq_of_isSmoothCylinder hv,
    hσ.rectangleIntegral_eq (σ.isSmoothForm.of_le (by simp)) hu hv]

/-- **Independence of the cylinder.** If `σ` vanishes on tori, the action of a loop is the same
measured against any two smooth cylinders to the same reference loop. -/
theorem cylinderAction_eq_of_vanishesOnTori (hσ : VanishesOnTori σ.1)
    (hu : IsSmoothCylinder I γ γ₀ u) (hv : IsSmoothCylinder I γ γ₀ v) :
    cylinderAction σ.1 H u = cylinderAction σ.1 H v := by
  rw [cylinderAction_eq_of_isSmoothCylinder hu, cylinderAction_eq_of_isSmoothCylinder hv,
    hσ.rectangleIntegral_eq (σ.isSmoothForm.of_le (by simp)) hu hv]

open Classical in
/-- The Hamiltonian action of a contractible loop `γ`, measured against a smooth cap of `γ`; it is
`0` when `γ` has no smooth cap. When `σ` vanishes on spheres it does not depend on the cap
(`TauCeti.SmoothTwoForm.contractibleAction_eq`). -/
def contractibleAction (σ : SmoothTwoForm I M) (H : ℝ → M → ℝ) (γ : ℝ → M) : ℝ :=
  if h : ∃ u : ℝ × ℝ → M, ∃ x : M, IsSmoothCylinder I γ (fun _ ↦ x) u then
    cylinderAction σ.1 H h.choose
  else 0

/-- If `σ` vanishes on spheres, the action of a contractible loop is its action measured against
any smooth cap. -/
theorem contractibleAction_eq (hσ : VanishesOnSpheres σ.1) {x : M}
    (hu : IsSmoothCylinder I γ (fun _ ↦ x) u) :
    σ.contractibleAction H γ = cylinderAction σ.1 H u := by
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
  if h : ∃ u : ℝ × ℝ → M, IsSmoothCylinder I γ γ₀ u then cylinderAction σ.1 H h.choose else 0

/-- If `σ` vanishes on tori, the action of a loop relative to `γ₀` is its action measured against
any smooth cylinder to `γ₀`. -/
theorem referenceAction_eq (hσ : VanishesOnTori σ.1) (hu : IsSmoothCylinder I γ γ₀ u) :
    σ.referenceAction H γ₀ γ = cylinderAction σ.1 H u := by
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
