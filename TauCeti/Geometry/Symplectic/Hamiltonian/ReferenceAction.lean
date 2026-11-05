/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction

/-!
# The action functional relative to a reference loop on an atoroidal manifold

On a weakly exact manifold the action of a contractible loop is measured against a cap
(`TauCeti.contractibleLoopAction`). For loops in an arbitrary free homotopy class one fixes a
reference loop `γ₀` in the class and measures the action against a cylinder from the loop to
`γ₀` (`TauCeti.IsLoopCylinder`), oriented from the loop at `s = 0` to `γ₀` at `s = 1`.

A cylinder from a loop to itself is a **torus**. The two-form `φ` **vanishes on tori**
(`TauCeti.VanishesOnTori`) when its integral over every torus vanishes. Gluing two cylinders from
`γ` to `γ₀` along `γ₀` gives a torus, so for a continuous form vanishing on tori all cylinders
from `γ` to `γ₀` have the same integral (`TauCeti.VanishesOnTori.rectangleIntegral_eq`). This
common value is the **reference area** `TauCeti.referenceArea φ γ₀ γ`, and gluing cylinders shows
that the reference areas of two loops joined by a cylinder `w` differ by `∫ w^* φ`
(`TauCeti.VanishesOnTori.referenceArea_eq_rectangleIntegral_add`). Exact forms vanish on tori
(`TauCeti.vanishesOnTori_mextDeriv`), and the reference area of `γ` for `dα` is
`∫_{γ₀} α - ∫_γ α` (`TauCeti.referenceArea_mextDeriv`).

For a two-form `ω` vanishing on tori and a time-dependent Hamiltonian `H : ℝ → M → ℝ`, the
**action relative to `γ₀`** of a loop `γ` joined to `γ₀` by a cylinder `w` is

`A_H(γ) = ∫ w^* ω - ∫₀¹ H(t, γ(t)) dt`

(`TauCeti.referenceLoopAction`). It does not depend on the cylinder
(`TauCeti.VanishesOnTori.referenceLoopAction_eq`), along a cylinder between two loops it changes
by the area of the cylinder and the Hamiltonian terms
(`TauCeti.VanishesOnTori.referenceLoopAction_sub`), and the reference loop itself has action
`-∫₀¹ H(t, γ₀(t)) dt` (`TauCeti.VanishesOnTori.referenceLoopAction_self`). Choosing one reference
loop in each free homotopy class gives the action functional on all loops admitting cylinders to
their reference loops, as in Barraud–Damian–Humilière–Oancea, §3.2.

Vanishing on tori is the area half of symplectic atoroidality, which also asks the first Chern
class to vanish on tori; the area condition alone is what the action functional needs.

## Main definitions

* `TauCeti.VanishesOnTori`: a two-form whose integral over every torus vanishes.
* `TauCeti.referenceArea`: the integral of a two-form over a cylinder from a loop to a reference
  loop.
* `TauCeti.referenceLoopAction`: the Hamiltonian action of a loop relative to a reference loop.

## Main results

* `TauCeti.VanishesOnTori.rectangleIntegral_eq`: for a form vanishing on tori, all cylinders
  between two loops have the same area.
* `TauCeti.VanishesOnTori.referenceArea_eq_rectangleIntegral_add`: the reference areas of the two
  ends of a cylinder differ by the area of the cylinder.
* `TauCeti.vanishesOnTori_mextDeriv`, `TauCeti.referenceArea_mextDeriv`: exact forms vanish on
  tori, and the reference area for `dα` is a difference of line integrals of `α`.
* `TauCeti.VanishesOnTori.referenceLoopAction_sub`: the action difference along a cylinder.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2 (asphericity, atoroidality and the
  action functional relative to reference loops).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology.
-/

public section

noncomputable section

open scoped Manifold Interval

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Forms vanishing on tori and the reference area -/

/-- A two-form **vanishes on tori** when its integral over every torus, a cylinder from a loop to
itself, vanishes. For a symplectic form this is the area half of symplectic atoroidality. -/
def VanishesOnTori (φ : RoughForm I M F 2) : Prop :=
  ∀ ⦃w : ℝ × ℝ → M⦄ ⦃γ : ℝ → M⦄, IsLoopCylinder I w γ γ → rectangleIntegral φ w (0, 0) (1, 1) = 0

theorem vanishesOnTori_iff {φ : RoughForm I M F 2} :
    VanishesOnTori φ ↔ ∀ ⦃w : ℝ × ℝ → M⦄ ⦃γ : ℝ → M⦄,
      IsLoopCylinder I w γ γ → rectangleIntegral φ w (0, 0) (1, 1) = 0 :=
  Iff.rfl

open Classical in
/-- The **reference area** of a loop `γ` relative to the reference loop `γ₀` for a two-form `φ`:
the integral of `φ` over a cylinder from `γ` to `γ₀`, or `0` when there is no such cylinder. For a
continuous form vanishing on tori it does not depend on the choice of cylinder
(`TauCeti.VanishesOnTori.referenceArea_eq`). -/
def referenceArea (φ : RoughForm I M F 2) (γ₀ γ : ℝ → M) : F :=
  if h : ∃ w, IsLoopCylinder I w γ γ₀ then rectangleIntegral φ h.choose (0, 0) (1, 1) else 0

/-- The reference area of a loop with no cylinder to the reference loop is `0`. -/
theorem referenceArea_of_not_exists {φ : RoughForm I M F 2} {γ₀ γ : ℝ → M}
    (h : ¬∃ w, IsLoopCylinder I w γ γ₀) : referenceArea φ γ₀ γ = 0 :=
  dite_eq_right h

section Continuous

variable [IsManifold I 1 M] {φ : RoughForm I M F 2}

/-- **Independence of the cylinder.** For a continuous form vanishing on tori, any two cylinders
between the same two loops have the same integral: gluing them along the second loop gives a
torus. -/
theorem VanishesOnTori.rectangleIntegral_eq (hφ : IsSmoothForm I 0 φ) (hT : VanishesOnTori φ)
    {u v : ℝ × ℝ → M} {γ γ₀ : ℝ → M} (hu : IsLoopCylinder I u γ γ₀)
    (hv : IsLoopCylinder I v γ γ₀) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) := by
  have htorus := hT (hu.symm.trans hv)
  rw [rectangleIntegral_rectangleTrans hφ (hu.symm.contMDiff.of_le one_le_two)
      (hv.contMDiff.of_le one_le_two)
      (fun t ↦ (hu.symm.apply_one t).trans (hv.apply_zero t).symm),
    rectangleIntegral_comp_prodMap_one_sub hφ (hu.contMDiff.of_le one_le_two)] at htorus
  exact neg_add_eq_zero.mp htorus

/-- For a continuous form vanishing on tori, the reference area of a loop is the integral over any
cylinder from the loop to the reference loop. -/
theorem VanishesOnTori.referenceArea_eq (hφ : IsSmoothForm I 0 φ) (hT : VanishesOnTori φ)
    {w : ℝ × ℝ → M} {γ₀ γ : ℝ → M} (hw : IsLoopCylinder I w γ γ₀) :
    referenceArea φ γ₀ γ = rectangleIntegral φ w (0, 0) (1, 1) := by
  have h : ∃ w, IsLoopCylinder I w γ γ₀ := ⟨w, hw⟩
  rw [referenceArea, dite_eq_left h]
  exact hT.rectangleIntegral_eq hφ h.choose_spec hw

/-- **The reference area along a cylinder.** For a continuous form vanishing on tori and a
cylinder `w` from `γ₁` to a loop `γ₂` joined to `γ₀` by a cylinder, the reference area of `γ₁` is
the area of `w` plus the reference area of `γ₂`. The loop `γ₁` is joined to `γ₀` by gluing `w` to
a cylinder from `γ₂` (`TauCeti.IsLoopCylinder.trans`). -/
theorem VanishesOnTori.referenceArea_eq_rectangleIntegral_add (hφ : IsSmoothForm I 0 φ)
    (hT : VanishesOnTori φ) {w v : ℝ × ℝ → M} {γ₀ γ₁ γ₂ : ℝ → M}
    (hwc : IsLoopCylinder I w γ₁ γ₂) (hv : IsLoopCylinder I v γ₂ γ₀) :
    referenceArea φ γ₀ γ₁ = rectangleIntegral φ w (0, 0) (1, 1) + referenceArea φ γ₀ γ₂ := by
  rw [hT.referenceArea_eq hφ (hwc.trans hv), hT.referenceArea_eq hφ hv,
    rectangleIntegral_rectangleTrans hφ (hwc.contMDiff.of_le one_le_two)
      (hv.contMDiff.of_le one_le_two) fun t ↦ (hwc.apply_one t).trans (hv.apply_zero t).symm]

/-- For a continuous form vanishing on tori, a `C²` reference loop has reference area `0` relative
to itself. -/
theorem VanishesOnTori.referenceArea_self (hφ : IsSmoothForm I 0 φ) (hT : VanishesOnTori φ)
    {γ₀ : ℝ → M} (hγ₀ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ₀) (hper : Function.Periodic γ₀ 1) :
    referenceArea φ γ₀ γ₀ = 0 := by
  rw [hT.referenceArea_eq hφ (isLoopCylinder_comp_snd hγ₀ hper)]
  exact rectangleIntegral_comp_snd φ γ₀ _ _

end Continuous

section Exact

variable [IsManifold I 2 M] {α : RoughForm I M F 1}

/-- **Exact forms vanish on tori.** -/
theorem vanishesOnTori_mextDeriv (hα : IsSmoothForm I 1 α) : VanishesOnTori (mextDeriv α) :=
  fun _ _ hw ↦ by simp [hw.rectangleIntegral_mextDeriv hα]

/-- The reference area of a loop `γ` relative to `γ₀` for an exact form `dα` is
`∫_{γ₀} α - ∫_γ α`, as soon as `γ` is joined to `γ₀` by a cylinder. -/
theorem referenceArea_mextDeriv (hα : IsSmoothForm I 1 α) {w : ℝ × ℝ → M} {γ₀ γ : ℝ → M}
    (hw : IsLoopCylinder I w γ γ₀) :
    referenceArea (mextDeriv α) γ₀ γ = pathIntegral α γ₀ 0 1 - pathIntegral α γ 0 1 := by
  have h : ∃ w, IsLoopCylinder I w γ γ₀ := ⟨w, hw⟩
  rw [referenceArea, dite_eq_left h, h.choose_spec.rectangleIntegral_mextDeriv hα]

end Exact

/-! ### The action functional relative to a reference loop -/

/-- The **Hamiltonian action** of a loop `γ` relative to the reference loop `γ₀`, for a two-form
`ω` and a time-dependent Hamiltonian `H`: `A_H(γ) = ∫ w^* ω - ∫₀¹ H(t, γ(t)) dt`, for a cylinder
`w` running from `γ` to `γ₀`. Its area term is the reference area `TauCeti.referenceArea ω γ₀ γ`,
which does not depend on the cylinder when `ω` is continuous and vanishes on tori, and is `0` for a
loop with no cylinder to `γ₀`. -/
def referenceLoopAction (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (γ₀ γ : ℝ → M) : ℝ :=
  referenceArea ω γ₀ γ - ∫ t in 0..1, H t (γ t)

theorem referenceLoopAction_def (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (γ₀ γ : ℝ → M) :
    referenceLoopAction ω H γ₀ γ = referenceArea ω γ₀ γ - ∫ t in 0..1, H t (γ t) :=
  (rfl)

section Continuous

variable [IsManifold I 1 M] {ω : RoughForm I M ℝ 2}

/-- For a continuous form vanishing on tori, the action of a loop relative to `γ₀` is computed
with any cylinder from the loop to `γ₀`. -/
theorem VanishesOnTori.referenceLoopAction_eq (hω : IsSmoothForm I 0 ω) (hT : VanishesOnTori ω)
    (H : ℝ → M → ℝ) {w : ℝ × ℝ → M} {γ₀ γ : ℝ → M} (hw : IsLoopCylinder I w γ γ₀) :
    referenceLoopAction ω H γ₀ γ =
      rectangleIntegral ω w (0, 0) (1, 1) - ∫ t in 0..1, H t (γ t) := by
  rw [referenceLoopAction_def, hT.referenceArea_eq hω hw]

/-- **The action difference along a cylinder.** For a continuous form vanishing on tori and a
cylinder `w` from `γ₁` to a loop `γ₂` joined to `γ₀` by a cylinder, the action relative to `γ₀`
decreases from `γ₁` to `γ₂` by the area of `w` minus the change of the Hamiltonian term:
`A_H(γ₁) - A_H(γ₂) = ∫ w^* ω - ∫₀¹ H(t, γ₁(t)) dt + ∫₀¹ H(t, γ₂(t)) dt`. -/
theorem VanishesOnTori.referenceLoopAction_sub (hω : IsSmoothForm I 0 ω) (hT : VanishesOnTori ω)
    (H : ℝ → M → ℝ) {w v : ℝ × ℝ → M} {γ₀ γ₁ γ₂ : ℝ → M} (hwc : IsLoopCylinder I w γ₁ γ₂)
    (hv : IsLoopCylinder I v γ₂ γ₀) :
    referenceLoopAction ω H γ₀ γ₁ - referenceLoopAction ω H γ₀ γ₂ =
      rectangleIntegral ω w (0, 0) (1, 1) - (∫ t in 0..1, H t (γ₁ t)) +
        ∫ t in 0..1, H t (γ₂ t) := by
  rw [referenceLoopAction_def, referenceLoopAction_def,
    hT.referenceArea_eq_rectangleIntegral_add hω hwc hv]
  ring

/-- For a continuous form vanishing on tori, a `C²` reference loop `γ₀` has action
`-∫₀¹ H(t, γ₀(t)) dt` relative to itself. -/
theorem VanishesOnTori.referenceLoopAction_self (hω : IsSmoothForm I 0 ω) (hT : VanishesOnTori ω)
    (H : ℝ → M → ℝ) {γ₀ : ℝ → M} (hγ₀ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ₀)
    (hper : Function.Periodic γ₀ 1) :
    referenceLoopAction ω H γ₀ γ₀ = -∫ t in 0..1, H t (γ₀ t) := by
  rw [referenceLoopAction_def, hT.referenceArea_self hω hγ₀ hper, zero_sub]

end Continuous

/-- For an exact form `ω = dθ`, the action relative to `γ₀` of a loop `γ` joined to `γ₀` by a
cylinder is `A_H(γ) = ∫_{γ₀} θ - ∫_γ θ - ∫₀¹ H(t, γ(t)) dt`. -/
theorem referenceLoopAction_mextDeriv [IsManifold I 2 M] {θ : RoughForm I M ℝ 1}
    (hθ : IsSmoothForm I 1 θ) (H : ℝ → M → ℝ) {w : ℝ × ℝ → M} {γ₀ γ : ℝ → M}
    (hw : IsLoopCylinder I w γ γ₀) :
    referenceLoopAction (mextDeriv θ) H γ₀ γ =
      pathIntegral θ γ₀ 0 1 - pathIntegral θ γ 0 1 - ∫ t in 0..1, H t (γ t) := by
  rw [referenceLoopAction_def, referenceArea_mextDeriv hθ hw]

end TauCeti
