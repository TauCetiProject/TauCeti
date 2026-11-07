/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder

/-!
# The action functional on contractible loops of a weakly exact manifold

Loops in a manifold `M` are `1`-periodic maps `γ : ℝ → M`. A **cylinder** from a loop `γ₀` to a
loop `γ₁` (`TauCeti.IsLoopCylinder`) is a `C²` map `w : ℝ × ℝ → M`, `1`-periodic in its second
coordinate `t`, with `w (0, ·) = γ₀` and `w (1, ·) = γ₁`. Cylinders compose
(`TauCeti.IsLoopCylinder.trans`, by `TauCeti.rectangleTrans`) and reverse
(`TauCeti.IsLoopCylinder.symm`), and their images under `C²` maps are cylinders
(`TauCeti.IsLoopCylinder.comp`). A **cap** of `γ` (`TauCeti.IsCap`) is a cylinder from `γ` to a
constant loop: a disc bounding `γ`, with the centre of the disc at `s = 1`. A cylinder between two
constant loops is a **sphere**.

The integral `∫ w^* φ` of a two-form `φ` over a cylinder is `TauCeti.rectangleIntegral φ w (0, 0)
(1, 1)`, oriented by the coordinates `(s, t)`. The form `φ` is **weakly exact**
(`TauCeti.IsWeaklyExact`) when its integral over every sphere vanishes. Gluing two caps of the
same loop along the loop gives a sphere, so for a continuous weakly exact form all caps of a loop
have the same integral (`TauCeti.IsWeaklyExact.rectangleIntegral_eq_of_isCap`). This common value
is the **cap area** `TauCeti.capArea φ γ`, and gluing a cylinder to a cap shows that the cap areas
of two loops joined by a cylinder `w` differ by `∫ w^* φ`
(`TauCeti.IsWeaklyExact.capArea_eq_rectangleIntegral_add`). Exact forms are weakly exact
(`TauCeti.isWeaklyExact_mextDeriv`), by Green's formula, and the cap area of `γ` for `dα` is
`-∫_γ α` (`TauCeti.capArea_mextDeriv`). Weak exactness is natural: its pullback along a `C²` map
is weakly exact (`TauCeti.IsWeaklyExact.mpullback`).

For a weakly exact two-form `ω` and a time-dependent Hamiltonian `H : ℝ → M → ℝ`, the **action**
of a loop `γ` admitting a cap `u` is

`A_H(γ) = ∫ u^* ω - ∫₀¹ H(t, γ(t)) dt`

(`TauCeti.contractibleLoopAction`), with `u` running from `γ` to the constant loop. It does not
depend on the cap (`TauCeti.IsWeaklyExact.contractibleLoopAction_eq`), and along a cylinder `w`
from `γ₀` to `γ₁` it changes by the area of `w` and the Hamiltonian terms
(`TauCeti.IsWeaklyExact.contractibleLoopAction_sub`); this is how the energy of a Floer cylinder
is identified with the action difference of its ends. A constant loop at `x` has cap area `0` and
action `-∫₀¹ H(t, x) dt` (`TauCeti.IsWeaklyExact.contractibleLoopAction_const`). For an exact
form `ω = dλ` it is `A_H(γ) = -∫_γ λ - ∫₀¹ H(t, γ(t)) dt`
(`TauCeti.contractibleLoopAction_mextDeriv`). These signs
are chosen so that, with the convention `ι_{X_H} ω = dH` for Hamiltonian vector fields, the first
variation of the action is `dA_H(γ) ξ = ∫₀¹ ω(γ' - X_H(γ), ξ) dt`, whose zeros for a
nondegenerate `ω` are the `1`-periodic orbits of `X_H`. This formula is
`TauCeti.SmoothTwoForm.hasDerivAt_contractibleLoopAction_of_isHamiltonianVectorField`, and that
the `1`-periodic orbits are critical points is
`TauCeti.SmoothTwoForm.hasDerivAt_contractibleLoopAction_of_mem_periodicSolutions`, both in
`TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.FirstVariation`.

Weak exactness is the area half of symplectic asphericity, which also asks the first Chern class
to vanish on spheres; the area condition alone is what the action functional needs. The spheres
here are `C²` maps of the square collapsing the sides `s = 0` and `s = 1` to points and identifying
`t = 0` with `t = 1`; every smooth map from the round sphere gives such a map by composing with a
smooth degree-one map of the square onto the sphere. Similarly a loop is in the domain of the
action exactly when it has a `C²` cap.

## Main definitions

* `TauCeti.IsLoopCylinder`: a `C²` cylinder between two loops.
* `TauCeti.IsCap`: a `C²` cap of a loop.
* `TauCeti.IsWeaklyExact`: a two-form whose integral over every sphere vanishes.
* `TauCeti.capArea`: the integral of a two-form over a cap of a loop.
* `TauCeti.contractibleLoopAction`: the Hamiltonian action of a capped loop.

## Main results

* `TauCeti.IsWeaklyExact.rectangleIntegral_eq_of_isCap`: for a weakly exact form, all caps of a
  loop have the same area.
* `TauCeti.IsWeaklyExact.capArea_eq_rectangleIntegral_add`: the cap areas of the two ends of a
  cylinder differ by the area of the cylinder.
* `TauCeti.isWeaklyExact_mextDeriv`, `TauCeti.capArea_mextDeriv`: exact forms are weakly exact,
  and the cap area for `dα` is minus the line integral of `α`.
* `TauCeti.IsWeaklyExact.mpullback`: the pullback of a weakly exact form is weakly exact.
* `TauCeti.IsWeaklyExact.contractibleLoopAction_sub`: the action difference along a cylinder.

## References

* H. Hofer and E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (the action functional on loops and its critical points).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (the symplectic action of contractible loops).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the symplectic action of contractible loops, with the sign
  convention used here).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
-/

public section

noncomputable section

open scoped Manifold Interval Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Cylinders and caps -/

variable (I) in
/-- A **cylinder** from the loop `γ₀` to the loop `γ₁`: a `C²` map `w : ℝ × ℝ → M` that is
`1`-periodic in its second coordinate, with `w (0, ·) = γ₀` and `w (1, ·) = γ₁`. -/
structure IsLoopCylinder (w : ℝ × ℝ → M) (γ₀ γ₁ : ℝ → M) : Prop where
  /-- A cylinder is `C²`. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w
  /-- A cylinder is `1`-periodic in its second coordinate. -/
  apply_add_one : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z
  /-- A cylinder starts at `γ₀`. -/
  apply_zero : ∀ t, w (0, t) = γ₀ t
  /-- A cylinder ends at `γ₁`. -/
  apply_one : ∀ t, w (1, t) = γ₁ t

variable (I) in
/-- A **cap** of the loop `γ`: a cylinder from `γ` to a constant loop, that is a disc bounding
`γ` with its centre at `s = 1`. -/
def IsCap (u : ℝ × ℝ → M) (γ : ℝ → M) : Prop :=
  ∃ x, IsLoopCylinder I u γ fun _ ↦ x

theorem isCap_iff {u : ℝ × ℝ → M} {γ : ℝ → M} :
    IsCap I u γ ↔ ∃ x, IsLoopCylinder I u γ fun _ ↦ x :=
  Iff.rfl

/-- The constant map at `x` is a cylinder from the constant loop at `x` to itself. -/
theorem isLoopCylinder_const (x : M) :
    IsLoopCylinder I (fun _ ↦ x) (fun _ ↦ x) (fun _ ↦ x) where
  contMDiff := contMDiff_const
  apply_add_one _ := rfl
  apply_zero _ := rfl
  apply_one _ := rfl

namespace IsLoopCylinder

variable {w w₁ w₂ : ℝ × ℝ → M} {γ₀ γ₁ γ₂ : ℝ → M}

/-- A cylinder ending at a constant loop is a cap of its initial loop. -/
theorem isCap {x : M} (hw : IsLoopCylinder I w γ₀ fun _ ↦ x) : IsCap I w γ₀ :=
  ⟨x, hw⟩

/-- The concatenation of a cylinder from `γ₀` to `γ₁` and a cylinder from `γ₁` to `γ₂` is a
cylinder from `γ₀` to `γ₂`. -/
theorem trans (hw₁ : IsLoopCylinder I w₁ γ₀ γ₁) (hw₂ : IsLoopCylinder I w₂ γ₁ γ₂) :
    IsLoopCylinder I (rectangleTrans w₁ w₂) γ₀ γ₂ where
  contMDiff := contMDiff_rectangleTrans (n := 2) hw₁.contMDiff hw₂.contMDiff
    fun t ↦ (hw₁.apply_one t).trans (hw₂.apply_zero t).symm
  apply_add_one := rectangleTrans_apply_add_snd hw₁.apply_add_one hw₂.apply_add_one
  apply_zero t := by rw [rectangleTrans_apply_zero, hw₁.apply_zero]
  apply_one t := by rw [rectangleTrans_apply_one, hw₂.apply_one]

/-- Reversing the first coordinate of a cylinder from `γ₀` to `γ₁` gives a cylinder from `γ₁` to
`γ₀`. -/
theorem symm (hw : IsLoopCylinder I w γ₀ γ₁) :
    IsLoopCylinder I (w ∘ Prod.map (fun s ↦ 1 - s) id) γ₁ γ₀ where
  contMDiff := hw.contMDiff.comp ((contDiff_const.sub contDiff_id).prodMap contDiff_id).contMDiff
  apply_add_one z := hw.apply_add_one (1 - z.1, z.2)
  apply_zero t := by simp [hw.apply_one]
  apply_one t := by simp [hw.apply_zero]

/-- The image of a cylinder from `γ₀` to `γ₁` under a `C²` map `f` is a cylinder from `f ∘ γ₀` to
`f ∘ γ₁`. -/
theorem comp {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    (hw : IsLoopCylinder I w γ₀ γ₁) {f : M → M'} (hf : ContMDiff I I' 2 f) :
    IsLoopCylinder I' (f ∘ w) (f ∘ γ₀) (f ∘ γ₁) where
  contMDiff := hf.comp hw.contMDiff
  apply_add_one z := congrArg f (hw.apply_add_one z)
  apply_zero t := congrArg f (hw.apply_zero t)
  apply_one t := congrArg f (hw.apply_one t)

end IsLoopCylinder

/-! ### Weakly exact forms and the cap area -/

/-- A two-form is **weakly exact** when its integral over every sphere, a cylinder between two
constant loops, vanishes. For a symplectic form this is the condition that `ω` vanishes on
`π₂(M)`, the area half of symplectic asphericity. -/
def IsWeaklyExact (φ : RoughForm I M F 2) : Prop :=
  ∀ ⦃w : ℝ × ℝ → M⦄ ⦃x y : M⦄, IsLoopCylinder I w (fun _ ↦ x) (fun _ ↦ y) →
    rectangleIntegral φ w (0, 0) (1, 1) = 0

theorem isWeaklyExact_iff {φ : RoughForm I M F 2} :
    IsWeaklyExact φ ↔ ∀ ⦃w : ℝ × ℝ → M⦄ ⦃x y : M⦄,
      IsLoopCylinder I w (fun _ ↦ x) (fun _ ↦ y) → rectangleIntegral φ w (0, 0) (1, 1) = 0 :=
  Iff.rfl

/-- **Weak exactness is natural**: the pullback of a weakly exact form along a `C²` map is weakly
exact, since the image of a sphere is a sphere. -/
theorem IsWeaklyExact.mpullback {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] {φ : RoughForm I' M' F 2} (hφ : IsWeaklyExact φ) {f : M → M'}
    (hf : ContMDiff I I' 2 f) : IsWeaklyExact (TauCeti.mpullback I I' f φ) := by
  intro w x y hw
  rw [rectangleIntegral_mpullback φ (fun z _ ↦ hf.mdifferentiable two_ne_zero (w z))
    (fun z _ ↦ hw.contMDiff.mdifferentiable two_ne_zero z)]
  exact hφ (hw.comp hf)

open Classical in
/-- The **cap area** of a loop `γ` for a two-form `φ`: the integral of `φ` over a cap of `γ`,
oriented from `γ` to the centre of the cap, or `0` when `γ` has no cap. For a continuous weakly
exact form it does not depend on the choice of cap
(`TauCeti.IsWeaklyExact.capArea_eq`). -/
def capArea (φ : RoughForm I M F 2) (γ : ℝ → M) : F :=
  if h : ∃ u, IsCap I u γ then rectangleIntegral φ h.choose (0, 0) (1, 1) else 0

/-- The cap area of a loop without a cap is `0`. -/
theorem capArea_of_not_exists_isCap {φ : RoughForm I M F 2} {γ : ℝ → M}
    (h : ¬∃ u, IsCap I u γ) : capArea φ γ = 0 :=
  dite_eq_right h

section Continuous

variable [IsManifold I 1 M] {φ : RoughForm I M F 2}

/-- **Independence of the cap.** For a continuous weakly exact form, any two caps of the same loop
have the same integral: gluing them along the loop gives a sphere. -/
theorem IsWeaklyExact.rectangleIntegral_eq_of_isCap (hφ : IsSmoothForm I 0 φ)
    (hw : IsWeaklyExact φ) {u v : ℝ × ℝ → M} {γ : ℝ → M} (hu : IsCap I u γ)
    (hv : IsCap I v γ) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) := by
  obtain ⟨x, hu⟩ := hu
  obtain ⟨y, hv⟩ := hv
  have hsphere := hw (hu.symm.trans hv)
  rw [rectangleIntegral_rectangleTrans hφ (hu.symm.contMDiff.of_le one_le_two)
      (hv.contMDiff.of_le one_le_two)
      (fun t ↦ (hu.symm.apply_one t).trans (hv.apply_zero t).symm),
    rectangleIntegral_comp_prodMap_one_sub hφ (hu.contMDiff.of_le one_le_two)] at hsphere
  exact (neg_add_eq_zero.mp hsphere)

/-- For a continuous weakly exact form, the cap area of a loop is the integral over any of its
caps. -/
theorem IsWeaklyExact.capArea_eq (hφ : IsSmoothForm I 0 φ) (hw : IsWeaklyExact φ)
    {u : ℝ × ℝ → M} {γ : ℝ → M} (hu : IsCap I u γ) :
    capArea φ γ = rectangleIntegral φ u (0, 0) (1, 1) := by
  have h : ∃ u, IsCap I u γ := ⟨u, hu⟩
  rw [capArea, dite_eq_left h]
  exact hw.rectangleIntegral_eq_of_isCap hφ h.choose_spec hu

/-- **The cap area along a cylinder.** For a continuous weakly exact form and a cylinder `w` from
`γ₀` to a loop `γ₁` with a cap, the cap area of `γ₀` is the area of `w` plus the cap area of `γ₁`.
The loop `γ₀` has a cap, obtained by gluing `w` to a cap of `γ₁` (`TauCeti.IsLoopCylinder.trans`).
-/
theorem IsWeaklyExact.capArea_eq_rectangleIntegral_add (hφ : IsSmoothForm I 0 φ)
    (hw : IsWeaklyExact φ) {w v : ℝ × ℝ → M} {γ₀ γ₁ : ℝ → M} (hwc : IsLoopCylinder I w γ₀ γ₁)
    (hv : IsCap I v γ₁) :
    capArea φ γ₀ = rectangleIntegral φ w (0, 0) (1, 1) + capArea φ γ₁ := by
  obtain ⟨x, hv'⟩ := hv
  rw [hw.capArea_eq hφ (hwc.trans hv').isCap, hw.capArea_eq hφ hv'.isCap,
    rectangleIntegral_rectangleTrans hφ (hwc.contMDiff.of_le one_le_two)
      (hv'.contMDiff.of_le one_le_two) fun t ↦ (hwc.apply_one t).trans (hv'.apply_zero t).symm]

/-- For a continuous weakly exact form, a constant loop has cap area `0`: the constant map is a
cap of it. -/
@[simp]
theorem IsWeaklyExact.capArea_const (hφ : IsSmoothForm I 0 φ) (hw : IsWeaklyExact φ) (x : M) :
    capArea φ (fun _ ↦ x) = 0 := by
  rw [hw.capArea_eq hφ (isLoopCylinder_const x).isCap]
  exact rectangleIntegral_comp_fst φ (fun _ ↦ x) _ _

end Continuous

section Exact

variable [IsManifold I 2 M] {α : RoughForm I M F 1}

/-- The integral of an exact form `dα` over a cylinder from `γ₀` to `γ₁` is the difference of the
line integrals of `α` along `γ₁` and `γ₀`, by Green's formula: the contributions of the two sides
`t = 0` and `t = 1` cancel by periodicity. -/
theorem IsLoopCylinder.rectangleIntegral_mextDeriv (hα : IsSmoothForm I 1 α)
    {w : ℝ × ℝ → M} {γ₀ γ₁ : ℝ → M} (hw : IsLoopCylinder I w γ₀ γ₁) :
    rectangleIntegral (mextDeriv α) w (0, 0) (1, 1) =
      pathIntegral α γ₁ 0 1 - pathIntegral α γ₀ 0 1 := by
  have hper : (fun s ↦ w (s, 1)) = fun s ↦ w (s, 0) :=
    funext fun s ↦ by simpa using hw.apply_add_one (s, 0)
  have h₀ : (fun t ↦ w (0, t)) = γ₀ := funext hw.apply_zero
  have h₁ : (fun t ↦ w (1, t)) = γ₁ := funext hw.apply_one
  rw [TauCeti.rectangleIntegral_mextDeriv hα hw.contMDiff, hper, h₀, h₁, sub_self, sub_zero]

/-- **Exact forms are weakly exact.** -/
theorem isWeaklyExact_mextDeriv (hα : IsSmoothForm I 1 α) : IsWeaklyExact (mextDeriv α) :=
  fun _ _ _ hw ↦ by simp [hw.rectangleIntegral_mextDeriv hα]

/-- The cap area of a loop `γ` for an exact form `dα` is minus the line integral of `α` along
`γ`, as soon as `γ` has a cap. -/
theorem capArea_mextDeriv (hα : IsSmoothForm I 1 α) {u : ℝ × ℝ → M} {γ : ℝ → M}
    (hu : IsCap I u γ) : capArea (mextDeriv α) γ = -pathIntegral α γ 0 1 := by
  have h : ∃ u, IsCap I u γ := ⟨u, hu⟩
  obtain ⟨x, hx⟩ := h.choose_spec
  rw [capArea, dite_eq_left h, hx.rectangleIntegral_mextDeriv hα, pathIntegral_const_curve,
    zero_sub]

end Exact

/-! ### The action functional -/

/-- The **Hamiltonian action** of a loop `γ` with a cap `u`, for a two-form `ω` and a
time-dependent Hamiltonian `H`:
`A_H(γ) = ∫ u^* ω - ∫₀¹ H(t, γ(t)) dt`, the cap running from `γ` to its centre. Its area term is
the cap area `TauCeti.capArea ω γ`, which does not depend on the cap when `ω` is continuous and
weakly exact, and is `0` for a loop without a cap. -/
def contractibleLoopAction (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (γ : ℝ → M) : ℝ :=
  capArea ω γ - ∫ t in 0..1, H t (γ t)

theorem contractibleLoopAction_def (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ) (γ : ℝ → M) :
    contractibleLoopAction ω H γ = capArea ω γ - ∫ t in 0..1, H t (γ t) :=
  (rfl)

section Continuous

variable [IsManifold I 1 M] {ω : RoughForm I M ℝ 2}

/-- For a continuous weakly exact form, the action of a loop is computed with any of its caps. -/
theorem IsWeaklyExact.contractibleLoopAction_eq (hω : IsSmoothForm I 0 ω) (hw : IsWeaklyExact ω)
    (H : ℝ → M → ℝ) {u : ℝ × ℝ → M} {γ : ℝ → M} (hu : IsCap I u γ) :
    contractibleLoopAction ω H γ =
      rectangleIntegral ω u (0, 0) (1, 1) - ∫ t in 0..1, H t (γ t) := by
  rw [contractibleLoopAction_def, hw.capArea_eq hω hu]

/-- **The action difference along a cylinder.** For a continuous weakly exact form and a cylinder
`w` from `γ₀` to a loop `γ₁` with a cap, the action decreases from `γ₀` to `γ₁` by the area of `w`
minus the change of the Hamiltonian term:
`A_H(γ₀) - A_H(γ₁) = ∫ w^* ω - ∫₀¹ H(t, γ₀(t)) dt + ∫₀¹ H(t, γ₁(t)) dt`. -/
theorem IsWeaklyExact.contractibleLoopAction_sub (hω : IsSmoothForm I 0 ω) (hw : IsWeaklyExact ω)
    (H : ℝ → M → ℝ) {w v : ℝ × ℝ → M} {γ₀ γ₁ : ℝ → M} (hwc : IsLoopCylinder I w γ₀ γ₁)
    (hv : IsCap I v γ₁) :
    contractibleLoopAction ω H γ₀ - contractibleLoopAction ω H γ₁ =
      rectangleIntegral ω w (0, 0) (1, 1) - (∫ t in 0..1, H t (γ₀ t)) +
        ∫ t in 0..1, H t (γ₁ t) := by
  rw [contractibleLoopAction_def, contractibleLoopAction_def,
    hw.capArea_eq_rectangleIntegral_add hω hwc hv]
  ring

/-- For a continuous weakly exact form, the action of the constant loop at `x` is
`-∫₀¹ H(t, x) dt`. -/
@[simp]
theorem IsWeaklyExact.contractibleLoopAction_const (hω : IsSmoothForm I 0 ω)
    (hw : IsWeaklyExact ω) (H : ℝ → M → ℝ) (x : M) :
    contractibleLoopAction ω H (fun _ ↦ x) = -∫ t in 0..1, H t x := by
  rw [contractibleLoopAction_def, hw.capArea_const hω, zero_sub]

end Continuous

/-- For an exact form `ω = dθ`, the action of a loop `γ` with a cap is
`A_H(γ) = -∫_γ θ - ∫₀¹ H(t, γ(t)) dt`. -/
theorem contractibleLoopAction_mextDeriv [IsManifold I 2 M] {θ : RoughForm I M ℝ 1}
    (hθ : IsSmoothForm I 1 θ) (H : ℝ → M → ℝ) {u : ℝ × ℝ → M} {γ : ℝ → M} (hu : IsCap I u γ) :
    contractibleLoopAction (mextDeriv θ) H γ = -pathIntegral θ γ 0 1 - ∫ t in 0..1, H t (γ t) := by
  rw [contractibleLoopAction_def, capArea_mextDeriv hθ hu]

end TauCeti
