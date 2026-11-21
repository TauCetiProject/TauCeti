/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Disc
public import TauCeti.Geometry.Symplectic.Floer.Cap.Area
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped

/-!
# The capped action of raw caps and cap classes

Let `M` be a compact boundaryless manifold with a closed `C¹` two-form `ω`, such as a closed
symplectic manifold, and let `γ` be a loop based at `x`. The capped action
`A_H(γ, D) = ∫ D^* ω + ∫₀¹ H(t, γ(t)) dt` of `TauCeti.cappedLoopAction` is defined for a
differentiable disc `D` bounding `γ`, while the cap API of capped Floer theory works with raw caps
(`TauCeti.Floer.RawCap γ`): homotopy classes of continuous discs relative to their boundary,
which form a torsor under `π₂(M, x)`. This file shows that the capped action is a function of the
raw cap, with the recapping law given by the actual integral `TauCeti.sphereIntegral` of `ω` over
`π₂(M, x)`.

A smooth disc `D` bounding `γ` (`TauCeti.IsSmoothDisc`) has a raw cap
`TauCeti.IsSmoothDisc.rawCap`, its class as a path in the loop space from `γ` to the constant loop.
For two smooth discs `D` and `D'` of `γ`, the sphere `D'.rawCap -ᵥ D.rawCap ∈ π₂(M, x)` by which
their raw caps differ is the class of the double loop that runs from the centre of `D` to `γ` and
back to the centre of `D'`, so by
`TauCeti.IsSmoothDisc.sphereIntegral_loopPath_symm_trans`

`A_H(γ, D') - A_H(γ, D) = -∫_{D'.rawCap -ᵥ D.rawCap} ω`

(`TauCeti.IsSmoothDisc.cappedLoopAction_sub_cappedLoopAction_eq_neg_sphereIntegral`). In
particular smooth discs with the same raw cap have the same action. The sign is that of the
orientation conventions: a raw cap runs from the loop to its centre, the reverse of the disc of the
capped action, which runs from its centre to the loop. So gluing a sphere `a` at the centre of the
raw cap glues the sphere `a` run backwards in front of the disc, and changes the action by
`-∫_a ω`.

Consequently, once `γ` bounds one smooth disc `D₀`, the capped action for a closed `C¹` form `ω`
descends to a function on all raw caps of `γ`, `TauCeti.IsSmoothDisc.rawCapAction`: it is
`A_H(γ, D)` on the raw cap of every smooth disc `D` (`TauCeti.IsSmoothDisc.rawCapAction_rawCap`),
it obeys the recapping law `A(a +ᵥ P) = A(P) - ∫_a ω` (`TauCeti.IsSmoothDisc.rawCapAction_vadd`),
and it does not depend on the reference disc `D₀`
(`TauCeti.IsSmoothDisc.rawCapAction_eq_rawCapAction`). That every raw cap of a smooth loop is the
raw cap of a smooth disc is not treated here.

The same action is also defined directly on the raw caps of a loop `γ : Ω M x` that has a smooth
based cap (`TauCeti.Floer.IsSmoothBasedCap`), through the area of raw caps
(`TauCeti.Floer.RawCap.area`) and with a two-form `σ`, and it descends to the cap classes
`TauCeti.Floer.SphericalCapClass ω c γ` of capped Hamiltonian Floer theory.

* **The action of a raw cap.** A raw cap `D` is oriented from `γ` to its centre, so the area term
  of the capped action is minus its area (`TauCeti.Floer.RawCap.area`), and
  `RawCap.action σ Ham h D = -RawCap.area σ h D + ∫₀¹ Ham(t, γ(t)) dt`. On the raw cap of a smooth
  based cap `u` it is the capped action of `γ` with the disc `u` run backwards
  (`TauCeti.Floer.RawCap.action_homotopyClass`).
* **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap, with the orientation of the
  cap, lowers the action by the integral of `σ` over `a`
  (`TauCeti.Floer.RawCap.action_vadd`), and two raw caps have actions differing by minus the
  integral over the sphere by which they differ (`TauCeti.Floer.RawCap.action_sub_action`). When
  `σ` vanishes on spheres the action does not depend on the cap
  (`TauCeti.Floer.RawCap.action_eq_action_of_vanishesOnSpheres`).
* **Descent to cap classes.** Let `ω` and `c` be homomorphisms on `H₂(M; ℤ)` defining the period
  group `Γ = SphericalPeriodGroup ω c`, and suppose that `ω` is the integral of `σ` on spherical
  classes: `ω` of the Hurewicz class of every sphere `a` is `∫_a σ`. Then the action descends to the
  cap classes of `γ` (`TauCeti.Floer.SphericalCapClass.action`), and recapping a cap class by a
  class `B ∈ Γ` lowers its action by the area of `B`
  (`TauCeti.Floer.SphericalCapClass.action_vadd`). So the cap classes of finitely many orbits,
  with their actions, are generators with an equivariant potential for the periods
  `PeriodGroup.area`, in the sense of `TauCeti.NovikovModule`. When the area is injective on `Γ`,
  for instance when `c` vanishes on spherical classes, a cap class is determined by its action
  (`TauCeti.Floer.SphericalCapClass.action_injective`).

The sign in the recapping law comes from the orientation of the torsor of raw caps:
`a +ᵥ D` glues `a` with the orientation of the cap, from `γ` to its centre, while the capped action
measures the disc from its centre to `γ`. With the orientation of the disc, gluing a sphere `B` to
`D` is `(-B) +ᵥ D`, and the law reads `A_H(γ, B # D) = ω(B) + A_H(γ, D)`.

That the integral of a closed form over spheres factors through their Hurewicz classes in
`H₂(M; ℤ)` is not proved here: the descent takes a homomorphism `ω` on `H₂(M; ℤ)` together with
its agreement with the sphere integral `TauCeti.sphereIntegralHom`.

## Main definitions

* `TauCeti.IsSmoothDisc.isLoopCylinder`: a smooth disc is a disc of the capped action.
* `TauCeti.IsSmoothDisc.cappedLoopAction_apply_one`: the capped action of a disc may use the
  boundary loop `t ↦ D (1, t)` of a smooth disc `D` of `γ` in place of `γ`.
* `TauCeti.IsSmoothDisc.rawCap`: the raw cap of a smooth disc.
* `TauCeti.IsSmoothDisc.rawCapAction`: the capped action as a function on raw caps.
* `TauCeti.Floer.RawCap.action`: the capped action of a loop with a raw cap.
* `TauCeti.Floer.SphericalCapClass.action`: the capped action of a loop with a cap class.

## Main results

* `TauCeti.IsSmoothDisc.sphereIntegral_rawCap_vsub_rawCap`: the integral of a closed form over
  the sphere by which the raw caps of two smooth discs differ.
* `TauCeti.IsSmoothDisc.cappedLoopAction_sub_cappedLoopAction_eq_neg_sphereIntegral`: the change
  of the capped action between two smooth discs is minus the area of that sphere.
* `TauCeti.IsSmoothDisc.cappedLoopAction_eq_of_rawCap_eq`: the capped action only depends on the
  raw cap.
* `TauCeti.IsSmoothDisc.rawCapAction_rawCap`, `TauCeti.IsSmoothDisc.rawCapAction_vadd`,
  `TauCeti.IsSmoothDisc.rawCapAction_eq_rawCapAction`: the descended action and its recapping law.
* `TauCeti.Floer.RawCap.action_homotopyClass`: the action of a smooth cap is the capped action.
* `TauCeti.Floer.RawCap.action_vadd`, `TauCeti.Floer.SphericalCapClass.action_vadd`: the
  recapping laws.
* `TauCeti.Floer.SphericalCapClass.action_sub_action`: two cap classes have actions differing by
  minus the area of the class by which they differ.
* `TauCeti.Floer.SphericalCapClass.action_injective`: when the area is injective on the period
  group, a cap class is determined by its action.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops and its recapping law.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and capped loops).
-/

public section

noncomputable section

open CategoryTheory HomotopyGroup
open scoped Manifold Topology Topology.Homotopy

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {x : M}
  {γ : Path x x} {D D' : ℝ × ℝ → M}

namespace IsSmoothDisc

/-- A smooth disc is a disc in the sense of the capped action: a `C²` cylinder from the constant
loop at its centre to its loop `t ↦ D (1, t)` along `s = 1`. -/
theorem isLoopCylinder (hD : IsSmoothDisc I γ D) :
    IsLoopCylinder I D (fun _ ↦ x) fun t ↦ D (1, t) where
  contMDiff := hD.contMDiff.of_le (by simp)
  apply_add_one := hD.apply_add_one
  apply_zero := hD.apply_zero_eq
  apply_one _ := rfl

/-- The capped action of a disc `D'` computed with the boundary loop `t ↦ D (1, t)` of a smooth
disc `D` of `γ`, as in `TauCeti.IsSmoothDisc.isLoopCylinder`, is the one computed with `γ`. -/
theorem cappedLoopAction_apply_one (hD : IsSmoothDisc I γ D) (ω : RoughForm I M ℝ 2)
    (H : ℝ → M → ℝ) (D' : ℝ × ℝ → M) :
    cappedLoopAction ω H (fun t ↦ D (1, t)) D' = cappedLoopAction ω H γ.extend D' :=
  cappedLoopAction_congr_loop ω H (fun t ht ↦ by
    simpa [Path.extend_apply _ ht] using hD.apply_one ⟨t, ht⟩) D'

/-- The **raw cap of a smooth disc**: the homotopy class of the disc, read as a path in the loop
space from the loop `γ` it bounds to the constant loop at its centre (`IsSmoothDisc.loopPath`). -/
def rawCap (hD : IsSmoothDisc I γ D) : Floer.RawCap γ :=
  Path.Homotopic.Quotient.mk hD.loopPath

theorem rawCap_def (hD : IsSmoothDisc I γ D) :
    hD.rawCap = Path.Homotopic.Quotient.mk hD.loopPath :=
  (rfl)

/-- For smooth discs `D` and `D'` of `γ`, the sphere `D'.rawCap -ᵥ D.rawCap` by which their raw
caps differ is the class of the double loop `D⁻¹ ⬝ D'`, which runs from the centre of `D` to `γ`
and back to the centre of `D'`. -/
theorem rawCap_vsub_rawCap (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') :
    hD'.rawCap -ᵥ hD.rawCap = Additive.ofMul (fundamentalGroupLoopSpaceMulEquiv
      (FundamentalGroup.fromPath (.mk (hD.loopPath.symm.trans hD'.loopPath)))) := by
  rw [Floer.RawCap.vsub_def]
  refine congrArg (fun g ↦ Additive.ofMul (fundamentalGroupLoopSpaceMulEquiv g)) (End.ext ?_)
  rw [End.sdiv_asHom, IsIso.inv_comp_eq, rawCap_def, rawCap_def, FundamentalGroupoid.comp_eq]
  -- `FundamentalGroup.fromPath p` is the endomorphism `End.of p`, with underlying morphism `p`.
  dsimp only [FundamentalGroup.fromPath, FundamentalGroup.fromArrow]
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M]
  [T2Space M]

/-- **The area of the sphere between the raw caps of two discs.** For a closed `C¹` two-form `φ`
and smooth discs `D`, `D'` bounding the same loop, the integral of `φ` over the sphere
`D'.rawCap -ᵥ D.rawCap` is the integral of `φ` over `D` minus its integral over `D'`. -/
theorem sphereIntegral_rawCap_vsub_rawCap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') :
    sphereIntegral φ x (hD'.rawCap -ᵥ hD.rawCap).toMul =
      rectangleIntegral φ D (0, 0) (1, 1) - rectangleIntegral φ D' (0, 0) (1, 1) := by
  rw [rawCap_vsub_rawCap, toMul_ofMul, sphereIntegral_loopPath_symm_trans hφ hdφ hD hD']

variable {ω : RoughForm I M ℝ 2}

/-- **Two smooth discs give capped actions differing by the area of a sphere.** For a closed `C¹`
two-form `ω` and smooth discs `D` and `D'` bounding the same loop, `A_H(γ, D') - A_H(γ, D)` is
minus the integral of `ω` over the sphere `D'.rawCap -ᵥ D.rawCap` by which their raw caps differ.
The loop `ℓ` in the Hamiltonian term is arbitrary, since that term is the same for both discs. -/
theorem cappedLoopAction_sub_cappedLoopAction_eq_neg_sphereIntegral (hω : IsSmoothForm I 1 ω)
    (hdω : mextDeriv ω = 0) (H : ℝ → M → ℝ) (ℓ : ℝ → M) (hD : IsSmoothDisc I γ D)
    (hD' : IsSmoothDisc I γ D') :
    cappedLoopAction ω H ℓ D' - cappedLoopAction ω H ℓ D =
      -sphereIntegral ω x (hD'.rawCap -ᵥ hD.rawCap).toMul := by
  rw [sphereIntegral_rawCap_vsub_rawCap hω hdω hD hD', cappedLoopAction_def,
    cappedLoopAction_def]
  ring

/-- **The capped action only depends on the raw cap.** For a closed `C¹` two-form `ω`, two smooth
discs bounding the same loop with the same raw cap have the same capped action. -/
theorem cappedLoopAction_eq_of_rawCap_eq (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (H : ℝ → M → ℝ) (ℓ : ℝ → M) (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D')
    (h : hD.rawCap = hD'.rawCap) : cappedLoopAction ω H ℓ D = cappedLoopAction ω H ℓ D' := by
  have : Nonempty (Floer.RawCap γ) := ⟨hD.rawCap⟩
  have := cappedLoopAction_sub_cappedLoopAction_eq_neg_sphereIntegral hω hdω H ℓ hD hD'
  rw [h, vsub_self, toMul_zero, sphereIntegral_one hω hdω, neg_zero, sub_eq_zero] at this
  exact this.symm

variable {D₀ D₁ : ℝ × ℝ → M}

/-- The **capped action on raw caps** of a loop `γ` that bounds a smooth disc `D₀`:
`A(P) = A_H(γ, D₀) - ∫_{P -ᵥ D₀.rawCap} ω` for a raw cap `P` of `γ`. When `ω` is a closed `C¹`
two-form, it is `A_H(γ, D)` on the raw cap of every smooth disc `D`
(`TauCeti.IsSmoothDisc.rawCapAction_rawCap`), and it does not depend on `D₀`
(`TauCeti.IsSmoothDisc.rawCapAction_eq_rawCapAction`). -/
def rawCapAction (hD₀ : IsSmoothDisc I γ D₀) (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ)
    (P : Floer.RawCap γ) : ℝ :=
  cappedLoopAction ω H γ.extend D₀ - sphereIntegral ω x (P -ᵥ hD₀.rawCap).toMul

theorem rawCapAction_def (hD₀ : IsSmoothDisc I γ D₀) (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ)
    (P : Floer.RawCap γ) :
    hD₀.rawCapAction ω H P =
      cappedLoopAction ω H γ.extend D₀ - sphereIntegral ω x (P -ᵥ hD₀.rawCap).toMul :=
  (rfl)

/-- For a closed `C¹` two-form `ω`, the capped action on the raw cap of a smooth disc `D` is
`A_H(γ, D)`. -/
@[simp]
theorem rawCapAction_rawCap (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (hD₀ : IsSmoothDisc I γ D₀) (H : ℝ → M → ℝ) (hD : IsSmoothDisc I γ D) :
    hD₀.rawCapAction ω H hD.rawCap = cappedLoopAction ω H γ.extend D := by
  have := cappedLoopAction_sub_cappedLoopAction_eq_neg_sphereIntegral hω hdω H γ.extend hD₀ hD
  rw [rawCapAction_def]
  linarith

/-- **The recapping law.** For a closed `C¹` two-form `ω`, gluing a sphere `a ∈ π₂(M, x)` at the
centre of a raw cap changes the capped action by minus the integral of `ω` over `a`. -/
theorem rawCapAction_vadd (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (hD₀ : IsSmoothDisc I γ D₀) (H : ℝ → M → ℝ) (a : Additive (π_ 2 M x))
    (P : Floer.RawCap γ) :
    hD₀.rawCapAction ω H (a +ᵥ P) = hD₀.rawCapAction ω H P - sphereIntegral ω x a.toMul := by
  have : Nonempty (Floer.RawCap γ) := ⟨P⟩
  have h := (sphereIntegralHom x hω hdω).map_add a (P -ᵥ hD₀.rawCap)
  simp only [sphereIntegralHom_apply] at h
  rw [rawCapAction_def, rawCapAction_def, vadd_vsub_assoc, h]
  ring

/-- For a closed `C¹` two-form `ω`, the capped action on raw caps does not depend on the
reference disc. -/
theorem rawCapAction_eq_rawCapAction (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (hD₀ : IsSmoothDisc I γ D₀) (hD₁ : IsSmoothDisc I γ D₁) (H : ℝ → M → ℝ) :
    hD₀.rawCapAction ω H = hD₁.rawCapAction ω H := by
  have : Nonempty (Floer.RawCap γ) := ⟨hD₀.rawCap⟩
  funext P
  rw [← vsub_vadd P hD₁.rawCap, rawCapAction_vadd hω hdω, rawCapAction_vadd hω hdω,
    rawCapAction_rawCap hω hdω, rawCapAction_rawCap hω hdω]

end IsSmoothDisc

end TauCeti

section CapClass

open Set

namespace TauCeti.Floer

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [FiniteDimensional ℝ E] [I.Boundaryless]

/-! ### The action of a raw cap -/

section Raw

open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M] {x : M} {γ : Ω M x} {σ : RoughForm I M ℝ 2}

namespace RawCap

/-- The **capped action** of a loop `γ` with a raw cap `D`, for a two-form `σ` and a
time-dependent Hamiltonian `Ham`: minus the area of `D` plus `∫₀¹ Ham(t, γ(t)) dt`. The raw cap is
oriented from `γ` to its centre, so minus its area is the area of the disc from its centre to `γ`,
as in `TauCeti.cappedLoopAction`. It is defined for loops with a smooth based cap (`h`), like
`TauCeti.Floer.RawCap.area`. -/
def action (σ : RoughForm I M ℝ 2) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) : ℝ :=
  -RawCap.area σ h D + ∫ t in 0..1, Ham t (γ.extend t)

/-- The defining equation of `TauCeti.Floer.RawCap.action`. -/
theorem action_def (σ : RoughForm I M ℝ 2) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) :
    action σ Ham h D = -RawCap.area σ h D + ∫ t in 0..1, Ham t (γ.extend t) :=
  (rfl)

/-- **The action of a smooth cap.** For a closed `C¹` two-form, the action of the raw cap of a
smooth based cap `u` is the capped action of `γ` with the disc `u` run backwards, from its centre
to `γ`. -/
theorem action_homotopyClass (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ)
    {u : ℝ × ℝ → M} (hu : IsSmoothBasedCap I γ u) :
    action σ Ham ⟨u, hu⟩ hu.homotopyClass =
      cappedLoopAction σ Ham (fun t ↦ u (0, t)) (u ∘ Prod.map (fun s ↦ 1 - s) id) := by
  rw [hu.cappedLoopAction_comp_prodMap_one_sub hσ hdσ, action_def]
  congr 1
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [γ.extend_apply ht, hu.apply_zero ⟨t, ht⟩]

/-- **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` to a raw cap, with the orientation of
the cap, lowers the action by the integral of a closed `C¹` two-form over `a`. -/
theorem action_vadd (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) (a : Additive (π_ 2 M x)) (D : RawCap γ) :
    action σ Ham h (a +ᵥ D) = -sphereIntegralHom x hσ hdσ a + action σ Ham h D := by
  rw [action_def, action_def, RawCap.area_vadd hσ hdσ h]
  ring

/-- **Two raw caps differ by a sphere.** The actions of two raw caps of `γ` differ by minus the
integral of a closed `C¹` two-form over the sphere by which they differ. -/
theorem action_sub_action (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) (D' D : RawCap γ) :
    action σ Ham h D' - action σ Ham h D = -sphereIntegralHom x hσ hdσ (D' -ᵥ D) := by
  rw [action_def, action_def, ← RawCap.area_sub_area hσ hdσ h]
  ring

/-- **The action does not depend on the cap when the form vanishes on spheres**, as for a
symplectically aspherical form. -/
theorem action_eq_action_of_vanishesOnSpheres (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0)
    (hS : VanishesOnSpheres σ) (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D' D : RawCap γ) : action σ Ham h D' = action σ Ham h D := by
  rw [← sub_eq_zero, action_sub_action hσ hdσ, sphereIntegralHom_apply,
    hS.sphereIntegral_eq_zero, neg_zero]

/-- **Normalization.** Adding a function `f` of time to the Hamiltonian adds `∫₀¹ f` to the
action, for an integrable `f` and a Hamiltonian that is integrable along `γ`. -/
theorem action_add_const (σ : RoughForm I M ℝ 2) {Ham : ℝ → M → ℝ} {f : ℝ → ℝ}
    (hHam : IntervalIntegrable (fun t ↦ Ham t (γ.extend t)) MeasureTheory.volume 0 1)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) (h : ∃ u, IsSmoothBasedCap I γ u)
    (D : RawCap γ) :
    action σ (fun t y ↦ Ham t y + f t) h D = action σ Ham h D + ∫ t in 0..1, f t := by
  rw [action_def, action_def, intervalIntegral.integral_add hHam hf]
  ring

end RawCap

end Raw

/-! ### The action of a cap class -/

namespace SphericalCapClass

open AlgebraicTopology

-- `ω` names the area homomorphism here, so the `ContDiff` scope, whose notation includes `ω`, is
-- not opened, and smoothness `∞` is written out.
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M] {x : M} {γ : Ω M x}
  {σ : RoughForm I M ℝ 2} {hσ : IsSmoothForm I 1 σ} {hdσ : mextDeriv σ = 0}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℤ}

/-- The **capped action** of a loop `γ` with a cap class, for a closed `C¹` two-form `σ`, a
time-dependent Hamiltonian `Ham` and a homomorphism `ω` on `H₂(M; ℤ)` that agrees with the
integral of `σ` on the Hurewicz classes of spheres (`hω`): the action of any raw cap in the class.
It is well defined because raw caps in the same class differ by a sphere whose Hurewicz class has
zero `ω`, hence zero integral. -/
def action (hσ : IsSmoothForm I 1 σ) (hdσ : mextDeriv σ = 0)
    (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegralHom x hσ hdσ a) (Ham : ℝ → M → ℝ)
    (h : ∃ u, IsSmoothBasedCap I γ u) : SphericalCapClass ω c γ → ℝ :=
  lift (-PeriodGroup.area _ _) (RawCap.action σ Ham h) fun a D ↦ by
    rw [RawCap.action_vadd hσ hdσ, AddMonoidHom.neg_apply,
      SphericalPeriodGroup.area_ofHomotopyGroup, hω]

variable (hω : ∀ a, ω (hurewiczIntHom M x 1 a) = sphereIntegralHom x hσ hdσ a)
  (Ham : ℝ → M → ℝ) (h : ∃ u, IsSmoothBasedCap I γ u)

/-- The action of the cap class of a raw cap is the action of the raw cap. -/
@[simp]
theorem action_mk (D : RawCap γ) : action hσ hdσ hω Ham h (mk ω c D) = RawCap.action σ Ham h D :=
  lift_mk _ _ _ D

/-- **Two cap classes differ by a class of the period group.** The actions of two cap classes of
`γ` differ by minus the area of the class by which they differ. -/
theorem action_sub_action (q' q : SphericalCapClass ω c γ) :
    action hσ hdσ hω Ham h q' - action hσ hdσ hω Ham h q = -PeriodGroup.area _ _ (q' -ᵥ q) := by
  induction q' using induction_on with | h D' =>
  induction q using induction_on with
  | h D => rw [action_mk, action_mk, mk_vsub_mk, SphericalPeriodGroup.area_ofHomotopyGroup, hω,
      RawCap.action_sub_action hσ hdσ]

variable [PathConnectedSpace M]

/-- **The recapping law on cap classes.** Recapping a cap class by a class `B` of the period group
lowers its action by the area of `B`. -/
@[simp]
theorem action_vadd (B : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ) :
    action hσ hdσ hω Ham h (B +ᵥ q) = -PeriodGroup.area _ _ B + action hσ hdσ hω Ham h q :=
  lift_vadd _ _ _ B q

/-- **A cap class is determined by its action when the area is injective on the period group**, as
when the first Chern number vanishes on spherical classes
(`TauCeti.Floer.PeriodGroup.area_injective_of_chern_eq_zero`). -/
theorem action_injective
    (hinj : Function.Injective (PeriodGroup.area _ _ : SphericalPeriodGroup ω c →+ ℝ)) :
    Function.Injective (action (c := c) hσ hdσ hω Ham h) := by
  have : Nonempty (RawCap γ) := ⟨h.choose_spec.homotopyClass⟩
  refine AddTorsor.injective_of_forall_vadd_eq_add (δ := -PeriodGroup.area _ _)
    (action_vadd hω Ham h) fun B B' hB ↦ hinj ?_
  simpa using hB

end SphericalCapClass

end TauCeti.Floer

end CapClass
