/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Disc
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped

/-!
# The capped action of raw caps

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

(`TauCeti.IsSmoothDisc.cappedLoopAction_sub_cappedLoopAction_eq_neg`). In particular smooth discs
with the same raw cap have the same action. The sign is that of the orientation conventions: a raw
cap runs from the loop to its centre, the reverse of the disc of the capped action, which runs from
its centre to the loop. So gluing a sphere `a` at the centre of the raw cap glues the sphere `a` run
backwards in front of the disc, and changes the action by `-∫_a ω`.

Consequently, once `γ` bounds one smooth disc `D₀`, the capped action descends to a function on
all raw caps of `γ`, `TauCeti.IsSmoothDisc.rawCapAction`: it is `A_H(γ, D)` on the raw cap of
every smooth disc `D` (`TauCeti.IsSmoothDisc.rawCapAction_rawCap`), it obeys the recapping law
`A(a +ᵥ P) = A(P) - ∫_a ω` (`TauCeti.IsSmoothDisc.rawCapAction_vadd`), and it does not depend on
the reference disc `D₀` (`TauCeti.IsSmoothDisc.rawCapAction_eq_rawCapAction`). That every raw cap
of a smooth loop is the raw cap of a smooth disc is not treated here.

## Main definitions

* `TauCeti.IsSmoothDisc.isLoopCylinder`: a smooth disc is a disc of the capped action.
* `TauCeti.IsSmoothDisc.rawCap`: the raw cap of a smooth disc.
* `TauCeti.IsSmoothDisc.rawCapAction`: the capped action as a function on raw caps.

## Main results

* `TauCeti.IsSmoothDisc.sphereIntegral_rawCap_vsub_rawCap`: the integral of a closed form over
  the sphere by which the raw caps of two smooth discs differ.
* `TauCeti.IsSmoothDisc.cappedLoopAction_sub_cappedLoopAction_eq_neg`: the change of the capped
  action between two smooth discs is minus the area of that sphere.
* `TauCeti.IsSmoothDisc.cappedLoopAction_eq_of_rawCap_eq`: the capped action only depends on the
  raw cap.
* `TauCeti.IsSmoothDisc.rawCapAction_rawCap`, `TauCeti.IsSmoothDisc.rawCapAction_vadd`,
  `TauCeti.IsSmoothDisc.rawCapAction_eq_rawCapAction`: the descended action and its recapping law.

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

/-- The **raw cap of a smooth disc**: the homotopy class of the disc, read as a path in the loop
space from the loop `γ` it bounds to the constant loop at its centre (`IsSmoothDisc.loopPath`). -/
def rawCap (hD : IsSmoothDisc I γ D) : Floer.RawCap γ :=
  Path.Homotopic.Quotient.mk hD.loopPath

/-- The sphere by which the raw caps of two smooth discs differ is the class of the double loop
that runs from the centre of the first disc to `γ` and back to the centre of the second. -/
theorem rawCap_vsub_rawCap (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D') :
    hD'.rawCap -ᵥ hD.rawCap = Additive.ofMul (fundamentalGroupLoopSpaceMulEquiv
      (FundamentalGroup.fromPath (.mk (hD.loopPath.symm.trans hD'.loopPath)))) :=
  (rfl)

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

/-- **Two smooth discs give capped actions differing by the area of a sphere.** For smooth discs
`D` and `D'` bounding the same loop, `A_H(γ, D') - A_H(γ, D)` is minus the integral of the closed
form `ω` over the sphere `D'.rawCap -ᵥ D.rawCap` by which their raw caps differ. The loop `ℓ` in
the Hamiltonian term is arbitrary, since that term is the same for both discs. -/
theorem cappedLoopAction_sub_cappedLoopAction_eq_neg (hω : IsSmoothForm I 1 ω)
    (hdω : mextDeriv ω = 0) (H : ℝ → M → ℝ) (ℓ : ℝ → M) (hD : IsSmoothDisc I γ D)
    (hD' : IsSmoothDisc I γ D') :
    cappedLoopAction ω H ℓ D' - cappedLoopAction ω H ℓ D =
      -sphereIntegral ω x (hD'.rawCap -ᵥ hD.rawCap).toMul := by
  rw [sphereIntegral_rawCap_vsub_rawCap hω hdω hD hD', cappedLoopAction_def,
    cappedLoopAction_def]
  ring

/-- **The capped action only depends on the raw cap.** Two smooth discs bounding the same loop
with the same raw cap have the same capped action. -/
theorem cappedLoopAction_eq_of_rawCap_eq (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (H : ℝ → M → ℝ) (ℓ : ℝ → M) (hD : IsSmoothDisc I γ D) (hD' : IsSmoothDisc I γ D')
    (h : hD.rawCap = hD'.rawCap) : cappedLoopAction ω H ℓ D = cappedLoopAction ω H ℓ D' := by
  have : Nonempty (Floer.RawCap γ) := ⟨hD.rawCap⟩
  have := cappedLoopAction_sub_cappedLoopAction_eq_neg hω hdω H ℓ hD hD'
  rw [h, vsub_self, toMul_zero, sphereIntegral_one hω hdω, neg_zero, sub_eq_zero] at this
  exact this.symm

variable {D₀ D₁ : ℝ × ℝ → M}

/-- The **capped action on raw caps** of a loop `γ` that bounds a smooth disc `D₀`:
`A(P) = A_H(γ, D₀) - ∫_{P -ᵥ D₀.rawCap} ω` for a raw cap `P` of `γ`. On the raw cap of a smooth
disc `D` it is `A_H(γ, D)` (`TauCeti.IsSmoothDisc.rawCapAction_rawCap`), and it does not depend
on `D₀` (`TauCeti.IsSmoothDisc.rawCapAction_eq_rawCapAction`). -/
def rawCapAction (hD₀ : IsSmoothDisc I γ D₀) (ω : RoughForm I M ℝ 2) (H : ℝ → M → ℝ)
    (P : Floer.RawCap γ) : ℝ :=
  cappedLoopAction ω H γ.extend D₀ - sphereIntegral ω x (P -ᵥ hD₀.rawCap).toMul

/-- On the raw cap of a smooth disc `D`, the capped action on raw caps is `A_H(γ, D)`. -/
@[simp]
theorem rawCapAction_rawCap (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (hD₀ : IsSmoothDisc I γ D₀) (H : ℝ → M → ℝ) (hD : IsSmoothDisc I γ D) :
    hD₀.rawCapAction ω H hD.rawCap = cappedLoopAction ω H γ.extend D := by
  have := cappedLoopAction_sub_cappedLoopAction_eq_neg hω hdω H γ.extend hD₀ hD
  rw [rawCapAction]
  linarith

/-- **The recapping law.** Gluing a sphere `a ∈ π₂(M, x)` at the centre of a raw cap changes the
capped action by minus the integral of `ω` over `a`. -/
theorem rawCapAction_vadd (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (hD₀ : IsSmoothDisc I γ D₀) (H : ℝ → M → ℝ) (a : Additive (π_ 2 M x))
    (P : Floer.RawCap γ) :
    hD₀.rawCapAction ω H (a +ᵥ P) = hD₀.rawCapAction ω H P - sphereIntegral ω x a.toMul := by
  have : Nonempty (Floer.RawCap γ) := ⟨P⟩
  have h := (sphereIntegralHom x hω hdω).map_add a (P -ᵥ hD₀.rawCap)
  simp only [sphereIntegralHom_apply] at h
  rw [rawCapAction, rawCapAction, vadd_vsub_assoc, h]
  ring

/-- The capped action on raw caps does not depend on the reference disc. -/
theorem rawCapAction_eq_rawCapAction (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0)
    (hD₀ : IsSmoothDisc I γ D₀) (hD₁ : IsSmoothDisc I γ D₁) (H : ℝ → M → ℝ) :
    hD₀.rawCapAction ω H = hD₁.rawCapAction ω H := by
  have : Nonempty (Floer.RawCap γ) := ⟨hD₀.rawCap⟩
  funext P
  rw [← vsub_vadd P hD₁.rawCap, rawCapAction_vadd hω hdω, rawCapAction_vadd hω hdω,
    rawCapAction_rawCap hω hdω, rawCapAction_rawCap hω hdω]

end IsSmoothDisc

end TauCeti
