/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Area
import TauCeti.Geometry.Manifold.SmoothApprox.PeriodicLoop

/-!
# Smooth representatives of raw caps

Let `M` be a Hausdorff boundaryless manifold modelled on a finite-dimensional space, and `γ` a loop
in `M` based at `x` whose `1`-periodic extension `g : ℝ → M` is smooth, as for a one-periodic
orbit of a Hamiltonian. This file proves that every raw cap of `γ`
(`TauCeti.Floer.RawCap γ`), a homotopy class of continuous discs bounding `γ`, is the homotopy
class of a smooth based cap (`TauCeti.Floer.IsSmoothBasedCap`)
(`TauCeti.Floer.RawCap.exists_isSmoothBasedCap_homotopyClass_eq`). Consequently a loop has a smooth
based cap exactly when it is null-homotopic and its periodic extension is smooth
(`TauCeti.Floer.exists_isSmoothBasedCap_iff`). This discharges the hypothesis of
`TauCeti.Floer.RawCap.area` for every smooth contractible loop, and the area of every raw cap of
such a loop is the integral of the form over a smooth based cap in its class
(`TauCeti.Floer.RawCap.exists_area_eq_rectangleIntegral`).

A raw cap is the class of a path `P` in the loop space from `γ` to the constant loop. The smoothing
of paths of smooth periodic loops relative to their ends
(`TauCeti.exists_contMDiff_periodic_homotopic`, in
`Geometry/Manifold/SmoothApprox/PeriodicLoop.lean`), applied with the constant loop as second end,
replaces `P` by the path of loops of a smooth map of the plane, periodic in `t`, which is the
periodic extension of `γ` along `s = 0` and constant along `s = 1`. This map is a smooth based cap.

## Main results

* `TauCeti.Floer.RawCap.exists_isSmoothBasedCap_homotopyClass_eq`: every raw cap of a loop with a
  smooth periodic extension is the homotopy class of a smooth based cap.
* `TauCeti.Floer.exists_isSmoothBasedCap_iff`: a loop has a smooth based cap exactly when it is
  null-homotopic and its periodic extension is smooth.
* `TauCeti.Floer.RawCap.exists_area_eq_rectangleIntegral`: the area of every raw cap of such a loop
  is the integral of the form over a smooth based cap representing it.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (capped periodic orbits and their action).
-/

public section

open Set Function
open scoped Manifold ContDiff Topology.Homotopy

namespace TauCeti.Floer

section Smoothing

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {x : M} {γ : Ω M x}
  {g : ℝ → M}

variable [FiniteDimensional ℝ E] [BoundarylessManifold I M] [IsManifold I ∞ M] [T2Space M]

/-- **Smooth representatives of raw caps.** If the `1`-periodic extension `g` of a loop `γ` is
smooth, every raw cap of `γ` is the homotopy class of a smooth based cap. -/
theorem RawCap.exists_isSmoothBasedCap_homotopyClass_eq (hg : ContMDiff 𝓘(ℝ) I ∞ g)
    (hgp : Periodic g 1) (hgγ : ∀ t : unitInterval, g t = γ t) (D : RawCap γ) :
    ∃ u, ∃ hu : IsSmoothBasedCap I γ u, hu.homotopyClass = D := by
  obtain ⟨P, rfl⟩ := Path.Homotopic.Quotient.mk_surjective D
  obtain ⟨u, hu, hper, hu₀, hu₁, P', hP', hP⟩ := exists_contMDiff_periodic_homotopic hg hgp
    (fun t ↦ (hgγ t).symm) contMDiff_const (fun _ ↦ rfl) (fun _ ↦ rfl) P
  have hcap : IsSmoothBasedCap I γ u :=
    ⟨hu, hper, fun t ↦ (hu₀ t).trans (hgγ t), fun t ↦ hu₁ t,
      fun s ↦ by rw [← Icc.coe_zero, ← hP', (P' s).source]⟩
  have h : hcap.toPath = P' :=
    Path.ext (funext fun s ↦ Path.ext (funext fun t ↦ (hcap.toPath_apply s t).trans (hP' s t).symm))
  refine ⟨u, hcap, ?_⟩
  rw [IsSmoothBasedHomotopy.homotopyClass_def, h]
  exact Path.Homotopic.Quotient.eq.2 hP

/-- **Existence of smooth based caps.** A loop has a smooth based cap exactly when it is
null-homotopic and its `1`-periodic extension is smooth. -/
theorem exists_isSmoothBasedCap_iff :
    (∃ u, IsSmoothBasedCap I γ u) ↔ γ.Homotopic (Path.refl x) ∧
      ∃ g : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ g ∧ Periodic g 1 ∧ ∀ t : unitInterval, g t = γ t := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨RawCap.nonempty_iff.1 ⟨hu.homotopyClass⟩, fun t ↦ u (0, t),
      hu.contMDiff.comp (contDiff_const.prodMk contDiff_id).contMDiff,
      fun t ↦ hu.apply_add_one (0, t), hu.apply_zero⟩
  · rintro ⟨h, g, hg, hgp, hgγ⟩
    obtain ⟨D⟩ := RawCap.nonempty_iff.2 h
    obtain ⟨u, hu, -⟩ := RawCap.exists_isSmoothBasedCap_homotopyClass_eq hg hgp hgγ D
    exact ⟨u, hu⟩

omit [BoundarylessManifold I M] in
/-- **The area of a raw cap is the integral over a smooth representative.** For a loop with a
smooth based cap and a closed `C¹` two-form, every raw cap is the raw cap of a smooth based cap
`u`, and its area is the integral of the form over `u` on the unit square. -/
theorem RawCap.exists_area_eq_rectangleIntegral [I.Boundaryless] [CompactSpace M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (h : ∃ u, IsSmoothBasedCap I γ u) (D : RawCap γ) :
    ∃ u, ∃ hu : IsSmoothBasedCap I γ u,
      hu.homotopyClass = D ∧ RawCap.area φ h D = rectangleIntegral φ u (0, 0) (1, 1) := by
  obtain ⟨-, g, hg, hgp, hgγ⟩ := exists_isSmoothBasedCap_iff.1 h
  obtain ⟨u, hu, rfl⟩ := RawCap.exists_isSmoothBasedCap_homotopyClass_eq hg hgp hgγ D
  exact ⟨u, hu, rfl, RawCap.area_homotopyClass hφ hdφ hu⟩

end Smoothing

end TauCeti.Floer
