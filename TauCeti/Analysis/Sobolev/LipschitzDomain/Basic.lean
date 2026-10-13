/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Domains with Lipschitz boundary

This file defines the local graph condition for a Lipschitz domain in a Euclidean product
`WithLp 2 (ℝ × E)`. At every boundary point, a rigid change of coordinates must identify the
domain inside a product cylinder with the region above the graph of a Lipschitz function. The
graph passes through the centre of the chart, so the normal and tangential radii can subsequently
be reduced without changing the chart.

The global predicate `Set.IsLipschitzDomainWith` requires a single Lipschitz bound for all local
graphs. It is invariant under affine isometries. These are the geometric hypotheses used to
transport Sobolev trace and extension operators from a flat half-space through boundary charts.

## Main declarations

* `TauCeti.normalCylinder`: the product cylinder used by boundary charts.
* `Set.IsLipschitzDomainAtWith`: the local Lipschitz graph condition at one point.
* `Set.IsLipschitzDomainWith`: an open set with the local graph condition at every frontier point.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The open product cylinder of normal radius `a` and tangential radius `b`, centred at the
origin of `WithLp 2 (ℝ × E)`. -/
def normalCylinder (a b : ℝ) : Set (WithLp 2 (ℝ × E)) :=
  {x | x.fst ∈ Ioo (-a) a ∧ x.snd ∈ ball 0 b}

omit [NormedSpace ℝ E] in
/-- Membership in the normal product cylinder, in terms of its two coordinates. -/
@[simp]
theorem mem_normalCylinder {a b : ℝ} {x : WithLp 2 (ℝ × E)} :
    x ∈ normalCylinder a b ↔ -a < x.fst ∧ x.fst < a ∧ ‖x.snd‖ < b := by
  simp [normalCylinder, and_assoc]

omit [NormedSpace ℝ E] in
/-- A normal product cylinder is open. -/
theorem isOpen_normalCylinder (a b : ℝ) : IsOpen (normalCylinder (E := E) a b) := by
  exact (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ E).fst).inter
    (isOpen_ball.preimage (WithLp.prod_continuous_ofLp 2 ℝ E).snd)

omit [NormedSpace ℝ E] in
/-- Shrinking either radius shrinks the normal product cylinder. -/
theorem normalCylinder_mono {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b' ≤ b) :
    normalCylinder (E := E) a' b' ⊆ normalCylinder a b := by
  intro x hx
  simp only [mem_normalCylinder] at hx ⊢
  exact ⟨lt_of_le_of_lt (neg_le_neg ha) hx.1, hx.2.1.trans_le ha, hx.2.2.trans_le hb⟩

end TauCeti

namespace Set

open Metric TauCeti
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A set is a Lipschitz domain at `x`, with graph constant at most `L`, if a rigid coordinate
change taking `x` to the origin identifies the set in some open product cylinder with the strict
epigraph of a function `φ` satisfying `LipschitzWith L φ` and `φ 0 = 0`.

The two independently positive cylinder radii retain the product geometry needed for boundary
charts and permit either the normal or tangential direction to be shrunk later. -/
def IsLipschitzDomainAtWith (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0)
    (x : WithLp 2 (ℝ × E)) : Prop :=
  ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
    0 < a ∧ 0 < b ∧ e x = 0 ∧ φ 0 = 0 ∧ LipschitzWith L φ ∧
      ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst)

/-- The local Lipschitz-domain predicate written out as a rigid-coordinate graph condition. -/
theorem isLipschitzDomainAtWith_iff (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0)
    (x : WithLp 2 (ℝ × E)) :
    Omega.IsLipschitzDomainAtWith L x ↔
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (a b : ℝ),
        0 < a ∧ 0 < b ∧ e x = 0 ∧ φ 0 = 0 ∧ LipschitzWith L φ ∧
          ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ φ z.snd < z.fst) :=
  Iff.rfl

/-- An open set is a Lipschitz domain with constant `L` if it has a Lipschitz graph chart with
that bound at every point of its frontier. -/
def IsLipschitzDomainWith (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0) : Prop :=
  IsOpen Omega ∧ ∀ x ∈ frontier Omega, Omega.IsLipschitzDomainAtWith L x

/-- A set is a Lipschitz domain with constant `L` exactly when it is open and has a local
`L`-Lipschitz graph chart at every frontier point. -/
theorem isLipschitzDomainWith_iff (Omega : Set (WithLp 2 (ℝ × E))) (L : ℝ≥0) :
    Omega.IsLipschitzDomainWith L ↔
      IsOpen Omega ∧ ∀ x ∈ frontier Omega, Omega.IsLipschitzDomainAtWith L x :=
  Iff.rfl

/-- A local Lipschitz-domain chart remains valid after increasing the allowed Lipschitz
constant. -/
theorem IsLipschitzDomainAtWith.mono {Omega : Set (WithLp 2 (ℝ × E))} {L L' : ℝ≥0}
    {x : WithLp 2 (ℝ × E)} (h : Omega.IsLipschitzDomainAtWith L x) (hLL' : L ≤ L') :
    Omega.IsLipschitzDomainAtWith L' x := by
  obtain ⟨e, φ, a, b, ha, hb, hex, hφ0, hφ, hOmega⟩ := h
  exact ⟨e, φ, a, b, ha, hb, hex, hφ0, hφ.weaken hLL', hOmega⟩

/-- A Lipschitz domain remains one after increasing the allowed Lipschitz constant. -/
theorem IsLipschitzDomainWith.mono {Omega : Set (WithLp 2 (ℝ × E))} {L L' : ℝ≥0}
    (h : Omega.IsLipschitzDomainWith L) (hLL' : L ≤ L') :
    Omega.IsLipschitzDomainWith L' :=
  ⟨h.1, fun x hx ↦ (h.2 x hx).mono hLL'⟩

/-- Transport a local Lipschitz-domain chart by an affine isometry. -/
theorem IsLipschitzDomainAtWith.image_affineIsometryEquiv
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} {x : WithLp 2 (ℝ × E)}
    (h : Omega.IsLipschitzDomainAtWith L x)
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainAtWith L (g x) := by
  obtain ⟨e, φ, a, b, ha, hb, hex, hφ0, hφ, hOmega⟩ := h
  refine ⟨g.symm.trans e, φ, a, b, ha, hb, ?_, hφ0, hφ, ?_⟩
  · simp [hex]
  · intro z hz
    have hchart : (g.symm.trans e).symm z = g (e.symm z) := by
      simpa only [Function.comp_apply, AffineIsometryEquiv.symm_symm] using
        congrFun (AffineIsometryEquiv.coe_symm_trans g.symm e) z
    have himage : g (e.symm z) ∈ g '' Omega ↔ e.symm z ∈ Omega := by
      constructor
      · rintro ⟨y, hy, hgy⟩
        rw [← g.injective hgy]
        exact hy
      · exact fun hz ↦ ⟨e.symm z, hz, rfl⟩
    rw [hchart, himage]
    exact hOmega z hz

/-- The local Lipschitz-domain condition is invariant under an affine isometry. -/
theorem isLipschitzDomainAtWith_image_affineIsometryEquiv_iff
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} {x : WithLp 2 (ℝ × E)}
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainAtWith L (g x) ↔ Omega.IsLipschitzDomainAtWith L x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.image_affineIsometryEquiv g⟩
  have himage : g.symm '' g '' Omega = Omega :=
    g.toContinuousAffineEquiv.symm_image_image Omega
  simpa only [himage, AffineIsometryEquiv.symm_apply_apply] using
    h.image_affineIsometryEquiv g.symm

/-- Affine isometries preserve Lipschitz domains and their Lipschitz constant. -/
theorem IsLipschitzDomainWith.image_affineIsometryEquiv
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} (h : Omega.IsLipschitzDomainWith L)
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainWith L := by
  refine ⟨g.toHomeomorph.isOpenMap _ h.1, fun y hy ↦ ?_⟩
  have hfrontier : g '' frontier Omega = frontier (g '' Omega) := by
    exact g.toHomeomorph.image_frontier Omega
  rw [← hfrontier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact (h.2 x hx).image_affineIsometryEquiv g

/-- Being a Lipschitz domain with a fixed constant is invariant under affine isometries. -/
theorem isLipschitzDomainWith_image_affineIsometryEquiv_iff
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainWith L ↔ Omega.IsLipschitzDomainWith L := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.image_affineIsometryEquiv g⟩
  have himage : g.symm '' g '' Omega = Omega :=
    g.toContinuousAffineEquiv.symm_image_image Omega
  simpa only [himage] using h.image_affineIsometryEquiv g.symm

end Set

end
