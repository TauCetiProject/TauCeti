/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

/-!
Interface source: `TauCetiRoadmap/AnalyticToricGeometry/README.md`, Layer 0 item 9
(global dense torus), using the Layer 0 item 7 zero-cone chart prerequisite.  The torus action
remains later work.

# The dense torus of a toric fan

The zero cone is a cone of every nonempty finite fan.  This module places the generic dense-torus
scheme from `Algebraic.DenseTorus` in the toric scheme of a regular fan and records the canonical
open immersion into the realization.  The compatibility theorem says that this inclusion is
obtained on every affine chart by the face localization from the zero cone.

This is the zero-cone chart/open-subscheme prerequisite for the global dense-torus layer.  It does
not replace the fan realization by a second quotient, and it leaves the global torus action and
the analytic realization to their later roadmap layers.

## Main declarations

* `TauCeti.Toric.Fan.denseTorus`: the zero-cone dense torus attached to a fan.
* `TauCeti.Toric.Fan.denseTorusι`: the canonical inclusion into a regular fan realization.
* `TauCeti.Toric.Fan.denseTorusι_eq`: independence of the nonemptiness witness.
* `TauCeti.Toric.Fan.isOpenImmersion_denseTorusι`: the inclusion is an open immersion.
* `TauCeti.Toric.Fan.denseTorusι_face`: the inclusion agrees with face localization on every
  affine chart.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3--1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The dense torus of a fan is the zero-cone dense torus of its integral lattice. -/
noncomputable abbrev denseTorus (Φ : Fan i) : Scheme :=
  denseTorusScheme Φ.lattice

/-- The zero cone selected from a nonempty fan.  This is an implementation helper for the
canonical inclusion; the public inclusion below takes the nonemptiness proof directly. -/
private noncomputable def botCone (Φ : Fan i) (hΦ₀ : Nonempty Φ.cones) : Φ.cones :=
  ⟨⊥, Φ.bot_mem hΦ₀.some.property⟩

/-- The canonical inclusion of the dense torus for a nonempty regular toric fan. -/
noncomputable def denseTorusι (Φ : Fan i) (hΦ : Φ.IsRegular)
    (hΦ₀ : Nonempty Φ.cones) : Φ.denseTorus ⟶ Φ.algebraicRealization hΦ :=
  Φ.affineToricChartι hΦ (botCone Φ hΦ₀)

/-- The dense torus is an open subscheme of every regular toric fan realization. -/
instance isOpenImmersion_denseTorusι (Φ : Fan i) (hΦ : Φ.IsRegular)
    (hΦ₀ : Nonempty Φ.cones) : IsOpenImmersion (Φ.denseTorusι hΦ hΦ₀) :=
  Φ.isOpenImmersion_affineToricChartι hΦ (botCone Φ hΦ₀)

/-- The dense-torus inclusion is independent of the proof witnessing fan nonemptiness. -/
theorem denseTorusι_eq (Φ : Fan i) (hΦ : Φ.IsRegular)
    (hΦ₀ hΦ₁ : Nonempty Φ.cones) :
    Φ.denseTorusι hΦ hΦ₀ = Φ.denseTorusι hΦ hΦ₁ := by
  let σ : Φ.cones := botCone Φ hΦ₀
  have hσ : (Nonempty.intro σ) = hΦ₀ := by rfl
  rw [← hσ]

/-- On every affine chart, the dense-torus inclusion is the face localization from the zero cone. -/
theorem denseTorusι_face (Φ : Fan i) (hΦ : Φ.IsRegular) (σ : Φ.cones) :
    Φ.denseTorusι hΦ (Nonempty.intro σ) =
      faceAffineToricSchemeMap Φ.lattice
          ((Φ.isToricCone σ.2).salient.bot_isFaceOf) ≫
        Φ.affineToricChartι hΦ σ := by
  have hbot : (⊥ : PointedCone ℝ V).IsFaceOf σ.1 :=
    (Φ.isToricCone σ.2).salient.bot_isFaceOf
  symm
  simpa [denseTorusι, denseTorus, denseTorusScheme, botCone] using
    (faceAffineToricSchemeMap_comp_affineToricChartι (Φ := Φ) hΦ
      (τ := botCone Φ (Nonempty.intro σ)) (σ := σ) hbot)

end TauCeti.Toric.Fan
