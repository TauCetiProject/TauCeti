/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import Mathlib.RingTheory.Noetherian.Defs

import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rueckert

/-!
# Holomorphic stalks are Noetherian

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is Noetherian. In a chart this is the ring of convergent power series
in `n` variables, and the proof inducts on `n` via `stalk_induction`, using `evalEquiv` in
dimension `0`, Weierstrass preparation in the Rückert framework (`isRueckert_evalVertical` and
`RingHom.IsRueckert.isNoetherianRing`) for the inductive step, and chart pullback to transfer from
`Fin n → ℂ` to the manifold. Through the comparison of holomorphic and complex-smooth germs, the
same holds for the stalks of Mathlib's complex-smooth structure sheaf.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.stalkIsNoetherianRing`: holomorphic stalks are Noetherian.
* `TauCeti.holomorphicStructureSheaf.smoothStalkIsNoetherianRing`: so are the stalks of the
  complex-smooth structure sheaf.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter VI.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Ch. 2.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a Noetherian ring. -/
instance stalkIsNoetherianRing (x : X) :
    IsNoetherianRing ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  stalk_induction (P := fun R _ ↦ IsNoetherianRing R) inferInstance
    (fun e _ ↦ isNoetherianRing_of_ringEquiv _ e) (fun h _ ↦ h.isNoetherianRing) x

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a Noetherian ring, via its comparison with holomorphic germs. -/
instance smoothStalkIsNoetherianRing (x : X) :
    IsNoetherianRing ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  isNoetherianRing_of_ringEquiv _ (smoothStalkIso I X x).commRingCatIsoToRingEquiv

end TauCeti.holomorphicStructureSheaf
