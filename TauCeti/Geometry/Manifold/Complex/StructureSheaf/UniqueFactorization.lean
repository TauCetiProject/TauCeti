/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison

import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rueckert
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback

/-!
# Holomorphic stalks are unique factorisation domains

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is a unique factorisation domain.

The proof follows Rückert's inductive descent along Weierstrass preparation and division. In
dimension zero the stalk is `ℂ`. For the inductive step from `Fin n → ℂ` to `(Fin n → ℂ) × ℂ` at
`(0, 0)`, vertical polynomial evaluation satisfies the Rückert hypotheses with respect to
distinguished polynomials (`TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`), and
Rückert's factorial descent (`RingHom.IsRueckert.uniqueFactorizationMonoid`) passes unique
factorisation from `𝒪_{Fin n → ℂ, 0}` to `𝒪_{(Fin n → ℂ) × ℂ, (0, 0)}`. Dimension induction and
chart pullback (`TauCeti.holomorphicStructureSheaf.stalk_induction`) then transfer the property to
arbitrary finite-dimensional complex manifolds without boundary, as well as to Mathlib's native
complex-smooth structure sheaf via `TauCeti.holomorphicStructureSheaf.smoothStalkIso`.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`: holomorphic stalks are
  unique factorisation domains.
* `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: so are the stalks of
  Mathlib's complex-smooth structure sheaf.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, Theorem (2.10).
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5 (for Rückert descent).
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a unique factorisation domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  stalk_induction (fun R _ ↦ UniqueFactorizationMonoid R)
    (fun e h ↦ e.toMulEquiv.uniqueFactorizationMonoid h) inferInstance
    (fun n hV ↦ have := hV 0
      (isRueckert_evalVertical (0 : Fin n → ℂ) 0).uniqueFactorizationMonoid) x

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorisation domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end TauCeti.holomorphicStructureSheaf
