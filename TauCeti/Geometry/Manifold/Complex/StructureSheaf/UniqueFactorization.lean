/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass

import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rueckert
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback

/-!
# Holomorphic stalks are unique factorisation domains

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is a unique factorisation domain. The same holds chart-locally at any
point in the domain of a holomorphic chart with respect to a boundaryless model on a
finite-dimensional complex normed space, without assuming a global manifold structure.

The proof follows Rückert's inductive descent along Weierstrass preparation and division. In
dimension zero the stalk is `ℂ`. For the inductive step from `Fin n → ℂ` to `(Fin n → ℂ) × ℂ` at
`(0, 0)`, vertical polynomial evaluation satisfies the Rückert hypotheses with respect to
distinguished polynomials (`TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`), and
Rückert's factorial descent (`RingHom.IsRueckert.uniqueFactorizationMonoid`) passes unique
factorisation from `𝒪_{Fin n → ℂ, 0}` to `𝒪_{(Fin n → ℂ) × ℂ, (0, 0)}`. Dimension induction on
model spaces (`TauCeti.holomorphicStructureSheaf.stalk_induction_modelSpace`) and chart pullback
(`OpenPartialHomeomorph.holomorphicStalkEquivModelSpace`) then transfer the property to arbitrary
chart-local and manifold holomorphic stalks, as well as to Mathlib's native complex-smooth
structure sheaf via `TauCeti.holomorphicStructureSheaf.smoothStalkIso`.

Consequently, a distinguished polynomial `P` over `𝒪_{E, x₀}` is irreducible in `(𝒪_{E, x₀})[X]`
if and only if `evalVertical x₀ w₀ P` is irreducible in `𝒪_{E × ℂ, (x₀, w₀)}`.

## Main declarations

* `OpenPartialHomeomorph.uniqueFactorizationMonoid_holomorphicStalk`: unique factorisation of the
  holomorphic stalk at any point in the domain of a holomorphic chart.
* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`: holomorphic stalks are
  unique factorisation domains.
* `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: so are the stalks of
  Mathlib's complex-smooth structure sheaf.
* `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_iff_of_isDistinguishedAt`:
  irreducibility of distinguished Weierstrass polynomials matches that of their vertical
  evaluations.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, Theorem (2.10).
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5 (for Rückert descent).
-/

public noncomputable section

open IsLocalRing Module Polynomial
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  (e : OpenPartialHomeomorph X H) (he : e ∈ IsManifold.maximalAtlas I ω X) {x : X}
  (hx : x ∈ e.source)

include he hx in
/-- At any point in the domain of a holomorphic chart with respect to a boundaryless model on a
finite-dimensional complex normed space `E`, the holomorphic stalk is a unique factorisation
domain, without assuming a global manifold structure on `X`. -/
theorem uniqueFactorizationMonoid_holomorphicStalk :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  (e.holomorphicStalkEquivModelSpace he x hx
    (ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun ℂ).symm)).symm.toMulEquiv
    |>.uniqueFactorizationMonoid
      (stalk_induction_modelSpace (fun R _ ↦ UniqueFactorizationMonoid R)
        (fun eqv h ↦ eqv.toMulEquiv.uniqueFactorizationMonoid h) inferInstance
        (fun n hV ↦ have := hV 0
          (isRueckert_evalVertical (0 : Fin n → ℂ) 0).uniqueFactorizationMonoid) _ _)

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a unique factorisation domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  exact (chartAt H x).uniqueFactorizationMonoid_holomorphicStalk
    (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source H x)

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorisation domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end Manifold

section Vertical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A distinguished polynomial over `𝒪_{E, x₀}` has irreducible vertical evaluation at `(x₀, w₀)`
if and only if it is irreducible in `(𝒪_{E, x₀})[X]`. -/
theorem irreducible_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P :=
  (isRueckert_evalVertical x₀ w₀).irreducible_apply_iff hP

end Vertical

end TauCeti.holomorphicStructureSheaf
