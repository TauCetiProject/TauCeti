/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Invertible
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.LocallyPrincipal

/-!
# Line bundles from locally principal Weil divisors

Let `X` be a Noetherian integral scheme of dimension at most one whose codimension-one local
rings are discrete valuation rings. This file proves that a locally principal Weil divisor `D`
defines a line bundle `𝒪_X(D)`.

The local-principality API supplies, around every point, a divisor `E` whose sheaf is isomorphic
to `𝒪_X(D)` and whose sections agree with those of `𝒪_X(0)` on every smaller open subset. This is
`SchemeWeilDivisor.IsLocallyPrincipal.exists_iso_sheaf_sections_eq_sections_zero`.
Restricting that isomorphism and composing it with
`SchemeWeilDivisor.sheafOverIsoOfSectionsEq` and the identification
`SchemeWeilDivisor.unitIsoSheafZero` of `𝒪_X(0)` with `𝒪_X` therefore gives a rank-one
trivialization atlas, in the sense of
`TauCeti.SheafOfModules.LocalTrivializations`.

The hypothesis is `IsNoetherian X`, rather than the `IsLocallyNoetherian X` under which
`𝒪_X(D)` itself is built, because the existing local-principality comparison used here is
currently available under the stronger hypothesis.

## Main declarations

* `SchemeWeilDivisor.IsLocallyPrincipal.isInvertible_sheaf` proves that the sheaf of a locally
  principal Weil divisor is invertible;
* `SchemeWeilDivisor.IsLocallyPrincipal.toInvertibleSheaf` packages it as an object of the
  category of invertible sheaves on `X`.

The construction follows Hartshorne, *Algebraic Geometry*, II.6.11 and the Stacks Project,
*Divisors*, Tags 0BE0 and 0BE9.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

noncomputable section

section Noetherian

variable [IsNoetherian X]

namespace IsLocallyPrincipal

variable {D : SchemeWeilDivisor X}

/-- A rank-one local trivialization atlas for the sheaf of a locally principal Weil divisor.

The cover is indexed by the points of `X`: at `x`, choose a neighbourhood `U`, a divisor `E`
whose sheaf is isomorphic to `𝒪_X(D)`, and section equalities between `𝒪_X(E)` and `𝒪_X(0)` below
`U`. Restricting the chosen isomorphism and composing with `𝒪_X(0) ≅ 𝒪_X` gives the required
trivialization. -/
private def localTrivializations (hD : IsLocallyPrincipal D) (hX : ∀ y : X, coheight y ≤ 1) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} (sheaf D) := by
  classical
  let hU := fun x : X ↦ hD.exists_iso_sheaf_sections_eq_sections_zero x
  let U : X → X.Opens := fun x ↦ (hU x).choose
  let E : X → SchemeWeilDivisor X := fun x ↦ (hU x).choose_spec.choose
  let hx : ∀ x, x ∈ U x := fun x ↦ (hU x).choose_spec.choose_spec.1
  let e : ∀ x, sheaf D ≅ sheaf (E x) := fun x ↦
    (hU x).choose_spec.choose_spec.2.1.some
  let hsec : ∀ (x : X), ∀ V ≤ U x,
      sections (E x) V = sections (0 : SchemeWeilDivisor X) V :=
    fun x ↦ (hU x).choose_spec.choose_spec.2.2
  exact
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff (X : Type u) U).mpr (by
        rw [TopologicalSpace.IsOpenCover]
        ext x
        constructor
        · exact fun _ ↦ Opens.mem_top x
        · exact fun _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
      iso := fun x ↦
        TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over (U x)) ≪≫
          (SheafOfModules.overFunctor X.ringCatSheaf (U x)).mapIso
            (unitIsoSheafZero hX) ≪≫
          (sheafOverIsoOfSectionsEq (E x) 0 (U x) (hsec x)).symm ≪≫
          ((SheafOfModules.overFunctor X.ringCatSheaf (U x)).mapIso (e x)).symm }

/-- **The sheaf of a locally principal Weil divisor is a line bundle.** On a Noetherian
integral scheme of dimension at most one whose codimension-one local rings are discrete
valuation rings, local equations for `D` trivialize `𝒪_X(D)` as a rank-one module sheaf. -/
theorem isInvertible_sheaf (hD : IsLocallyPrincipal D) (hX : ∀ y : X, coheight y ≤ 1) :
    SheafOfModules.isInvertible X (sheaf D) :=
  (hD.localTrivializations hX).isInvertible

/-- The invertible sheaf `𝒪_X(D)` attached to a locally principal Weil divisor. -/
def toInvertibleSheaf (hD : IsLocallyPrincipal D) (hX : ∀ y : X, coheight y ≤ 1) :
    InvertibleSheaf X :=
  ⟨sheaf D, hD.isInvertible_sheaf hX⟩

/-- The underlying sheaf of the line bundle attached to `D` is `𝒪_X(D)`. -/
@[simp]
lemma toInvertibleSheaf_obj (hD : IsLocallyPrincipal D) (hX : ∀ y : X, coheight y ≤ 1) :
    (hD.toInvertibleSheaf hX).obj = sheaf D :=
  (rfl)

end IsLocallyPrincipal

end Noetherian

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
