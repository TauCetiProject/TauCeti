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

Let `X` be a locally Noetherian integral scheme of dimension at most one whose codimension-one
local rings are discrete valuation rings. This file proves that a locally principal Weil divisor
`D` defines a line bundle `𝒪_X(D)`.

The local-principality API supplies, around every point, a nonzero rational function whose order
agrees with `D`. Multiplication by this local equation identifies the restriction of `𝒪_X(D)`
with that of `𝒪_X(0)`. Since `𝒪_X(0) ≅ 𝒪_X`, these local isomorphisms form a rank-one
trivialization atlas.

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

section LocallyNoetherian

variable [IsLocallyNoetherian X]

namespace IsLocallyPrincipal

variable {D : SchemeWeilDivisor X}

/-- A rank-one local trivialization atlas for the sheaf of a locally principal Weil divisor.

The cover is indexed by the points of `X`: at `x`, choose a neighbourhood `U` and a local equation
`g`. Multiplication by `g` identifies `𝒪_X(D)|_U` with `𝒪_X(0)|_U`; composing with
`𝒪_X(0) ≅ 𝒪_X` gives the required trivialization. -/
private def localTrivializations (hD : IsLocallyPrincipal D) (hX : ∀ y : X, coheight y ≤ 1) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} (sheaf D) := by
  classical
  let hD' := isLocallyPrincipal_iff.mp hD
  let U : X → X.Opens := fun x ↦ (hD' x).choose
  let hx : ∀ x, x ∈ U x := fun x ↦ (hD' x).choose_spec.1
  let g : X → Additive X.functionFieldˣ := fun x ↦ (hD' x).choose_spec.2.choose
  let hg : ∀ x (y : CodimensionOnePoint X), (y : X) ∈ U x →
      WeilDivisor.coeff D y = orderAt y (g x) :=
    fun x ↦ (hD' x).choose_spec.2.choose_spec
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
          (sheafOverMulIsoOfCoeffEq D 0 (U x) (g x) (by
            intro y hy
            simpa using hg x y hy)).symm }

/-- **The sheaf of a locally principal Weil divisor is a line bundle.** On a locally Noetherian
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

end LocallyNoetherian

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
