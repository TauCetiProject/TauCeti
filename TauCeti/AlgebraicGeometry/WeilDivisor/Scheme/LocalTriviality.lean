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

The local-principality API supplies, around every point, a divisor `E` such that `𝒪_X(D)` is
isomorphic to `𝒪_X(E)` and the sections of `𝒪_X(E)` equal those of `𝒪_X(0)` on every smaller
open. The latter equality gives an isomorphism after restriction to that neighbourhood. Since
`𝒪_X(0) ≅ 𝒪_X`, these local isomorphisms form a rank-one trivialization atlas.

## Main declarations

* `SchemeWeilDivisor.sheafOverIsoOfSectionsEq` identifies the restrictions of two divisor
  sheaves when their section submodules agree below an open set;
* `SchemeWeilDivisor.IsLocallyPrincipal.localTrivializations` constructs a rank-one
  trivialization atlas for the sheaf of a locally principal divisor;
* `SchemeWeilDivisor.IsLocallyPrincipal.isInvertible_sheaf` proves that this sheaf is
  invertible;
* `SchemeWeilDivisor.IsLocallyPrincipal.toInvertibleSheaf` packages it as an object of the
  category of invertible sheaves on `X`.

The construction follows Hartshorne, *Algebraic Geometry*, II.6.11 and the Stacks Project,
*Divisors*, Tags 0BE0 and 0BE9. No formalization is vendored.
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

/-- If two divisor sheaves have the same sections on every open subset of `U`, then their
restrictions to the over-site of `U` are isomorphic.

The isomorphism is the identity on the underlying rational functions. The hypothesis is stated
as equality of the displayed section submodules, rather than equality of sheaves, so it can be
applied directly to local equations of a Weil divisor. -/
def sheafOverIsoOfSectionsEq (D E : SchemeWeilDivisor X) (U : X.Opens)
    (h : ∀ V ≤ U, sections D V = sections E V) :
    (sheaf D).over U ≅ (sheaf E).over U := by
  let e : ((submodule D).toSheafOfModules).over U ≅
      ((submodule E).toSheafOfModules).over U :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk
        (fun V ↦ by
          have hV : (submodule D).toSubmodule.obj ((Over.forget U).op.obj V) =
              (submodule E).toSubmodule.obj ((Over.forget U).op.obj V) := by
            change (submodule D).toSubmodule.obj (op V.unop.left) =
              (submodule E).toSubmodule.obj (op V.unop.left)
            rw [submodule_obj, submodule_obj]
            exact h V.unop.left V.unop.hom.le
          exact LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ hV))
        (by
          intro V W f
          ext s
          apply Subtype.ext
          -- Both restriction maps come from the ambient rational-function sheaf, while the
          -- component is the identity on underlying rational functions.
          rfl)
  exact eqToIso (congrArg (fun M : X.Modules ↦ M.over U) (sheaf_def D)) ≪≫ e ≪≫
    (eqToIso (congrArg (fun M : X.Modules ↦ M.over U) (sheaf_def E))).symm

end LocallyNoetherian

section Noetherian

variable [IsNoetherian X]

namespace IsLocallyPrincipal

variable {D : SchemeWeilDivisor X}

/-- **A locally principal Weil divisor has a rank-one local trivialization atlas.**

The cover is indexed by the points of `X`: at `x`, choose the neighbourhood and locally
principal comparison divisor supplied by
`IsLocallyPrincipal.exists_iso_sheaf_sections_eq_sections_zero`. On that neighbourhood the
comparison divisor has the same section submodules as the zero divisor. Composing the resulting
restricted isomorphisms with `𝒪_X(0) ≅ 𝒪_X` gives the required trivialization. -/
def localTrivializations (hD : IsLocallyPrincipal D) (hX : ∀ y : X, coheight y ≤ 1) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} (sheaf D) := by
  classical
  choose U E hx e hsections using
    fun x ↦ hD.exists_iso_sheaf_sections_eq_sections_zero x
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
          (sheafOverIsoOfSectionsEq (E x) 0 (U x) (hsections x)).symm ≪≫
          ((SheafOfModules.overFunctor X.ringCatSheaf (U x)).mapIso
            (e x).some).symm }

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
