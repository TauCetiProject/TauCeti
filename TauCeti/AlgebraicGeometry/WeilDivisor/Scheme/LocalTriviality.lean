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

Let `X` be a locally Noetherian integral scheme of dimension at most one whose codimension-one local
rings are discrete valuation rings. This file proves that a locally principal Weil divisor `D`
defines a line bundle `𝒪_X(D)`.

The local-principality API supplies, around every point, a nonzero rational function whose order
agrees with `D`. Multiplication by this local equation identifies the restriction of `𝒪_X(D)`
with that of `𝒪_X(0)`. Since `𝒪_X(0) ≅ 𝒪_X`, these local isomorphisms form a rank-one
trivialization atlas.

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
  let e : (sheaf D).over U ≅ (sheaf E).over U :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk
        (fun V ↦ by
          have hV : (submodule D).toSubmodule.obj ((Over.forget U).op.obj V) =
              (submodule E).toSubmodule.obj ((Over.forget U).op.obj V) :=
            by
              rw [show ((Over.forget U).op.obj V) = op V.unop.left from rfl,
                submodule_obj, submodule_obj]
              exact h V.unop.left V.unop.hom.le
          exact LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ hV))
        (by
          intro V W f
          ext s
          apply Subtype.ext
          -- Both restriction maps come from the ambient rational-function sheaf, while the
          -- component is the identity on underlying rational functions.
          rfl)
  exact e

/-- The restricted isomorphism induced by equality of section submodules commutes with their
inclusions into the restricted rational-function sheaf. -/
@[reassoc (attr := simp)]
lemma sheafOverIsoOfSectionsEq_hom_ι (D E : SchemeWeilDivisor X) (U : X.Opens)
    (h : ∀ V ≤ U, sections D V = sections E V) :
    (sheafOverIsoOfSectionsEq D E U h).hom ≫ (sheafι E).over U = (sheafι D).over U := by
  ext V s
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  rw [sheafι_over_app_apply, sheafι_over_app_apply]
  rfl

private lemma rationalFunctionsMul_mem_sections_of_localEquation
    (g : Additive X.functionFieldˣ) {D E : SchemeWeilDivisor X} {U V : X.Opens}
    (hVU : V ≤ U)
    (h : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      WeilDivisor.coeff D y = WeilDivisor.coeff E y + orderAt y g)
    {s : Γ(Scheme.rationalFunctions X, V)} (hs : s ∈ sections D V) :
    Scheme.Modules.Hom.app
        (Scheme.rationalFunctionsMul X ((Additive.toMul g : X.functionFieldˣ) : X.functionField))
        V s ∈ sections E V := by
  refine mem_sections.mpr fun y hy ↦ ?_
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  rw [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app]
  by_cases h0 : Scheme.rationalFunctionsEquiv V s = 0
  · exact Or.inl (by rw [h0, mul_zero])
  · refine Or.inr ?_
    have hs' := (mem_sections.mp hs y hy).resolve_left h0
    have hcoeff := h y (hVU hy)
    rw [Scheme.ord_mul (Units.ne_zero _) h0, ← orderAt_apply]
    omega

private lemma rationalFunctionsMul_over_mem_sections_of_localEquation
    (g : Additive X.functionFieldˣ) {D E : SchemeWeilDivisor X} {U : X.Opens}
    (V : (Over U)ᵒᵖ)
    (h : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      WeilDivisor.coeff D y = WeilDivisor.coeff E y + orderAt y g)
    (s : ((sheaf D).over U).val.obj V) :
    ((Scheme.rationalFunctionsMul X
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField)).over U).val.app V s.val ∈
        (submodule E).toSubmodule.obj ((Over.forget U).op.obj V) := by
  -- Restriction to the over-site evaluates at the underlying open `V.unop.left`; Mathlib has
  -- no rewrite lemma exposing this definitional identification.
  have hs : s.val ∈ sections D V.unop.left := s.2
  have key := rationalFunctionsMul_mem_sections_of_localEquation g V.unop.hom.le h hs
  change Scheme.Modules.Hom.app
      (Scheme.rationalFunctionsMul X
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField)) V.unop.left s.val ∈
    sections E V.unop.left
  exact key

/-- A local equation for `D` identifies its divisor sheaf with the zero-divisor sheaf after
restriction to the equation's neighbourhood. The forward map is multiplication by the local
equation. -/
private def sheafOverIsoZeroOfLocalEquation (D : SchemeWeilDivisor X) (U : X.Opens)
    (g : Additive X.functionFieldˣ)
    (h : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      WeilDivisor.coeff D y = orderAt y g) :
    (sheaf D).over U ≅ (sheaf (0 : SchemeWeilDivisor X)).over U := by
  have hforward : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      WeilDivisor.coeff D y = WeilDivisor.coeff (0 : SchemeWeilDivisor X) y + orderAt y g := by
    intro y hy
    simpa using h y hy
  have hinverse : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      WeilDivisor.coeff (0 : SchemeWeilDivisor X) y = WeilDivisor.coeff D y + orderAt y (-g) := by
    intro y hy
    rw [WeilDivisor.coeff_zero, h y hy, map_neg, add_neg_cancel]
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun V ↦ by
        letI := (((sheaf D).over U).val.obj V).isModule
        letI := (((sheaf (0 : SchemeWeilDivisor X)).over U).val.obj V).isModule
        exact LinearEquiv.toModuleIso ({
          toFun := fun s ↦
            ⟨((Scheme.rationalFunctionsMul X
                ((Additive.toMul g : X.functionFieldˣ) : X.functionField)).over U).val.app V s.val,
              rationalFunctionsMul_over_mem_sections_of_localEquation g V hforward s⟩
          invFun := fun s ↦
            ⟨((Scheme.rationalFunctionsMul X
                ((Additive.toMul (-g) : X.functionFieldˣ) : X.functionField)).over U).val.app V
                  s.val,
              rationalFunctionsMul_over_mem_sections_of_localEquation (-g) V hinverse s⟩
          left_inv := by
            intro s
            apply Subtype.ext
            change (Scheme.Modules.Hom.app
                (Scheme.rationalFunctionsMul X
                  ((Additive.toMul g : X.functionFieldˣ) : X.functionField)) V.unop.left ≫
              Scheme.Modules.Hom.app
                (Scheme.rationalFunctionsMul X
                  ((Additive.toMul (-g) : X.functionFieldˣ) : X.functionField)) V.unop.left)
                s.val = s.val
            rw [← Scheme.Modules.Hom.comp_app, rationalFunctionsMul_comp_neg,
              Scheme.Modules.Hom.id_app]
            rfl
          right_inv := by
            intro s
            apply Subtype.ext
            change (Scheme.Modules.Hom.app
                (Scheme.rationalFunctionsMul X
                  ((Additive.toMul (-g) : X.functionFieldˣ) : X.functionField)) V.unop.left ≫
              Scheme.Modules.Hom.app
                (Scheme.rationalFunctionsMul X
                  ((Additive.toMul g : X.functionFieldˣ) : X.functionField)) V.unop.left)
                s.val = s.val
            rw [← Scheme.Modules.Hom.comp_app, rationalFunctionsMul_neg_comp,
              Scheme.Modules.Hom.id_app]
            rfl
          map_add' := by
            intro s t
            apply Subtype.ext
            exact map_add _ _ _
          map_smul' := by
            intro r s
            apply Subtype.ext
            exact
              (((Scheme.rationalFunctionsMul X
                ((Additive.toMul g : X.functionFieldˣ) : X.functionField)).over U).val.app V).hom
                  |>.map_smul r s.val } :
          ((sheaf D).over U).val.obj V ≃ₗ[((X.ringCatSheaf.over U).obj.obj V : Type u)]
            ((sheaf (0 : SchemeWeilDivisor X)).over U).val.obj V))
      (by
        intro V W f
        ext s
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply
          ((Scheme.rationalFunctionsMul X
            ((Additive.toMul g : X.functionFieldˣ) : X.functionField)).over U).val f s.val)

namespace IsLocallyPrincipal

variable {D : SchemeWeilDivisor X}

/-- **A locally principal Weil divisor has a rank-one local trivialization atlas.**

The cover is indexed by the points of `X`: at `x`, choose a neighbourhood and local equation.
Multiplication by that equation identifies the restricted divisor sheaf with `𝒪_X(0)`, and
`𝒪_X(0) ≅ 𝒪_X` gives the required trivialization. -/
def localTrivializations (hD : IsLocallyPrincipal D) (hX : ∀ y : X, coheight y ≤ 1) :
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
          (sheafOverIsoZeroOfLocalEquation D (U x) (g x) (hg x)).symm }

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
