/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.AlgebraicGeometry.Scheme.Normal

/-!
# Functions on a normal scheme universally closed over an affine base

Let `X` be an integral scheme and `U` a nonempty open subset at whose points the local rings of
`X` are integrally closed. Inside the function field `K(X)`, the ring `Γ(X, U)` is the
intersection of these local rings, each of which is integrally closed in its fraction field
`K(X)`; hence `Γ(X, U)` is integrally closed in `K(X)`
(`AlgebraicGeometry.Scheme.isIntegrallyClosedIn_functionField`).

If moreover `f : X ⟶ Y` is universally closed and `V ⊆ Y` is an affine open, the ring map
`Γ(Y, V) ⟶ Γ(X, f⁻¹V)` is integral
(`AlgebraicGeometry.Scheme.Hom.isIntegral_app_of_universallyClosed`). Combining the two, when
the local rings of `X` along `f⁻¹V` are integrally closed, the functions on `f⁻¹V` are exactly
the rational functions on `X` that are integral over `Γ(Y, V)`
(`AlgebraicGeometry.Scheme.Hom.mem_range_germToFunctionField_iff`). For an affine base, the
case `V = Y` describes the global functions
(`AlgebraicGeometry.Scheme.Hom.mem_range_germToFunctionField_top_iff`).

For instance, for a normal integral scheme `X` proper over a Dedekind domain `R`, the ring
`Γ(X, 𝒪_X)` is the integral closure of `R` in the function field of `X`. Since the description
holds over every affine open of the base, it determines the pushforward `f_* 𝒪_X`. No flatness,
finiteness or Noetherian hypothesis is needed.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- On an integral scheme, the sections over a nonempty open subset `U` whose local rings are
integrally closed form a ring integrally closed in the function field. -/
theorem isIntegrallyClosedIn_functionField (U : X.Opens) [Nonempty U]
    (hU : ∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosedIn Γ(X, U) X.functionField := by
  refine isIntegrallyClosedIn_iff.mpr ⟨X.germToFunctionField_injective U, fun {a} ha ↦ ?_⟩
  -- A rational function lying in every local ring of `U` is a section over `U`.
  refine TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range
    fun y hy ↦ ?_
  let y' : U := ⟨y, hy⟩
  have := hU y hy
  -- The `Γ(X, U)`-algebra structure on the stalk is not found by instance search here.
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf y'
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk y') X.functionField :=
    functionField_isScalarTower X U y'
  have hay : _root_.IsIntegral (X.presheaf.stalk y') a := ha.tower_top
  exact IsIntegrallyClosed.isIntegral_iff.mp hay

variable {X}

/-- **Functions on a normal scheme universally closed over an affine open.** Let `f : X ⟶ Y` be
universally closed with `X` integral, and let `V ⊆ Y` be an affine open with nonempty preimage
along which the local rings of `X` are integrally closed. A rational function on `X` is a
function on `f⁻¹V` if and only if it is integral over `Γ(Y, V)`. -/
theorem Hom.mem_range_germToFunctionField_iff {Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] {V : Y.Opens} (hV : IsAffineOpen V) [Nonempty (f ⁻¹ᵁ V)]
    (hX : ∀ x ∈ f ⁻¹ᵁ V, IsIntegrallyClosed (X.presheaf.stalk x)) (a : X.functionField) :
    a ∈ (X.germToFunctionField (f ⁻¹ᵁ V)).hom.range ↔
      (f.app V ≫ X.germToFunctionField (f ⁻¹ᵁ V)).hom.IsIntegralElem a := by
  refine ⟨?_, fun ha ↦ ?_⟩
  · rintro ⟨b, rfl⟩
    exact (f.isIntegral_app_of_universallyClosed hV b).map _
  · have := X.isIntegrallyClosedIn_functionField (f ⁻¹ᵁ V) hX
    exact IsIntegrallyClosedIn.algebraMap_eq_of_integral (RingHom.IsIntegralElem.of_comp ha)

/-- **Global functions on a normal scheme universally closed over an affine scheme.** If `X` is
a normal integral scheme and `f : X ⟶ Y` is universally closed with `Y` affine, a rational
function on `X` is a global function if and only if it is integral over `Γ(Y, ⊤)`. -/
theorem Hom.mem_range_germToFunctionField_top_iff {Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    [UniversallyClosed f] [TauCeti.AlgebraicGeometry.IsNormalScheme X] (a : X.functionField) :
    a ∈ (X.germToFunctionField ⊤).hom.range ↔
      (f.appTop ≫ X.germToFunctionField ⊤).hom.IsIntegralElem a := by
  have : Nonempty (f ⁻¹ᵁ ⊤) := inferInstanceAs (Nonempty (⊤ : X.Opens))
  exact f.mem_range_germToFunctionField_iff (isAffineOpen_top Y) (fun _ _ ↦ inferInstance) a

end AlgebraicGeometry.Scheme
