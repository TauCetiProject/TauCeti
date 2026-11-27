/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import TauCeti.AlgebraicGeometry.Cohomology.Support
public import TauCeti.AlgebraicGeometry.Modules.Unit

/-!
# Supported functions on an integral scheme

On an integral scheme `X`, restriction of functions to a nonempty open is injective, so a global
function supported in a closed subset `Z ≠ X` vanishes: `Γ_Z(X, 𝒪_X) = 0` and
`H⁰_Z(X, 𝒪_X) = 0`.

## Main declarations

* `Scheme.Modules.sectionsWithSupport_unit_eq_bot`: `Γ_Z(X, 𝒪_X) = 0` for `Z ≠ X`.
* `Scheme.Modules.subsingleton_cohomologyWithSupport_zero_unit`: `H⁰_Z(X, 𝒪_X) = 0` for `Z ≠ X`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

/-- On an integral scheme, a global function supported in a closed subset `Z ≠ X` vanishes. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.sectionsWithSupport_unit_eq_bot (Z : Closeds X)
    (hZ : (Z : Set X) ≠ Set.univ) : (Scheme.Modules.unit X).sectionsWithSupport Z = ⊥ := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 hZ
  have : Nonempty ((⊤ : X.Opens) ⊓ Z.compl : X.Opens) := ⟨⟨x, trivial, hx⟩⟩
  refine (Submodule.eq_bot_iff _).2 fun s hs ↦
    map_injective_of_isIntegral (X := X) (Z.complInclusion ⊤) ?_
  rw [Scheme.Modules.mem_sectionsWithSupport_iff] at hs
  -- The restriction maps of the abelian sheaf underlying `𝒪_X` are by definition those of the
  -- structure sheaf `X.presheaf` (compare `Scheme.Modules.presheaf_unit_map_apply`).
  change X.presheaf.map (Z.complInclusion ⊤).op s = 0 at hs
  exact hs.trans (map_zero _).symm

/-- On an integral scheme, `H⁰_Z(X, 𝒪_X) = 0` for every closed subset `Z ≠ X`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyWithSupport_zero_unit
    (Z : Closeds X) (hZ : (Z : Set X) ≠ Set.univ) :
    Subsingleton ((Scheme.Modules.unit X).cohomologyWithSupport Z ⊤ 0) := by
  have : Subsingleton ((Scheme.Modules.unit X).sectionsWithSupport Z) := by
    rw [Scheme.Modules.sectionsWithSupport_unit_eq_bot Z hZ]
    infer_instance
  exact ((Scheme.Modules.unit X).cohomologyWithSupportZeroLinearEquiv Z).toEquiv.subsingleton

end TauCeti.AlgebraicGeometry
