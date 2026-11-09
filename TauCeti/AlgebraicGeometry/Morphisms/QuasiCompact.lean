/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Quasi-compact morphisms

Every point of the target of a quasi-compact morphism of schemes has an open neighbourhood whose
preimage is quasi-compact (`Scheme.Hom.exists_isOpen_mem_isCompact_preimage`): an affine open
neighbourhood will do.

A morphism of `S`-schemes from a scheme with quasi-compact structure map to one with
quasi-separated structure map is quasi-compact
(`AlgebraicGeometry.quasiCompact_left_of_quasiCompact_hom`).
-/

public section

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- Every point of the target of a quasi-compact morphism has an open neighbourhood, for instance
an affine one, whose preimage is quasi-compact. -/
lemma exists_isOpen_mem_isCompact_preimage (y : Y) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ IsCompact (f ⁻¹' U) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact ⟨U, U.isOpen, hyU, QuasiCompact.isCompact_preimage (f := f) _ U.isOpen hU.isCompact⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

open CategoryTheory

/-- A morphism of `S`-schemes from a scheme with quasi-compact structure map to one with
quasi-separated structure map has quasi-compact underlying map. -/
theorem quasiCompact_left_of_quasiCompact_hom {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U)
    [QuasiCompact T.hom] [QuasiSeparated U.hom] : QuasiCompact f.left := by
  have : QuasiCompact (f.left ≫ U.hom) := by
    rw [Over.w f]
    infer_instance
  exact QuasiCompact.of_comp f.left U.hom

end AlgebraicGeometry
