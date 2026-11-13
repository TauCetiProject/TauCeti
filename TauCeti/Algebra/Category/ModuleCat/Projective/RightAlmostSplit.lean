/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Jacobson.Radical
public import TauCeti.CategoryTheory.AlmostSplit.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Projective
import TauCeti.Algebra.Module.ProjectiveCover.Simple
import TauCeti.LinearAlgebra.End.Basic

/-!
# The right almost split map into an indecomposable projective module

Let `P` be a finitely generated projective module with a local endomorphism ring. A morphism into
`P` that is not a split epimorphism is not surjective, so its image is a proper submodule of `P`
and lies in the radical of `P` (`TauCeti.le_jacobson_of_ne_top_of_isLocalRing_end`). Hence the
inclusion `rad P ⟶ P` is right almost split in the category of all `A`-modules
(`TauCeti.isRightAlmostSplit_ofHom_subtype_jacobson`).

Indecomposable projective modules end no almost-split sequence, and this is the right almost split
map that takes the place of such a sequence at them. It is the dual of the quotient of an
indecomposable injective module by its socle, `TauCeti.exists_isAtom_isLeftAlmostSplit_ofHom_mkQ`.
The same map is right almost split in `FGModuleCat` when the radical is finitely generated
(`FGModuleCat.isRightAlmostSplit_ofHom_subtype_jacobson`).

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe v w

variable {A : Type v} [Ring A] {P : ModuleCat.{w} A} [Module.Projective A P] [Module.Finite A P]
  [IsLocalRing (End P)]

/-- **The sink map of a projective module.** For a finitely generated projective module `P` with a
local endomorphism ring, the inclusion `rad P ⟶ P` is right almost split. -/
theorem isRightAlmostSplit_ofHom_subtype_jacobson :
    IsRightAlmostSplit (ModuleCat.ofHom (Module.jacobson A P).subtype) := by
  have : IsLocalRing (Module.End A P) := P.endRingEquiv.isLocalRing
  have : Nontrivial P := nontrivial_of_nontrivial_end (R := A) (M := P)
  refine isRightAlmostSplit_iff.2 ⟨fun _ ↦ (Module.jacobson_lt_top A P).ne ?_, fun W g hg ↦ ?_⟩
  · -- A split epimorphism is surjective.
    rw [← Submodule.range_subtype (Module.jacobson A P)]
    exact ModuleCat.range_eq_top_of_epi (ModuleCat.ofHom (Module.jacobson A P).subtype)
  · -- A morphism onto `P` splits, since `P` is projective.
    have hrange : LinearMap.range g.hom ≠ ⊤ := fun htop ↦ hg <| by
      have : Epi g := (ModuleCat.epi_iff_range_eq_top g).mpr htop
      exact .mk' ⟨Projective.factorThru (𝟙 P) g, Projective.factorThru_comp (𝟙 P) g⟩
    have hle := le_jacobson_of_ne_top_of_isLocalRing_end hrange
    exact ⟨ModuleCat.ofHom (g.hom.codRestrict _ fun x ↦ hle ⟨x, rfl⟩), by ext; rfl⟩

end TauCeti
