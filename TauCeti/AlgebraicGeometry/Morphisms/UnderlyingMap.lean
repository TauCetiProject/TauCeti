/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Surjectivity of morphisms out of coproducts

A morphism `∐ᵢ Yᵢ ⟶ X` out of a nonempty coproduct of schemes is surjective when each component
`Yᵢ ⟶ X` is (`AlgebraicGeometry.surjective_sigmaDesc`). This follows from Mathlib's
`AlgebraicGeometry.Surjective.sigmaDesc_of_union_range_eq_univ`, stated as an instance; it applies,
for example, to the fold map `∐_{i : ι} U ⟶ U` for nonempty `ι`.
-/

public section

open CategoryTheory Limits

universe v u

namespace AlgebraicGeometry

/-- A morphism `∐ᵢ Yᵢ ⟶ X` out of a nonempty coproduct is surjective if each of its components
`Yᵢ ⟶ X` is. -/
instance surjective_sigmaDesc {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] [Nonempty ι]
    {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X} [∀ i, Surjective (f i)] :
    Surjective (Sigma.desc f) :=
  Surjective.sigmaDesc_of_union_range_eq_univ <| by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨i, (f i).surjective x⟩

end AlgebraicGeometry
