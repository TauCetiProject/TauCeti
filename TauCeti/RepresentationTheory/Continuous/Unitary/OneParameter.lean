/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Unitary
public import TauCeti.RepresentationTheory.Continuous.OneParameter
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Unitary representations of the real line as unitary C₀-groups

When `π` is a strongly continuous complex unitary representation of `Multiplicative ℝ`, its
one-parameter group `ContRepresentation.toStronglyContinuousGroup` is unitary,
`ContRepresentation.IsUnitary.isUnitary_toStronglyContinuousGroup`. This makes the generator
theory of unitary groups, in particular the self-adjoint Stone generator
`StronglyContinuousGroup.stoneGenerator` with `π (ofAdd t) = exp (i t H)`, available for unitary
representations of `ℝ`.
-/

public section

open TauCeti.Semigroups
open scoped InnerProductSpace

namespace ContRepresentation

/-- The one-parameter group of a strongly continuous unitary representation of `ℝ` is unitary. -/
theorem IsUnitary.isUnitary_toStronglyContinuousGroup {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : ContRepresentation ℂ (Multiplicative ℝ) H} (hπ : π.IsUnitary)
    (hc : ∀ v, Continuous fun g => π g v) : (π.toStronglyContinuousGroup hc).IsUnitary :=
  .intro fun t v w => by simpa using hπ.inner_map_map (Multiplicative.ofAdd t) v w

end ContRepresentation
