/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Bundling discrete continuous modules over a discrete ring

`TauCeti.DiscreteRep` carries an explicit `ContinuousSMul R V` field so that topological rings
such as `ℤ_p` can act continuously on discrete torsion modules. When the scalar ring `R` itself
carries the discrete topology (for instance `ℤ` or `ZMod n`), scalar multiplication on any discrete
`R`-module `M` is automatically continuous.

This file provides `TauCeti.DiscreteRep.of` and `TauCeti.SmoothDiscreteTopRep.of`, bundling a
discrete `R`-module `M` with continuous `G`-action directly into `TauCeti.DiscreteRep R G` and
`TauCeti.SmoothDiscreteTopRep R G` without requiring a separate `ContinuousSMul R M` hypothesis.
-/

public section

universe u v w

namespace TauCeti

section DiscreteRing

variable (R : Type u) [Ring R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type v) [Monoid G] [TopologicalSpace G]
  (M : Type w) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [SMulCommClass G R M] [ContinuousSMul G M]

/-- A discrete `R`-module `M` with continuous `G`-action over a discrete ring `R`, bundled as an
object of `TauCeti.DiscreteRep R G`. Continuity of scalar multiplication by `R` holds automatically
because both `R` and `M` carry the discrete topology. -/
abbrev DiscreteRep.of : DiscreteRep.{u, v, w} R G where
  V := M
  continuousSMulRing := ⟨continuous_of_discreteTopology⟩

/-- The underlying module of `DiscreteRep.of R G M` is `M`. -/
theorem DiscreteRep.of_V : (DiscreteRep.of R G M).V = M := (rfl)

/-- The representation of `DiscreteRep.of R G M` is `Representation.ofDistribMulAction R G M`. -/
theorem DiscreteRep.of_ρ :
    (DiscreteRep.of R G M).ρ = Representation.ofDistribMulAction R G M := (rfl)

/-- A discrete `R`-module `M` with continuous `G`-action over a discrete ring `R`, bundled as an
object of `TauCeti.SmoothDiscreteTopRep R G` via `toSmoothDiscrete` and `DiscreteRep.of`. -/
abbrev SmoothDiscreteTopRep.of : SmoothDiscreteTopRep.{u, v, w} R G :=
  (toSmoothDiscrete R G).obj (DiscreteRep.of R G M)

/-- The underlying `TopRep` of `SmoothDiscreteTopRep.of R G M` is `ofDiscreteModule R G M`. -/
theorem SmoothDiscreteTopRep.of_obj :
    letI : ContinuousSMul R M := ⟨continuous_of_discreteTopology⟩
    (SmoothDiscreteTopRep.of R G M).obj = ofDiscreteModule R G M := (rfl)

/-- The underlying module of `(SmoothDiscreteTopRep.of R G M).obj` is `M`. -/
theorem SmoothDiscreteTopRep.of_V : (SmoothDiscreteTopRep.of R G M).obj.V = M := (rfl)

end DiscreteRing

end TauCeti
