/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.FiniteModuleTopology

/-!
# Strict morphisms out of a finite module over a Tate ring

Let `A` be a complete Hausdorff Tate ring, let `M` be a finite `A`-module and let `N` be a
noetherian `A`-module, each carrying a complete Hausdorff first-countable topology making it a
topological `A`-module. This file proves that every linear map `M →ₗ[A] N` is strict: it is open
onto its image, and in particular continuous, with no continuity hypothesis imposed on it. This is
[Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(2).

Wedhorn states the target side as a finite module over a noetherian ring; that case is the
instance `isNoetherian_of_isNoetherianRing_of_finite` of the noetherian target asked for here.

The strictness of a morphism is what makes a presentation of a module by finite free modules a
topological presentation, so this is the result that lets finite modules over a noetherian Tate
ring — where finiteness of the target already gives the noetherian hypothesis — be glued and
localised topologically. The open mapping theorem it rests on is Henkel's, credited in
`TauCeti.RingTheory.Huber.OpenMapping`.

## Main result

* `LinearMap.isStrictMap_of_module_finite`: a linear map from a finite module to a noetherian
  module, over a complete Hausdorff Tate ring, is strict.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(2).
-/

public section

open Filter Topology
open scoped Uniformity

namespace LinearMap

variable {A M N : Type*}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A]
  [(𝓤 A).IsCountablyGenerated] [IsTopologicalRing A] [TauCeti.Huber.IsTateRing A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓤 M).IsCountablyGenerated] [T0Space M]
  [Module A M] [ContinuousSMul A M] [Module.Finite A M]
  [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [CompleteSpace N]
  [(𝓤 N).IsCountablyGenerated] [T0Space N]
  [Module A N] [ContinuousSMul A N] [IsNoetherian A N]

/-- **A linear map from a finite module to a noetherian module over a complete Tate ring is
strict** ([Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(2)): it is open onto its image.

No continuity hypothesis is imposed on `f`; continuity is part of the conclusion, obtained from
it by `Topology.IsStrictMap.continuous`. -/
theorem isStrictMap_of_module_finite (f : M →ₗ[A] N) : Topology.IsStrictMap f := by
  let _ : IsModuleTopology A M := TauCeti.Huber.IsTateRing.isModuleTopology
  let _ : NonarchimedeanAddGroup M := by
    rw [_root_.eq_moduleTopology A M]
    exact TauCeti.nonarchimedeanAddGroup_moduleTopology
  have hcont : Continuous f := IsModuleTopology.continuous_of_linearMap f
  exact TauCeti.Huber.IsTateRing.isStrictMap_of_isClosed_range f hcont.continuousAt
    (TauCeti.Huber.isClosed_of_isNoetherian (LinearMap.range f))

end LinearMap

end
