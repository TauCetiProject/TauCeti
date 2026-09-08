/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.FiniteModuleTopology

/-!
# Strict morphisms between finite modules over a Tate ring

Let `A` be a complete Hausdorff noetherian Tate ring, and let `M` and `N` be finite `A`-modules
with complete Hausdorff first-countable module topologies. This file proves that every linear map
`M →ₗ[A] N` is continuous and strict: it is open onto its image. This is
[Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(2).

The two conclusions use different halves of the preceding finite-module theory. The topology on
`M` is forced to be Mathlib's `moduleTopology A M` by
`TauCeti.Huber.IsTateRing.isModuleTopology`; hence every linear map out of `M` is continuous.
Noetherianity makes the range, as a submodule of `N`, closed by
`TauCeti.Huber.isClosed_of_isNoetherian`. The open mapping theorem applied to the range
restriction then makes the map strict.

Henkel's open mapping theorem needs the source additive group to be nonarchimedean. That is not an
extra hypothesis here: once the source topology is identified with `moduleTopology A M`, it
follows from `TauCeti.nonarchimedeanAddGroup_moduleTopology`. Thus the statement has exactly the
complete, Hausdorff, first-countable topological hypotheses of the roadmap's derived form.

## Main result

* `LinearMap.isStrictMap_of_module_finite`: every linear map between finite complete
  metrisable modules over a complete Hausdorff noetherian Tate ring is strict, and hence
  continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(2).
-/

public section

open Filter Topology
open scoped Uniformity

namespace LinearMap

variable {A M N : Type*}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A]
  [(𝓤 A).IsCountablyGenerated] [NonarchimedeanRing A] [TauCeti.Huber.IsTateRing A]
  [IsNoetherianRing A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓤 M).IsCountablyGenerated] [T0Space M]
  [Module A M] [ContinuousSMul A M] [Module.Finite A M]
  [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N] [CompleteSpace N]
  [(𝓤 N).IsCountablyGenerated] [T0Space N]
  [Module A N] [ContinuousSMul A N] [Module.Finite A N]

/-- **Linear maps between finite modules over a complete noetherian Tate ring are strict**
([Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(2)).

The supplied complete Hausdorff first-countable topology on the finite source is necessarily the
module topology, so `f` is continuous without a continuity hypothesis. Its range is a submodule
of the noetherian target and is therefore closed. The open mapping theorem, applied to the range
restriction, then says exactly that `f` is strict, i.e. open onto its image.

Continuity follows from the conclusion by `Topology.IsStrictMap.continuous`. -/
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
