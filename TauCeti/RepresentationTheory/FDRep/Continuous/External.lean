/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Continuous.Restriction
public import TauCeti.RepresentationTheory.FDRep.External

/-!
# The external tensor product of continuous finite-dimensional representations

For topological monoids `G` and `H` over a topological field `k`, the external tensor product
`V ⊠ W` of continuous finite-dimensional representations of `G` and `H`, on which `(g, h)` acts by
`ρ_V g ⊗ ρ_W h`, is again continuous (`FDRep.isContinuous_externalTensor`): by
`FDRep.externalTensorIso` it is the tensor product over `G × H` of the restrictions of `V` and `W`
along the two continuous projections, and continuity is preserved by restriction and by tensor
products.

## Main statements

* `FDRep.isContinuous_externalTensor`: the external tensor product of continuous representations
  is continuous.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §3.2, for the
  external tensor product of representations of a product group.
-/

public section

universe u v v'

namespace FDRep

variable {k : Type u} [Field k] [TopologicalSpace k] [ContinuousAdd k] [ContinuousMul k]
  {G : Type v} {H : Type v'} [Monoid G] [TopologicalSpace G] [Monoid H] [TopologicalSpace H]

/-- **The external tensor product of continuous representations is continuous**: it is the tensor
product over `G × H` of their restrictions along the two continuous projections. -/
theorem isContinuous_externalTensor {V : FDRep k G} {W : FDRep k H} (hV : isContinuous k G V)
    (hW : isContinuous k H W) :
    isContinuous k (G × H) (FDRep.of (Representation.externalTensor V.ρ W.ρ)) :=
  (isContinuous k (G × H)).prop_of_iso (externalTensorIso V W)
    (isContinuous_tensor (isContinuous_res continuous_fst hV) (isContinuous_res continuous_snd hW))

end FDRep
