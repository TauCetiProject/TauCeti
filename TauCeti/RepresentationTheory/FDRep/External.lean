/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Action.Monoidal
public import TauCeti.RepresentationTheory.Tensor.External

/-!
# The external tensor product of finite-dimensional representations as a tensor product

For monoids `G` and `H` over a field `k`, the external tensor product `V ⊠ W` of a
finite-dimensional representation `V` of `G` and a representation `W` of `H` is the representation
of `G × H` on `V ⊗ W` in which `(g, h)` acts by `ρ_V g ⊗ ρ_W h`
(`Representation.externalTensor`). This file identifies it, in the monoidal category
`FDRep k (G × H)`, with the tensor product of the restrictions of `V` and `W` along the two
projections of `G × H`. The comparison is the identity of `V ⊗ W`.

## Main definitions

* `FDRep.externalTensorIso`: the external tensor product of `V` and `W` is the tensor product over
  `G × H` of their restrictions along the two projections.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §3.2, for the
  external tensor product of representations of a product group.
-/

public section

open CategoryTheory MonoidalCategory

namespace FDRep

universe u v v'

variable {k : Type u} [Field k] {G : Type v} {H : Type v'} [Monoid G] [Monoid H]

/-- **The external tensor product as a tensor product over `G × H`**: the tensor product of the
restrictions of `V` and `W` along the two projections of `G × H` is the external tensor product
`(g, h) ↦ ρ_V g ⊗ ρ_W h` on `V ⊗ W`. The two objects have the same carrier, and the isomorphism is
the identity of `V ⊗ W`. -/
noncomputable def externalTensorIso (V : FDRep k G) (W : FDRep k H) :
    (Action.res (FGModuleCat.{u} k) (MonoidHom.fst G H)).obj V ⊗
        (Action.res (FGModuleCat.{u} k) (MonoidHom.snd G H)).obj W ≅
      FDRep.of (Representation.externalTensor V.ρ W.ρ) :=
  Action.mkIso (Iso.refl _) fun p ↦ FGModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
    -- `change` reads both sides through the linear maps `FDRep.ρ`: the action on the left is
    -- stated through `Action.ρ` and the endomorphism ring equivalences of `FGModuleCat`, which
    -- `simp` does not unfold, and the restrictions act through `p.1` and `p.2` by definition.
    change TensorProduct.map (V.ρ p.1) (W.ρ p.2) x =
      (FDRep.of (Representation.externalTensor V.ρ W.ρ)).ρ p x
    rw [FDRep.of_ρ', Representation.externalTensor_apply]

/-- The isomorphism `FDRep.externalTensorIso` is the identity of `V ⊗ W`. -/
theorem externalTensorIso_hom_apply (V : FDRep k G) (W : FDRep k H)
    (x : TensorProduct k V W) : (externalTensorIso V W).hom.hom.hom x = x :=
  (rfl)

/-- The inverse of `FDRep.externalTensorIso` is the identity of `V ⊗ W`. -/
theorem externalTensorIso_inv_apply (V : FDRep k G) (W : FDRep k H)
    (x : TensorProduct k V W) : (externalTensorIso V W).inv.hom.hom x = x :=
  (rfl)

end FDRep
