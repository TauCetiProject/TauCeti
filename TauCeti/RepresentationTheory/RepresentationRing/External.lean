/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.RepresentationRing.Restriction
public import TauCeti.RepresentationTheory.FDRep.External

/-!
# The external tensor product of representation rings

For monoids `G` and `H` over a field `k`, the external tensor product `V ⊠ W` of a
finite-dimensional representation `V` of `G` and a representation `W` of `H` is the representation
of `G × H` on `V ⊗ W` in which `(g, h)` acts by `ρ_V g ⊗ ρ_W h`
(`Representation.externalTensor`). It is the tensor product, over `G × H`, of the pullbacks of
`V` and `W` along the two projections. This file passes it to the representation rings of
`TauCeti/RepresentationTheory/RepresentationRing/Basic.lean`, as the biadditive map

`TauCeti.repRingExternalTensor k G H : R(G) →+ R(H) →+ R(G × H)`,

`x ⊠ y = res_{pr₁} x * res_{pr₂} y`, the product in `R(G × H)` of the restrictions along the two
projections (`TauCeti.repRingRes`). On classes it is the class of the external tensor product of
representations (`TauCeti.repRingExternalTensor_of_of`), through the comparison
`FDRep.externalTensorIso` of `TauCeti/RepresentationTheory/FDRep/External.lean`. Since
restrictions are ring homomorphisms, it is compatible with the ring structures,
`(x * x') ⊠ (y * y') = (x ⊠ y) * (x' ⊠ y')` and `1 ⊠ 1 = 1`, with restriction along products
of homomorphisms, `res_{φ × ψ} (x ⊠ y) = res_φ x ⊠ res_ψ y`, and it recovers the product of
`R(G)` along the diagonal, `res_Δ (x ⊠ y) = x * y`. Its character at `(g, h)` is the product of
the characters at `g` and at `h`.

The external tensor product of representation rings is the coefficient map of the external product
of equivariant K-theory and of the multiplicativity of the equivariant index, where the index of
the external product of a `G`-equivariant and an `H`-equivariant elliptic operator is the external
product of their indices in `R(G × H)`.

## Main definitions

* `TauCeti.repRingExternalTensor`: the external tensor product `R(G) →+ R(H) →+ R(G × H)`.

## Main statements

* `TauCeti.repRingExternalTensor_of_of`: `[V] ⊠ [W]` is the class of the external tensor product.
* `TauCeti.repRingExternalTensor_mul_mul` and `TauCeti.repRingExternalTensor_one_one`:
  compatibility with the ring structures.
* `TauCeti.repRingRes_prodMap_repRingExternalTensor`: restriction along `φ × ψ`.
* `TauCeti.repRingRes_prod_id_id_repRingExternalTensor`: restriction along the diagonal is the
  product of `R(G)`.
* `TauCeti.repRingCharacter_repRingExternalTensor_apply`: the character at `(g, h)` is
  `χ_x(g) χ_y(h)`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §3.2, for the
  external tensor product of representations of a product group and its character.
* G. Segal, *Equivariant K-theory*, Publ. Math. IHÉS 34 (1968), §2, for the representation ring
  `R(G)` as the coefficient ring of equivariant K-theory.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u v v' w w'

variable {k : Type u} [Field k] {G : Type v} {H : Type v'} [Monoid G] [Monoid H]

variable (k G H) in
/-- **The external tensor product of representation rings**, the biadditive map
`R(G) →+ R(H) →+ R(G × H)` sending `(x, y)` to the product in `R(G × H)` of the restrictions of
`x` and `y` along the two projections. On classes of representations it is the class of their
external tensor product (`TauCeti.repRingExternalTensor_of_of`). -/
noncomputable def repRingExternalTensor : repRing k G →+ repRing k H →+ repRing k (G × H) :=
  (AddMonoidHom.mul.comp (repRingRes k (MonoidHom.fst G H)).toAddMonoidHom).compl₂
    (repRingRes k (MonoidHom.snd G H)).toAddMonoidHom

/-- The external tensor product is the product of the restrictions along the two projections. -/
theorem repRingExternalTensor_apply (x : repRing k G) (y : repRing k H) :
    repRingExternalTensor k G H x y =
      repRingRes k (MonoidHom.fst G H) x * repRingRes k (MonoidHom.snd G H) y :=
  (rfl)

/-- The external tensor product of the classes of two representations is the class of their
external tensor product: the pullbacks of `V` and `W` along the two projections, tensored over
`G × H`, are the representation `(g, h) ↦ ρ_V g ⊗ ρ_W h` on `V ⊗ W`. -/
@[simp]
theorem repRingExternalTensor_of_of (V : FDRep k G) (W : FDRep k H) :
    repRingExternalTensor k G H (SplitK0.of V) (SplitK0.of W) =
      SplitK0.of (FDRep.of (Representation.externalTensor V.ρ W.ρ)) := by
  rw [repRingExternalTensor_apply, repRingRes_of, repRingRes_of, SplitK0.of_mul_of]
  exact SplitK0.of_congr (FDRep.externalTensorIso V W)

/-- **The external tensor product is multiplicative** in both variables at once:
`(x * x') ⊠ (y * y') = (x ⊠ y) * (x' ⊠ y')`. -/
theorem repRingExternalTensor_mul_mul (x x' : repRing k G) (y y' : repRing k H) :
    repRingExternalTensor k G H (x * x') (y * y') =
      repRingExternalTensor k G H x y * repRingExternalTensor k G H x' y' := by
  simp only [repRingExternalTensor_apply, map_mul]
  ring

/-- The external tensor product of the units is the unit: the external tensor product of two
trivial lines is the trivial line. -/
@[simp]
theorem repRingExternalTensor_one_one : repRingExternalTensor k G H 1 1 = 1 := by
  simp [repRingExternalTensor_apply]

/-- **Restriction along a product of homomorphisms**: restricting `x ⊠ y` along `φ × ψ` is the
external tensor product of the restrictions of `x` along `φ` and of `y` along `ψ`. -/
theorem repRingRes_prodMap_repRingExternalTensor {G' : Type w} {H' : Type w'} [Monoid G']
    [Monoid H'] (φ : G' →* G) (ψ : H' →* H) (x : repRing k G) (y : repRing k H) :
    repRingRes k (φ.prodMap ψ) (repRingExternalTensor k G H x y) =
      repRingExternalTensor k G' H' (repRingRes k φ x) (repRingRes k ψ y) := by
  have hfst : (MonoidHom.fst G H).comp (φ.prodMap ψ) = φ.comp (MonoidHom.fst G' H') :=
    MonoidHom.ext fun _ ↦ rfl
  have hsnd : (MonoidHom.snd G H).comp (φ.prodMap ψ) = ψ.comp (MonoidHom.snd G' H') :=
    MonoidHom.ext fun _ ↦ rfl
  simp only [repRingExternalTensor_apply, map_mul, ← RingHom.comp_apply, ← repRingRes_comp, hfst,
    hsnd]

/-- **Along the diagonal the external tensor product is the product**: restricting `x ⊠ y` along
`g ↦ (g, g)` gives `x * y`, as the internal tensor product of two representations of `G` is the
restriction of their external tensor product to the diagonal. -/
@[simp]
theorem repRingRes_prod_id_id_repRingExternalTensor (x y : repRing k G) :
    repRingRes k ((MonoidHom.id G).prod (MonoidHom.id G)) (repRingExternalTensor k G G x y) =
      x * y := by
  simp only [repRingExternalTensor_apply, map_mul, ← RingHom.comp_apply, ← repRingRes_comp,
    MonoidHom.fst_comp_prod, MonoidHom.snd_comp_prod, repRingRes_id, RingHom.id_apply]

/-- **The character of an external tensor product** at `(g, h)` is the product of the characters
at `g` and at `h`. -/
@[simp]
theorem repRingCharacter_repRingExternalTensor_apply (x : repRing k G) (y : repRing k H)
    (p : G × H) :
    repRingCharacter k (G × H) (repRingExternalTensor k G H x y) p =
      repRingCharacter k G x p.1 * repRingCharacter k H y p.2 := by
  simp [repRingExternalTensor_apply]

end TauCeti
