/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants
public import TauCeti.Algebra.HopfAlgebra.TensorShear

/-!
# The canonical map over the coinvariants of a Hopf ideal

For a Hopf ideal `I` in a commutative Hopf algebra `H`, put `B = I.coinvariants`.
The canonical map

```text
H ⊗[B] H → H ⊗[R] (H / I),    a ⊗ b ↦ (a ⊗ 1) (id ⊗ π)(Δ b)
```

is an `H`-algebra homomorphism and is surjective. Geometrically, this says that
`(g, n) ↦ (g, gn)` is a closed immersion from `G × N` into
`G ×_{Spec B} G`. This supplies the surjectivity part of the canonical-map criterion
for a quotient torsor; injectivity and faithful flatness are separate questions.
Neither normality of `I` nor flatness over the base is needed here.

The proof factors the map on the absolute tensor square through the tensor shear
and `id ⊗ π`, both of which are surjective.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open scoped TensorProduct
open Algebra.TensorProduct

namespace TauCeti.HopfIdeal

variable {R H : Type*} [CommSemiring R] [CommRing H] [HopfAlgebra R H]

/-- The quotient coaction regarded as a map over the coinvariant subalgebra. -/
private noncomputable def coinvariantCoaction (I : HopfIdeal R H) :
    H →ₐ[I.coinvariants] H ⊗[R] (H ⧸ I.toIdeal) where
  toRingHom := ((Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)).comp
    (Bialgebra.comulAlgHom R H)).toRingHom
  commutes' b := mem_coinvariants_iff.mp b.property

/-- The canonical map for a Hopf quotient, with the tensor product balanced over
the coinvariant subalgebra. It is linear over the first copy of `H`. -/
noncomputable def canonicalMap (I : HopfIdeal R H) :
    H ⊗[I.coinvariants] H →ₐ[H] H ⊗[R] (H ⧸ I.toIdeal) :=
  lift (Algebra.ofId H _) (coinvariantCoaction I) (fun _ _ ↦ .all _ _)

/-- On pure tensors the canonical map multiplies the left factor by the quotient
coaction of the right factor. -/
@[simp]
theorem canonicalMap_tmul (I : HopfIdeal R H) (a b : H) :
    I.canonicalMap (a ⊗ₜ[I.coinvariants] b) =
      (a ⊗ₜ[R] 1) * Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)
        (Coalgebra.comul (R := R) b) := by
  simp [canonicalMap, coinvariantCoaction]

/-- The absolute tensor-square map factors through balancing over the coinvariants.
Its other factorization is the tensor shear followed by the quotient in the second
factor. -/
theorem canonicalMap_comp_mapOfCompatibleSMul (I : HopfIdeal R H) :
    (I.canonicalMap.restrictScalars R).comp
        (mapOfCompatibleSMul I.coinvariants R R H H) =
      (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)).comp
        (HopfAlgebra.tensorShear (R := R)).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp

/-- The canonical map over the coinvariants of any Hopf ideal is surjective.
No normality or flatness hypothesis is required. -/
theorem canonicalMap_surjective (I : HopfIdeal R H) :
    Function.Surjective I.canonicalMap := by
  have hmap : Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)) :=
    TensorProduct.map_surjective (g := (AlgHom.id R H).toLinearMap)
      (g' := (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap)
      Function.surjective_id Ideal.Quotient.mk_surjective
  intro z
  obtain ⟨x, rfl⟩ := hmap z
  refine ⟨mapOfCompatibleSMul I.coinvariants R R H H
    ((HopfAlgebra.tensorShear (R := R)).symm x), ?_⟩
  simpa using AlgHom.congr_fun (canonicalMap_comp_mapOfCompatibleSMul I)
    ((HopfAlgebra.tensorShear (R := R)).symm x)

end TauCeti.HopfIdeal
