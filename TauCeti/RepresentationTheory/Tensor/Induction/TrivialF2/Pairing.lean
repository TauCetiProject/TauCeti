/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.TrivialF2.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic

/-!
# Multiplication under the trivial F₂ tensor-induction comparison

The coefficient identification `TauCeti.smoothTensorInducedTrivialF2Iso` multiplies the tensor
factors. It carries the factorwise multiplication pairing to `TauCeti.trivialF2TopPairing` of
the ambient group. Thus the pairing used for a product of tensor-induced cohomology classes
agrees with the canonical mod-two cup pairing after identifying the coefficients.

`TauCeti.smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_map₂` states this as an
equation on arbitrary tensors, rather than only on pure tensors. For pure tensors it is the identity
`∏ i, (a i * b i) = (∏ i, a i) * (∏ i, b i)` in `ZMod 2`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6, Proposition 1, for multiplicativity of the norm.
-/

public section

namespace TauCeti

open scoped TensorProduct

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]

-- Use the coefficient objects' own integer modules instead of the fallback additive-group ones.
attribute [local instance 1100] DiscreteRep.module
attribute [local instance 1200] TopRep.hV2

/-- The canonical identification of tensor-induced trivial `𝔽₂` coefficients preserves the
factorwise multiplication pairing. This is the coefficient compatibility needed to transport
cup products from tensor-induced coefficients to the canonical trivial coefficients. -/
theorem smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_map₂
    (a b : ⨂[ℤ] _ : G ⧸ U, (DiscreteRep.trivialF2 U).V) :
    (smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom
        (PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ (trivialF2TopPairing U).bil) a b) =
      (trivialF2TopPairing G).bil
        ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom a)
        ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom b) := by
  classical
  let : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  -- Give the maps their tensor-module types explicitly. The smooth/discrete dictionary
  -- preserves carriers, but rewriting cannot unfold its sealed coefficient objects.
  let e : (⨂[ℤ] _ : G ⧸ U, (trivialF2 U).V) →ₗ[ℤ] (trivialF2 G).V :=
    (smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom.toLinearMap
  let f : (⨂[ℤ] _ : G ⧸ U, (trivialF2 U).V) →ₗ[ℤ]
      (⨂[ℤ] _ : G ⧸ U, (trivialF2 U).V) →ₗ[ℤ]
        ⨂[ℤ] _ : G ⧸ U, (trivialF2 U).V :=
    PiTensorProduct.map₂ fun _ : G ⧸ U ↦ (trivialF2TopPairing U).bil
  have he (x : G ⧸ U → (trivialF2 U).V) :
      trivialF2Equiv G (e (PiTensorProduct.tprod ℤ x)) =
        ∏ i, trivialF2Equiv U (x i) :=
    smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod G U hU s x
  have hf (x y : G ⧸ U → (trivialF2 U).V) :
      f (PiTensorProduct.tprod ℤ x) (PiTensorProduct.tprod ℤ y) =
        PiTensorProduct.tprod ℤ fun i ↦ (trivialF2TopPairing U).bil (x i) (y i) :=
    PiTensorProduct.map₂_tprod_tprod _ x y
  suffices ∀ a b : ⨂[ℤ] _ : G ⧸ U, (trivialF2 U).V,
      e (f a b) = (trivialF2TopPairing G).bil (e a) (e b) from this a b
  intro a b
  have htprod (x y : G ⧸ U → (trivialF2 U).V) :
      e (f (PiTensorProduct.tprod ℤ x) (PiTensorProduct.tprod ℤ y)) =
      (trivialF2TopPairing G).bil (e (PiTensorProduct.tprod ℤ x))
        (e (PiTensorProduct.tprod ℤ y)) := by
    apply (trivialF2Equiv G).injective
    simp only [hf, he, trivialF2TopPairing_bil_apply, AddEquiv.apply_symm_apply,
      Finset.prod_mul_distrib]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [LinearMap.map_smul, LinearMap.smul_apply]
    congr 1
    induction b using PiTensorProduct.induction_on with
    | smul_tprod t y => simp only [LinearMap.map_smul, htprod]
    | add b c hb hc => simp only [map_add, hb, hc]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]

end TauCeti
