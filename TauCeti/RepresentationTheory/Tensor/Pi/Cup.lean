/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.SumSplit
public import TauCeti.RepresentationTheory.Tensor.Pi.Resolution
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Contraction

/-!
# Cup products of classes on tensor products of contracted resolutions

Let `M i` be finitely many contracted graded smooth discrete representations of a locally compact
group `G` in characteristic two, indexed by a disjoint union `I₁ ⊕ I₂`, with coefficients `X i`.
Their tensor product is contracted onto `⨂ i, X i` (`TauCeti.smoothPiTensorProductContraction`),
and so is the tensor product over each block. Tensoring a cocycle `x` over `I₁` with a cocycle `y`
over `I₂` (`TauCeti.PiTensorProduct.tmulLex`) gives a cocycle over the whole family, and this file
proves that its class is the cup product of the classes of `x` and `y`
(`TauCeti.gradedCohomologyClass_smoothPiTensorProductLexPairing`), for the coefficient pairing
`(⨂ i, X (inl i)) × (⨂ j, X (inr j)) → ⨂ k, X k` that tensors the two blocks
(`TauCeti.smoothPiTensorProductLexPairing`).

The whole family is indexed by the lexicographic sum `I₁ ⊕ₗ I₂`, in which every index of `I₁`
precedes every index of `I₂`; this order fixes the slot homotopy of the contraction. For it,
multiplying on the left by an augmented tensor over `I₁` commutes with the contraction, since
the factor homotopies kill and the factor projectors fix augmented vectors
(`TauCeti.PiTensorProduct.slotHomotopy_tmulLex`). That is what
`TopRep.ResolutionContraction.gradedCohomologyClass_pairing` needs to identify the class of a
product with the cup product of the classes.

Splitting off blocks repeatedly expresses the class of a tensor of cocycles over a finite family as
an iterated cup product. In the double-coset formula for the Evens norm, the factors are the
tensor-induced resolutions of the orbits of a subgroup on the cosets, and the classes of the
orbitwise diagonal tensors are norms from the stabilizers.

## Main definitions

* `TauCeti.smoothPiTensorProductLexPairing`: the pairing tensoring the tensor products over the two
  blocks of a family of discrete representations into the tensor product over the lexicographic
  sum.

## Main results

* `TauCeti.smoothPiTensorProductDifferential_lexPairing`: the slot differential satisfies the
  unsigned Leibniz rule for the block pairing.
* `TauCeti.gradedCohomologyClass_smoothPiTensorProductLexPairing`: the class of the block tensor of
  two homogeneous invariant cocycles is the cup product of their classes.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. **108** (1963), §6, Proposition 2, for products of orbitwise classes.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, for the cup
  product and its independence of the resolution.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {I₁ I₂ : Type x} [Fintype I₁] [Fintype I₂]

section Pairing

variable (X : I₁ ⊕ I₂ → DiscreteRep.{u, v, max v w} R G)

/-- **The block pairing of a family indexed by a sum.** A tensor over the block `I₁` and a tensor
over the block `I₂` of a family of discrete representations give a tensor over the whole family,
indexed by the lexicographic sum `I₁ ⊕ₗ I₂` (`PiTensorProduct.tmulLex`). This is an equivariant
coefficient pairing. -/
noncomputable def smoothPiTensorProductLexPairing :
    TopPairing ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun i ↦ X (.inl i))).obj
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun j ↦ X (.inr j))).obj
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.piTensorProduct fun k : I₁ ⊕ₗ I₂ ↦ X (ofLex k))).obj where
  bil := PiTensorProduct.tmulLex R fun i ↦ (X i).V
  cont := by
    have := ((toSmoothDiscrete R G).obj
      (DiscreteRep.piTensorProduct fun i ↦ X (.inl i))).property.discreteTopology
    have := ((toSmoothDiscrete R G).obj
      (DiscreteRep.piTensorProduct fun j ↦ X (.inr j))).property.discreteTopology
    exact continuous_of_discreteTopology
  equivariant g a b := by
    -- On each tensor product, `g` acts by the factorwise map.
    exact (congrArg₂ (fun a b ↦ PiTensorProduct.tmulLex R (fun i ↦ (X i).V) a b)
      (DiscreteRep.piTensorProduct_ρ_apply _ g a) (DiscreteRep.piTensorProduct_ρ_apply _ g b)).trans
      ((PiTensorProduct.map_tmulLex (fun i ↦ (X i).ρ g) a b).symm.trans
        (DiscreteRep.piTensorProduct_ρ_apply _ g _).symm)

omit [IsTopologicalGroup G] in
/-- The block pairing is the lexicographic tensor of the two blocks. -/
@[simp]
theorem smoothPiTensorProductLexPairing_bil :
    (smoothPiTensorProductLexPairing X).bil = PiTensorProduct.tmulLex R fun i ↦ (X i).V :=
  (rfl)

end Pairing

section Differential

variable (M : I₁ ⊕ I₂ → DiscreteRep.{u, v, max v w} R G) (d : ∀ i, M i ⟶ M i)

omit [IsTopologicalGroup G] in
/-- **The Leibniz rule for the block pairing.** The slot differential of the block pairing of `a`
and `b` is the pairing of the differential of `a` with `b`, plus the pairing of `a` with the
differential of `b`. In characteristic two no signs appear. -/
theorem smoothPiTensorProductDifferential_lexPairing
    (a : ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun i ↦ M (.inl i))).obj.V)
    (b : ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun j ↦ M (.inr j))).obj.V) :
    (smoothPiTensorProductDifferential (fun k : I₁ ⊕ₗ I₂ ↦ M (ofLex k))
        (fun k ↦ d (ofLex k))).hom.hom ((smoothPiTensorProductLexPairing M).bil a b) =
      (smoothPiTensorProductLexPairing M).bil
          ((smoothPiTensorProductDifferential (fun i ↦ M (.inl i)) (fun i ↦ d (.inl i))).hom.hom
            a) b +
        (smoothPiTensorProductLexPairing M).bil a
          ((smoothPiTensorProductDifferential (fun j ↦ M (.inr j)) (fun j ↦ d (.inr j))).hom.hom
            b) := by
  classical
  -- The slot differentials are slot sums on the native tensor carriers.
  refine (smoothPiTensorProductDifferential_apply _ _ _).trans <|
    (PiTensorProduct.slotSum_tmulLex (fun i ↦ (d i).toLinearMap) a b).trans ?_
  exact congrArg₂ (· + ·)
    (congrArg (fun z ↦ PiTensorProduct.tmulLex R (fun i ↦ (M i).V) z b)
      (smoothPiTensorProductDifferential_apply _ _ a).symm)
    (congrArg (fun z ↦ PiTensorProduct.tmulLex R (fun i ↦ (M i).V) a z)
      (smoothPiTensorProductDifferential_apply _ _ b).symm)

end Differential

section Contraction

variable (M : I₁ ⊕ I₂ → DiscreteRep.{u, v, max v w} R G) (d : ∀ i, M i ⟶ M i)
  (hM : ∀ i (v : (M i).V), v + v = 0)
  (hdd : ∀ i, (d i).toLinearMap ∘ₗ (d i).toLinearMap = 0)
  (X : I₁ ⊕ I₂ → DiscreteRep.{u, v, max v w} R G)
  (ℳ : ∀ i, ℤ → Submodule R (M i).V)
  (hρ : ∀ i n g v, v ∈ ℳ i n → (M i).ρ g v ∈ ℳ i n)
  (hd : ∀ i, LinearMap.IsHomogeneous (d i).toLinearMap (ℳ i) (ℳ i) 1)
  (a : ∀ i, X i ⟶ M i) (ha : ∀ i v, (a i).toLinearMap v ∈ ℳ i 0)
  (π : ∀ i, (M i).V →ₗ[R] (X i).V) (h : ∀ i, Module.End R (M i).V)
  (hh : ∀ i, LinearMap.IsHomogeneous (h i) (ℳ i) (ℳ i) (-1))
  (hπa : ∀ i v, π i ((a i).toLinearMap v) = v)
  (hπ : ∀ i p, 0 < p → ∀ v ∈ ℳ i p, π i v = 0)
  (hneg : ∀ i p, p < 0 → ℳ i p = ⊥)
  (hdh : ∀ i v, (d i).toLinearMap (h i v) + h i ((d i).toLinearMap v) =
    v - (a i).toLinearMap (π i v))
  [LinearOrder I₁] [LinearOrder I₂]

/-- The contraction of the tensor product over the block `I₁`. -/
local notation "c₁" => smoothPiTensorProductContraction (fun i ↦ M (Sum.inl i))
  (fun i ↦ d (Sum.inl i))
  (fun i ↦ hM (Sum.inl i)) (fun i ↦ hdd (Sum.inl i)) (fun i ↦ X (Sum.inl i)) (fun i ↦ ℳ (Sum.inl i))
  (fun i ↦ hρ (Sum.inl i)) (fun i ↦ hd (Sum.inl i)) (fun i ↦ a (Sum.inl i)) (fun i ↦ ha (Sum.inl i))
  (fun i ↦ π (Sum.inl i)) (fun i ↦ h (Sum.inl i)) (fun i ↦ hh (Sum.inl i)) (fun i ↦ hπa (Sum.inl i))
  (fun i ↦ hπ (Sum.inl i)) (fun i ↦ hneg (Sum.inl i)) (fun i ↦ hdh (Sum.inl i))

/-- The contraction of the tensor product over the block `I₂`. -/
local notation "c₂" => smoothPiTensorProductContraction (fun j ↦ M (Sum.inr j))
  (fun j ↦ d (Sum.inr j))
  (fun j ↦ hM (Sum.inr j)) (fun j ↦ hdd (Sum.inr j)) (fun j ↦ X (Sum.inr j)) (fun j ↦ ℳ (Sum.inr j))
  (fun j ↦ hρ (Sum.inr j)) (fun j ↦ hd (Sum.inr j)) (fun j ↦ a (Sum.inr j)) (fun j ↦ ha (Sum.inr j))
  (fun j ↦ π (Sum.inr j)) (fun j ↦ h (Sum.inr j)) (fun j ↦ hh (Sum.inr j)) (fun j ↦ hπa (Sum.inr j))
  (fun j ↦ hπ (Sum.inr j)) (fun j ↦ hneg (Sum.inr j)) (fun j ↦ hdh (Sum.inr j))

/-- The contraction of the tensor product over the lexicographic sum `I₁ ⊕ₗ I₂`. -/
local notation "c₃" => smoothPiTensorProductContraction (fun k : I₁ ⊕ₗ I₂ ↦ M (ofLex k))
  (fun k ↦ d (ofLex k)) (fun k ↦ hM (ofLex k)) (fun k ↦ hdd (ofLex k))
  (fun k ↦ X (ofLex k)) (fun k ↦ ℳ (ofLex k)) (fun k ↦ hρ (ofLex k))
  (fun k ↦ hd (ofLex k)) (fun k ↦ a (ofLex k)) (fun k ↦ ha (ofLex k))
  (fun k ↦ π (ofLex k)) (fun k ↦ h (ofLex k)) (fun k ↦ hh (ofLex k))
  (fun k ↦ hπa (ofLex k)) (fun k ↦ hπ (ofLex k)) (fun k ↦ hneg (ofLex k))
  (fun k ↦ hdh (ofLex k))

/-- The retraction of the tensor contraction over `I₁ ⊕ₗ I₂` carries the block pairing of an
augmented tensor `x` with `w` to the block pairing of `x` with the retraction of `w`. -/
private theorem smoothPiTensorProductContraction_proj_lexPairing (x)
    (w : ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun j ↦ M (.inr j))).obj.V)
    (hw : w ∈ PiTensorProduct.totalDegreePiece I₂ (fun j ↦ ℳ (.inr j)) (0 : ℕ))
    (hxw : (smoothPiTensorProductLexPairing M).bil ((c₁).ι.hom x).val w ∈
      PiTensorProduct.totalDegreePiece (I₁ ⊕ₗ I₂) (fun k ↦ ℳ (ofLex k)) (0 : ℕ)) :
    (c₃).proj ⟨(smoothPiTensorProductLexPairing M).bil ((c₁).ι.hom x).val w, hxw⟩ =
      (smoothPiTensorProductLexPairing X).bil x ((c₂).proj ⟨w, hw⟩) := by
  -- Both retractions are factorwise, and the augmentation of `x` is factorwise.
  refine (smoothPiTensorProductContraction_proj_apply ..).trans <| Eq.trans ?_
    (congrArg ((smoothPiTensorProductLexPairing X).bil x)
      (smoothPiTensorProductContraction_proj_apply ..).symm)
  refine (congrArg (fun z ↦ PiTensorProduct.map (fun k ↦ π (ofLex k))
    (PiTensorProduct.tmulLex R (fun i ↦ (M i).V) z w))
      (smoothPiTensorProductContraction_ι_apply ..)).trans <|
    (PiTensorProduct.map_tmulLex π _ w).trans ?_
  -- The retraction undoes the augmentation in every factor of the left block.
  exact congrArg (fun z ↦ PiTensorProduct.tmulLex R (fun i ↦ (X i).V) z _)
    (piTensorProductMap_retraction_augmentation _ _ _ _ (fun i ↦ hπa (.inl i)) x)

/-- The homotopy of the tensor contraction over `I₁ ⊕ₗ I₂` commutes with the block pairing with an
augmented tensor on the left. -/
private theorem smoothPiTensorProductContraction_hom_lexPairing (n : ℕ) (x)
    (w : ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun j ↦ M (.inr j))).obj.V)
    (hw : w ∈ PiTensorProduct.totalDegreePiece I₂ (fun j ↦ ℳ (.inr j)) (n + 1 : ℕ))
    (hxw : (smoothPiTensorProductLexPairing M).bil ((c₁).ι.hom x).val w ∈
      PiTensorProduct.totalDegreePiece (I₁ ⊕ₗ I₂) (fun k ↦ ℳ (ofLex k)) (n + 1 : ℕ)) :
    ((c₃).hom n ⟨(smoothPiTensorProductLexPairing M).bil ((c₁).ι.hom x).val w, hxw⟩).val =
      (smoothPiTensorProductLexPairing M).bil ((c₁).ι.hom x).val ((c₂).hom n ⟨w, hw⟩).val := by
  -- The homotopies are ordered slot homotopies, and the augmentation of `x` is factorwise.
  refine (smoothPiTensorProductContraction_hom_apply ..).trans <| Eq.trans ?_
    (congrArg ((smoothPiTensorProductLexPairing M).bil ((c₁).ι.hom x).val)
      (smoothPiTensorProductContraction_hom_apply ..).symm)
  refine (congrArg (fun z ↦ PiTensorProduct.slotHomotopy (I₁ ⊕ₗ I₂)
      (fun k ↦ (a (ofLex k)).toLinearMap ∘ₗ π (ofLex k)) (fun k ↦ h (ofLex k))
      (PiTensorProduct.tmulLex R (fun i ↦ (M i).V) z w))
    (smoothPiTensorProductContraction_ι_apply ..)).trans <|
    (PiTensorProduct.slotHomotopy_tmulLex (fun i ↦ (a i).toLinearMap ∘ₗ π i) h _ w).trans <|
      Eq.trans ?_
    (congrArg (fun z ↦ PiTensorProduct.tmulLex R (fun i ↦ (M i).V) z _)
      (smoothPiTensorProductContraction_ι_apply ..).symm)
  -- The left block is augmented: the slot homotopy kills it and the projectors fix it.
  have h₀ : PiTensorProduct.slotHomotopy I₁
      (fun i ↦ (a (.inl i)).toLinearMap ∘ₗ π (.inl i)) (fun i ↦ h (.inl i))
      (PiTensorProduct.map (fun i ↦ (a (.inl i)).toLinearMap) x) = 0 :=
    PiTensorProduct.slotHomotopy_eq_zero_of_mem_totalDegreePiece_zero
      (fun i ↦ hneg (.inl i)) (fun i _ ↦ factorHomotopy_eq_zero_of_mem_zero M ℳ h hh hneg (.inl i))
      (PiTensorProduct.map_mem_totalDegreePiece_zero (fun i ↦ ha (.inl i)) x)
  have h₁ : PiTensorProduct.map (fun i ↦ (a (.inl i)).toLinearMap ∘ₗ π (.inl i))
      (PiTensorProduct.map (fun i ↦ (a (.inl i)).toLinearMap) x) =
      PiTensorProduct.map (fun i ↦ (a (.inl i)).toLinearMap) x := by
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply,
      piTensorProductMap_retraction_augmentation _ _ _ _ (fun i ↦ hπa (.inl i)) x]
  rw [h₀, h₁]
  exact (congrArg (· + _) (LinearMap.map_zero₂ (PiTensorProduct.tmulLex R fun i ↦ (M i).V) w)).trans
    (zero_add _)

/-- **The class of a block tensor is the cup product of the classes.** Let `x` and `y` be
homogeneous cocycles of degrees `p` and `q`, fixed by `G`, of the tensor products of the contracted
resolutions over the blocks `I₁` and `I₂`. Then the class of their block tensor, computed through
the tensor contraction over the lexicographic sum `I₁ ⊕ₗ I₂`, is the cup product of their classes
for the block pairing of the coefficients. -/
theorem gradedCohomologyClass_smoothPiTensorProductLexPairing [LocallyCompactSpace G] {p q : ℕ}
    {x : ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun i ↦ M (.inl i))).obj.V}
    (hx : x ∈ PiTensorProduct.totalDegreePiece I₁ (fun i ↦ ℳ (.inl i)) p)
    (hxinv : ∀ g,
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun i ↦ M (.inl i))).obj.ρ g x = x)
    (hdx : (smoothPiTensorProductDifferential (fun i ↦ M (.inl i))
      (fun i ↦ d (.inl i))).hom.hom x = 0)
    {y : ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun j ↦ M (.inr j))).obj.V}
    (hy : y ∈ PiTensorProduct.totalDegreePiece I₂ (fun j ↦ ℳ (.inr j)) q)
    (hyinv : ∀ g,
      ((toSmoothDiscrete R G).obj (DiscreteRep.piTensorProduct fun j ↦ M (.inr j))).obj.ρ g y = y)
    (hdy : (smoothPiTensorProductDifferential (fun j ↦ M (.inr j))
      (fun j ↦ d (.inr j))).hom.hom y = 0) :
    (c₃).gradedCohomologyClass ((smoothPiTensorProductLexPairing M).bil x y)
        (by exact_mod_cast PiTensorProduct.tmulLex_mem_totalDegreePiece hx hy)
        (fun g ↦ by rw [← (smoothPiTensorProductLexPairing M).equivariant, hxinv, hyinv])
        (by rw [smoothPiTensorProductDifferential_lexPairing, hdx, hdy, LinearMap.map_zero₂,
          map_zero, add_zero]) =
      (smoothPiTensorProductLexPairing X).cup p q ((c₁).gradedCohomologyClass x hx hxinv hdx)
        ((c₂).gradedCohomologyClass y hy hyinv hdy) :=
  (c₁).gradedCohomologyClass_pairing c₂ c₃ (smoothPiTensorProductLexPairing X)
    (smoothPiTensorProductLexPairing M).bil
    (fun ha hb ↦ PiTensorProduct.tmulLex_mem_totalDegreePiece ha hb)
    (smoothPiTensorProductLexPairing M).equivariant
    (fun b ↦ (smoothPiTensorProductLexPairing M).cont.comp (.prodMk_left b))
    (fun a b hb ↦ by
      rw [smoothPiTensorProductDifferential_lexPairing, hb, map_zero, add_zero])
    (smoothPiTensorProductContraction_proj_lexPairing M d hM hdd X ℳ hρ hd a ha π h hh hπa hπ
      hneg hdh)
    (smoothPiTensorProductContraction_hom_lexPairing M d hM hdd X ℳ hρ hd a ha π h hh hπa hπ
      hneg hdh)
    hx hxinv hdx hy hyinv hdy

end Contraction

end TauCeti
