/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Continuous.Restriction
public import TauCeti.RepresentationTheory.FDRep.External
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RepresentationTheory.Irreducible.ExternalTensor
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The external tensor product of continuous finite-dimensional representations

For topological monoids `G` and `H` over a topological field `k`, the external tensor product
`V ⊠ W` of continuous finite-dimensional representations of `G` and `H`, on which `(g, h)` acts by
`ρ_V g ⊗ ρ_W h`, is again continuous (`FDRep.isContinuous_externalTensor`): by
`FDRep.externalTensorIso` it is the tensor product over `G × H` of the restrictions of `V` and `W`
along the two continuous projections, and continuity is preserved by restriction and by tensor
products.

Conversely, if `V ⊠ W` is continuous and `W` is nonzero, then `V` is continuous: a matrix
coefficient `g ↦ f (ρ_V g v)` of `V` is the matrix coefficient `g ↦ (f ⊗ μ) ((g, 1) • (v ⊗ w))`
of `V ⊠ W` divided by `μ w`, for a vector `w` and a linear form `μ` with `μ w ≠ 0`
(`FDRep.isContinuous_left_of_isContinuous_externalTensor`), and symmetrically for `W`. Combined
with the classification of simple representations of `G × H` by external tensor products
(`FDRep.externalTensor_classification`), this shows that over an algebraically closed field every
continuous simple representation of `G × H` is isomorphic to an external tensor product of
continuous simple representations of `G` and of `H`
(`FDRep.exists_isContinuous_iso_externalTensor`). Conversely, such an external tensor product is
continuous by `FDRep.isContinuous_externalTensor` and simple by
`Representation.isIrreducible_externalTensor`, so the continuous simple representations of `G × H`
are exactly these. For compact groups over `ℂ` these are the irreducible classes of the
representation ring `R(G × H)`.

## Main statements

* `FDRep.isContinuous_externalTensor`: the external tensor product of continuous representations
  is continuous.
* `FDRep.isContinuous_left_of_isContinuous_externalTensor` and
  `FDRep.isContinuous_right_of_isContinuous_externalTensor`: the factors of a continuous external
  tensor product with nonzero factors are continuous.
* `FDRep.exists_isContinuous_iso_externalTensor`: every continuous simple representation of
  `G × H` is an external tensor product of continuous simple representations.

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

omit [ContinuousAdd k] in
/-- **The left factor of a continuous external tensor product is continuous**, when the right
factor is nonzero: a matrix coefficient of `V` is a matrix coefficient of `V ⊠ W` along
`g ↦ (g, 1)`. -/
theorem isContinuous_left_of_isContinuous_externalTensor {V : FDRep k G} {W : FDRep k H}
    [Nontrivial W]
    (h : isContinuous k (G × H) (FDRep.of (Representation.externalTensor V.ρ W.ρ))) :
    isContinuous k G V := isContinuous_iff.2 fun f v ↦ by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_ne_zero k hw
  -- The matrix coefficient of `V ⊠ W` for `f ⊗ μ` and `v ⊗ w`, along `g ↦ (g, 1)`, is
  -- `f (ρ_V g v) * μ w`.
  have hc := (isContinuous_iff.1 h ((TensorProduct.lid k k).toLinearMap ∘ₗ TensorProduct.map f μ)
    (v ⊗ₜ w)).comp
    (continuous_id.prodMk continuous_const : Continuous fun g : G ↦ (g, (1 : H)))
  refine (hc.mul continuous_const : Continuous fun g ↦ _ * (μ w)⁻¹).congr fun g ↦ ?_
  simp [FDRep.of_ρ', hμ]

omit [ContinuousAdd k] in
/-- **The right factor of a continuous external tensor product is continuous**, when the left
factor is nonzero: a matrix coefficient of `W` is a matrix coefficient of `V ⊠ W` along
`h ↦ (1, h)`. -/
theorem isContinuous_right_of_isContinuous_externalTensor {V : FDRep k G} {W : FDRep k H}
    [Nontrivial V]
    (h : isContinuous k (G × H) (FDRep.of (Representation.externalTensor V.ρ W.ρ))) :
    isContinuous k H W := isContinuous_iff.2 fun f w ↦ by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_ne_zero k hv
  -- The matrix coefficient of `V ⊠ W` for `μ ⊗ f` and `v ⊗ w`, along `h ↦ (1, h)`, is
  -- `μ v * f (ρ_W h w)`.
  have hc := (isContinuous_iff.1 h ((TensorProduct.lid k k).toLinearMap ∘ₗ TensorProduct.map μ f)
    (v ⊗ₜ w)).comp
    (continuous_const.prodMk continuous_id : Continuous fun h : H ↦ ((1 : G), h))
  refine (continuous_const.mul hc : Continuous fun h ↦ (μ v)⁻¹ * _).congr fun h ↦ ?_
  simp [FDRep.of_ρ', hμ]

omit [ContinuousAdd k] in
open CategoryTheory in
/-- **Continuous simple representations of a product are external tensor products of continuous
simple representations.** Over an algebraically closed topological field, every continuous simple
representation of `G × H` is isomorphic to `V ⊠ W` for continuous simple representations `V` of
`G` and `W` of `H`, which are unique up to isomorphism by
`FDRep.externalTensor_classification`. -/
theorem exists_isContinuous_iso_externalTensor [IsAlgClosed k] (X : FDRep k (G × H)) [Simple X]
    (hX : isContinuous k (G × H) X) :
    ∃ (V : FDRep k G) (W : FDRep k H), Simple V ∧ Simple W ∧ isContinuous k G V ∧
      isContinuous k H W ∧ Nonempty (X ≅ FDRep.of (Representation.externalTensor V.ρ W.ρ)) := by
  obtain ⟨V, W, hV, hW, ⟨i⟩, -⟩ := externalTensor_classification X
  have : Nontrivial V := (isIrreducible_of_simple V).nontrivial
  have : Nontrivial W := (isIrreducible_of_simple W).nontrivial
  have hVW := (isContinuous k (G × H)).prop_of_iso i hX
  exact ⟨V, W, hV, hW, isContinuous_left_of_isContinuous_externalTensor hVW,
    isContinuous_right_of_isContinuous_externalTensor hVW, ⟨i⟩⟩

end FDRep
