/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.EquivariantIndex
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous.Prod
public import TauCeti.Analysis.Fredholm.Prod

/-!
# Additivity of the equivariant Fredholm index

The equivariant index of a binary product of Fredholm intertwining maps is the sum of their
indices in the continuous representation ring. The proof compares the actual kernel and
quotient cokernel representations and uses their product classes. Strong continuity of the
input actions suffices; no compactness, unitarity or completeness of the ambient spaces is needed.

Adapted from `equivariantFredholmIndex_prod` in
[AtiyahSinger/Analysis/EquivariantIndexOperations.lean][source], Lean-Atiyah-Singer. The native
Fredholm product theorem replaces the source's quasi-inverse argument, and categorical
biproducts replace its finite-coordinate comparison of representation classes.

## References

* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §9, Definition 9.3, p. 212,
  [DOI 10.1515/9781400883912](https://doi.org/10.1515/9781400883912), for the virtual index
  `[ker T] - [coker T]`. The binary product proof is a supplementary argument in the
  formalization linked above.

[source]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/EquivariantIndexOperations.lean
-/

public section

open ContRepresentation TauCeti

namespace ContIntertwiningMap

variable {𝕜 G E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {π₁ : ContRepresentation 𝕜 G E₁} {π₂ : ContRepresentation 𝕜 G E₂}
  {ρ₁ : ContRepresentation 𝕜 G F₁} {ρ₂ : ContRepresentation 𝕜 G F₂}

/-- The equivariant Fredholm index is additive under binary products of intertwining maps,
as an equality of actual virtual representations in `contRepRing`. Fredholmness and strong
continuity of the factors are derived from the corresponding product certificates. -/
@[simp]
theorem equivariantIndex_prodMap (T : π₁ →ⁱL ρ₁) (S : π₂ →ⁱL ρ₂)
    (hTS : (T.prodMap S).toContinuousLinearMap.IsFredholm)
    (hπ : ∀ v, Continuous fun g ↦ (π₁.prod π₂) g v)
    (hρ : ∀ v, Continuous fun g ↦ (ρ₁.prod ρ₂) g v) :
    (T.prodMap S).equivariantIndex hTS hπ hρ =
      T.equivariantIndex
        (Eq.mp (congrArg ContinuousLinearMap.IsFredholm (toContinuousLinearMap_prodMap T S))
          hTS).of_prodMap_left
        (continuous_apply_of_continuous_prod_apply_left hπ)
        (continuous_apply_of_continuous_prod_apply_left hρ) +
      S.equivariantIndex
        (Eq.mp (congrArg ContinuousLinearMap.IsFredholm (toContinuousLinearMap_prodMap T S))
          hTS).of_prodMap_right
        (continuous_apply_of_continuous_prod_apply_right hπ)
        (continuous_apply_of_continuous_prod_apply_right hρ) := by
  have hU := Eq.mp
    (congrArg ContinuousLinearMap.IsFredholm (toContinuousLinearMap_prodMap T S)) hTS
  have hT := hU.of_prodMap_left
  have hS := hU.of_prodMap_right
  have hπ₁ := continuous_apply_of_continuous_prod_apply_left hπ
  have hπ₂ := continuous_apply_of_continuous_prod_apply_right hπ
  have hρ₁ := continuous_apply_of_continuous_prod_apply_left hρ
  have hρ₂ := continuous_apply_of_continuous_prod_apply_right hρ
  have := hT.finite_ker
  have := hS.finite_ker
  have := hTS.finite_ker
  have := hT.isClosed_range
  have := hS.isClosed_range
  have := hTS.isClosed_range
  have := hT.finite_coker
  have := hS.finite_coker
  have := hTS.finite_coker
  have hkT := T.continuous_kerRepresentation hπ₁
  have hkS := S.continuous_kerRepresentation hπ₂
  have hcT := T.continuous_cokerRepresentation hρ₁
  have hcS := S.continuous_cokerRepresentation hρ₂
  let ek := T.kerProdEquiv S
  let ec := T.cokerProdEquiv S
  rw [equivariantIndex_def, equivariantIndex_def, equivariantIndex_def,
    SplitK0.of_congr (ContFDRep.ofContRepresentationIso ek.toLinearEquiv
      (fun g v ↦ ek.toContIntertwiningMap.isIntertwining g v)
      ((T.prodMap S).continuous_kerRepresentation hπ)
      (T.kerRepresentation.continuous_prod S.kerRepresentation hkT hkS)),
    SplitK0.of_congr (ContFDRep.ofContRepresentationIso ec.toLinearEquiv
      (fun g v ↦ ec.toContIntertwiningMap.isIntertwining g v)
      ((T.prodMap S).continuous_cokerRepresentation hρ)
      (T.cokerRepresentation.continuous_prod S.cokerRepresentation hcT hcS)),
    contRepRing_of_prod, contRepRing_of_prod]
  abel

end ContIntertwiningMap
