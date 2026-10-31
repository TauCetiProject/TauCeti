/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.TensorInduction

/-!
# The Evens norm at index two in degree one

For a compact open subgroup `U` of index two in a locally compact group `G`, the general Evens
norm `OpenSubgroup.evensNorm : H¹(U, 𝔽₂) → H^{2 · 1}(G, 𝔽₂)`, defined through the diagonal tensor
in the tensor-induced resolution, agrees with the explicit index-two norm
`TauCeti.ContCohomology.evensNormIndexTwo : H¹(U, 𝔽₂) → H²(G, 𝔽₂)`, defined as the class of the
two-point graph cocycle
```
ν_α (γ, η) = b₁ γ · b_s η                     if γ ∈ U,
ν_α (γ, η) = b₁ γ · b₁ η + b₁ η · b_s η       otherwise.
```
So the graph cocycle, and with it the identities of the index-two norm (restriction to `U`,
polarization, the norm of a restricted class, the `D₁₆` pullback), describe the multiplicative
transfer itself rather than an ad hoc formula. Both statements hold up to the degree transport
`TauCeti.ContinuousCohomology.degreeCast` between `2` and `Fintype.card (G ⧸ U) * 1`.

The computation on representatives is
`TauCeti.ContCohomology.smoothTensorInducedDiagonalClass_eq_graphClass`, for the transversal
`{1, s}`; the general norm may be computed with that transversal by `evensNorm_cochainClass`, and
the class of a continuous homomorphism is the class of its homogeneous cochain by
`TauCeti.ContCohomology.homClass_eq_cochainClass`.

## Main results

* `OpenSubgroup.evensNorm_eq_graphClass`: the Evens norm of the class of a continuous
  homomorphism `α : U → 𝔽₂` is its graph class.
* `OpenSubgroup.evensNormIndexTwo_eq`: the index-two norm is the Evens norm on all of `H¹(U, 𝔽₂)`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–5.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4, for the index-two graph normalization.
-/

public section

namespace OpenSubgroup

open TauCeti TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex]
  [CompactSpace U.toSubgroup] [Fintype (G ⧸ U.toSubgroup)]

/-- **The Evens norm of a character at index two is its graph class:** for `U` of index two and a
continuous homomorphism `α : U → 𝔽₂`, the norm `N_U^G` of the class of `α` is the class of the
two-point graph cocycle of `α`, up to the transport of degrees from `2` to
`Fintype.card (G ⧸ U) * 1`. -/
theorem evensNorm_eq_graphClass (hU : U.toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    U.evensNorm (homClass U.toSubgroup α hα) =
      (ContinuousCohomology.degreeCast (trivialF2 G)
        (by rw [mul_one, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hU] :
          2 = Fintype.card (G ⧸ U.toSubgroup) * 1)).hom
        (graphClass U hU α hα) := by
  obtain ⟨s, hs, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hU
  rw [homClass_eq_cochainClass, evensNorm_cochainClass U
    ⟨Set.range (U.toSubgroup.indexTwoTransversal s),
      Subgroup.isComplement_range_left (Subgroup.indexTwoTransversal_mk hU hs)⟩,
    tensorNormCocycleClass_def,
    smoothTensorInducedDiagonalClass_eq_graphClass U hU s hs α hα _ _ _ _
      ((trivialF2 U.toSubgroup).cochainToGradedResolution_apply 1 _)]
  -- The comparison writes its degree transport as an `eqToHom` and the statement as
  -- `degreeCast`; generalizing the target degree makes both transports along `2 = 2`.
  generalize_proofs h₁ h₂
  revert h₁ h₂
  generalize Fintype.card (G ⧸ U.toSubgroup) * 1 = k
  rintro - rfl
  simp

/-- **The index-two Evens norm is the Evens norm:** for `U` of index two, the explicit index-two
norm `evensNormIndexTwo U hU`, defined by the graph cocycle, is the general Evens norm `N_U^G` on
`H¹(U, 𝔽₂)`, up to the transport of degrees from `Fintype.card (G ⧸ U) * 1` to `2`. -/
theorem evensNormIndexTwo_eq (hU : U.toSubgroup.index = 2)
    (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    evensNormIndexTwo U hU x =
      (ContinuousCohomology.degreeCast (trivialF2 G)
        (by rw [mul_one, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hU] :
          Fintype.card (G ⧸ U.toSubgroup) * 1 = 2)).hom
        (U.evensNorm x) := by
  obtain ⟨α, hα, rfl⟩ := homClass_surjective U.toSubgroup x
  rw [evensNormIndexTwo_homClass, evensNorm_eq_graphClass U hU, ← CategoryTheory.comp_apply]
  simp

end OpenSubgroup
