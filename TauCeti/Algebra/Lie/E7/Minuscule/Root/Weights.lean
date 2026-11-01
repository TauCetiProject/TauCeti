/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Coordinates
public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Differential
public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Support
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace

/-!
# Adjoint weights of the numbered E₇ root differentials

The normalized differentials of the fourteen numbered root subgroups of the specialized
integral minuscule carrier have the corresponding positive or negative simple-root characters
under its weight torus. In particular, over every field, these characters are actual nontrivial
adjoint weights. The root parameters therefore give nonzero vectors in the expected root spaces,
as required when comparing the carrier's numbered subgroups with a pinning.

Weight-space membership is proved whenever the carrier's augmentation cotangent module is
projective; over a field this is automatic. The entrywise criterion retains the integral
characters, so it also distinguishes opposite roots in characteristic two. Neither equality
of these root lines with the entire weight spaces nor maximality of the torus is asserted.
The carrier is not identified here with an independently pinned simply connected E₇ group.

The differential normalization comes from
`TauCeti.Algebra.Lie.E7.Minuscule.Root.Differential`. The weight-space argument follows
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`, using the general closed-subgroup
weight criterion rather than a computation of the fifty-six by fifty-six matrices.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule

open DynkinType

noncomputable section

-- The closed-subgroup weight criterion uses base and torus indices in the same universe.
variable (R : Type) [CommRing R]

private theorem weightTorus_comp_quotient :
    (weightTorusToBaseChangeCoordinateMap R).hom.comp
        (Bialgebra.Quotient.mkBialgHom (baseChangeDefiningIdeal R).toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap (R := R) e7MinusculeWeight).hom := by
  rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp]
  -- The ambient coordinate map is the quotient map in the carrier's chosen presentation.
  rw [← coordinateMap_def]
  rw [coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
    GeneralLinear.weightTorusBaseChangeCoordinateMap_eq]

variable [Module.Projective R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R))]

/-- A cotangent-dual vector of the specialized E₇ carrier has adjoint character `α` exactly
when its tangent matrix vanishes at every entry of a different integral weight difference. -/
theorem mem_adjointWeightSpace_iff (α : Multiplicative (Fin 7 →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R))) :
    x ∈ Derivation.adjointWeightSpace (weightTorusToBaseChangeCoordinateMap R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (e7MinusculeWeight a - e7MinusculeWeight b) ≠ α →
        GeneralLinear.tangentMatrix 56
          (derivationComp (B := R) (coordinateMap R).hom
            (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  -- Rewrite the ambient coordinate morphism to use the quotient differential criterion.
  rw [coordinateMap_def]
  rw [CommHopfAlgCat.hom_mkQuotient]
  simpa only [HopfIdeal.quotientLieHom_apply] using
    HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus
      (baseChangeDefiningIdeal R) e7MinusculeWeight _ (weightTorus_comp_quotient R) α x

/-- The differential of each numbered positive or negative simple root subgroup has the
corresponding integral root character under the carrier's weight torus. -/
theorem rootVector_mem_adjointWeightSpace (k : Fin 7 ⊕ Fin 7) :
    (Derivation.cotangentLinearEquiv (B := R)).symm (rootVector R k) ∈
      Derivation.adjointWeightSpace (weightTorusToBaseChangeCoordinateMap R).hom
        (SplitTorus.weightCharacter (E7.rootGeneratorWeight valid_E7 k)) := by
  erw [mem_adjointWeightSpace_iff]
  intro a b hab
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_rootVector, Matrix.map_apply,
    rootMatrix_apply_eq_zero_of_weight_sub_ne k a b
      (fun h => hab (congrArg SplitTorus.weightCharacter h)),
    Int.cast_zero]

/-- Each numbered signed simple root is an actual nontrivial adjoint weight of the specialized
E₇ carrier. This uses the nonzero differential, rather than assuming a root-space dimension. -/
theorem rootWeightCharacter_mem_nontrivialAdjointWeights [Nontrivial R] (k : Fin 7 ⊕ Fin 7) :
    SplitTorus.weightCharacter (E7.rootGeneratorWeight valid_E7 k) ∈
      Derivation.nontrivialAdjointWeights (weightTorusToBaseChangeCoordinateMap R).hom := by
  -- Normalize the rank-seven root character before applying the generic membership rule.
  erw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨SplitTorus.weightCharacter_eq_one_iff.not.2 (rootGeneratorWeight_ne_zero k), ?_⟩
  intro hbot
  have hz := rootVector_mem_adjointWeightSpace R k
  erw [hbot, Submodule.mem_bot] at hz
  exact rootVector_ne_zero R k ((Derivation.cotangentLinearEquiv (B := R)).symm.injective
    (hz.trans (map_zero _).symm))

end

end TauCeti.E7Minuscule
