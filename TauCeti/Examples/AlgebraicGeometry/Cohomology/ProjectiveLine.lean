/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.NegativeTwist
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf

/-!
# Examples of quasi-coherent cohomology on the projective line

Worked cases of the cohomology of the twisting sheaves `𝒪(n)` on the projective line
`ℙ¹_R = TauCeti.AlgebraicGeometry.projectiveLine R`, and of flat base change.

* `H¹(ℙ¹_R, 𝒪(-2)) ≅ R` over every commutative ring `R`
  (`cohomologyOneTwistingSheafNegTwoLinearEquiv`), so over a field `k` it is one-dimensional
  (`finrank_cohomology_one_twistingSheaf_neg_two`).
* `H⁰(ℙ¹_k, 𝒪(1))` has dimension `2` over a field `k`, and is free of rank `2` over every
  nontrivial ring (`finrank_cohomology_zero_twistingSheaf_one`).
* For a flat `R`-algebra `B`, flat base change along `ℙ¹_B ⟶ ℙ¹_R` identifies
  `H¹(ℙ¹_B, g^* 𝒪(-2))` with `B ⊗_R R ≅ B` (`cohomologyOneBaseChangeLinearEquiv`), sending
  the base change `b ⊗ x` of a class `x ∈ H¹(ℙ¹_R, 𝒪(-2)) ≅ R` to `b` times the image of `x`
  (`cohomologyOneBaseChangeLinearEquiv_cohomologyBaseChange_tmul`). For the zero algebra both
  sides are zero (`subsingleton_cohomology_one_pullback_of_subsingleton`).

## References

* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS)
* [Stacks, Lemma 30.5.2 (02KH)](https://stacks.math.columbia.edu/tag/02KH)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.ProjectiveLineCohomologyExample

local notation "𝒜" R => SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-! ### Cohomology of `𝒪(-2)` and `𝒪(1)` -/

section Cohomology

variable (R : Type u) [CommRing R]

/-- `H¹(ℙ¹_R, 𝒪(-2))` is free of rank one. -/
theorem finrank_cohomology_one_twistingSheaf_neg_two [Nontrivial R] :
    Module.finrank R (Cohomology (Proj.twistingSheaf (𝒜 R) (-2)) 1) = 1 := by
  have h := projectiveLine.finrank_cohomology_one_twistingSheaf R (n := -2) le_rfl
  omega

/-- **`H¹(ℙ¹_R, 𝒪(-2)) ≅ R`** over every commutative ring `R`: `H¹(ℙ¹_R, 𝒪(-2))` is the module of
forms of degree `0`, whose basis is the empty monomial. -/
def cohomologyOneTwistingSheafNegTwoLinearEquiv :
    Cohomology (Proj.twistingSheaf (𝒜 R) (-2)) 1 ≃ₗ[R] R :=
  (projectiveLine.cohomologyOneTwistingSheafLinearEquiv R 0).trans
    (((Pi.basisFun R (Fin 2)).symmetricAlgebraHomogeneous 0).equivFun.trans
      (LinearEquiv.funUnique (Sym (Fin 2) 0) R R))

/-- `H⁰(ℙ¹_R, 𝒪(1))` is free of rank two: its basis is the pair of coordinates `X₀, X₁`. -/
theorem finrank_cohomology_zero_twistingSheaf_one [Nontrivial R] :
    Module.finrank R (Cohomology (Proj.twistingSheaf (𝒜 R) 1) 0) = 2 := by
  have h := projectiveLine.finrank_cohomology_zero_twistingSheaf R 1
  norm_num at h
  exact h

end Cohomology

/-! ### Flat base change in degree one -/

section BaseChange

variable (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
  [Module.Flat R B]

/-- **Flat base change of `H¹(ℙ¹, 𝒪(-2))`.** For a flat `R`-algebra `B`, with
`g : ℙ¹_B ⟶ ℙ¹_R` the base change projection, `H¹(ℙ¹_B, g^* 𝒪(-2)) ≅ B ⊗_R H¹(ℙ¹_R, 𝒪(-2))
≅ B ⊗_R R ≅ B`. -/
def cohomologyOneBaseChangeLinearEquiv :
    Cohomology ((Scheme.Modules.pullback (projectiveLine.baseChangeProjection R B)).obj
      (Proj.twistingSheaf (𝒜 R) (-2))) 1 ≃ₗ[B] B :=
  (cohomologyBaseChangeLinearEquiv (projectiveLine.isPullback_baseChangeProjection R B) _ 1).symm
    ≪≫ₗ (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (cohomologyOneTwistingSheafNegTwoLinearEquiv R)) ≪≫ₗ AlgebraTensorModule.rid R B B

/-- The flat base change isomorphism `H¹(ℙ¹_B, g^* 𝒪(-2)) ≅ B` sends the base change of
`b ⊗ x` to `b` times the image of `x` under `H¹(ℙ¹_R, 𝒪(-2)) ≅ R`: on `B ⊗_R R ≅ B` it is
`b ⊗ a ↦ a b`. -/
theorem cohomologyOneBaseChangeLinearEquiv_cohomologyBaseChange_tmul (b : B)
    (x : Cohomology (Proj.twistingSheaf (𝒜 R) (-2)) 1) :
    cohomologyOneBaseChangeLinearEquiv R B
        (cohomologyBaseChange (projectiveLine.isPullback_baseChangeProjection R B) _ 1 (b ⊗ₜ x)) =
      cohomologyOneTwistingSheafNegTwoLinearEquiv R x • b := by
  have h : cohomologyBaseChange (projectiveLine.isPullback_baseChangeProjection R B) _ 1 (b ⊗ₜ x) =
      cohomologyBaseChangeLinearEquiv (projectiveLine.isPullback_baseChangeProjection R B)
        (Proj.twistingSheaf (𝒜 R) (-2)) 1 (b ⊗ₜ x) :=
    LinearMap.congr_fun (cohomologyBaseChangeLinearEquiv_toLinearMap _ _ _).symm _
  rw [h, cohomologyOneBaseChangeLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    AlgebraTensorModule.rid_tmul]

omit [Module.Flat R B] in
/-- Over the zero algebra `B`, which is flat over `R`, `H¹(ℙ¹_B, g^* 𝒪(-2))` vanishes, like
`B ⊗_R R`. -/
theorem subsingleton_cohomology_one_pullback_of_subsingleton [Subsingleton B] :
    Subsingleton (Cohomology ((Scheme.Modules.pullback
      (projectiveLine.baseChangeProjection R B)).obj (Proj.twistingSheaf (𝒜 R) (-2))) 1) :=
  haveI : Module.Free R B := Module.Free.of_subsingleton R B
  (cohomologyOneBaseChangeLinearEquiv R B).toEquiv.subsingleton

end BaseChange

end TauCeti.AlgebraicGeometry.ProjectiveLineCohomologyExample
