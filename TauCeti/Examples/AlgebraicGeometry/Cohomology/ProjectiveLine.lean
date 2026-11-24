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
* `H⁰(ℙ¹_k, 𝒪(1))` has dimension `2` over a field `k`, and has rank `2` over every
  nontrivial ring (`finrank_cohomology_zero_twistingSheaf_one`).
* For a flat `R`-algebra `B`, flat base change along `ℙ¹_B ⟶ ℙ¹_R` identifies
  `H¹(ℙ¹_B, g^* 𝒪(-2))` with `B ⊗_R R ≅ B`
  (`cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv`), sending the base change `b ⊗ x`
  of a class `x ∈ H¹(ℙ¹_R, 𝒪(-2)) ≅ R` to `b` times the image of `x`
  (`cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv_cohomologyBaseChange_tmul`). For the
  zero algebra both sides are zero (`subsingleton_cohomology_one_pullback_of_subsingleton`).

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

/-- `H¹(ℙ¹_R, 𝒪(-2))` has rank one. -/
theorem finrank_cohomology_one_twistingSheaf_neg_two [Nontrivial R] :
    Module.finrank R (Cohomology (Proj.twistingSheaf (𝒜 R) (-2)) 1) = 1 := by
  have h := projectiveLine.finrank_cohomology_one_twistingSheaf R (n := -2) le_rfl
  omega

/-- **`H¹(ℙ¹_R, 𝒪(-2)) ≅ R`** over every commutative ring `R`: `H¹(ℙ¹_R, 𝒪(-2))` is the module of
forms of degree `0`, which are the scalars. -/
def cohomologyOneTwistingSheafNegTwoLinearEquiv :
    Cohomology (Proj.twistingSheaf (𝒜 R) (-2)) 1 ≃ₗ[R] R :=
  projectiveLine.cohomologyOneTwistingSheafLinearEquiv R 0 ≪≫ₗ
    TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv R (Fin 2 → R)

/-- The inverse of `H¹(ℙ¹_R, 𝒪(-2)) ≅ R` sends `r` to the Mayer–Vietoris boundary of the section
`r / (X₀X₁)` over the overlap of the standard charts. -/
theorem cohomologyOneTwistingSheafNegTwoLinearEquiv_symm_apply (r : R) :
    (cohomologyOneTwistingSheafNegTwoLinearEquiv R).symm r =
      mayerVietorisBoundaryLinear _ _ _ (projectiveLine.basicOpen_coord_sup_eq_top R)
        (Proj.twistingSheaf.const (i := 2) (j := 0) (by norm_num)
          (algebraMap R (SymmetricAlgebra R (Fin 2 → R)) r)
          ((projectiveLine.coord R 0 * projectiveLine.coord R 1) ^ 1)
          (SetLike.algebraMap_mem_graded _ r) (projectiveLine.coord_mul_coord_pow_mem R 1) _
          (projectiveLine.inf_le_basicOpen_coord_mul_coord_pow R)) := by
  rw [cohomologyOneTwistingSheafNegTwoLinearEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    projectiveLine.cohomologyOneTwistingSheafLinearEquiv_symm_apply]
  simp only [TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleZeroEquiv_symm_apply]
  -- The two sides differ only in the numerals `-(0 + 2)`, `(0 + 1) * 2` and `0 + 1`.
  rfl

/-- `H⁰(ℙ¹_R, 𝒪(1))` has rank two, spanned by the pair of coordinates `X₀, X₁`. -/
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
def cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv :
    Cohomology ((Scheme.Modules.pullback (projectiveLine.baseChangeProjection R B)).obj
      (Proj.twistingSheaf (𝒜 R) (-2))) 1 ≃ₗ[B] B :=
  (cohomologyBaseChangeLinearEquiv (projectiveLine.isPullback_baseChangeProjection R B) _ 1).symm
    ≪≫ₗ (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (cohomologyOneTwistingSheafNegTwoLinearEquiv R)) ≪≫ₗ AlgebraTensorModule.rid R B B

/-- The flat base change isomorphism `H¹(ℙ¹_B, g^* 𝒪(-2)) ≅ B` sends the pullback of a class
`x ∈ H¹(ℙ¹_R, 𝒪(-2))` to the image in `B` of `x` under `H¹(ℙ¹_R, 𝒪(-2)) ≅ R`. -/
@[simp]
theorem cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv_cohomologyPullback
    (x : Cohomology (Proj.twistingSheaf (𝒜 R) (-2)) 1) :
    cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv R B
        ((projectiveLine.baseChangeProjection R B).cohomologyPullback _ 1 x) =
      algebraMap R B (cohomologyOneTwistingSheafNegTwoLinearEquiv R x) := by
  rw [← one_smul B ((projectiveLine.baseChangeProjection R B).cohomologyPullback _ 1 x),
    ← cohomologyBaseChangeLinearEquiv_tmul (projectiveLine.isPullback_baseChangeProjection R B),
    cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The flat base change isomorphism `H¹(ℙ¹_B, g^* 𝒪(-2)) ≅ B` sends the base change of
`b ⊗ x` to `b` times the image of `x` under `H¹(ℙ¹_R, 𝒪(-2)) ≅ R`: on `B ⊗_R R ≅ B` it is
`b ⊗ a ↦ a b`. -/
theorem cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv_cohomologyBaseChange_tmul (b : B)
    (x : Cohomology (Proj.twistingSheaf (𝒜 R) (-2)) 1) :
    cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv R B
        (cohomologyBaseChange (projectiveLine.isPullback_baseChangeProjection R B) _ 1 (b ⊗ₜ x)) =
      cohomologyOneTwistingSheafNegTwoLinearEquiv R x • b := by
  rw [cohomologyBaseChange_tmul, LinearEquiv.map_smul,
    cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv_cohomologyPullback, smul_eq_mul,
    Algebra.smul_def, mul_comm]

omit [Module.Flat R B] in
/-- Over the zero algebra `B`, which is flat over `R`, `H¹(ℙ¹_B, g^* 𝒪(-2))` vanishes, like
`B ⊗_R R`. -/
theorem subsingleton_cohomology_one_pullback_of_subsingleton [Subsingleton B] :
    Subsingleton (Cohomology ((Scheme.Modules.pullback
      (projectiveLine.baseChangeProjection R B)).obj (Proj.twistingSheaf (𝒜 R) (-2))) 1) :=
  haveI : Module.Free R B := Module.Free.of_subsingleton R B
  (cohomologyOneTwistingSheafNegTwoBaseChangeLinearEquiv R B).toEquiv.subsingleton

end BaseChange

end TauCeti.AlgebraicGeometry.ProjectiveLineCohomologyExample
