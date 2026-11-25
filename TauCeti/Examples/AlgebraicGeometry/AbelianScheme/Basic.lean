/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.AbelianVariety
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.AbelianVariety
public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# Tests for abelian schemes

* An elliptic curve `E` over a field `K`, made an abelian scheme over `Spec K` by
  `AbelianScheme.ofAbelianVariety` and turned back by `AbelianScheme.toAbelianVariety`, is
  `E.toAbelianVariety` again. Its group scheme is the projective model of `E`, with the zero
  section `[0 : 1 : 0]` as unit and the addition morphism as multiplication.
* For `S = ℙ¹_K` and the constant elliptic scheme `E × S`, the base change of the abelian variety
  of `E` along `ℙ¹_K ⟶ Spec K`, the point groups of its restrictions to the two standard affine
  charts `Spec K[X] ⟶ ℙ¹_K` and to their intersection are the point groups of `E × S` over the same
  test schemes viewed over `S`, by `TauCeti.GroupScheme.baseChangePointMulEquiv`. The comparison
  uses the carrier `Over S` although `S` is not affine.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj Polynomial
open TauCeti.AlgebraicGeometry TauCeti.GroupScheme

universe u

namespace TauCeti.Examples.AbelianScheme

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-! ### An elliptic curve through `ofAbelianVariety` and `toAbelianVariety` -/

/-- `ofAbelianVariety` followed by `toAbelianVariety` returns the abelian variety of `E`. -/
example :
    (AbelianScheme.ofAbelianVariety W.toAbelianVariety).toAbelianVariety = W.toAbelianVariety :=
  AbelianScheme.toAbelianVariety_ofAbelianVariety _

/-- The group scheme of the abelian scheme attached to `E` is the projective model of `E`. -/
example : (AbelianScheme.ofAbelianVariety W.toAbelianVariety).toOver = Over.mk W.projModelOver :=
  W.toAbelianVariety_toOver

/-- The unit of the abelian scheme attached to `E` is the zero section of the projective model. -/
example : η[(AbelianScheme.ofAbelianVariety W.toAbelianVariety).toOver] ≫
      eqToHom W.toAbelianVariety_toOver = η[Over.mk W.projModelOver] :=
  W.toAbelianVariety_one

/-- The multiplication of the abelian scheme attached to `E` is the addition morphism of the
projective model. -/
example : (μ[(AbelianScheme.ofAbelianVariety W.toAbelianVariety).toOver] ≫
      eqToHom W.toAbelianVariety_toOver).left =
      (eqToHom W.toAbelianVariety_toOver ⊗ₘ eqToHom W.toAbelianVariety_toOver).left ≫
        W.additionMorphism := by
  have h := congrArg Over.Hom.left W.toAbelianVariety_mul
  rw [Over.comp_left, Over.comp_left, WeierstrassCurve.mul_projModelOver_left] at h
  rw [Over.comp_left]
  exact h

/-! ### The constant elliptic scheme over `ℙ¹` -/

/-- The constant elliptic scheme `E × ℙ¹_K` over `ℙ¹_K`. -/
noncomputable abbrev constantOverProjectiveLine :
    TauCeti.AlgebraicGeometry.AbelianScheme (projectiveLine K) :=
  (AbelianScheme.ofAbelianVariety W.toAbelianVariety).baseChange
    (projectiveLine K ↘ Spec (.of K))

/-- The inclusion of the intersection of the two standard affine charts of `ℙ¹_K`. -/
noncomputable abbrev chartIntersectionι :
    pullback (projectiveLine.polynomialChartι K 0) (projectiveLine.polynomialChartι K 1) ⟶
      projectiveLine K :=
  pullback.fst _ _ ≫ projectiveLine.polynomialChartι K 0

/-- On the standard chart `Spec K[X] ⟶ ℙ¹_K` with index `i`, the points of the restriction of
`E × ℙ¹_K` are the points of `E × ℙ¹_K` over the same test scheme viewed over `ℙ¹_K`. -/
noncomputable example (i : Fin 2) (T : Over (Spec (.of K[X]))) :
    (T ⟶ ((constantOverProjectiveLine W).baseChange (projectiveLine.polynomialChartι K i)).toOver)
      ≃* ((Over.map (projectiveLine.polynomialChartι K i)).obj T ⟶
        (constantOverProjectiveLine W).toOver) :=
  baseChangePointMulEquiv _ (Grp.mk (constantOverProjectiveLine W).toOver) T

/-- On the intersection of the two standard charts, the points of the restriction of
`E × ℙ¹_K` are the points of `E × ℙ¹_K` over the same test scheme viewed over `ℙ¹_K`. -/
noncomputable example (T : Over (pullback (projectiveLine.polynomialChartι K 0)
      (projectiveLine.polynomialChartι K 1))) :
    (T ⟶ ((constantOverProjectiveLine W).baseChange (chartIntersectionι (K := K))).toOver) ≃*
      ((Over.map (chartIntersectionι (K := K))).obj T ⟶ (constantOverProjectiveLine W).toOver) :=
  baseChangePointMulEquiv _ (Grp.mk (constantOverProjectiveLine W).toOver) T

/-- The points of `E × ℙ¹_K` over `ℙ¹_K` are the points of `E` over `ℙ¹_K` viewed over `Spec K`,
so the point groups of all the restrictions above are point groups of `E`. -/
noncomputable example (T : Over (projectiveLine K)) :
    (T ⟶ (constantOverProjectiveLine W).toOver) ≃*
      ((Over.map (projectiveLine K ↘ Spec (.of K))).obj T ⟶
        (AbelianScheme.ofAbelianVariety W.toAbelianVariety).toOver) :=
  baseChangePointMulEquiv _ (Grp.mk (AbelianScheme.ofAbelianVariety W.toAbelianVariety).toOver) T

end TauCeti.Examples.AbelianScheme
