/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Power
public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Proj

/-!
# Power morphisms of projective space

On the affine chart of a cone contained in the maximal cone omitting the ray `k`, the homogeneous
coordinate ratios `X_j / X_k` are monomials. The toric power morphism `φ_q` acts on a chart by
raising every monomial to its `q`-th power
(`TauCeti.Toric.Fan.affineToricChartι_comp_algebraicMap_nsmulHom`), so it pulls each ratio
`X_j / X_k` back to `(X_j / X_k) ^ q`. In homogeneous coordinates, `φ_q` is the map
`[X_j] ↦ [X_j ^ q]`. For the projective line this is `[x₀ : x₁] ↦ [x₀ ^ q : x₁ ^ q]`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §8, the paragraph preceding
  Theorem 8.5.
-/

public section

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] {b : Module.Basis ι ℤ N} {i : N →+ V} {hi : IsIntegralLattice i}
  {σ : PointedCone ℝ V}

/-- Raising monomials to the `q`-th power, the coordinate-ring map of the toric power morphism,
sends the homogeneous coordinate ratio `X_j / X_k` to its `q`-th power. -/
theorem mapDomainRingHom_powMonoidHom_projectiveSpaceRatioMonomial (q : ℕ) {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) (j : Option ι) :
    MonoidAlgebra.mapDomainRingHom ℂ (powMonoidHom q) (projectiveSpaceRatioMonomial b hi hσ j) =
      projectiveSpaceRatioMonomial b hi hσ j ^ q := by
  simp [projectiveSpaceRatioMonomial_def, MonoidAlgebra.single_pow]

end TauCeti.Toric
