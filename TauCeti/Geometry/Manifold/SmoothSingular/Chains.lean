/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

/-!
# Smooth singular chains

Apply Mathlib's simplicial chain-complex functor to the smooth singular subcomplex.
The resulting differential is the alternating sum of the faces of smooth simplices,
and the inclusion into continuous singular chains is a degreewise monomorphism.
Coefficients may be taken in any preadditive category with the required coproducts;
in particular, this gives real smooth singular chains.

This construction supplies the chains on which differential forms can be integrated.
It does not assert the smoothing equivalence, which requires additional manifold and
approximation hypotheses.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 18.
* The chain complex and its differential use Mathlib's `SSet.chainComplex` and
  `SSet.ιChainComplex_d`, without a separate boundary-square calculation.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Manifold Simplicial

namespace TauCeti

universe w v u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type w) [TopologicalSpace M] [ChartedSpace H M]
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)

/-- The smooth singular chain complex with coefficients in `R`. -/
abbrev smoothSingularChainComplex : ChainComplex C ℕ :=
  (smoothSingularSubcomplex I M : SSet).chainComplex R

/-- Inclusion of smooth singular chains into continuous singular chains. -/
def smoothToSingular : smoothSingularChainComplex I M R ⟶
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of M) :=
  SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R

/-- The inclusion of smooth chains is a monomorphism in every degree. -/
instance (n : ℕ) : Mono ((smoothToSingular I M R).f n) :=
  inferInstanceAs (Mono ((sigmaConst.obj R).map
    ((smoothSingularSubcomplex I M).ι.app (Opposite.op ⦋n⦌))))

instance : Mono (smoothToSingular I M R) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

namespace SmoothSimplex

variable {I M} {n : ℕ}

/-- The inclusion of the coefficient summand indexed by a smooth simplex. -/
abbrev chain (σ : SmoothSimplex I M n) : R ⟶ (smoothSingularChainComplex I M R).X n :=
  (smoothSingularSubcomplex I M : SSet).ιChainComplex σ

/-- The boundary of a smooth simplex is the alternating sum of its faces. -/
-- Not a simp lemma: the generic simplicial boundary formula is already in simp normal form.
@[reassoc]
theorem chain_d (σ : SmoothSimplex I M (n + 1)) :
    σ.chain R ≫ (smoothSingularChainComplex I M R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ i.val • (σ.face i).chain R := by
  simpa only [face_eq_delta] using SSet.ιChainComplex_d _ R σ

/-- Inclusion into continuous chains preserves the coefficient and the underlying simplex. -/
@[reassoc (attr := simp)]
theorem chain_smoothToSingular (σ : SmoothSimplex I M n) :
    σ.chain R ≫ (smoothToSingular I M R).f n =
      (TopCat.toSSet.obj (TopCat.of M)).ιChainComplex σ.val :=
  SSet.ι_chainComplexMap_f _ _ _ R σ

end SmoothSimplex

end TauCeti
