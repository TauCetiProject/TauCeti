/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.MonomialWord
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Enveloping
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Seminorm

/-!
# Word seminorms are bounded by Sobolev seminorms

Let `π` be a continuous representation of a real Lie group `G` and `X₁, …, X_m` a spanning
family of its Lie algebra of left-invariant derivations. The word seminorm
`P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖` sums over all words of length at most `k`, the Sobolev seminorm
`Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}` only over the ordered monomials
`X^α = X₁^{α₁} ⋯ X_m^{α_m}`, and `Q_k ≤ P_k` is
`ContRepresentation.sobolevSeminorm_le_wordSeminorm`. This file proves the converse bound
`P_k ≤ C_k Q_k` (`ContRepresentation.exists_wordSeminorm_le_mul_sobolevSeminorm`).

The operator `dπ(X_w)` of a word is the action of the monomial `X_w` of the universal enveloping
algebra (`ContRepresentation.wordAction_eq_lieSmoothVectorsEnvelopingAction`). By the spanning
half of the Poincaré–Birkhoff–Witt theorem
(`TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`), `X_w` is a real
linear combination of ordered monomials of degree at most `k`, and these are exactly the monomials
`X^α` with `α` in `SobolevIndex m k`
(`TauCeti.UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials`). So
in any algebra receiving `U(L)`, the image of a word of length at most `k` is a combination of the
images of the ordered monomials of degree at most `k`
(`TauCeti.UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord`). For the operators
`dπ(X_i)` the comparison of the word and Sobolev seminorms along a family of operators
(`LinearMap.exists_endWordSeminorm_le_mul_endSobolevSeminorm`) then gives the bound.

## Main results

* `ContRepresentation.wordAction_eq_lieSmoothVectorsEnvelopingAction`: `dπ(X_w)` is the action of
  the PBW monomial `X_w`.
* `ContRepresentation.exists_wordSeminorm_le_mul_sobolevSeminorm`: `P_k ≤ C_k Q_k`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §2.4.2–§2.4.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The operator of a word is the action of its PBW monomial**: `dπ(X_w)` is the action of
`X_w = ι(X_{i₁}) ⋯ ι(X_{iₙ})` on the smooth vectors. -/
theorem wordAction_eq_lieSmoothVectorsEnvelopingAction {R : Type*} [Ring R] [Module R V]
    [Algebra ℝ R] [IsScalarTower ℝ R V] [ContinuousConstSMul R V]
    {π : ContRepresentation R G V} {ι : Type*} (X : ι → LeftInvariantDerivation I G)
    (w : List ι) :
    wordAction I π X w =
      lieSmoothVectorsEnvelopingAction I π
        (UniversalEnvelopingAlgebra.pbwMonomial ℝ (LeftInvariantDerivation I G) X w) := by
  induction w with
  | nil => rw [wordAction_nil, UniversalEnvelopingAlgebra.pbwMonomial_nil, map_one]
  | cons i w ih =>
    rw [wordAction_cons, ih, UniversalEnvelopingAlgebra.pbwMonomial_cons, map_mul,
      lieSmoothVectorsEnvelopingAction_ι]

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V] {π : ContRepresentation 𝕜 G V} {m : ℕ}

/-- **The word seminorm is bounded by a multiple of the Sobolev seminorm.** For a spanning family
`X₁, …, X_m` of the Lie algebra and every order `k` there is `C_k` with `P_k ≤ C_k Q_k`. -/
theorem exists_wordSeminorm_le_mul_sobolevSeminorm (X : Fin m → LeftInvariantDerivation I G)
    (hX : Submodule.span ℝ (Set.range X) = ⊤) (k : ℕ) :
    ∃ C : ℝ, ∀ v : lieSmoothVectors I π,
      wordSeminorm I π X k v ≤ C * sobolevSeminorm I π X k v := by
  simp only [wordSeminorm_eq_endWordSeminorm, sobolevSeminorm_eq_endSobolevSeminorm]
  refine LinearMap.exists_endWordSeminorm_le_mul_endSobolevSeminorm _ _ fun _ hw ↦
    Submodule.span_le_restrictScalars ℝ 𝕜 _ ?_
  simpa only [lieSmoothVectorsEnvelopingAction_ι] using
    UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord ℝ
      (lieSmoothVectorsEnvelopingAction I π) X hX hw

end ContRepresentation
