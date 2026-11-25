/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered
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
(`TauCeti.UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials`). Each
`‖dπ(X^α) v‖` is at most `Q_k(v)`, so the triangle inequality gives the bound, with `C_k` the sum
of the absolute values of the coefficients.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials`: the
  ordered PBW monomials of degree at most `k` are the monomials `X^α` with `|α| ≤ k`.
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

namespace TauCeti.UniversalEnvelopingAlgebra

/-- The ordered PBW monomials of degree at most `k` in a family `X₁, …, X_m` are exactly the
monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}` of the exponent vectors `α` in `SobolevIndex m k`. -/
theorem range_pbwMonomial_monomialWord_eq_orderedPBWMonomials (R : Type*) (L : Type*)
    [CommRing R] [LieRing L] [LieAlgebra R L] {m : ℕ} (X : Fin m → L) (k : ℕ) :
    Set.range (fun α : SobolevIndex m k ↦ pbwMonomial R L X (monomialWord α.exponent)) =
      orderedPBWMonomials R L X k := by
  ext a
  refine ⟨?_, ?_⟩
  · rintro ⟨α, rfl⟩
    refine pbwMonomial_mem_orderedPBWMonomials R L X (pairwise_monomialWord _) ?_
    rw [length_monomialWord]
    simpa only [SobolevIndex.exponent_apply] using α.property
  · intro ha
    obtain ⟨word, hsorted, hlength, rfl⟩ := (mem_orderedPBWMonomials_iff R L X).1 ha
    obtain ⟨α, hα⟩ := exists_sobolevIndex_monomialWord_eq hsorted hlength
    exact ⟨α, congrArg (pbwMonomial R L X) hα⟩

end TauCeti.UniversalEnvelopingAlgebra

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

omit [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V] in
/-- The term of an ordered monomial is bounded by the Sobolev seminorm. -/
theorem norm_wordAction_monomialWord_le_sobolevSeminorm
    (X : Fin m → LeftInvariantDerivation I G) {k : ℕ} (α : SobolevIndex m k)
    (v : lieSmoothVectors I π) :
    ‖(wordAction I π X (monomialWord α.exponent) v : V)‖ ≤ sobolevSeminorm I π X k v := by
  rw [← sobolevVector_apply]
  refine (PiLp.norm_apply_le (sobolevVector I π X k v) α).trans_eq ?_
  rw [sobolevSeminorm_apply, PiLp.norm_eq_of_L2]
  simp only [sobolevVector_apply]

/-- **The word seminorm is bounded by a multiple of the Sobolev seminorm.** For a spanning family
`X₁, …, X_m` of the Lie algebra and every order `k` there is `C_k` with `P_k ≤ C_k Q_k`. -/
theorem exists_wordSeminorm_le_mul_sobolevSeminorm (X : Fin m → LeftInvariantDerivation I G)
    (hX : Submodule.span ℝ (Set.range X) = ⊤) (k : ℕ) :
    ∃ C : ℝ, ∀ v : lieSmoothVectors I π,
      wordSeminorm I π X k v ≤ C * sobolevSeminorm I π X k v := by
  classical
  -- Every word of length at most `k` is a combination of the ordered monomials `X^α`.
  have hspan : ∀ w : BoundedWord (Fin m) k, ∃ c : SobolevIndex m k → ℝ,
      ∑ α, c α • UniversalEnvelopingAlgebra.pbwMonomial ℝ _ X (monomialWord α.exponent) =
        UniversalEnvelopingAlgebra.pbwMonomial ℝ _ X (List.ofFn w.2) := by
    intro w
    refine (Submodule.mem_span_range_iff_exists_fun ℝ).1 ?_
    rw [UniversalEnvelopingAlgebra.range_pbwMonomial_monomialWord_eq_orderedPBWMonomials,
      UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration ℝ _ X hX]
    refine UniversalEnvelopingAlgebra.pbwFiltration_mono ℝ _ ?_
      (UniversalEnvelopingAlgebra.pbwMonomial_mem_pbwFiltration ℝ _ X _)
    rw [List.length_ofFn]
    exact Nat.lt_succ_iff.1 w.1.isLt
  choose c hc using hspan
  refine ⟨∑ w, ∑ α, |c w α|, fun v ↦ ?_⟩
  rw [wordSeminorm_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  rw [wordAction_eq_lieSmoothVectorsEnvelopingAction, ← hc w, Finset.sum_mul]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, ← wordAction_eq_lieSmoothVectorsEnvelopingAction]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_wordAction_monomialWord_le_sobolevSeminorm X α v)
    (abs_nonneg _)

end ContRepresentation
