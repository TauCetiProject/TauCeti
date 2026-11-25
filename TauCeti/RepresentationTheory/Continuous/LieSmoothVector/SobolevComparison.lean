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
`X^α = X₁^{α₁} ⋯ X_m^{α_m}`, and `Q_k ≤ P_k` is on main
(`ContRepresentation.sobolevSeminorm_le_wordSeminorm`). This file proves the converse bound
`P_k ≤ C_k Q_k` (`ContRepresentation.exists_wordSeminorm_le_mul_sobolevSeminorm`).

The operator `dπ(X_w)` of a word is the action of the monomial `X_w` of the universal enveloping
algebra (`ContRepresentation.wordAction_eq_lieSmoothVectorsEnvelopingAction`). By the spanning
half of the Poincaré–Birkhoff–Witt theorem
(`TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`), `X_w` is a real
linear combination of ordered monomials of degree at most `k`, and an ordered word is the word
`TauCeti.monomialWord α` of its exponent vector (`TauCeti.monomialWord_count`). Each
`‖dπ(X^α) v‖` is at most `Q_k(v)`, so the triangle inequality gives the bound, with `C_k` the sum
of the absolute values of the coefficients.

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

omit [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V] in
/-- The term of an ordered monomial is bounded by the Sobolev seminorm. -/
theorem norm_wordAction_monomialWord_le_sobolevSeminorm
    (X : Fin m → LeftInvariantDerivation I G) {k : ℕ} (α : SobolevIndex m k)
    (v : lieSmoothVectors I π) :
    ‖(wordAction I π X (monomialWord α.exponent) v : V)‖ ≤ sobolevSeminorm I π X k v := by
  rw [sobolevSeminorm_apply]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun β : SobolevIndex m k ↦
    ‖(wordAction I π X (monomialWord β.exponent) v : V)‖ ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ α)

/-- **The word seminorm is bounded by a multiple of the Sobolev seminorm.** For a spanning family
`X₁, …, X_m` of the Lie algebra and every order `k` there is `C_k` with `P_k ≤ C_k Q_k`: by the
PBW theorem every word of length at most `k` is a real linear combination of ordered monomials of
degree at most `k`. -/
theorem exists_wordSeminorm_le_mul_sobolevSeminorm (X : Fin m → LeftInvariantDerivation I G)
    (hX : Submodule.span ℝ (Set.range X) = ⊤) (k : ℕ) :
    ∃ C : ℝ, ∀ v : lieSmoothVectors I π,
      wordSeminorm I π X k v ≤ C * sobolevSeminorm I π X k v := by
  classical
  set f : SobolevIndex m k → UniversalEnvelopingAlgebra ℝ (LeftInvariantDerivation I G) :=
    fun α ↦ UniversalEnvelopingAlgebra.pbwMonomial ℝ _ X (monomialWord α.exponent)
  -- Every word of length at most `k` is a combination of the ordered monomials `f α`.
  have hspan : ∀ w : BoundedWord (Fin m) k, ∃ c : SobolevIndex m k → ℝ,
      ∑ α, c α • f α = UniversalEnvelopingAlgebra.pbwMonomial ℝ _ X (List.ofFn w.2) := by
    intro w
    refine (Submodule.mem_span_range_iff_exists_fun ℝ).1 ?_
    have hrange : Set.range f =
        UniversalEnvelopingAlgebra.orderedPBWMonomials ℝ (LeftInvariantDerivation I G) X k := by
      ext a
      refine ⟨?_, ?_⟩
      · rintro ⟨α, rfl⟩
        refine UniversalEnvelopingAlgebra.pbwMonomial_mem_orderedPBWMonomials ℝ
          (LeftInvariantDerivation I G) X (pairwise_monomialWord _) ?_
        rw [length_monomialWord]
        simpa only [SobolevIndex.exponent_apply] using α.property
      · intro ha
        obtain ⟨word, hsorted, hlength, rfl⟩ :=
          (UniversalEnvelopingAlgebra.mem_orderedPBWMonomials_iff ℝ _ X).1 ha
        obtain ⟨α, hα⟩ := exists_sobolevIndex_monomialWord_eq hsorted hlength
        exact ⟨α, by simp only [f, hα]⟩
    rw [hrange, UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration ℝ _ X hX]
    refine UniversalEnvelopingAlgebra.pbwFiltration_mono ℝ _ ?_
      (UniversalEnvelopingAlgebra.pbwMonomial_mem_pbwFiltration ℝ _ X _)
    rw [List.length_ofFn]
    exact Nat.lt_succ_iff.1 w.1.isLt
  choose c hc using hspan
  refine ⟨∑ w, ∑ α, |c w α|, fun v ↦ ?_⟩
  rw [wordSeminorm_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  rw [wordAction_eq_lieSmoothVectorsEnvelopingAction, ← hc w, map_sum, Finset.sum_mul]
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
  rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul_of_tower, norm_smul,
    Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← wordAction_eq_lieSmoothVectorsEnvelopingAction]
  exact norm_wordAction_monomialWord_le_sobolevSeminorm X α v

end ContRepresentation
