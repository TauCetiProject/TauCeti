/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import TauCeti.Analysis.Normed.Module.Quotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Kolmogorov numbers

The zero-based Kolmogorov number `dₙ(T)` is the infimum of the norms of `T` followed by
quotient projections by subspaces of dimension at most `n`. The quotient seminorm is used
even when the subspace is not closed. This definition works over every nontrivially normed
field; its closed-unit-ball interpretation requires a densely normed field.

We prove the norm, monotonicity, mixed-index additivity and multiplicativity, perturbation,
ideal and rank laws over every nontrivially normed field. Over a complete scalar field,
finite-dimensional subspaces are closed, and the Kolmogorov numbers form a strict s-number
sequence. No completeness of the domain or codomain is needed.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §§4, 9
  (Theorem 9.5).
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Kolmogorov.lean`: an earlier Lean formalization of Kolmogorov numbers and their
  index laws.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The `n`-th Kolmogorov number is the best quotient norm obtained by removing a subspace
of dimension at most `n` from the codomain. Indexing starts at zero. -/
noncomputable def kolmogorovNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨅ V : {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n}, ‖V.1.mkQL ∘L T‖₊

/-- The quotient-norm formula for the Kolmogorov numbers. -/
theorem kolmogorovNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n =
      ⨅ V : {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n}, ‖V.1.mkQL ∘L T‖₊ := (rfl)

private instance (n : ℕ) : Nonempty {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n} :=
  ⟨⟨⊥, by simp⟩⟩

/-- Each admissible subspace gives an upper bound on the Kolmogorov number. -/
theorem kolmogorovNumber_le (T : E →L[𝕜] F) {n : ℕ} {V : Submodule 𝕜 F}
    (hV : Module.rank 𝕜 V ≤ n) : T.kolmogorovNumber n ≤ ‖V.mkQL ∘L T‖₊ := by
  rw [kolmogorovNumber_def]
  exact ciInf_le (f := fun V : {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n} ↦
    ‖V.1.mkQL ∘L T‖₊) (OrderBot.bddBelow _) ⟨V, hV⟩

/-- Lower bounds can be checked on all admissible quotient norms. -/
theorem le_kolmogorovNumber_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    c ≤ T.kolmogorovNumber n ↔
      ∀ V : Submodule 𝕜 F, Module.rank 𝕜 V ≤ n → c ≤ ‖V.mkQL ∘L T‖₊ := by
  rw [kolmogorovNumber_def]
  exact (le_ciInf_iff (OrderBot.bddBelow _)).trans Subtype.forall

/-- A strict upper bound admits a subspace with strictly smaller quotient norm. -/
theorem exists_nnnorm_mkQL_comp_lt_of_kolmogorovNumber_lt
    {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : T.kolmogorovNumber n < c) :
    ∃ V : Submodule 𝕜 F, Module.rank 𝕜 V ≤ n ∧ ‖V.mkQL ∘L T‖₊ < c := by
  rw [kolmogorovNumber_def] at h
  obtain ⟨⟨V, hV⟩, hlt⟩ := exists_lt_of_ciInf_lt h
  exact ⟨V, hV, hlt⟩

/-- Kolmogorov numbers decrease with the index. -/
theorem antitone_kolmogorovNumber (T : E →L[𝕜] F) : Antitone T.kolmogorovNumber :=
  fun _ _ hmn ↦ le_kolmogorovNumber_iff.mpr fun _ hV ↦
    T.kolmogorovNumber_le (hV.trans (by exact_mod_cast hmn))

/-- Every Kolmogorov number is bounded by the operator norm. -/
theorem kolmogorovNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n ≤ ‖T‖₊ := by
  refine (T.kolmogorovNumber_le (V := ⊥) (by simp)).trans ?_
  exact (⊥ : Submodule 𝕜 F).nnnorm_mkQL_comp_le T

/-- The zeroth Kolmogorov number is the operator norm. -/
@[simp]
theorem kolmogorovNumber_zero (T : E →L[𝕜] F) : T.kolmogorovNumber 0 = ‖T‖₊ := by
  refine (T.kolmogorovNumber_le_nnnorm 0).antisymm (le_kolmogorovNumber_iff.mpr ?_)
  intro V hV
  have hbot : V = ⊥ := Submodule.rank_eq_zero.mp (by simpa using hV)
  subst V
  exact_mod_cast T.opNorm_le_bound (norm_nonneg _) (fun x ↦ by
    have h := ((⊥ : Submodule 𝕜 F).mkQL ∘L T).le_opNorm x
    simpa only [comp_apply, Submodule.norm_mkQL_apply, Submodule.bot_coe,
      Metric.infDist_singleton, dist_zero_right] using h)

/-- Kolmogorov numbers of the zero operator vanish. -/
@[simp]
theorem zero_kolmogorovNumber (n : ℕ) : (0 : E →L[𝕜] F).kolmogorovNumber n = 0 := by
  simpa using (0 : E →L[𝕜] F).kolmogorovNumber_le_nnnorm n

/-- Rank at most `n` forces the `n`-th Kolmogorov number to vanish. -/
theorem kolmogorovNumber_eq_zero_of_rank_le {T : E →L[𝕜] F} {n : ℕ}
    (hT : T.rank ≤ n) : T.kolmogorovNumber n = 0 := by
  have hz : T.range.mkQL ∘L T = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ x)
  simpa [hz] using T.kolmogorovNumber_le hT

/-- **Mixed-index additive inequality.** `d_{m+n}(S + T) ≤ dₘ(S) + dₙ(T)`, witnessed on the
sum of subspaces admissible for `S` and `T`. -/
theorem kolmogorovNumber_add_index_le (S T : E →L[𝕜] F) (m n : ℕ) :
    (S + T).kolmogorovNumber (m + n) ≤ S.kolmogorovNumber m + T.kolmogorovNumber n := by
  rw [kolmogorovNumber_def S, kolmogorovNumber_def T]
  refine NNReal.le_iInf_add_iInf fun V W ↦ ?_
  have hrank : Module.rank 𝕜 ↥(V.1 ⊔ W.1) ≤ ↑(m + n) := by
    rw [Nat.cast_add]
    exact (Submodule.rank_add_le_rank_add_rank V.1 W.1).trans (add_le_add V.2 W.2)
  refine ((S + T).kolmogorovNumber_le hrank).trans ?_
  rw [comp_add]
  exact (nnNorm_add_le _ _).trans
    (add_le_add (Submodule.nnnorm_mkQL_comp_antitone S le_sup_left)
      (Submodule.nnnorm_mkQL_comp_antitone T le_sup_right))

/-- The Kolmogorov number of `S + T` exceeds that of `S` by at most `‖T‖₊`. -/
theorem kolmogorovNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).kolmogorovNumber n ≤ S.kolmogorovNumber n + ‖T‖₊ := by
  simpa using S.kolmogorovNumber_add_index_le T n 0

/-- **Mixed-index product inequality.** `d_{m+n}(S T) ≤ dₘ(S) dₙ(T)`, witnessed on `W + S(V)`
for subspaces `W` admissible for `S` and `V` admissible for `T`. -/
theorem kolmogorovNumber_comp_add_le_mul (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    (S ∘L T).kolmogorovNumber (m + n) ≤ S.kolmogorovNumber m * T.kolmogorovNumber n := by
  rw [kolmogorovNumber_def S, NNReal.iInf_mul]
  refine le_ciInf fun W ↦ ?_
  rw [kolmogorovNumber_def T, NNReal.mul_iInf]
  refine le_ciInf fun V ↦ ?_
  let U := W.1 ⊔ V.1.map S.toLinearMap
  have hSV : Module.rank 𝕜 ↥(V.1.map S.toLinearMap) ≤ n :=
    Cardinal.lift_le_nat_iff.mp
      ((lift_rank_map_le S.toLinearMap V.1).trans (Cardinal.lift_le_nat_iff.mpr V.2))
  have hU : Module.rank 𝕜 U ≤ ↑(m + n) := by
    rw [Nat.cast_add]
    exact (Submodule.rank_add_le_rank_add_rank _ _).trans (add_le_add W.2 hSV)
  have hker : V.1 ≤ (U.mkQL ∘L S).ker := fun x hx ↦
    (Submodule.Quotient.mk_eq_zero U).mpr (Submodule.mem_sup_right ⟨x, hx, rfl⟩)
  have heq : U.mkQL ∘L (S ∘L T) = (V.1.liftQL (U.mkQL ∘L S) hker) ∘L (V.1.mkQL ∘L T) := by
    ext x; rfl
  refine ((S ∘L T).kolmogorovNumber_le hU).trans ?_
  rw [heq]
  refine (opNNNorm_comp_le _ _).trans ?_
  gcongr
  have hlift : ‖V.1.liftQL (U.mkQL ∘L S) hker‖₊ = ‖U.mkQL ∘L S‖₊ :=
    Subtype.ext (V.1.norm_liftQL (U.mkQL ∘L S) hker)
  exact hlift.trans_le (Submodule.nnnorm_mkQL_comp_antitone S le_sup_left)

/-- Precomposition scales Kolmogorov numbers by at most the operator norm. -/
theorem kolmogorovNumber_comp_le_right (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (T ∘L A).kolmogorovNumber n ≤ T.kolmogorovNumber n * ‖A‖₊ := by
  simpa using T.kolmogorovNumber_comp_add_le_mul A n 0

/-- Postcomposition scales Kolmogorov numbers by at most the operator norm. -/
theorem kolmogorovNumber_comp_le_left (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T).kolmogorovNumber n ≤ ‖B‖₊ * T.kolmogorovNumber n := by
  simpa using B.kolmogorovNumber_comp_add_le_mul T 0 n

/-- The two-sided ideal inequality for Kolmogorov numbers. -/
theorem kolmogorovNumber_comp_comp_le (B : G →L[𝕜] H) (T : F →L[𝕜] G)
    (A : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T ∘L A).kolmogorovNumber n ≤ ‖B‖₊ * T.kolmogorovNumber n * ‖A‖₊ := by
  refine (B.kolmogorovNumber_comp_le_left (T ∘L A) n).trans ?_
  rw [mul_assoc]
  gcongr
  exact T.kolmogorovNumber_comp_le_right A n

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over a densely normed field, Kolmogorov numbers are the best deviations of the image
of the closed unit ball from subspaces of dimension at most `n`. -/
theorem kolmogorovNumber_eq_iInf_sSup_infNndist
    (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n =
      ⨅ V : {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n},
        sSup ((fun x ↦ Metric.infNndist (T x) (V.1 : Set F)) '' Metric.closedBall 0 1) := by
  rw [kolmogorovNumber_def]
  congr 1
  funext V
  rw [← (V.1.mkQL ∘L T).sSup_unitClosedBall_eq_nnNorm]
  congr 2
  funext x
  apply NNReal.coe_injective
  exact V.1.norm_mkQL_apply (T x)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Over a complete scalar field, the identity has Kolmogorov number one below the
cardinal dimension, and zero from the dimension onwards. -/
@[simp]
theorem kolmogorovNumber_id (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 X).kolmogorovNumber n =
      if (n : Cardinal) < Module.rank 𝕜 X then 1 else 0 := by
  split_ifs with hn
  · apply le_antisymm
    · exact ((ContinuousLinearMap.id 𝕜 X).kolmogorovNumber_le_nnnorm n).trans (by
        exact_mod_cast norm_id_le (𝕜 := 𝕜) (E := X))
    · apply le_kolmogorovNumber_iff.mpr
      intro V hV
      have : FiniteDimensional 𝕜 V :=
        Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
      have hproper : V ≠ ⊤ := by
        intro h
        subst V
        exact hn.not_ge (by simpa using hV)
      have hnot : ¬ Dense (V : Set X) := by
        intro h
        apply hproper
        apply SetLike.coe_injective
        exact V.isClosed_of_finiteDimensional.closure_eq.symm.trans h.closure_eq
      rw [comp_id]
      exact_mod_cast (V.norm_mkQL hnot).ge
  · exact kolmogorovNumber_eq_zero_of_rank_le
      ((LinearMap.rank_le_domain _).trans (le_of_not_gt hn))

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- The family of Kolmogorov numbers on normed spaces over the scalar field. -/
noncomputable def kolmogorov : SNumberFamily 𝕜 := fun T ↦ T.kolmogorovNumber

/-- Evaluation of the Kolmogorov family. -/
@[simp]
theorem kolmogorov_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : kolmogorov T n = T.kolmogorovNumber n := (rfl)

/-- Kolmogorov numbers form an additive family over every nontrivially normed field. -/
theorem additive_kolmogorov : Additive (kolmogorov (𝕜 := 𝕜)) :=
  fun S T m n ↦ S.kolmogorovNumber_add_index_le T m n

/-- Kolmogorov numbers form a multiplicative family over every nontrivially normed field. -/
theorem multiplicative_kolmogorov : Multiplicative (kolmogorov (𝕜 := 𝕜)) :=
  fun S T m n ↦ S.kolmogorovNumber_comp_add_le_mul T m n

/-- Over a complete scalar field, Kolmogorov numbers are a strict s-number sequence.
The normed spaces themselves need not be complete. -/
theorem isStrictSNumberSequence_kolmogorov [CompleteSpace 𝕜] :
    IsStrictSNumberSequence (kolmogorov (𝕜 := 𝕜)) :=
  .of_normalize_of_lt_rank
    (fun T ↦ T.kolmogorovNumber_zero)
    (fun T ↦ T.antitone_kolmogorovNumber)
    (fun S T n ↦ S.kolmogorovNumber_add_le T n)
    (fun B T A n ↦ B.kolmogorovNumber_comp_comp_le T A n)
    ContinuousLinearMap.kolmogorovNumber_eq_zero_of_rank_le
    fun n hn ↦ by simp [ContinuousLinearMap.kolmogorovNumber_id, hn]

/-- Kolmogorov numbers satisfy the s-number axioms over complete scalar fields. -/
theorem isSNumberSequence_kolmogorov [CompleteSpace 𝕜] :
    IsSNumberSequence (kolmogorov (𝕜 := 𝕜)) :=
  isStrictSNumberSequence_kolmogorov.toIsSNumberSequence

end TauCeti.SNumbers
