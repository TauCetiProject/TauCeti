/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.Normed.Module.Quotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Lp.PiLp.ModuleTopology
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Kolmogorov numbers

The zero-based Kolmogorov number `dₙ(T)` is the infimum of the norms of `T` followed by
quotient projections by subspaces of dimension at most `n`. The quotient seminorm is used
even when the subspace is not closed. This definition works over every nontrivially normed
field; its closed-unit-ball interpretation requires a densely normed field.

We prove the norm, monotonicity, perturbation, ideal and rank laws, invariance under
precomposition with normed quotient maps (`NormedAddGroupHom.IsQuotient`), so that the
Kolmogorov numbers are surjective, the bound by approximation numbers, and the index laws: the
Kolmogorov numbers are additive, `d_{m+n}(S + T) ≤ dₘ(S) + dₙ(T)`, and multiplicative,
`d_{m+n}(S T) ≤ dₘ(S) dₙ(T)`; with one index zero these recover the perturbation and
postcomposition laws. The Kolmogorov numbers form an s-number sequence over every nontrivially
normed field, since all subspaces of finite Euclidean coordinate spaces are closed. Over a complete
scalar field, finite-dimensional subspaces of any normed space are closed, giving a strict
s-number sequence.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4, and
  Theorem 9.5 for additivity.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  blueprint Theorems 3.6 and 3.8, for the multiplicativity of Gelfand and Kolmogorov numbers.
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
  ⨅ V : {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n}, ‖V.val.mkQL ∘L T‖₊

/-- The quotient-norm formula for the Kolmogorov numbers. -/
theorem kolmogorovNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n =
      ⨅ V : {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n}, ‖V.val.mkQL ∘L T‖₊ := (rfl)

private instance (n : ℕ) : Nonempty {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n} :=
  ⟨⟨⊥, by simp⟩⟩

/-- Each admissible subspace gives an upper bound on the Kolmogorov number. -/
theorem kolmogorovNumber_le (T : E →L[𝕜] F) {n : ℕ} {V : Submodule 𝕜 F}
    (hV : Module.rank 𝕜 V ≤ n) : T.kolmogorovNumber n ≤ ‖V.mkQL ∘L T‖₊ := by
  rw [kolmogorovNumber_def]
  exact ciInf_le (f := fun V : {V : Submodule 𝕜 F // Module.rank 𝕜 V ≤ n} ↦
    ‖V.val.mkQL ∘L T‖₊) (OrderBot.bddBelow _) ⟨V, hV⟩

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

/-- **Mixed-index additivity.** `d_{m+n}(S + T) ≤ dₘ(S) + dₙ(T)`: quotient by the sum of
subspaces admissible for `S` and for `T`, of dimension at most `m + n`. -/
theorem kolmogorovNumber_add_index_le (S T : E →L[𝕜] F) (m n : ℕ) :
    (S + T).kolmogorovNumber (m + n) ≤ S.kolmogorovNumber m + T.kolmogorovNumber n := by
  rw [kolmogorovNumber_def S, kolmogorovNumber_def T]
  refine NNReal.le_iInf_add_iInf fun V W ↦ ?_
  have hrank : Module.rank 𝕜 ↥(V.val ⊔ W.val) ≤ ↑(m + n) := by
    rw [Nat.cast_add]
    exact (Submodule.rank_add_le_rank_add_rank _ _).trans (add_le_add V.property W.property)
  refine ((S + T).kolmogorovNumber_le hrank).trans ?_
  rw [comp_add]
  exact (nnNorm_add_le _ _).trans (add_le_add (Submodule.nnnorm_mkQL_comp_le_of_le le_sup_left S)
    (Submodule.nnnorm_mkQL_comp_le_of_le le_sup_right T))

/-- The Kolmogorov number of `S + T` exceeds that of `S` by at most `‖T‖₊`. -/
theorem kolmogorovNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).kolmogorovNumber n ≤ S.kolmogorovNumber n + ‖T‖₊ := by
  simpa using S.kolmogorovNumber_add_index_le T n 0

/-- Precomposition scales Kolmogorov numbers by at most the operator norm. -/
theorem kolmogorovNumber_comp_le_right (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (T ∘L A).kolmogorovNumber n ≤ T.kolmogorovNumber n * ‖A‖₊ := by
  rw [kolmogorovNumber_def T, NNReal.iInf_mul]
  refine le_ciInf fun V ↦ ((T ∘L A).kolmogorovNumber_le V.property).trans ?_
  simpa only [comp_assoc] using opNNNorm_comp_le (V.val.mkQL ∘L T) A

/-- **Mixed-index multiplicativity.** `d_{m+n}(S T) ≤ dₘ(S) dₙ(T)`: for `V` admissible for `T`
and `W` admissible for `S`, quotient by `W + S(V)`, of dimension at most `m + n`. -/
theorem kolmogorovNumber_comp_add_le_mul (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    (S ∘L T).kolmogorovNumber (m + n) ≤ S.kolmogorovNumber m * T.kolmogorovNumber n := by
  rw [kolmogorovNumber_def S, kolmogorovNumber_def T, NNReal.iInf_mul]
  refine le_ciInf fun W ↦ ?_
  rw [NNReal.mul_iInf]
  refine le_ciInf fun V ↦ ?_
  let U := W.val ⊔ V.val.map S.toLinearMap
  have hU : Module.rank 𝕜 U ≤ ↑(m + n) := by
    have hV : Module.rank 𝕜 (V.val.map S.toLinearMap) ≤ n := by
      have h := (lift_rank_map_le S.toLinearMap V.val).trans (Cardinal.lift_le.mpr V.property)
      simpa only [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] using h
    rw [Nat.cast_add]
    exact (Submodule.rank_add_le_rank_add_rank _ _).trans (add_le_add W.property hV)
  -- `S` maps `V` into `U`, so the quotient map `F → G ⧸ U` descends to `F ⧸ V`.
  have hker : V.val ≤ (U.mkQL ∘L S).ker := fun x hx ↦
    (Submodule.Quotient.mk_eq_zero U).mpr (le_sup_right (a := W.val) ⟨x, hx, rfl⟩)
  let D := V.val.liftQL (U.mkQL ∘L S) hker
  have hD : ‖D‖₊ ≤ ‖W.val.mkQL ∘L S‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, V.val.norm_liftQL]
    exact Submodule.norm_mkQL_comp_le_of_le le_sup_left S
  have heq : U.mkQL ∘L (S ∘L T) = D ∘L (V.val.mkQL ∘L T) := by
    ext x
    simp [D]
  refine ((S ∘L T).kolmogorovNumber_le hU).trans ?_
  rw [heq]
  exact (opNNNorm_comp_le _ _).trans (by gcongr)

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

/-- **Quotient invariance of Kolmogorov numbers.** Precomposing with a continuous linear operator
whose underlying bounded additive homomorphism is a normed quotient map leaves all Kolmogorov
numbers unchanged, over every nontrivially normed field. -/
theorem kolmogorovNumber_comp_of_isQuotient (T : F →L[𝕜] G) {Q : E →L[𝕜] F}
    (hQ : Q.toNormedAddGroupHom.IsQuotient) (n : ℕ) :
    (T ∘L Q).kolmogorovNumber n = T.kolmogorovNumber n := by
  simp only [kolmogorovNumber_def, ← comp_assoc, opNNNorm_comp_of_isQuotient _ hQ]

/-- Every Kolmogorov number is bounded above by the corresponding approximation number. -/
theorem kolmogorovNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n ≤ T.singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  simpa [R.kolmogorovNumber_eq_zero_of_rank_le hR] using R.kolmogorovNumber_add_le (T - R) n

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
        sSup ((fun x ↦ Metric.infNndist (T x) (V.val : Set F)) '' Metric.closedBall 0 1) := by
  rw [kolmogorovNumber_def]
  congr 1
  funext V
  rw [← (V.val.mkQL ∘L T).sSup_unitClosedBall_eq_nnNorm]
  congr 2
  funext x
  apply NNReal.coe_injective
  exact V.val.norm_mkQL_apply (T x)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]

/-- The identity has Kolmogorov number one below the dimension if every admissible subspace
is closed. -/
theorem kolmogorovNumber_id_eq_one_of_isClosed [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    {n : ℕ} (hn : (n : Cardinal) < Module.rank 𝕜 X)
    (hclosed : ∀ V : Submodule 𝕜 X, Module.rank 𝕜 V ≤ n → IsClosed (V : Set X)) :
    (ContinuousLinearMap.id 𝕜 X).kolmogorovNumber n = 1 := by
  have hnorm : ‖ContinuousLinearMap.id 𝕜 X‖₊ ≤ 1 := by
    exact_mod_cast norm_id_le (𝕜 := 𝕜) (E := X)
  refine le_antisymm (((ContinuousLinearMap.id 𝕜 X).kolmogorovNumber_le_nnnorm n).trans hnorm)
    (le_kolmogorovNumber_iff.mpr fun V hV ↦ ?_)
  have hnot : ¬ Dense (V : Set X) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      (hclosed V hV).submodule_topologicalClosure_eq]
    rintro rfl
    exact hn.not_ge (by simpa only [rank_top] using hV)
  rw [comp_id]
  exact_mod_cast (V.norm_mkQL hnot).ge

/-- Over a complete scalar field, the identity has Kolmogorov number one below the
cardinal dimension, and zero from the dimension onwards. -/
@[simp]
theorem kolmogorovNumber_id [CompleteSpace 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 X).kolmogorovNumber n =
      if (n : Cardinal) < Module.rank 𝕜 X then 1 else 0 := by
  split_ifs with hn
  · refine kolmogorovNumber_id_eq_one_of_isClosed hn fun V hV ↦ ?_
    have : FiniteDimensional 𝕜 V :=
      Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
    exact V.isClosed_of_finiteDimensional
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

/-- The Kolmogorov numbers are surjective: precomposing with a metric surjection leaves them
unchanged, over every nontrivially normed field. -/
theorem isSurjective_kolmogorov : IsSurjective (kolmogorov (𝕜 := 𝕜)) where
  comp_of_isQuotient T _ hQ n := T.kolmogorovNumber_comp_of_isQuotient hQ n

/-- Kolmogorov numbers satisfy the s-number axioms over every nontrivially normed field. -/
theorem isSNumberSequence_kolmogorov : IsSNumberSequence (kolmogorov (𝕜 := 𝕜)) where
  norm T := T.kolmogorovNumber_zero
  antitone T := T.antitone_kolmogorovNumber
  add_le S T n := S.kolmogorovNumber_add_le T n
  comp_le B T A n := B.kolmogorovNumber_comp_comp_le T A n
  eq_zero_of_rank_le := ContinuousLinearMap.kolmogorovNumber_eq_zero_of_rank_le
  normalize n := by
    apply ContinuousLinearMap.kolmogorovNumber_id_eq_one_of_isClosed
    · rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).rank_eq, rank_fin_fun]
      exact_mod_cast n.lt_succ_self
    · exact fun V _ ↦ V.isClosed_of_isModuleTopology

/-- Over a complete scalar field, Kolmogorov numbers are a strict s-number sequence.
The normed spaces themselves need not be complete. -/
theorem isStrictSNumberSequence_kolmogorov [CompleteSpace 𝕜] :
    IsStrictSNumberSequence (kolmogorov (𝕜 := 𝕜)) where
  toIsSNumberSequence := isSNumberSequence_kolmogorov
  normalize_of_lt_rank n hn := by simp [ContinuousLinearMap.kolmogorovNumber_id, hn]

end TauCeti.SNumbers
