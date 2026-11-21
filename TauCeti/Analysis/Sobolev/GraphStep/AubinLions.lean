/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Order.SuccPred.IntervalSucc
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# Compactness of the window restriction over a compactly embedded domain

Let `ι : D →L[ℝ] H` be a compact operator between real Banach spaces, typically the embedding of
the domain `D` of an unbounded operator on `H` into `H`. Over an open set `Ω ⊆ ℝ`, the
weak-derivative graph space `WeakDerivStep volume Ω p (ι.compLpL p (volume.restrict Ω))` consists
of the `u ∈ Lᵖ(Ω, D)` such that `ι ∘ u` has a weak derivative in `Lᵖ(Ω, H)`; it is the space
`Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` on which `∂ₛ ∘ ι + A` acts for a family of operators `A : D →L[ℝ] H`.

This file proves that restricting `ι ∘ u` to a bounded open interval `(a, b) ⊆ Ω` is a compact
operator from this graph space to `Lᵖ((a, b), H)`, for every `1 ≤ p ≤ ∞`
(`TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL_compLpL`). This is the case of the
Aubin–Lions lemma in which the derivative is measured in the same space `H` as the values: no
compactness in time is assumed, and it comes from the bound on the derivative. Neither space needs
to be finite dimensional. The Rellich theorem
`TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL` is different: it needs a
finite-dimensional target, but holds over any finite-dimensional domain, for any preceding
operator `base`, and for restriction to any compactly contained open subset. The result here
instead needs the domain to be `ℝ`, the restriction to be to an interval and
`base = ι.compLpL p _` with `ι` compact, but lets both `D` and `H` be infinite dimensional. It
supplies the compact error term in the semi-Fredholm estimate of the operator `∂ₛ + A(s)` on the
line, whose domain is this graph space for `Ω = ℝ`, `p = 2` and a compactly embedded common
domain `D`.

## Proof

The first ingredient is the Poincaré–Wirtinger inequality on an interval,
`TauCeti.HasWeakLineDerivOn.eLpNorm_sub_setAverage_le`: on an interval `J` of length `h`, the
deviation of `ι ∘ u` from its mean over `J` has `Lᵖ(J)` norm at most `h` times that of the weak
derivative. Cut `(a, b)` into `N` intervals of length `h = (b - a) / N`, and replace `ι ∘ u` on
each of them by its mean value. Since `ι` commutes with integration, this mean value is
`ι (⨍_J u)`, and `u ↦ ⨍_J u` is a bounded operator `Lᵖ(Ω, D) → D`. The resulting step function
therefore depends on `u` through finitely many operators of the form
`(indicator of a piece) ∘ ι ∘ (mean over the piece)`, each compact because `ι` is. The estimates on
the pieces glue without loss (`MeasureTheory.eLpNorm_sum_measure_le_mul_of_forall_le`), so the
restriction differs from this compact step approximation by an operator of norm at most `h`.
Letting `N → ∞`, it is a limit of compact operators in operator norm, hence compact.

## Main results

* `TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL_compLpL`: the restriction of `ι ∘ u` to
  a bounded open interval in `Ω` is a compact operator on the graph space.

## References

* J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non linéaires*, Dunod,
  1969, Chapitre 1, Théorème 5.1.
* J. Simon, *Compact sets in the space `Lᵖ(0, T; B)`*, Ann. Mat. Pura Appl. **146** (1987),
  65–96, Theorem 5 and Corollary 4.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

/-! ### Cutting an interval into `N` pieces -/

/-- The left endpoint `a + k (b - a) / N` of the `k`-th of the `N` intervals of equal length
cutting `(a, b]`. -/
private def node (a b : ℝ) (N k : ℕ) : ℝ := a + k * ((b - a) / N)

private theorem node_succ (N k : ℕ) : node a b N (k + 1) = node a b N k + (b - a) / N := by
  simp only [node]
  push_cast
  ring

private theorem node_zero (N : ℕ) : node a b N 0 = a := by
  simp [node]

private theorem node_self {N : ℕ} (hN : N ≠ 0) : node a b N N = b := by
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  simp only [node]
  field_simp
  ring

private theorem node_le_node (hab : a ≤ b) (N : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    node a b N j ≤ node a b N k := by
  have : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) N.cast_nonneg
  simp only [node]
  gcongr

/-- The `k`-th piece `(a + k h, a + (k + 1) h]`, with `h = (b - a) / N`. -/
private abbrev piece (a b : ℝ) (N k : ℕ) : Set ℝ := Ioc (node a b N k) (node a b N (k + 1))

/-- The interior `(a + k h, a + (k + 1) h)` of the `k`-th piece. -/
private abbrev pieceIoo (a b : ℝ) (N k : ℕ) : Set ℝ := Ioo (node a b N k) (node a b N (k + 1))

private theorem pieceIoo_subset_Ioo (hab : a ≤ b) {N : ℕ} {k : ℕ} (hk : k < N) :
    pieceIoo a b N k ⊆ Ioo a b := by
  refine Ioo_subset_Ioo ?_ ?_
  · exact (node_zero N).symm.trans_le (node_le_node hab N (Nat.zero_le k))
  · exact (node_le_node hab N (Nat.succ_le_of_lt hk)).trans_eq
      (node_self ((Nat.zero_le k).trans_lt hk).ne')

private theorem pairwise_disjoint_piece (hab : a ≤ b) (N : ℕ) :
    Pairwise (Function.onFun Disjoint fun k : Fin N ↦ piece a b N k) :=
  (Monotone.pairwise_disjoint_on_Ioc_succ fun _ _ h ↦ node_le_node hab N h).comp_of_injective
    Fin.val_injective

private theorem iUnion_piece (hab : a ≤ b) {N : ℕ} (hN : 0 < N) :
    ⋃ k : Fin N, piece a b N k = Ioc a b := by
  have h := (Monotone.biUnion_Ico_Ioc_map_succ (fun _ _ h ↦ node_le_node hab N h) 0 N)
  rw [node_zero, node_self hN.ne'] at h
  rw [← h]
  ext t
  simp [Fin.exists_iff]

/-- Lebesgue measure on `(a, b)` is the sum of its restrictions to the `N` pieces. -/
private theorem restrict_Ioo_eq_sum (hab : a < b) {N : ℕ} (hN : 0 < N) :
    volume.restrict (Ioo a b) = Measure.sum fun k : Fin N ↦ volume.restrict (piece a b N k) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← iUnion_piece hab.le hN,
    Measure.restrict_iUnion (pairwise_disjoint_piece hab.le N) fun _ ↦ measurableSet_Ioc]

/-! ### The step approximation -/

variable (ι : D →L[ℝ] H)

/-- The mean over the `k`-th piece, as a continuous linear map `Lᵖ(Ω, D) → D`. -/
private def pieceMean (a b : ℝ) (N k : ℕ) : Lp D p (volume.restrict (Omega : Set ℝ)) →L[ℝ] D :=
  (volume.real (pieceIoo a b N k))⁻¹ •
    Set.setIntegralLp (𝕜 := ℝ) (pieceIoo a b N k)
      ((Measure.restrict_apply_le _ _).trans_lt measure_Ioo_lt_top)

/-- The indicator of the `k`-th piece times a constant, as a continuous linear map
`H → Lᵖ((a, b), H)`. -/
private def pieceIndicator (a b : ℝ) (N k : ℕ) : H →L[ℝ] Lp H p (volume.restrict (Ioo a b)) :=
  indicatorConstLpL ℝ p (measurableSet_Ioc (a := node a b N k) (b := node a b N (k + 1)))
    ((Measure.restrict_apply_le _ _).trans_lt measure_Ioc_lt_top).ne

omit [CompleteSpace H] in
/-- On `(a, b)`, `pieceIndicator a b N k c` is the indicator of the `k`-th piece with value `c`. -/
private theorem pieceIndicator_coeFn (a b : ℝ) (N k : ℕ) (c : H) :
    ⇑(pieceIndicator (p := p) a b N k c) =ᵐ[volume.restrict (Ioo a b)]
      (piece a b N k).indicator fun _ ↦ c := by
  rw [pieceIndicator, indicatorConstLpL_apply]
  exact indicatorConstLp_coeFn

/-- `pieceMean a b N k u` is the average of `u` over the interior of the `k`-th piece. -/
private theorem pieceMean_apply {N k : ℕ} (hΩ : pieceIoo a b N k ⊆ Omega)
    (u : Lp D p (volume.restrict (Omega : Set ℝ))) :
    pieceMean a b N k u = ⨍ s in pieceIoo a b N k, u s := by
  rw [pieceMean, smul_apply, Set.setIntegralLp_apply, setAverage_eq,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 hΩ]

/-- The step approximation of `ι ∘ u` on `(a, b)` by its means over the `N` pieces. -/
private def stepApprox (a b : ℝ) (N : ℕ) :
    Lp D p (volume.restrict (Omega : Set ℝ)) →L[ℝ] Lp H p (volume.restrict (Ioo a b)) :=
  ∑ k : Fin N, (pieceIndicator a b N k).comp (ι.comp (pieceMean a b N k))

variable {ι}

omit [CompleteSpace H] in
/-- The step approximation is a compact operator, as a finite sum of operators factoring through
the compact operator `ι`. -/
private theorem isCompactOperator_stepApprox (hι : IsCompactOperator ι) (N : ℕ) :
    IsCompactOperator (stepApprox (Omega := Omega) (p := p) ι a b N) := by
  refine Finset.sum_induction _
    (fun T : Lp D p (volume.restrict (Omega : Set ℝ)) →L[ℝ] Lp H p (volume.restrict (Ioo a b)) ↦
      IsCompactOperator T) (fun S T hS hT ↦ ?_) ?_ fun k _ ↦ ?_
  · exact hS.add hT
  · exact isCompactOperator_zero
  · rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
    exact (hι.comp_clm _).clm_comp _

/-- On the interior of the `k`-th piece, the step approximation is the mean value of `ι ∘ u` over
that piece. -/
private theorem stepApprox_ae_eq (hΩ : Ioo a b ⊆ Omega) (hab : a < b) {N : ℕ} (k : Fin N)
    (u : Lp D p (volume.restrict (Omega : Set ℝ))) :
    stepApprox ι a b N u =ᵐ[volume.restrict (pieceIoo a b N k)]
      fun _ ↦ ⨍ s in pieceIoo a b N k, ι.compLpL p (volume.restrict (Omega : Set ℝ)) u s := by
  have hsub : pieceIoo a b N k ⊆ Ioo a b := pieceIoo_subset_Ioo hab.le k.isLt
  have happ : stepApprox ι a b N u =
      ∑ j : Fin N, pieceIndicator (p := p) a b N j (ι (pieceMean a b N j u)) := by
    simp only [stepApprox, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply]
  have hsum := Lp.coeFn_finsetSum Finset.univ
    fun j : Fin N ↦ pieceIndicator (p := p) a b N j (ι (pieceMean a b N j u))
  have hind := ae_all_iff.2 fun j : Fin N ↦
    pieceIndicator_coeFn (p := p) a b N j (ι (pieceMean (Omega := Omega) a b N j u))
  rw [happ]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsum,
    ae_restrict_of_ae_restrict_of_subset hsub hind, ae_restrict_mem measurableSet_Ioo]
    with t hs hi ht
  rw [hs, Finset.sum_apply, Finset.sum_eq_single k]
  · rw [hi k, indicator_of_mem (Ioo_subset_Ioc_self ht), pieceMean_apply (hsub.trans hΩ),
      setAverage_eq, setAverage_eq, map_smul, ← ι.integral_comp_comm]
    · refine congrArg _ (integral_congr_ae ?_)
      exact ae_restrict_of_ae_restrict_of_subset (hsub.trans hΩ) (ι.coeFn_compLpL u).symm
    · have hm := (Lp.memLp u).restrict (pieceIoo a b N k)
      rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 (hsub.trans hΩ)] at hm
      have : IsFiniteMeasure (volume.restrict (pieceIoo a b N k)) :=
        isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
      exact hm.integrable Fact.out
  · intro j _ hjk
    rw [hi j, indicator_of_notMem]
    exact fun htj ↦ Set.disjoint_left.1 (pairwise_disjoint_piece hab.le N hjk) htj
      (Ioo_subset_Ioc_self ht)
  · exact fun h ↦ absurd (Finset.mem_univ k) h

/-! ### The approximation estimate and compactness -/

local notation "base" => ι.compLpL p (volume.restrict (Omega : Set ℝ))

/-- The restriction of `ι ∘ u` to `(a, b)` differs from the step approximation by at most
`(b - a) / N` times the graph norm of `u`: on each piece this is the Poincaré–Wirtinger
inequality, and the estimates on the pieces glue without loss. -/
private theorem norm_restrictBaseL_sub_stepApprox_le
    (hΩ : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ Omega) (hab : a < b) {N : ℕ} (hN : 0 < N)
    (u : WeakDerivStep volume Omega p base) :
    ‖restrictBaseL base hΩ u - stepApprox ι a b N (prev base u)‖ ≤ (b - a) / N * ‖u‖ := by
  set F := restrictBaseL base hΩ u - stepApprox ι a b N (prev base u)
  set g : ℝ → H := fun t ↦ weakFDeriv base u t 1
  have hΩ' : Ioo a b ⊆ Omega := SetLike.coe_subset_coe.2 hΩ
  have hd : HasWeakLineDerivOn volume Omega (base (prev base u)) g 1 :=
    (hasWeakFDerivOn_base_prev base u).hasWeakLineDerivOn 1
  have hgΩ : MemLp g p (volume.restrict (Omega : Set ℝ)) :=
    (Lp.memLp (weakFDeriv base u)).continuousLinearMap_comp (ContinuousLinearMap.apply ℝ H 1)
  -- On each piece, the Poincaré–Wirtinger inequality.
  have hpiece : ∀ k : Fin N, eLpNorm F p (volume.restrict (piece a b N k)) ≤
      ENNReal.ofReal ((b - a) / N) * eLpNorm g p (volume.restrict (piece a b N k)) := fun k ↦ by
    have hsub : pieceIoo a b N k ⊆ Ioo a b := pieceIoo_subset_Ioo hab.le k.isLt
    have hP := HasWeakLineDerivOn.eLpNorm_sub_setAverage_le (F := H) Fact.out
      (hd.mono (Ω' := ⟨pieceIoo a b N k, isOpen_Ioo⟩) (SetLike.coe_subset_coe.mp (hsub.trans hΩ')))
      (hgΩ.mono_measure (Measure.restrict_mono (hsub.trans hΩ') le_rfl))
    have hlen : node a b N (k + 1) - node a b N k = (b - a) / N := by
      rw [node_succ, add_sub_cancel_left]
    rw [hlen] at hP
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine le_of_eq_of_le (eLpNorm_congr_ae ?_) hP
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
        (Lp.coeFn_sub (restrictBaseL base hΩ u) (stepApprox ι a b N (prev base u))),
      ae_restrict_of_ae_restrict_of_subset hsub (restrictBaseL_apply_ae base hΩ u),
      stepApprox_ae_eq (ι := ι) hΩ' hab k (prev base u)] with t h₁ h₂ h₃
    rw [h₁, Pi.sub_apply, h₂, h₃]
  -- Gluing the pieces.
  have hglue := eLpNorm_sum_measure_le_mul_of_forall_le
    (fun k : Fin N ↦ volume.restrict (piece a b N k)) hpiece
  rw [← restrict_Ioo_eq_sum hab hN] at hglue
  have hg : eLpNorm g p (volume.restrict (Ioo a b)) ≤
      eLpNorm g p (volume.restrict (Omega : Set ℝ)) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hΩ' le_rfl)
  have hgnorm : (eLpNorm g p (volume.restrict (Omega : Set ℝ))).toReal ≤ ‖u‖ := by
    have hcomp := (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (p := p)
      (μ := volume.restrict (Omega : Set ℝ)) (weakFDeriv base u)
    have hg_eq : eLpNorm g p (volume.restrict (Omega : Set ℝ)) =
        eLpNorm ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p _ (weakFDeriv base u)) p
          (volume.restrict (Omega : Set ℝ)) :=
      eLpNorm_congr_ae hcomp.symm
    rw [hg_eq, ← Lp.norm_def, ContinuousLinearMap.norm_apply_one_compLpL_apply]
    exact norm_weakFDeriv_le base u
  have hh : 0 ≤ (b - a) / N := div_nonneg (sub_pos.2 hab).le N.cast_nonneg
  rw [Lp.norm_def]
  calc (eLpNorm F p (volume.restrict (Ioo a b))).toReal
      ≤ (ENNReal.ofReal ((b - a) / N) * eLpNorm g p (volume.restrict (Omega : Set ℝ))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgΩ.eLpNorm_ne_top)
          (hglue.trans (by gcongr))
    _ = (b - a) / N * (eLpNorm g p (volume.restrict (Omega : Set ℝ))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hh]
    _ ≤ (b - a) / N * ‖u‖ := by gcongr

/-- **Compactness of the window restriction over a compactly embedded domain.** Let
`ι : D →L[ℝ] H` be a compact operator between real Banach spaces and `Ω ⊆ ℝ` open. On the graph
space `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` of the `u ∈ Lᵖ(Ω, D)` such that `ι ∘ u` has a weak derivative in
`Lᵖ(Ω, H)`, restricting `ι ∘ u` to a bounded open interval `(a, b) ⊆ Ω` is a compact operator to
`Lᵖ((a, b), H)`, for every `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_restrictBaseL_compLpL (hι : IsCompactOperator ι)
    (hΩ : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ Omega) :
    IsCompactOperator (restrictBaseL (ι.compLpL p (volume.restrict (Omega : Set ℝ))) hΩ) := by
  rcases le_or_gt b a with hba | hab
  · -- An empty interval: the target is `Lᵖ` of the zero measure.
    have h0 : restrictBaseL base hΩ = 0 := by
      ext u : 1
      have hfalse : ∀ᵐ _ ∂(volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)), False := by
        simp [Ioo_eq_empty_of_le hba]
      refine Lp.ext ?_
      filter_upwards [hfalse] with t ht
      exact ht.elim
    rw [h0]
    exact isCompactOperator_zero
  -- Otherwise the restriction is a limit of the compact step approximations.
  refine isClosed_setOfPred_isCompactOperator.closure_subset ?_
  refine (Metric.mem_closure_iff (α := WeakDerivStep volume Omega p base →L[ℝ]
    Lp H p (volume.restrict (Ioo a b)))).2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / ε)
  have hN0 : 0 < N := by
    exact_mod_cast (div_pos (sub_pos.2 hab) hε).trans hN
  refine ⟨(stepApprox ι a b N).comp (prevL base),
    (isCompactOperator_stepApprox hι N).comp_clm _, ?_⟩
  have hle : ‖restrictBaseL base hΩ - (stepApprox ι a b N).comp (prevL base)‖ ≤ (b - a) / N :=
    ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (sub_pos.2 hab).le N.cast_nonneg) fun u ↦ by
      simpa only [sub_apply, ContinuousLinearMap.comp_apply, prevL_apply] using
        norm_restrictBaseL_sub_stepApprox_le hΩ hab hN0 u
  have hlt : (b - a) / N < ε := by
    rw [div_lt_iff₀ (Nat.cast_pos.2 hN0)]
    rw [div_lt_iff₀ hε] at hN
    linarith
  exact (dist_eq_norm (E := WeakDerivStep volume Omega p base →L[ℝ]
    Lp H p (volume.restrict (Ioo a b))) _ _).trans_lt (hle.trans_lt hlt)

end TauCeti.WeakDerivStep
