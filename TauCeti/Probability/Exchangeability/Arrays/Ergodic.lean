/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.ZeroOne
public import TauCeti.MeasureTheory.Group.CountableAction
public import TauCeti.Algebra.GroupAction.FiniteSupportPerm
-- Non-public: cylinder approximation and its real-valued measure estimates are proof tools.
import TauCeti.MeasureTheory.Constructions.CylinderApproximation
import TauCeti.MeasureTheory.Measure.ZeroOne
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Finitary actions and ergodicity for exchangeable arrays

The finitely supported permutations of `ℕ` act diagonally on array path space: one permutation
relabels both array coordinates.  For a jointly exchangeable array law, this action is ergodic
exactly when the coordinate array is jointly dissociated.  By the corner-tail theorem in
`Arrays.ZeroOne`, these are also equivalent to triviality of the corner-tail σ-algebra.

Together with the corner-tail theorem this closes a representation-free triangle for jointly
exchangeable arrays: joint dissociation, triviality of the corner tail, and ergodicity of the
diagonal relabelling action are the same condition. It is stated on the law alone, for any
measurable value space. Where the Aldous--Hoover representation theorem applies (a standard Borel
value space), it is the condition singling out the ergodic form of that representation, in which
the array is coded without a global coordinate.

Independent finitary row and column relabelings give the corresponding action for separately
exchangeable laws. Finitary invariance already implies full joint or separate exchangeability,
because finite-dimensional marginals determine the array law.

## Main declarations

* `TauCeti.Probability.instSMulFinitaryPermArray` — the diagonal action of the finitary symmetric
  group `TauCeti.FinitaryPerm` (defined in `Algebra/GroupAction/FiniteSupportPerm.lean`) on array
  path space, one permutation relabelling both coordinates;
* `TauCeti.Probability.instSMulFinitaryPermPairArray` — independent finitary row and column
  relabelings, with `SeparatelyExchangeable.smulInvariantMeasure_pair` and its converse linking
  separate exchangeability to invariance of the law;
* `TauCeti.Probability.jointlyExchangeable_of_smulInvariantMeasure` — invariance under the
  diagonal finitary action gives joint exchangeability;
* `TauCeti.Probability.separatelyExchangeable_iff_map_pairReindex_finitary` — finite-support
  reindexings suffice to test separate exchangeability;
* `TauCeti.Probability.preimage_pairReindex_eq_self_of_measurableSet_arrayTail` — a corner-tail
  event is fixed by every pair of finitely supported axis permutations, not only by the diagonal
  ones;
* `TauCeti.Probability.jointlyDissociated_iff_ergodicSMul` — joint dissociation is ergodicity of
  that action for a jointly exchangeable array law;
* `TauCeti.Probability.jointlyDissociated_iff_ergodicSMul_pair` — joint dissociation is
  ergodicity of the independent row-and-column action for a separately exchangeable array law.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

The block-swap argument adapts `Graphon/RelErgodicLinks.lean` in `cameronfreer/graphon`
(Apache 2.0) at commit `175911f9d2e053f2a33d966658dfce0e4ae2811d`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal symmDiff

namespace TauCeti

namespace Probability

variable {α : Type*}

/-! ## The diagonal finitary-permutation action -/

/-- Finitely supported vertex permutations act diagonally on array path space, by the inverse
permutation so that reindexing is a left action. -/
instance instSMulFinitaryPermArray : SMul FinitaryPerm (ℕ × ℕ → α) :=
  ⟨fun g x => pairReindex (FinitaryPerm.toPerm g)⁻¹ (FinitaryPerm.toPerm g)⁻¹ x⟩

/-- The diagonal array action written as an explicit pair reindexing. -/
theorem finitaryPerm_smul_array_def (g : FinitaryPerm) (x : ℕ × ℕ → α) :
    g • x = pairReindex (FinitaryPerm.toPerm g)⁻¹ (FinitaryPerm.toPerm g)⁻¹ x :=
  rfl

/-- The diagonal array action relabels both coordinates by the inverse permutation. -/
@[simp]
theorem finitaryPerm_smul_array_apply (g : FinitaryPerm) (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    (g • x) p = x ((FinitaryPerm.toPerm g)⁻¹ p.1, (FinitaryPerm.toPerm g)⁻¹ p.2) :=
  by rw [finitaryPerm_smul_array_def, pairReindex_apply]

instance instMulActionFinitaryPermArray : MulAction FinitaryPerm (ℕ × ℕ → α) where
  one_smul x := by ext p; simp
  mul_smul g h x := by ext p; simp [mul_inv_rev]

/-- Independent finitely supported permutations act on the two axes of an array. The inverse
permutations make reindexing a left action. -/
instance instSMulFinitaryPermPairArray :
    SMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) :=
  ⟨fun g x => pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ x⟩

/-- The separate action is coordinate reindexing on each axis. -/
@[simp]
theorem finitaryPermPair_smul_array_apply (g : FinitaryPerm × FinitaryPerm)
    (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    (g • x) p = x ((FinitaryPerm.toPerm g.1)⁻¹ p.1,
      (FinitaryPerm.toPerm g.2)⁻¹ p.2) := by
  -- Expose the reindexing map behind the scalar action.
  change (pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ x) p = _
  rw [pairReindex_apply]

/-- Independent row and column permutations compose as a left action on arrays. -/
instance instMulActionFinitaryPermPairArray :
    MulAction (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) where
  one_smul x := by ext p; simp
  mul_smul g h x := by ext p; simp [mul_inv_rev]

variable [MeasurableSpace α]

instance instMeasurableConstSMulFinitaryPermArray :
    MeasurableConstSMul FinitaryPerm (ℕ × ℕ → α) :=
  ⟨fun _ => measurable_pairReindex (α := α) _ _⟩

/-- A jointly exchangeable array law is invariant under diagonal finitary relabeling. -/
theorem JointlyExchangeable.smulInvariantMeasure {ρ : Measure (ℕ × ℕ → α)}
    (hρ : JointlyExchangeable ρ fun p x => x p) :
    SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ := by
  constructor
  intro g s hs
  simp only [finitaryPerm_smul_array_def]
  rw [← Measure.map_apply (measurable_pairReindex _ _) hs]
  have hmap := congrArg (fun m : Measure (ℕ × ℕ → α) => m s)
    (jointlyExchangeable_iff.mp hρ (FinitaryPerm.toPerm g)⁻¹)
  rw [← pairReindex_def, Measure.map_id'] at hmap
  exact hmap

/-! ## Corner-tail events are invariant -/

private theorem preimage_pairReindex_eq_of_measurable_arrayTailFamily
    {s : Set (ℕ × ℕ → α)} {σ τ : Equiv.Perm ℕ} {N : ℕ}
    (hs : MeasurableSet[arrayTailFamily (fun p (x : ℕ × ℕ → α) => x p) N] s)
    (hσ : ∀ k, N ≤ k → σ k = k) (hτ : ∀ k, N ≤ k → τ k = k) :
    pairReindex (α := α) σ τ ⁻¹' s = s := by
  rw [arrayTailFamily_eq_blockSigma, blockSigma_def] at hs
  rw [MeasurableSpace.measurableSet_iSup] at hs
  induction hs with
  | basic u hu =>
      rcases hu with ⟨p, hu⟩
      rw [MeasurableSpace.measurableSet_iSup] at hu
      induction hu with
      | basic u hu =>
          rcases hu with ⟨hp, v, _, rfl⟩
          ext x
          simp only [Set.mem_preimage, pairReindex_apply]
          rw [hσ p.1 hp.1, hτ p.2 hp.2]
      | empty => simp
      | compl t _ hpre => rw [Set.preimage_compl, hpre]
      | iUnion f _ hf =>
          rw [Set.preimage_iUnion]
          simp [hf]
  | empty => simp
  | compl t _ hpre => rw [Set.preimage_compl, hpre]
  | iUnion f _ hf =>
      rw [Set.preimage_iUnion]
      simp [hf]

/-- **Every corner-tail event is fixed by a finitely supported separate relabelling**: permuting
the two axes independently by finitely supported permutations fixes every sufficiently far corner,
which is all that a corner-tail event reads. -/
theorem preimage_pairReindex_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    {σ τ : Equiv.Perm ℕ} (hσ : (MulAction.fixedBy ℕ σ)ᶜ.Finite)
    (hτ : (MulAction.fixedBy ℕ τ)ᶜ.Finite) : pairReindex (α := α) σ τ ⁻¹' s = s := by
  obtain ⟨M, hM⟩ := finite_compl_fixedBy_eventually_eq_self hσ
  obtain ⟨N, hN⟩ := finite_compl_fixedBy_eventually_eq_self hτ
  exact preimage_pairReindex_eq_of_measurable_arrayTailFamily
    ((measurableSet_arrayTail_iff.mp hs) (max M N))
    (fun k hk => hM k ((le_max_left M N).trans hk)) fun k hk => hN k ((le_max_right M N).trans hk)

/-- **Every corner-tail event is fixed by the diagonal action**: a finitely supported relabelling
of both coordinates changes only finitely many entries, and a corner-tail event does not read
them. -/
theorem preimage_finitaryPerm_smul_array_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    (g : FinitaryPerm) : (fun x : ℕ × ℕ → α => g • x) ⁻¹' s = s := by
  have hfin : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g⁻¹
  simp only [finitaryPerm_smul_array_def]
  exact preimage_pairReindex_eq_self_of_measurableSet_arrayTail hs hfin hfin

/-! ## The block-swap zero-one argument -/

private theorem measurableSet_cylinder_blockSigma {F : Finset (ℕ × ℕ)} {I : Finset ℕ}
    (hFI : ∀ p ∈ F, p.1 ∈ I ∧ p.2 ∈ I) {S : Set (∀ _p : F, α)} (hS : MeasurableSet S) :
    MeasurableSet[blockSigma (fun p (x : ℕ × ℕ → α) => x p)
      ((I : Set ℕ) ×ˢ (I : Set ℕ))] (cylinder F S) := by
  let _ : MeasurableSpace (ℕ × ℕ → α) :=
    blockSigma (fun p (x : ℕ × ℕ → α) => x p) ((I : Set ℕ) ×ˢ (I : Set ℕ))
  refine (Measurable.of_eval fun p => ?_) hS
  have hp : p.1 ∈ (I : Set ℕ) ×ˢ (I : Set ℕ) := hFI p.1 p.2
  simpa using (measurable_blockSigma_of_mem
    (Z := fun p (x : ℕ × ℕ → α) => x p) hp)

private theorem measure_eq_zero_or_one_of_jointlyDissociated
    {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    [SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ]
    (hdiss : JointlyDissociated ρ fun p x => x p)
    {s : Set (ℕ × ℕ → α)} (hs : MeasurableSet s)
    (hinv : ∀ g : FinitaryPerm, (fun x : ℕ × ℕ → α => g • x) ⁻¹' s = s) :
    ρ s = 0 ∨ ρ s = 1 := by
  classical
  -- Strategy: for each `ε`, produce a cylinder `t` within `ε` of `s` and its block-swapped copy
  -- `t'`, also within `ε` of `s` by invariance, whose intersection factors by dissociation; the
  -- shared zero-one criterion then forces `ρ s ∈ {0, 1}`.
  refine TauCeti.MeasureTheory.measure_eq_zero_or_one_of_forall_exists_symmDiff_lt_inter_eq_mul
    ?_
  intro ε hε
  -- Step 1: the approximating cylinder `t` on a finite square `I × I` inside `[0, N)²`.
  obtain ⟨F, S, hS, hFS⟩ := TauCeti.MeasureTheory.exists_cylinder_measure_symmDiff_lt (ρ := ρ) hs
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  let I : Finset ℕ := F.image Prod.fst ∪ F.image Prod.snd
  have hFI : ∀ p ∈ F, p.1 ∈ I ∧ p.2 ∈ I := by
    intro p hp
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  obtain ⟨N, hIN⟩ := Finset.exists_nat_subset_range I
  -- Step 2: the block swap moves `I` onto a disjoint copy `J`; `t'` is `t` read through it.
  let π : Equiv.Perm ℕ := N.blockSwap
  let J : Finset ℕ := I.map (Equiv.toEmbedding π)
  set t : Set (ℕ × ℕ → α) := cylinder F S with ht
  set t' : Set (ℕ × ℕ → α) := pairReindex π π ⁻¹' t with ht'
  have ht_meas : MeasurableSet t := by
    rw [ht]
    exact MeasurableSet.cylinder (α := fun _ : ℕ × ℕ => α) F hS
  have ht_block : MeasurableSet[blockSigma (fun p (x : ℕ × ℕ → α) => x p)
      ((I : Set ℕ) ×ˢ (I : Set ℕ))] t := by
    rw [ht]
    exact measurableSet_cylinder_blockSigma hFI hS
  have ht'_block : MeasurableSet[blockSigma (fun p (x : ℕ × ℕ → α) => x p)
      ((J : Set ℕ) ×ˢ (J : Set ℕ))] t' := by
    let _ : MeasurableSpace (ℕ × ℕ → α) :=
      blockSigma (fun p (x : ℕ × ℕ → α) => x p) ((J : Set ℕ) ×ˢ (J : Set ℕ))
    rw [ht', ht]
    -- a cylinder is the preimage of `S` under restriction to `F`; `cylinder` is a definition with
    -- no propositional unfolding lemma, so the preimage form is by `rfl`
    have hcyl : pairReindex π π ⁻¹' cylinder F S
        = (fun x : ℕ × ℕ → α => fun p : F => pairReindex π π x p.1) ⁻¹' S := rfl
    rw [hcyl]
    have hread : Measurable (fun x : ℕ × ℕ → α => fun p : F => pairReindex π π x p.1) :=
      Measurable.of_eval fun p => by
        have hp1 : π p.1.1 ∈ J := Finset.mem_map_of_mem _ (hFI p.1 p.2).1
        have hp2 : π p.1.2 ∈ J := Finset.mem_map_of_mem _ (hFI p.1 p.2).2
        have hpJ : (π p.1.1, π p.1.2) ∈ (J : Set ℕ) ×ˢ (J : Set ℕ) := ⟨hp1, hp2⟩
        simpa only [pairReindex_apply] using (measurable_blockSigma_of_mem
          (Z := fun p (x : ℕ × ℕ → α) => x p) hpJ)
    exact hread hS
  -- Step 3: `s` is invariant under the swap, so `t'` is as close to `s` as `t` is.
  have hIJ : Disjoint I J := Nat.disjoint_map_blockSwap hIN
  have hIJset : Disjoint (I : Set ℕ) (J : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hiI hiJ
    exact Finset.disjoint_left.mp hIJ hiI hiJ
  have hfactor : ρ (t ∩ t') = ρ t * ρ t' :=
    (ProbabilityTheory.Indep_iff
      (blockSigma (fun p (x : ℕ × ℕ → α) => x p) ((I : Set ℕ) ×ˢ (I : Set ℕ)))
      (blockSigma (fun p (x : ℕ × ℕ → α) => x p) ((J : Set ℕ) ×ˢ (J : Set ℕ))) ρ).mp
        (hdiss.indep_blockSigma_prod_self hIJset) t t' ht_block ht'_block
  have hπinv : (MulAction.fixedBy ℕ π⁻¹)ᶜ.Finite := by
    simpa only [π, MulAction.fixedBy_inv ℕ] using Nat.finite_compl_fixedBy_blockSwap N
  have hs_inv : pairReindex π π ⁻¹' s = s := by
    have hg := hinv (FinitaryPerm.ofPerm π⁻¹ hπinv)
    simpa only [finitaryPerm_smul_array_def, FinitaryPerm.toPerm_ofPerm, inv_inv] using hg
  -- the swap acts by `pairReindex π π`, so invariance of `ρ` under the action is invariance
  -- under this reindexing
  have hmap : ρ.map (pairReindex π π) = ρ := by
    ext u hu
    rw [Measure.map_apply (measurable_pairReindex _ _) hu]
    have h := SMulInvariantMeasure.measure_preimage_smul (FinitaryPerm.ofPerm π⁻¹ hπinv) hu
      (μ := ρ)
    simpa only [finitaryPerm_smul_array_def, FinitaryPerm.toPerm_ofPerm, inv_inv] using h
  have ht'_symm : ρ (symmDiff t' s) = ρ (symmDiff t s) := by
    have hpre : symmDiff t' s = pairReindex π π ⁻¹' symmDiff t s := by
      rw [Set.preimage_symmDiff, hs_inv, ht']
    rw [hpre, ← Measure.map_apply (measurable_pairReindex π π)
      (ht_meas.symmDiff hs), hmap]
  have h1 : ρ.real (symmDiff t s) < ε := by
    rw [ht]
    exact ENNReal.toReal_lt_of_lt_ofReal hFS
  have h2 : ρ.real (symmDiff t' s) < ε :=
    ENNReal.toReal_lt_of_lt_ofReal (ht'_symm ▸ (ht ▸ hFS))
  -- Step 4: `t` and `t'` read disjoint blocks, so dissociation factors their intersection.
  have hfactor_real : ρ.real (t ∩ t') = ρ.real t * ρ.real t' := by
    rw [measureReal_def, measureReal_def, measureReal_def, hfactor, ENNReal.toReal_mul]
  exact ⟨t, t', h1, h2, hfactor_real⟩

/-- **Joint dissociation makes the diagonal finitary-permutation action ergodic**, for a law
invariant under that action; joint exchangeability supplies the invariance
(`JointlyExchangeable.smulInvariantMeasure`). -/
theorem ergodicSMul_of_jointlyDissociated {ρ : Measure (ℕ × ℕ → α)} [IsZeroOrProbabilityMeasure ρ]
    [SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ]
    (hdiss : JointlyDissociated ρ fun p x => x p) :
    ErgodicSMul FinitaryPerm (ℕ × ℕ → α) ρ := by
  refine TauCeti.MeasureTheory.ergodicSMul_of_forall_smul_invariant fun s hs hinv => ?_
  rcases eq_zero_or_isProbabilityMeasure ρ with rfl | _
  · exact eventuallyEmptyOrUniv_iff'.mpr (Or.inl (by rw [ae_zero]; exact Filter.eventually_bot))
  refine eventuallyEmptyOrUniv_iff'.mpr ?_
  rcases measure_eq_zero_or_one_of_jointlyDissociated hdiss hs hinv with h | h
  · exact Or.inl (ae_eq_empty.mpr h)
  · exact Or.inr (ae_eq_univ.mpr ((prob_compl_eq_zero_iff hs).mpr h))

/-- Ergodicity of the diagonal finitary-permutation action makes a jointly exchangeable array law
jointly dissociated. -/
theorem jointlyDissociated_of_ergodicSMul {ρ : Measure (ℕ × ℕ → α)} [IsZeroOrProbabilityMeasure ρ]
    [ErgodicSMul FinitaryPerm (ℕ × ℕ → α) ρ]
    (hexch : JointlyExchangeable ρ fun p x => x p) :
    JointlyDissociated ρ fun p x => x p := by
  apply (jointlyDissociated_iff_forall_arrayTail_measure_eq_zero_or_one
    (X := fun p (x : ℕ × ℕ → α) => x p) (fun p => measurable_pi_apply p) hexch).mpr
  intro s hs
  rcases eq_zero_or_isProbabilityMeasure ρ with rfl | _
  · exact Or.inl rfl
  have hconst : EventuallyEmptyOrUniv s (ae ρ) :=
    MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq FinitaryPerm
      ((arrayTail_le_ambient (X := fun p (x : ℕ × ℕ → α) => x p) 0
        fun p _ _ => measurable_pi_apply p) s hs).nullMeasurableSet
      fun g => EventuallyEq.of_eq
        (preimage_finitaryPerm_smul_array_eq_self_of_measurableSet_arrayTail hs g)
  rcases eventuallyEmptyOrUniv_iff'.mp hconst with h | h
  · exact Or.inl (by simpa using measure_congr h)
  · exact Or.inr (by simpa using measure_congr h)

/-- **Joint dissociation is ergodicity** for a jointly exchangeable array law.  The acting group
simultaneously applies one finitely supported permutation to both coordinates. -/
theorem jointlyDissociated_iff_ergodicSMul {ρ : Measure (ℕ × ℕ → α)} [IsZeroOrProbabilityMeasure ρ]
    (hexch : JointlyExchangeable ρ fun p x => x p) :
    JointlyDissociated ρ (fun p x => x p) ↔ ErgodicSMul FinitaryPerm (ℕ × ℕ → α) ρ :=
  ⟨fun h => haveI := hexch.smulInvariantMeasure; ergodicSMul_of_jointlyDissociated h,
    fun _ => jointlyDissociated_of_ergodicSMul hexch⟩

/-! ## Finitary tests and the separate action -/

private theorem map_pairReindex_eq_self_of_forall_finset
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ] {σ τ : Equiv.Perm ℕ}
    (h : ∀ F : Finset (ℕ × ℕ), ∃ σ' τ' : Equiv.Perm ℕ,
      ρ.map (pairReindex σ' τ') = ρ ∧
        ∀ p ∈ F, σ' p.1 = σ p.1 ∧ τ' p.2 = τ p.2) :
    (ρ.map fun x : ℕ × ℕ → α => fun p => x (σ p.1, τ p.2)) =
      ρ.map fun x : ℕ × ℕ → α => fun p => x p := by
  have hmeas : ∀ π π' : Equiv.Perm ℕ,
      AEMeasurable (fun x : ℕ × ℕ → α => fun p : ℕ × ℕ => x (π p.1, π' p.2)) ρ :=
    fun π π' => by
      rw [← pairReindex_def]
      exact (measurable_pairReindex π π').aemeasurable
  rw [ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq (hmeas σ τ)
    (Measurable.of_eval fun p => measurable_pi_apply p).aemeasurable]
  intro F
  obtain ⟨σ', τ', hinv, hagree⟩ := h F
  have hinv' : (ρ.map fun x : ℕ × ℕ → α => fun p => x (σ' p.1, τ' p.2)) =
      ρ.map fun x : ℕ × ℕ → α => fun p => x p := by
    simpa only [← pairReindex_def, Measure.map_id'] using hinv
  have hres := (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq (hmeas σ' τ')
    (Measurable.of_eval fun p => measurable_pi_apply p).aemeasurable).mp hinv' F
  have heq : (fun x : ℕ × ℕ → α => F.restrict fun p => x (σ' p.1, τ' p.2)) =
      fun x : ℕ × ℕ → α => F.restrict fun p => x (σ p.1, τ p.2) := by
    funext x p
    obtain ⟨q, hq⟩ := p
    simp only [Finset.restrict_def, (hagree q hq).1, (hagree q hq).2]
  rwa [heq] at hres

/-- A finite law on `ℕ × ℕ → α` invariant under the finitary diagonal action is jointly
exchangeable: invariant under the diagonal relabelling by every permutation of `ℕ`. -/
theorem jointlyExchangeable_of_smulInvariantMeasure {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ] [SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ] :
    JointlyExchangeable ρ fun p x => x p := by
  rw [jointlyExchangeable_iff]
  intro σ
  apply map_pairReindex_eq_self_of_forall_finset
  intro F
  obtain ⟨π, hπfin, hπ⟩ := Equiv.Perm.exists_finite_compl_fixedBy_apply_eq_on_finset σ
    (F.image Prod.fst ∪ F.image Prod.snd)
  refine ⟨π, π, ?_, ?_⟩
  · -- the law is invariant under `π`, read through the action
    have hπ' : (MulAction.fixedBy ℕ π⁻¹)ᶜ.Finite := by
      simpa only [MulAction.fixedBy_inv ℕ] using hπfin
    have h := SMulInvariantMeasure.measure_preimage_smul (μ := ρ) (FinitaryPerm.ofPerm π⁻¹ hπ')
    ext s hs
    rw [Measure.map_apply (measurable_pairReindex _ _) hs]
    have := h hs
    simpa only [finitaryPerm_smul_array_def, FinitaryPerm.toPerm_ofPerm, inv_inv] using this
  · intro p hp
    exact ⟨hπ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)),
      hπ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))⟩

/-- **Finitely supported permutations already test separate exchangeability.** A finite law on
array path space invariant under every pair of finitely supported axis relabellings is invariant
under every pair of axis relabellings: the law is determined by its finite-dimensional marginals,
and on finitely many indices any permutation agrees with a finitely supported one.

This is the separate counterpart of `jointlyExchangeable_of_smulInvariantMeasure`; it is stated
through the two permutations rather than through a group action because the two axes are
relabelled independently. -/
theorem separatelyExchangeable_of_map_pairReindex_finitary
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]
    (h : ∀ σ τ : Equiv.Perm ℕ, (MulAction.fixedBy ℕ σ)ᶜ.Finite → (MulAction.fixedBy ℕ τ)ᶜ.Finite →
      ρ.map (pairReindex σ τ) = ρ) :
    SeparatelyExchangeable ρ fun p x => x p := by
  rw [separatelyExchangeable_iff]
  intro σ τ
  apply map_pairReindex_eq_self_of_forall_finset
  intro F
  -- finitely supported relabellings agreeing with `σ` and `τ` on the indices that `F` reads
  obtain ⟨σ', hσ'fin, hσ'⟩ :=
    Equiv.Perm.exists_finite_compl_fixedBy_apply_eq_on_finset σ (F.image Prod.fst)
  obtain ⟨τ', hτ'fin, hτ'⟩ :=
    Equiv.Perm.exists_finite_compl_fixedBy_apply_eq_on_finset τ (F.image Prod.snd)
  exact ⟨σ', τ', h σ' τ' hσ'fin hτ'fin, fun p hp =>
    ⟨hσ' _ (Finset.mem_image_of_mem _ hp), hτ' _ (Finset.mem_image_of_mem _ hp)⟩⟩

/-- A finite law on array path space is separately exchangeable if and only if it is invariant
under every pair of finitely supported axis relabellings. -/
theorem separatelyExchangeable_iff_map_pairReindex_finitary
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ] :
    SeparatelyExchangeable ρ (fun p x => x p) ↔
      ∀ σ τ : Equiv.Perm ℕ, (MulAction.fixedBy ℕ σ)ᶜ.Finite → (MulAction.fixedBy ℕ τ)ᶜ.Finite →
        ρ.map (pairReindex σ τ) = ρ :=
  ⟨fun h σ τ _ _ => (h.measurePreserving_pairReindex σ τ).map_eq,
    separatelyExchangeable_of_map_pairReindex_finitary⟩

/-- A finite law is jointly exchangeable if and only if it is invariant under the finitary
diagonal action. -/
theorem jointlyExchangeable_iff_smulInvariantMeasure {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ] :
    JointlyExchangeable ρ (fun p x => x p) ↔ SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α) ρ :=
  ⟨JointlyExchangeable.smulInvariantMeasure, fun _ => jointlyExchangeable_of_smulInvariantMeasure⟩

/-- Each independent finitary relabeling is measurable. -/
instance instMeasurableConstSMulFinitaryPermPairArray :
    MeasurableConstSMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) :=
  ⟨fun _ => measurable_pairReindex _ _⟩

/-- A separately exchangeable array law is invariant under the separate finitary action. -/
theorem SeparatelyExchangeable.smulInvariantMeasure_pair {ρ : Measure (ℕ × ℕ → α)}
    (hρ : SeparatelyExchangeable ρ fun p x => x p) :
    SMulInvariantMeasure (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ := by
  constructor
  intro g s hs
  -- Unfold only the action, leaving the measurable reindexing map visible to `map_apply`.
  change ρ (pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ ⁻¹' s) = ρ s
  rw [← Measure.map_apply (measurable_pairReindex _ _) hs]
  have hmap := congrArg (fun m : Measure (ℕ × ℕ → α) => m s)
    (separatelyExchangeable_iff.mp hρ (FinitaryPerm.toPerm g.1)⁻¹
      (FinitaryPerm.toPerm g.2)⁻¹)
  rw [← pairReindex_def, Measure.map_id'] at hmap
  exact hmap

/-- Finitary invariance under independent row and column relabelings implies separate
exchangeability, by finite-dimensional determinacy of the array law. -/
theorem separatelyExchangeable_of_smulInvariantMeasure_pair {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ]
    [SMulInvariantMeasure (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ] :
    SeparatelyExchangeable ρ fun p x => x p := by
  apply separatelyExchangeable_of_map_pairReindex_finitary
  intro σ τ hσ hτ
  let g : FinitaryPerm × FinitaryPerm :=
    (FinitaryPerm.ofPerm σ⁻¹ (by simpa only [MulAction.fixedBy_inv ℕ] using hσ),
      FinitaryPerm.ofPerm τ⁻¹ (by simpa only [MulAction.fixedBy_inv ℕ] using hτ))
  ext s hs
  rw [Measure.map_apply (measurable_pairReindex _ _) hs]
  have h := SMulInvariantMeasure.measure_preimage_smul (μ := ρ) g hs
  have hact : (fun x : ℕ × ℕ → α => g • x) = pairReindex σ τ := by
    funext x p
    simp [finitaryPermPair_smul_array_apply, pairReindex_apply, g]
  rwa [hact] at h

/-- A corner-tail event is fixed by every separate finitary relabeling. -/
theorem preimage_finitaryPermPair_smul_array_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    (g : FinitaryPerm × FinitaryPerm) :
    (fun x : ℕ × ℕ → α => g • x) ⁻¹' s = s := by
  have h₁ : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g.1)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g.1⁻¹
  have h₂ : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g.2)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g.2⁻¹
  -- The action is exactly this two-axis reindexing.
  change pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ ⁻¹' s = s
  exact preimage_pairReindex_eq_self_of_measurableSet_arrayTail hs h₁ h₂

/-- Joint dissociation is ergodicity for the independent row-and-column action on a separately
exchangeable array law. -/
theorem jointlyDissociated_iff_ergodicSMul_pair {ρ : Measure (ℕ × ℕ → α)}
    [IsZeroOrProbabilityMeasure ρ] (hexch : SeparatelyExchangeable ρ fun p x => x p) :
    JointlyDissociated ρ (fun p x => x p) ↔
      ErgodicSMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ := by
  constructor
  · intro hdiss
    let := hexch.smulInvariantMeasure_pair
    let := hexch.jointlyExchangeable.smulInvariantMeasure
    let : ErgodicSMul FinitaryPerm (ℕ × ℕ → α) ρ :=
      ergodicSMul_of_jointlyDissociated hdiss
    apply TauCeti.MeasureTheory.ergodicSMul_of_forall_smul_invariant
    intro s hs hinv
    apply MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq FinitaryPerm hs.nullMeasurableSet
    intro g
    have hact : (fun x : ℕ × ℕ → α => (g, g) • x) = fun x => g • x := by
      funext x p
      simp [finitaryPermPair_smul_array_apply, finitaryPerm_smul_array_apply]
    exact EventuallyEq.of_eq (by rw [← hact]; exact hinv (g, g))
  · intro herg
    let := hexch.smulInvariantMeasure_pair
    let : ErgodicSMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ := herg
    apply (jointlyDissociated_iff_forall_arrayTail_measure_eq_zero_or_one
      (X := fun p (x : ℕ × ℕ → α) => x p)
      (fun p => measurable_pi_apply p) hexch.jointlyExchangeable).mpr
    intro s hs
    rcases eq_zero_or_isProbabilityMeasure ρ with rfl | _
    · exact Or.inl rfl
    have hconst : EventuallyEmptyOrUniv s (ae ρ) :=
      MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq
        (FinitaryPerm × FinitaryPerm)
        ((arrayTail_le_ambient (X := fun p (x : ℕ × ℕ → α) => x p) 0
          fun p _ _ => measurable_pi_apply p) s hs).nullMeasurableSet
        fun g => EventuallyEq.of_eq
          (preimage_finitaryPermPair_smul_array_eq_self_of_measurableSet_arrayTail hs g)
    rcases eventuallyEmptyOrUniv_iff'.mp hconst with h | h
    · exact Or.inl (by simpa using measure_congr h)
    · exact Or.inr (by simpa using measure_congr h)

end Probability

end TauCeti

end

end
