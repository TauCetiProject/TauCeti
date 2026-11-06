/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.Dual.Helly
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
import TauCeti.Topology.Algebra.Module.WeakSpace
import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Triangular sequences and nonreflexivity

A nonreflexive Banach space admits sequences `x n` and `f n` in the closed unit balls
of the space and its continuous dual, and a real number `θ > 0`, such that
`f i (x j) = θ` for `i ≤ j` and `f i (x j) = 0` for `j < i`.
These exact triangular arrays provide a countable obstruction to weak compactness,
as used in the proof of James's compactness theorem. They do not by themselves
assert the existence of a functional which fails to attain its norm.

We prove the converse too: such a sequence has no weakly convergent subsequence,
and consequently the space is not reflexive. This obstruction needs no completeness;
completeness is required only to construct the array from nonreflexivity.
The closed span of the constructed vectors is separable and nonreflexive, so
nonreflexivity of a Banach space can always be detected on a closed separable subspace.

The construction uses Hahn–Banach separation from the closed canonical bidual range,
then Helly's finite interpolation lemma, first in the dual and then in the space.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.9
  (triangular sequences in the proof of James's theorem).
-/

public section

open Filter Function Metric NormedSpace Set TopologicalSpace Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A nonreflexive Banach space admits an exact triangular array of evaluations,
with vectors and functionals in their closed unit balls and a fixed positive entry. -/
theorem exists_seq_dual_triangular_of_not_surjective_inclusionInDoubleDual [CompleteSpace E]
    (hE : ¬ Surjective (inclusionInDoubleDual 𝕜 E)) :
    ∃ (θ : ℝ) (x : ℕ → E) (f : ℕ → StrongDual 𝕜 E), 0 < θ ∧
      (∀ n, ‖x n‖ ≤ 1) ∧ (∀ n, ‖f n‖ ≤ 1) ∧
      (∀ i j, i ≤ j → f i (x j) = (θ : 𝕜)) ∧
      (∀ i j, j < i → f i (x j) = 0) := by
  classical
  -- Completeness makes the canonical range closed, so Hahn–Banach detects
  -- a bidual vector at a strictly positive distance from it.
  obtain ⟨φ, hφ⟩ := not_forall.mp hE
  let J := inclusionInDoubleDual 𝕜 E
  let R := LinearMap.range J.toLinearMap
  have hR : IsClosed (R : Set (StrongDual 𝕜 (StrongDual 𝕜 E))) :=
    (inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.isComplete_range.isClosed
  have hd : 0 < infDist φ (R : Set (StrongDual 𝕜 (StrongDual 𝕜 E))) :=
    (hR.notMem_iff_infDist_pos R.nonempty).1 hφ
  obtain ⟨Φ, hΦR, hΦnorm, hΦφ⟩ := Submodule.exists_dual_eq_infDist (𝕜 := 𝕜) R φ
  let d := infDist φ (R : Set (StrongDual 𝕜 (StrongDual 𝕜 E))) / 2
  let C := ‖φ‖ + 1
  have hC : 0 < C := by positivity
  have hd' : 0 < d := by positivity
  -- One interpolation step works for arbitrary finite histories: no inductive
  -- compatibility assumptions need to be carried by the recursion.
  have step (n : ℕ) (p : Fin n → E × StrongDual 𝕜 E) :
      ∃ q : E × StrongDual 𝕜 E,
        ‖q.1‖ < C ∧ ‖q.2‖ ≤ 1 ∧ φ q.2 = (d : 𝕜) ∧
        q.2 q.1 = (d : 𝕜) ∧
        (∀ i, q.2 (p i).1 = 0) ∧ (∀ i, (p i).2 q.1 = φ (p i).2) := by
    let tests : Option (Fin n) → StrongDual 𝕜 (StrongDual 𝕜 E) :=
      fun i ↦ i.elim φ (fun j ↦ J (p j).1)
    obtain ⟨g, hg, htests⟩ := Φ.exists_norm_lt_and_forall_apply_eq tests (by norm_num : (0 : ℝ) < 1)
    let f : StrongDual 𝕜 E := (2 : 𝕜)⁻¹ • g
    have hfn : ‖f‖ ≤ 1 := by
      have hgn : ‖g‖ < 2 := hg.trans_le (by linarith)
      simp only [f, norm_smul, norm_inv, RCLike.norm_ofNat]
      linarith
    have hfg : φ f = (d : 𝕜) := by
      have ht := htests none
      simp only [tests, Option.elim_none] at ht
      simp only [f, map_smul, smul_eq_mul, ht, hΦφ, d]
      push_cast
      ring
    have hfx (i : Fin n) : f (p i).1 = 0 := by
      have ht := htests (some i)
      simp only [tests, Option.elim_some] at ht
      have hz : Φ (J (p i).1) = 0 := hΦR _ ⟨(p i).1, rfl⟩
      rw [hz] at ht
      simpa [f, dual_def, J] using congrArg (fun z : 𝕜 ↦ (2 : 𝕜)⁻¹ * z) ht
    let fs : Option (Fin n) → StrongDual 𝕜 E := fun i ↦ i.elim f (fun j ↦ (p j).2)
    obtain ⟨x, hx, hfs⟩ := φ.exists_norm_lt_and_forall_apply_eq fs (by norm_num : (0 : ℝ) < 1)
    refine ⟨(x, f), hx, hfn, hfg, ?_, hfx, ?_⟩
    · simpa only [fs, Option.elim_none, hfg] using hfs none
    · intro i
      exact hfs (some i)
  -- Iterate the finite interpolation step, then rescale the vectors into the unit ball.
  choose next hnext using step
  let p : ℕ → E × StrongDual 𝕜 E :=
    Nat.strongRec fun n prev ↦ next n (fun i ↦ prev i i.isLt)
  have hp (n : ℕ) : p n = next n (fun i : Fin n ↦ p i) := by
    exact Nat.strongRec_eq _ n
  have hn (n : ℕ) := hp n ▸ hnext n (fun i : Fin n ↦ p i)
  refine ⟨d / C, fun n ↦ (C⁻¹ : 𝕜) • (p n).1, fun n ↦ (p n).2,
    div_pos hd' hC, ?_, fun n ↦ (hn n).2.1, ?_, ?_⟩
  · intro n
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg hC.le]
    exact (mul_le_mul_of_nonneg_left (hn n).1.le (inv_nonneg.2 hC.le)).trans_eq
      (inv_mul_cancel₀ hC.ne')
  · intro i j hij
    have he : (p i).2 (p j).1 = (d : 𝕜) := by
      rcases hij.eq_or_lt with rfl | hij
      · exact (hn i).2.2.2.1
      · exact ((hn j).2.2.2.2.2 ⟨i, hij⟩).trans (hn i).2.2.1
    simp [map_smul, he, smul_eq_mul, div_eq_mul_inv, mul_comm]
  · intro i j hji
    simp [map_smul, (hn i).2.2.2.2.1 ⟨j, hji⟩]

/-- A triangular array with uniformly bounded functionals and a fixed nonzero diagonal
entry has no weakly convergent subsequence. The vectors need not be norm bounded. -/
theorem not_tendsto_subseq_toWeakSpace_of_dual_triangular
    {θ : 𝕜} (hθ : θ ≠ 0) {x : ℕ → E} {f : ℕ → StrongDual 𝕜 E}
    (hf : ∃ C, ∀ n, ‖f n‖ ≤ C)
    (hdiag : ∀ i j, i ≤ j → f i (x j) = θ)
    (hzero : ∀ i j, j < i → f i (x j) = 0)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (y : E) :
    ¬ Tendsto (fun n ↦ toWeakSpace 𝕜 E (x (σ n))) atTop (𝓝 (toWeakSpace 𝕜 E y)) := by
  intro hlim
  -- The common domain of convergence to zero is a norm-closed linear subspace,
  -- hence weakly closed. All the sequence vectors belong to it.
  let M : Submodule 𝕜 E :=
    { carrier := {z | Tendsto (fun n ↦ f n z) atTop (𝓝 0)}
      zero_mem' := by simp
      add_mem' := fun ha hb ↦ by simpa using ha.add hb
      smul_mem' := fun c _ hz ↦ by simpa using hz.const_smul c }
  have hequi : Equicontinuous (fun n z ↦ f n z) :=
    ((NormedSpace.equicontinuous_tfae f).out 6 2).mp hf
  have hclosed : IsClosed (M : Set E) := hequi.isClosed_setOfPred_tendsto continuous_const
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  have hweak : IsClosed (toWeakSpace 𝕜 E '' (M : Set E)) := by
    apply isClosed_of_closure_subset
    have hconv : Convex ℝ (M : Set E) := by
      simpa only [Submodule.coe_restrictScalars] using (M.restrictScalars ℝ).convex
    rw [← hconv.toWeakSpace_closure 𝕜, hclosed.closure_eq]
  have hx (j : ℕ) : x j ∈ M := by
    exact tendsto_const_nhds.congr'
      (eventually_atTop.2 ⟨j + 1, fun n hn ↦ (hzero n j (by omega)).symm⟩)
  have hy : y ∈ M := by
    obtain ⟨z, hz, hzy⟩ := hweak.mem_of_tendsto hlim
      (Eventually.of_forall fun n ↦ mem_image_of_mem _ (hx (σ n)))
    exact (toWeakSpace 𝕜 E).injective hzy ▸ hz
  have hfy (i : ℕ) : f i y = θ := by
    have hi := (tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hlim) (f i)
    have he : ∀ᶠ n in atTop, f i (x (σ n)) = θ :=
      (hσ.tendsto_atTop.eventually (eventually_ge_atTop i)).mono fun n hn ↦ hdiag i (σ n) hn
    exact tendsto_nhds_unique hi (tendsto_const_nhds.congr' (he.mono fun _ hn ↦ hn.symm))
  have hy0 : Tendsto (fun n ↦ f n y) atTop (𝓝 0) := hy
  exact hθ (tendsto_nhds_unique tendsto_const_nhds (by simpa only [hfy] using hy0))

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A norm-bounded triangular array with uniformly bounded functionals and a fixed
nonzero entry forces nonreflexivity. No completeness assumption is needed. -/
theorem not_surjective_inclusionInDoubleDual_of_exists_seq_dual_triangular
    {θ : 𝕜} (hθ : θ ≠ 0) {x : ℕ → E} {f : ℕ → StrongDual 𝕜 E}
    (hx : ∃ C, ∀ n, ‖x n‖ ≤ C) (hf : ∃ C, ∀ n, ‖f n‖ ≤ C)
    (hdiag : ∀ i j, i ≤ j → f i (x j) = θ)
    (hzero : ∀ i j, j < i → f i (x j) = 0) :
    ¬ Surjective (inclusionInDoubleDual 𝕜 E) := by
  intro hE
  obtain ⟨C, hx⟩ := hx
  obtain ⟨_, ⟨y, -, rfl⟩, σ, hσ, hlim⟩ :=
    isSeqCompact_toWeakSpace_of_isCompact (isCompact_toWeakSpace_closedBall hE 0 C)
      (fun n ↦ mem_image_of_mem _ (mem_closedBall_zero_iff.2 (hx n)))
  exact not_tendsto_subseq_toWeakSpace_of_dual_triangular hθ hf hdiag hzero hσ y hlim

/-- **Triangular sequence criterion for nonreflexivity.** A Banach space is nonreflexive
if and only if its unit ball and dual unit ball admit an exact triangular evaluation
array with a fixed positive entry. -/
theorem not_surjective_inclusionInDoubleDual_iff_exists_seq_dual_triangular [CompleteSpace E] :
    ¬ Surjective (inclusionInDoubleDual 𝕜 E) ↔
      ∃ (θ : ℝ) (x : ℕ → E) (f : ℕ → StrongDual 𝕜 E), 0 < θ ∧
        (∀ n, ‖x n‖ ≤ 1) ∧ (∀ n, ‖f n‖ ≤ 1) ∧
        (∀ i j, i ≤ j → f i (x j) = (θ : 𝕜)) ∧
        (∀ i j, j < i → f i (x j) = 0) := by
  refine ⟨exists_seq_dual_triangular_of_not_surjective_inclusionInDoubleDual, ?_⟩
  rintro ⟨θ, x, f, hθ, hx, hf, hdiag, hzero⟩
  exact not_surjective_inclusionInDoubleDual_of_exists_seq_dual_triangular
    (by exact_mod_cast hθ.ne' : (θ : 𝕜) ≠ 0) ⟨1, hx⟩ ⟨1, hf⟩ hdiag hzero

/-- **Separable reduction of nonreflexivity.** Every nonreflexive Banach space contains
a closed separable subspace which is itself nonreflexive. -/
theorem exists_isClosed_isSeparable_not_surjective_inclusionInDoubleDual [CompleteSpace E]
    (hE : ¬ Surjective (inclusionInDoubleDual 𝕜 E)) :
    ∃ S : Submodule 𝕜 E, IsClosed (S : Set E) ∧ IsSeparable (S : Set E) ∧
      ¬ Surjective (inclusionInDoubleDual 𝕜 S) := by
  obtain ⟨θ, x, f, hθ, hx, hf, hdiag, hzero⟩ :=
    exists_seq_dual_triangular_of_not_surjective_inclusionInDoubleDual hE
  let S := (Submodule.span 𝕜 (range x)).topologicalClosure
  have hxS (n : ℕ) : x n ∈ S :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self n))
  have hclosed : IsClosed (S : Set E) := Submodule.isClosed_topologicalClosure _
  refine ⟨S, hclosed, (countable_range x).isSeparable.span.closure, ?_⟩
  apply not_surjective_inclusionInDoubleDual_of_exists_seq_dual_triangular
    (x := fun n ↦ (⟨x n, hxS n⟩ : S)) (f := fun n ↦ (f n).comp S.subtypeL)
    (by exact_mod_cast hθ.ne' : (θ : 𝕜) ≠ 0) ⟨1, hx⟩ ?_ hdiag hzero
  exact ⟨1, fun n ↦ ((f n).opNorm_comp_le _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans S.norm_subtypeL_le)⟩

end Normed

end TauCeti
