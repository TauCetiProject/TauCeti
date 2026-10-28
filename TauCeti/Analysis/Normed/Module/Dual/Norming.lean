/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Order.IsLUB

/-!
# Predual norming sets

Finite-dimensional subspaces of a continuous dual admit finite norming sets in the
predual unit ball, with any prescribed loss greater than one. Norm-separable sets
of functionals admit countable sets in that ball which recover their norms exactly.

In particular, applying these results with a continuous dual as the predual gives
norm tests on finite-dimensional or norm-separable parts of a bidual using only
evaluations at elements of the original dual. Unlike arbitrary functionals on the
bidual, these evaluations are weak-star continuous. Such norming sets are used in
separable reductions for weak compactness.

The proofs use Mathlib's operator-norm supremum formulas and compactness of the
finite-dimensional unit sphere; no separability or completeness of the predual
is required.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8.
-/

public section

open Filter Metric Set Topology TopologicalSpace

namespace TauCeti

section Finite

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜) in
/-- A finite-dimensional subspace of a continuous dual has a finite norming set
in the predual unit ball, with any loss `A > 1`. This also covers the zero subspace. -/
theorem exists_finset_predual_norming (M : Submodule 𝕜 (StrongDual 𝕜 E))
    [FiniteDimensional 𝕜 M] {A : ℝ} (hA : 1 < A) :
    ∃ t : Finset E, (∀ x ∈ t, ‖x‖ ≤ 1) ∧
      ∀ f ∈ M, ∃ x ∈ t, ‖f‖ ≤ A * ‖f x‖ := by
  classical
  have hApos : 0 < A := zero_lt_one.trans hA
  let U (x : closedBall (0 : E) 1) : Set M := {f | A⁻¹ < ‖(f : StrongDual 𝕜 E) x‖}
  have hU (x : closedBall (0 : E) 1) : IsOpen (U x) := by
    exact isOpen_lt continuous_const
      (((ContinuousLinearMap.apply 𝕜 𝕜 (x : E)).continuous.comp
        M.subtypeL.continuous).norm)
  -- Cover the dual subspace's unit sphere by evaluations which exceed `A⁻¹`.
  have hcover : sphere (0 : M) 1 ⊆ ⋃ x, U x := by
    intro f hf
    have hnorm : ‖(f : StrongDual 𝕜 E)‖ = 1 :=
      (Submodule.norm_coe f).trans ((mem_sphere_zero_iff_norm (E := M)).mp hf)
    obtain ⟨x, hx, hfx⟩ := (f : StrongDual 𝕜 E).exists_lt_apply_of_lt_opNorm
      (by rw [hnorm]; exact (inv_lt_one₀ hApos).mpr hA)
    exact mem_iUnion.mpr ⟨⟨x, mem_closedBall_zero_iff.mpr hx.le⟩, hfx⟩
  obtain ⟨s, hs⟩ := (isCompact_sphere (0 : M) 1).elim_finite_subcover U hU hcover
  refine ⟨insert 0 (s.image Subtype.val), ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact mem_closedBall_zero_iff.mp y.property
  · intro f hf
    by_cases hf0 : f = 0
    · exact ⟨0, Finset.mem_insert_self _ _, by simp [hf0]⟩
    have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
    let g : M := (algebraMap ℝ 𝕜 ‖f‖⁻¹) • (⟨f, hf⟩ : M)
    have hg : g ∈ sphere (0 : M) 1 := by
      apply (mem_sphere_zero_iff_norm (E := M)).mpr
      simp [g, norm_smul, hfpos.ne']
    obtain ⟨x, hxs, hx⟩ := mem_iUnion₂.mp (hs hg)
    have hx' : A⁻¹ < ‖f (x : E)‖ / ‖f‖ := by
      simpa [U, g, norm_smul, abs_of_nonneg (inv_nonneg.mpr hfpos.le),
        div_eq_inv_mul] using hx
    refine ⟨x, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hxs, rfl⟩), ?_⟩
    have := (lt_div_iff₀ hfpos).mp hx'
    nlinarith [inv_mul_cancel₀ hApos.ne']

end Finite

section Countable

variable {𝕜 E : Type*} [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A norm-separable set in a continuous dual admits a countable norming set in
its predual unit ball. The same set recovers the norm of every functional in the
original set, even if the predual is not separable. -/
theorem exists_countable_predual_norming {s : Set (StrongDual 𝕜 E)} (hs : IsSeparable s) :
    ∃ t : Set E, t.Countable ∧ t.Nonempty ∧ (∀ x ∈ t, ‖x‖ ≤ 1) ∧
      ∀ f ∈ s, ‖f‖ = sSup ((fun x ↦ ‖f x‖) '' t) := by
  obtain ⟨d, -, hd, hsd⟩ := hs.exists_countable_dense_subset
  obtain ⟨v, hv⟩ := (hd.insert 0).exists_eq_range (insert_nonempty 0 d)
  -- Choose countably many near-norming vectors for each member of a dense sequence.
  have hseq (n : ℕ) : ∃ u : ℕ → E, (∀ m, ‖u m‖ ≤ 1) ∧
      Tendsto (fun m ↦ ‖v n (u m)‖) atTop (𝓝 ‖v n‖) := by
    have hb : BddAbove ((fun x ↦ ‖v n x‖) '' ball 0 1) := by
      refine ⟨‖v n‖, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (v n).unit_le_opNorm x (mem_ball_zero_iff.mp hx).le
    obtain ⟨a, -, ha, hamem⟩ := exists_seq_tendsto_sSup
      ((nonempty_ball.mpr zero_lt_one).image (fun x ↦ ‖v n x‖)) hb
    choose u hu hua using hamem
    refine ⟨u, fun m ↦ (mem_ball_zero_iff.mp (hu m)).le, ?_⟩
    simpa only [hua, (v n).sSup_unit_ball_eq_norm] using ha
  choose u hu hlim using hseq
  let t : Set E := range (fun p : ℕ × ℕ ↦ u p.1 p.2)
  have ht (n m : ℕ) : u n m ∈ t := mem_range_self (n, m)
  have htunit : ∀ x ∈ t, ‖x‖ ≤ 1 := by
    rintro _ ⟨⟨n, m⟩, rfl⟩
    exact hu n m
  refine ⟨t, countable_range _, range_nonempty _, htunit, ?_⟩
  intro f hf
  let C := sSup ((fun x ↦ ‖f x‖) '' t)
  have hb : BddAbove ((fun x ↦ ‖f x‖) '' t) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (htunit x hx)
  have hC (x : E) (hx : x ∈ t) : ‖f x‖ ≤ C := le_csSup hb (mem_image_of_mem _ hx)
  -- Uniformly bounded tests transfer a norm estimate from the dense sequence to `f`.
  have hdle (n : ℕ) : ‖v n‖ ≤ C + ‖v n - f‖ := by
    apply le_of_tendsto (hlim n)
    filter_upwards [] with m
    calc
      ‖v n (u n m)‖ ≤ ‖f (u n m)‖ + ‖(v n - f) (u n m)‖ := by
        simpa using norm_le_insert' (v n (u n m)) (f (u n m))
      _ ≤ C + ‖v n - f‖ := add_le_add (hC _ (ht n m))
        ((v n - f).unit_le_opNorm _ (hu n m))
  have hfclosure : f ∈ closure (range v) :=
    closure_mono (hv ▸ subset_insert 0 d) (hsd hf)
  have hclosed : IsClosed {g : StrongDual 𝕜 E | ‖g‖ ≤ C + ‖g - f‖} :=
    isClosed_le continuous_norm (continuous_const.add (continuous_id.sub continuous_const).norm)
  have hfle : ‖f‖ ≤ C := by
    have := closure_minimal (range_subset_iff.mpr hdle) hclosed hfclosure
    simpa using this
  exact le_antisymm hfle (csSup_le ((range_nonempty _).image _) (by
    rintro _ ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (htunit x hx)))

end Countable

end TauCeti
