/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Order.IsLUB
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Norming sets for continuous linear maps

Finite-dimensional subspaces of continuous linear maps admit finite norming sets in the
domain unit ball, with any prescribed loss greater than one. Every map has a sequence in
that ball along which its values approach its norm
(`ContinuousLinearMap.exists_seq_norm_apply_tendsto_opNorm`), and norm-separable sets
of maps admit countable sets in that ball which recover their norms exactly.
For a separable domain, a single sequence in its unit ball norms all continuous linear maps,
even when their family is not norm-separable.
Dually, on a separable normed space every norming set of functionals, and every set of
functionals separating points, contains a countable subset with the same property
(`TauCeti.exists_countable_norming_subset`, `TauCeti.exists_countable_separating_subset`).
Tests uniformly norming an increasing sequence of operator subspaces separate points
in the closure of their union.

For scalar-valued maps these are predual norming sets. In particular, applying these
results with a continuous dual as the domain gives
norm tests on finite-dimensional or norm-separable parts of a bidual using only
evaluations at elements of the original dual. Unlike arbitrary functionals on the
bidual, these evaluations are weak-star continuous. Such norming sets are used in
separable reductions for weak compactness.

The operator results use Mathlib's operator-norm supremum formulas and compactness of the
finite-dimensional unit sphere. The finite-dimensional and norm-separable-family results
require neither separability nor completeness of the domain. The countable subsets of
functionals are extracted from a dense sequence and from the Lindelöf property of the
separable space.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8.
-/

public section

open Filter Metric Set Topology TopologicalSpace

section Finite

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A finite-dimensional subspace of continuous linear maps has a finite norming set
in the domain unit ball, with any loss `A > 1`. This also covers the zero subspace. -/
theorem Submodule.exists_finset_norming (M : Submodule 𝕜 (E →L[𝕜] F))
    [FiniteDimensional 𝕜 M] {A : ℝ} (hA : 1 < A) :
    ∃ t : Finset E, (∀ x ∈ t, ‖x‖ ≤ 1) ∧
      ∀ f ∈ M, ∃ x ∈ t, ‖f‖ ≤ A * ‖f x‖ := by
  classical
  have hApos : 0 < A := zero_lt_one.trans hA
  let U (x : closedBall (0 : E) 1) : Set M := {f | A⁻¹ < ‖(f : E →L[𝕜] F) x‖}
  have hU (x : closedBall (0 : E) 1) : IsOpen (U x) := by
    exact isOpen_lt continuous_const
      (((ContinuousLinearMap.apply 𝕜 F (x : E)).continuous.comp
        M.subtypeL.continuous).norm)
  -- Cover the subspace's unit sphere by evaluations which exceed `A⁻¹`.
  have hcover : sphere (0 : M) 1 ⊆ ⋃ x, U x := by
    intro f hf
    have hnorm : ‖(f : E →L[𝕜] F)‖ = 1 :=
      (Submodule.norm_coe f).trans ((mem_sphere_zero_iff_norm (E := M)).mp hf)
    obtain ⟨x, hx, hfx⟩ := (f : E →L[𝕜] F).exists_lt_apply_of_lt_opNorm
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

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear map admits a sequence in the domain unit ball along which the norms
of its values tend to its operator norm. -/
theorem ContinuousLinearMap.exists_seq_norm_apply_tendsto_opNorm (f : E →L[𝕜] F) :
    ∃ v : ℕ → E, (∀ n, ‖v n‖ ≤ 1) ∧ Tendsto (fun n ↦ ‖f (v n)‖) atTop (𝓝 ‖f‖) := by
  have hb : BddAbove ((fun x ↦ ‖f x‖) '' ball 0 1) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_ball_zero_iff.mp hx).le
  obtain ⟨a, -, ha, hamem⟩ := exists_seq_tendsto_sSup
    ((nonempty_ball.mpr zero_lt_one).image (fun x ↦ ‖f x‖)) hb
  choose v hv hav using hamem
  refine ⟨v, fun n ↦ (mem_ball_zero_iff.mp (hv n)).le, ?_⟩
  simpa only [hav, f.sSup_unit_ball_eq_norm] using ha

/-- A norm-separable set of continuous linear maps admits a countable norming set in
the domain unit ball. The same set recovers the norm of every map in the
original set, even if the domain is not separable. -/
theorem TopologicalSpace.IsSeparable.exists_countable_norming
    {s : Set (E →L[𝕜] F)} (hs : IsSeparable s) :
    ∃ t : Set E, t.Countable ∧ t.Nonempty ∧ (∀ x ∈ t, ‖x‖ ≤ 1) ∧
      ∀ f ∈ s, ‖f‖ = sSup ((fun x ↦ ‖f x‖) '' t) := by
  obtain ⟨d, -, hd, hsd⟩ := hs.exists_countable_dense_subset
  obtain ⟨v, hv⟩ := (hd.insert 0).exists_eq_range (insert_nonempty 0 d)
  -- Choose countably many near-norming vectors for each member of a dense sequence.
  choose u hu hlim using fun n ↦ (v n).exists_seq_norm_apply_tendsto_opNorm
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
  have hclosed : IsClosed {g : E →L[𝕜] F | ‖g‖ ≤ C + ‖g - f‖} :=
    isClosed_le continuous_norm (continuous_const.add (continuous_id.sub continuous_const).norm)
  have hfle : ‖f‖ ≤ C := by
    have := closure_minimal (range_subset_iff.mpr hdle) hclosed hfclosure
    simpa using this
  exact le_antisymm hfle (csSup_le ((range_nonempty _).image _) (by
    rintro _ ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (htunit x hx)))

end Countable

section SeparableDomain

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a separable domain, one sequence in the closed unit ball recovers the norm of
every continuous linear map, with no separability assumption on the family of maps. -/
theorem ContinuousLinearMap.exists_seq_norming [SeparableSpace E] :
    ∃ v : ℕ → E, (∀ n, ‖v n‖ ≤ 1) ∧
      ∀ f : E →L[𝕜] F, IsLUB (range fun n ↦ ‖f (v n)‖) ‖f‖ := by
  let B := closedBall (0 : E) 1
  let : Nonempty B := ⟨⟨0, by simp [B]⟩⟩
  let u := denseSeq B
  refine ⟨fun n ↦ (u n : E), fun n ↦ mem_closedBall_zero_iff.mp (u n).property, ?_⟩
  intro f
  have hb : BddAbove ((fun x ↦ ‖f x‖) '' B) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact f.unit_le_opNorm x (mem_closedBall_zero_iff.mp hx)
  have hsup : IsLUB ((fun x ↦ ‖f x‖) '' B) ‖f‖ := by
    rw [← f.sSup_unitClosedBall_eq_norm]
    exact isLUB_csSup ((nonempty_closedBall.mpr zero_le_one).image _) hb
  have hrange : (range fun x : B ↦ ‖f (x : E)‖) = (fun x ↦ ‖f x‖) '' B := by
    ext r
    simp
  have hdense : Dense (range u) := denseRange_denseSeq B
  have hd := hdense.upperBounds_image
    (f.continuous.comp continuous_subtypeVal).norm
  simp only [← range_comp, Function.comp_def, hrange] at hd
  exact (isLUB_congr hd).mpr hsup

end SeparableDomain

namespace TauCeti

section CountableDual

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [SeparableSpace X]

/-- On a separable normed space, a norming set `T` of functionals, in the sense that `‖x‖` is the
supremum of `‖x' x‖` over the members of `T` of norm at most one, contains a countable norming
subset all of whose members have norm at most one. -/
theorem exists_countable_norming_subset {T : Set (StrongDual 𝕜 X)}
    (hT : ∀ x : X, ∀ r < ‖x‖, ∃ x' ∈ T, ‖x'‖ ≤ 1 ∧ r < ‖x' x‖) :
    ∃ T₀ ⊆ T, T₀.Countable ∧ (∀ x' ∈ T₀, ‖x'‖ ≤ 1) ∧ ∀ x : X, ∀ r < ‖x‖, ∃ x' ∈ T₀, r < ‖x' x‖ := by
  obtain ⟨d, hd⟩ := exists_dense_seq X
  -- Countably many tests nearly attain the norms of the points of a dense sequence.
  have hchoice (p : ℕ × ℕ) : ∃ x' ∈ T, ‖x'‖ ≤ 1 ∧ ‖d p.1‖ - 1 / (p.2 + 1) < ‖x' (d p.1)‖ :=
    hT (d p.1) _ (sub_lt_self _ Nat.one_div_pos_of_nat)
  choose g hgT hg1 hgd using hchoice
  refine ⟨range g, range_subset_iff.2 hgT, countable_range g, forall_mem_range.2 hg1,
    fun x r hr ↦ ?_⟩
  -- These tests recover the norm of every point, up to three small errors.
  obtain ⟨n, hn⟩ := hd.exists_dist_lt x (by linarith : 0 < (‖x‖ - r) / 3)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : 0 < (‖x‖ - r) / 3)
  refine ⟨g (n, k), mem_range_self _, ?_⟩
  have h1 : ‖g (n, k) (x - d n)‖ ≤ ‖x - d n‖ :=
    (g (n, k)).le_of_opNorm_le (hg1 _) _ |>.trans_eq (one_mul _)
  have h2 : ‖g (n, k) (d n)‖ ≤ ‖g (n, k) x‖ + ‖g (n, k) (x - d n)‖ := by
    rw [map_sub, norm_sub_rev]
    exact norm_le_insert' _ _
  have h3 : ‖x‖ ≤ ‖d n‖ + ‖x - d n‖ := norm_le_insert' _ _
  rw [dist_eq_norm] at hn
  linarith [hgd (n, k)]

/-- On a separable normed space, a set `T` of functionals separating points contains a countable
subset that still separates points. -/
theorem exists_countable_separating_subset {T : Set (StrongDual 𝕜 X)}
    (hT : ∀ x : X, (∀ x' ∈ T, x' x = 0) → x = 0) :
    ∃ T₀ ⊆ T, T₀.Countable ∧ ∀ x : X, (∀ x' ∈ T₀, x' x = 0) → x = 0 := by
  -- The sets `{x | x' x ≠ 0}`, `x' ∈ T`, cover `{x | x ≠ 0}`; extract a countable subcover.
  obtain ⟨T₀, hT₀T, hT₀c, hT₀⟩ := isOpen_biUnion_countable T (fun x' ↦ {x : X | x' x ≠ 0})
    fun x' _ ↦ isOpen_ne_fun x'.continuous continuous_const
  refine ⟨T₀, hT₀T, hT₀c, fun x hx ↦ by_contra fun hne ↦ ?_⟩
  obtain ⟨x', hx'T, hx'⟩ : ∃ x' ∈ T, x' x ≠ 0 := by
    by_contra! h
    exact hne (hT x h)
  have hmem : x ∈ ⋃ x' ∈ T, {x : X | x' x ≠ 0} := mem_biUnion hx'T hx'
  rw [← hT₀] at hmem
  obtain ⟨i, hi, hix⟩ := mem_iUnion₂.1 hmem
  exact hix (hx i hi)

end CountableDual

end TauCeti

/-- Tests uniformly norming an increasing sequence of operator subspaces separate points
in the closure of their union. -/
theorem ContinuousLinearMap.eq_zero_of_mem_topologicalClosure_iSup_of_norming
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (ψ : E →L[𝕜] F) {M : ℕ → Submodule 𝕜 (E →L[𝕜] F)} (hM : Monotone M)
    {t : ℕ → Set E} {A : ℝ} (hA : 0 ≤ A)
    (ht : ∀ n x, x ∈ t n → ‖x‖ ≤ 1)
    (hnorm : ∀ n g, g ∈ M n → ∃ x ∈ t n, ‖g‖ ≤ A * ‖g x‖)
    (hψ : ψ ∈ (⨆ n, M n).topologicalClosure)
    (hzero : ∀ n x, x ∈ t n → ψ x = 0) : ψ = 0 := by
  have hclosed : IsClosed {g : E →L[𝕜] F | ‖g‖ ≤ A * ‖g - ψ‖} :=
    isClosed_le continuous_norm (continuous_const.mul (continuous_id.sub continuous_const).norm)
  have hbound : (⨆ n, M n : Submodule 𝕜 _) ≤
      {g : E →L[𝕜] F | ‖g‖ ≤ A * ‖g - ψ‖} := by
    intro g hg
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hM.directed_le).mp hg
    obtain ⟨x, hx, hgx⟩ := hnorm n g hn
    calc
      ‖g‖ ≤ A * ‖g x‖ := hgx
      _ = A * ‖(g - ψ) x‖ := by simp [hzero n x hx]
      _ ≤ A * ‖g - ψ‖ := mul_le_mul_of_nonneg_left ((g - ψ).unit_le_opNorm x (ht n x hx)) hA
  have hnorm : ‖ψ‖ ≤ 0 := by
    simpa only [mem_ofPred_eq, sub_self, norm_zero, mul_zero] using
      closure_minimal hbound hclosed hψ
  exact ψ.opNorm_zero_iff'.mp (le_antisymm hnorm ψ.opNorm_nonneg)
