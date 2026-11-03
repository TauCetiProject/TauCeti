/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Completion
public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion

/-!
# Series representations of completed projective tensors

Every element `u` of the completed projective tensor product `E ⊗̂π F` is the sum of a
norm-convergent series of pure tensors `∑ n, x n ⊗ₜ y n` whose cost `∑ n, ‖x n‖ * ‖y n‖` is less
than any prescribed bound `c > ‖u‖`. Conversely, the norm of the sum of any such series is at most
its cost. Hence the projective norm of a completed tensor is the infimum of the costs of its series
representations, extending the description of the projective norm of an algebraic tensor as the
infimum of the costs of its finite decompositions.

The series is assembled from the finite decompositions of the terms of an absolutely convergent
series of algebraic tensors converging to `u`, given by
`UniformSpace.Completion.exists_hasSum_coe_of_norm_lt`.

This representation underlies the series description `T x = ∑ n, f n x • y n`, with
`∑ n, ‖f n‖ * ‖y n‖ < ∞`, of nuclear operators: the operators `E →L[𝕜] F` induced by elements of
`StrongDual 𝕜 E ⊗̂π F`.

## Main results

* `TauCeti.CompletedProjectiveTensor.exists_hasSum_tmul_of_norm_lt`: if `‖u‖ < c`, then
  `u = ∑ n, x n ⊗ₜ y n` for some `x : ℕ → E` and `y : ℕ → F` with `∑ n, ‖x n‖ * ‖y n‖ < c`.
* `TauCeti.CompletedProjectiveTensor.norm_le_tsum_of_hasSum_tmul`: the norm of the sum of a series
  of pure tensors is at most its cost.
* `TauCeti.CompletedProjectiveTensor.norm_lt_iff_exists_hasSum_tmul`: the combined
  characterization of the strict sublevel sets of the norm.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Proposition 2.8.
-/

public section

open scoped TensorProduct

open UniformSpace

namespace TauCeti.CompletedProjectiveTensor

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The norm of the sum of a series of pure tensors in the completed projective tensor product is
at most its cost `∑ i, ‖x i‖ * ‖y i‖`. -/
theorem norm_le_tsum_of_hasSum_tmul {ι : Type*} {u : CompletedProjectiveTensor 𝕜 E F}
    {x : ι → E} {y : ι → F}
    (hu : HasSum (fun i ↦ ((⟨x i ⊗ₜ y i⟩ : ProjectiveTensor 𝕜 E F) :
      CompletedProjectiveTensor 𝕜 E F)) u)
    (hxy : Summable fun i ↦ ‖x i‖ * ‖y i‖) :
    ‖u‖ ≤ ∑' i, ‖x i‖ * ‖y i‖ :=
  hu.norm_le_of_bounded hxy.hasSum fun i ↦ norm_coe_tmul_le (x i) (y i)

/-- A finite decomposition of an algebraic tensor, padded by zeros to a sequence: if
`‖w‖ < c`, then `w` is the sum of the pure tensors `x i ⊗ₜ y i` for `i < n`, these
pure tensors vanish for `i ≥ n`, and the cost of the decomposition is less than `c`. -/
private theorem exists_tmul_padded_of_norm_lt {w : ProjectiveTensor 𝕜 E F} {c : ℝ}
    (hw : ‖w‖ < c) :
    ∃ (n : ℕ) (x : ℕ → E) (y : ℕ → F),
      (∀ i, n ≤ i → x i = 0) ∧
      ∑ i ∈ Finset.range n, (⟨x i ⊗ₜ y i⟩ : ProjectiveTensor 𝕜 E F) = w ∧
      ∑ i ∈ Finset.range n, ‖x i‖ * ‖y i‖ < c := by
  obtain ⟨n, x, y, hsum, hcost⟩ :=
    TensorProduct.exists_sum_tmul_eq_of_projectiveSeminorm_lt (𝕜 := 𝕜) (u := w.toTensorProduct)
      (c := c) (by rwa [← ProjectiveTensor.norm_def])
  refine ⟨n, fun i ↦ if h : i < n then x ⟨i, h⟩ else 0, fun i ↦ if h : i < n then y ⟨i, h⟩ else 0,
    fun i hi ↦ by simp [not_lt.2 hi], ?_, ?_⟩
  · rw [Finset.sum_range]
    apply ProjectiveTensor.ext
    rw [← hsum, ← ProjectiveTensor.linearEquiv_apply, map_sum]
    simp
  · rw [Finset.sum_range]
    simpa using hcost

/-- **Series representation of completed projective tensors.** Every element `u` of the
completed projective tensor product is the sum of a norm-convergent series of pure tensors
`∑ n, x n ⊗ₜ y n` whose cost `∑ n, ‖x n‖ * ‖y n‖` is less than any prescribed bound `c > ‖u‖`. -/
theorem exists_hasSum_tmul_of_norm_lt (u : CompletedProjectiveTensor 𝕜 E F) {c : ℝ}
    (hu : ‖u‖ < c) :
    ∃ (x : ℕ → E) (y : ℕ → F),
      HasSum (fun n ↦ ((⟨x n ⊗ₜ y n⟩ : ProjectiveTensor 𝕜 E F) :
        CompletedProjectiveTensor 𝕜 E F)) u ∧
      Summable (fun n ↦ ‖x n‖ * ‖y n‖) ∧ ∑' n, ‖x n‖ * ‖y n‖ < c := by
  set δ := (c - ‖u‖) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  -- An absolutely convergent series of algebraic tensors `w k` with sum `u`.
  obtain ⟨w, hwu, hws, hwc⟩ := Completion.exists_hasSum_coe_of_norm_lt u
    (by linarith : ‖u‖ < ‖u‖ + δ)
  -- Finite decompositions of the `w k`, with cost exceeding `‖w k‖` by less than `δ / 2 / 2 ^ k`.
  have hη (k : ℕ) : ‖w k‖ < ‖w k‖ + δ / 2 / 2 ^ k := by
    have : 0 < δ / 2 / 2 ^ k := by positivity
    linarith
  choose n X Y hXzero hXsum hXcost using fun k ↦ exists_tmul_padded_of_norm_lt (hη k)
  -- The doubly indexed series of pure tensors and of their costs.
  set z : ℕ × ℕ → CompletedProjectiveTensor 𝕜 E F :=
    fun p ↦ ((⟨X p.1 p.2 ⊗ₜ Y p.1 p.2⟩ : ProjectiveTensor 𝕜 E F) :
      CompletedProjectiveTensor 𝕜 E F) with hz_def
  set a : ℕ × ℕ → ℝ := fun p ↦ ‖X p.1 p.2‖ * ‖Y p.1 p.2‖ with ha_def
  have ha_nonneg : 0 ≤ a := fun p ↦ by positivity
  have hrow_a (k : ℕ) : HasSum (fun i ↦ a (k, i)) (∑ i ∈ Finset.range (n k), a (k, i)) :=
    hasSum_sum_of_ne_finset_zero fun i hi ↦ by
      simp [ha_def, hXzero k i (by simpa using hi)]
  have hrow_z (k : ℕ) : HasSum (fun i ↦ z (k, i)) (w k : CompletedProjectiveTensor 𝕜 E F) := by
    have hval : (w k : CompletedProjectiveTensor 𝕜 E F) = ∑ i ∈ Finset.range (n k), z (k, i) := by
      rw [← hXsum k, ← Completion.toCompl_apply, map_sum]
      simp [hz_def]
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero fun i hi ↦ by simp [hz_def, hXzero k i (by simpa using hi)]
  have hrow_le (k : ℕ) : ∑ i ∈ Finset.range (n k), a (k, i) ≤ ‖w k‖ + δ / 2 / 2 ^ k :=
    (hXcost k).le
  have hgeom : HasSum (fun k ↦ ‖w k‖ + δ / 2 / 2 ^ k) (∑' k, ‖w k‖ + δ) :=
    hws.hasSum.add (hasSum_geometric_two' δ)
  have hrows : Summable fun k ↦ ∑ i ∈ Finset.range (n k), a (k, i) :=
    Summable.of_nonneg_of_le (fun k ↦ Finset.sum_nonneg fun i _ ↦ ha_nonneg _) hrow_le
      hgeom.summable
  have ha : Summable a :=
    (summable_prod_of_nonneg ha_nonneg).2
      ⟨fun k ↦ (hrow_a k).summable, by simpa only [(hrow_a _).tsum_eq] using hrows⟩
  have hz : HasSum z u := by
    have hzs : Summable z :=
      Summable.of_norm_bounded ha fun p ↦ norm_coe_tmul_le (X p.1 p.2) (Y p.1 p.2)
    rw [hwu.unique (hzs.hasSum.prod_fiberwise hrow_z)]
    exact hzs.hasSum
  have ha_le : ∑' p, a p < c :=
    calc ∑' p, a p = ∑' k, ∑ i ∈ Finset.range (n k), a (k, i) :=
          (ha.hasSum.prod_fiberwise hrow_a).tsum_eq.symm
      _ ≤ ∑' k, ‖w k‖ + δ := hasSum_le hrow_le hrows.hasSum hgeom
      _ < c := by rw [hδ_def] at hwc ⊢; linarith
  -- Reindex the doubly indexed series by `ℕ` along `Nat.pairEquiv`.
  refine ⟨fun m ↦ X m.unpair.1 m.unpair.2, fun m ↦ Y m.unpair.1 m.unpair.2,
    (Nat.pairEquiv.symm.hasSum_iff (f := z)).2 hz,
    (Nat.pairEquiv.symm.summable_iff (f := a)).2 ha, ?_⟩
  rwa [← Nat.pairEquiv.symm.tsum_eq a] at ha_le

/-- The projective norm of a completed tensor is the infimum of the costs of its series
representations: `‖u‖ < c` if and only if `u = ∑ n, x n ⊗ₜ y n` for some series of pure tensors of
cost `∑ n, ‖x n‖ * ‖y n‖ < c`. -/
theorem norm_lt_iff_exists_hasSum_tmul {u : CompletedProjectiveTensor 𝕜 E F} {c : ℝ} :
    ‖u‖ < c ↔ ∃ (x : ℕ → E) (y : ℕ → F),
      HasSum (fun n ↦ ((⟨x n ⊗ₜ y n⟩ : ProjectiveTensor 𝕜 E F) :
        CompletedProjectiveTensor 𝕜 E F)) u ∧
      Summable (fun n ↦ ‖x n‖ * ‖y n‖) ∧ ∑' n, ‖x n‖ * ‖y n‖ < c :=
  ⟨exists_hasSum_tmul_of_norm_lt u, fun ⟨_, _, hu, hxy, hc⟩ ↦
    (norm_le_tsum_of_hasSum_tmul hu hxy).trans_lt hc⟩

end TauCeti.CompletedProjectiveTensor
