/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.InnerProductSpace.SpectralProjection

/-!
# Spectral projections of self-adjoint Fredholm operators

A self-adjoint Fredholm operator `T` on a complex Hilbert space has some `a > 0` such that for every
self-adjoint `S` near `T` the numbers `±a` are not in the spectrum of `S` and the spectral
projection `cfc ((Icc (-a) a).indicator 1) S` has finite rank equal to the dimension of the kernel
of `T`. This combines the spectral gap of `T` at `0`, the identification of its spectral projection
with the projection onto its kernel, and the local constancy of the rank of spectral projections,
all proved for general self-adjoint operators in
`TauCeti.Analysis.InnerProductSpace.SpectralProjection`.
This is the local input in Phillips' construction of the spectral flow: the spectral flow of a path
counts, along a partition, the changes of the ranks of the spectral projections for `[0, a]`.

## Main results

* `IsSelfAdjoint.exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm`: near a
  self-adjoint Fredholm operator the spectral projections for a fixed interval `[-a, a]` have rank
  equal to the dimension of its kernel.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Filter Set Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace IsSelfAdjoint

variable {T : H →L[ℂ] H}

/-- **Finite spectral projections near a self-adjoint Fredholm operator.** For a self-adjoint
Fredholm operator `T` there is `a > 0` such that every self-adjoint `S` near `T` has neither `-a`
nor `a` in its spectrum, and its spectral projection for `[-a, a]` has finite rank equal to the
dimension of the kernel of `T`. -/
theorem exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm
    (hT : IsSelfAdjoint T) (hF : T.IsFredholm) :
    ∃ a > 0, ∀ᶠ S in 𝓝[{S | IsSelfAdjoint S}] T,
      -a ∉ spectrum ℝ S ∧ a ∉ spectrum ℝ S ∧
        FiniteDimensional ℂ (cfc ((Icc (-a) a).indicator (1 : ℝ → ℝ)) S).range ∧
        Module.finrank ℂ (cfc ((Icc (-a) a).indicator (1 : ℝ → ℝ)) S).range =
          Module.finrank ℂ T.ker := by
  obtain ⟨c, hc, hgap⟩ :=
    hT.exists_pos_spectrum_inter_Ioo_subset_of_isClosed_range hF.isClosed_range
  rw [spectrum.preimage_algebraMap] at hgap
  refine ⟨c / 2, by positivity, ?_⟩
  have hfr : frontier (Icc (-(c / 2)) (c / 2)) = {-(c / 2), c / 2} := frontier_Icc (by linarith)
  have hsub : spectrum ℝ T ∩ Icc (-(c / 2)) (c / 2) ⊆ {0} := fun r hr ↦
    hgap ⟨hr.1, by linarith [hr.2.1], by linarith [hr.2.2]⟩
  have hdisj : Disjoint (frontier (Icc (-(c / 2)) (c / 2))) (spectrum ℝ T) := by
    rw [hfr, Set.disjoint_left]
    intro r hr hrs
    have hr0 : r ≠ 0 := by
      rcases hr with rfl | rfl <;> simp [hc.ne']
    refine hr0 (hsub ⟨hrs, ?_⟩)
    rcases hr with rfl | rfl <;> constructor <;> linarith
  have hker := hT.cfc_indicator_eq_starProjection_ker
    (by rw [mem_Icc]; constructor <;> linarith) hsub hdisj
  have : FiniteDimensional ℂ T.ker := hF.finite_ker
  filter_upwards [hT.eventually_rank_range_cfc_indicator_eq hdisj,
    nhdsWithin_le_nhds (spectrum.eventually_disjoint_of_isClosed isClosed_frontier hdisj)]
    with S hrank hS
  rw [hker, Submodule.range_starProjection] at hrank
  rw [hfr] at hS
  refine ⟨hS.notMem_of_mem_left (by simp), hS.notMem_of_mem_left (by simp), ?_,
    congr_arg Cardinal.toNat hrank⟩
  exact Module.rank_lt_aleph0_iff.1 (hrank ▸ Module.rank_lt_aleph0 ℂ T.ker)

end IsSelfAdjoint
