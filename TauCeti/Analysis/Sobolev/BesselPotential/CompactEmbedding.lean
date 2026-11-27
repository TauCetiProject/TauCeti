/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Rellich.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff

/-!
# Compact Sobolev embeddings of `H^s(ℝⁿ)` into `C^k` with a fixed compact support

Let `E` be a finite-dimensional real inner product space of dimension `n` and `F` a
finite-dimensional complex Hilbert space. For a Schwartz function `φ` with topological support in a
compact set `K` and `s > k + n / 2`, the bounded operator `u ↦ φ u` from the Bessel-potential space
`H^s(E, F)` to Mathlib's space `𝓓^{k}_{K}(E, F)` of `C^k` functions vanishing outside `K`
(`BesselPotentialSpace.smulLeftContDiffMapSupportedIn`) is compact
(`BesselPotentialSpace.isCompactOperator_smulLeftContDiffMapSupportedIn`). So a bounded set of
elements of `H^s` supported in a fixed compact set, on a neighbourhood of which `φ = 1`, has
relatively compact image in `C^k`: every bounded sequence has a subsequence whose derivatives of
order at most `k` converge uniformly.

The compactness is Rellich's theorem composed with the continuous embedding. Choose an order `r`
with `k + n / 2 < r < s` and a compactly supported Schwartz function `ψ` equal to `1` near the
support of `φ`. Then `φ u = φ (ψ u)`, so the operator factors as `u ↦ ψ u`, which is compact from
`H^s` to `H^r` (`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`), followed by
the bounded operator `v ↦ φ v` from `H^r` to `𝓓^{k}_{K}(E, F)`.

## References

* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (Rellich's theorem for a common compact support).
-/

public section

noncomputable section

open Module Set TopologicalSpace
open scoped SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

variable {s : ℝ} {k : ℕ} {φ : 𝓢(E, ℂ)} {K : Compacts E}

/-- **Compactness of the Sobolev embedding into `C^k` with a fixed compact support.** For a
finite-dimensional fibre `F`, a Schwartz function `φ` with topological support in a compact set `K`
and `s > k + dim E / 2`, the operator `u ↦ φ u` from `H^s(E, F)` to `𝓓^{k}_{K}(E, F)` is compact.
In particular a bounded subset of `H^s` on which multiplication by `φ` is the identity, for
instance one of elements supported in a compact set on a neighbourhood of which `φ = 1`, has
relatively compact image in `𝓓^{k}_{K}(E, F)`. -/
theorem isCompactOperator_smulLeftContDiffMapSupportedIn [FiniteDimensional ℂ F]
    (hk : finrank ℝ E + 2 * k < 2 * s) (hφ : tsupport φ ⊆ K) :
    IsCompactOperator (smulLeftContDiffMapSupportedIn F hk hφ) := by
  -- An intermediate order `r` with `k + dim E / 2 < r < s`.
  set r := (finrank ℝ E + 2 * k + 2 * s) / 4
  have hr : finrank ℝ E + 2 * k < 2 * r := by
    simp only [r]
    linarith
  have hrs : r < s := by
    simp only [r]
    linarith
  -- A cutoff `ψ` equal to `1` near the support of `φ`, so that `φ (ψ u) = φ u`.
  obtain ⟨ψ, -, -, hψ⟩ := (K.isCompact.of_isClosed_subset (isClosed_tsupport φ) hφ)
    |>.exists_schwartzMap_cutoff isOpen_univ (subset_univ _)
  have hψφ (x : E) : φ x * ψ x = φ x := by
    by_cases hx : x ∈ tsupport φ
    · simp [hψ.self_of_nhdsSet x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have heq : smulLeftContDiffMapSupportedIn F hk hφ =
      smulLeftContDiffMapSupportedIn F hr hφ ∘L (inclusion hrs.le ∘L smulLeftCLM s ψ) := by
    ext u : 1
    refine ContDiffMapSupportedIn.ext fun x ↦ ?_
    simp [toZeroAtInfty_inclusion (hs := by linarith) hrs.le, smul_smul, hψφ]
  rw [heq, ContinuousLinearMap.coe_comp]
  exact (isCompactOperator_inclusion_comp_smulLeftCLM ψ hrs).clm_comp _

end BesselPotentialSpace
