/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.Monotonicity

/-!
# The Hofer–Zehnder–Struwe almost existence theorem

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless manifold `M` and let
`F : M → ℝ` be smooth.

**Almost existence.** Let `{F ≤ s}` be compact for `s < b`, let `F` attain every value in
`(a, b)`, and let `Z ⊆ {F ≤ a}`. If the relative `π₁`-sensitive Hofer–Zehnder capacity
`c°_HZ({F < b}, Z)` (`TauCeti.SmoothTwoForm.relContractibleHZCapacity`) is finite, then almost every
regular level of `F` in `(a, b)` carries a closed characteristic contractible in `M`
(`TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`), so every level
in `(a, b)` has the contractible almost existence property
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`). The Hofer–Zehnder
monotonicity argument gives, near almost every level `s`, closed characteristics of a bounded
period on levels in `[s, s + δ]` for every `δ > 0`
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`); at a regular
level they pass to the limit
(`IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`),
giving a closed characteristic on `F⁻¹(s)` itself. This is the relative version, on a family of
levels, of the almost existence theorem of Hofer–Zehnder and Struwe
(Barraud–Damian–Humilière–Oancea, Proposition 6.3), with contractibility tested in the ambient
manifold.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`: finiteness of
  the relative capacity gives closed characteristics on almost every regular level.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`: finiteness of the
  relative capacity gives the contractible almost existence property of every level in `(a, b)`.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.3.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {Z : Set M} {F : M → ℝ}

namespace IsNondegenerate

/-- **Closed characteristics on almost every regular level.** Let `F` be smooth, with compact
sublevel sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be attained by `F`, and let
`Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)` is finite, then almost every regular
level of `F` in `(a, b)` carries a closed characteristic contractible in `M`. -/
theorem ae_hasContractibleClosedCharacteristic (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s})
    (hrange : Ioo a b ⊆ range F) (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) :
    ∀ᵐ s, s ∈ Ioo a b → IsRegularValue I 𝓘(ℝ) F s →
      σ.HasContractibleClosedCharacteristic univ F s := by
  filter_upwards [hσ.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE hF hcpt
    (by simp [ModelWithCorners.interior_eq_univ]) hrange hZ hcap] with s hs hsI hreg
  obtain ⟨K, hK⟩ := hs hsI
  -- The levels carrying short closed characteristics accumulate at `s` from above.
  have hfreq : ∃ᶠ c in 𝓝 s, σ.HasContractibleClosedCharacteristicOfPeriodLE univ F c K := by
    refine frequently_iff.2 fun hU ↦ ?_
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨c, hc, hcK⟩ := hK (δ / 2) (half_pos hδ)
    refine ⟨c, hδU ?_, hcK⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hc.1, hc.2]
  -- `F⁻¹([a, b'])` is compact for `b' = (s + b) / 2 < b`.
  have hb' : (s + b) / 2 < b := by linarith [hsI.2]
  have hcpt' : IsCompact (F ⁻¹' Icc a ((s + b) / 2)) :=
    (hcpt _ hb').of_isClosed_subset (isClosed_Icc.preimage hF.continuous) fun x hx ↦ hx.2
  exact (hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently hF
    ⟨hsI.1, by linarith [hsI.2]⟩ hcpt' hreg hfreq).hasContractibleClosedCharacteristic

/-- **The Hofer–Zehnder–Struwe almost existence theorem.** Let `F` be smooth, with compact
sublevel sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be attained by `F`, and let
`Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)` is finite, then every level `F⁻¹(c)`,
`c ∈ (a, b)`, has the contractible almost existence property in `M`. -/
theorem hasContractibleAlmostExistence (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    {a b c : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s}) (hrange : Ioo a b ⊆ range F)
    (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) (hc : c ∈ Ioo a b) :
    σ.HasContractibleAlmostExistence univ F c := by
  rw [hasContractibleAlmostExistence_iff]
  refine ⟨min (c - a) (b - c), lt_min (by linarith [hc.1]) (by linarith [hc.2]), ?_⟩
  filter_upwards [hσ.ae_hasContractibleClosedCharacteristic hF hcpt hrange hZ hcap] with c' hc'
    hmem
  refine hc' ⟨?_, ?_⟩
  · linarith [hmem.1, min_le_left (c - a) (b - c)]
  · linarith [hmem.2, min_le_right (c - a) (b - c)]

end IsNondegenerate

end SmoothTwoForm

end TauCeti
