/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.Monotonicity
import TauCeti.Geometry.Manifold.RegularValue.Factorization

/-!
# Almost existence of closed characteristics from a finite capacity

Let `σ` be a symplectic form on a boundaryless finite-dimensional manifold `M`, and `F : M → ℝ` a
smooth function with compact sublevel sets near the levels under consideration. This file proves
the almost existence theorem of Hofer, Zehnder and Struwe for the `π₁`-sensitive capacities:

* if the relative capacity `c°_HZ({F < b}, Z)` is finite, where `Z ⊆ {F ≤ a}`, then almost every
  regular level `F⁻¹(s)`, `s ∈ (a, b)`, carries a closed characteristic contractible in `M`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`), so that every
  level in `(a, b)` has the contractible almost existence property
  (`IsNondegenerate.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top`);
* if the capacity `c°_HZ(M)` of the manifold is finite, every nonempty regular level of `F` with
  compact sublevel sets has the contractible almost existence property
  (`IsNondegenerate.hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top`).

The monotonicity argument
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`) gives, for
almost every `s`, closed characteristics of a fixed bounded period on levels arbitrarily close
above `s`. The remaining step is a limit
(`IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`, in
`TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence`): on a regular
level the Hamiltonian vector field does not vanish, so by the compactness of the nearby levels and
the continuity of the flow these orbits converge, along a subnet, to a closed characteristic of
the level `F⁻¹(s)` itself, of the same bounded period and still contractible in `M`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`: a finite relative
  capacity gives closed characteristics on almost every regular level.
* `IsNondegenerate.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top`: the
  relative almost existence theorem.
* `IsNondegenerate.hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top`: finiteness of
  `c°_HZ(M)` implies the contractible almost existence property of every nonempty regular level
  with compact sublevel sets.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.3 and §5.
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
-/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {Z : Set M} {F : M → ℝ}

/-- **Closed characteristics on almost every level.** Let `σ` be nondegenerate and `F` smooth,
with compact sublevel sets `{F ≤ s}` for `s < b`, let every value in `(a, b)` be attained by `F`,
and let `Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)` is finite, then almost every
regular level `F⁻¹(s)`, `s ∈ (a, b)`, carries a closed characteristic contractible in `M`. -/
theorem ae_hasContractibleClosedCharacteristic (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s})
    (hrange : Ioo a b ⊆ range F) (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) :
    ∀ᵐ s, s ∈ Ioo a b → IsRegularValue I 𝓘(ℝ) F s →
      σ.HasContractibleClosedCharacteristic univ F s := by
  filter_upwards [hσ.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE hF hcpt
    (by rw [I.interior_eq_univ]; exact subset_univ _) hrange hZ hcap] with s hs hsI hreg
  obtain ⟨K, hK⟩ := hs hsI
  refine (hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently hF (a := a) (K := K)
    (b := (s + b) / 2) ((hcpt _ (by linarith [hsI.2])).of_isClosed_subset
      (isClosed_Icc.preimage hF.continuous) fun _ hx ↦ hx.2)
    ⟨hsI.1, by linarith [hsI.2]⟩ hreg (frequently_iff.2 fun {U} hU ↦ ?_)
    ).hasContractibleClosedCharacteristic
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨c, hc, hcK⟩ := hK (ε / 2) (half_pos hε)
  refine ⟨c, hεU ?_, hcK⟩
  rw [mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hc.1, hc.2]

/-- **The relative almost existence theorem.** Under the hypotheses of
`ae_hasContractibleClosedCharacteristic`, in particular finiteness of `c°_HZ({F < b}, Z)` with
`Z ⊆ {F ≤ a}`, every level `F⁻¹(c)` with `c ∈ (a, b)` has the contractible almost existence
property in `M`. -/
theorem hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b c : ℝ}
    (hcpt : ∀ s < b, IsCompact {x | F x ≤ s}) (hrange : Ioo a b ⊆ range F)
    (hZ : Z ⊆ {x | F x ≤ a}) (hcap : σ.relContractibleHZCapacity {x | F x < b} Z ≠ (∞ : ℝ≥0∞))
    (hc : c ∈ Ioo a b) : σ.HasContractibleAlmostExistence univ F c := by
  refine hasContractibleAlmostExistence_iff.2
    ⟨min (c - a) (b - c), lt_min (sub_pos.2 hc.1) (sub_pos.2 hc.2), ?_⟩
  filter_upwards [hσ.ae_hasContractibleClosedCharacteristic hF hcpt hrange hZ hcap]
    with c' h hc' hreg
  exact h ⟨by linarith [hc'.1, min_le_left (c - a) (b - c)],
    by linarith [hc'.2, min_le_right (c - a) (b - c)]⟩ hreg

/-- **Finite capacity implies contractible almost existence** (Barraud–Damian–Humilière–Oancea,
Proposition 6.3, after Hofer–Zehnder and Struwe). Let `σ` be nondegenerate, with finite
`π₁`-sensitive Hofer–Zehnder capacity `c°_HZ(M)`, and let `F` be smooth. Every nonempty regular
level `F⁻¹(c)` such that `{F ≤ b}` is compact for some `b > c` has the contractible almost
existence property in `M`. -/
theorem hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (hcap : σ.contractibleHZCapacity univ ≠ (∞ : ℝ≥0∞)) {b c : ℝ} (hcb : c < b)
    (hcpt : IsCompact {x | F x ≤ b}) (hreg : IsRegularValue I 𝓘(ℝ) F c) (hne : ∃ x, F x = c) :
    σ.HasContractibleAlmostExistence univ F c := by
  -- `F` is open at a point of the regular level, so its range contains a neighbourhood of `c`.
  obtain ⟨x, hx⟩ := hne
  have hrange : range F ∈ 𝓝 c := by
    rw [← hx, ← (hreg.isRegularPoint hx).map_nhds_eq (hF x) (by simp)]
    exact mem_of_superset (image_mem_map univ_mem) (image_subset_range F univ)
  obtain ⟨ε, hε, hεr⟩ := Metric.mem_nhds_iff.1 hrange
  set ε' := min ε (b - c)
  have hε' : 0 < ε' := lt_min hε (sub_pos.2 hcb)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'b : ε' ≤ b - c := min_le_right _ _
  have hball : Ioo (c - ε') (c + ε') ⊆ range F := fun r hr ↦ hεr (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2])
  -- Apply the relative theorem on `(c - ε' / 2, c + ε')` with `Z = {F < c - ε' / 2}`.
  obtain ⟨y, hy⟩ := hball (show c - 3 * ε' / 4 ∈ Ioo (c - ε') (c + ε') from
    ⟨by linarith, by linarith⟩)
  refine hσ.hasContractibleAlmostExistence_of_relContractibleHZCapacity_ne_top hF
    (a := c - ε' / 2) (b := c + ε') (Z := {y | F y < c - ε' / 2})
    (fun s hs ↦ hcpt.of_isClosed_subset (isClosed_le hF.continuous continuous_const)
      fun z hz ↦ by rw [mem_ofPred_eq] at hz ⊢; linarith)
    ((Ioo_subset_Ioo_left (by linarith)).trans hball)
    (fun _ hz ↦ by rw [mem_ofPred_eq] at hz ⊢; exact hz.le)
    (ne_top_of_le_ne_top hcap ((relContractibleHZCapacity_mono (subset_univ _) subset_rfl).trans
      (relContractibleHZCapacity_le_contractibleHZCapacity
        ⟨y, mem_interior_iff_mem_nhds.2 <| (isOpen_lt hF.continuous continuous_const).mem_nhds
          (by rw [mem_ofPred_eq]; linarith)⟩)))
    ⟨by linarith, by linarith⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
