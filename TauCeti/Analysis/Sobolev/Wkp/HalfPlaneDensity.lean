/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.Wkp.ShiftedMollification

/-!
# Approximation up to the real axis in `W^{k,p}` of an upper half, for compact support in `Ω`

Let `Ω ⊆ ℂ` be open and let `Ω⁺ = Ω ∩ {0 < im}` be its upper half
(`TopologicalSpace.Opens.upperHalf`). For a half-disc chart of a surface with boundary, `Ω⁺` is the
interior of the chart image and the real axis is the boundary. This file shows that an element of
`W^{k,p}(Ω⁺)` vanishing off a compact subset `K` of `Ω`, which may meet the real axis, is a limit
in `W^{k,p}(Ω⁺)` of restrictions of test functions on the whole plane, for every order `k` and
`1 ≤ p < ∞` (`TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf`). So such
an element is approximated by functions smooth up to the real axis. The support condition cannot
be dropped: the rest of the boundary of `Ω⁺` can be irregular, for instance a slit, and near it a
general element of `W^{k,p}(Ω⁺)` need not be approximable by functions smooth on the plane.

The argument is the shifted mollification
`TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift`: translate by `2 r i`
upwards and mollify at radius `r`. A ball of radius `r` about a point `z + 2 r i` with `z ∈ Ω⁺`
lies in the open upper half-plane, and when it meets `K` it lies within `2 r` of `K`, so in `Ω` once
`2 r` is below the distance from `K` to the complement of `Ω`.

## Main declarations

* `TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf`: density of
  restrictions of test functions among the elements of `W^{k,p}(Ω⁺)` vanishing off a compact
  subset of `Ω`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 3.22.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Distributions ENNReal Topology

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℂ}

/-- **Density up to the real axis.** Let `Ω ⊆ ℂ` be open, `K ⊆ Ω` compact, `1 ≤ p < ∞` and `k` an
order. An element of `W^{k,p}` of the upper half `Ω ∩ {0 < im}` vanishing off `K` is a limit of
restrictions of test functions on the whole plane. The set `K` may meet the real axis. -/
theorem mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf (hp : p ≠ ∞) {K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (k : ℕ) (u : Wkp volume Ω.upperHalf p k)
    (hu : ∀ᵐ z ∂volume.restrict (Ω.upperHalf : Set ℂ), z ∉ K → value k u z = 0) :
    u ∈ closure (range fun psi : 𝓓((⊤ : Opens ℂ), ℝ) =>
      restrictL (le_top : Ω.upperHalf ≤ ⊤) k (ofTestFunctionₗ (mu := volume) (p := p) k psi)) := by
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  -- Mollify at radius `r j` after translating upwards by `2 r j`.
  set r : ℕ → ℝ := fun j ↦ δ / 2 / (j + 1)
  have hr (j : ℕ) : 0 < r j := by positivity
  have hrδ (j : ℕ) : 2 * r j ≤ δ := by
    have : r j ≤ δ / 2 := div_le_self (by positivity) (by linarith [j.cast_nonneg (α := ℝ)])
    linarith
  have hr0 : Tendsto r atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine mem_closure_range_restrictL_ofTestFunctionₗ_top_of_shift hp hK (l := atTop)
    (phi := fun j ↦ ⟨r j / 2, r j, by linarith [hr j], by linarith [hr j]⟩)
    (h := fun j ↦ ((2 * r j : ℝ) : ℂ) * Complex.I) hr0 ?_ (fun j z hz ↦ ?_) k u hu
  · have h2 : Tendsto (fun j ↦ 2 * r j) atTop (𝓝 0) := by simpa using hr0.const_mul 2
    simpa using ((Complex.continuous_ofReal.tendsto 0).comp h2).mul_const Complex.I
  · rcases (Set.disjoint_or_nonempty_inter (closedBall (z + ((2 * r j : ℝ) : ℂ) * Complex.I) (r j))
      K) with hdisj | ⟨y, hy, hyK⟩
    · exact Or.inr hdisj
    refine Or.inl fun w hw ↦ Opens.mem_upperHalf.2 ⟨hδK (mem_cthickening_of_dist_le w y δ K hyK ?_),
      ?_⟩
    · have := dist_triangle w (z + ((2 * r j : ℝ) : ℂ) * Complex.I) y
      rw [mem_closedBall] at hw hy
      rw [dist_comm] at hy
      linarith [hrδ j]
    · have him := Complex.abs_im_le_norm (w - (z + ((2 * r j : ℝ) : ℂ) * Complex.I))
      rw [mem_closedBall, dist_eq_norm] at hw
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
      have hz0 := (Opens.mem_upperHalf.1 hz).2
      rw [abs_le] at him
      nlinarith [hr j]

end TauCeti.Wkp
