/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Analysis.InnerProductSpace.Harmonic.Convergence
import TauCeti.Analysis.PDE.Harnack.Basic

/-!
# Harnack's convergence theorem

Let `E` be a finite-dimensional real inner product space. This file proves **Harnack's convergence
theorem**: a monotone family of harmonic functions `E → ℝ` on a preconnected open set `U` that is
bounded above at one point of `U` converges locally uniformly on `U`, and its limit is harmonic.
For `F m ≤ F n` the difference `F n - F m` is harmonic and nonnegative, so Harnack's inequality
(`IsCompact.harnack_inequality`) bounds it on a compact set `K ⊆ U` by a multiple of its value at
the base point, which tends to zero. Harmonicity of the limit then follows from
`TauCeti.harmonicOnNhd_of_tendstoLocallyUniformlyOn`: a locally uniform limit of harmonic
functions is harmonic.

This is the compactness input of Perron's method for the Dirichlet problem, which takes the
limit of increasing sequences of harmonic functions on a ball.

## Main declarations

* `TauCeti.tendstoLocallyUniformlyOn_iSup_of_monotone`: **Harnack's convergence theorem**, the
  locally uniform convergence of a monotone family of harmonic functions.
* `TauCeti.harmonicOnNhd_iSup_of_monotone`: the limit of such a family is harmonic.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.9.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.3.
-/

public section

namespace TauCeti

open InnerProductSpace Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [SemilatticeSup ι] [Nonempty ι] {F : ι → E → ℝ} {U : Set E}

/-- **Harnack's convergence theorem.** Let `F` be a family of functions harmonic on a
preconnected open set `U`, monotone at each point of `U` and bounded above at some point `x₀ ∈ U`.
Then `F` converges locally uniformly on `U` to its pointwise supremum. -/
theorem tendstoLocallyUniformlyOn_iSup_of_monotone (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, HarmonicOnNhd (F i) U) (hmono : ∀ x ∈ U, Monotone fun i ↦ F i x) {x₀ : E}
    (hx₀ : x₀ ∈ U)
    (hbdd : BddAbove (range fun i ↦ F i x₀)) :
    TendstoLocallyUniformlyOn F (fun x ↦ ⨆ i, F i x) atTop U := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2 fun K hKU hK ↦ ?_
  obtain ⟨C, hC, hharnack⟩ :=
    (hK.insert x₀).harnack_inequality hU hUc (insert_subset_iff.2 ⟨hx₀, hKU⟩)
  -- For `m ≤ n`, Harnack's inequality for `F n - F m ≥ 0` compares its values on `K` with its
  -- value at `x₀`.
  have hcomp : ∀ m n, m ≤ n → ∀ x ∈ K, F n x - F m x ≤ C * (F n x₀ - F m x₀) := fun m n hmn x hx ↦
    hharnack (F n - F m) ((hF n).sub (hF m)) (fun z hz ↦ sub_nonneg.2 (hmono z hz hmn)) x
      (mem_insert_of_mem _ hx) x₀ (mem_insert _ _)
  have hlim₀ : Tendsto (fun i ↦ F i x₀) atTop (𝓝 (⨆ i, F i x₀)) :=
    tendsto_atTop_ciSup (hmono x₀ hx₀) hbdd
  -- Every `F n x` with `x ∈ K` lies below `F m x + C * (⨆ i, F i x₀ - F m x₀)`.
  have hupper : ∀ m n, ∀ x ∈ K, F n x ≤ F m x + C * ((⨆ i, F i x₀) - F m x₀) := by
    intro m n x hx
    have h := hcomp m (n ⊔ m) le_sup_right x hx
    have hx₀le : F (n ⊔ m) x₀ ≤ ⨆ i, F i x₀ := le_ciSup hbdd _
    nlinarith [hmono x (hKU hx) (le_sup_left : n ≤ n ⊔ m)]
  have hbddK : ∀ x ∈ K, BddAbove (range fun i ↦ F i x) := fun x hx ↦
    ⟨_, forall_mem_range.2 fun n ↦ hupper (Classical.arbitrary ι) n x hx⟩
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  have hsmall : ∀ᶠ m in atTop, C * ((⨆ i, F i x₀) - F m x₀) < ε := by
    have : Tendsto (fun m ↦ C * ((⨆ i, F i x₀) - F m x₀)) atTop
        (𝓝 (C * ((⨆ i, F i x₀) - ⨆ i, F i x₀))) :=
      (tendsto_const_nhds.sub hlim₀).const_mul C
    exact this.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hsmall] with m hm x hx
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (le_ciSup (hbddK x hx) m))]
  linarith [ciSup_le fun n ↦ hupper m n x hx]

/-- **The limit in Harnack's convergence theorem is harmonic.** Let `F` be a family of functions
harmonic on a preconnected open set `U`, monotone at each point of `U` and bounded above at some
point `x₀ ∈ U`. Then its pointwise supremum is harmonic on `U`. -/
theorem harmonicOnNhd_iSup_of_monotone (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, HarmonicOnNhd (F i) U) (hmono : ∀ x ∈ U, Monotone fun i ↦ F i x) {x₀ : E}
    (hx₀ : x₀ ∈ U)
    (hbdd : BddAbove (range fun i ↦ F i x₀)) :
    HarmonicOnNhd (fun x ↦ ⨆ i, F i x) U :=
  harmonicOnNhd_of_tendstoLocallyUniformlyOn hU (.of_forall hF)
    (tendstoLocallyUniformlyOn_iSup_of_monotone hU hUc hF hmono hx₀ hbdd)

end TauCeti
