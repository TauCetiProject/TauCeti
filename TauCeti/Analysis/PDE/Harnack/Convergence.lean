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

If instead the family is unbounded above at one point of `U`, the same comparison runs the other
way: Harnack's inequality bounds the value of `F n - F m` at that point by a multiple of its values
on `K`, so `F` tends to `+∞` uniformly on every compact subset of `U`. Since a monotone family is
bounded above at a point exactly when it converges there, these two cases give the dichotomy:
either `F` converges locally uniformly on `U` to a harmonic function, or it tends to `+∞` locally
uniformly on `U`.

This is the compactness input of Perron's method for the Dirichlet problem, which takes the
limit of increasing sequences of harmonic functions on a ball.

## Main declarations

* `TauCeti.tendstoLocallyUniformlyOn_iSup_of_monotone`: **Harnack's convergence theorem**, the
  locally uniform convergence of a monotone family of harmonic functions.
* `TauCeti.harmonicOnNhd_iSup_of_monotone`: the limit of such a family is harmonic.
* `TauCeti.tendsto_atTop_of_monotone_of_not_bddAbove`: a monotone family of harmonic functions
  unbounded above at one point tends to `+∞` uniformly on compact subsets.
* `TauCeti.tendstoLocallyUniformlyOn_iSup_or_tendsto_atTop_of_monotone`: the dichotomy between the
  two cases.

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

/-- **Harnack's convergence theorem, divergent case.** Let `F` be a family of functions harmonic on
a preconnected open set `U`, monotone at each point of `U` and unbounded above at some point
`x₀ ∈ U`. Then `F` tends to `+∞` uniformly on every compact subset `K` of `U`: for every `M`,
eventually `M ≤ F i x` for all `x ∈ K`. -/
theorem tendsto_atTop_of_monotone_of_not_bddAbove (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, HarmonicOnNhd (F i) U) (hmono : ∀ x ∈ U, Monotone fun i ↦ F i x) {x₀ : E}
    (hx₀ : x₀ ∈ U) (hbdd : ¬BddAbove (range fun i ↦ F i x₀)) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    Tendsto (fun p : ι × E ↦ F p.1 p.2) (atTop ×ˢ 𝓟 K) atTop := by
  obtain ⟨C, hC, hharnack⟩ :=
    (hK.insert x₀).harnack_inequality hU hUc (insert_subset_iff.2 ⟨hx₀, hKU⟩)
  let i₀ : ι := Classical.arbitrary ι
  -- The first member of the family is bounded below on `K`.
  obtain ⟨m, hm⟩ := hK.bddBelow_image fun x hx ↦
    ((hF i₀) x (hKU hx)).1.continuousAt.continuousWithinAt
  -- For `i₀ ≤ i`, Harnack's inequality for `F i - F i₀ ≥ 0` bounds its value at `x₀` by a
  -- multiple of its values on `K`.
  have hlow : ∀ i, i₀ ≤ i → ∀ x ∈ K, F i x₀ - F i₀ x₀ ≤ (C + 1) * (F i x - F i₀ x) := by
    intro i hi x hx
    have hx' : 0 ≤ F i x - F i₀ x := sub_nonneg.2 (hmono x (hKU hx) hi)
    have h := hharnack (F i - F i₀) ((hF i).sub (hF i₀)) (fun z hz ↦ sub_nonneg.2 (hmono z hz hi))
      x₀ (mem_insert _ _) x (mem_insert_of_mem _ hx)
    simp only [Pi.sub_apply] at h
    nlinarith
  have htend : Tendsto (fun i ↦ F i x₀) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (hmono x₀ hx₀) fun b ↦ by
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.1 hbdd b
      exact ⟨i, hi.le⟩
  refine tendsto_atTop.2 fun M ↦ eventually_prod_principal_iff.2 ?_
  filter_upwards [htend.eventually_ge_atTop ((C + 1) * (M - m) + F i₀ x₀),
    eventually_ge_atTop i₀] with i hi hii x hx
  have h₁ := hlow i hii x hx
  have h₂ : m ≤ F i₀ x := hm ⟨x, hx, rfl⟩
  have h₃ : M - m ≤ F i x - F i₀ x :=
    le_of_mul_le_mul_left (by linarith) (by linarith : 0 < C + 1)
  linarith

/-- **Harnack's convergence theorem, the dichotomy.** A family of functions harmonic on a
preconnected open set `U` and monotone at each point of `U` either converges locally uniformly on
`U` to its pointwise supremum, which is then harmonic, or tends to `+∞` uniformly on every compact
subset of `U`. -/
theorem tendstoLocallyUniformlyOn_iSup_or_tendsto_atTop_of_monotone (hU : IsOpen U)
    (hUc : IsPreconnected U) (hF : ∀ i, HarmonicOnNhd (F i) U)
    (hmono : ∀ x ∈ U, Monotone fun i ↦ F i x) :
    (TendstoLocallyUniformlyOn F (fun x ↦ ⨆ i, F i x) atTop U ∧
        HarmonicOnNhd (fun x ↦ ⨆ i, F i x) U) ∨
      ∀ K, IsCompact K → K ⊆ U → Tendsto (fun p : ι × E ↦ F p.1 p.2) (atTop ×ˢ 𝓟 K) atTop := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine Or.inr fun K _ hK ↦ ?_
    rw [subset_empty_iff.1 hK, principal_empty, prod_bot]
    exact tendsto_bot
  by_cases hbdd : BddAbove (range fun i ↦ F i x₀)
  · exact Or.inl ⟨tendstoLocallyUniformlyOn_iSup_of_monotone hU hUc hF hmono hx₀ hbdd,
      harmonicOnNhd_iSup_of_monotone hU hUc hF hmono hx₀ hbdd⟩
  · exact Or.inr fun K hK hKU ↦
      tendsto_atTop_of_monotone_of_not_bddAbove hU hUc hF hmono hx₀ hbdd hK hKU

end TauCeti
