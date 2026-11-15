/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Projection
public import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Topology.Algebra.Indicator

/-!
# Spectral flow of paths of self-adjoint Fredholm operators

Let `A` be a continuous path of bounded self-adjoint Fredholm operators on a real or complex
Hilbert space `H`, parametrized by an interval of `ℝ`. Its *spectral flow* `spectralFlow A a b` is
the net number of eigenvalues of `A t` that cross `0` from below as `t` runs from `a` to `b`. We
follow Phillips' construction from spectral projections. Near any parameter `r` there is a level
`c > 0` such that, for `t` near `r`, `c` is not in the spectrum of `A t` and the spectral
projection of `A t` for `[0, c]` has finite rank; we call such a level admissible. The rank
`(A t).spectralRank (Icc 0 c)` of that projection is the number of eigenvalues of `A t` in
`[0, c]`, and it changes exactly when an eigenvalue crosses `0`. The spectral flow adds up the
changes of these counts along a partition of the interval into pieces with admissible levels.

Instead of partitions we use counting functions. A function `σ : ℝ → ℤ` *counts the spectral
flow* of `A` on a set `s` (`TauCeti.IsSpectralFlowCount`) if near every point of `s` it differs by
a constant from the count `(A t).spectralRank (Icc 0 c)` for some admissible level `c`. Two
admissible levels `c' < c` give counts differing by the number of eigenvalues in `(c', c]`, which
is locally constant since neither level is in the spectrum. Hence two counting functions on a
preconnected set differ by a constant (`TauCeti.IsSpectralFlowCount.sub_eq_sub`), which is
Phillips' independence of the partition and of the levels. On a compact interval a counting
function exists (`TauCeti.exists_isSpectralFlowCount`). The spectral flow from `a` to `b` is then
`σ b - σ a` for any counting function `σ` on `[[a, b]]`.

The convention is that an eigenvalue crossing `0` upwards counts `+1`: for the scalar path
`t ↦ tanh t` on a line, the spectral flow from `-1` to `1` is `1`
(`TauCeti.spectralFlow_algebraMap`).

## Main definitions

* `ContinuousLinearMap.spectralRank T Ω`: the rank of the spectral projection of `T` for `Ω ⊆ ℝ`.
* `TauCeti.IsSpectralFlowCount A s σ`: `σ` counts the spectral flow of the path `A` on `s`.
* `TauCeti.spectralFlow A a b`: the spectral flow of `A` from `a` to `b`.

## Main results

* `IsSelfAdjoint.spectralRank_Icc_zero_eq_add`: changing the level of the count by `(c', c]`
  adds the number of eigenvalues in `(c', c]`.
* `TauCeti.IsSpectralFlowCount.sub_eq_sub`: counting functions are unique up to a constant.
* `TauCeti.exists_isSpectralFlowCount`: a continuous path of self-adjoint Fredholm operators on a
  compact interval has a counting function.
* `TauCeti.IsSpectralFlowCount.spectralFlow_eq`: the spectral flow is computed by any counting
  function.
* `TauCeti.spectralFlow_eq_spectralRank_sub_spectralRank`: Phillips' formula on an interval with
  one admissible level.
* `TauCeti.spectralFlow_add_spectralFlow`, `TauCeti.spectralFlow_symm`,
  `TauCeti.spectralFlow_self`: the spectral flow is additive under concatenation and changes sign
  when the endpoints are exchanged.
* `TauCeti.spectralFlow_comp`: invariance under reparametrization.
* `TauCeti.spectralFlow_eq_zero_of_isUnit`: a path of invertible operators has spectral flow `0`.
* `TauCeti.spectralFlow_algebraMap`: the spectral flow of a path of scalar operators.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* B. Booss-Bavnbek, M. Lesch and J. Phillips, *Unbounded Fredholm operators and spectral flow*,
  Canad. J. Math. **57** (2005), 225--250, Section 2.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Filter Set Topology

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-! ### Ranks of spectral projections -/

namespace ContinuousLinearMap

section Rank

variable [Algebra ℝ (H →L[𝕜] H)] [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

/-- The rank of the spectral projection `cfc (Ω.indicator 1) T` of an operator `T` for a set
`Ω ⊆ ℝ`. When `T` is self-adjoint, the frontier of `Ω` avoids its spectrum and the projection has
finite rank, it is the number of eigenvalues of `T` in `Ω`, counted with multiplicity. -/
noncomputable def spectralRank (T : H →L[𝕜] H) (Ω : Set ℝ) : ℕ :=
  Module.finrank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range

theorem spectralRank_def (T : H →L[𝕜] H) (Ω : Set ℝ) :
    T.spectralRank Ω = Module.finrank 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range :=
  (rfl)

/-- The spectral projections of an operator are monotone in the set: the range of the projection
for `Ω₁` lies in that for `Ω₂ ⊇ Ω₁`, when both indicators are continuous on the spectrum. -/
theorem range_cfc_indicator_le_of_subset {T : H →L[𝕜] H} {Ω₁ Ω₂ : Set ℝ} (h : Ω₁ ⊆ Ω₂)
    (h₁ : ContinuousOn (Ω₁.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (h₂ : ContinuousOn (Ω₂.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    (cfc (Ω₁.indicator (1 : ℝ → ℝ)) T).range ≤ (cfc (Ω₂.indicator (1 : ℝ → ℝ)) T).range := by
  have hmul : cfc (Ω₁.indicator (1 : ℝ → ℝ)) T =
      cfc (Ω₂.indicator (1 : ℝ → ℝ)) T * cfc (Ω₁.indicator (1 : ℝ → ℝ)) T := by
    rw [← cfc_mul _ _ T h₂ h₁]
    refine cfc_congr fun x _ ↦ ?_
    by_cases hx : x ∈ Ω₁
    · simp [hx, h hx]
    · simp [hx]
  rintro _ ⟨x, rfl⟩
  refine ⟨cfc (Ω₁.indicator (1 : ℝ → ℝ)) T x, ?_⟩
  simp only [ContinuousLinearMap.coe_coe]
  rw [← mul_apply_eq_comp, ← hmul]

/-- The spectral rank is additive over disjoint sets whose indicators are continuous on the
spectrum, provided the projection for the union has finite rank. -/
theorem spectralRank_union {T : H →L[𝕜] H} {Ω₁ Ω₂ : Set ℝ} (hd : Disjoint Ω₁ Ω₂)
    (h₁ : ContinuousOn (Ω₁.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (h₂ : ContinuousOn (Ω₂.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    [FiniteDimensional 𝕜 (cfc ((Ω₁ ∪ Ω₂).indicator (1 : ℝ → ℝ)) T).range] :
    T.spectralRank (Ω₁ ∪ Ω₂) = T.spectralRank Ω₁ + T.spectralRank Ω₂ := by
  have hc : ContinuousOn ((Ω₁ ∪ Ω₂).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) := by
    rw [indicator_union_of_disjoint hd]
    exact h₁.add h₂
  have hP : cfc ((Ω₁ ∪ Ω₂).indicator (1 : ℝ → ℝ)) T =
      cfc (Ω₁.indicator (1 : ℝ → ℝ)) T + cfc (Ω₂.indicator (1 : ℝ → ℝ)) T := by
    rw [indicator_union_of_disjoint hd, cfc_add (a := T) _ _ h₁ h₂]
  have h₁₂ : cfc (Ω₁.indicator (1 : ℝ → ℝ)) T * cfc (Ω₂.indicator (1 : ℝ → ℝ)) T = 0 := by
    rw [← cfc_mul _ _ T h₁ h₂, ← cfc_zero ℝ T]
    refine cfc_congr fun x _ ↦ ?_
    by_cases hx : x ∈ Ω₁
    · simp [hx, hd.notMem_of_mem_left hx]
    · simp [hx]
  set P₁ := cfc (Ω₁.indicator (1 : ℝ → ℝ)) T
  set P₂ := cfc (Ω₂.indicator (1 : ℝ → ℝ)) T
  set P := cfc ((Ω₁ ∪ Ω₂).indicator (1 : ℝ → ℝ)) T
  have hP₁ : IsIdempotentElem P₁ := (TauCeti.isStarProjection_cfc_indicator T Ω₁).isIdempotentElem
  have hle₁ : P₁.range ≤ P.range := range_cfc_indicator_le_of_subset subset_union_left h₁ hc
  have hle₂ : P₂.range ≤ P.range := range_cfc_indicator_le_of_subset subset_union_right h₂ hc
  have hrange : P.range = P₁.range ⊔ P₂.range := by
    refine le_antisymm ?_ (sup_le hle₁ hle₂)
    rintro _ ⟨x, rfl⟩
    simp only [hP, ContinuousLinearMap.coe_coe, add_apply]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hinf : P₁.range ⊓ P₂.range = ⊥ := by
    refine eq_bot_iff.2 fun y hy ↦ ?_
    obtain ⟨hy₁, hy₂⟩ := Submodule.mem_inf.1 hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hy₁
    obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hy₂
    have hu : P₁ (P₁ u) = P₁ u := by rw [← mul_apply_eq_comp, hP₁.eq]
    simp only [ContinuousLinearMap.coe_coe] at hv ⊢
    rw [Submodule.mem_bot, ← hu, ← hv, ← mul_apply_eq_comp, h₁₂]
    simp
  have : FiniteDimensional 𝕜 P₁.range := Submodule.finiteDimensional_of_le hle₁
  have : FiniteDimensional 𝕜 P₂.range := Submodule.finiteDimensional_of_le hle₂
  have := Submodule.finrank_sup_add_finrank_inf_eq P₁.range P₂.range
  rw [hinf, finrank_bot, add_zero, ← hrange] at this
  rw [spectralRank_def, spectralRank_def, spectralRank_def]
  exact this

/-- The spectral projection for a set disjoint from the spectrum is `0`, so its rank is `0`. -/
theorem spectralRank_eq_zero_of_disjoint {T : H →L[𝕜] H} {Ω : Set ℝ}
    (h : Disjoint Ω (spectrum ℝ T)) : T.spectralRank Ω = 0 := by
  rw [spectralRank_def, cfc_congr (g := 0) fun x hx ↦ indicator_of_notMem
    (h.notMem_of_mem_right hx) _, cfc_zero, ContinuousLinearMap.toLinearMap_zero,
    LinearMap.range_zero, finrank_bot]

end Rank

end ContinuousLinearMap

/-! ### Counting eigenvalues in `[0, c]` -/

section ClosedRange

variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace IsSelfAdjoint

variable {T : H →L[𝕜] H}

omit [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] in
/-- A self-adjoint operator with closed range has a spectral gap below `0`. -/
private theorem exists_pos_disjoint_Ico_spectrum (hT : IsSelfAdjoint T)
    (hR : IsClosed (T.range : Set H)) : ∃ e > 0, Disjoint (Ico (-e) 0) (spectrum ℝ T) := by
  obtain ⟨e, he, hgap⟩ := hT.exists_pos_spectrum_inter_Ioo_subset_of_isClosed_range hR
  rw [spectrum.preimage_algebraMap] at hgap
  refine ⟨e / 2, half_pos he, Set.disjoint_left.2 fun x hx hxs ↦ ?_⟩
  have := hgap ⟨hxs, by linarith [hx.1], by linarith [hx.2]⟩
  exact (ne_of_lt hx.2) (mem_singleton_iff.1 this)

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Below a spectral gap, the spectral projection for `[0, c]` is that for `[-d, c]`. -/
private theorem cfc_indicator_Icc_zero_eq {e d : ℝ} (hgap : Disjoint (Ico (-e) 0) (spectrum ℝ T))
    (hd₀ : 0 ≤ d) (hd : d ≤ e) (c : ℝ) :
    cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) T = cfc ((Icc (-d) c).indicator (1 : ℝ → ℝ)) T := by
  refine cfc_congr fun x hx ↦ ?_
  have hmem : x ∈ Icc 0 c ↔ x ∈ Icc (-d) c :=
    ⟨fun h ↦ ⟨by linarith [h.1], h.2⟩, fun h ↦ ⟨not_lt.1 fun hx₀ ↦
      hgap.notMem_of_mem_right hx ⟨by linarith [h.1], hx₀⟩, h.2⟩⟩
  simp only [indicator_apply, hmem]

/-- If the spectral projection of a self-adjoint operator with closed range for `[-c, c]` has
finite rank, where `±c` are not in the spectrum, then so does its projection for `[0, c]`. -/
theorem finiteDimensional_range_cfc_indicator_Icc_zero (hT : IsSelfAdjoint T)
    (hR : IsClosed (T.range : Set H)) {c : ℝ} (hc : 0 < c) (hnc : -c ∉ spectrum ℝ T)
    (hpc : c ∉ spectrum ℝ T)
    [FiniteDimensional 𝕜 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) T).range] :
    FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) T).range := by
  obtain ⟨e, he, hgap⟩ := hT.exists_pos_disjoint_Ico_spectrum hR
  set d := min e c
  have hd : 0 < d := lt_min he hc
  have hnd : -d ∉ spectrum ℝ T := hgap.notMem_of_mem_left ⟨neg_le_neg (min_le_left e c), by
    linarith⟩
  rw [cfc_indicator_Icc_zero_eq hgap hd.le (min_le_left e c)]
  refine Submodule.finiteDimensional_of_le
    (ContinuousLinearMap.range_cfc_indicator_le_of_subset (Icc_subset_Icc_left
      (neg_le_neg (min_le_right e c))) ?_ ?_)
  · refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
    rw [frontier_Icc (by linarith)]
    simp [Set.disjoint_insert_left, hnd, hpc]
  · refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
    rw [frontier_Icc (by linarith)]
    simp [Set.disjoint_insert_left, hnc, hpc]

/-- **Change of level.** For a self-adjoint operator with closed range and levels `0 ≤ c' < c`
outside its spectrum, with finite-rank projection for `[0, c]`, the number of eigenvalues in
`[0, c]` is the number in `[0, c']` plus the number in `(c', c]`. -/
theorem spectralRank_Icc_zero_eq_add (hT : IsSelfAdjoint T) (hR : IsClosed (T.range : Set H))
    {c c' : ℝ} (hc' : 0 ≤ c') (hc'c : c' < c) (hnc' : c' ∉ spectrum ℝ T)
    (hnc : c ∉ spectrum ℝ T) [FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) T).range] :
    T.spectralRank (Icc 0 c) = T.spectralRank (Icc 0 c') + T.spectralRank (Ioc c' c) := by
  obtain ⟨e, he, hgap⟩ := hT.exists_pos_disjoint_Ico_spectrum hR
  have hne : -e ∉ spectrum ℝ T := hgap.notMem_of_mem_left ⟨le_rfl, by linarith⟩
  have hU : Icc (-e) c = Icc (-e) c' ∪ Ioc c' c := (Icc_union_Ioc_eq_Icc (by linarith) hc'c.le).symm
  have heq : ∀ x, cfc ((Icc 0 x).indicator (1 : ℝ → ℝ)) T =
      cfc ((Icc (-e) x).indicator (1 : ℝ → ℝ)) T :=
    cfc_indicator_Icc_zero_eq hgap he.le le_rfl
  have hfd : FiniteDimensional 𝕜
      (cfc ((Icc (-e) c' ∪ Ioc c' c).indicator (1 : ℝ → ℝ)) T).range := by
    rw [← hU, ← heq]
    infer_instance
  have hrank : ∀ x, T.spectralRank (Icc 0 x) = T.spectralRank (Icc (-e) x) := fun x ↦ by
    rw [ContinuousLinearMap.spectralRank_def, ContinuousLinearMap.spectralRank_def, heq]
  rw [hrank, hrank, hU]
  refine ContinuousLinearMap.spectralRank_union ?_ ?_ ?_
  · exact Set.disjoint_left.2 fun x h₁ h₂ ↦ (not_le.2 h₂.1) h₁.2
  · refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
    rw [frontier_Icc (by linarith)]
    simp [Set.disjoint_insert_left, hne, hnc']
  · refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
    rw [frontier_Ioc hc'c]
    simp [Set.disjoint_insert_left, hnc', hnc]

end IsSelfAdjoint

end ClosedRange

variable [NormedAlgebra ℝ (H →L[𝕜] H)]
  [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace TauCeti

/-! ### Counting functions of the spectral flow -/

variable {A : ℝ → H →L[𝕜] H}

/-- A function `σ : ℝ → ℤ` *counts the spectral flow* of the path `A` on `s` if near every point
`r` of `s` there is a level `c > 0` such that, for `t` in `s` near `r`, `c` is not in the spectrum
of `A t`, the spectral projection of `A t` for `[0, c]` has finite rank, and `σ t` differs from
the number `(A t).spectralRank (Icc 0 c)` of eigenvalues of `A t` in `[0, c]` by the same constant
as at `r`. -/
def IsSpectralFlowCount (A : ℝ → H →L[𝕜] H) (s : Set ℝ) (σ : ℝ → ℤ) : Prop :=
  ∀ r ∈ s, ∃ c > 0, ∀ᶠ t in 𝓝[s] r, c ∉ spectrum ℝ (A t) ∧
    FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A t)).range ∧
    σ t - (A t).spectralRank (Icc 0 c) = σ r - (A r).spectralRank (Icc 0 c)

/-- A function counting the spectral flow on `s` counts it on every subset of `s`. -/
theorem IsSpectralFlowCount.mono {s s' : Set ℝ} {σ : ℝ → ℤ} (h : IsSpectralFlowCount A s σ)
    (hs : s' ⊆ s) : IsSpectralFlowCount A s' σ := fun r hr ↦
  let ⟨c, hc, h⟩ := h r (hs hr)
  ⟨c, hc, nhdsWithin_mono r hs h⟩

/-- The number of eigenvalues in `[0, c]` counts the spectral flow on a set along which the level
`c` is admissible. -/
theorem isSpectralFlowCount_spectralRank {s : Set ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ t ∈ s, c ∉ spectrum ℝ (A t) ∧
      FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A t)).range) :
    IsSpectralFlowCount A s fun t ↦ (A t).spectralRank (Icc 0 c) := fun _ _ ↦
  ⟨c, hc, eventually_nhdsWithin_of_forall fun t ht ↦ ⟨(h t ht).1, (h t ht).2, by simp⟩⟩

/-- A counting function of the spectral flow of `A` on `s` composed with a continuous map `φ`
from `s'` to `s` counts the spectral flow of `A ∘ φ` on `s'`. -/
theorem IsSpectralFlowCount.comp {s s' : Set ℝ} {σ : ℝ → ℤ} {φ : ℝ → ℝ}
    (h : IsSpectralFlowCount A s σ) (hφ : ContinuousOn φ s') (hmaps : MapsTo φ s' s) :
    IsSpectralFlowCount (fun t ↦ A (φ t)) s' (fun t ↦ σ (φ t)) := fun r hr ↦
  let ⟨c, hc, h⟩ := h (φ r) (hmaps hr)
  ⟨c, hc, (hφ r hr).tendsto_nhdsWithin hmaps |>.eventually h⟩

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- Near a point of a continuous path of self-adjoint operators with closed range, the counts for
two levels `0 < c' < c` that stay admissible differ by the number of eigenvalues in `(c', c]` at
that point. -/
private theorem eventually_spectralRank_Icc_zero_eq_add {s : Set ℝ} {r : ℝ}
    (hA : ContinuousWithinAt A s r) (hr : r ∈ s) (hsa : ∀ t ∈ s, IsSelfAdjoint (A t))
    (hR : ∀ t ∈ s, IsClosed ((A t).range : Set H)) {c c' : ℝ} (hc' : 0 < c') (hc'c : c' < c)
    (H : ∀ᶠ t in 𝓝[s] r, c ∉ spectrum ℝ (A t) ∧
      FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A t)).range)
    (H' : ∀ᶠ t in 𝓝[s] r, c' ∉ spectrum ℝ (A t)) :
    ∀ᶠ t in 𝓝[s] r, (A t).spectralRank (Icc 0 c) =
      (A t).spectralRank (Icc 0 c') + (A r).spectralRank (Ioc c' c) := by
  have hdisj : Disjoint (frontier (Ioc c' c)) (spectrum ℝ (A r)) := by
    rw [frontier_Ioc hc'c]
    simp [Set.disjoint_insert_left, H'.self_of_nhdsWithin hr, (H.self_of_nhdsWithin hr).1]
  have htend : Tendsto A (𝓝[s] r) (𝓝[{S | IsSelfAdjoint S}] (A r)) :=
    tendsto_nhdsWithin_iff.2 ⟨hA, eventually_mem_nhdsWithin.mono hsa⟩
  filter_upwards [H, H', self_mem_nhdsWithin,
    htend.eventually ((hsa r hr).eventually_rank_range_cfc_indicator_eq hdisj)]
    with t hcfd hc't hts hrank
  obtain ⟨hct, hfd⟩ := hcfd
  rw [(hsa t hts).spectralRank_Icc_zero_eq_add (hR t hts) hc'.le hc'c hc't hct]
  congr 1
  exact congrArg Cardinal.toNat hrank

/-- **Uniqueness of counting functions.** Two functions counting the spectral flow of a continuous
path of self-adjoint operators with closed range on a preconnected set differ by a constant. -/
theorem IsSpectralFlowCount.sub_eq_sub {s : Set ℝ} {σ₁ σ₂ : ℝ → ℤ}
    (h₁ : IsSpectralFlowCount A s σ₁) (h₂ : IsSpectralFlowCount A s σ₂) (hs : IsPreconnected s)
    (hA : ContinuousOn A s) (hsa : ∀ t ∈ s, IsSelfAdjoint (A t))
    (hR : ∀ t ∈ s, IsClosed ((A t).range : Set H)) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    σ₁ x - σ₂ x = σ₁ y - σ₂ y := by
  -- The difference `σ₁ - σ₂` is locally constant on `s`: near `r`, each `σᵢ` differs by a constant
  -- from the count for its level, and the counts for two levels differ by a constant.
  have hloc : ∀ r ∈ s, ∀ᶠ t in 𝓝[s] r, σ₁ t - σ₂ t = σ₁ r - σ₂ r := by
    intro r hr
    obtain ⟨c₁, hc₁, H₁⟩ := h₁ r hr
    obtain ⟨c₂, hc₂, H₂⟩ := h₂ r hr
    have hlev : ∀ᶠ t in 𝓝[s] r, ((A t).spectralRank (Icc 0 c₁) : ℤ) -
        (A t).spectralRank (Icc 0 c₂) =
          ((A r).spectralRank (Icc 0 c₁) : ℤ) - (A r).spectralRank (Icc 0 c₂) := by
      rcases lt_trichotomy c₂ c₁ with hlt | rfl | hlt
      · have := eventually_spectralRank_Icc_zero_eq_add (hA r hr) hr hsa hR hc₂ hlt
          (H₁.mono fun t ht ↦ ⟨ht.1, ht.2.1⟩) (H₂.mono fun t ht ↦ ht.1)
        filter_upwards [this] with t ht
        rw [ht, this.self_of_nhdsWithin hr]
        push_cast
        ring
      · exact Eventually.of_forall fun t ↦ by simp
      · have := eventually_spectralRank_Icc_zero_eq_add (hA r hr) hr hsa hR hc₁ hlt
          (H₂.mono fun t ht ↦ ⟨ht.1, ht.2.1⟩) (H₁.mono fun t ht ↦ ht.1)
        filter_upwards [this] with t ht
        rw [ht, this.self_of_nhdsWithin hr]
        push_cast
        ring
    filter_upwards [H₁, H₂, hlev] with t ht₁ ht₂ ht
    linarith [ht₁.2.2, ht₂.2.2]
  have := isPreconnected_iff_preconnectedSpace.mp hs
  let g : s → ℤ := fun t ↦ σ₁ t - σ₂ t
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro r
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact (hloc r r.2).comap _
  exact hg.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- A counting function on `[a, t]` extends to `[a, t']` when one level is admissible on the part
of `[a, t']` to the right of some `u < t`. -/
private theorem IsSpectralFlowCount.exists_extend {a t t' u c : ℝ} {σ : ℝ → ℤ}
    (hσ : IsSpectralFlowCount A (Icc a t) σ) (hat : a ≤ t) (htt' : t ≤ t') (hut : u < t)
    (hc : 0 < c) (hadm : ∀ x ∈ Icc a t' ∩ Ioi u, c ∉ spectrum ℝ (A x) ∧
      FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A x)).range)
    (hA : ContinuousOn A (Icc a t')) (hsa : ∀ x ∈ Icc a t', IsSelfAdjoint (A x))
    (hR : ∀ x ∈ Icc a t', IsClosed ((A x).range : Set H)) :
    ∃ σ', IsSpectralFlowCount A (Icc a t') σ' := by
  set N : ℝ → ℤ := fun x ↦ (A x).spectralRank (Icc 0 c)
  have hsub : Icc a t ∩ Ioi u ⊆ Icc a t' ∩ Ioi u :=
    inter_subset_inter_left _ (Icc_subset_Icc_right htt')
  have hJ : Icc a t ∩ Ioi u ⊆ Icc a t' := hsub.trans inter_subset_left
  -- On the overlap `[a, t] ∩ (u, ∞)`, `σ` and the count for the level `c` differ by a constant.
  have hconst : ∀ x ∈ Icc a t ∩ Ioi u, σ x - N x = σ t - N t := fun x hx ↦
    (hσ.mono inter_subset_left).sub_eq_sub
      (isSpectralFlowCount_spectralRank hc fun y hy ↦ hadm y (hsub hy))
      (ordConnected_Icc.inter ordConnected_Ioi).isPreconnected (hA.mono hJ)
      (fun y hy ↦ hsa y (hJ hy)) (fun y hy ↦ hR y (hJ hy)) hx ⟨⟨hat, le_rfl⟩, hut⟩
  set σ' : ℝ → ℤ := fun x ↦ if x ≤ t then σ x else σ t - N t + N x
  have hσ' : ∀ x ∈ Icc a t' ∩ Ioi u, σ' x - N x = σ t - N t := by
    intro x hx
    by_cases hxt : x ≤ t
    · simp only [σ', hxt, ↓reduceIte]
      exact hconst x ⟨⟨hx.1.1, hxt⟩, hx.2⟩
    · simp only [σ', hxt, ↓reduceIte]
      ring
  refine ⟨σ', fun r hr ↦ ?_⟩
  rcases lt_or_ge r t with hrt | hrt
  · -- To the left of `t`, `σ'` is `σ`.
    obtain ⟨c₀, hc₀, h₀⟩ := hσ r ⟨hr.1, hrt.le⟩
    have hle : 𝓝[Icc a t'] r ≤ 𝓝[Icc a t] r := nhdsWithin_le_of_mem
      (mem_nhdsWithin.2 ⟨Iio t, isOpen_Iio, hrt, fun x hx ↦ ⟨hx.2.1, hx.1.le⟩⟩)
    refine ⟨c₀, hc₀, ?_⟩
    filter_upwards [hle h₀, nhdsWithin_le_nhds (Iio_mem_nhds hrt)] with x hx hxt
    simpa only [σ', hrt.le, (mem_Iio.1 hxt).le, ↓reduceIte] using hx
  · -- From `t` on, `σ'` differs from the count for the level `c` by a constant.
    have hru : u < r := hut.trans_le hrt
    refine ⟨c, hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hru)] with x hx hxu
    exact ⟨(hadm x ⟨hx, hxu⟩).1, (hadm x ⟨hx, hxu⟩).2,
      (hσ' x ⟨hx, hxu⟩).trans (hσ' r ⟨hr, hru⟩).symm⟩

/-- Along a continuous path of self-adjoint Fredholm operators on a compact interval, there is
`δ > 0` such that every point `x` has a level that is admissible on the `δ`-neighbourhood of `x`:
a Lebesgue number of the cover by neighbourhoods on which some level is admissible. -/
private theorem exists_pos_forall_exists_admissible {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∃ c > 0, ∀ t ∈ Icc a b, dist t x < δ →
      c ∉ spectrum ℝ (A t) ∧
        FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A t)).range := by
  -- Every point has a neighbourhood on which some level is admissible.
  have hloc : ∀ r ∈ Icc a b, ∃ c > 0, ∀ᶠ t in 𝓝[Icc a b] r, c ∉ spectrum ℝ (A t) ∧
      FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A t)).range := by
    intro r hr
    obtain ⟨c, hc, h⟩ :=
      (hsa r hr).exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm (hF r hr)
    have htend : Tendsto A (𝓝[Icc a b] r) (𝓝[{S | IsSelfAdjoint S}] (A r)) :=
      tendsto_nhdsWithin_iff.2 ⟨hA r hr, eventually_mem_nhdsWithin.mono hsa⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [htend.eventually h, self_mem_nhdsWithin] with t hS ht
    obtain ⟨hnc, hpc, hfd, -⟩ := hS
    exact ⟨hpc, (hsa t ht).finiteDimensional_range_cfc_indicator_Icc_zero (hF t ht).isClosed_range
      hc hnc hpc⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Icc a b)
    (c := fun U : {U : Set ℝ // IsOpen U ∧ ∃ c > 0, ∀ t ∈ U ∩ Icc a b,
      c ∉ spectrum ℝ (A t) ∧
        FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A t)).range} ↦ (U : Set ℝ))
    isCompact_Icc (fun U ↦ U.2.1) fun r hr ↦ by
      obtain ⟨c, hc, h⟩ := hloc r hr
      obtain ⟨U, hU, hrU, hUs⟩ := mem_nhdsWithin.1 h
      exact mem_iUnion.2 ⟨⟨U, hU, c, hc, fun t ht ↦ hUs ht⟩, hrU⟩
  refine ⟨δ, hδ, fun x hx ↦ ?_⟩
  obtain ⟨⟨U, hUo, c, hc, hU⟩, hxU⟩ := hball x hx
  exact ⟨c, hc, fun t ht htx ↦ hU t ⟨hxU (Metric.mem_ball.2 htx), ht⟩⟩

/-- **Existence of counting functions.** A continuous path of self-adjoint Fredholm operators on a
compact interval has a function counting its spectral flow. -/
theorem exists_isSpectralFlowCount {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) :
    ∃ σ, IsSpectralFlowCount A (Icc a b) σ := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨0, fun r hr ↦ absurd (hr.1.trans hr.2) (not_le.2 hba)⟩
  obtain ⟨δ, hδ, hlev⟩ := exists_pos_forall_exists_admissible hA hsa hF
  -- Extend a counting function to the right by steps of length `δ / 2`.
  have key : ∀ n : ℕ, ∀ t ∈ Icc a b, t ≤ a + n * (δ / 2) →
      ∃ σ, IsSpectralFlowCount A (Icc a t) σ := by
    intro n
    induction n with
    | zero =>
      intro t ht hta
      rw [Nat.cast_zero, zero_mul, add_zero] at hta
      obtain ⟨c, hc, h⟩ := hlev t ht
      refine ⟨_, isSpectralFlowCount_spectralRank hc fun x hx ↦
        h x ⟨hx.1, hx.2.trans ht.2⟩ ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    | succ n ih =>
      intro t ht hta
      by_cases htn : t ≤ a + n * (δ / 2)
      · exact ih t ht htn
      replace htn := not_le.1 htn
      have ht₀ : a + n * (δ / 2) ∈ Icc a b :=
        ⟨le_add_of_nonneg_right (by positivity), htn.le.trans ht.2⟩
      obtain ⟨σ, hσ⟩ := ih _ ht₀ le_rfl
      obtain ⟨c, hc, h⟩ := hlev _ ht₀
      have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
      refine hσ.exists_extend ht₀.1 htn.le (by linarith : a + n * (δ / 2) - δ / 2 < _) hc
        (fun x hx ↦ h x (hsub hx.1) ?_) (hA.mono hsub) (fun x hx ↦ hsa x (hsub hx))
        (fun x hx ↦ (hF x (hsub hx)).isClosed_range)
      rw [Real.dist_eq, abs_lt]
      push_cast at hta
      constructor <;> linarith [hx.1.2, mem_Ioi.1 hx.2]
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / (δ / 2))
  refine key n b ⟨hab, le_rfl⟩ ?_
  rw [div_le_iff₀ (by positivity)] at hn
  linarith

/-! ### The spectral flow -/

/-- The **spectral flow** of a path `A` of self-adjoint Fredholm operators from `a` to `b`: the net
number of eigenvalues crossing `0` upwards, computed as `σ b - σ a` for a function `σ` counting the
spectral flow of `A` on `[[a, b]]` (`TauCeti.IsSpectralFlowCount.spectralFlow_eq`). It is `0` if
there is no counting function. -/
noncomputable def spectralFlow (A : ℝ → H →L[𝕜] H) (a b : ℝ) : ℤ :=
  open scoped Classical in
  if h : ∃ σ, IsSpectralFlowCount A (uIcc a b) σ then h.choose b - h.choose a else 0

/-- The spectral flow is computed by any counting function on a set containing `[[a, b]]`. -/
theorem IsSpectralFlowCount.spectralFlow_eq {s : Set ℝ} {σ : ℝ → ℤ}
    (hσ : IsSpectralFlowCount A s σ) {a b : ℝ} (hab : uIcc a b ⊆ s)
    (hA : ContinuousOn A (uIcc a b)) (hsa : ∀ t ∈ uIcc a b, IsSelfAdjoint (A t))
    (hR : ∀ t ∈ uIcc a b, IsClosed ((A t).range : Set H)) :
    spectralFlow A a b = σ b - σ a := by
  have h : ∃ σ, IsSpectralFlowCount A (uIcc a b) σ := ⟨σ, hσ.mono hab⟩
  simp only [spectralFlow, h, ↓reduceDIte]
  have := h.choose_spec.sub_eq_sub (hσ.mono hab) isPreconnected_uIcc hA hsa hR right_mem_uIcc
    left_mem_uIcc
  linarith

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
@[simp]
theorem spectralFlow_self (A : ℝ → H →L[𝕜] H) (a : ℝ) : spectralFlow A a a = 0 := by
  unfold spectralFlow
  split_ifs <;> simp

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **Reversal.** Exchanging the endpoints changes the sign of the spectral flow. -/
theorem spectralFlow_symm (A : ℝ → H →L[𝕜] H) (a b : ℝ) :
    spectralFlow A b a = -spectralFlow A a b := by
  unfold spectralFlow
  rw [uIcc_comm b a]
  split_ifs <;> simp

/-- **Concatenation.** The spectral flow is additive along a continuous path of self-adjoint
Fredholm operators. -/
theorem spectralFlow_add_spectralFlow {p q a b c : ℝ} (hA : ContinuousOn A (Icc p q))
    (hsa : ∀ t ∈ Icc p q, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc p q, (A t).IsFredholm)
    (ha : a ∈ Icc p q) (hb : b ∈ Icc p q) (hc : c ∈ Icc p q) :
    spectralFlow A a b + spectralFlow A b c = spectralFlow A a c := by
  obtain ⟨σ, hσ⟩ := exists_isSpectralFlowCount hA hsa hF
  have hR : ∀ t ∈ Icc p q, IsClosed ((A t).range : Set H) := fun t ht ↦ (hF t ht).isClosed_range
  have key : ∀ x ∈ Icc p q, ∀ y ∈ Icc p q, spectralFlow A x y = σ y - σ x := fun x hx y hy ↦
    hσ.spectralFlow_eq (uIcc_subset_Icc hx hy) (hA.mono (uIcc_subset_Icc hx hy))
      (fun t ht ↦ hsa t (uIcc_subset_Icc hx hy ht)) (fun t ht ↦ hR t (uIcc_subset_Icc hx hy ht))
  rw [key a ha b hb, key b hb c hc, key a ha c hc]
  ring

/-- **Phillips' formula on one interval.** If a single level `c` is admissible along the whole
path, the spectral flow is the change of the number of eigenvalues in `[0, c]`. -/
theorem spectralFlow_eq_spectralRank_sub_spectralRank {a b c : ℝ} (hc : 0 < c)
    (h : ∀ t ∈ uIcc a b, c ∉ spectrum ℝ (A t) ∧
      FiniteDimensional 𝕜 (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) (A t)).range)
    (hA : ContinuousOn A (uIcc a b)) (hsa : ∀ t ∈ uIcc a b, IsSelfAdjoint (A t))
    (hR : ∀ t ∈ uIcc a b, IsClosed ((A t).range : Set H)) :
    spectralFlow A a b = (A b).spectralRank (Icc 0 c) - (A a).spectralRank (Icc 0 c) :=
  (isSpectralFlowCount_spectralRank hc h).spectralFlow_eq subset_rfl hA hsa hR

/-- **Reparametrization.** For a continuous map `φ` sending `[[a, b]]` into `[[φ a, φ b]]`, the
spectral flow of `A ∘ φ` from `a` to `b` is that of `A` from `φ a` to `φ b`. -/
theorem spectralFlow_comp {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hmaps : MapsTo φ (uIcc a b) (uIcc (φ a) (φ b))) (hA : ContinuousOn A (uIcc (φ a) (φ b)))
    (hsa : ∀ t ∈ uIcc (φ a) (φ b), IsSelfAdjoint (A t))
    (hF : ∀ t ∈ uIcc (φ a) (φ b), (A t).IsFredholm) :
    spectralFlow (fun t ↦ A (φ t)) a b = spectralFlow A (φ a) (φ b) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, IsSpectralFlowCount A (uIcc (φ a) (φ b)) σ :=
    exists_isSpectralFlowCount hA hsa hF
  have hR : ∀ t ∈ uIcc (φ a) (φ b), IsClosed ((A t).range : Set H) :=
    fun t ht ↦ (hF t ht).isClosed_range
  rw [(hσ.comp hφ hmaps).spectralFlow_eq subset_rfl (hA.comp hφ hmaps)
    (fun t ht ↦ hsa _ (hmaps ht)) (fun t ht ↦ hR _ (hmaps ht)),
    hσ.spectralFlow_eq subset_rfl hA hsa hR]

/-- A continuous path of invertible self-adjoint operators has spectral flow `0`. -/
theorem spectralFlow_eq_zero_of_isUnit {a b : ℝ} (hA : ContinuousOn A (uIcc a b))
    (hsa : ∀ t ∈ uIcc a b, IsSelfAdjoint (A t)) (hu : ∀ t ∈ uIcc a b, IsUnit (A t)) :
    spectralFlow A a b = 0 := by
  have hR : ∀ t ∈ uIcc a b, IsClosed ((A t).range : Set H) := by
    intro t ht
    rw [LinearMap.range_eq_top.2 (ContinuousLinearMap.isUnit_iff_bijective.1 (hu t ht)).2,
      Submodule.top_coe]
    exact isClosed_univ
  -- The zero function counts the spectral flow: near each point, `[0, c]` avoids the spectrum
  -- for some `c > 0`.
  have hσ : IsSpectralFlowCount A (uIcc a b) 0 := by
    intro r hr
    have h0 : (0 : ℝ) ∈ (spectrum ℝ (A r))ᶜ := spectrum.zero_notMem ℝ (hu r hr)
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.1 (spectrum.isClosed (𝕜 := ℝ) (A r)).isOpen_compl 0 h0
    have hdisj : Disjoint (Icc 0 (ε / 2)) (spectrum ℝ (A r)) :=
      Set.disjoint_left.2 fun x hx ↦ hball (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith [hx.1, hx.2])
    refine ⟨ε / 2, by positivity, ?_⟩
    filter_upwards [Tendsto.eventually (hA r hr)
      (spectrum.eventually_disjoint_of_isClosed isClosed_Icc hdisj)] with t ht
    have h0t : cfc ((Icc 0 (ε / 2)).indicator (1 : ℝ → ℝ)) (A t) = 0 := by
      rw [cfc_congr (g := 0) fun x hx ↦ indicator_of_notMem (ht.notMem_of_mem_right hx) _,
        cfc_zero]
    refine ⟨ht.notMem_of_mem_left ⟨by positivity, le_rfl⟩, ?_, ?_⟩
    · rw [h0t, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]
      infer_instance
    · simp [ContinuousLinearMap.spectralRank_eq_zero_of_disjoint ht,
        ContinuousLinearMap.spectralRank_eq_zero_of_disjoint hdisj]
  rw [hσ.spectralFlow_eq subset_rfl hA hsa hR]
  simp

/-- **Scalar paths.** On a finite-dimensional space, the spectral flow of the path of scalar
operators `t ↦ f t` is the dimension times the change of the indicator of `f ≥ 0`. For instance
`t ↦ tanh t` crosses `0` once upwards, and its spectral flow from `-1` to `1` on a line is `1`. -/
theorem spectralFlow_algebraMap [FiniteDimensional 𝕜 H] {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b)) :
    spectralFlow (fun t ↦ algebraMap ℝ (H →L[𝕜] H) (f t)) a b =
      Module.finrank 𝕜 H * ((if 0 ≤ f b then 1 else 0) - if 0 ≤ f a then 1 else 0) := by
  -- The number of eigenvalues in `[0, c]` of a scalar `x < c` is the dimension if `0 ≤ x`.
  have hrank : ∀ x c : ℝ, x < c → (((algebraMap ℝ (H →L[𝕜] H) x).spectralRank (Icc 0 c) : ℕ) : ℤ) =
      Module.finrank 𝕜 H * (if 0 ≤ x then 1 else 0) := by
    intro x c hxc
    rw [ContinuousLinearMap.spectralRank_def, cfc_algebraMap]
    by_cases hx : 0 ≤ x
    · rw [indicator_of_mem (s := Icc 0 c) ⟨hx, hxc.le⟩, Pi.one_apply, map_one,
        LinearMap.range_eq_top.2 fun y ↦ ⟨y, rfl⟩, finrank_top]
      simp [hx]
    · rw [indicator_of_notMem (s := Icc 0 c) fun h ↦ hx h.1, map_zero,
        ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]
      simp [hx]
  have hσ : IsSpectralFlowCount (fun t ↦ algebraMap ℝ (H →L[𝕜] H) (f t)) (uIcc a b)
      fun t ↦ Module.finrank 𝕜 H * (if 0 ≤ f t then 1 else 0) := by
    intro r hr
    refine ⟨|f r| + 1, by positivity, ?_⟩
    have hlt : ∀ᶠ t in 𝓝[uIcc a b] r, |f t| < |f r| + 1 :=
      (continuous_abs.continuousAt.comp_continuousWithinAt (hf r hr)).eventually
        (Iio_mem_nhds (lt_add_one _))
    filter_upwards [hlt] with t ht
    have hft : f t < |f r| + 1 := (le_abs_self (f t)).trans_lt ht
    refine ⟨?_, inferInstance, ?_⟩
    · exact fun h ↦ hft.ne' (mem_singleton_iff.1 (CFC.spectrum_algebraMap_subset (f t) h))
    · rw [hrank _ _ hft, hrank _ _ ((le_abs_self (f r)).trans_lt (lt_add_one _))]
      ring
  rw [hσ.spectralFlow_eq subset_rfl
    ((((continuous_algebraMap 𝕜 (H →L[𝕜] H)).comp (continuous_algebraMap ℝ 𝕜)).comp_continuousOn
      hf).congr fun t _ ↦ IsScalarTower.algebraMap_apply ℝ 𝕜 (H →L[𝕜] H) (f t))
    (fun t _ ↦ cfc_predicate_algebraMap (f t))
    (fun t _ ↦ Submodule.isClosed_of_finiteDimensional _)]
  ring

end TauCeti
