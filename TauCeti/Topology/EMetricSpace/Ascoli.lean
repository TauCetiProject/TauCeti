/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import TauCeti.Order.Filter.AtTopBot

/-!
# A refined Arzelà–Ascoli theorem for maps with an asymptotic modulus

Let `v k : T → X` be a sequence of maps from a separable topological space `T` to an extended
metric space `X`, or more generally a weak extended metric space. The maps need not be
continuous: they are only asked to be *asymptotically* equicontinuous, in the sense that

`limsup_k d(v k s, v k t) ≤ ω s t`

for a function `ω` with `ω t s → 0` as `s → t`. The values are compared through an auxiliary
convergence `y_n ⇀ y` on `X`, given by filters `l y`, which may be weaker than that of the metric
but for which the distance is jointly lower semicontinuous. If the values at each time lie in a
set that is relatively sequentially compact for `⇀`, then a subsequence of the maps converges
pointwise for `⇀` to a map `u` with `d(u s, u t) ≤ ω s t`
(`TauCeti.tendsto_subseq_of_limsup_edist_le`).

This is the compactness theorem behind the convergence of the minimizing movement scheme. The
piecewise constant interpolants of the scheme jump at every time step, so they are not
equicontinuous, but the jumps vanish as the time step tends to zero. In the Wasserstein space the
auxiliary convergence is narrow convergence. Relative narrow compactness of bounded energy
sublevels is then a hypothesis on the energy and the underlying space; it holds, for instance,
over a proper underlying space, where bounded sets are tight, although they need not be
relatively compact for the metric.

The proof extracts, by a diagonal argument, a subsequence converging at the points of a countable
dense set. At any other time `t`, two limits of further subsequences are both within `ω t s` of
the limit at every point `s` of the dense set, so they coincide, and the whole subsequence
converges.

## Main results

* `TauCeti.tendsto_subseq_of_limsup_edist_le`: the refined Arzelà–Ascoli theorem.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Proposition 3.3.1.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace TauCeti

variable {T X : Type*} [TopologicalSpace T] [TopologicalSpace X] [WeakEMetricSpace X]
  {l : X → Filter X}

/-- **A refined Arzelà–Ascoli theorem** (Ambrosio–Gigli–Savaré, Proposition 3.3.1). Let `l y` be
the filter of an auxiliary convergence `y_n ⇀ y` on a weak extended metric space `X`, for which
the distance is jointly sequentially lower semicontinuous. The topology of `X` need not be
induced by its extended distance; the auxiliary convergence is specified only by `l`. Let
`v k : T → X` be maps on a separable space `T` such that

* at each time `t`, the values `v k t` lie in a set `K t` in which every sequence has a
  `⇀`-convergent subsequence;
* `limsup_k d(v k s, v k t) ≤ ω s t`, where `ω t s → 0` as `s → t`.

Then a subsequence `v (ψ n)` converges pointwise for `⇀` to a map `u : T → X` with
`d(u s, u t) ≤ ω s t`. The maps `v k` need not be continuous. -/
theorem tendsto_subseq_of_limsup_edist_le [TopologicalSpace.SeparableSpace T]
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    {v : ℕ → T → X} {K : T → Set X} (hvK : ∀ k t, v k t ∈ K t)
    (hK : ∀ t ⦃w : ℕ → X⦄, (∀ n, w n ∈ K t) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (w ∘ ψ) atTop (l y))
    {ω : T → T → ℝ≥0∞} (hvω : ∀ s t, limsup (fun k ↦ edist (v k s) (v k t)) atTop ≤ ω s t)
    (hω : ∀ t, Tendsto (ω t) (𝓝 t) (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ u : T → X,
      (∀ t, Tendsto (fun n ↦ v (ψ n) t) atTop (l (u t))) ∧ ∀ s t, edist (u s) (u t) ≤ ω s t := by
  -- Limits at two times along a common subsequence are within `ω` of each other.
  have hlim : ∀ ⦃ψ : ℕ → ℕ⦄, Tendsto ψ atTop atTop → ∀ ⦃s t : T⦄ ⦃y z : X⦄,
      Tendsto (fun n ↦ v (ψ n) s) atTop (l y) → Tendsto (fun n ↦ v (ψ n) t) atTop (l z) →
      edist y z ≤ ω s t := fun ψ hψ s t _ _ hy hz ↦
    (hd hy hz).trans <| le_trans liminf_le_limsup <|
      (hψ.limsup_comp_le_limsup (u := fun k ↦ edist (v k s) (v k t))).trans (hvω s t)
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨id, strictMono_id, isEmptyElim, isEmptyElim, isEmptyElim⟩
  -- A subsequence `Ψ` along which the values at the points `e j` of a dense set converge.
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense T
  obtain ⟨e, rfl⟩ := hDc.exists_eq_range hD.nonempty
  obtain ⟨Ψ, hΨ, hconv⟩ := extraction_forall_exists_tendsto (l := l) (x := fun j k ↦ v k (e j))
    fun j ψ _ ↦ hK (e j) (w := fun n ↦ v (ψ n) (e j)) fun n ↦ hvK _ _
  choose y hy using hconv
  -- At every time, two limits along subsequences of `Ψ` are within `2 ω t (e j)` of each other
  -- for every `j`, so they coincide.
  have huniq : ∀ t ⦃ψ₁ ψ₂ : ℕ → ℕ⦄, Tendsto ψ₁ atTop atTop → Tendsto ψ₂ atTop atTop →
      ∀ ⦃z₁ z₂ : X⦄, Tendsto (fun n ↦ v (Ψ (ψ₁ n)) t) atTop (l z₁) →
        Tendsto (fun n ↦ v (Ψ (ψ₂ n)) t) atTop (l z₂) → z₁ = z₂ := by
    intro t ψ₁ ψ₂ h₁ h₂ z₁ z₂ hz₁ hz₂
    have hΨ₁ := hΨ.tendsto_atTop.comp h₁
    have hΨ₂ := hΨ.tendsto_atTop.comp h₂
    have hj j : edist z₁ z₂ ≤ ω t (e j) + ω t (e j) := by
      refine (edist_triangle _ (y j) _).trans (add_le_add (hlim hΨ₁ hz₁ ((hy j).comp h₁)) ?_)
      rw [edist_comm]
      exact hlim hΨ₂ hz₂ ((hy j).comp h₂)
    apply edist_le_zero.1
    have hbound : ∃ᶠ s in 𝓝 t, edist z₁ z₂ ≤ ω t s + ω t s :=
      (mem_closure_iff_frequently.1 (hD t)).mono <| by
        rintro _ ⟨j, rfl⟩
        exact hj j
    simpa using ge_of_tendsto_of_frequently ((hω t).add (hω t)) hbound
  -- The limit `u t` along some subsequence of `Ψ` is the limit along `Ψ` itself.
  choose u ψ' hψ' hu using fun t ↦ hK t (w := fun n ↦ v (Ψ n) t) fun n ↦ hvK _ _
  have htend t : Tendsto (fun n ↦ v (Ψ n) t) atTop (l (u t)) :=
    tendsto_of_subseq_tendsto fun ns hns ↦ by
      obtain ⟨z, ms, hms, hz⟩ := hK t (w := fun n ↦ v (Ψ (ns n)) t) fun n ↦ hvK _ _
      refine ⟨ms, ?_⟩
      rwa [huniq t (hns.comp hms.tendsto_atTop) (hψ' t).tendsto_atTop hz (hu t)] at hz
  exact ⟨Ψ, hΨ, u, htend, fun s t ↦ hlim hΨ.tendsto_atTop (htend s) (htend t)⟩

end TauCeti
