/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.EMetricSpace.BoundedVariation

import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The `r`-variation of a function

For a function `f : α → E` from a linear order to a space with an extended distance, and an
exponent `r : ℝ≥0∞`, the `r`-variation `rEVariationOn r f s` of `f` on a set `s` is

* for `0 < r < ∞`, the supremum over finite monotone sequences `u` in `s` of
  `(∑ i < n, edist (f (u (i + 1))) (f (u i)) ^ r) ^ r⁻¹`;
* for `r = ∞`, the oscillation `⨆ x y ∈ s, edist (f x) (f y)`;
* for `r = 0`, the supremum over monotone sequences in `s` of the number of jumps of `f`.

It takes values in `ℝ≥0∞`, so that it is defined for every function. At `r = 1` it is Mathlib's
total variation `eVariationOn`. This is the `p`-variation of rough path theory
(Lyons–Caruana–Lévy, *Differential Equations Driven by Rough Paths*, Definition 1.5, p. 4).

## Main definitions and results

* `TauCeti.rEVariationOn r f s`: the `r`-variation of `f` on `s`.
* `TauCeti.rEVariationOn_zero`, `TauCeti.rEVariationOn_top`,
  `TauCeti.rEVariationOn_of_ne_zero_of_ne_top`: the three cases of the definition.
* `TauCeti.rEVariationOn.sum_le`: each `ℓ^r` sum of increments along a monotone sequence in `s`
  is bounded by the `r`-variation; `TauCeti.rEVariationOn_le_iff` is the converse bound.
* `TauCeti.rEVariationOn.mono`: the `r`-variation is monotone in the set.
* `TauCeti.rEVariationOn_one`: the `1`-variation is `eVariationOn`.
* `TauCeti.rEVariationOn_anti`: the `r`-variation is antitone in `r ∈ (0, ∞)`
  (Lyons–Caruana–Lévy, Lemma 1.6, pp. 4–5), and so
  `TauCeti.rEVariationOn_le_eVariationOn`: for `1 ≤ r` it is at most the total variation.

## Implementation notes

The definition and the results up to `rEVariationOn_anti` need only an extended distance
`[EDist E]` on `E`; the comparison with `eVariationOn` takes Mathlib's
`[WeakPseudoEMetricSpace E]`.
-/

public section

open scoped ENNReal

namespace TauCeti

section EDist

variable {α E : Type*} [LinearOrder α] [EDist E]

/-- The `r`-variation of `f` on `s`, in `ℝ≥0∞`. For `0 < r < ∞` it is the supremum over finite
monotone sequences `u` in `s` of `(∑ i < n, edist (f (u (i + 1))) (f (u i)) ^ r) ^ r⁻¹`; at
`r = ⊤` it is the oscillation `⨆ x y ∈ s, edist (f x) (f y)`, and at `r = 0` the supremum over
monotone sequences in `s` of the number of indices at which `f` jumps. -/
noncomputable def rEVariationOn (r : ℝ≥0∞) (f : α → E) (s : Set α) : ℝ≥0∞ :=
  if r = 0 then ⨆ p : { t : ℕ → α // Monotone t ∧ ∀ i, t i ∈ s },
    ((Function.support fun i : ℕ ↦ edist (f (p.val (i + 1))) (f (p.val i))).encard : ℝ≥0∞)
  else if r = ⊤ then ⨆ j : s × s, edist (f j.1) (f j.2)
  else ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    (∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) ^ r.toReal) ^ r.toReal⁻¹

/-- The `0`-variation is the supremum over monotone sequences in `s` of the number of jumps. -/
theorem rEVariationOn_zero (f : α → E) (s : Set α) :
    rEVariationOn 0 f s = ⨆ p : { t : ℕ → α // Monotone t ∧ ∀ i, t i ∈ s },
      ((Function.support fun i : ℕ ↦ edist (f (p.val (i + 1))) (f (p.val i))).encard : ℝ≥0∞) := by
  simp [rEVariationOn]

/-- The `⊤`-variation is the oscillation `⨆ x y ∈ s, edist (f x) (f y)`. -/
theorem rEVariationOn_top (f : α → E) (s : Set α) :
    rEVariationOn ⊤ f s = ⨆ j : s × s, edist (f j.1) (f j.2) := by
  simp [rEVariationOn]

/-- For `0 < r < ∞`, the `r`-variation is the supremum over finite monotone sequences `u` in `s`
of the `ℓ^r` norm of the increments of `f` along `u`. -/
theorem rEVariationOn_of_ne_zero_of_ne_top {r : ℝ≥0∞} (hr : r ≠ 0) (hr' : r ≠ ⊤) (f : α → E)
    (s : Set α) :
    rEVariationOn r f s = ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
      (∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) ^ r.toReal) ^
        r.toReal⁻¹ := by
  simp [rEVariationOn, hr, hr']

/-- For `0 < r < ∞`, the `ℓ^r` norm of the increments of `f` along a monotone sequence in `s`
is at most the `r`-variation of `f` on `s`. -/
theorem rEVariationOn.sum_le {r : ℝ≥0∞} (hr : r ≠ 0) (hr' : r ≠ ⊤) (f : α → E) {s : Set α}
    (n : ℕ) {u : ℕ → α} (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ r.toReal) ^ r.toReal⁻¹ ≤
      rEVariationOn r f s := by
  rw [rEVariationOn_of_ne_zero_of_ne_top hr hr']
  exact le_iSup_of_le (n, ⟨u, hu, us⟩) le_rfl

/-- For `0 < r < ∞`, the `r`-variation of `f` on `s` is at most `C` if and only if the `ℓ^r`
norm of the increments of `f` along every finite monotone sequence in `s` is at most `C`. -/
theorem rEVariationOn_le_iff {r : ℝ≥0∞} (hr : r ≠ 0) (hr' : r ≠ ⊤) {f : α → E} {s : Set α}
    {C : ℝ≥0∞} :
    rEVariationOn r f s ≤ C ↔ ∀ (n : ℕ) (u : ℕ → α), Monotone u → (∀ i, u i ∈ s) →
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ^ r.toReal) ^ r.toReal⁻¹ ≤ C := by
  rw [rEVariationOn_of_ne_zero_of_ne_top hr hr', iSup_le_iff]
  exact ⟨fun h n u hu us ↦ h (n, ⟨u, hu, us⟩),
    fun h p ↦ h p.1 p.2.val p.2.property.1 p.2.property.2⟩

/-- The `r`-variation is monotone in the set. -/
theorem rEVariationOn.mono (r : ℝ≥0∞) (f : α → E) {s t : Set α} (hst : t ⊆ s) :
    rEVariationOn r f t ≤ rEVariationOn r f s := by
  unfold rEVariationOn
  split_ifs
  · exact iSup_le fun p ↦ le_iSup_of_le ⟨p.val, p.property.1, fun i ↦ hst (p.property.2 i)⟩ le_rfl
  · exact iSup_le fun j ↦
      le_iSup_of_le (⟨⟨j.1, hst j.1.property⟩, ⟨j.2, hst j.2.property⟩⟩ : s × s) le_rfl
  · exact iSup_le fun p ↦
      le_iSup_of_le (p.1, ⟨p.2.val, p.2.property.1, fun i ↦ hst (p.2.property.2 i)⟩) le_rfl

/-- **Monotonicity in the exponent.** For `0 < r ≤ r' < ∞`, the `r'`-variation is at most the
`r`-variation (Lyons–Caruana–Lévy, Lemma 1.6, pp. 4–5). -/
theorem rEVariationOn_anti {r r' : ℝ≥0∞} (hr : r ≠ 0) (hrr' : r ≤ r') (hr' : r' ≠ ⊤)
    (f : α → E) (s : Set α) : rEVariationOn r' f s ≤ rEVariationOn r f s := by
  have hr'0 : r' ≠ 0 := (pos_iff_ne_zero.2 hr |>.trans_le hrr').ne'
  have hrtop : r ≠ ⊤ := ne_top_of_le_ne_top hr' hrr'
  rw [rEVariationOn_le_iff hr'0 hr']
  intro n u hu us
  -- The `ℓ^r` norm of a finite family is antitone in `r > 0`.
  have h := ENNReal.rpow_sum_rpow_le (Finset.range n)
    (fun i ↦ edist (f (u (i + 1))) (f (u i))) (ENNReal.toReal_pos hr hrtop)
    (ENNReal.toReal_mono hr' hrr')
  rw [one_div, one_div] at h
  exact h.trans (rEVariationOn.sum_le hr hrtop f n hu us)

end EDist

section WeakPseudoEMetricSpace

variable {α E : Type*} [LinearOrder α] [TopologicalSpace E] [WeakPseudoEMetricSpace E]

/-- The `1`-variation is Mathlib's total variation `eVariationOn`. -/
@[simp]
theorem rEVariationOn_one (f : α → E) (s : Set α) : rEVariationOn 1 f s = eVariationOn f s := by
  simp [rEVariationOn, eVariationOn]

/-- For `1 ≤ r`, the `r`-variation is at most the total variation `eVariationOn`. -/
theorem rEVariationOn_le_eVariationOn {r : ℝ≥0∞} (hr : 1 ≤ r) (f : α → E) (s : Set α) :
    rEVariationOn r f s ≤ eVariationOn f s := by
  rcases eq_or_ne r ⊤ with rfl | hr'
  · rw [rEVariationOn_top]
    exact iSup_le fun j ↦ eVariationOn.edist_le f j.1.property j.2.property
  · exact rEVariationOn_one f s ▸ rEVariationOn_anti one_ne_zero hr hr' f s

end WeakPseudoEMetricSpace

end TauCeti
