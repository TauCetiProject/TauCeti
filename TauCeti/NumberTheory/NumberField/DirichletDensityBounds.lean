/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# One-sided bounds for Dirichlet density

For a set `S` of nonzero prime ideals of a number field, Mathlib's
`NumberField.Set.HasDirichletDensity S δ` says that the ratio

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s`

tends to `δ` as `s` approaches `1` from the right.  Squeeze arguments often produce the two
sides of this limit separately.  This file records those one-sided conclusions as
`NumberField.Set.IsLowerDirichletDensityBound S δ` and
`NumberField.Set.IsUpperDirichletDensityBound S δ`.

The predicates use eventual epsilon inequalities, rather than assigning junk-valued lower and
upper densities.  They are monotone in the proposed bound, and a common lower and upper bound
forces the defining ratio to converge.  A lower bound is always at most an upper bound; this
comparison also gives the natural interval restrictions on one-sided bounds.

## Main results

* `NumberField.Set.isLowerDirichletDensityBound_of_tendsto` and
  `NumberField.Set.isUpperDirichletDensityBound_of_tendsto`: convergence of the defining
  ratio supplies its one-sided bounds.
* `NumberField.Set.IsLowerDirichletDensityBound.le_of_isUpperDirichletDensityBound`:
  every lower bound is at most every upper bound.
* `NumberField.Set.tendsto_primeIdealZetaSum_div_of_upperBound_of_lowerBound`: matching
  one-sided bounds force convergence of the defining ratio.
* `NumberField.Set.tendsto_primeIdealZetaSum_div_iff_bounds`: the resulting
  characterization of that convergence.

## References

* J.-P. Serre, *Corps locaux*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

open Filter IsDedekindDomain NumberField
open scoped Topology

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- A real number `δ` is a lower Dirichlet-density bound for `S` if, for every positive `ε`,
the ratio defining Dirichlet density is eventually strictly above `δ - ε` as `s → 1⁺`. -/
def IsLowerDirichletDensityBound
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
    δ - ε < S.primeIdealZetaSum s /
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s

/-- A real number `δ` is an upper Dirichlet-density bound for `S` if, for every positive `ε`,
the ratio defining Dirichlet density is eventually strictly below `δ + ε` as `s → 1⁺`. -/
def IsUpperDirichletDensityBound
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
    S.primeIdealZetaSum s /
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s < δ + ε

/-- Characteristic restatement of a lower Dirichlet-density bound. -/
theorem isLowerDirichletDensityBound_iff
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    IsLowerDirichletDensityBound S δ ↔
      ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
        δ - ε < S.primeIdealZetaSum s /
          NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
  Iff.rfl

/-- Characteristic restatement of an upper Dirichlet-density bound. -/
theorem isUpperDirichletDensityBound_iff
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    IsUpperDirichletDensityBound S δ ↔
      ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
        S.primeIdealZetaSum s /
          NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s < δ + ε :=
  Iff.rfl

/-- The ratio used to define Dirichlet density is nonnegative at every real parameter. -/
theorem primeIdealZetaSum_div_univ_nonneg
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    0 ≤ S.primeIdealZetaSum s /
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
  div_nonneg (S.primeIdealZetaSum_nonneg s)
    ((Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum_nonneg s)

/-- The ratio used to define Dirichlet density is at most one at every real parameter.

The proof follows `NumberField.Set.HasDirichletDensity.le_one` from
`Mathlib.NumberTheory.NumberField.DirichletDensity`. -/
theorem primeIdealZetaSum_div_univ_le_one
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    S.primeIdealZetaSum s /
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s ≤ 1 := by
  rw [NumberField.Set.primeIdealZetaSum_def, NumberField.Set.primeIdealZetaSum_def,
    tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)]
  by_cases hs : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
  · exact div_le_one_of_le₀ (hs.tsum_subtype_le _ S (fun _ ↦ by positivity))
      (tsum_nonneg fun _ ↦ by positivity)
  · grw [tsum_eq_zero_of_not_summable hs, div_zero, zero_le_one]

/-- Zero is a lower Dirichlet-density bound for every set of primes. -/
@[simp]
theorem isLowerDirichletDensityBound_zero
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsLowerDirichletDensityBound S 0 := by
  intro ε hε
  filter_upwards [] with s
  simpa only [zero_sub] using
    (neg_lt_zero.mpr hε).trans_le (primeIdealZetaSum_div_univ_nonneg S s)

/-- One is an upper Dirichlet-density bound for every set of primes. -/
@[simp]
theorem isUpperDirichletDensityBound_one
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsUpperDirichletDensityBound S 1 := by
  intro ε hε
  filter_upwards [] with s
  exact (primeIdealZetaSum_div_univ_le_one S s).trans_lt (lt_add_of_pos_right 1 hε)

/-- A lower Dirichlet-density bound remains a lower bound when its value is decreased. -/
theorem IsLowerDirichletDensityBound.mono {S : Set (HeightOneSpectrum (𝓞 K))} {δ δ' : ℝ}
    (h : IsLowerDirichletDensityBound S δ) (hδ : δ' ≤ δ) :
    IsLowerDirichletDensityBound S δ' := by
  intro ε hε
  filter_upwards [h ε hε] with s hs
  exact lt_of_le_of_lt (sub_le_sub_right hδ ε) hs

/-- An upper Dirichlet-density bound remains an upper bound when its value is increased. -/
theorem IsUpperDirichletDensityBound.mono {S : Set (HeightOneSpectrum (𝓞 K))} {δ δ' : ℝ}
    (h : IsUpperDirichletDensityBound S δ) (hδ : δ ≤ δ') :
    IsUpperDirichletDensityBound S δ' := by
  intro ε hε
  filter_upwards [h ε hε] with s hs
  exact hs.trans_le (by linarith)

/-- Convergence of the ratio defining Dirichlet density makes its limit a lower
Dirichlet-density bound. -/
theorem isLowerDirichletDensityBound_of_tendsto
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : Tendsto
      (fun s : ℝ ↦ S.primeIdealZetaSum s /
        NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 δ)) :
    IsLowerDirichletDensityBound S δ := by
  intro ε hε
  exact (tendsto_order.1 h).1 (δ - ε) (by linarith)

/-- Convergence of the ratio defining Dirichlet density makes its limit an upper
Dirichlet-density bound. -/
theorem isUpperDirichletDensityBound_of_tendsto
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : Tendsto
      (fun s : ℝ ↦ S.primeIdealZetaSum s /
        NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 δ)) :
    IsUpperDirichletDensityBound S δ := by
  intro ε hε
  exact (tendsto_order.1 h).2 (δ + ε) (by linarith)

/-- Every lower Dirichlet-density bound is at most every upper Dirichlet-density bound for the
same set of primes. -/
theorem IsLowerDirichletDensityBound.le_of_isUpperDirichletDensityBound
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ η : ℝ}
    (hlower : IsLowerDirichletDensityBound S δ)
    (hupper : IsUpperDirichletDensityBound S η) : δ ≤ η := by
  by_contra hle
  have hηδ : η < δ := lt_of_not_ge hle
  let ε := (δ - η) / 2
  have hε : 0 < ε := div_pos (sub_pos.mpr hηδ) zero_lt_two
  obtain ⟨s, hs_lower, hs_upper⟩ :=
    ((hlower ε hε).and (hupper ε hε)).exists
  have heq : δ - ε = η + ε := by
    dsimp [ε]
    ring
  rw [heq] at hs_lower
  exact (not_lt_of_ge hs_upper.le) hs_lower

/-- A lower Dirichlet-density bound cannot exceed `1`. -/
theorem IsLowerDirichletDensityBound.le_one
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : IsLowerDirichletDensityBound S δ) : δ ≤ 1 :=
  h.le_of_isUpperDirichletDensityBound (isUpperDirichletDensityBound_one S)

/-- An upper Dirichlet-density bound cannot be negative. -/
theorem IsUpperDirichletDensityBound.nonneg
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : IsUpperDirichletDensityBound S δ) : 0 ≤ δ :=
  (isLowerDirichletDensityBound_zero S).le_of_isUpperDirichletDensityBound h

/-- Matching lower and upper Dirichlet-density bounds force the defining ratio to tend to their
common value. -/
theorem tendsto_primeIdealZetaSum_div_of_upperBound_of_lowerBound
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hupper : IsUpperDirichletDensityBound S δ)
    (hlower : IsLowerDirichletDensityBound S δ) :
    Tendsto
      (fun s : ℝ ↦ S.primeIdealZetaSum s /
        NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 δ) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let ε := (δ - a) / 2
    have hε : 0 < ε := div_pos (sub_pos.mpr ha) zero_lt_two
    filter_upwards [hlower ε hε] with s hs
    have hlt : a < δ - ε := by
      dsimp [ε]
      linarith
    exact hlt.trans hs
  · intro b hb
    let ε := (b - δ) / 2
    have hε : 0 < ε := div_pos (sub_pos.mpr hb) zero_lt_two
    filter_upwards [hupper ε hε] with s hs
    have hlt : δ + ε < b := by
      dsimp [ε]
      linarith
    exact hs.trans hlt

/-- The ratio defining Dirichlet density tends to `δ` exactly when `δ` is both an upper and a
lower Dirichlet-density bound. -/
theorem tendsto_primeIdealZetaSum_div_iff_bounds
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    Tendsto
      (fun s : ℝ ↦ S.primeIdealZetaSum s /
        NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 δ) ↔
      IsUpperDirichletDensityBound S δ ∧ IsLowerDirichletDensityBound S δ :=
  ⟨fun h ↦ ⟨isUpperDirichletDensityBound_of_tendsto h,
      isLowerDirichletDensityBound_of_tendsto h⟩,
    fun h ↦ tendsto_primeIdealZetaSum_div_of_upperBound_of_lowerBound h.1 h.2⟩

end NumberField.Set
