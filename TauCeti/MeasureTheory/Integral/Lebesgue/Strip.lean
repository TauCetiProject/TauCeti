/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lebesgue integrals over a strip by exhaustion

The strip `ℝ × T` is exhausted by the increasing rectangles `[-n, n] × T`
(`TauCeti.iUnion_Icc_neg_prod`), so the integrals of a function over these rectangles increase to
its integral over the strip (`TauCeti.tendsto_setLIntegral_Icc_neg_prod`). If the lower Lebesgue
integral of an `ℝ≥0∞`-valued function over `[-n, n] × T` is `ENNReal.ofReal (F(n) - F(-n))` for a
real function `F` with limits `A₁` at `-∞` and `A₂` at `∞`, then its integral over the whole strip
is `ENNReal.ofReal (A₂ - A₁)` (`TauCeti.setLIntegral_univ_prod_eq_ofReal_of_tendsto`). Since
`ENNReal.ofReal` truncates at zero, this is `A₂ - A₁` when `A₁ ≤ A₂` and `0` otherwise.

This is the passage from the energy identity on finite rectangles to the energy of a
holomorphic strip or a Floer cylinder, whose energy is the difference of the limiting actions at
its two ends.

The strip is also the union of the disjoint translates of a period rectangle
`(a, a + c] × T`. A function on the strip that is periodic in the first variable has the same
integral over each translate, so if its integral over the strip is finite, then its integral over
each period rectangle vanishes, and hence so does its integral over the whole strip
(`TauCeti.setLIntegral_univ_prod_eq_zero_of_periodic`). For the energy density of a Floer cylinder
this says that a finite-energy cylinder invariant under a nontrivial translation has zero
energy.
-/

public section

namespace TauCeti

open Function MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The rectangles `[-n, n] × T` increase with `n`. -/
theorem monotone_Icc_neg_prod {β : Type*} (T : Set β) :
    Monotone fun n : ℕ ↦ Icc (-(n : ℝ)) n ×ˢ T := fun _ _ hmn ↦
  prod_mono (Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)) le_rfl

/-- The rectangles `[-n, n] × T` exhaust the strip `ℝ × T`. -/
theorem iUnion_Icc_neg_prod {β : Type*} (T : Set β) :
    ⋃ n : ℕ, Icc (-(n : ℝ)) n ×ˢ T = (univ : Set ℝ) ×ˢ T := by
  refine (iUnion_subset fun n ↦ prod_mono (subset_univ _) le_rfl).antisymm fun z hz ↦ ?_
  obtain ⟨n, hn⟩ := exists_nat_ge |z.1|
  exact mem_iUnion.mpr ⟨n, ⟨abs_le.mp hn, hz.2⟩⟩

/-- The integrals of `f` over the rectangles `[-n, n] × T` increase to its integral over the
strip `ℝ × T`. -/
theorem tendsto_setLIntegral_Icc_neg_prod {β : Type*} [MeasurableSpace β]
    (μ : Measure (ℝ × β)) (T : Set β) (f : ℝ × β → ℝ≥0∞) :
    Tendsto (fun n : ℕ ↦ ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ T, f z ∂μ) atTop
      (𝓝 (∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ)) := by
  rw [← iUnion_Icc_neg_prod, setLIntegral_iUnion_of_directed _
    (monotone_Icc_neg_prod T).directed_le]
  exact tendsto_atTop_iSup fun _ _ hmn ↦
    lintegral_mono' (Measure.restrict_mono (monotone_Icc_neg_prod T hmn) le_rfl) le_rfl

/-- **Integrals over a strip by exhaustion.** If the integral of `f` over each rectangle
`[-n, n] × T` is `ENNReal.ofReal (F(n) - F(-n))`, where `F` tends to `A₁` at `-∞` and to `A₂` at
`∞`, then the integral of `f` over the strip `ℝ × T` is `ENNReal.ofReal (A₂ - A₁)`, that is
`A₂ - A₁` truncated at zero. -/
theorem setLIntegral_univ_prod_eq_ofReal_of_tendsto {β : Type*} [MeasurableSpace β]
    {μ : Measure (ℝ × β)} {T : Set β} {f : ℝ × β → ℝ≥0∞} {F : ℝ → ℝ} {A₁ A₂ : ℝ}
    (hE : ∀ n : ℕ, ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ T, f z ∂μ = ENNReal.ofReal (F n - F (-n)))
    (hbot : Tendsto F atBot (𝓝 A₁)) (htop : Tendsto F atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ = ENNReal.ofReal (A₂ - A₁) := by
  refine tendsto_nhds_unique (tendsto_setLIntegral_Icc_neg_prod μ T f) ?_
  simp only [hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((htop.comp tendsto_natCast_atTop_atTop).sub
      (hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)))

/-- A function on the strip `ℝ × T`, periodic in the first variable with period `c` and with
finite integral over the strip, has zero integral over each period rectangle `(a, a + c] × T`:
the disjoint translates of the rectangle inside the strip all have the same integral. -/
private theorem setLIntegral_Ioc_prod_eq_zero_of_periodic {β : Type*} [MeasurableSpace β]
    {μ : Measure (ℝ × β)} {T : Set β} (hT : MeasurableSet T) {f : ℝ × β → ℝ≥0∞} {c : ℝ}
    (hμ : MeasurePreserving (fun z : ℝ × β ↦ (z.1 + c, z.2)) μ μ)
    (hf : ∀ s, ∀ t ∈ T, f (s + c, t) = f (s, t))
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ ≠ ∞) (a : ℝ) :
    ∫⁻ z in Ioc a (a + c) ×ˢ T, f z ∂μ = 0 := by
  set S : ℕ → Set (ℝ × β) := fun n ↦ Ioc (a + n * c) (a + n * c + c) ×ˢ T
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_Ioc.prod hT
  -- The translation carries each rectangle onto the next and preserves the integrand there.
  have hshift : MeasurableEmbedding fun z : ℝ × β ↦ (z.1 + c, z.2) :=
    (measurableEmbedding_addRight c).prodMap MeasurableEmbedding.id
  have hstep (n : ℕ) : ∫⁻ z in S (n + 1), f z ∂μ = ∫⁻ z in S n, f z ∂μ := by
    rw [← hμ.setLIntegral_comp_preimage_emb hshift]
    have hpre : (fun z : ℝ × β ↦ (z.1 + c, z.2)) ⁻¹' S (n + 1) = S n := by
      ext z
      simp only [S, mem_preimage, mem_prod, mem_Ioc, Nat.cast_add, Nat.cast_one]
      constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> refine ⟨⟨?_, ?_⟩, h₃⟩ <;> linarith
    rw [hpre]
    exact setLIntegral_congr_fun (hS n) fun z hz ↦ hf z.1 z.2 hz.2
  have hconst (n : ℕ) : ∫⁻ z in S n, f z ∂μ = ∫⁻ z in S 0, f z ∂μ := by
    induction n with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
  -- The rectangles are disjoint subsets of the strip.
  have hdisj : Pairwise (Disjoint on S) := by
    intro m n hmn
    refine disjoint_prod.2 (Or.inl ?_)
    have h := pairwise_disjoint_Ioc_add_zsmul a c (Nat.cast_injective.ne hmn)
    simpa only [Function.onFun, natCast_zsmul, add_smul, one_smul, nsmul_eq_mul, ← add_assoc,
      Int.cast_natCast] using h
  have hle : ∑' n, ∫⁻ z in S n, f z ∂μ ≤ ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ := by
    rw [← lintegral_iUnion hS hdisj]
    exact lintegral_mono_set (iUnion_subset fun n ↦ prod_mono (subset_univ _) le_rfl)
  simp only [hconst] at hle
  have h0 : ∫⁻ z in S 0, f z ∂μ = 0 := by
    by_contra h
    exact hfin (top_le_iff.1 ((ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) h) ▸ hle))
  simpa [S] using h0

/-- **Periodic functions on a strip.** Let `μ` be a measure on `ℝ × β` invariant under the
translation `(s, t) ↦ (s + c, t)` for some `c > 0`, and let `f` be periodic in `s` with period `c`
on the strip `ℝ × T`. If the integral of `f` over the strip is finite, then it is zero. No
measurability of `f` is assumed. -/
theorem setLIntegral_univ_prod_eq_zero_of_periodic {β : Type*} [MeasurableSpace β]
    {μ : Measure (ℝ × β)} {T : Set β} (hT : MeasurableSet T) {f : ℝ × β → ℝ≥0∞} {c : ℝ}
    (hc : 0 < c) (hμ : MeasurePreserving (fun z : ℝ × β ↦ (z.1 + c, z.2)) μ μ)
    (hf : ∀ s, ∀ t ∈ T, f (s + c, t) = f (s, t))
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ ≠ ∞) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ = 0 := by
  -- The strip is the union of the period rectangles `(n c, (n + 1) c] × T`.
  have hunion : (univ : Set ℝ) ×ˢ T = ⋃ n : ℤ, Ioc (n • c) (n • c + c) ×ˢ T := by
    rw [← iUnion_prod_const]
    simpa only [zero_add, add_smul, one_smul] using
      congrArg (· ×ˢ T) (iUnion_Ioc_add_zsmul hc 0).symm
  refine le_antisymm ?_ zero_le
  rw [hunion]
  refine (lintegral_iUnion_le _ _).trans (le_of_eq ?_)
  simp [setLIntegral_Ioc_prod_eq_zero_of_periodic hT hμ hf hfin]

end TauCeti
