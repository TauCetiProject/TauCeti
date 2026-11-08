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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.MeasureTheory.Integral.Lebesgue.Exhaustion

/-!
# Lebesgue integrals over a strip by exhaustion

The strip `ℝ × T` is exhausted by the increasing rectangles `[-n, n] × T`
(`TauCeti.iUnion_Icc_neg_prod`), so the integrals of a function over these rectangles increase to
its integral over the strip (`TauCeti.tendsto_setLIntegral_Icc_neg_prod`). If the lower Lebesgue
integral of an `ℝ≥0∞`-valued function over `[-n, n] × T` is `ENNReal.ofReal (F(n) - F(-n))` for a
real function `F` with limits `A₁` at `-∞` and `A₂` at `∞`, then its integral over the whole strip
is `ENNReal.ofReal (A₂ - A₁)` (`TauCeti.setLIntegral_univ_prod_eq_ofReal_of_tendsto`). Since
`ENNReal.ofReal` truncates at zero, this is `A₂ - A₁` when `A₁ ≤ A₂` and `0` otherwise.
Likewise the half-strip `[b, ∞) × T` is exhausted by the rectangles `[b, b + n] × T`: if the
integral over `[b, b + n] × T` is `ENNReal.ofReal (F(b + n) - F(b))` and `F` tends to `L` at `∞`,
then the integral over the half-strip is `ENNReal.ofReal (L - F(b))`
(`TauCeti.setLIntegral_Ici_prod_eq_ofReal_of_tendsto`).

This is the passage from the energy identity on finite rectangles to the energy of a
holomorphic strip or a Floer cylinder, whose energy is the difference of the limiting actions at
its two ends, and of a Floer half-cylinder.

The strip is also the union of the disjoint translates of a period rectangle
`(a, a + c] × T`. A function on the strip that is periodic in the first variable has the same
integral over each translate, so if its integral over the strip is finite, then its integral over
each period rectangle vanishes, and hence so does its integral over the whole strip
(`TauCeti.setLIntegral_univ_prod_eq_zero_of_periodic`). For the energy density of a Floer cylinder
this says that a finite-energy cylinder invariant under a nontrivial translation has zero
energy.

Finally, a function with finite integral over a set `E` has small integral over the parts of `E`
far out along the strip: its integrals over sets that eventually lie in `E` and outside every band
`|z.1| < R` tend to zero (`TauCeti.tendsto_setLIntegral_of_eventually_subset`). Applied to
windows `[a + s_k, b + s_k] × T` with `|s_k| → ∞`, this says that a half-cylinder of finite energy
carries less and less energy over its translated windows, since such windows eventually lie
outside every band (`TauCeti.eventually_Icc_add_prod_subset_inter`).
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
  rw [← iUnion_Icc_neg_prod]
  exact tendsto_setLIntegral_of_monotone (monotone_Icc_neg_prod T)

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

/-- **Integrals over a half-strip by exhaustion.** If the integral of `f` over each rectangle
`[b, b + n] × T` is `ENNReal.ofReal (F(b + n) - F(b))`, where `F` tends to `L` at `∞`, then the
integral of `f` over the half-strip `[b, ∞) × T` is `ENNReal.ofReal (L - F(b))`, that is
`L - F(b)` truncated at zero. -/
theorem setLIntegral_Ici_prod_eq_ofReal_of_tendsto {β : Type*} [MeasurableSpace β]
    {μ : Measure (ℝ × β)} {T : Set β} {f : ℝ × β → ℝ≥0∞} {F : ℝ → ℝ} {b L : ℝ}
    (hE : ∀ n : ℕ, ∫⁻ z in Icc b (b + n) ×ˢ T, f z ∂μ = ENNReal.ofReal (F (b + n) - F b))
    (htop : Tendsto F atTop (𝓝 L)) :
    ∫⁻ z in Ici b ×ˢ T, f z ∂μ = ENNReal.ofReal (L - F b) := by
  set R : ℕ → Set (ℝ × β) := fun n ↦ Icc b (b + n) ×ˢ T
  have hmono : Monotone R := fun m n hmn ↦
    prod_mono (Icc_subset_Icc le_rfl (by simpa using hmn)) le_rfl
  have hunion : ⋃ n, R n = Ici b ×ˢ T := by
    refine (iUnion_subset fun n ↦ Set.prod_mono Icc_subset_Ici_self le_rfl).antisymm fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (z.1 - b)
    exact mem_iUnion.2 ⟨n, ⟨hz.1, by linarith⟩, hz.2⟩
  -- The integrals over the rectangles increase to the integral over the half-strip.
  have hlim := tendsto_setLIntegral_of_monotone (μ := μ) (f := f) hmono
  rw [hunion] at hlim
  refine tendsto_nhds_unique hlim ?_
  simp only [R, hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((htop.comp (tendsto_atTop_add_const_left _ b tendsto_natCast_atTop_atTop)).sub_const _)

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

/-- If `|s_i| → ∞` and the translated window `[a + s_i, b + s_i] × T` eventually lies in `E`, then
it eventually lies in `E` and outside the band `|z.1| < R`, for every `R`. These windows are thus
sets to which `TauCeti.tendsto_setLIntegral_of_eventually_subset` applies. -/
theorem eventually_Icc_add_prod_subset_inter {ι β : Type*} {l : Filter ι} {s : ι → ℝ}
    {T : Set β} {E : Set (ℝ × β)} {a b : ℝ} (hs : Tendsto s l (cocompact ℝ))
    (hW : ∀ᶠ i in l, Icc (a + s i) (b + s i) ×ˢ T ⊆ E) (R : ℝ) :
    ∀ᶠ i in l, Icc (a + s i) (b + s i) ×ˢ T ⊆ E ∩ {z | R ≤ |z.1|} := by
  filter_upwards [hW,
    hs.eventually (isCompact_closedBall (0 : ℝ) (R + |a| + |b|)).compl_mem_cocompact]
    with i hi hsi z hz
  refine ⟨hi hz, ?_⟩
  have hsi' : R + |a| + |b| < |s i| := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hsi
  have h₁ : |z.1 - s i| ≤ |a| + |b| := by
    obtain ⟨⟨h₁, h₂⟩, -⟩ := hz
    refine abs_le.2 ⟨?_, ?_⟩ <;>
      linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have h₂ : |s i| ≤ |z.1| + |z.1 - s i| := by
    simpa using abs_sub z.1 (z.1 - s i)
  exact (by linarith : R ≤ |z.1|)

/-- **Integrals over sets escaping along the strip.** If `f` has finite integral over `E`, then its
integrals over sets `A i` that eventually lie in `E` and outside every band `|z.1| < R` tend to
zero. For the energy density of a half-cylinder of finite energy, this says that the energy over
a window translated towards the end tends to zero. No measurability of `f`, `E` or `A i` is
assumed. -/
theorem tendsto_setLIntegral_of_eventually_subset {ι β : Type*} [MeasurableSpace β]
    {μ : Measure (ℝ × β)} {E : Set (ℝ × β)} {f : ℝ × β → ℝ≥0∞}
    (hE : ∫⁻ z in E, f z ∂μ ≠ ∞) {l : Filter ι} {A : ι → Set (ℝ × β)}
    (hA : ∀ R : ℝ, ∀ᶠ i in l, A i ⊆ E ∩ {z | R ≤ |z.1|}) :
    Tendsto (fun i ↦ ∫⁻ z in A i, f z ∂μ) l (𝓝 0) := by
  set ν := (μ.restrict E).withDensity f
  set C : ℕ → Set (ℝ × β) := fun n ↦ {z | (n : ℝ) ≤ |z.1|}
  have hC (n : ℕ) : MeasurableSet (C n) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp measurable_fst)
  have hν (n : ℕ) : ν (C n) = ∫⁻ z in C n ∩ E, f z ∂μ := by
    rw [withDensity_apply _ (hC n), Measure.restrict_restrict (hC n)]
  -- The integrals over `E` outside the bands `|z.1| < n` decrease to zero.
  have hlim : Tendsto (fun n ↦ ν (C n)) atTop (𝓝 0) := by
    have hanti : Antitone C := fun m n hmn z (hz : (n : ℝ) ≤ |z.1|) ↦
      show (m : ℝ) ≤ |z.1| from le_trans (by exact_mod_cast hmn) hz
    have hfin : ν (C 0) ≠ ∞ := by
      rw [hν]
      exact ne_top_of_le_ne_top hE (lintegral_mono_set inter_subset_right)
    have hempty : ⋂ n, C n = ∅ := by
      refine eq_empty_of_forall_notMem fun z hz ↦ ?_
      obtain ⟨n, hn⟩ := exists_nat_gt |z.1|
      exact (mem_iInter.1 hz n).not_gt hn
    have h := tendsto_measure_iInter_atTop (fun n ↦ (hC n).nullMeasurableSet) hanti ⟨0, hfin⟩
    rwa [hempty, measure_empty] at h
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hlim ε hε)
  filter_upwards [hA n] with i hi
  calc ∫⁻ z in A i, f z ∂μ ≤ ∫⁻ z in C n ∩ E, f z ∂μ :=
        lintegral_mono_set fun z hz ↦ ⟨(hi hz).2, (hi hz).1⟩
    _ = ν (C n) := (hν n).symm
    _ ≤ ε := hn n le_rfl

end TauCeti
