/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Statistics.Experiments.Density

/-!
# Countable mixtures and the Halmos–Savage lemma

For a family of measures `P : Θ → Measure X` and a sequence of parameters `θs : ℕ → Θ`, the
countable mixture `countableMixture P θs` is `∑ₙ 2^{-(n+1)} • P (θs n)`. Its weights
`mixtureWeight n = 2^{-(n+1)}` are positive and sum to `1`, so a mixture of probability measures
is a probability measure and a set is null for the mixture iff it is null for every component.

The **Halmos–Savage lemma** says that a family dominated by an s-finite (in particular, a
σ-finite) measure is dominated by one of its own countable mixtures. This is the form of
domination used throughout statistics: the factorization theorem and the theory of sufficiency
work with a dominating measure that is itself a mixture of the laws of the model.

## Main definitions

* `TauCeti.mixtureWeight n`: the weight `2^{-(n+1)}`.
* `TauCeti.countableMixture P θs`: the mixture `∑ₙ mixtureWeight n • P (θs n)`.

## Main results

* `TauCeti.tsum_mixtureWeight`: the weights sum to `1`.
* `TauCeti.countableMixture_apply_eq_zero_iff`: a set is null for a mixture iff it is null for
  every component.
* `TauCeti.map_countableMixture`, `TauCeti.countableMixture_compProd`,
  `TauCeti.map_prodMk_countableMixture_eq_compProd`: pushforwards, composition products, and
  disintegrations commute with countable mixtures.
* `TauCeti.countableMixture_eq_withDensity`, `TauCeti.countableMixture_eq_withDensity_mul`,
  `TauCeti.HasDensity.countableMixture`: a mixture of measures with densities has the mixed
  density.
* `TauCeti.exists_absolutelyContinuous_countableMixture`: the Halmos–Savage lemma.

## References

* P. R. Halmos and L. J. Savage, *Application of the Radon–Nikodym theorem to the theory of
  sufficient statistics*, Ann. Math. Statist. 20 (1949), 225–241.
* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Lemma 1.2.1.
* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorem A.78.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

variable {Θ X : Type*} [MeasurableSpace X] {P : Θ → Measure X} {θs : ℕ → Θ} {μ : Measure X}

/-- The weight `2^{-(n+1)}` of the `n`-th component of a countable mixture. -/
def mixtureWeight (n : ℕ) : ℝ≥0∞ := (2 ^ (n + 1))⁻¹

theorem mixtureWeight_def (n : ℕ) : mixtureWeight n = (2 ^ (n + 1))⁻¹ := (rfl)

@[simp]
theorem mixtureWeight_ne_zero (n : ℕ) : mixtureWeight n ≠ 0 := by
  simp [mixtureWeight_def]

@[simp]
theorem mixtureWeight_ne_top (n : ℕ) : mixtureWeight n ≠ ∞ := by
  simp [mixtureWeight_def]

/-- The mixture weights sum to `1`. -/
@[simp]
theorem tsum_mixtureWeight : ∑' n, mixtureWeight n = 1 := by
  simp_rw [mixtureWeight_def, ENNReal.inv_pow, pow_succ, ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric_two]
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The **countable mixture** `∑ₙ 2^{-(n+1)} • P (θs n)` of the members `P (θs n)` of a family
of measures. -/
def countableMixture (P : Θ → Measure X) (θs : ℕ → Θ) : Measure X :=
  Measure.sum fun n ↦ mixtureWeight n • P (θs n)

theorem countableMixture_def (P : Θ → Measure X) (θs : ℕ → Θ) :
    countableMixture P θs = Measure.sum fun n ↦ mixtureWeight n • P (θs n) := (rfl)

/-- The mass of any set, measurable or not, under a countable mixture. -/
theorem countableMixture_apply (P : Θ → Measure X) (θs : ℕ → Θ) (s : Set X) :
    countableMixture P θs s = ∑' n, mixtureWeight n * P (θs n) s := by
  simp [countableMixture_def, Measure.sum_apply_of_countable]

/-- A set is null for a countable mixture iff it is null for every component. -/
@[simp]
theorem countableMixture_apply_eq_zero_iff {s : Set X} :
    countableMixture P θs s = 0 ↔ ∀ n, P (θs n) s = 0 := by
  simp [countableMixture_def]

/-- Every component is absolutely continuous with respect to the mixture. -/
theorem absolutelyContinuous_countableMixture (n : ℕ) : P (θs n) ≪ countableMixture P θs :=
  fun _ hs ↦ countableMixture_apply_eq_zero_iff.mp hs n

/-- A mixture of measures dominated by `μ` is dominated by `μ`. -/
theorem countableMixture_absolutelyContinuous (h : ∀ n, P (θs n) ≪ μ) :
    countableMixture P θs ≪ μ :=
  fun _ hs ↦ countableMixture_apply_eq_zero_iff.mpr fun n ↦ h n hs

instance isProbabilityMeasure_countableMixture [∀ n, IsProbabilityMeasure (P (θs n))] :
    IsProbabilityMeasure (countableMixture P θs) :=
  ⟨by simp [countableMixture_apply]⟩

instance sFinite_countableMixture [∀ n, SFinite (P (θs n))] :
    SFinite (countableMixture P θs) := by
  rw [countableMixture_def]
  infer_instance

/-- The mixture of a constant sequence is the measure it repeats. -/
@[simp]
theorem countableMixture_const (P : Θ → Measure X) (θ : Θ) :
    countableMixture P (fun _ ↦ θ) = P θ := by
  ext s -
  rw [countableMixture_apply, ENNReal.tsum_mul_right, tsum_mixtureWeight, one_mul]

/-- Pushforward commutes with taking a countable mixture. -/
theorem map_countableMixture {Y : Type*} [MeasurableSpace Y] {φ : X → Y}
    (hφ : AEMeasurable φ (countableMixture P θs)) :
    (countableMixture P θs).map φ = countableMixture (fun θ ↦ (P θ).map φ) θs := by
  rw [countableMixture_def, countableMixture_def, Measure.map_sum (by rwa [← countableMixture_def])]
  exact Measure.sum_congr fun n ↦
    Measure.map_smul _ (hφ.mono_ac (absolutelyContinuous_countableMixture n))

/-- Composition product with an s-finite kernel distributes over a countable mixture on the left. -/
theorem countableMixture_compProd {Y : Type*} [MeasurableSpace Y] [∀ n, SFinite (P (θs n))]
    (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsSFiniteKernel κ] :
    countableMixture P θs ⊗ₘ κ = countableMixture (fun θ ↦ P θ ⊗ₘ κ) θs := by
  rw [countableMixture_def, countableMixture_def, Measure.compProd_sum_left]
  exact Measure.sum_congr fun n ↦ Measure.compProd_smul_left _

/-- If an s-finite kernel `K` disintegrates each component `P (θs n)` along a measurable map `T`,
then `K` also disintegrates the countable mixture `countableMixture P θs` along `T`. -/
theorem map_prodMk_countableMixture_eq_compProd {S : Type*} [MeasurableSpace S]
    [∀ n, SFinite (P (θs n))] {T : X → S} (hT : Measurable T)
    {K : ProbabilityTheory.Kernel S X} [ProbabilityTheory.IsSFiniteKernel K]
    (h : ∀ n, (P (θs n)).map (fun x ↦ (T x, x)) = (P (θs n)).map T ⊗ₘ K) :
    (countableMixture P θs).map (fun x ↦ (T x, x)) =
      (countableMixture P θs).map T ⊗ₘ K := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  calc (countableMixture P θs).map (fun x ↦ (T x, x))
    _ = countableMixture (fun θ ↦ (P θ).map (fun x ↦ (T x, x))) θs :=
        map_countableMixture hpair.aemeasurable
    _ = countableMixture (fun θ ↦ (P θ).map T ⊗ₘ K) θs := by
        rw [countableMixture_def, countableMixture_def]
        exact Measure.sum_congr fun n ↦ by rw [h n]
    _ = countableMixture (fun θ ↦ (P θ).map T) θs ⊗ₘ K :=
        (countableMixture_compProd K).symm
    _ = (countableMixture P θs).map T ⊗ₘ K := by rw [← map_countableMixture hT.aemeasurable]

/-- A countable mixture of measures with densities `g n` in `ℝ≥0∞` has the mixed density
`∑ₙ mixtureWeight n * g n`. -/
theorem countableMixture_eq_withDensity {g : ℕ → X → ℝ≥0∞} (hg : ∀ n, Measurable (g n))
    (hP : ∀ n, P (θs n) = μ.withDensity (g n)) :
    countableMixture P θs = μ.withDensity fun x ↦ ∑' n, mixtureWeight n * g n x := by
  simp_rw [countableMixture_def, hP, ← withDensity_smul _ (hg _)]
  rw [← withDensity_tsum fun n ↦ (hg n).const_smul (mixtureWeight n)]
  congr with x
  simp [ENNReal.tsum_apply]

/-- A countable mixture of measures whose densities share a measurable factor `h` has the mixed
density `(∑ₙ mixtureWeight n * g n) * h`. -/
theorem countableMixture_eq_withDensity_mul {g : ℕ → X → ℝ≥0∞} {h : X → ℝ≥0∞}
    (hg : ∀ n, Measurable (g n)) (hh : Measurable h)
    (hP : ∀ n, P (θs n) = μ.withDensity fun x ↦ g n x * h x) :
    countableMixture P θs = μ.withDensity fun x ↦ (∑' n, mixtureWeight n * g n x) * h x := by
  rw [countableMixture_eq_withDensity (fun n ↦ (hg n).mul hh) hP]
  congr 1
  simp_rw [Pi.mul_apply, ← mul_assoc]
  funext x
  rw [ENNReal.tsum_mul_right]

/-- A countable mixture that is a finite measure, of measures with real densities `f n`, has the
real density `(∑ₙ mixtureWeight n * ofReal (f n)).toReal`. That sum is finite
`μ`-almost everywhere because the mixture is finite; the hypothesis is needed, since for densities
`f n = 4 ^ n` on a set of positive measure the sum is infinite there. -/
theorem HasDensity.countableMixture {f : ℕ → X → ℝ} [IsFiniteMeasure (countableMixture P θs)]
    (hf : ∀ n, HasDensity (P (θs n)) μ (f n)) :
    HasDensity (countableMixture P θs) μ
      fun x ↦ (∑' n, mixtureWeight n * ENNReal.ofReal (f n x)).toReal := by
  have hg : ∀ n, Measurable fun x ↦ ENNReal.ofReal (f n x) :=
    fun n ↦ (hf n).measurable.ennreal_ofReal
  have hmix := countableMixture_eq_withDensity hg fun n ↦ (hf n).eq_withDensity
  have hsum : Measurable fun x ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (f n x) :=
    Measurable.tsum fun n ↦ (hg n).const_mul _
  refine ⟨hsum.ennreal_toReal, ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  have hfin : ∀ᵐ x ∂μ, ∑' n, mixtureWeight n * ENNReal.ofReal (f n x) < ∞ := by
    refine ae_lt_top hsum ?_
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hmix]
    exact measure_ne_top _ _
  rw [hmix]
  refine withDensity_congr_ae ?_
  filter_upwards [hfin] with x hx
  rw [ENNReal.ofReal_toReal hx.ne]

/-- **The Halmos–Savage lemma.** A nonempty family of measures dominated by an s-finite measure
`μ` is dominated by one of its countable mixtures. A family with real densities with respect to
`μ` is dominated by `μ`, by `TauCeti.HasDensity.absolutelyContinuous`. -/
theorem exists_absolutelyContinuous_countableMixture [Nonempty Θ] (P : Θ → Measure X)
    (μ : Measure X) [SFinite μ] (hP : ∀ θ, P θ ≪ μ) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs := by
  -- A `P θ`-null set `N θ` that a.e. contains every measurable `P θ`-null set: the union of a
  -- countable subfamily of the measurable `P θ`-null sets.
  have hN : ∀ θ, ∃ N, MeasurableSet N ∧ P θ N = 0 ∧
      ∀ s, MeasurableSet s → P θ s = 0 → s ≤ᵐ[μ] N := by
    intro θ
    obtain ⟨D, hDC, hDc, hD⟩ := Measure.exists_ae_subset_biUnion_countable μ
      (C := {s | MeasurableSet s ∧ P θ s = 0}) fun _ hs ↦ hs.1
    exact ⟨⋃₀ D, .sUnion hDc fun _ hs ↦ (hDC hs).1,
      (measure_sUnion_null_iff hDc).2 fun _ hs ↦ (hDC hs).2, fun s hs hs0 ↦ hD s ⟨hs, hs0⟩⟩
  choose N hNm hN0 hN using hN
  -- Countably many complements `(N (θs n))ᶜ` whose union a.e. contains every `(N θ)ᶜ`.
  obtain ⟨D, hDC, hDc, hD⟩ := Measure.exists_ae_subset_biUnion_countable μ
    (C := range fun θ ↦ (N θ)ᶜ) (by rintro _ ⟨θ, rfl⟩; exact (hNm θ).compl)
  obtain ⟨e, he⟩ := (hDc.insert (N ‹Nonempty Θ›.some)ᶜ).exists_eq_range (insert_nonempty _ _)
  have he_mem : ∀ n, e n ∈ range fun θ ↦ (N θ)ᶜ :=
    fun n ↦ insert_subset (mem_range_self _) hDC (he ▸ mem_range_self n)
  choose θs hθs using he_mem
  have hDθs : ⋃₀ D ⊆ ⋃ n, (N (θs n))ᶜ := by
    simp_rw [hθs, ← sUnion_range, ← he]
    exact sUnion_subset_sUnion (subset_insert _ _)
  have hT : ∀ θ, (N θ)ᶜ ≤ᵐ[μ] ⋃ n, (N (θs n))ᶜ :=
    fun θ ↦ (hD _ (mem_range_self θ)).trans (ae_of_all _ fun _ hx ↦ hDθs hx)
  refine ⟨θs, fun θ ↦ Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_⟩
  -- A measurable mixture-null set is `μ`-a.e. inside every `N (θs n)`, hence inside `N θ`.
  have hsN : ∀ n, s ≤ᵐ[μ] N (θs n) :=
    fun n ↦ hN _ s hs (countableMixture_apply_eq_zero_iff.mp hs0 n)
  have hsNθ : s ≤ᵐ[μ] N θ := by
    filter_upwards [ae_all_iff.2 hsN, hT θ] with x hxs hxθ hx
    by_contra hxN
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hxθ hxN)
    exact hn (hxs n hx)
  exact measure_mono_null_ae ((hP θ).ae_le hsNθ) (hN0 θ)

end TauCeti
