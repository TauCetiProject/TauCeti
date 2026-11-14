/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Sobolev wave front sets

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`, and `s` a real number. The `H^s` wave front set refines the wave front set of
`Distribution.waveFrontSet` by measuring the singularities of `T` on the Sobolev scale instead of
by rapid decay: `T` is *microlocally `H^s`* at `(x, ξ)` if some test function `φ` with `φ x ≠ 0`
and some open cone `Γ` containing `ξ` make the weighted localized Fourier transform

`η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) T (φ e_η)`

square integrable on `Γ`, where `η ↦ T (φ e_η)` is the Fourier transform `Distribution.localFourier`
of the compactly supported distribution `φ T`. The weight is the symbol of Mathlib's Bessel
potential `TemperedDistribution.besselPotential`; with `Γ = E` the condition is the Fourier
description of `φ T ∈ H^s` (the comparison with `TemperedDistribution.MemSobolev` is not
formalized here). The **`H^s` wave front set** `Distribution.sobolevWaveFrontSet s T` consists of
the `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0` at which `T` is not microlocally `H^s`.

The point mass in dimension `d` shows how the order enters: its localized Fourier transform has
constant modulus, so it is microlocally `H^s` everywhere for `s < -d / 2`, while for `s ≥ -d / 2`
its `H^s` wave front set is the whole punctured fibre over the point, since the weight
`(1 + ‖η‖ ^ 2) ^ s` is then not integrable over any open cone
(`TauCeti.not_integrableOn_rpow_neg_one_add_norm_sq`).

## Main declarations

* `Distribution.IsMicrolocallySobolevAt s T x ξ`: `T` is microlocally `H^s` at `(x, ξ)`.
* `Distribution.sobolevWaveFrontSet s T`: the `H^s` wave front set.

## Main results

* `Distribution.isOpen_diff_sobolevWaveFrontSet`, `Distribution.smul_mem_sobolevWaveFrontSet_iff`:
  the `H^s` wave front set is closed in `Ω × (E \ {0})` and conic in the frequency.
* `Distribution.sobolevWaveFrontSet_mono`: it grows with `s`.
* `Distribution.sobolevWaveFrontSet_subset_waveFrontSet`: it is contained in the wave front set.
* `Distribution.sobolevWaveFrontSet_smul`, `Distribution.sobolevWaveFrontSet_conj`: nonzero
  scalar multiples have the same `H^s` wave front set, and complex conjugation reflects the
  frequencies.
* `Distribution.sobolevWaveFrontSet_delta_eq_empty`, `Distribution.sobolevWaveFrontSet_delta`:
  the point mass at `x₀ ∈ Ω` has empty `H^s` wave front set for `s < -d / 2` and `H^s` wave front
  set `{x₀} × (E \ {0})` for `s ≥ -d / 2`.
* `Distribution.sobolevWaveFrontSet_compCLMOfContinuousLinearEquiv`: the `H^s` wave front set is
  invariant under linear changes of coordinates, with covectors transforming by the transpose. The
  substitution `ζ = (e⁻¹)ᵀ η` in the square integrability on a cone changes the weight
  `(1 + ‖η‖ ^ 2) ^ (s / 2)` by a bounded factor, since `η` and `(e⁻¹)ᵀ η` have comparable norms
  (`TauCeti.one_add_norm_sq_rpow_le_of_norm_le_mul`).

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.1 (the wave front
  set) and §8.2, Theorem 8.2.4 (the wave front set of a pullback, here along a linear change of
  coordinates).
-/

public section

noncomputable section

open Complex ComplexConjugate Filter MeasureTheory Module Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- A complex distribution `T` is **microlocally `H^s`** at `(x, ξ)` if some complex test
function `φ` with `φ x ≠ 0` and some open cone `Γ` containing `ξ` make the weighted localized
Fourier transform `η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) localFourier T φ η` square integrable on `Γ`. -/
def IsMicrolocallySobolevAt (s : ℝ) (T : 𝓓'(Ω, ℂ)) (x ξ : E) : Prop :=
  ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
    (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 (volume.restrict Γ)

/-- Unfolds `IsMicrolocallySobolevAt` into its cutoff, cone and integrability witnesses. -/
theorem isMicrolocallySobolevAt_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E} :
    T.IsMicrolocallySobolevAt s x ξ ↔
      ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
        (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
        MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 (volume.restrict Γ) :=
  Iff.rfl

/-- The **`H^s` wave front set** of a complex distribution `T` on `Ω`: the pairs `(x, ξ)` with
`x ∈ Ω` and `ξ ≠ 0` at which `T` is not microlocally `H^s`. -/
def sobolevWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, ℂ)) : Set (E × E) :=
  {p | p.1 ∈ Ω ∧ p.2 ≠ 0 ∧ ¬ T.IsMicrolocallySobolevAt s p.1 p.2}

@[simp]
theorem mem_sobolevWaveFrontSet_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E} :
    (x, ξ) ∈ T.sobolevWaveFrontSet s ↔ x ∈ Ω ∧ ξ ≠ 0 ∧ ¬ T.IsMicrolocallySobolevAt s x ξ :=
  Iff.rfl

/-- The `H^s` wave front set lies in `Ω × (E \ {0})`. -/
theorem sobolevWaveFrontSet_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevWaveFrontSet s ⊆ (Ω : Set E) ×ˢ {0}ᶜ :=
  fun _ hp ↦ ⟨hp.1, hp.2.1⟩

omit [FiniteDimensional ℝ E] in
/-- The weighted localized Fourier transform is continuous, hence measurable. -/
private theorem aestronglyMeasurable_weight_smul_localFourier (s : ℝ) (T : 𝓓'(Ω, ℂ))
    (φ : 𝓓(Ω, ℂ)) (μ : Measure E) :
    AEStronglyMeasurable (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) μ :=
  ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)).1.continuous.smul
    (T.continuous_localFourier φ)).aestronglyMeasurable

/-! ### Cones, openness and the order -/

/-- Being microlocally `H^s` depends only on the ray through the frequency. -/
theorem isMicrolocallySobolevAt_smul_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E} {t : ℝ}
    (ht : 0 < t) : T.IsMicrolocallySobolevAt s x (t • ξ) ↔ T.IsMicrolocallySobolevAt s x ξ := by
  -- An open cone contains `ξ` exactly when it contains `t • ξ`.
  have key {r : ℝ} (hr : 0 < r) {ζ : E} :
      T.IsMicrolocallySobolevAt s x ζ → T.IsMicrolocallySobolevAt s x (r • ζ) := by
    rintro ⟨φ, hφ, Γ, hΓ, hζ, hcone, hL⟩
    exact ⟨φ, hφ, Γ, hΓ, hcone r hr ζ hζ, hcone, hL⟩
  refine ⟨fun h ↦ ?_, key ht⟩
  simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using key (inv_pos.2 ht) h

/-- The `H^s` wave front set is conic in the frequency variable. -/
theorem smul_mem_sobolevWaveFrontSet_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E} {t : ℝ} (ht : 0 < t) :
    (x, t • ξ) ∈ T.sobolevWaveFrontSet s ↔ (x, ξ) ∈ T.sobolevWaveFrontSet s := by
  simp [isMicrolocallySobolevAt_smul_iff ht, ht.ne']

/-- The set of points at which a distribution is microlocally `H^s` is open. -/
theorem isOpen_setOf_isMicrolocallySobolevAt (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    IsOpen {p : E × E | T.IsMicrolocallySobolevAt s p.1 p.2} := by
  refine isOpen_iff_mem_nhds.2 fun p ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL⟩ ↦ ?_
  have hU : IsOpen {y : E | φ y ≠ 0} := isOpen_ne_fun φ.continuous continuous_const
  filter_upwards [(hU.prod hΓ).mem_nhds ⟨hφ, hξ⟩] with q hq
  exact ⟨φ, hq.1, Γ, hΓ, hq.2, hcone, hL⟩

/-- The `H^s` wave front set is closed in `Ω × (E \ {0})`. -/
theorem isOpen_diff_sobolevWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ T.sobolevWaveFrontSet s) := by
  have h : ((Ω : Set E) ×ˢ {0}ᶜ) \ T.sobolevWaveFrontSet s =
      ((Ω : Set E) ×ˢ {0}ᶜ) ∩ {p : E × E | T.IsMicrolocallySobolevAt s p.1 p.2} := by
    ext ⟨x, ξ⟩
    simp only [sobolevWaveFrontSet, Set.mem_sdiff, mem_inter_iff, mem_prod, mem_compl_iff,
      mem_ofPred_eq]
    tauto
  rw [h]
  exact (Ω.isOpen.prod isOpen_compl_singleton).inter (T.isOpen_setOf_isMicrolocallySobolevAt s)

/-- Being microlocally `H^s` implies being microlocally `H^t` for every `t ≤ s`. -/
theorem IsMicrolocallySobolevAt.mono {s t : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) (hts : t ≤ s) : T.IsMicrolocallySobolevAt t x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL⟩ := h
  refine ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL.mono (aestronglyMeasurable_weight_smul_localFourier t T φ _)
    (.of_forall fun η ↦ ?_)⟩
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)]
  gcongr
  · nlinarith [sq_nonneg ‖η‖]

/-- The `H^s` wave front set grows with `s`. -/
theorem sobolevWaveFrontSet_mono {s t : ℝ} (hts : t ≤ s) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevWaveFrontSet t ⊆ T.sobolevWaveFrontSet s :=
  fun _ ⟨hx, hξ, hT⟩ ↦ ⟨hx, hξ, fun h ↦ hT (h.mono hts)⟩

/-- A distribution whose weighted localized Fourier transform, for a cutoff not vanishing at
`x`, is square integrable on all of `E` is microlocally `H^s` at `x` in every direction. -/
theorem isMicrolocallySobolevAt_of_memLp {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E} {φ : 𝓓(Ω, ℂ)}
    (hφ : φ x ≠ 0) (h : MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2)
    (ξ : E) : T.IsMicrolocallySobolevAt s x ξ :=
  ⟨φ, hφ, univ, isOpen_univ, mem_univ ξ, fun _ _ _ _ ↦ mem_univ _, by
    rwa [Measure.restrict_univ]⟩

/-! ### Comparison with the wave front set -/

/-- Microlocal smoothness implies being microlocally `H^s` for every `s`. -/
theorem IsMicrolocallySmoothAt.isMicrolocallySobolevAt {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySmoothAt x ξ) (s : ℝ) : T.IsMicrolocallySobolevAt s x ξ := by
  obtain ⟨k, hk⟩ := exists_nat_ge s
  refine IsMicrolocallySobolevAt.mono ?_ hk
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 h
  obtain ⟨C, hC⟩ := hdecay (k + finrank ℝ E + 1)
  refine ⟨φ, hφ, Γ, hΓ, hξ, hcone, (((TauCeti.memLp_two_one_add_norm_rpow_neg (V := E) volume
    (r := finrank ℝ E + 1) (by linarith)).const_mul C).restrict Γ).mono
    (aestronglyMeasurable_weight_smul_localFourier _ T φ _)
    ((ae_restrict_iff' hΓ.measurableSet).2 (.of_forall fun η hη ↦ ?_))⟩
  -- With `a = 1 + ‖η‖`, the weight is at most `a ^ k` and the decay bound gives
  -- `a ^ (k + d + 1) ‖localFourier T φ η‖ ≤ C`.
  set a := 1 + ‖η‖
  have ha : 1 ≤ a := le_add_of_nonneg_right (norm_nonneg η)
  have hw : (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2) ≤ a ^ k := by
    calc (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (a ^ 2) ^ ((k : ℝ) / 2) := by
          gcongr
          nlinarith [norm_nonneg η]
      _ = a ^ k := by rw [Real.sq_rpow_div_two (by positivity), Real.rpow_natCast]
  have hpow : a ^ (-((finrank ℝ E : ℝ) + 1)) = (a ^ (finrank ℝ E + 1))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast, Nat.cast_succ]
  have hbound := hC η hη
  rw [norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, hpow]
  refine le_trans ?_ (le_abs_self _)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2) * ‖T.localFourier φ η‖ * a ^ (finrank ℝ E + 1)
      ≤ a ^ k * ‖T.localFourier φ η‖ * a ^ (finrank ℝ E + 1) := by gcongr
    _ = a ^ (k + finrank ℝ E + 1) * ‖T.localFourier φ η‖ := by ring
    _ ≤ C := hbound

/-- The `H^s` wave front set is contained in the wave front set. -/
theorem sobolevWaveFrontSet_subset_waveFrontSet (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevWaveFrontSet s ⊆ T.waveFrontSet := by
  rintro ⟨x, ξ⟩ ⟨hx, hξ, hT⟩
  exact mem_waveFrontSet_iff.2 ⟨hx, hξ, fun h ↦ hT (h.isMicrolocallySobolevAt s)⟩

/-- The zero distribution has empty `H^s` wave front set. -/
@[simp]
theorem sobolevWaveFrontSet_zero (s : ℝ) : (0 : 𝓓'(Ω, ℂ)).sobolevWaveFrontSet s = ∅ :=
  subset_empty_iff.1 (waveFrontSet_zero (Ω := Ω) ▸ sobolevWaveFrontSet_subset_waveFrontSet s 0)

/-! ### Scalar multiples and conjugation -/

/-- A scalar multiple of `T` is microlocally `H^s` wherever `T` is. -/
theorem IsMicrolocallySobolevAt.smul {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) (c : ℂ) : (c • T).IsMicrolocallySobolevAt s x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL⟩ := h
  refine ⟨φ, hφ, Γ, hΓ, hξ, hcone, ?_⟩
  convert hL.const_smul c using 1
  funext η
  simp only [localFourier_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- A scalar multiple of `T` has `H^s` wave front set contained in that of `T`. -/
theorem sobolevWaveFrontSet_smul_subset (s : ℝ) (c : ℂ) (T : 𝓓'(Ω, ℂ)) :
    (c • T).sobolevWaveFrontSet s ⊆ T.sobolevWaveFrontSet s :=
  fun _ ⟨hx, hξ, hT⟩ ↦ ⟨hx, hξ, fun h ↦ hT (h.smul c)⟩

/-- A nonzero scalar multiple of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_smul (s : ℝ) {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, ℂ)) :
    (c • T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet s := by
  refine (sobolevWaveFrontSet_smul_subset s c T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ hc] using sobolevWaveFrontSet_smul_subset s c⁻¹ (c • T)

/-- The negative of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_neg (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (-T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet s := by
  rw [← neg_one_smul ℂ T, sobolevWaveFrontSet_smul s (neg_ne_zero.2 one_ne_zero)]

/-- The complex conjugate of `T` is microlocally `H^s` at `(x, ξ)` exactly when `T` is
microlocally `H^s` at `(x, -ξ)`. -/
theorem isMicrolocallySobolevAt_conj_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E} :
    (mapCLM conjCLE.toContinuousLinearMap T).IsMicrolocallySobolevAt s x ξ ↔
      T.IsMicrolocallySobolevAt s x (-ξ) := by
  -- Conjugating the cutoff and reflecting the cone transfers the integrability from `T` to its
  -- conjugate, since the reflection `η ↦ -η` preserves Lebesgue measure and the weight.
  have key {S : 𝓓'(Ω, ℂ)} {ζ : E} (h : S.IsMicrolocallySobolevAt s x (-ζ)) :
      (mapCLM conjCLE.toContinuousLinearMap S).IsMicrolocallySobolevAt s x ζ := by
    obtain ⟨φ, hφ, Γ, hΓ, hζ, hcone, hL⟩ := h
    have hneg : MeasurePreserving Neg.neg (volume.restrict (Neg.neg ⁻¹' Γ))
        (volume.restrict Γ) :=
      (Measure.measurePreserving_neg volume).restrict_preimage hΓ.measurableSet
    refine ⟨postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap φ, by simpa using hφ,
      Neg.neg ⁻¹' Γ, hΓ.preimage continuous_neg, hζ, fun t ht η hη ↦ ?_,
      (hL.comp_measurePreserving hneg).mono
        (aestronglyMeasurable_weight_smul_localFourier _ _ _ _) (.of_forall fun η ↦ ?_)⟩
    · simpa [smul_neg] using hcone t ht (-η) hη
    · simp [localFourier_conj]
  refine ⟨fun h ↦ ?_, key⟩
  rw [← mapCLM_conj_mapCLM_conj T]
  exact key (by rwa [neg_neg])

/-- Complex conjugation reflects the `H^s` wave front set in the frequency variable. -/
theorem sobolevWaveFrontSet_conj (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (mapCLM conjCLE.toContinuousLinearMap T).sobolevWaveFrontSet s =
      Prod.map id Neg.neg ⁻¹' T.sobolevWaveFrontSet s := by
  ext ⟨x, ξ⟩
  simp [isMicrolocallySobolevAt_conj_iff]

/-! ### Point masses -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The weighted localized Fourier transform of the point mass at `x₀` has modulus
`‖φ x₀‖ (1 + ‖η‖ ^ 2) ^ (s / 2)`. -/
private theorem norm_weight_smul_localFourier_delta (s : ℝ) (x₀ : E) (φ : 𝓓(Ω, ℂ)) (η : E) :
    ‖(1 + ‖η‖ ^ 2) ^ (s / 2) •
        (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).localFourier φ η‖ =
      ‖φ x₀‖ * (1 + ‖η‖ ^ 2) ^ (s / 2) := by
  rw [localFourier_delta, norm_smul, norm_mul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (by positivity), mul_comm]

/-- **Point masses are `H^s` below the critical order.** In dimension `d`, the point mass at `x₀`
has empty `H^s` wave front set for `s < -d / 2`. -/
theorem sobolevWaveFrontSet_delta_eq_empty {s : ℝ} (hs : (finrank ℝ E : ℝ) < -2 * s) (x₀ : E) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).sobolevWaveFrontSet s = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun ⟨x, ξ⟩ ⟨hx, _, hT⟩ ↦ hT ?_
  obtain ⟨φ, -, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) (Ω.isOpen.mem_nhds hx)
    subset_rfl (1 : ℂ)
  refine isMicrolocallySobolevAt_of_memLp (φ := φ) (by simp [hφx])
    ((memLp_two_iff_integrable_sq_norm
      (aestronglyMeasurable_weight_smul_localFourier _ _ _ _)).2 ?_) ξ
  refine ((integrable_rpow_neg_one_add_norm_sq (μ := volume) hs).const_mul (‖φ x₀‖ ^ 2)).congr
    (.of_forall fun η ↦ ?_)
  simp only [norm_weight_smul_localFourier_delta, mul_pow,
    Real.rpow_div_two_sq (by positivity : (0 : ℝ) ≤ 1 + ‖η‖ ^ 2),
    show -(-2 * s) / 2 = s by ring]

/-- **The `H^s` wave front set of a point mass.** In dimension `d`, the point mass at `x₀ ∈ Ω`
has `H^s` wave front set `{x₀} × (E \ {0})` for `s ≥ -d / 2`: its localized Fourier transform has
constant modulus, and the weight `(1 + ‖η‖ ^ 2) ^ s` is not integrable over any open cone. -/
theorem sobolevWaveFrontSet_delta {s : ℝ} (hs : -2 * s ≤ finrank ℝ E) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).sobolevWaveFrontSet s = {x₀} ×ˢ {0}ᶜ := by
  refine ((sobolevWaveFrontSet_subset_waveFrontSet s _).trans
    (waveFrontSet_delta hx₀).subset).antisymm ?_
  rintro ⟨x, ξ⟩ ⟨hx, hξ⟩
  rw [mem_singleton_iff] at hx
  subst hx
  refine ⟨hx₀, hξ, fun h ↦ ?_⟩
  obtain ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hL⟩ := h
  have hint := (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_weight_smul_localFourier _ _ _ _)).1 hL
  refine TauCeti.not_integrableOn_rpow_neg_one_add_norm_sq volume hs hΓ hcone hξΓ hξ
    ((hint.const_mul (‖φ x‖ ^ 2)⁻¹).congr (.of_forall fun η ↦ ?_))
  have hφ2 : ‖φ x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hφ)
  simp only [norm_weight_smul_localFourier_delta, mul_pow,
    Real.rpow_div_two_sq (by positivity : (0 : ℝ) ≤ 1 + ‖η‖ ^ 2),
    show -(-2 * s) / 2 = s by ring, inv_mul_cancel_left₀ hφ2]

/-! ### Linear changes of coordinates -/

section LinearEquiv

open scoped InnerProduct

variable {V : Opens E}

/-- If `T` is microlocally `H^s` at `(e x, (e⁻¹)ᵀ ξ)`, then its pullback along `e` is microlocally
`H^s` at `(x, ξ)`. Here `e` identifies `V` with `Ω`. -/
theorem IsMicrolocallySobolevAt.compCLMOfContinuousLinearEquiv {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V)
    (h : T.IsMicrolocallySobolevAt s (e x) (((e.symm : E →L[ℝ] E)†) ξ)) :
    (compCLMOfContinuousLinearEquiv e hVO T).IsMicrolocallySobolevAt s x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL⟩ := h
  -- The frequencies change by `A = (e⁻¹)ᵀ`, a linear isomorphism with inverse `eᵀ`.
  set A : E →L[ℝ] E := (e.symm : E →L[ℝ] E)†
  have hinv : ∀ η, ((e : E →L[ℝ] E)†) (A η) = η := fun η ↦ by
    simpa using e.symm.adjoint_symm_adjoint_apply η
  set L : E ≃L[ℝ] E := e.symm.adjointEquiv
  have hLA : (L : E → E) = A := funext e.symm.adjointEquiv_apply
  refine ⟨e.symm.transportTestFunction hOV φ, by simpa using hφ, A ⁻¹' Γ,
    hΓ.preimage A.continuous, hξ, fun t ht η hη ↦ ?_, ?_⟩
  · simpa only [mem_preimage, map_smul] using hcone t ht (A η) hη
  -- Change variables `ζ = A η` in the square integrability of `T` on `Γ`.
  have hmem : MemLp (fun η ↦ (1 + ‖A η‖ ^ 2) ^ (s / 2) • T.localFourier φ (A η)) 2
      (volume.restrict (A ⁻¹' Γ)) := by
    rw [← hLA, ← Function.comp_def (fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ (s / 2) • T.localFourier φ ζ) L,
      memLp_iff, Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) hL
  -- The weights at `η` and at `A η` are comparable, since `‖η‖ ≤ ‖e‖ ‖A η‖`.
  set c : ℝ := max 1 (max ‖(e : E →L[ℝ] E)‖ ‖A‖)
  have hc : 1 ≤ c := le_max_left _ _
  have hweight : ∀ η, (1 + ‖η‖ ^ 2) ^ (s / 2) ≤ c ^ |s| * (1 + ‖A η‖ ^ 2) ^ (s / 2) := fun η ↦ by
    refine TauCeti.one_add_norm_sq_rpow_le_of_norm_le_mul hc s ?_ ?_
    · calc ‖η‖ = ‖((e : E →L[ℝ] E)†) (A η)‖ := by rw [hinv]
        _ ≤ ‖(e : E →L[ℝ] E)†‖ * ‖A η‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖(e : E →L[ℝ] E)‖ * ‖A η‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ c * ‖A η‖ := by gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
    · calc ‖A η‖ ≤ ‖A‖ * ‖η‖ := A.le_opNorm η
        _ ≤ c * ‖η‖ := by gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
  refine hmem.of_le_mul (c := |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹ * c ^ |s|)
    (aestronglyMeasurable_weight_smul_localFourier _ _ _ _) (.of_forall fun η ↦ ?_)
  rw [localFourier_compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.transportTestFunction_transportTestFunction_symm, norm_smul, norm_smul,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), mul_left_comm,
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hweight η) (norm_nonneg _)

/-- **Microlocal `H^s` regularity under a linear change of coordinates.** When `e` identifies `V`
with `Ω`, the pullback `e^* T` is microlocally `H^s` at `(x, ξ)` exactly when `T` is microlocally
`H^s` at `(e x, (e⁻¹)ᵀ ξ)`. -/
theorem isMicrolocallySobolevAt_compCLMOfContinuousLinearEquiv_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)}
    {x ξ : E} (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) :
    (compCLMOfContinuousLinearEquiv e hVO T).IsMicrolocallySobolevAt s x ξ ↔
      T.IsMicrolocallySobolevAt s (e x) (((e.symm : E →L[ℝ] E)†) ξ) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compCLMOfContinuousLinearEquiv e hVO hOV⟩
  -- Pull `e^* T` back along `e⁻¹`, which gives back `T`.
  have h' : (compCLMOfContinuousLinearEquiv e hVO T).IsMicrolocallySobolevAt s (e.symm (e x))
      (((e.symm.symm : E →L[ℝ] E)†) (((e.symm : E →L[ℝ] E)†) ξ)) := by
    simpa only [ContinuousLinearEquiv.adjoint_symm_adjoint_apply,
      ContinuousLinearEquiv.symm_apply_apply] using h
  simpa using h'.compCLMOfContinuousLinearEquiv e.symm hOV (by simpa using hVO)

/-- **The `H^s` wave front set under a linear change of coordinates.** When `e` identifies `V`
with `Ω`, the `H^s` wave front set of the pullback `e^* T` consists of the `(x, ξ)` with
`(e x, (e⁻¹)ᵀ ξ)` in the `H^s` wave front set of `T`: positions move by `e⁻¹` and covectors by the
transpose `eᵀ`, as for the wave front set
(`Distribution.waveFrontSet_compCLMOfContinuousLinearEquiv`). -/
theorem sobolevWaveFrontSet_compCLMOfContinuousLinearEquiv (s : ℝ) (e : E ≃L[ℝ] E)
    (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) (T : 𝓓'(Ω, ℂ)) :
    (compCLMOfContinuousLinearEquiv e hVO T).sobolevWaveFrontSet s =
      Prod.map e ((e.symm : E →L[ℝ] E)†) ⁻¹' T.sobolevWaveFrontSet s := by
  ext ⟨x, ξ⟩
  have hx : x ∈ V ↔ e x ∈ Ω := ⟨fun h ↦ hVO h, fun h ↦ by simpa using hOV h⟩
  have hξ : ξ ≠ 0 ↔ ((e.symm : E →L[ℝ] E)†) ξ ≠ 0 :=
    (map_ne_zero_iff _ e.symm.adjoint_bijective.injective).symm
  simp only [mem_sobolevWaveFrontSet_iff, mem_preimage, Prod.map_apply, hx, hξ,
    isMicrolocallySobolevAt_compCLMOfContinuousLinearEquiv_iff e hVO hOV]

end LinearEquiv

end Distribution
