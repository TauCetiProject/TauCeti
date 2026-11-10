/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Integral.Cone

/-!
# The Sobolev wave front set

The wave front set of a distribution `T` records the directions in which `T` fails to be smooth.
Its Sobolev refinement records the directions in which `T` fails to lie in the Sobolev space `H^s`,
for a real order `s`. With `⟨η⟩ = (1 + ‖η‖ ^ 2) ^ (1 / 2)`, the distribution `T` is
*microlocally `H^s`* at `(x, ξ)` if some complex test function `φ` with `φ x ≠ 0` has localized
Fourier transform `η ↦ T (φ e_η)` (`Distribution.localFourier`) with

`∫_Γ ⟨η⟩ ^ (2 s) ‖T (φ e_η)‖ ^ 2 dη < ∞`

on an open cone `Γ` containing `ξ`, and the **Sobolev wave front set** `WF_s(T)`
(`Distribution.sobolevWaveFrontSet T s`) consists of the `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0` at which
`T` is not microlocally `H^s`. Over all of `E` instead of a cone, the condition says that `φ T`
lies in `H^s`.

The Sobolev wave front sets grow with the order `s` and lie in the wave front set: a rapidly
decreasing localized Fourier transform is square integrable against every weight `⟨η⟩ ^ (2 s)`.
They measure the strength of a singularity, which the wave front set does not: the point mass at
`x₀` in dimension `n` has wave front set `{x₀} × (E \ {0})`, while its Sobolev wave front set is
empty for `s < -n / 2` and equal to the wave front set for `s ≥ -n / 2`, matching the classical
fact that `δ_{x₀}` lies in `H^s` exactly when `s < -n / 2`. Microlocal regularity theorems for
pseudodifferential operators are stated with these sets, an operator of order `m` shifting the
order `s` by `m`.

## Main declarations

* `Distribution.IsMicrolocallySobolevAt T s x ξ`: `T` is microlocally `H^s` at `(x, ξ)`.
* `Distribution.sobolevWaveFrontSet T s`: the Sobolev wave front set `WF_s(T)`.

## Main results

* `Distribution.isOpen_diff_sobolevWaveFrontSet`, `Distribution.smul_mem_sobolevWaveFrontSet_iff`:
  `WF_s(T)` is closed in `Ω × (E \ {0})` and conic in the frequency variable.
* `Distribution.sobolevWaveFrontSet_mono`: `WF_t(T) ⊆ WF_s(T)` for `t ≤ s`.
* `Distribution.sobolevWaveFrontSet_subset_waveFrontSet`: `WF_s(T) ⊆ WF(T)`; consequently
  `WF_s(T)` lies over the support of `T` and is empty for a smooth function.
* `Distribution.IsMicrolocallySobolevAt.exists_nhds_cone`: independence of the cutoff. At a point
  where `T` is microlocally `H^s`, every cutoff supported near `x` gives a square integrable
  localized Fourier transform on a smaller open cone.
* `Distribution.sobolevWaveFrontSet_add_subset`, `Distribution.sobolevWaveFrontSet_smul`: the
  Sobolev wave front set of a sum lies in the union, and nonzero scalar multiples do not change it.
* `Distribution.sobolevWaveFrontSet_delta_of_lt`, `Distribution.sobolevWaveFrontSet_delta_of_le`:
  the Sobolev wave front sets of a point mass.

## Implementation notes

The weighted square integral is the lower Lebesgue integral of
`ENNReal.ofReal (⟨η⟩ ^ s * ‖T (φ e_η)‖) ^ 2`. The localized Fourier transform is a smooth function
of `η` (`Distribution.contDiff_localFourier`), so this integrand is measurable. Independence of
the cutoff follows the proof of Hörmander I, Lemma 8.1.1, for the wave front set: changing the
cutoff from `φ` to `φ g` turns the localized Fourier transform into a rapidly decreasing
superposition of its translates, which preserves square integrability with the weight on a smaller
cone (`TauCeti.setLIntegral_ofReal_one_add_norm_sq_rpow_mul_norm_sq_lt_top_of_hasSum`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Lemma 8.1.1 and §8.1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (wave front sets of finite order).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction MeasureTheory Module
open scoped Distributions Topology ENNReal

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- A complex distribution `T` is **microlocally `H^s`** at `(x, ξ)` if some complex test function
`φ` with `φ x ≠ 0` has localized Fourier transform `localFourier T φ` square integrable against
the weight `(1 + ‖η‖ ^ 2) ^ s` on an open cone `Γ` containing `ξ`. -/
def IsMicrolocallySobolevAt (T : 𝓓'(Ω, ℂ)) (s : ℝ) (x ξ : E) : Prop :=
  ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
    (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
    ∫⁻ η in Γ, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier φ η‖) ^ 2 < ∞

/-- Unfolds `IsMicrolocallySobolevAt` into its cutoff, cone and integrability witnesses. -/
theorem isMicrolocallySobolevAt_iff {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E} :
    T.IsMicrolocallySobolevAt s x ξ ↔
      ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
        (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
        ∫⁻ η in Γ, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier φ η‖) ^ 2 < ∞ :=
  Iff.rfl

/-- The **Sobolev wave front set** `WF_s(T)` of order `s` of a complex distribution `T` on `Ω`:
the pairs `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0` at which `T` is not microlocally `H^s`. -/
def sobolevWaveFrontSet (T : 𝓓'(Ω, ℂ)) (s : ℝ) : Set (E × E) :=
  {p | p.1 ∈ Ω ∧ p.2 ≠ 0 ∧ ¬ T.IsMicrolocallySobolevAt s p.1 p.2}

@[simp]
theorem mem_sobolevWaveFrontSet_iff {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E} :
    (x, ξ) ∈ T.sobolevWaveFrontSet s ↔
      x ∈ Ω ∧ ξ ≠ 0 ∧ ¬ T.IsMicrolocallySobolevAt s x ξ :=
  Iff.rfl

/-- The Sobolev wave front set lies in `Ω × (E \ {0})`. -/
theorem sobolevWaveFrontSet_subset (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    T.sobolevWaveFrontSet s ⊆ (Ω : Set E) ×ˢ {0}ᶜ :=
  fun _ hp => ⟨hp.1, hp.2.1⟩

/-! ### Conicity, closedness and monotonicity -/

/-- Being microlocally `H^s` depends only on the ray through the frequency. -/
theorem isMicrolocallySobolevAt_smul_iff {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E} {t : ℝ} (ht : 0 < t) :
    T.IsMicrolocallySobolevAt s x (t • ξ) ↔ T.IsMicrolocallySobolevAt s x ξ := by
  -- An open cone contains `ξ` exactly when it contains `t • ξ`.
  have key {r : ℝ} (hr : 0 < r) {ζ : E} :
      T.IsMicrolocallySobolevAt s x ζ → T.IsMicrolocallySobolevAt s x (r • ζ) := by
    rintro ⟨φ, hφ, Γ, hΓ, hζ, hcone, hL2⟩
    exact ⟨φ, hφ, Γ, hΓ, hcone r hr ζ hζ, hcone, hL2⟩
  refine ⟨fun h => ?_, key ht⟩
  simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using key (inv_pos.2 ht) h

/-- The Sobolev wave front set is conic in the frequency variable. -/
theorem smul_mem_sobolevWaveFrontSet_iff {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E} {t : ℝ} (ht : 0 < t) :
    (x, t • ξ) ∈ T.sobolevWaveFrontSet s ↔ (x, ξ) ∈ T.sobolevWaveFrontSet s := by
  simp [isMicrolocallySobolevAt_smul_iff ht, ht.ne']

/-- The set of points at which a distribution is microlocally `H^s` is open. -/
theorem isOpen_setOf_isMicrolocallySobolevAt (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    IsOpen {p : E × E | T.IsMicrolocallySobolevAt s p.1 p.2} := by
  refine isOpen_iff_mem_nhds.2 fun p ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL2⟩ => ?_
  have hU : IsOpen {y : E | φ y ≠ 0} := isOpen_ne_fun φ.continuous continuous_const
  filter_upwards [(hU.prod hΓ).mem_nhds ⟨hφ, hξ⟩] with q hq
  exact ⟨φ, hq.1, Γ, hΓ, hq.2, hcone, hL2⟩

/-- The Sobolev wave front set is closed in `Ω × (E \ {0})`. -/
theorem isOpen_diff_sobolevWaveFrontSet (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ T.sobolevWaveFrontSet s) := by
  have h : ((Ω : Set E) ×ˢ {0}ᶜ) \ T.sobolevWaveFrontSet s =
      ((Ω : Set E) ×ˢ {0}ᶜ) ∩ {p : E × E | T.IsMicrolocallySobolevAt s p.1 p.2} := by
    ext ⟨x, ξ⟩
    simp only [sobolevWaveFrontSet, Set.mem_sdiff, mem_inter_iff, mem_prod, mem_compl_iff,
      mem_ofPred_eq]
    tauto
  rw [h]
  exact (Ω.isOpen.prod isOpen_compl_singleton).inter (T.isOpen_setOf_isMicrolocallySobolevAt s)

/-- A distribution microlocally `H^s` at `(x, ξ)` is microlocally `H^t` there for every `t ≤ s`. -/
theorem IsMicrolocallySobolevAt.of_le {T : 𝓓'(Ω, ℂ)} {s t : ℝ} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) (hts : t ≤ s) : T.IsMicrolocallySobolevAt t x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL2⟩ := h
  refine ⟨φ, hφ, Γ, hΓ, hξ, hcone, lt_of_le_of_lt (lintegral_mono fun η => ?_) hL2⟩
  gcongr
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The Sobolev wave front sets increase with the order. -/
theorem sobolevWaveFrontSet_mono (T : 𝓓'(Ω, ℂ)) : Monotone T.sobolevWaveFrontSet :=
  fun _ _ hts _ ⟨hx, hξ, hT⟩ => ⟨hx, hξ, fun h => hT (h.of_le hts)⟩

/-! ### Comparison with the wave front set -/

/-- A distribution microlocally smooth at `(x, ξ)` is microlocally `H^s` there for every `s`. -/
theorem IsMicrolocallySmoothAt.isMicrolocallySobolevAt {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySmoothAt x ξ) (s : ℝ) : T.IsMicrolocallySobolevAt s x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 h
  set K := ⌈|s|⌉₊
  set r := finrank ℝ E + 1
  obtain ⟨C, hC⟩ := hdecay (K + r)
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ _).trans (hC ξ hξ)
  refine ⟨φ, hφ, Γ, hΓ, hξ, hcone, lt_of_le_of_lt ?_
    (TauCeti.lintegral_ofReal_mul_one_add_norm_rpow_neg_sq_lt_top (μ := volume) hC0
      (by simp [r] : (finrank ℝ E : ℝ) < r))⟩
  refine (setLIntegral_mono (by fun_prop) fun η hη => ?_).trans (setLIntegral_le_lintegral _ _)
  -- On `Γ`, `⟨η⟩ ^ s ‖T (φ e_η)‖ ≤ (1 + ‖η‖) ^ K C (1 + ‖η‖) ^ (-(K + r))`.
  have ht : 0 < 1 + ‖η‖ := by positivity
  have hw : (1 + ‖η‖ ^ 2) ^ (s / 2) ≤ (1 + ‖η‖) ^ K :=
    calc (1 + ‖η‖ ^ 2) ^ (s / 2) ≤ (1 + ‖η‖ ^ 2) ^ ((K : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _))
            (by linarith [le_abs_self s, Nat.le_ceil |s|])
      _ ≤ (1 + ‖η‖) ^ K := TauCeti.one_add_norm_sq_rpow_le_one_add_norm_pow η K
  have hF : ‖T.localFourier φ η‖ ≤ C / (1 + ‖η‖) ^ (K + r) := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hC η hη
  refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) 2
  calc (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier φ η‖
      ≤ (1 + ‖η‖) ^ K * (C / (1 + ‖η‖) ^ (K + r)) := by gcongr
    _ = C * (1 + ‖η‖) ^ (-(r : ℝ)) := by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast, pow_add]
        field_simp

/-- The Sobolev wave front set of every order lies in the wave front set. -/
theorem sobolevWaveFrontSet_subset_waveFrontSet (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    T.sobolevWaveFrontSet s ⊆ T.waveFrontSet :=
  fun ⟨_, _⟩ ⟨hx, hξ, hT⟩ =>
    mem_waveFrontSet_iff.2 ⟨hx, hξ, fun h => hT (h.isMicrolocallySobolevAt s)⟩

/-- The Sobolev wave front set lies over the support of the distribution. -/
theorem sobolevWaveFrontSet_subset_dsupport (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    T.sobolevWaveFrontSet s ⊆ dsupport T ×ˢ univ :=
  (T.sobolevWaveFrontSet_subset_waveFrontSet s).trans T.waveFrontSet_subset_dsupport

/-- The zero distribution has empty Sobolev wave front sets. -/
@[simp]
theorem sobolevWaveFrontSet_zero (s : ℝ) : (0 : 𝓓'(Ω, ℂ)).sobolevWaveFrontSet s = ∅ :=
  subset_empty_iff.1 ((sobolevWaveFrontSet_subset_waveFrontSet 0 s).trans waveFrontSet_zero.le)

/-- A function smooth on `Ω` has empty Sobolev wave front sets. -/
theorem sobolevWaveFrontSet_ofFun_eq_empty {f : E → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (s : ℝ) :
    (ofFun Ω f volume ⊤).sobolevWaveFrontSet s = ∅ :=
  subset_empty_iff.1 ((sobolevWaveFrontSet_subset_waveFrontSet _ s).trans
    (waveFrontSet_ofFun_eq_empty hf).le)

/-! ### Scalar multiples -/

/-- A scalar multiple of `T` is microlocally `H^s` wherever `T` is. -/
theorem IsMicrolocallySobolevAt.smul {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) (c : ℂ) : (c • T).IsMicrolocallySobolevAt s x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hL2⟩ := h
  refine ⟨φ, hφ, Γ, hΓ, hξ, hcone, ?_⟩
  have heq (η : E) : ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖(c • T).localFourier φ η‖) ^ 2 =
      ENNReal.ofReal (‖c‖ ^ 2) *
        ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier φ η‖) ^ 2 := by
    rw [localFourier_smul, norm_mul, mul_left_comm, ENNReal.ofReal_mul (norm_nonneg c), mul_pow,
      ENNReal.ofReal_pow (norm_nonneg c)]
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL2

/-- A scalar multiple of `T` has Sobolev wave front set contained in that of `T`. -/
theorem sobolevWaveFrontSet_smul_subset (c : ℂ) (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    (c • T).sobolevWaveFrontSet s ⊆ T.sobolevWaveFrontSet s :=
  fun _ ⟨hx, hξ, hT⟩ => ⟨hx, hξ, fun h => hT (h.smul c)⟩

/-- A nonzero scalar multiple of `T` has the same Sobolev wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_smul {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    (c • T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet s := by
  refine (sobolevWaveFrontSet_smul_subset c T s).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ hc] using sobolevWaveFrontSet_smul_subset c⁻¹ (c • T) s

/-- The negative of `T` has the same Sobolev wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_neg (T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    (-T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet s := by
  rw [← neg_one_smul ℂ T, sobolevWaveFrontSet_smul (neg_ne_zero.2 one_ne_zero)]

/-! ### Independence of the cutoff and sums -/

/-- **Independence of the cutoff.** If `T` is microlocally `H^s` at `(x, ξ)`, then there are a
neighbourhood `U` of `x` and an open cone `Γ` containing `ξ` such that for *every* test function
`ψ` supported in `U`, the localized Fourier transform of `T` with cutoff `ψ` is square integrable
against the weight `(1 + ‖η‖ ^ 2) ^ s` on `Γ`. -/
theorem IsMicrolocallySobolevAt.exists_nhds_cone {T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E}
    (h : T.IsMicrolocallySobolevAt s x ξ) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
        ∫⁻ η in Γ, ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) * ‖T.localFourier ψ η‖) ^ 2 < ∞ := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hL2⟩ := h
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  obtain ⟨U, hU, hUψ⟩ := exists_nhds_forall_exists_contDiff_eq_mul φ hφx
  refine ⟨U, hU, Γ', hΓ'o, hξ', hcone', fun ψ hψ => ?_⟩
  -- The localized Fourier transform with cutoff `ψ = φ g` is a rapidly decreasing superposition of
  -- translates of the one with cutoff `φ`.
  obtain ⟨g, hg, hψg⟩ := hUψ ψ hψ
  obtain ⟨L, a, ha, hsum⟩ := exists_hasSum_localFourier_of_eq_mul T hg.contDiffOn hψg
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T φ
  exact TauCeti.setLIntegral_ofReal_one_add_norm_sq_rpow_mul_norm_sq_lt_top_of_hasSum
    (v := fun m : L => (m : E)) ha (contDiff_localFourier T φ).continuous.norm.measurable hF
    hΓ.measurableSet hc hΓ' s hL2 fun η _ => by simpa only [smul_eq_mul] using hsum η

/-- The sum of two distributions microlocally `H^s` at `(x, ξ)` is microlocally `H^s` there. -/
theorem IsMicrolocallySobolevAt.add {S T : 𝓓'(Ω, ℂ)} {s : ℝ} {x ξ : E}
    (hS : S.IsMicrolocallySobolevAt s x ξ) (hT : T.IsMicrolocallySobolevAt s x ξ) :
    (S + T).IsMicrolocallySobolevAt s x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySobolevAt_iff.1 hS
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdS⟩ := hS.exists_nhds_cone
  obtain ⟨V, hV, Γ', hΓ', hξ', hcone', hdT⟩ := hT.exists_nhds_cone
  -- A cutoff supported in `U ∩ V` serves for both distributions, on the cone `Γ ∩ Γ'`.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU hV) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  refine isMicrolocallySobolevAt_iff.2 ⟨ψ, by simp [hψx], Γ ∩ Γ', hΓ.inter hΓ', ⟨hξ, hξ'⟩,
    fun t ht η hη => ⟨hcone t ht η hη.1, hcone' t ht η hη.2⟩, ?_⟩
  have hS2 := (lintegral_mono_set (μ := volume) (inter_subset_left (t := Γ'))).trans_lt
    (hdS ψ (hψ.trans (inter_subset_left.trans inter_subset_left)))
  have hT2 := (lintegral_mono_set (μ := volume) (inter_subset_right (s := Γ))).trans_lt
    (hdT ψ (hψ.trans (inter_subset_left.trans inter_subset_right)))
  set w : E → ℝ := fun η => (1 + ‖η‖ ^ 2) ^ (s / 2)
  have hw : Continuous w :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const fun η =>
      Or.inl (by positivity : (1 : ℝ) + ‖η‖ ^ 2 ≠ 0)
  have hmeas : Measurable fun η => ENNReal.ofReal (w η * ‖S.localFourier ψ η‖) ^ 2 :=
    ((hw.mul (contDiff_localFourier S ψ).continuous.norm).measurable.ennreal_ofReal).pow_const 2
  calc ∫⁻ η in Γ ∩ Γ', ENNReal.ofReal (w η * ‖(S + T).localFourier ψ η‖) ^ 2
      ≤ ∫⁻ η in Γ ∩ Γ', 2 * (ENNReal.ofReal (w η * ‖S.localFourier ψ η‖) ^ 2 +
          ENNReal.ofReal (w η * ‖T.localFourier ψ η‖) ^ 2) := by
        refine lintegral_mono fun η => (pow_le_pow_left' ?_ 2).trans (ENNReal.add_sq_le _ _)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← mul_add, localFourier_add]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity))
    _ = 2 * ((∫⁻ η in Γ ∩ Γ', ENNReal.ofReal (w η * ‖S.localFourier ψ η‖) ^ 2) +
          ∫⁻ η in Γ ∩ Γ', ENNReal.ofReal (w η * ‖T.localFourier ψ η‖) ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_add_left hmeas]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofNat_lt_top (ENNReal.add_lt_top.2 ⟨hS2, hT2⟩)

/-- The Sobolev wave front set of a sum lies in the union of the Sobolev wave front sets. -/
theorem sobolevWaveFrontSet_add_subset (S T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    (S + T).sobolevWaveFrontSet s ⊆ S.sobolevWaveFrontSet s ∪ T.sobolevWaveFrontSet s := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, h⟩ := mem_sobolevWaveFrontSet_iff.1 hp
  by_contra hST
  simp only [mem_union, mem_sobolevWaveFrontSet_iff, not_or, not_and, not_not] at hST
  exact h ((hST.1 hx hξ).add (hST.2 hx hξ))

/-- The Sobolev wave front set of a difference lies in the union of the Sobolev wave front sets. -/
theorem sobolevWaveFrontSet_sub_subset (S T : 𝓓'(Ω, ℂ)) (s : ℝ) :
    (S - T).sobolevWaveFrontSet s ⊆ S.sobolevWaveFrontSet s ∪ T.sobolevWaveFrontSet s := by
  simpa [sub_eq_add_neg] using sobolevWaveFrontSet_add_subset S (-T) s

/-- The Sobolev wave front set of a finite sum lies in the union of the Sobolev wave front sets. -/
theorem sobolevWaveFrontSet_sum_subset {ι : Type*} (u : Finset ι) (T : ι → 𝓓'(Ω, ℂ)) (s : ℝ) :
    (∑ i ∈ u, T i).sobolevWaveFrontSet s ⊆ ⋃ i ∈ u, (T i).sobolevWaveFrontSet s := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    exact (sobolevWaveFrontSet_add_subset _ _ s).trans (union_subset_union_right _ ih)

/-! ### The point mass -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The weighted square of the localized Fourier transform of the point mass at `x₀` is
`‖φ x₀‖ ^ 2 (1 + ‖η‖ ^ 2) ^ s`. -/
private theorem ofReal_mul_norm_localFourier_delta_sq (x₀ : E) (φ : 𝓓(Ω, ℂ)) (s : ℝ) (η : E) :
    ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ (s / 2) *
        ‖(mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).localFourier φ η‖) ^ 2 =
      ENNReal.ofReal (‖φ x₀‖ ^ 2) * ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ s) := by
  have hw : ((1 + ‖η‖ ^ 2) ^ (s / 2)) ^ 2 = (1 + ‖η‖ ^ 2) ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [localFourier_delta, norm_mul, Circle.norm_coe, mul_one,
    ← ENNReal.ofReal_pow (by positivity), mul_pow, hw, mul_comm,
    ENNReal.ofReal_mul (sq_nonneg _)]

/-- Below the order `-n / 2`, in dimension `n`, the point mass is microlocally `H^s` everywhere:
its Sobolev wave front set is empty. -/
theorem sobolevWaveFrontSet_delta_of_lt (x₀ : E) {s : ℝ} (hs : 2 * s < -(finrank ℝ E : ℝ)) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).sobolevWaveFrontSet s = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun ⟨x, ξ⟩ ⟨hx, _, hT⟩ => hT ?_
  obtain ⟨φ, -, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) (Ω.isOpen.mem_nhds hx)
    subset_rfl (1 : ℂ)
  refine ⟨φ, by simp [hφx], univ, isOpen_univ, mem_univ ξ, fun _ _ _ _ => mem_univ _, ?_⟩
  simp_rw [ofReal_mul_norm_localFourier_delta_sq, Measure.restrict_univ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- `(1 + ‖η‖ ^ 2) ^ s` is integrable for `2 s < -n`.
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := E) (r := -(2 * s))
    (by linarith)
  simp only [neg_neg, mul_div_cancel_left₀ s two_ne_zero] at hint
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint.lintegral_lt_top

/-- From the order `-n / 2` on, in dimension `n`, the Sobolev wave front set of the point mass at
`x₀ ∈ Ω` is `{x₀} × (E \ {0})`, its whole wave front set. -/
theorem sobolevWaveFrontSet_delta_of_le {x₀ : E} (hx₀ : x₀ ∈ Ω) {s : ℝ}
    (hs : -(finrank ℝ E : ℝ) ≤ 2 * s) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).sobolevWaveFrontSet s = {x₀} ×ˢ {0}ᶜ := by
  refine subset_antisymm ((sobolevWaveFrontSet_subset_waveFrontSet _ s).trans
    (waveFrontSet_delta hx₀).le) ?_
  rintro ⟨x, ξ⟩ ⟨hx, hξ⟩
  rw [mem_singleton_iff] at hx
  subst hx
  refine ⟨hx₀, hξ, fun ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hL2⟩ => ?_⟩
  -- On every open cone the weight `(1 + ‖η‖ ^ 2) ^ s` has infinite integral.
  simp_rw [ofReal_mul_norm_localFourier_delta_sq] at hL2
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    TauCeti.setLIntegral_ofReal_one_add_norm_sq_rpow_eq_top hΓ hcone hξΓ hξ hs,
    ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne'] at hL2
  exact lt_irrefl _ hL2

end Distribution
