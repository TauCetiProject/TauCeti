/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Localization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The projection of the Sobolev wave front set and the local Sobolev order

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. The localized Fourier transform `η ↦ T (φ e_η)` of `Distribution.localFourier` is the
Fourier transform of the compactly supported distribution `φ T`, so `T` is `H^s` near a point `x`
when some cutoff `φ` with `φ x ≠ 0` makes `η ↦ ⟨η⟩ ^ s T (φ e_η)` square integrable on all of `E`,
where `⟨η⟩ ^ s = (1 + ‖η‖ ^ 2) ^ (s / 2)` (`Distribution.IsLocallySobolevAt`). The points of `Ω`
near which `T` is not `H^s` form the **`H^s` singular support**
`Distribution.sobolevSingularSupport s T`, a relatively closed subset of `Ω`.

This file proves the `H^s` counterparts of two basic facts about the wave front set.

* **The projection of the `H^s` wave front set is the `H^s` singular support**
  (`Distribution.fst_image_sobolevWaveFrontSet`): `T` is `H^s` near `x` exactly when it is
  microlocally `H^s` at `x` in every direction. As for the wave front set
  (`Distribution.fst_image_waveFrontSet`), finitely many of the cones on which the localized
  Fourier transforms are square integrable cover the unit sphere of directions
  (`Distribution.exists_nhds_forall_memLp_of_forall_isMicrolocallySobolevAt`). No Fourier
  inversion is needed here, since square integrability on all of `E` is already the definition of
  being `H^s` near `x`.
* **Every distribution has a finite Sobolev order locally**
  (`Distribution.exists_forall_isLocallySobolevAt`): for every compact `K ⊆ Ω` there is an order
  `s` such that `T` is `H^s` near every point of `K`. Indeed, for a cutoff `φ` equal to one near
  `K`, the localized Fourier transform `η ↦ T (φ e_η)` grows at most polynomially
  (`Distribution.exists_norm_localFourier_le`), so a sufficiently negative weight makes it square
  integrable. This is the local finite negative order on which the distributional form of
  elliptic regularity rests: an estimate on the Sobolev scale applies to every distribution near
  every compact set.

The point mass in dimension `d > 0` has `H^s` singular support `{x₀}` for `s ≥ -d / 2` and is
`H^s` everywhere for `s < -d / 2` (`Distribution.sobolevSingularSupport_delta`,
`Distribution.sobolevSingularSupport_delta_eq_empty`).

## Main declarations

* `Distribution.IsLocallySobolevAt s T x`: `T` is `H^s` near `x`.
* `Distribution.sobolevSingularSupport s T`: the `H^s` singular support.

## Main results

* `Distribution.isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt`: `T` is `H^s` near a point
  `x ∈ Ω` exactly when it is microlocally `H^s` at `x` in every nonzero direction.
* `Distribution.fst_image_sobolevWaveFrontSet`: the projection of the `H^s` wave front set is the
  `H^s` singular support.
* `Distribution.isOpen_diff_sobolevSingularSupport`, `Distribution.sobolevSingularSupport_mono`,
  `Distribution.sobolevSingularSupport_subset_singularSupport`: the `H^s` singular support is
  closed in `Ω`, grows with `s`, and lies in the singular support.
* `Distribution.sobolevSingularSupport_add_subset`,
  `Distribution.sobolevSingularSupport_smulLeftCLM_subset`: sums and smooth multiples.
* `Distribution.exists_forall_isLocallySobolevAt`,
  `Distribution.exists_disjoint_sobolevSingularSupport`: the local finite Sobolev order.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Proposition 8.1.3 (the projection of the wave front set, whose `H^s` analogue
  is proved here) and Theorem 7.3.1 (the Paley–Wiener–Schwartz bound behind the local finite
  order).
-/

public section

noncomputable section

open Complex Filter Metric Module Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-! ### Being `H^s` near a point -/

/-- A complex distribution `T` is **`H^s` near `x`** if some complex test function `φ` with
`φ x ≠ 0` makes the weighted localized Fourier transform
`η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) localFourier T φ η` square integrable on all of `E`: the Fourier
description of `φ T ∈ H^s`. -/
def IsLocallySobolevAt (s : ℝ) (T : 𝓓'(Ω, ℂ)) (x : E) : Prop :=
  ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 volume

/-- Unfolds `IsLocallySobolevAt` into its cutoff and integrability witnesses. -/
theorem isLocallySobolevAt_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E} :
    T.IsLocallySobolevAt s x ↔ ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 volume :=
  Iff.rfl

/-- A distribution can only be `H^s` near points of its domain. -/
theorem IsLocallySobolevAt.mem {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E} (h : T.IsLocallySobolevAt s x) :
    x ∈ Ω := by
  obtain ⟨φ, hφ, -⟩ := h
  exact φ.tsupport_subset (subset_tsupport _ hφ)

/-- A distribution that is `H^s` near `x` is microlocally `H^s` at `x` in every direction. -/
theorem IsLocallySobolevAt.isMicrolocallySobolevAt {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : T.IsLocallySobolevAt s x) (ξ : E) : T.IsMicrolocallySobolevAt s x ξ := by
  obtain ⟨φ, hφ, hL⟩ := h
  exact isMicrolocallySobolevAt_of_memLp hφ hL ξ

/-- The set of points near which a distribution is `H^s` is open. -/
theorem isOpen_setOf_isLocallySobolevAt (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    IsOpen {x : E | T.IsLocallySobolevAt s x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨φ, hφ, hL⟩ ↦ ?_
  filter_upwards [(isOpen_ne_fun φ.continuous continuous_const).mem_nhds hφ] with y hy
  exact ⟨φ, hy, hL⟩

/-- **Compactness of the sphere of directions.** If `T` is microlocally `H^s` at `(x, ξ)` for every
`ξ ≠ 0`, then there is a neighbourhood `U` of `x` such that for every cutoff `ψ` supported in `U`
the weighted localized Fourier transform of `T` is square integrable on all of `E`. -/
theorem exists_nhds_forall_memLp_of_forall_isMicrolocallySobolevAt {s : ℝ} {T : 𝓓'(Ω, ℂ)}
    {x : E} (h : ∀ ξ, ξ ≠ 0 → T.IsMicrolocallySobolevAt s x ξ) :
    ∃ U ∈ 𝓝 x, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 volume := by
  classical
  -- For each unit direction, a neighbourhood of `x` and an open cone with square integrability.
  choose U hU Γ hΓ hξΓ hcone hL using fun ξ : sphere (0 : E) 1 ↦
    (h ξ (ne_zero_of_mem_unit_sphere ξ)).exists_nhds_cone
  -- Finitely many of the cones cover the unit sphere.
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover Γ hΓ
    fun ζ hζ ↦ mem_iUnion.2 ⟨⟨ζ, hζ⟩, hξΓ _⟩
  refine ⟨⋂ ξ ∈ t, U ξ, (biInter_finset_mem t).2 fun ξ _ ↦ hU ξ, fun ψ hψ ↦ ?_⟩
  -- Together with the origin, the finitely many cones cover `E`.
  have hcover : univ ⊆ ⋃ i : Option t, i.elim {0} fun ξ ↦ Γ ξ := by
    intro η _
    rcases eq_or_ne η 0 with rfl | hη
    · exact mem_iUnion.2 ⟨none, rfl⟩
    have hη' : 0 < ‖η‖ := norm_pos_iff.2 hη
    obtain ⟨ξ, hξt, hηξ⟩ := mem_iUnion₂.1 (ht (show ‖η‖⁻¹ • η ∈ sphere (0 : E) 1 by
      simp [norm_smul, inv_mul_cancel₀ hη'.ne']))
    refine mem_iUnion.2 ⟨some ⟨ξ, hξt⟩, ?_⟩
    simpa [smul_smul, mul_inv_cancel₀ hη'.ne'] using hcone ξ ‖η‖ hη' _ hηξ
  rw [← Measure.restrict_univ (μ := volume)]
  refine MemLp.restrict_of_subset_iUnion hcover fun i ↦ ?_
  rcases i with _ | ⟨ξ, hξ⟩
  · -- At the origin the integrand is bounded, and the singleton has finite measure.
    rw [Option.elim_none]
    have : IsFiniteMeasure (volume.restrict ({0} : Set E)) :=
      isFiniteMeasure_restrict.2 (measure_singleton_lt_top (μ := volume)).ne
    refine MemLp.of_bound (((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)).1
      |>.continuous.smul (T.continuous_localFourier ψ)).aestronglyMeasurable)
      ‖(1 + ‖(0 : E)‖ ^ 2) ^ (s / 2) • T.localFourier ψ 0‖ ?_
    filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : E))] with η hη
    rw [mem_singleton_iff.1 hη]
  · exact hL ξ ψ (hψ.trans (biInter_subset_of_mem hξ))

/-- A complex distribution is `H^s` near a point `x ∈ Ω` exactly when it is microlocally `H^s` at
`x` in every nonzero direction. -/
theorem isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ Ω) :
    T.IsLocallySobolevAt s x ↔ ∀ ξ, ξ ≠ 0 → T.IsMicrolocallySobolevAt s x ξ := by
  refine ⟨fun h ξ _ ↦ h.isMicrolocallySobolevAt ξ, fun h ↦ ?_⟩
  obtain ⟨U, hU, hL⟩ := exists_nhds_forall_memLp_of_forall_isMicrolocallySobolevAt h
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  exact ⟨ψ, by simp [hψx], hL ψ (hψ.trans inter_subset_left)⟩

/-- Being `H^s` near `x` implies being `H^t` near `x` for every `t ≤ s`. -/
theorem IsLocallySobolevAt.mono {s t : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : T.IsLocallySobolevAt s x) (hts : t ≤ s) : T.IsLocallySobolevAt t x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt h.mem).2 fun ξ _ ↦
    (h.isMicrolocallySobolevAt ξ).mono hts

/-! ### The `H^s` singular support -/

/-- The **`H^s` singular support** of a complex distribution `T` on `Ω`: the points of `Ω` near
which `T` is not `H^s`. -/
def sobolevSingularSupport (s : ℝ) (T : 𝓓'(Ω, ℂ)) : Set E :=
  {x | x ∈ Ω ∧ ¬ T.IsLocallySobolevAt s x}

@[simp]
theorem mem_sobolevSingularSupport_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E} :
    x ∈ T.sobolevSingularSupport s ↔ x ∈ Ω ∧ ¬ T.IsLocallySobolevAt s x :=
  Iff.rfl

/-- A point of `Ω` lies outside the `H^s` singular support of `T` exactly when `T` is `H^s` near
it. -/
theorem notMem_sobolevSingularSupport_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω) :
    x ∉ T.sobolevSingularSupport s ↔ T.IsLocallySobolevAt s x := by
  simp [hx]

/-- The `H^s` singular support lies in `Ω`. -/
theorem sobolevSingularSupport_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevSingularSupport s ⊆ Ω :=
  fun _ hx ↦ hx.1

/-- The `H^s` singular support is closed in `Ω`. -/
theorem isOpen_diff_sobolevSingularSupport (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    IsOpen ((Ω : Set E) \ T.sobolevSingularSupport s) := by
  have h : (Ω : Set E) \ T.sobolevSingularSupport s =
      (Ω : Set E) ∩ {x : E | T.IsLocallySobolevAt s x} := by
    ext x
    simp only [sobolevSingularSupport, Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [h]
  exact Ω.isOpen.inter (T.isOpen_setOf_isLocallySobolevAt s)

/-- **The projection of the `H^s` wave front set is the `H^s` singular support**, the `H^s`
analogue of Hörmander I, Proposition 8.1.3. -/
theorem fst_image_sobolevWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    Prod.fst '' T.sobolevWaveFrontSet s = T.sobolevSingularSupport s := by
  ext x
  constructor
  · rintro ⟨⟨x, ξ⟩, hp, rfl⟩
    obtain ⟨hx, -, hT⟩ := mem_sobolevWaveFrontSet_iff.1 hp
    exact ⟨hx, fun h ↦ hT (h.isMicrolocallySobolevAt ξ)⟩
  · rintro ⟨hx, hT⟩
    obtain ⟨ξ, hξ, hξT⟩ := not_forall₂.1 fun h ↦
      hT ((isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hx).2 h)
    exact ⟨(x, ξ), mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, hξT⟩, rfl⟩

/-- A complex distribution has empty `H^s` singular support exactly when it has empty `H^s` wave
front set. -/
theorem sobolevSingularSupport_eq_empty_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} :
    T.sobolevSingularSupport s = ∅ ↔ T.sobolevWaveFrontSet s = ∅ := by
  rw [← fst_image_sobolevWaveFrontSet, image_eq_empty]

/-- The `H^s` singular support grows with `s`. -/
theorem sobolevSingularSupport_mono {s t : ℝ} (hts : t ≤ s) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevSingularSupport t ⊆ T.sobolevSingularSupport s :=
  fun _ ⟨hx, hT⟩ ↦ ⟨hx, fun h ↦ hT (h.mono hts)⟩

/-- The `H^s` singular support lies in the singular support. -/
theorem sobolevSingularSupport_subset_singularSupport (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevSingularSupport s ⊆ T.singularSupport := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_waveFrontSet]
  exact image_mono (sobolevWaveFrontSet_subset_waveFrontSet s T)

/-- The `H^s` singular support of a sum lies in the union of the `H^s` singular supports. -/
theorem sobolevSingularSupport_add_subset (s : ℝ) (S T : 𝓓'(Ω, ℂ)) :
    (S + T).sobolevSingularSupport s ⊆
      S.sobolevSingularSupport s ∪ T.sobolevSingularSupport s := by
  simp only [← fst_image_sobolevWaveFrontSet, ← image_union]
  exact image_mono (sobolevWaveFrontSet_add_subset s S T)

/-- The `H^s` singular support of a smooth multiple `g T` lies in the `H^s` singular support of
`T`, over the support of `g`. -/
theorem sobolevSingularSupport_smulLeftCLM_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).sobolevSingularSupport s ⊆ T.sobolevSingularSupport s ∩ tsupport g := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet]
  rintro _ ⟨⟨x, ξ⟩, hp, rfl⟩
  obtain ⟨hT, hx, -⟩ := sobolevWaveFrontSet_smulLeftCLM_subset s T hg hp
  exact ⟨⟨(x, ξ), hT, rfl⟩, hx⟩

/-! ### The local Sobolev order -/

/-- **Distributions have finite Sobolev order locally.** For every compact set `K ⊆ Ω` there is an
order `s` such that `T` is `H^s` near every point of `K`. -/
theorem exists_forall_isLocallySobolevAt (T : 𝓓'(Ω, ℂ)) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ s : ℝ, ∀ x ∈ K, T.IsLocallySobolevAt s x := by
  -- A cutoff equal to one near `K`.
  obtain ⟨χ, hχ1, -⟩ := exists_eventually_eq_one (n := ⊤) hK hKΩ
  let φ : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
  have hφ (y : E) : φ y = χ y := by simp [φ]
  -- The localized Fourier transform with cutoff `φ` grows at most like `(1 + ‖η‖) ^ k`.
  obtain ⟨C, k, hC⟩ := exists_norm_localFourier_le T φ
  set d : ℝ := (finrank ℝ E : ℝ)
  refine ⟨-((k : ℝ) + d + 1), fun x hx ↦ ⟨φ, by simp [hφ, hχ1.self_of_nhdsSet x hx], ?_⟩⟩
  have hmeas : AEStronglyMeasurable
      (fun η ↦ (1 + ‖η‖ ^ 2) ^ (-((k : ℝ) + d + 1) / 2) • T.localFourier φ η) volume :=
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E _).1.continuous.smul
      (T.continuous_localFourier φ)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine ((integrable_rpow_neg_one_add_norm_sq (μ := volume) (r := 2 * d + 2)
    (by linarith [(finrank ℝ E).cast_nonneg (α := ℝ)])).const_mul ((C * 2 ^ k) ^ 2)).mono'
    (hmeas.norm.pow 2) (.of_forall fun η ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  -- `⟨η⟩ ^ s (1 + ‖η‖) ^ k ≤ 2 ^ k ⟨η⟩ ^ (s + k)`, with `s + k = -(d + 1)`.
  have hw : 0 < 1 + ‖η‖ ^ 2 := by positivity
  have hk : (1 + ‖η‖) ^ k ≤ 2 ^ k * (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2) := by
    simpa [one_add_one_eq_two] using TauCeti.one_add_mul_norm_pow_le zero_le_one η k
  have hC0 : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans_eq (by simp))
  have hbound : ‖(1 + ‖η‖ ^ 2) ^ (-((k : ℝ) + d + 1) / 2) • T.localFourier φ η‖ ≤
      C * 2 ^ k * (1 + ‖η‖ ^ 2) ^ (-(2 * d + 2) / 2 / 2) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (1 + ‖η‖ ^ 2) ^ (-((k : ℝ) + d + 1) / 2) * ‖T.localFourier φ η‖
        ≤ (1 + ‖η‖ ^ 2) ^ (-((k : ℝ) + d + 1) / 2) *
            (C * (2 ^ k * (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2))) := by
          gcongr
          exact (hC η).trans (by gcongr)
      _ = C * 2 ^ k * ((1 + ‖η‖ ^ 2) ^ (-((k : ℝ) + d + 1) / 2) *
            (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2)) := by ring
      _ = C * 2 ^ k * (1 + ‖η‖ ^ 2) ^ (-(2 * d + 2) / 2 / 2) := by
          rw [← Real.rpow_add hw]
          congr 2
          ring
  calc ‖(1 + ‖η‖ ^ 2) ^ (-((k : ℝ) + d + 1) / 2) • T.localFourier φ η‖ ^ 2
      ≤ (C * 2 ^ k * (1 + ‖η‖ ^ 2) ^ (-(2 * d + 2) / 2 / 2)) ^ 2 := by
        gcongr
    _ = (C * 2 ^ k) ^ 2 * (1 + ‖η‖ ^ 2) ^ (-(2 * d + 2) / 2) := by
        rw [mul_pow, Real.rpow_div_two_sq hw.le]

/-- **Distributions have finite Sobolev order locally**, in terms of the `H^s` singular support:
every compact set `K ⊆ Ω` is disjoint from the `H^s` singular support for some order `s`. -/
theorem exists_disjoint_sobolevSingularSupport (T : 𝓓'(Ω, ℂ)) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ s : ℝ, Disjoint K (T.sobolevSingularSupport s) := by
  obtain ⟨s, hs⟩ := T.exists_forall_isLocallySobolevAt hK hKΩ
  exact ⟨s, disjoint_left.2 fun x hx hxs ↦ hxs.2 (hs x hx)⟩

/-! ### Point masses -/

/-- **Point masses are `H^s` below the critical order.** In dimension `d`, the point mass at `x₀`
has empty `H^s` singular support for `s < -d / 2`. -/
theorem sobolevSingularSupport_delta_eq_empty {s : ℝ} (hs : (finrank ℝ E : ℝ) < -2 * s)
    (x₀ : E) : (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).sobolevSingularSupport s = ∅ :=
  sobolevSingularSupport_eq_empty_iff.2 (sobolevWaveFrontSet_delta_eq_empty hs x₀)

/-- **The `H^s` singular support of a point mass.** In dimension `d > 0`, the point mass at
`x₀ ∈ Ω` has `H^s` singular support `{x₀}` for `s ≥ -d / 2`. -/
theorem sobolevSingularSupport_delta [Nontrivial E] {s : ℝ} (hs : -2 * s ≤ finrank ℝ E) {x₀ : E}
    (hx₀ : x₀ ∈ Ω) : (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).sobolevSingularSupport s = {x₀} := by
  rw [← fst_image_sobolevWaveFrontSet, sobolevWaveFrontSet_delta hs hx₀]
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  exact fst_image_prod _ ⟨ξ, hξ⟩

end Distribution
