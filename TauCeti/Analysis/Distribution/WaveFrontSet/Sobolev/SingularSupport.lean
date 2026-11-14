/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Localization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Lp

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
  `s` such that `T` is `H^s` near every point of `K`. Indeed, for every cutoff `φ` the localized
  Fourier transform `η ↦ T (φ e_η)` grows at most polynomially
  (`Distribution.exists_norm_localFourier_le`), so a sufficiently negative weight makes it square
  integrable (`Distribution.exists_memLp_one_add_norm_sq_rpow_smul_localFourier`); we apply this to
  a cutoff equal to one near `K`. This is the local finite
  negative order on which the distributional form of elliptic regularity rests: an estimate on the
  Sobolev scale applies to every distribution near every compact set.

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
* `Distribution.IsLocallySobolevAt.add`, `Distribution.IsLocallySobolevAt.smulLeftCLM`,
  `Distribution.isLocallySobolevAt_restrictCLM_iff`: being `H^s` near a point is preserved by
  sums, smooth multiples and restriction.
* `Distribution.sobolevSingularSupport_restrictCLM`,
  `Distribution.sobolevSingularSupport_add_subset`,
  `Distribution.sobolevSingularSupport_smulLeftCLM_subset`: restriction, sums and smooth multiples.
* `Distribution.exists_memLp_one_add_norm_sq_rpow_smul_localFourier`,
  `Distribution.exists_forall_isLocallySobolevAt`,
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
  -- Finitely many of the cones cover the nonzero vectors.
  obtain ⟨t, ht⟩ := TauCeti.exists_finset_compl_singleton_subset_biUnion hΓ hξΓ hcone
  refine ⟨⋂ ξ ∈ t, U ξ, (biInter_finset_mem t).2 fun ξ _ ↦ hU ξ, fun ψ hψ ↦ ?_⟩
  -- Together with the origin, the finitely many cones cover `E`.
  have hcover : univ ⊆ ⋃ i : Option t, i.elim {0} fun ξ ↦ Γ ξ := by
    intro η _
    rcases eq_or_ne η 0 with rfl | hη
    · exact mem_iUnion.2 ⟨none, rfl⟩
    obtain ⟨ξ, hξt, hηξ⟩ := mem_iUnion₂.1 (ht hη)
    exact mem_iUnion.2 ⟨some ⟨ξ, hξt⟩, hηξ⟩
  rw [← Measure.restrict_univ (μ := volume)]
  refine MemLp.restrict_of_subset_iUnion hcover fun i ↦ ?_
  rcases i with _ | ⟨ξ, hξ⟩
  · -- The singleton at the origin carries a finite multiple of a point mass.
    rw [Option.elim_none, Measure.restrict_singleton]
    exact (memLp_dirac eNorm_lt_top).smul_measure measure_singleton_lt_top.ne
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

/-- **Cutoff independence.** If `T` is `H^s` near `x`, then some neighbourhood `U` of `x` makes the
weighted localized Fourier transform of `T` square integrable for every cutoff supported in `U`. -/
theorem IsLocallySobolevAt.exists_nhds {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : T.IsLocallySobolevAt s x) :
    ∃ U ∈ 𝓝 x, ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier ψ η) 2 volume :=
  exists_nhds_forall_memLp_of_forall_isMicrolocallySobolevAt fun ξ _ ↦
    h.isMicrolocallySobolevAt ξ

/-- The zero distribution is `H^s` near every point of its domain. -/
@[simp]
theorem isLocallySobolevAt_zero_iff {s : ℝ} {x : E} :
    (0 : 𝓓'(Ω, ℂ)).IsLocallySobolevAt s x ↔ x ∈ Ω := by
  refine ⟨IsLocallySobolevAt.mem, fun hx ↦
    (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hx).2 fun ξ hξ ↦ ?_⟩
  by_contra h
  simpa using mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, h⟩

/-- A scalar multiple of a distribution `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.smul {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : T.IsLocallySobolevAt s x) (c : ℂ) : (c • T).IsLocallySobolevAt s x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt h.mem).2 fun ξ _ ↦
    (h.isMicrolocallySobolevAt ξ).smul c

/-- A nonzero scalar multiple of `T` is `H^s` near `x` exactly when `T` is. -/
theorem isLocallySobolevAt_smul_iff {s : ℝ} {c : ℂ} (hc : c ≠ 0) {T : 𝓓'(Ω, ℂ)} {x : E} :
    (c • T).IsLocallySobolevAt s x ↔ T.IsLocallySobolevAt s x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul c⁻¹, fun h ↦ h.smul c⟩

/-- The negative of `T` is `H^s` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallySobolevAt_neg_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E} :
    (-T).IsLocallySobolevAt s x ↔ T.IsLocallySobolevAt s x := by
  rw [← neg_one_smul ℂ T, isLocallySobolevAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

/-- The sum of two distributions `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.add {s : ℝ} {S T : 𝓓'(Ω, ℂ)} {x : E}
    (hS : S.IsLocallySobolevAt s x) (hT : T.IsLocallySobolevAt s x) :
    (S + T).IsLocallySobolevAt s x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hS.mem).2 fun ξ _ ↦
    (hS.isMicrolocallySobolevAt ξ).add (hT.isMicrolocallySobolevAt ξ)

/-- The difference of two distributions `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.sub {s : ℝ} {S T : 𝓓'(Ω, ℂ)} {x : E}
    (hS : S.IsLocallySobolevAt s x) (hT : T.IsLocallySobolevAt s x) :
    (S - T).IsLocallySobolevAt s x := by
  rw [sub_eq_add_neg]
  exact hS.add (isLocallySobolevAt_neg_iff.2 hT)

/-- The complex conjugate of `T` is `H^s` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallySobolevAt_conj_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E} :
    (mapCLM conjCLE.toContinuousLinearMap T).IsLocallySobolevAt s x ↔
      T.IsLocallySobolevAt s x := by
  by_cases hx : x ∈ Ω
  · simp only [isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hx,
      isMicrolocallySobolevAt_conj_iff]
    exact ⟨fun h ξ hξ ↦ by simpa using h (-ξ) (neg_ne_zero.2 hξ),
      fun h ξ hξ ↦ h (-ξ) (neg_ne_zero.2 hξ)⟩
  · exact iff_of_false (fun h ↦ hx h.mem) fun h ↦ hx h.mem

section SmulLeft

variable {g : E → ℝ}

/-- A smooth multiple `g T` of a distribution `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.smulLeftCLM {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (h : T.IsLocallySobolevAt s x) (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).IsLocallySobolevAt s x :=
  (isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt h.mem).2 fun ξ _ ↦
    (h.isMicrolocallySobolevAt ξ).smulLeftCLM hg

/-- Where `g` does not vanish, a smooth multiple `g T` is `H^s` near `x` exactly when `T` is. -/
theorem isLocallySobolevAt_smulLeftCLM_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hg : ContDiff ℝ ∞ g) (hx : g x ≠ 0) :
    (smulLeftCLM hg T).IsLocallySobolevAt s x ↔ T.IsLocallySobolevAt s x := by
  by_cases hxΩ : x ∈ Ω
  · simp only [isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hxΩ,
      isMicrolocallySobolevAt_smulLeftCLM_iff hg hx]
  · exact iff_of_false (fun h ↦ hxΩ h.mem) fun h ↦ hxΩ h.mem

end SmulLeft

/-- At a point of an open subset `Ω' ≤ Ω`, the restriction `T|_{Ω'}` is `H^s` near `x` exactly
when `T` is. -/
theorem isLocallySobolevAt_restrictCLM_iff {Ω' : Opens E} (h : Ω' ≤ Ω) {s : ℝ} {T : 𝓓'(Ω, ℂ)}
    {x : E} (hx : x ∈ Ω') :
    (restrictCLM T : 𝓓'(Ω', ℂ)).IsLocallySobolevAt s x ↔ T.IsLocallySobolevAt s x := by
  simp only [isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hx,
    isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt (h hx),
    isMicrolocallySobolevAt_restrictCLM_iff h hx]

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
theorem sobolevSingularSupport_eq_empty_iff_sobolevWaveFrontSet_eq_empty {s : ℝ} {T : 𝓓'(Ω, ℂ)} :
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

/-- The `H^s` singular support lies in the support. -/
theorem sobolevSingularSupport_subset_dsupport (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    T.sobolevSingularSupport s ⊆ dsupport T :=
  (sobolevSingularSupport_subset_singularSupport s T).trans (singularSupport_subset_dsupport T)

/-- A function smooth on `Ω` has empty `H^s` singular support. -/
theorem sobolevSingularSupport_ofFun_eq_empty (s : ℝ) {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f volume ⊤).sobolevSingularSupport s = ∅ :=
  subset_empty_iff.1 (singularSupport_ofFun_eq_empty hf ▸
    sobolevSingularSupport_subset_singularSupport s _)

/-- A function smooth on `Ω` is `H^s` near every point of `Ω`. -/
theorem isLocallySobolevAt_ofFun {s : ℝ} {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f Ω) {x : E}
    (hx : x ∈ Ω) : (ofFun Ω f volume ⊤).IsLocallySobolevAt s x :=
  (notMem_sobolevSingularSupport_iff hx).1 (by simp [sobolevSingularSupport_ofFun_eq_empty s hf])

/-- The zero distribution has empty `H^s` singular support. -/
@[simp]
theorem sobolevSingularSupport_zero (s : ℝ) : (0 : 𝓓'(Ω, ℂ)).sobolevSingularSupport s = ∅ := by
  ext x
  simp

/-- A scalar multiple of `T` has `H^s` singular support contained in that of `T`. -/
theorem sobolevSingularSupport_smul_subset (s : ℝ) (c : ℂ) (T : 𝓓'(Ω, ℂ)) :
    (c • T).sobolevSingularSupport s ⊆ T.sobolevSingularSupport s :=
  fun _ ⟨hx, hT⟩ ↦ ⟨hx, fun h ↦ hT (h.smul c)⟩

/-- A nonzero scalar multiple of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_smul (s : ℝ) {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, ℂ)) :
    (c • T).sobolevSingularSupport s = T.sobolevSingularSupport s := by
  ext x
  simp [isLocallySobolevAt_smul_iff hc]

/-- The negative of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_neg (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (-T).sobolevSingularSupport s = T.sobolevSingularSupport s := by
  ext x
  simp

/-- The complex conjugate of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_conj (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (mapCLM conjCLE.toContinuousLinearMap T).sobolevSingularSupport s =
      T.sobolevSingularSupport s := by
  ext x
  simp

/-- The `H^s` singular support of a sum lies in the union of the `H^s` singular supports. -/
theorem sobolevSingularSupport_add_subset (s : ℝ) (S T : 𝓓'(Ω, ℂ)) :
    (S + T).sobolevSingularSupport s ⊆
      S.sobolevSingularSupport s ∪ T.sobolevSingularSupport s := by
  simp only [← fst_image_sobolevWaveFrontSet, ← image_union]
  exact image_mono (sobolevWaveFrontSet_add_subset s S T)

/-- The `H^s` singular support of a difference lies in the union of the `H^s` singular
supports. -/
theorem sobolevSingularSupport_sub_subset (s : ℝ) (S T : 𝓓'(Ω, ℂ)) :
    (S - T).sobolevSingularSupport s ⊆
      S.sobolevSingularSupport s ∪ T.sobolevSingularSupport s := by
  simp only [← fst_image_sobolevWaveFrontSet, ← image_union]
  exact image_mono (sobolevWaveFrontSet_sub_subset s S T)

/-- The `H^s` singular support of a finite sum lies in the union of the `H^s` singular
supports. -/
theorem sobolevSingularSupport_sum_subset (s : ℝ) {ι : Type*} (t : Finset ι)
    (T : ι → 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, T i).sobolevSingularSupport s ⊆ ⋃ i ∈ t, (T i).sobolevSingularSupport s := by
  simp only [← fst_image_sobolevWaveFrontSet, ← image_iUnion₂]
  exact image_mono (sobolevWaveFrontSet_sum_subset s t T)

/-- The `H^s` singular support of a smooth multiple `g T` lies in the `H^s` singular support of
`T`, over the support of `g`. -/
theorem sobolevSingularSupport_smulLeftCLM_subset (s : ℝ) (T : 𝓓'(Ω, ℂ)) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).sobolevSingularSupport s ⊆ T.sobolevSingularSupport s ∩ tsupport g := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet, ← image_inter_preimage,
    ← prod_univ]
  exact image_mono (sobolevWaveFrontSet_smulLeftCLM_subset s T hg)

/-- Over the points where `g` does not vanish, a smooth multiple `g T` has the same `H^s` singular
support as `T`. -/
theorem mem_sobolevSingularSupport_smulLeftCLM_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {g : E → ℝ}
    {x : E} (hg : ContDiff ℝ ∞ g) (hx : g x ≠ 0) :
    x ∈ (smulLeftCLM hg T).sobolevSingularSupport s ↔ x ∈ T.sobolevSingularSupport s := by
  simp [isLocallySobolevAt_smulLeftCLM_iff hg hx]

/-- Multiplying by a smooth function that vanishes nowhere on `Ω` does not change the `H^s`
singular support. -/
theorem sobolevSingularSupport_smulLeftCLM_of_ne_zero (s : ℝ) (T : 𝓓'(Ω, ℂ)) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x ∈ Ω, g x ≠ 0) :
    (smulLeftCLM hg T).sobolevSingularSupport s = T.sobolevSingularSupport s := by
  ext x
  by_cases hx : x ∈ Ω
  · exact mem_sobolevSingularSupport_smulLeftCLM_iff hg (hg0 x hx)
  · simp [hx]

section Restriction

variable {Ω' : Opens E}

/-- **Restriction** to an open subset `Ω' ≤ Ω` cuts the `H^s` singular support down to the points
of `Ω'`. -/
theorem sobolevSingularSupport_restrictCLM (h : Ω' ≤ Ω) (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (restrictCLM T : 𝓓'(Ω', ℂ)).sobolevSingularSupport s =
      T.sobolevSingularSupport s ∩ Ω' := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet,
    sobolevWaveFrontSet_restrictCLM h, prod_univ, image_inter_preimage]

/-- The `H^s` singular support is local: two distributions with the same restriction to an open
set `U ≤ Ω` have the same `H^s` singular support in `U`. -/
theorem sobolevSingularSupport_inter_eq_of_restrictCLM_eq {s : ℝ} {S T : 𝓓'(Ω, ℂ)}
    {U : Opens E} (hU : U ≤ Ω) (h : (restrictCLM S : 𝓓'(U, ℂ)) = restrictCLM T) :
    S.sobolevSingularSupport s ∩ U = T.sobolevSingularSupport s ∩ U := by
  rw [← sobolevSingularSupport_restrictCLM hU, h, sobolevSingularSupport_restrictCLM hU]

end Restriction

/-! ### The local Sobolev order -/

/-- **Finite Sobolev order for a prescribed cutoff.** For every cutoff `φ` there is an order `s`
making the weighted localized Fourier transform `η ↦ ⟨η⟩ ^ s T (φ e_η)` square integrable: the
localized Fourier transform grows at most polynomially. -/
theorem exists_memLp_one_add_norm_sq_rpow_smul_localFourier (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ s : ℝ, MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • T.localFourier φ η) 2 volume := by
  obtain ⟨C, k, hC⟩ := exists_norm_localFourier_le T φ
  refine ⟨-((k : ℝ) + finrank ℝ E + 1),
    TauCeti.memLp_two_one_add_norm_sq_rpow_smul_of_norm_le volume
      (T.continuous_localFourier φ).aestronglyMeasurable (.of_forall hC) ?_⟩
  linarith [(finrank ℝ E).cast_nonneg (α := ℝ)]

/-- **Distributions have finite Sobolev order locally.** For every compact set `K ⊆ Ω` there is an
order `s` such that `T` is `H^s` near every point of `K`. -/
theorem exists_forall_isLocallySobolevAt (T : 𝓓'(Ω, ℂ)) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ s : ℝ, ∀ x ∈ K, T.IsLocallySobolevAt s x := by
  -- A cutoff equal to one near `K`.
  obtain ⟨χ, hχ1, -⟩ := exists_eventually_eq_one (n := ⊤) hK hKΩ
  let φ : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
  have hφ (y : E) : φ y = χ y := by simp [φ]
  obtain ⟨s, hs⟩ := T.exists_memLp_one_add_norm_sq_rpow_smul_localFourier φ
  exact ⟨s, fun x hx ↦ ⟨φ, by simp [hφ, hχ1.self_of_nhdsSet x hx], hs⟩⟩

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
  sobolevSingularSupport_eq_empty_iff_sobolevWaveFrontSet_eq_empty.2
    (sobolevWaveFrontSet_delta_eq_empty hs x₀)

/-- **The `H^s` singular support of a point mass.** In dimension `d > 0`, the point mass at
`x₀ ∈ Ω` has `H^s` singular support `{x₀}` for `s ≥ -d / 2`. -/
theorem sobolevSingularSupport_delta [Nontrivial E] {s : ℝ} (hs : -2 * s ≤ finrank ℝ E) {x₀ : E}
    (hx₀ : x₀ ∈ Ω) : (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).sobolevSingularSupport s = {x₀} := by
  rw [← fst_image_sobolevWaveFrontSet, sobolevWaveFrontSet_delta hs hx₀]
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  exact fst_image_prod _ ⟨ξ, hξ⟩

end Distribution
