/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.Inversion
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Pullback of distributions along linear maps

Let `A : E →L[ℝ] E'` be a linear map between finite-dimensional real inner product spaces, `T` a
complex distribution on an open set `Ω'` of `E'` and `φ` a test function on `Ω'`. When `T` is a
smooth function, the pullback of the compactly supported function `φ T` along `A` is the function
`x ↦ φ (A x) T (A x)`, and Fourier inversion writes its pairing with a test function `ψ` on `E` as

`∫ ψ (x) φ (A x) T (A x) dx = ∫ T (φ e_η) 𝓕 ψ (-Aᵀ η) dη`,

where `η ↦ T (φ e_η)` is the localized Fourier transform `Distribution.localFourier` of `T`, the
Fourier transform of `φ T`. For a general distribution `T` the right side still converges, provided
no covector of the wave front set of `T` over the support of `φ` is *conormal* to the range of `A`,
that is, annihilated by `Aᵀ`:

`(y, η) ∈ WF(T)`, `y ∈ supp φ` `⟹` `Aᵀ η ≠ 0`.

Indeed this condition makes `T (φ e_η)` rapidly decreasing on a conic neighbourhood
`{η | ‖Aᵀ η‖ < c ‖η‖}` of the kernel of `Aᵀ`
(`Distribution.exists_pos_forall_decay_of_adjoint_ne_zero`), while outside it `‖η‖` is comparable to
`‖Aᵀ η‖`, so that the rapid decay of `𝓕 ψ` absorbs the polynomial growth of `T (φ e_η)`. The
pullback `A^* (φ T)` (`Distribution.cutoffPullback`) is the distribution on `E` defined by the right
side; it extends the pullback of smooth functions (`Distribution.cutoffPullback_apply_eq_integral`).
This is the construction of Hörmander's pullback theorem for a linear map. The condition used here
is `WF(T) ∩ (supp φ × ker Aᵀ) = ∅`. It implies Hörmander's condition `WF(T) ∩ N_A = ∅` over the
support of `φ`, for the set of normals `N_A = {(A x, η) | Aᵀ η = 0}` of `A`, but is stronger: it
constrains the wave front set at every point of the support of `φ`, not only at points of the range
of `A`. The wave front bound of that theorem is not proved here. For a surjective map `A` the
transpose `Aᵀ` is injective and every distribution can be pulled back; for the inclusion of a linear
subspace the condition says that, over the support of `φ`, the wave front set of `T` contains no
covector conormal to the subspace.

## Main declarations

* `Distribution.adjoint_ne_zero_of_surjective`: the wave front condition holds for every
  distribution when `A` is surjective.
* `Distribution.adjoint_ne_zero_add`, `Distribution.adjoint_ne_zero_smul`,
  `Distribution.adjoint_ne_zero_add_cutoff`: the wave front condition is preserved by sums and
  scalar multiples of distributions and by sums of cutoffs.
* `Distribution.exists_pos_forall_decay_of_adjoint_ne_zero`: under the wave front condition,
  `T (φ e_η)` decays rapidly on `{η | ‖Aᵀ η‖ < c ‖η‖}` for some `c > 0`.
* `Distribution.integrable_localFourier_mul_fourier`: under the wave front condition, the integrand
  `T (φ e_η) 𝓕 ψ (-Aᵀ η)` is integrable.
* `Distribution.cutoffPullback`: the pullback `A^* (φ T)`, a distribution on any open set of `E`,
  with its defining formula `Distribution.cutoffPullback_apply`.
* `Distribution.cutoffPullback_add`, `Distribution.cutoffPullback_smul`: linearity in `T`.
* `Distribution.cutoffPullback_add_cutoff`: additivity in the cutoff `φ`.
* `Distribution.cutoffPullback_apply_eq_integral`: if `T` is a function `f` smooth near the
  support of `φ`, then `A^* (φ T)` is the function `x ↦ φ (A x) f (A x)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the pullback of distributions along smooth maps).
* C. Brouder, N. V. Dang and F. Hélein, *Continuity of the fundamental operations on
  distributions having a specified wave front set*, Studia Math. 232 (2016), Proposition 5.1;
  arXiv:1409.7662v2.
-/

public section

noncomputable section

open Complex Filter Function MeasureTheory Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace InnerProduct FourierTransform ContDiff
  SchwartzMap

namespace Distribution

variable {E E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'}

/-! ### The wave front condition -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- For a surjective linear map `A`, the transpose `Aᵀ` is injective, so the wave front condition
of the pullback holds for every distribution `T` and every cutoff `φ`. -/
theorem adjoint_ne_zero_of_surjective [CompleteSpace E] [CompleteSpace E'] {A : E →L[ℝ] E'}
    (hA : Surjective A) (T : 𝓓'(Ω', ℂ)) (φ : 𝓓(Ω', ℂ)) :
    ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0 := by
  rintro y - η hη h0
  obtain ⟨x, rfl⟩ := hA η
  have : ⟪A x, A x⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left, h0, inner_zero_left]
  exact (mem_waveFrontSet_iff.1 hη).2.1 (inner_self_eq_zero.1 this)

omit [FiniteDimensional ℝ E] in
/-- The wave front condition of the pullback holds for `T + S` when it holds for `T` and for `S`. -/
theorem adjoint_ne_zero_add [CompleteSpace E] {A : E →L[ℝ] E'}
    {T S : 𝓓'(Ω', ℂ)} {φ : 𝓓(Ω', ℂ)}
    (h : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0)
    (hS : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ S.waveFrontSet → (A†) η ≠ 0) :
    ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ (T + S).waveFrontSet → (A†) η ≠ 0 := fun y hy η hη ↦
  (waveFrontSet_add_subset T S hη).elim (h y hy η) (hS y hy η)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The wave front condition of the pullback holds for `c • T` when it holds for `T`. -/
theorem adjoint_ne_zero_smul [CompleteSpace E] [CompleteSpace E'] {A : E →L[ℝ] E'}
    {T : 𝓓'(Ω', ℂ)} {φ : 𝓓(Ω', ℂ)} (c : ℂ)
    (h : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0) :
    ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ (c • T).waveFrontSet → (A†) η ≠ 0 := fun y hy η hη ↦
  h y hy η (waveFrontSet_smul_subset c T hη)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The wave front condition of the pullback holds for the cutoff `φ + φ'` when it holds for `φ`
and for `φ'`. -/
theorem adjoint_ne_zero_add_cutoff [CompleteSpace E] [CompleteSpace E'] {A : E →L[ℝ] E'}
    {T : 𝓓'(Ω', ℂ)} {φ φ' : 𝓓(Ω', ℂ)}
    (h : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0)
    (h' : ∀ y ∈ tsupport φ', ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0) :
    ∀ y ∈ tsupport (φ + φ'), ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0 := fun y hy ↦
  (tsupport_add φ φ' hy).elim (h y) (h' y)

omit [FiniteDimensional ℝ E] in
/-- **Decay near the conormal directions.** If no covector of the wave front set of `T` over the
support of `φ` is annihilated by `Aᵀ`, then the localized Fourier transform `T (φ e_η)` decays
rapidly on a conic neighbourhood `{η | ‖Aᵀ η‖ < c ‖η‖}` of the kernel of `Aᵀ`. -/
theorem exists_pos_forall_decay_of_adjoint_ne_zero [CompleteSpace E] {A : E →L[ℝ] E'}
    {T : 𝓓'(Ω', ℂ)} {φ : 𝓓(Ω', ℂ)}
    (h : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0) :
    ∃ c > 0, ∀ N : ℕ, ∃ C, ∀ η, ‖(A†) η‖ < c * ‖η‖ →
      (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C := by
  classical
  set S : Set E' := Metric.sphere 0 1 ∩ (A†) ⁻¹' {0}
  -- Over the support of `φ`, `T` is microlocally smooth in every direction of `S`.
  have hsmooth (u : S) : ∀ y ∈ tsupport φ, T.IsMicrolocallySmoothAt y u := fun y hy ↦ by
    by_contra hns
    have hu : (u : E') ≠ 0 := fun h0 ↦ by simpa [h0] using u.2.1
    exact h y hy u (mem_waveFrontSet_iff.2 ⟨φ.tsupport_subset hy, hu, hns⟩) u.2.2
  choose W _ hKW Γ hΓ huΓ hcone hdecay using fun u : S ↦
    exists_isOpen_cone_forall_decay_of_isCompact φ.hasCompactSupport.isCompact (hsmooth u)
  -- Finitely many of the cones cover `S`; their union `G` contains the kernel of `Aᵀ`.
  obtain ⟨t, ht⟩ := ((isCompact_sphere 0 1).inter_right
    (isClosed_singleton.preimage (A†).continuous)).elim_finite_subcover (fun u : S ↦ Γ u) hΓ
    fun u hu ↦ mem_iUnion.2 ⟨⟨u, hu⟩, huΓ ⟨u, hu⟩⟩
  have hGcone (r : ℝ) (hr : 0 < r) (η : E') (hη : η ∈ ⋃ u ∈ t, Γ u) : r • η ∈ ⋃ u ∈ t, Γ u :=
    let ⟨u, hut, hηu⟩ := mem_iUnion₂.1 hη
    mem_iUnion₂.2 ⟨u, hut, hcone u r hr η hηu⟩
  obtain ⟨c, hc, hcG⟩ := IsOpen.exists_pos_forall_mem_of_norm_lt_mul_norm
    (isOpen_biUnion fun u _ ↦ hΓ u) hGcone (A†) fun η hη h0 ↦ by
      have hnη : 0 < ‖η‖ := norm_pos_iff.2 hη
      simpa [smul_smul, hnη.ne'] using hGcone ‖η‖ hnη (‖η‖⁻¹ • η)
        (ht ⟨by simp [norm_smul, hnη.ne'], by simp [h0]⟩)
  refine ⟨c, hc, fun N ↦ ?_⟩
  choose C hC using fun u : S ↦ hdecay u φ (subset_union_left.trans' (hKW u)) N
  refine ⟨∑ u ∈ t, max (C u) 0, fun η hη ↦ ?_⟩
  obtain ⟨v, hvt, hηv⟩ := mem_iUnion₂.1 (hcG η hη)
  calc (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C v := hC v η hηv
    _ ≤ max (C v) 0 := le_max_left _ _
    _ ≤ ∑ u ∈ t, max (C u) 0 :=
      Finset.single_le_sum (fun u _ ↦ le_max_right (C u) 0) hvt

/-! ### The pullback -/

variable [MeasurableSpace E] [BorelSpace E]

/-- A real test function, viewed as a complex function, is integrable. -/
private theorem integrable_ofReal_testFunction (ψ : 𝓓(Ω, ℝ)) : Integrable fun x ↦ (ψ x : ℂ) :=
  (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).ofReal

/-- The arithmetic of the bound away from the kernel of `Aᵀ`: if `a ≤ C₀ (1 + t) ^ k`,
`(1 + s) ^ (k + j) b ≤ D` and `1 + t ≤ K (1 + s)`, then `a b (1 + t) ^ j ≤ C₀ K ^ (k + j) D`. -/
private theorem mul_mul_pow_le {a b t s C₀ D K : ℝ} {k j : ℕ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (ha : a ≤ C₀ * (1 + t) ^ k) (hb : (1 + s) ^ (k + j) * b ≤ D)
    (hts : 1 + t ≤ K * (1 + s)) : a * b * (1 + t) ^ j ≤ C₀ * K ^ (k + j) * D := by
  have hC₀ : 0 ≤ C₀ := nonneg_of_mul_nonneg_left (ha0.trans ha) (by positivity)
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left (by linarith) (by linarith : (0 : ℝ) < 1 + s)
  calc a * b * (1 + t) ^ j ≤ C₀ * (1 + t) ^ k * b * (1 + t) ^ j := by gcongr
    _ = C₀ * ((1 + t) ^ (k + j) * b) := by ring
    _ ≤ C₀ * ((K * (1 + s)) ^ (k + j) * b) := by gcongr
    _ = C₀ * K ^ (k + j) * ((1 + s) ^ (k + j) * b) := by rw [mul_pow]; ring
    _ ≤ C₀ * K ^ (k + j) * D := by gcongr

/-- **The integrand is bounded uniformly in the test function.** Under the wave front condition
there are an order `M` and a constant `B` such that, for every real function `ψ` smooth and
supported in the compact set `K` whose first `M` derivatives are bounded by `C ≥ 0`, the integrand
`T (φ e_η) 𝓕 ψ (-Aᵀ η)` is bounded by `B C (1 + ‖η‖) ^ (-(d + 1))`, with `d` the dimension of
`E'`. -/
private theorem exists_norm_mul_fourier_le {A : E →L[ℝ] E'} {T : 𝓓'(Ω', ℂ)}
    {φ : 𝓓(Ω', ℂ)} (h : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0)
    {K : Set E} (hK : IsCompact K) :
    ∃ (M : ℕ) (B : ℝ), ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ K → ∀ C, 0 ≤ C →
      (∀ p ≤ M, ∀ x, ‖iteratedFDeriv ℝ p ψ x‖ ≤ C) → ∀ η,
        ‖T.localFourier φ η * 𝓕 (fun x ↦ (ψ x : ℂ)) (-(A†) η)‖ ≤
          B * C * (1 + ‖η‖) ^ (-((Module.finrank ℝ E' : ℝ) + 1)) := by
  set d := Module.finrank ℝ E'
  obtain ⟨c, hc, hdecay⟩ := exists_pos_forall_decay_of_adjoint_ne_zero h
  obtain ⟨C₁, hC₁⟩ := hdecay (d + 1)
  obtain ⟨C₀, k, hC₀⟩ := exists_norm_localFourier_le T φ
  set V := volume.real K
  refine ⟨k + (d + 1), max C₁ 0 * V + max C₀ 0 * (1 + c⁻¹) ^ (k + (d + 1)) * 2 ^ (k + (d + 1)) * V,
    fun ψ hψ hψK C hC0 hC η ↦ ?_⟩
  -- The Fourier transform of `ψ` decays at every order up to `k + d + 1`, uniformly in `ψ`.
  have hF (j : ℕ) (hj : j ≤ k + (d + 1)) (ζ : E) :
      (1 + ‖ζ‖) ^ j * ‖𝓕 (fun x ↦ (ψ x : ℂ)) ζ‖ ≤ 2 ^ j * (C * V) := by
    refine TauCeti.one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset (f := ofRealLI ∘ ψ)
      ((ofRealLI.contDiff.comp hψ).of_le (by exact_mod_cast le_top)) hK.measure_lt_top.ne
      ((tsupport_comp_subset (map_zero ofRealLI) ψ).trans hψK) (fun p hp x ↦ ?_) ζ
    rw [ofRealLI.norm_iteratedFDeriv_comp_left hψ.contDiffAt (by exact_mod_cast le_top)]
    exact hC p (hp.trans hj) x
  have hpow : 0 < (1 + ‖η‖) ^ (d + 1) := by positivity
  have hF0 := hF 0 (Nat.zero_le _) (-(A†) η)
  rw [pow_zero, one_mul, pow_zero, one_mul] at hF0
  rw [Real.rpow_neg (by positivity), ← Nat.cast_add_one, Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ hpow, norm_mul]
  rcases lt_or_ge ‖(A†) η‖ (c * ‖η‖) with hlt | hge
  · -- Near the kernel of `Aᵀ`, `T (φ e_η)` decays rapidly.
    calc ‖T.localFourier φ η‖ * ‖𝓕 (fun x ↦ (ψ x : ℂ)) (-(A†) η)‖ * (1 + ‖η‖) ^ (d + 1)
        = (1 + ‖η‖) ^ (d + 1) * ‖T.localFourier φ η‖ *
            ‖𝓕 (fun x ↦ (ψ x : ℂ)) (-(A†) η)‖ := by ring
      _ ≤ max C₁ 0 * (C * V) :=
          mul_le_mul ((hC₁ η hlt).trans (le_max_left _ _)) hF0 (norm_nonneg _) (le_max_right _ _)
      _ ≤ _ := by nlinarith [show 0 ≤ max C₀ 0 * (1 + c⁻¹) ^ (k + (d + 1)) *
          2 ^ (k + (d + 1)) * V * C by positivity]
  · -- Away from it, `‖η‖` is comparable to `‖Aᵀ η‖`, and `𝓕 ψ` decays rapidly.
    have hcmp : 1 + ‖η‖ ≤ (1 + c⁻¹) * (1 + ‖(A†) η‖) := by
      have : ‖η‖ ≤ c⁻¹ * ‖(A†) η‖ := by
        rw [le_inv_mul_iff₀ hc]
        linarith
      nlinarith [norm_nonneg ((A†) η), inv_pos.2 hc]
    have hFM := hF _ le_rfl (-(A†) η)
    rw [norm_neg] at hFM
    refine (mul_mul_pow_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      ((hC₀ η).trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))) hFM
      hcmp).trans ?_
    nlinarith [show 0 ≤ max C₁ 0 * V * C by positivity]

variable [MeasurableSpace E'] [BorelSpace E']

/-- **The integrand of the pullback is integrable.** Under the wave front condition, the integrand
`T (φ e_η) 𝓕 ψ (-Aᵀ η)` defining the pullback `Distribution.cutoffPullback` is integrable for
every real test function `ψ`. -/
theorem integrable_localFourier_mul_fourier {A : E →L[ℝ] E'} {T : 𝓓'(Ω', ℂ)}
    {φ : 𝓓(Ω', ℂ)} (h : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0)
    (ψ : 𝓓(Ω, ℝ)) :
    Integrable fun η ↦ T.localFourier φ η * 𝓕 (fun x ↦ (ψ x : ℂ)) (-(A†) η) := by
  obtain ⟨M, B, hB⟩ := exists_norm_mul_fourier_le h ψ.hasCompactSupport.isCompact
  -- A common bound for the first `M` derivatives of `ψ`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ≤ M, ∀ x, ‖iteratedFDeriv ℝ p ψ x‖ ≤ C := by
    choose C hC using fun p : Fin (M + 1) ↦
      ((ψ.contDiff.continuous_iteratedFDeriv (m := (p : ℕ)) (by exact_mod_cast le_top)).norm
        ).bounded_above_of_compact_support (ψ.hasCompactSupport.iteratedFDeriv (p : ℕ)).norm
    refine ⟨∑ p, max (C p) 0, fun p hp x ↦ ?_⟩
    have h1 := hC ⟨p, by omega⟩ x
    rw [norm_norm] at h1
    exact h1.trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun p ↦ max (C p) 0)
      (fun _ _ ↦ le_max_right _ _) (Finset.mem_univ _)))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
  refine Integrable.mono' ((integrable_one_add_norm (by linarith)).const_mul (B * C)) ?_
    (Eventually.of_forall (hB ψ ψ.contDiff subset_rfl C hC0 hC))
  exact ((T.continuous_localFourier φ).mul
    ((integrable_ofReal_testFunction ψ).continuous_fourier.comp
      (A†).continuous.neg)).aestronglyMeasurable

variable (A : E →L[ℝ] E') (T : 𝓓'(Ω', ℂ)) (φ : 𝓓(Ω', ℂ))
  (h : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0)

/-- The pairing of the pullback with test functions, as a linear map. -/
private def pullbackLM : 𝓓(Ω, ℝ) →ₗ[ℝ] ℂ where
  toFun ψ := ∫ η, T.localFourier φ η * 𝓕 (fun x ↦ (ψ x : ℂ)) (-(A†) η)
  map_add' ψ ψ' := by
    rw [← integral_add (integrable_localFourier_mul_fourier h ψ)
      (integrable_localFourier_mul_fourier h ψ')]
    congr 1 with η
    have hfun : (fun x ↦ ((ψ + ψ') x : ℂ)) = (fun x ↦ (ψ x : ℂ)) + fun x ↦ (ψ' x : ℂ) := by
      ext x
      simp
    rw [← mul_add, hfun,
      (integrable_ofReal_testFunction ψ).fourier_add (integrable_ofReal_testFunction ψ'),
      Pi.add_apply]
  map_smul' c ψ := by
    simp only [RingHom.id_apply, ← integral_smul]
    congr 1 with η
    have hfun : (fun x ↦ ((c • ψ) x : ℂ)) = (c : ℂ) • fun x ↦ (ψ x : ℂ) := by
      ext x
      simp
    rw [hfun, Real.fourier_const_smul, Pi.smul_apply, mul_smul_comm, Complex.coe_smul]

/-- **The pullback of a cut-off distribution along a linear map.** Let `A : E →L[ℝ] E'` be linear
and let no covector of the wave front set of `T` over the support of `φ` be annihilated by `Aᵀ`.
The pullback `A^* (φ T)` is the distribution on `Ω` pairing with a real test function `ψ` as

`A^* (φ T) ψ = ∫ T (φ e_η) 𝓕 ψ (-Aᵀ η) dη`,

where `η ↦ T (φ e_η)` is the localized Fourier transform `Distribution.localFourier`. When `T` is a
smooth function this is the pairing of `ψ` with `x ↦ φ (A x) T (A x)`
(`Distribution.cutoffPullback_apply_eq_integral`). -/
def cutoffPullback : 𝓓'(Ω, ℂ) :=
  TestFunction.mkCLM ℝ (pullbackLM A T φ h) (map_add _) (map_smul _) fun K hK ↦ by
    obtain ⟨M, B, hB⟩ := exists_norm_mul_fourier_le h K.isCompact
    set I := ∫ η : E', (1 + ‖η‖) ^ (-((Module.finrank ℝ E' : ℝ) + 1))
    -- On test functions supported in `K`, the pairing is bounded by a seminorm of order `M`.
    refine (ContDiffMapSupportedIn.withSeminorms ..).continuous_of_isBounded
      (norm_withSeminorms ℝ ℂ) ((pullbackLM A T φ h).comp (ofSupportedInCLM ℝ hK).toLinearMap)
      fun _ ↦ ⟨Finset.Iic M, ⟨max B 0 * I, by positivity⟩, fun f ↦ ?_⟩
    set S := (Finset.Iic M).sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) f
    have hS : 0 ≤ S := apply_nonneg _ _
    have hbound := hB f f.contDiff f.tsupport_subset S hS fun p hp x ↦
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hp))
    simp only [Seminorm.comp_apply, coe_normSeminorm]
    calc ‖(pullbackLM A T φ h) (ofSupportedInCLM ℝ hK f)‖
        ≤ ∫ η : E', B * S * (1 + ‖η‖) ^ (-((Module.finrank ℝ E' : ℝ) + 1)) :=
          norm_integral_le_of_norm_le
            ((integrable_one_add_norm (by linarith)).const_mul (B * S))
            (Eventually.of_forall hbound)
      _ = B * I * S := by rw [integral_const_mul]; ring
      _ ≤ max B 0 * I * S := by gcongr; exact le_max_left _ _

/-- The defining formula of the pullback: `A^* (φ T) ψ = ∫ T (φ e_η) 𝓕 ψ (-Aᵀ η) dη`. -/
theorem cutoffPullback_apply (ψ : 𝓓(Ω, ℝ)) :
    cutoffPullback A T φ h ψ =
      ∫ η, T.localFourier φ η * 𝓕 (fun x ↦ (ψ x : ℂ)) (-(A†) η) :=
  (rfl)

variable {A T φ}

/-- The pullback is additive in the distribution. -/
theorem cutoffPullback_add {S : 𝓓'(Ω', ℂ)}
    (hS : ∀ y ∈ tsupport φ, ∀ η, (y, η) ∈ S.waveFrontSet → (A†) η ≠ 0) :
    (cutoffPullback A (T + S) φ (adjoint_ne_zero_add h hS) : 𝓓'(Ω, ℂ)) =
      cutoffPullback A T φ h + cutoffPullback A S φ hS := by
  ext ψ
  simp only [add_apply, cutoffPullback_apply, localFourier_add, add_mul]
  exact integral_add (integrable_localFourier_mul_fourier h ψ)
    (integrable_localFourier_mul_fourier hS ψ)

/-- The pullback is complex-linear in the distribution. -/
theorem cutoffPullback_smul (c : ℂ) :
    (cutoffPullback A (c • T) φ (adjoint_ne_zero_smul c h) : 𝓓'(Ω, ℂ)) =
      c • cutoffPullback A T φ h := by
  ext ψ
  simp only [smul_apply, cutoffPullback_apply, localFourier_smul, mul_assoc,
    integral_const_mul, smul_eq_mul]

/-- The pullback is additive in the cutoff. -/
theorem cutoffPullback_add_cutoff {φ' : 𝓓(Ω', ℂ)}
    (h' : ∀ y ∈ tsupport φ', ∀ η, (y, η) ∈ T.waveFrontSet → (A†) η ≠ 0) :
    (cutoffPullback A T (φ + φ') (adjoint_ne_zero_add_cutoff h h') : 𝓓'(Ω, ℂ)) =
      cutoffPullback A T φ h + cutoffPullback A T φ' h' := by
  ext ψ
  simp only [add_apply, cutoffPullback_apply, localFourier_add_cutoff, add_mul]
  exact integral_add (integrable_localFourier_mul_fourier h ψ)
    (integrable_localFourier_mul_fourier h' ψ)

/-- **The pullback of a smooth function.** If `T` coincides on an open set `U` containing the
support of `φ` with a function `f` smooth on `U`, then `A^* (φ T)` is the function
`x ↦ φ (A x) f (A x)`. -/
theorem cutoffPullback_apply_eq_integral {U : Set E'} (hU : IsOpen U) {f : E' → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hT : ∀ χ : 𝓓(Ω', ℝ), tsupport χ ⊆ U → T χ = ∫ y, χ y • f y)
    (hφU : tsupport φ ⊆ U) (ψ : 𝓓(Ω, ℝ)) :
    cutoffPullback A T φ h ψ = ∫ x, ψ x • (φ (A x) * f (A x)) := by
  set g : E' → ℂ := fun y ↦ φ y * f y
  -- The product `φ f` is smooth with compact support, so it is a Schwartz function.
  have hg : ContDiff ℝ ∞ g := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ U
    · exact φ.contDiff.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hy))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hy (hφU h)] with z hz
      simp [g, hz]
  set G : 𝓢(E', ℂ) := (φ.hasCompactSupport.mul_right (f' := f)).toSchwartzMap hg
  have hGg : (G : E' → ℂ) = g := rfl
  have hFg : Integrable (𝓕 g) := by
    rw [← hGg, ← SchwartzMap.fourier_coe]
    exact (𝓕 G).integrable
  rw [cutoffPullback_apply]
  simp_rw [localFourier_eq_fourier (hf.continuousOn.locallyIntegrableOn hU.measurableSet) hT hφU,
    Complex.real_smul]
  exact (A.integral_mul_comp_eq_integral_fourier_mul_fourier hg.continuous (hGg ▸ G.integrable)
    hFg (integrable_ofReal_testFunction ψ)).symm

end Distribution
