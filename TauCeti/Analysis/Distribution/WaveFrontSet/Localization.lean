/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Localization of the wave front set

The definition of microlocal smoothness of a distribution `T` at `(x, ξ)` asks for *one* cutoff `φ`
with `φ x ≠ 0` whose localized Fourier transform `η ↦ T (φ e_η)` decays rapidly in an open cone
around `ξ`. This file shows that the choice of cutoff does not matter near `x`: multiplying `φ` by
a smooth function keeps rapid decay, at the price of shrinking the cone (Hörmander I,
Lemma 8.1.1). Consequently the wave front set of a sum lies in the union of the wave front sets,
multiplication by a smooth function `g` does not enlarge the wave front set and leaves it unchanged
where `g ≠ 0`, and the wave front set of the restriction of a distribution to an open subset is
the part of its wave front set lying over that subset. In particular the wave front set over an
open set depends only on the restriction to it.

The proof expands the multiplier in a Fourier series. If `ψ = φ g` with `g` smooth, choose a compact
set `K` around the support of `φ` and a full lattice `L` none of whose nonzero translates of `K`
meet `K`. On `K`, the function `g` (times a cutoff) is the sum, in the topology of smooth functions
supported in `K`, of its Fourier series along the dual lattice `L^∨`, with rapidly decreasing
coefficients `a_m` (`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate`). Pairing with `T`
turns this into the discrete convolution formula

`T (ψ e_η) = ∑ m : L^∨, a_m T (φ e_(η - m))`

(`Distribution.exists_hasSum_localFourier_of_eq_mul`). The localized Fourier transform grows at
most polynomially (`Distribution.exists_norm_localFourier_le`). For `η` in a smaller cone `Γ'`,
the terms with `‖m‖ ≤ c ‖η‖` evaluate the transform of `φ T` inside the original cone `Γ`, where it
decays rapidly, and the remaining terms are controlled by the rapid decay of `a_m`.

## Main results

* `Distribution.localFourier_eq_complexPairing_modulate`,
  `Distribution.localFourier_eq_complexPairing_mul_modulate`: the localized Fourier transform as
  the pairing with a modulated test function.
* `Distribution.exists_norm_localFourier_le`: the localized Fourier transform of a distribution
  grows at most polynomially, with a degree that is uniform over the cutoffs supported in a fixed
  compact set (`Distribution.exists_forall_norm_localFourier_le`).
* `Distribution.exists_hasSum_localFourier_of_eq_mul`: the localized Fourier transform with
  cutoff `φ g` is a rapidly decreasing superposition of translates of the one with cutoff `φ`.
* `Distribution.exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul`: decay of each order
  of the localized Fourier transform on a set `Γ` survives multiplication of the cutoff by a smooth
  function, on any set `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)` lie in `Γ`.
* `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`: at a point of microlocal smoothness
  there are a neighbourhood `U` of `x` and an open cone `Γ` around `ξ` such that every cutoff
  supported in `U` has localized Fourier transform rapidly decreasing on `Γ`.
* `Distribution.exists_isOpen_cone_forall_decay_of_isCompact`: the same holds uniformly over a
  compact set `K` of points of microlocal smoothness: there is an open `W ⊇ K` such that it holds
  for every cutoff supported in `W ∪ (dsupport T)ᶜ`, that is, whose support meets the support of
  `T` only inside `W`.
* `Distribution.exists_hasSum_localFourier_of_forall_norm_iteratedFDeriv_le`: a family of cutoffs
  supported in a fixed compact set and bounded in every `C^n` norm has a Fourier expansion in the
  modulations of one cutoff, with coefficients rapidly decreasing uniformly over the family. Hence
  the localized Fourier transforms with these cutoffs grow polynomially
  (`Distribution.exists_forall_norm_localFourier_le_of_forall_norm_iteratedFDeriv_le`) and, at a
  point of microlocal smoothness, decay rapidly
  (`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone_of_forall_norm_iteratedFDeriv_le`),
  uniformly over the family.
* `Distribution.IsMicrolocallySmoothAt.add`, `Distribution.waveFrontSet_add_subset`,
  `Distribution.waveFrontSet_sub_subset`, `Distribution.waveFrontSet_sum_subset`: the wave front
  set of a sum lies in the union of the wave front sets.
* `Distribution.IsMicrolocallySmoothAt.smulLeftCLM`,
  `Distribution.isMicrolocallySmoothAt_smulLeftCLM_iff`,
  `Distribution.waveFrontSet_smulLeftCLM_subset`, `Distribution.mem_waveFrontSet_smulLeftCLM_iff`:
  the wave front set of a smooth multiple `g T` lies in that of `T` over `tsupport g`, with
  equality at the points where `g ≠ 0`, and everywhere when `g` vanishes nowhere on `Ω`
  (`Distribution.waveFrontSet_smulLeftCLM_of_ne_zero`).
* `Distribution.isMicrolocallySmoothAt_restrictCLM_iff`, `Distribution.waveFrontSet_restrictCLM`:
  for an open subset `Ω' ≤ Ω`, `WF(T|_{Ω'}) = WF(T) ∩ (Ω' × E)`.
* `Distribution.waveFrontSet_inter_eq_of_restrictCLM_eq`: distributions with the same restriction
  to an open set have the same wave front set over it.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Lemma 8.1.1 and §8.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff SchwartzMap

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

omit [FiniteDimensional ℝ E] in
/-- The localized Fourier transform of `T` with cutoff `φ` at `η` pairs `T` with the modulation by
`-η` of any test function `f` supported in a compact set `K ⊆ Ω` that agrees with `φ`. -/
theorem localFourier_eq_complexPairing_modulate (T : 𝓓'(Ω, ℂ)) {φ : 𝓓(Ω, ℂ)} {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) {f : 𝓓_{K}(E, ℂ)} (hf : ∀ x, f x = φ x) (η : E) :
    T.localFourier φ η = T.complexPairing (ofSupportedIn hKΩ (f.modulate (-η))) := by
  refine localFourier_eq T φ fun x ↦ ?_
  simp only [coe_ofSupportedIn, ContDiffMapSupportedIn.modulate_apply, smul_eq_mul, hf]
  rw [mul_comm, Real.fourierChar_apply, inner_neg_right]
  congr 2
  push_cast
  ring

omit [FiniteDimensional ℝ E] in
/-- If the cutoff `ψ` is `φ f` with `f` a test function supported in a compact set `K ⊆ Ω`, the
localized Fourier transform of `T` with cutoff `ψ` at `η` pairs `T` with `φ` times the modulation
of `f` by `-η`. -/
theorem localFourier_eq_complexPairing_mul_modulate (T : 𝓓'(Ω, ℂ)) {φ ψ : 𝓓(Ω, ℂ)}
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) {f : 𝓓_{K}(E, ℂ)} (hψ : ∀ x, ψ x = φ x * f x)
    (η : E) :
    T.localFourier ψ η = T.complexPairing (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
      φ.contDiff (ofSupportedIn hKΩ (f.modulate (-η)))) := by
  have hψK : support ψ ⊆ K := fun x hx ↦
    f.support_subset (right_ne_zero_of_mul (a := φ x) (by rwa [← hψ]))
  let ψK : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset ψ.contDiff hψK
  rw [localFourier_eq_complexPairing_modulate T hKΩ (f := ψK)
    (fun _ ↦ by simp [ψK, ContDiffMapSupportedIn.coe_of_support_subset]) η]
  congr 1
  ext x
  simp [ψK, ContDiffMapSupportedIn.coe_of_support_subset, TestFunction.bilinLeftCLM_apply, hψ]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Polynomial growth of the localized Fourier transform, uniformly in the cutoff.** For a
complex distribution `T` and a compact set `K ⊆ Ω` there is a degree `k` such that for every
complex test function `φ` supported in `K`, the localized Fourier transform `η ↦ T (φ e_η)` is
bounded by `C (1 + ‖η‖) ^ k` for some `C`. -/
theorem exists_forall_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ k : ℕ, ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K →
      ∃ C : ℝ, ∀ η, ‖T.localFourier φ η‖ ≤ C * (1 + ‖η‖) ^ k := by
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L ofSupportedInCLM ℂ hKΩ
  -- The modulations of a cutoff grow polynomially in every continuous seminorm.
  obtain ⟨k, hk⟩ := ContDiffMapSupportedIn.exists_seminorm_modulate_le
    ((normSeminorm ℂ ℂ).comp Λ.toLinearMap) (continuous_norm.comp Λ.continuous)
  refine ⟨k, fun φ hφ ↦ ?_⟩
  let φK : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset φ.contDiff ((subset_tsupport _).trans hφ)
  obtain ⟨C, hC⟩ := hk φK
  refine ⟨C, fun η ↦ ?_⟩
  have h : T.localFourier φ η = Λ (φK.modulate (-η)) := by
    rw [ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    exact localFourier_eq_complexPairing_modulate T hKΩ
      (fun _ ↦ by simp [φK, ContDiffMapSupportedIn.coe_of_support_subset]) η
  simpa [h] using hC (-η)

omit [FiniteDimensional ℝ E] in
/-- **Polynomial growth of the localized Fourier transform.** For a complex distribution `T` and a
complex test function `φ`, the localized Fourier transform `η ↦ T (φ e_η)` is bounded by
`C (1 + ‖η‖) ^ k` for some `C` and `k`. -/
theorem exists_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (C : ℝ) (k : ℕ), ∀ η, ‖T.localFourier φ η‖ ≤ C * (1 + ‖η‖) ^ k := by
  obtain ⟨k, hk⟩ := exists_forall_norm_localFourier_le T
    (K := ⟨tsupport φ, φ.hasCompactSupport⟩) φ.tsupport_subset
  obtain ⟨C, hC⟩ := hk φ subset_rfl
  exact ⟨C, k, hC⟩

/-- **The localized Fourier transform of a smooth multiple.** If the cutoff `ψ` is `φ g` with `g`
smooth on `Ω`, then there are a subgroup `L` of `E` and rapidly decreasing coefficients `a : L → ℂ`
such that

`T (ψ e_η) = ∑ m : L, a m T (φ e_(η - m))`

for every frequency `η`. This is the discrete form of the convolution formula
`(φ g T)^ = ĝ * (φ T)^`: the coefficients are those of a Fourier series of `g` on a compact set
around the support of `φ`. -/
theorem exists_hasSum_localFourier_of_eq_mul (T : 𝓓'(Ω, ℂ)) {φ ψ : 𝓓(Ω, ℂ)} {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g Ω) (hψ : ∀ x, ψ x = φ x * g x) :
    ∃ (L : Submodule ℤ E) (a : L → ℂ),
      (∀ j : ℕ, Summable fun m : L ↦ (1 + ‖(m : E)‖) ^ j * ‖a m‖) ∧
        ∀ η, HasSum (fun m : L ↦ a m * T.localFourier φ (η - m)) (T.localFourier ψ η) := by
  borelize E
  -- Nested compact sets `tsupport φ ⊆ K₁ ⊆ K₂ ⊆ Ω` and cutoffs `χ₁, χ₂` adapted to them.
  obtain ⟨K₁, hK₁, hφK₁, hK₁Ω⟩ :=
    exists_compact_between φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  obtain ⟨K₂, hK₂, hK₁K₂, hK₂Ω⟩ := exists_compact_between hK₁ Ω.isOpen hK₁Ω
  obtain ⟨χ₁, hχ₁, -, hχ₁1, -, hχ₁s⟩ :=
    φ.hasCompactSupport.exists_contDiff_cutoff isOpen_interior hφK₁
  obtain ⟨χ₂, hχ₂, -, hχ₂1, -, hχ₂s⟩ := hK₁.exists_contDiff_cutoff isOpen_interior hK₁K₂
  let K : Compacts E := ⟨K₂, hK₂⟩
  have hKΩ : (K : Set E) ⊆ Ω := hK₂Ω
  have hχ₁φ {x : E} (hx : φ x ≠ 0) : χ₁ x = 1 := interior_subset (hχ₁1 (subset_tsupport _ hx))
  have hχ₂K₁ {x : E} (hx : x ∈ K₁) : χ₂ x = 1 := interior_subset (hχ₂1 hx)
  have hχ₁K₁ : tsupport χ₁ ⊆ K₁ := hχ₁s.trans interior_subset
  -- The function `χ₁ g`, expanded in the modulations of the cutoff `χ₂`.
  have hχ₁g : ContDiff ℝ ∞ fun x ↦ (χ₁ x : ℂ) * g x := by
    simpa [Complex.real_smul] using
      hg.contDiff_smul_of_tsupport_subset Ω.isOpen hχ₁.contDiffOn (hχ₁K₁.trans hK₁Ω)
  have hχ₂c : ContDiff ℝ ∞ fun x ↦ (χ₂ x : ℂ) := ofRealCLM.contDiff.comp hχ₂
  have hfK : support (fun x ↦ (χ₁ x : ℂ) * g x) ⊆ K₂ := fun x hx ↦
    interior_subset (hK₁K₂ (hχ₁K₁ (subset_tsupport _ (by simpa using left_ne_zero_of_mul hx))))
  have hχK : support (fun x ↦ (χ₂ x : ℂ)) ⊆ K₂ := fun x hx ↦
    interior_subset (hχ₂s (subset_tsupport _ (by simpa using hx)))
  let f : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hχ₁g hfK
  let χ : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hχ₂c hχK
  have hχ : EqOn χ 1 (support f) := fun x hx ↦ by
    have hx' : χ₁ x ≠ 0 := by
      simpa [f, ContDiffMapSupportedIn.coe_of_support_subset] using left_ne_zero_of_mul hx
    simp [χ, ContDiffMapSupportedIn.coe_of_support_subset, hχ₂K₁ (hχ₁K₁ (subset_tsupport _ hx'))]
  -- A lattice none of whose nonzero translates of `K` meet `K`.
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
  have hexp := ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L f χ
    (fun x hx ℓ h ↦ Subtype.ext (hL x hx ℓ ℓ.2 h)) hχ
  refine ⟨ZLattice.dual L, fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : E → ℂ) m,
    fun j ↦ ?_, fun η ↦ ?_⟩
  · have hdecay := ContDiffMapSupportedIn.summable_one_add_norm_pow_mul_norm_fourier
      (ZLattice.dual L) f j
    refine (hdecay.mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖).congr fun m ↦ ?_
    rw [norm_mul]
    ring
  · -- Pair the expansion with `T`, after modulating by `-η` and multiplying by `φ`.
    let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L
      (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff ∘L
        ofSupportedInCLM ℂ hKΩ ∘L ContDiffMapSupportedIn.modulateCLM (-η))
    have hΛ (h : 𝓓_{K}(E, ℂ)) : Λ h = T.complexPairing
        (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ.contDiff
          (ofSupportedIn hKΩ (h.modulate (-η)))) := by
      simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM,
        ContDiffMapSupportedIn.modulateCLM_apply]
    have h1 : Λ f = T.localFourier ψ η := by
      rw [hΛ, localFourier_eq_complexPairing_mul_modulate T hKΩ (φ := φ) (f := f) fun x ↦ ?_]
      by_cases hx : φ x = 0
      · simp [hψ, hx]
      · simp [f, ContDiffMapSupportedIn.coe_of_support_subset, hψ, hχ₁φ hx]
    have h2 (m : ZLattice.dual L) (a : ℂ) :
        Λ (a • χ.modulate m) = a * T.localFourier φ (η - m) := by
      rw [map_smul, smul_eq_mul, hΛ, ContDiffMapSupportedIn.modulate_modulate,
        localFourier_eq_complexPairing_mul_modulate T hKΩ (φ := φ) (f := χ) fun x ↦ ?_, neg_sub,
        sub_eq_add_neg]
      by_cases hx : φ x = 0
      · simp [hx]
      · simp [χ, ContDiffMapSupportedIn.coe_of_support_subset,
          hχ₂K₁ (hφK₁.trans interior_subset (subset_tsupport _ hx))]
    have hmap := hexp.map Λ Λ.continuous
    rw [h1] at hmap
    convert hmap using 1
    ext m
    exact (h2 m _).symm

/-- **Localization of decay** (Hörmander I, Lemma 8.1.1). Suppose `(1 + ‖η‖) ^ N` times the
localized Fourier transform of `T` with cutoff `φ` is bounded on a set `Γ`, and `Γ'` is a set such
that for some `c > 0` the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`. Then for
every cutoff `ψ = φ g` with `g` smooth on `Ω`, `(1 + ‖η‖) ^ N` times the localized Fourier
transform of `T` with cutoff `ψ` is bounded on `Γ'`. Each point `ξ` of an open cone `Γ` lies in
an open cone `Γ'` of this kind (`IsOpen.exists_cone_closedBall_subset`). -/
theorem exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul {T : 𝓓'(Ω, ℂ)}
    {φ ψ : 𝓓(Ω, ℂ)} {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g Ω) (hψ : ∀ x, ψ x = φ x * g x)
    {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    {N : ℕ} (hdecay : ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C) :
    ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  obtain ⟨L, a, ha, hsum⟩ := exists_hasSum_localFourier_of_eq_mul T hg hψ
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T φ
  obtain ⟨D, hD⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_le_mul_tsum_of_hasSum
    (v := fun m : L ↦ (m : E)) (𝕜 := ℂ) hF hc hΓ' hdecay
  exact ⟨_, fun η hη ↦ hD a (ha _) η hη _ (hsum η)⟩

/-- **Independence of the cutoff.** If `T` is microlocally smooth at `(x, ξ)`, then there are a
neighbourhood `U` of `x` and an open cone `Γ` containing `ξ` such that for *every* test function
`ψ` supported in `U`, the localized Fourier transform of `T` with cutoff `ψ` decays rapidly on
`Γ`. -/
theorem IsMicrolocallySmoothAt.exists_nhds_cone {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySmoothAt x ξ) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
        ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 h
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  -- Near `x` every cutoff is a smooth multiple of `φ`.
  obtain ⟨U, hU, hUφ⟩ := exists_mem_nhds_forall_exists_contDiff_eq_mul hφx
  refine ⟨U, hU, Γ', hΓ'o, hξ', hcone', fun ψ hψ N ↦ ?_⟩
  obtain ⟨g, hg, hψg⟩ := hUφ ψ hψ
  exact exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul hg.contDiffOn hψg hc hΓ'
    (hdecay N)

/-- **Uniform decay over a compact set.** If `T` is microlocally smooth at `(x, ξ)` for every `x` in
a compact set `K`, then there are an open set `W` containing `K` and an open cone `Γ` containing
`ξ` such that every cutoff `ψ` supported in `W ∪ (dsupport T)ᶜ`, that is, whose support meets the
support of `T` only inside `W`, has localized Fourier transform rapidly decreasing on `Γ`. -/
theorem exists_isOpen_cone_forall_decay_of_isCompact {T : 𝓓'(Ω, ℂ)} {K : Set E} {ξ : E}
    (hK : IsCompact K) (h : ∀ x ∈ K, T.IsMicrolocallySmoothAt x ξ) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ W ∪ (dsupport T)ᶜ →
        ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  -- Finitely many of the neighbourhoods given by `exists_nhds_cone` cover `K`.
  choose U hU Γ hΓ hξΓ hcone hdecay using fun x : K ↦ (h x x.2).exists_nhds_cone
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ interior (U x))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU ⟨x, hx⟩)⟩
  refine ⟨⋃ x ∈ t, interior (U x), isOpen_biUnion fun _ _ ↦ isOpen_interior, ht, ⋂ x ∈ t, Γ x,
    isOpen_biInter_finset fun x _ ↦ hΓ x, mem_iInter₂.2 fun x _ ↦ hξΓ x,
    fun s hs η hη ↦ mem_iInter₂.2 fun x hx ↦ hcone x s hs η (mem_iInter₂.1 hη x hx),
    fun ψ hψ N ↦ ?_⟩
  -- Split `ψ` into pieces supported in these neighbourhoods and one piece off the support of `T`.
  let V : Option t → Set E := fun i ↦ i.elim (dsupport T)ᶜ fun x ↦ interior (U x)
  have hV : ∀ i, IsOpen (V i) := by
    rintro (_ | x)
    exacts [isClosed_dsupport.isOpen_compl, isOpen_interior]
  have hcover : tsupport ψ ⊆ ⋃ i, V i := fun z hz ↦ by
    rcases hψ hz with hz | hz
    · obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz
      exact mem_iUnion.2 ⟨some ⟨x, hx⟩, hzx⟩
    · exact mem_iUnion.2 ⟨none, hz⟩
  obtain ⟨s, ψs, hψs, hsum, -⟩ := ψ.exists_sum_subordinate V hV hcover
  have hpiece (i : s) :
      ∃ C, ∀ η ∈ ⋂ x ∈ t, Γ x, (1 + ‖η‖) ^ N * ‖T.localFourier (ψs i) η‖ ≤ C := by
    obtain ⟨i, hi⟩ := i
    cases i with
    | none => exact ⟨0, fun η _ ↦ by
        simp [localFourier_eq_zero_of_disjoint_dsupport
          (disjoint_left.2 fun _ hz ↦ hψs ⟨none, hi⟩ hz)]⟩
    | some x =>
      obtain ⟨C, hC⟩ := hdecay x (ψs ⟨some x, hi⟩) ((hψs _).trans interior_subset) N
      exact ⟨C, fun η hη ↦ hC η (mem_iInter₂.1 hη x x.2)⟩
  choose C hC using hpiece
  refine ⟨∑ i, C i, fun η hη ↦ ?_⟩
  rw [← hsum, localFourier_sum_cutoff]
  calc (1 + ‖η‖) ^ N * ‖∑ i, T.localFourier (ψs i) η‖
      ≤ ∑ i, (1 + ‖η‖) ^ N * ‖T.localFourier (ψs i) η‖ := by
        rw [← Finset.mul_sum]
        gcongr
        exact norm_sum_le _ _
    _ ≤ ∑ i, C i := Finset.sum_le_sum fun i _ ↦ hC i η hη

/-! ### Bounded families of cutoffs

The decay estimates above are stated for one cutoff at a time. Arguments in which the cutoff
depends on the frequency, such as dividing a cutoff by a symbol `p (x, η)` evaluated at the
frequency `η` itself, need them uniformly over a family of cutoffs `ψ i`, `i ∈ S`, supported in a
fixed compact set and bounded in every `C^n` norm, uniformly in `i ∈ S`. -/

/-- Pairing the Fourier expansion `ContDiffMapSupportedIn.hasSum_fourier_smul_modulate` of `f` in
the modulations of `χ` with `T`, after modulating by `-η`: the localized Fourier transform of `T`
with cutoff `f` is the superposition of the translates of that with cutoff `χ`, with the Fourier
coefficients of `f` as weights. -/
private theorem hasSum_localFourier_ofSupportedIn [MeasurableSpace E] [BorelSpace E]
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hL : ∀ x ∈ (K : Set E), ∀ ℓ : L, x + ℓ ∈ (K : Set E) → ℓ = 0)
    {f χ : 𝓓_{K}(E, ℂ)} (hχ : EqOn χ 1 (support f)) (T : 𝓓'(Ω, ℂ)) (η : E) :
    HasSum (fun m : ZLattice.dual L ↦ ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : E → ℂ) m) *
      T.localFourier (ofSupportedIn hKΩ χ) (η - m)) (T.localFourier (ofSupportedIn hKΩ f) η) := by
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L
    (ofSupportedInCLM ℂ hKΩ ∘L ContDiffMapSupportedIn.modulateCLM (-η))
  have hΛ (h : 𝓓_{K}(E, ℂ)) : Λ h = T.complexPairing (ofSupportedIn hKΩ (h.modulate (-η))) := by
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM,
      ContDiffMapSupportedIn.modulateCLM_apply]
  have h1 : Λ f = T.localFourier (ofSupportedIn hKΩ f) η := by
    rw [hΛ, localFourier_eq_complexPairing_modulate T hKΩ (f := f) fun x ↦ rfl]
  have h2 (m : ZLattice.dual L) (a : ℂ) :
      Λ (a • χ.modulate m) = a * T.localFourier (ofSupportedIn hKΩ χ) (η - m) := by
    rw [map_smul, smul_eq_mul, hΛ, ContDiffMapSupportedIn.modulate_modulate,
      localFourier_eq_complexPairing_modulate T hKΩ (f := χ) (fun x ↦ rfl), neg_sub,
      sub_eq_add_neg]
  have hmap := (ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L f χ hL hχ).map Λ Λ.continuous
  rw [h1] at hmap
  convert hmap using 1
  ext m
  exact (h2 m _).symm

/-- **Uniform Fourier expansion of a bounded family of cutoffs.** Let `ψ i` be test functions
supported in a compact set `K`, with `K ⊆ W ⊆ Ω` for an open set `W`, whose derivatives of each
order are bounded uniformly for `i ∈ S`. There are a cutoff `χ` supported in `W`, a subgroup `L` of
`E` and coefficients `a i m` such that

`T (ψ i e_η) = ∑ m : L, a i m T (χ e_(η - m))`

for every distribution `T`, every `i` and every frequency `η`, and for every `j` the weighted sums
`∑ m, (1 + ‖m‖) ^ j ‖a i m‖` are bounded uniformly for `i ∈ S`. The coefficients are those of
the Fourier series of `ψ i` on a compact neighbourhood of `K`, and their uniform decay comes from
the uniform bounds on the derivatives of `ψ i`. -/
theorem exists_hasSum_localFourier_of_forall_norm_iteratedFDeriv_le {K W : Set E} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hWΩ : W ⊆ Ω) {ι : Type*} {S : Set ι} {ψ : ι → 𝓓(Ω, ℂ)}
    (hψK : ∀ i, tsupport (ψ i) ⊆ K)
    (hψ : ∀ n : ℕ, ∃ B, ∀ i ∈ S, ∀ x, ‖iteratedFDeriv ℝ n (ψ i) x‖ ≤ B) :
    ∃ (χ : 𝓓(Ω, ℂ)) (L : Submodule ℤ E) (a : ι → L → ℂ), tsupport χ ⊆ W ∧
      (∀ j : ℕ, ∃ A, ∀ i ∈ S, Summable (fun m : L ↦ (1 + ‖(m : E)‖) ^ j * ‖a i m‖) ∧
        ∑' m : L, (1 + ‖(m : E)‖) ^ j * ‖a i m‖ ≤ A) ∧
      ∀ (T : 𝓓'(Ω, ℂ)) (i : ι) (η : E),
        HasSum (fun m : L ↦ a i m * T.localFourier χ (η - m)) (T.localFourier (ψ i) η) := by
  borelize E
  -- A compact `K₂` between `K` and `W`, a cutoff `χ` equal to one near `K` and supported in `K₂`.
  obtain ⟨K₂, hK₂, hKK₂, hK₂W⟩ := exists_compact_between hK hW hKW
  obtain ⟨χ₂, hχ₂, -, hχ₂1, -, hχ₂s⟩ := hK.exists_contDiff_cutoff isOpen_interior hKK₂
  let K' : Compacts E := ⟨K₂, hK₂⟩
  have hK'Ω : (K' : Set E) ⊆ Ω := hK₂W.trans hWΩ
  have hχK : support (fun x ↦ (χ₂ x : ℂ)) ⊆ K₂ := fun x hx ↦
    interior_subset (hχ₂s (subset_tsupport _ (by simpa using hx)))
  have hχ₂c : ContDiff ℝ ∞ fun x ↦ (χ₂ x : ℂ) := ofRealCLM.contDiff.comp hχ₂
  let χ : 𝓓_{K'}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hχ₂c hχK
  have hψK₂ (i : ι) : support (ψ i : E → ℂ) ⊆ K₂ :=
    (subset_tsupport _).trans ((hψK i).trans (interior_subset.trans' hKK₂))
  let f (i : ι) : 𝓓_{K'}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset (ψ i).contDiff (hψK₂ i)
  have hχf (i : ι) : EqOn χ 1 (support (f i)) := fun x hx ↦ by
    have h1 : χ₂ x = 1 := interior_subset (hχ₂1 (hψK i (subset_tsupport _ hx)))
    simp [χ, ContDiffMapSupportedIn.coe_of_support_subset, h1]
  -- A lattice none of whose nonzero translates of `K₂` meet `K₂`.
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
  refine ⟨ofSupportedIn hK'Ω χ, ZLattice.dual L,
    fun i m ↦ (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (ψ i : E → ℂ) m, ?_, fun j ↦ ?_, fun T i η ↦ ?_⟩
  · exact (closure_minimal (fun x hx ↦ hχK hx) hK₂.isClosed).trans hK₂W
  · -- The Fourier coefficients decay rapidly, uniformly in `i ∈ S`.
    obtain ⟨A, hA⟩ := TauCeti.exists_forall_tsum_one_add_norm_pow_mul_norm_fourier_le
      (ZLattice.dual L) (fun i ↦ (ψ i).contDiff) hK.measurableSet hK.measure_lt_top.ne hψK hψ j
    refine ⟨‖(ZLattice.covolume L : ℂ)⁻¹‖ * A, fun i hi ↦ ?_⟩
    have heq : (fun m : ZLattice.dual L ↦ (1 + ‖(m : E)‖) ^ j *
        ‖(ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (ψ i : E → ℂ) m‖) = fun m : ZLattice.dual L ↦
          ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ((1 + ‖(m : E)‖) ^ j * ‖𝓕 (ψ i : E → ℂ) m‖) := by
      ext m
      rw [norm_mul]
      ring
    rw [heq, tsum_mul_left]
    exact ⟨(hA i hi).1.mul_left _, by gcongr; exact (hA i hi).2⟩
  · -- Pair the expansion of `ψ i` with `T`; `ψ i` is `f i` as a test function on `Ω`.
    have hψf : ofSupportedIn hK'Ω (f i) = ψ i := by
      ext x
      rfl
    have h := hasSum_localFourier_ofSupportedIn hK'Ω L
      (fun x hx ℓ h ↦ Subtype.ext (hL x hx ℓ ℓ.2 h)) (hχf i) T η
    rwa [hψf] at h

/-- **Uniform polynomial growth.** For a compact set `K ⊆ Ω` there is a degree `k` such that the
localized Fourier transforms of `T` with the cutoffs `ψ i` of any family supported in `K` and
bounded in every `C^n` norm uniformly for `i ∈ S` are `O((1 + ‖η‖) ^ k)`, uniformly for `i ∈ S`.
-/
theorem exists_forall_norm_localFourier_le_of_forall_norm_iteratedFDeriv_le (T : 𝓓'(Ω, ℂ))
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ k : ℕ, ∀ {ι : Type*} (S : Set ι) (ψ : ι → 𝓓(Ω, ℂ)), (∀ i, tsupport (ψ i) ⊆ K) →
      (∀ n : ℕ, ∃ B, ∀ i ∈ S, ∀ x, ‖iteratedFDeriv ℝ n (ψ i) x‖ ≤ B) →
      ∃ C, ∀ i ∈ S, ∀ η, ‖T.localFourier (ψ i) η‖ ≤ C * (1 + ‖η‖) ^ k := by
  -- The degree is that of the cutoffs supported in a fixed compact neighbourhood `K₂` of `K`.
  obtain ⟨K₂, hK₂, hKK₂, hK₂Ω⟩ := exists_compact_between hK Ω.isOpen hKΩ
  obtain ⟨k, hk⟩ := exists_forall_norm_localFourier_le T (K := ⟨K₂, hK₂⟩) hK₂Ω
  refine ⟨k, fun S ψ hψK hψ ↦ ?_⟩
  obtain ⟨χ, L, a, hχW, ha, hsum⟩ := exists_hasSum_localFourier_of_forall_norm_iteratedFDeriv_le hK
    isOpen_interior hKK₂ (interior_subset.trans hK₂Ω) hψK hψ
  obtain ⟨C₀, hC₀⟩ := hk χ (hχW.trans interior_subset)
  obtain ⟨A, hA⟩ := ha k
  refine ⟨|C₀| * A, fun i hi η ↦ ?_⟩
  have hbound := (hsum T i η).norm_le_of_bounded (((hA i hi).1.hasSum.mul_left
    (|C₀| * (1 + ‖η‖) ^ k))) fun m ↦ ?_
  · calc ‖T.localFourier (ψ i) η‖
        ≤ |C₀| * (1 + ‖η‖) ^ k * ∑' m : L, (1 + ‖(m : E)‖) ^ k * ‖a i m‖ := hbound
      _ ≤ |C₀| * (1 + ‖η‖) ^ k * A := by gcongr; exact (hA i hi).2
      _ = |C₀| * A * (1 + ‖η‖) ^ k := by ring
  · -- `1 + ‖η - m‖ ≤ (1 + ‖η‖) (1 + ‖m‖)`.
    have hle : 1 + ‖η - m‖ ≤ (1 + ‖η‖) * (1 + ‖(m : E)‖) := by
      nlinarith [norm_sub_le η m, norm_nonneg η, norm_nonneg (m : E)]
    rw [norm_mul]
    calc ‖a i m‖ * ‖T.localFourier χ (η - m)‖ ≤ ‖a i m‖ * (|C₀| * (1 + ‖η - m‖) ^ k) := by
          gcongr
          exact (hC₀ _).trans (by gcongr; exact le_abs_self _)
      _ ≤ ‖a i m‖ * (|C₀| * ((1 + ‖η‖) * (1 + ‖(m : E)‖)) ^ k) := by gcongr
      _ = |C₀| * (1 + ‖η‖) ^ k * ((1 + ‖(m : E)‖) ^ k * ‖a i m‖) := by rw [mul_pow]; ring

/-- **Uniform decay over bounded families of cutoffs.** If `T` is microlocally smooth at `(x, ξ)`,
there are an open neighbourhood `U ⊆ Ω` of `x` and an open cone `Γ` containing `ξ` such that for
every family of cutoffs `ψ i` supported in a compact subset of `U` and bounded in every `C^n` norm
uniformly for `i ∈ S`, the localized Fourier transforms of `T` with the cutoffs `ψ i` decay rapidly
on `Γ`, uniformly for `i ∈ S`. This is the uniform form of
`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`. -/
theorem IsMicrolocallySmoothAt.exists_nhds_cone_of_forall_norm_iteratedFDeriv_le
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (h : T.IsMicrolocallySmoothAt x ξ) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ {ι : Type*} (S : Set ι) (ψ : ι → 𝓓(Ω, ℂ)),
        (∀ i, tsupport (ψ i) ⊆ K) →
        (∀ n : ℕ, ∃ B, ∀ i ∈ S, ∀ y, ‖iteratedFDeriv ℝ n (ψ i) y‖ ≤ B) →
        ∀ N : ℕ, ∃ C, ∀ i ∈ S, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier (ψ i) η‖ ≤ C := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 h
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U₁, hU₁, Γ₁, hΓ₁, hξ₁, hcone₁, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨Γ, hΓ, hξ, hcone, c, hc, hΓΓ₁⟩ := hΓ₁.exists_cone_closedBall_subset hcone₁ hξ₁
  refine ⟨interior U₁ ∩ Ω, isOpen_interior.inter Ω.isOpen, ⟨mem_interior_iff_mem_nhds.2 hU₁, hx⟩,
    inter_subset_right, Γ, hΓ, hξ, hcone, fun K hK hKU {ι} S ψ hψK hψ N ↦ ?_⟩
  -- Expand the cutoffs in the modulations of one cutoff `χ` supported in `U₁`, at which `T` decays
  -- on `Γ₁`; the decay passes to the translates on the smaller cone `Γ`, uniformly in `i`.
  obtain ⟨χ, L, a, hχW, ha, hsum⟩ := exists_hasSum_localFourier_of_forall_norm_iteratedFDeriv_le hK
    (isOpen_interior.inter Ω.isOpen) hKU inter_subset_right hψK hψ
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T χ
  obtain ⟨D, hD⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_le_mul_tsum_of_hasSum
    (v := fun m : L ↦ (m : E)) (𝕜 := ℂ) hF hc hΓΓ₁
    (hdecay χ (hχW.trans (inter_subset_left.trans interior_subset)) N)
  obtain ⟨A, hA⟩ := ha (N + 2 * k)
  refine ⟨|D| * A, fun i hi η hη ↦ (hD (a i) (hA i hi).1 η hη _ (hsum T i η)).trans ?_⟩
  calc D * ∑' m : L, (1 + ‖(m : E)‖) ^ (N + 2 * k) * ‖a i m‖
      ≤ |D| * ∑' m : L, (1 + ‖(m : E)‖) ^ (N + 2 * k) * ‖a i m‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self D) (tsum_nonneg fun m ↦ by positivity)
    _ ≤ |D| * A := by gcongr; exact (hA i hi).2

/-- The sum of two distributions microlocally smooth at `(x, ξ)` is microlocally smooth there. -/
theorem IsMicrolocallySmoothAt.add {S T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hS : S.IsMicrolocallySmoothAt x ξ) (hT : T.IsMicrolocallySmoothAt x ξ) :
    (S + T).IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 hS
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdS⟩ := hS.exists_nhds_cone
  obtain ⟨V, hV, Γ', hΓ', hξ', hcone', hdT⟩ := hT.exists_nhds_cone
  -- A cutoff supported in `U ∩ V` serves for both distributions, on the cone `Γ ∩ Γ'`.
  obtain ⟨ψ, hψ, hψx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU hV) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψx], Γ ∩ Γ', hΓ.inter hΓ', ⟨hξ, hξ'⟩,
    fun t ht η hη ↦ ⟨hcone t ht η hη.1, hcone' t ht η hη.2⟩, fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := hdS ψ (hψ.trans (inter_subset_left.trans inter_subset_left)) N
  obtain ⟨C', hC'⟩ := hdT ψ (hψ.trans (inter_subset_left.trans inter_subset_right)) N
  refine ⟨C + C', fun η hη ↦ ?_⟩
  rw [localFourier_add]
  calc (1 + ‖η‖) ^ N * ‖S.localFourier ψ η + T.localFourier ψ η‖
      ≤ (1 + ‖η‖) ^ N * ‖S.localFourier ψ η‖ + (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ := by
        rw [← mul_add]
        gcongr
        exact norm_add_le _ _
    _ ≤ C + C' := add_le_add (hC η hη.1) (hC' η hη.2)

/-- The wave front set of a sum lies in the union of the wave front sets. -/
theorem waveFrontSet_add_subset (S T : 𝓓'(Ω, ℂ)) :
    (S + T).waveFrontSet ⊆ S.waveFrontSet ∪ T.waveFrontSet := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, h⟩ := mem_waveFrontSet_iff.1 hp
  by_contra hST
  simp only [mem_union, mem_waveFrontSet_iff, not_or, not_and, not_not] at hST
  exact h ((hST.1 hx hξ).add (hST.2 hx hξ))

/-- The wave front set of a difference lies in the union of the wave front sets. -/
theorem waveFrontSet_sub_subset (S T : 𝓓'(Ω, ℂ)) :
    (S - T).waveFrontSet ⊆ S.waveFrontSet ∪ T.waveFrontSet := by
  simpa [sub_eq_add_neg] using waveFrontSet_add_subset S (-T)

/-- The wave front set of a finite sum lies in the union of the wave front sets. -/
theorem waveFrontSet_sum_subset {ι : Type*} (s : Finset ι) (T : ι → 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, T i).waveFrontSet ⊆ ⋃ i ∈ s, (T i).waveFrontSet := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    exact (waveFrontSet_add_subset _ _).trans (union_subset_union_right _ ih)

section SmulLeft

variable {g : E → ℝ}

/-- A smooth multiple `g T` of a distribution microlocally smooth at `(x, ξ)` is microlocally
smooth there. -/
theorem IsMicrolocallySmoothAt.smulLeftCLM {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySmoothAt x ξ) (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 h
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  -- The same cutoff `φ` works for `g T` on the smaller cone `Γ'`, since `g T` with cutoff `φ`
  -- is `T` with cutoff `g φ`.
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, hφx, Γ', hΓ'o, hξ', hcone', fun N ↦ ?_⟩
  simp only [localFourier_smulLeftCLM]
  exact exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul
    (ofRealCLM.contDiff.comp hg).contDiffOn (fun y ↦ by simp [mul_comm]) hc hΓ' (hdecay N)

/-- Where `g` does not vanish, a smooth multiple `g T` is microlocally smooth exactly where `T`
is. -/
theorem isMicrolocallySmoothAt_smulLeftCLM_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E} (hg : ContDiff ℝ ∞ g)
    (hx : g x ≠ 0) :
    (smulLeftCLM hg T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smulLeftCLM hg⟩
  -- A cutoff `φ` for `g T` gives the cutoff `g φ` for `T`, which does not vanish at `x`.
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 h
  refine isMicrolocallySmoothAt_iff.2
    ⟨TestFunction.smulLeftCLM hg φ, by simp [hx, hφx], Γ, hΓ, hξ, hcone, ?_⟩
  simpa using hdecay

/-- **Smooth multiplication** (Hörmander I, §8.1). The wave front set of a smooth multiple
`g T` lies in the wave front set of `T`, over the support of `g`. -/
theorem waveFrontSet_smulLeftCLM_subset (T : 𝓓'(Ω, ℂ)) (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).waveFrontSet ⊆ T.waveFrontSet ∩ tsupport g ×ˢ univ := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
  have hxg : x ∈ dsupport (smulLeftCLM hg T) := (waveFrontSet_subset_dsupport _ hp).1
  rw [coe_smulLeftCLM] at hxg
  exact ⟨mem_waveFrontSet_iff.2 ⟨hx, hξ, fun h ↦ hT (h.smulLeftCLM hg)⟩,
    (dsupport_comp_smulLeftCLM_subset T hg hxg).1, trivial⟩

/-- Over the points where `g` does not vanish, a smooth multiple `g T` has the same wave front set
as `T`. -/
theorem mem_waveFrontSet_smulLeftCLM_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E} (hg : ContDiff ℝ ∞ g)
    (hx : g x ≠ 0) : (x, ξ) ∈ (smulLeftCLM hg T).waveFrontSet ↔ (x, ξ) ∈ T.waveFrontSet := by
  simp [isMicrolocallySmoothAt_smulLeftCLM_iff hg hx]

/-- Multiplying by a smooth function that vanishes nowhere on `Ω` does not change the wave front
set. -/
theorem waveFrontSet_smulLeftCLM_of_ne_zero (T : 𝓓'(Ω, ℂ)) (hg : ContDiff ℝ ∞ g)
    (hg0 : ∀ x ∈ Ω, g x ≠ 0) : (smulLeftCLM hg T).waveFrontSet = T.waveFrontSet := by
  ext ⟨x, ξ⟩
  by_cases hx : x ∈ Ω
  · exact mem_waveFrontSet_smulLeftCLM_iff hg (hg0 x hx)
  · simp [hx]

end SmulLeft

section Restriction

variable {Ω' : Opens E}

/-- At a point of an open subset `Ω' ≤ Ω`, the restriction `T|_{Ω'}` is microlocally smooth
exactly where `T` is. -/
theorem isMicrolocallySmoothAt_restrictCLM_iff (h : Ω' ≤ Ω) {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hx : x ∈ Ω') :
    (restrictCLM T : 𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ := by
  constructor
  · -- A cutoff on `Ω'`, extended by zero, is a cutoff on `Ω`.
    intro hT
    obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hT
    exact isMicrolocallySmoothAt_iff.2 ⟨TestFunction.monoCLM ℝ φ, by simpa [h] using hφx, Γ, hΓ,
      hξ, hcone, by simpa using hdecay⟩
  · -- Every cutoff supported near `x` works for `T`; take one supported in `Ω'`.
    intro hT
    obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := hT.exists_nhds_cone
    obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (Ω := Ω') (n := ⊤)
      (inter_mem hU (Ω'.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
    refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
    simp only [localFourier_restrictCLM]
    exact hdecay _ (by simpa [h] using hφ.trans inter_subset_left) N

/-- **Restriction** to an open subset `Ω' ≤ Ω` cuts the wave front set down to the points of
`Ω'`. -/
theorem waveFrontSet_restrictCLM (h : Ω' ≤ Ω) (T : 𝓓'(Ω, ℂ)) :
    (restrictCLM T : 𝓓'(Ω', ℂ)).waveFrontSet = T.waveFrontSet ∩ (Ω' : Set E) ×ˢ univ := by
  ext ⟨x, ξ⟩
  simp only [mem_inter_iff, mem_waveFrontSet_iff, mem_prod, mem_univ, and_true]
  constructor
  · rintro ⟨hx, hξ, hT⟩
    exact ⟨⟨h hx, hξ, fun h' ↦ hT ((isMicrolocallySmoothAt_restrictCLM_iff h hx).2 h')⟩, hx⟩
  · rintro ⟨⟨-, hξ, hT⟩, hx⟩
    exact ⟨hx, hξ, fun h' ↦ hT ((isMicrolocallySmoothAt_restrictCLM_iff h hx).1 h')⟩

/-- The wave front set is local: two distributions with the same restriction to an open set
`U ≤ Ω` have the same wave front set over `U`. -/
theorem waveFrontSet_inter_eq_of_restrictCLM_eq {S T : 𝓓'(Ω, ℂ)} {U : Opens E} (hU : U ≤ Ω)
    (h : (restrictCLM S : 𝓓'(U, ℂ)) = restrictCLM T) :
    S.waveFrontSet ∩ (U : Set E) ×ˢ univ = T.waveFrontSet ∩ (U : Set E) ×ˢ univ := by
  rw [← waveFrontSet_restrictCLM hU, h, waveFrontSet_restrictCLM hU]

end Restriction

end Distribution
