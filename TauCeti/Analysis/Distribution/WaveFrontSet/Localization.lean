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
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Localization of the wave front set

The definition of microlocal smoothness of a distribution `T` at `(x, ξ)` asks for *one* cutoff `φ`
with `φ x ≠ 0` whose localized Fourier transform `η ↦ T (φ e_η)` decays rapidly in an open cone
around `ξ`. This file shows that the choice of cutoff does not matter near `x`: multiplying `φ` by
a smooth function keeps rapid decay, at the price of shrinking the cone (Hörmander I,
Lemma 8.1.1). Consequently the wave front set of a sum lies in the union of the wave front sets.

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
  grows at most polynomially.
* `Distribution.exists_hasSum_localFourier_of_eq_mul`: the localized Fourier transform with
  cutoff `φ g` is a rapidly decreasing superposition of translates of the one with cutoff `φ`.
* `Distribution.exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul`: decay of each order
  of the localized Fourier transform on a set `Γ` survives multiplication of the cutoff by a smooth
  function, on any set `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)` lie in `Γ`.
* `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`: at a point of microlocal smoothness
  there are a neighbourhood `U` of `x` and an open cone `Γ` around `ξ` such that every cutoff
  supported in `U` has localized Fourier transform rapidly decreasing on `Γ`.
* `Distribution.IsMicrolocallySmoothAt.add`, `Distribution.waveFrontSet_add_subset`,
  `Distribution.waveFrontSet_sub_subset`, `Distribution.waveFrontSet_sum_subset`: the wave front
  set of a sum lies in the union of the wave front sets.

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
/-- **Polynomial growth of the localized Fourier transform.** For a complex distribution `T` and a
complex test function `φ`, the localized Fourier transform `η ↦ T (φ e_η)` is bounded by
`C (1 + ‖η‖) ^ k` for some `C` and `k`. -/
theorem exists_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (C : ℝ) (k : ℕ), ∀ η, ‖T.localFourier φ η‖ ≤ C * (1 + ‖η‖) ^ k := by
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩
  have hKΩ : (K : Set E) ⊆ Ω := φ.tsupport_subset
  let φK : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset φ.contDiff (subset_tsupport _)
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L ofSupportedInCLM ℂ hKΩ
  -- The modulations of `φ` grow polynomially in every continuous seminorm.
  obtain ⟨C, k, hC⟩ := φK.exists_seminorm_modulate_le ((normSeminorm ℂ ℂ).comp Λ.toLinearMap)
    (continuous_norm.comp Λ.continuous)
  refine ⟨C, k, fun η ↦ ?_⟩
  have h : T.localFourier φ η = Λ (φK.modulate (-η)) := by
    rw [ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    exact localFourier_eq_complexPairing_modulate T hKΩ
      (fun _ ↦ by simp [φK, ContDiffMapSupportedIn.coe_of_support_subset]) η
  simpa [h] using hC (-η)

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
  obtain ⟨C, hC⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum
    (v := fun m : L ↦ (m : E)) ha hF hc hΓ' hdecay
  exact ⟨C, fun η hη ↦ hC η hη _ (hsum η)⟩

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
  -- A cutoff `χ` equal to one near `x`, supported where `φ ≠ 0`.
  obtain ⟨χ, hχ, -, hχ1, -, hχs⟩ := (isCompact_singleton (x := x)).exists_contDiff_cutoff
    (isOpen_ne_fun φ.continuous continuous_const) (singleton_subset_iff.2 hφx)
  refine ⟨interior (χ ⁻¹' {1}), isOpen_interior.mem_nhds (hχ1 rfl), Γ', hΓ'o, hξ', hcone',
    fun ψ hψ N ↦ ?_⟩
  -- Write `ψ = φ (θ ψ)` with the smooth function `θ = χ / φ`.
  let θ : E → ℂ := fun y ↦ (χ y : ℂ) * (φ y)⁻¹
  have hθ : ContDiff ℝ ∞ θ := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : φ y = 0
    · have hy' : y ∉ tsupport χ := fun h ↦ hχs h hy
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy'] with z hz
      simp [θ, hz]
    · exact (ofRealCLM.contDiff.comp hχ).contDiffAt.mul (φ.contDiff.contDiffAt.fun_inv hy)
  refine exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul (hθ.mul ψ.contDiff).contDiffOn
    (fun y ↦ ?_) hc hΓ' (hdecay N)
  by_cases hψy : ψ y = 0
  · simp [hψy]
  · have hχy : χ y = 1 := interior_subset (hψ (subset_tsupport _ hψy))
    have hφy : φ y ≠ 0 := hχs (subset_tsupport _ (by simp [hχy]))
    simp only [θ, hχy, ofReal_one]
    field_simp

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

end Distribution
