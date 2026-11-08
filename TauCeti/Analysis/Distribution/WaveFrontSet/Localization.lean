/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.FourierSeries
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.PositiveDefinite.FourierAtom

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

* `Distribution.exists_norm_localFourier_le`: the localized Fourier transform of a distribution
  grows at most polynomially.
* `Distribution.exists_hasSum_localFourier_of_eq_mul`: the localized Fourier transform with
  cutoff `φ g` is a rapidly decreasing superposition of translates of the one with cutoff `φ`.
* `Distribution.exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul`: rapid decay of the
  localized Fourier transform on an open cone `Γ` survives multiplication of the cutoff by a smooth
  function, on any cone `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)` lie in `Γ`.
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
/-- Modulating the character `x ↦ 𝐞 (-⟪x, η⟫)` by `exp (2πi ⟪x, w⟫)` shifts its frequency
to `η - w`. -/
private theorem cexp_mul_fourierChar (x w η : E) :
    cexp (2 * Real.pi * I * ⟪x, w⟫) * (𝐞 (-⟪x, η⟫) : ℂ) = 𝐞 (-⟪x, η - w⟫) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add, inner_sub_right]
  congr 1
  push_cast
  ring

omit [FiniteDimensional ℝ E] in
/-- **Polynomial growth of the localized Fourier transform.** For a complex distribution `T` and a
complex test function `φ`, the localized Fourier transform `η ↦ T (φ e_η)` is bounded by
`C (1 + ‖η‖) ^ k` for some `C ≥ 0` and `k`. -/
theorem exists_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ η, ‖T.localFourier φ η‖ ≤ C * (1 + ‖η‖) ^ k := by
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩
  have hKΩ : (K : Set E) ⊆ Ω := φ.tsupport_subset
  let φK : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset φ.contDiff (subset_tsupport _)
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L ofSupportedInCLM ℂ hKΩ
  -- The modulations of `φ` grow polynomially in every continuous seminorm.
  obtain ⟨C, k, hC⟩ := φK.exists_seminorm_modulate_le ((normSeminorm ℂ ℂ).comp Λ.toLinearMap)
    (continuous_norm.comp Λ.continuous)
  refine ⟨max C 0, k, le_max_right _ _, fun η ↦ ?_⟩
  have h : T.localFourier φ η = Λ (φK.modulate (-η)) := by
    rw [ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    refine localFourier_eq T φ fun x ↦ ?_
    simp only [coe_ofSupportedIn, ContDiffMapSupportedIn.modulate_apply,
      smul_eq_mul, φK, ContDiffMapSupportedIn.coe_of_support_subset]
    rw [mul_comm, Real.fourierChar_apply, inner_neg_right]
    congr 2
    push_cast
    ring
  calc ‖T.localFourier φ η‖ = ‖Λ (φK.modulate (-η))‖ := by rw [h]
    _ ≤ C * (1 + ‖-η‖) ^ k := hC (-η)
    _ ≤ max C 0 * (1 + ‖η‖) ^ k := by
      rw [norm_neg]
      gcongr
      exact le_max_left _ _

/-- **The localized Fourier transform of a smooth multiple.** If the cutoff `ψ` is `φ g` with `g`
smooth, then there are a full lattice `L` and rapidly decreasing coefficients `a : L → ℂ` such that

`T (ψ e_η) = ∑ m : L, a m T (φ e_(η - m))`

for every frequency `η`. This is the discrete form of the convolution formula
`(φ g T)^ = ĝ * (φ T)^`: the coefficients are those of a Fourier series of `g` on a compact set
around the support of `φ`. -/
theorem exists_hasSum_localFourier_of_eq_mul (T : 𝓓'(Ω, ℂ)) {φ ψ : 𝓓(Ω, ℂ)} {g : E → ℂ}
    (hg : ContDiff ℝ ∞ g) (hψ : ∀ x, ψ x = φ x * g x) :
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
  have hχ₁c : ContDiff ℝ ∞ fun x ↦ (χ₁ x : ℂ) := ofRealCLM.contDiff.comp hχ₁
  have hχ₂c : ContDiff ℝ ∞ fun x ↦ (χ₂ x : ℂ) := ofRealCLM.contDiff.comp hχ₂
  have hfK : support (fun x ↦ (χ₁ x : ℂ) * g x) ⊆ K₂ := fun x hx ↦
    interior_subset (hK₁K₂ (hχ₁K₁ (subset_tsupport _ (by simpa using left_ne_zero_of_mul hx))))
  have hχK : support (fun x ↦ (χ₂ x : ℂ)) ⊆ K₂ := fun x hx ↦
    interior_subset (hχ₂s (subset_tsupport _ (by simpa using hx)))
  let f : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset (hχ₁c.mul hg) hfK
  let χ : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hχ₂c hχK
  have hχ : EqOn χ 1 (support f) := fun x hx ↦ by
    have hx' : χ₁ x ≠ 0 := by
      simpa [f, ContDiffMapSupportedIn.coe_of_support_subset] using left_ne_zero_of_mul hx
    simp [χ, ContDiffMapSupportedIn.coe_of_support_subset, hχ₂K₁ (hχ₁K₁ (subset_tsupport _ hx'))]
  -- A lattice none of whose nonzero translates of `K` meet `K`.
  obtain ⟨R, hR⟩ := hK₂.isBounded.subset_closedBall 0
  obtain ⟨L, _, _, hL⟩ := ZLattice.exists_forall_ne_zero_lt_norm (F := E) (2 * R)
  have hsep : ∀ x ∈ K, ∀ ℓ : L, x + ℓ ∈ K → ℓ = 0 := by
    intro x hx ℓ hℓ
    by_contra hne
    have h2R := hL ℓ ℓ.2 (by simpa using hne)
    have hx' := mem_closedBall_zero_iff.1 (hR hx)
    have hℓ' := mem_closedBall_zero_iff.1 (hR hℓ)
    have : ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖ := by
      simpa using norm_sub_le (x + (ℓ : E)) x
    linarith
  have hexp := ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L f χ hsep hχ
  refine ⟨ZLattice.dual L, fun m ↦ (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : E → ℂ) m,
    fun j ↦ ?_, fun η ↦ ?_⟩
  · -- The coefficients are values of the Fourier transform of a Schwartz function.
    let fS : 𝓢(E, ℂ) := f.hasCompactSupport.toSchwartzMap f.contDiff
    have hfS : (fS : E → ℂ) = f := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have hdecay := ZLattice.summable_one_add_norm_pow_mul_norm (ZLattice.dual L) (𝓕 fS) j
    rw [SchwartzMap.fourier_coe, hfS] at hdecay
    refine (hdecay.mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖).congr fun m ↦ ?_
    rw [norm_mul]
    ring
  · -- Pair the expansion with `T`, after multiplying by `x ↦ φ x 𝐞 (-⟪x, η⟫)`.
    have hw : ContDiff ℝ ∞ fun x ↦ φ x * TauCeti.fourierAtom η x :=
      φ.contDiff.mul (TauCeti.contDiff_fourierAtom η)
    let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L
      (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hw ∘L ofSupportedInCLM ℂ hKΩ)
    have hΛ (h : 𝓓_{K}(E, ℂ)) : Λ h = T.complexPairing
        (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hw (ofSupportedIn hKΩ h)) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    have h1 : Λ f = T.localFourier ψ η := by
      rw [hΛ, localFourier_eq T ψ fun x ↦ ?_]
      simp only [TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
        coe_ofSupportedIn, ContDiffMapSupportedIn.coe_of_support_subset, f, hψ,
        TauCeti.fourierAtom_eq_fourierChar]
      by_cases hx : φ x = 0
      · simp [hx]
      · simp only [hχ₁φ hx, ofReal_one]
        ring
    have h2 (m : ZLattice.dual L) (a : ℂ) :
        Λ (a • χ.modulate m) = a * T.localFourier φ (η - m) := by
      rw [map_smul, smul_eq_mul, hΛ, localFourier_eq T φ (η := η - m) fun x ↦ ?_]
      simp only [TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
        coe_ofSupportedIn, ContDiffMapSupportedIn.modulate_apply,
        ContDiffMapSupportedIn.coe_of_support_subset, χ, smul_eq_mul,
        TauCeti.fourierAtom_eq_fourierChar]
      by_cases hx : φ x = 0
      · simp [hx]
      · simp only [hχ₂K₁ (hφK₁.trans interior_subset (subset_tsupport _ hx)), ofReal_one,
          mul_one]
        rw [← cexp_mul_fourierChar x m η]
        ring
    have hmap := hexp.map Λ Λ.continuous
    rw [h1] at hmap
    convert hmap using 1
    ext m
    exact (h2 m _).symm

/-- **Localization of rapid decay** (Hörmander I, Lemma 8.1.1). Suppose the localized Fourier
transform of `T` with cutoff `φ` decays rapidly on a set `Γ`, and `Γ'` is a set such that for some
`c > 0` the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`. Then for every cutoff
`ψ = φ g` with `g` smooth, the localized Fourier transform of `T` with cutoff `ψ` decays rapidly
on `Γ'`. Every open cone around a point of an open cone `Γ` contains such a `Γ'`
(`IsOpen.exists_cone_closedBall_subset`). -/
theorem exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul {T : 𝓓'(Ω, ℂ)}
    {φ ψ : 𝓓(Ω, ℂ)} {g : E → ℂ} (hg : ContDiff ℝ ∞ g) (hψ : ∀ x, ψ x = φ x * g x)
    {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C) (N : ℕ) :
    ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C := by
  obtain ⟨L, a, ha, hsum⟩ := exists_hasSum_localFourier_of_eq_mul T hg hψ
  obtain ⟨C₀, k, hC₀, hF⟩ := exists_norm_localFourier_le T φ
  obtain ⟨C, hC⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum
    (v := fun m : L ↦ (m : E)) ha hC₀ hF hc hΓ' hdecay N
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
  refine exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul (hθ.mul ψ.contDiff)
    (fun y ↦ ?_) hc hΓ' hdecay N
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
