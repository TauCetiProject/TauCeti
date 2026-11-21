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
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
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
  grows at most polynomially, with a degree and a constant that are uniform over the cutoffs
  supported in a fixed compact set with bounded derivatives
  (`Distribution.exists_forall_norm_localFourier_le`); it is moreover Lipschitz with a
  polynomially growing constant (`Distribution.exists_norm_localFourier_sub_le`).
* `Distribution.exists_hasSum_localFourier_of_eq_mul`: the localized Fourier transform with
  cutoff `φ g` is a rapidly decreasing superposition of translates of the one with cutoff `φ`;
  `Distribution.hasSum_localFourier_ofSupportedIn` is the same formula for a cutoff `φ` supported
  in a compact set `K` and a fixed cutoff `χ` equal to one on its support, with the explicit
  Fourier coefficients of `φ`.
* `Distribution.exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul`: decay of each order
  of the localized Fourier transform on a set `Γ` survives multiplication of the cutoff by a smooth
  function, on any set `Γ'` whose conic neighbourhoods `closedBall η (c ‖η‖)` lie in `Γ`.
* `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`: at a point of microlocal smoothness
  there are a neighbourhood `U` of `x` and an open cone `Γ` around `ξ` such that every cutoff
  supported in `U` has localized Fourier transform rapidly decreasing on `Γ`;
  `IsMicrolocallySmoothAt.exists_nhds_cone_forall_one_add_norm_pow_mul_norm_localFourier_le`
  makes the decay uniform over the cutoffs supported in `U` with bounded derivatives of some order,
  so that it applies to cutoffs depending on the frequency.
* `Distribution.exists_isOpen_cone_forall_decay_of_isCompact`: the same holds uniformly over a
  compact set `K` of points of microlocal smoothness: there is an open `W ⊇ K` such that it holds
  for every cutoff supported in `W ∪ (dsupport T)ᶜ`, that is, whose support meets the support of
  `T` only inside `W`.
* `Distribution.exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint`: rapid decay
  of a localized Fourier transform on a closed cone of directions avoiding the wave front set over
  the support of the cutoff.
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
complex distribution `T` and a compact set `K ⊆ Ω` there are a degree `k` and a constant `C` such
that for every complex test function `φ` supported in `K` whose derivatives of order at most `k`
are bounded by `B`, the localized Fourier transform `η ↦ T (φ e_η)` is bounded by
`C B (1 + ‖η‖) ^ k`. -/
theorem exists_forall_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ B : ℝ,
      (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ B) →
        ∀ η, ‖T.localFourier φ η‖ ≤ C * B * (1 + ‖η‖) ^ k := by
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L ofSupportedInCLM ℂ hKΩ
  -- The modulations of a cutoff grow polynomially in every continuous seminorm.
  obtain ⟨k, C, hk⟩ := ContDiffMapSupportedIn.exists_seminorm_modulate_le
    ((normSeminorm ℂ ℂ).comp Λ.toLinearMap) (continuous_norm.comp Λ.continuous)
  refine ⟨k, max C 0, le_max_right _ _, fun φ hφ B hB η ↦ ?_⟩
  let φK : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset φ.contDiff ((subset_tsupport _).trans hφ)
  have h : T.localFourier φ η = Λ (φK.modulate (-η)) := by
    rw [ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM]
    exact localFourier_eq_complexPairing_modulate T hKΩ
      (fun _ ↦ by simp [φK, ContDiffMapSupportedIn.coe_of_support_subset]) η
  have hS : ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k φK ≤ B :=
    ContDiffMapSupportedIn.supSeminorm_le_of_forall_norm_iteratedFDeriv_le
      ((norm_nonneg _).trans (hB 0 (Nat.zero_le _) η)) hB
  calc ‖T.localFourier φ η‖ ≤ C * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k φK *
        (1 + ‖-η‖) ^ k := by simpa [h] using hk φK (-η)
    _ ≤ max C 0 * B * (1 + ‖η‖) ^ k := by
        rw [norm_neg]
        gcongr
        exact le_max_left _ _

omit [FiniteDimensional ℝ E] in
/-- **Polynomial growth of the localized Fourier transform.** For a complex distribution `T` and a
complex test function `φ`, the localized Fourier transform `η ↦ T (φ e_η)` is bounded by
`C (1 + ‖η‖) ^ k` for some `C` and `k`. -/
theorem exists_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (C : ℝ) (k : ℕ), ∀ η, ‖T.localFourier φ η‖ ≤ C * (1 + ‖η‖) ^ k := by
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩
  obtain ⟨k, C, -, hk⟩ := exists_forall_norm_localFourier_le T (K := K) φ.tsupport_subset
  let φK : 𝓓_{K}(E, ℂ) :=
    ContDiffMapSupportedIn.of_support_subset φ.contDiff (subset_tsupport _)
  refine ⟨C * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k φK, k,
    hk φ subset_rfl _ fun i hi x ↦ ?_⟩
  have h := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ (i := i) (f := φK)
    (x := x)
  simp only [φK] at h
  exact h.trans (Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K)
    (Finset.mem_Iic.2 hi) φK)

omit [FiniteDimensional ℝ E] in
/-- Leibniz's rule for the derivatives of `(1 - e_θ) f`, where `e_θ = fourierAtom θ`: if the
derivatives of `f` of order at most `i` at `x` are bounded by `S`, and `‖θ‖ ≤ 1`, the derivative
of order `i` of `(1 - e_θ) f` at `x` is at most `2π (1 + 2π) ^ i (1 + ‖x‖) S ‖θ‖`. -/
private theorem norm_iteratedFDeriv_one_sub_fourierAtom_mul_le {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) {θ : E} (hθ : ‖θ‖ ≤ 1) (x : E) {i : ℕ} {S : ℝ}
    (hS : ∀ m ≤ i, ‖iteratedFDeriv ℝ m f x‖ ≤ S) :
    ‖iteratedFDeriv ℝ i (fun y ↦ (1 - TauCeti.fourierAtom θ y) * f y) x‖ ≤
      2 * Real.pi * (1 + 2 * Real.pi) ^ i * (1 + ‖x‖) * S * ‖θ‖ := by
  refine (norm_iteratedFDeriv_mul_le (contDiff_const.sub (TauCeti.contDiff_fourierAtom θ)) hf x
    (by exact_mod_cast le_top)).trans ?_
  calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (fun y ↦ 1 - TauCeti.fourierAtom θ y) x‖ *
          ‖iteratedFDeriv ℝ (i - j) f x‖
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ((2 * Real.pi) ^ (j + 1) * (1 + ‖x‖) * ‖θ‖) * S := by
        gcongr with j _
        · exact TauCeti.norm_iteratedFDeriv_one_sub_fourierAtom_le hθ x j
        · exact hS _ (Nat.sub_le i j)
    _ = 2 * Real.pi * (1 + ‖x‖) * S * ‖θ‖ * ∑ j ∈ Finset.range (i + 1),
          (2 * Real.pi) ^ j * 1 ^ (i - j) * (i.choose j : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
    _ = _ := by
        rw [← add_pow, add_comm (2 * Real.pi)]
        ring

omit [FiniteDimensional ℝ E] in
/-- **The localized Fourier transform is Lipschitz with polynomially growing constant.** For a
complex distribution `T` and a complex test function `φ` there are `A` and `k` with
`‖T (φ e_η) - T (φ e_ζ)‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` whenever `‖η - ζ‖ ≤ 1`. Indeed
`φ e_η - φ e_ζ = (1 - e_(ζ - η)) φ e_η`, and the derivatives of the cutoff `(1 - e_(ζ - η)) φ`
are `O(‖η - ζ‖)`. -/
theorem exists_norm_localFourier_sub_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (A : ℝ) (k : ℕ), ∀ η ζ : E, ‖η - ζ‖ ≤ 1 →
      ‖T.localFourier φ η - T.localFourier φ ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖ := by
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩
  obtain ⟨k, C, -, hC⟩ := exists_forall_norm_localFourier_le T (K := K) φ.tsupport_subset
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.exists_norm_le
  -- A bound `S` for the derivatives of `φ` of order at most `k`.
  obtain ⟨S, hS0, hS⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff k
  set B := 2 * Real.pi * (1 + 2 * Real.pi) ^ k * (1 + |R|) * S
  refine ⟨C * B, k, fun η ζ hηζ ↦ ?_⟩
  set θ := ζ - η
  have hθ : ‖θ‖ = ‖η - ζ‖ := norm_sub_rev _ _
  -- The difference of the localized transforms is the one with cutoff `ψ = (1 - e_θ) φ`.
  let ψ : 𝓓(Ω, ℂ) := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    ((contDiff_const (c := (1 : ℂ))).sub (TauCeti.contDiff_fourierAtom θ)) φ
  have hψ : (ψ : E → ℂ) = fun x ↦ (1 - TauCeti.fourierAtom θ x) * φ x := by
    ext x
    simp [ψ, bilinLeftCLM_apply, mul_comm]
  have hdiff : T.localFourier φ η - T.localFourier φ ζ = T.localFourier ψ η := by
    rw [localFourier_def, localFourier_def, localFourier_def, ← map_sub]
    congr 1
    ext x
    have hζ : ζ = η + θ := by simp [θ]
    simp only [FunLike.coe_sub, Pi.sub_apply, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
      ψ, hζ, TauCeti.fourierAtom_add_left]
    ring
  have hsupp : tsupport ψ ⊆ K := by
    rw [hψ]
    exact tsupport_mul_subset_right
  -- The derivatives of `ψ` of order at most `k` are at most `B ‖θ‖`.
  have hψder : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i ψ x‖ ≤ B * ‖θ‖ := by
    intro i hi x
    by_cases hx : x ∈ tsupport φ
    · rw [hψ]
      refine (norm_iteratedFDeriv_one_sub_fourierAtom_mul_le φ.contDiff (hθ ▸ hηζ) x
        fun m hm ↦ hS m (hm.trans hi) x).trans ?_
      have hpow : (1 + 2 * Real.pi) ^ i ≤ (1 + 2 * Real.pi) ^ k :=
        pow_le_pow_right₀ (by linarith [Real.pi_pos]) hi
      have hxR : 1 + ‖x‖ ≤ 1 + |R| := by linarith [hR x hx, le_abs_self R]
      simp only [B]
      gcongr
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp (tsupport_iteratedFDeriv_subset i h)),
        norm_zero]
      positivity
  rw [hdiff]
  calc ‖T.localFourier ψ η‖ ≤ C * (B * ‖θ‖) * (1 + ‖η‖) ^ k := hC ψ hsupp _ hψder η
    _ = _ := by rw [hθ]; ring

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
    (fun x hx ℓ h ↦ Subtype.ext (hL x hx ℓ ℓ.property h)) hχ
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
  obtain ⟨D, -, hD⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum (𝕜 := ℂ)
    (fun m : L ↦ (m : E)) hF hc hΓ' hdecay
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

/-- **The localized Fourier transform as a discrete convolution.** Let `L` be a full lattice and
`K ⊆ Ω` a compact set meeting none of its translates by nonzero vectors of `L`, and let `χ` be a
smooth function supported in `K` equal to one on the support of `φ`. Then the localized Fourier
transform of `T` with cutoff `φ` is the superposition of translates of the one with cutoff `χ`,

`T (φ e_η) = ∑ m : L^∨, ((covolume L)⁻¹ 𝓕 φ (m)) T (χ e_(η - m))`,

obtained by pairing `T` with the Fourier expansion
`ContDiffMapSupportedIn.hasSum_fourier_smul_modulate` of `φ` in the modulations of `χ`. -/
theorem hasSum_localFourier_ofSupportedIn [MeasurableSpace E] [BorelSpace E] (T : 𝓓'(Ω, ℂ))
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ x ∈ K, ∀ ℓ : L, x + ℓ ∈ K → ℓ = 0) {φ χ : 𝓓_{K}(E, ℂ)}
    (hχ : EqOn χ 1 (support φ)) (η : E) :
    HasSum (fun m : ZLattice.dual L ↦ ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φ : E → ℂ) m) •
      T.localFourier (ofSupportedIn hKΩ χ) (η - m)) (T.localFourier (ofSupportedIn hKΩ φ) η) := by
  let Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ := T.complexPairing ∘L ofSupportedInCLM ℂ hKΩ ∘L
    ContDiffMapSupportedIn.modulateCLM (-η)
  have h1 : Λ φ = T.localFourier (ofSupportedIn hKΩ φ) η := by
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM,
      ContDiffMapSupportedIn.modulateCLM_apply]
    exact (localFourier_eq_complexPairing_modulate T hKΩ (fun _ ↦ rfl) η).symm
  have h2 (m : ZLattice.dual L) (a : ℂ) :
      Λ (a • χ.modulate m) = a • T.localFourier (ofSupportedIn hKΩ χ) (η - m) := by
    simp only [Λ, ContinuousLinearMap.comp_apply, coe_ofSupportedInCLM, map_smul,
      ContDiffMapSupportedIn.modulateCLM_apply, ContDiffMapSupportedIn.modulate_modulate]
    rw [localFourier_eq_complexPairing_modulate T hKΩ (f := χ) (fun _ ↦ rfl), neg_sub,
      sub_eq_add_neg]
  have hsum := (ContDiffMapSupportedIn.hasSum_fourier_smul_modulate L φ χ hL hχ).map Λ
    Λ.continuous
  rw [h1] at hsum
  simpa only [Function.comp_def, h2] using hsum

/-- Around every point of `Ω` there are a compact set `K ⊆ U ∩ Ω` for a given neighbourhood `U`, a
smaller neighbourhood `K₁` of the point, a smooth function supported in `K` equal to one on `K₁`,
and a full lattice none of whose nonzero translates of `K` meet `K`: the data of a Fourier expansion
of the cutoffs supported in `K₁`. -/
private theorem exists_compacts_cutoff_lattice {x : E} (hx : x ∈ Ω) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ (K : Compacts E) (K₁ : Set E), (K : Set E) ⊆ U ∩ Ω ∧ K₁ ∈ 𝓝 x ∧ K₁ ⊆ K ∧
      (∃ χ : 𝓓_{K}(E, ℂ), ∀ y ∈ K₁, χ y = 1) ∧ ∃ (L : Submodule ℤ E) (_ : DiscreteTopology L)
        (_ : IsZLattice ℝ L), ∀ y ∈ K, ∀ ℓ : L, y + ℓ ∈ K → ℓ = 0 := by
  obtain ⟨K₂, hK₂x, hK₂U, hK₂⟩ := local_compact_nhds (inter_mem hU (Ω.isOpen.mem_nhds hx))
  obtain ⟨K₁, hK₁x, hK₁K₂, hK₁⟩ := local_compact_nhds (interior_mem_nhds.2 hK₂x)
  obtain ⟨χ₀, hχ₀, -, hχ₀1, -, hχ₀s⟩ := hK₁.exists_contDiff_cutoff isOpen_interior hK₁K₂
  obtain ⟨L, hLd, hLz, hL⟩ := ZLattice.exists_forall_add_mem_eq_zero_of_isBounded hK₂.isBounded
  refine ⟨⟨K₂, hK₂⟩, K₁, hK₂U, hK₁x, hK₁K₂.trans interior_subset,
    ⟨ContDiffMapSupportedIn.of_support_subset (ofRealCLM.contDiff.comp hχ₀)
      fun y hy ↦ interior_subset (hχ₀s (subset_tsupport _ (by simpa using hy))), fun y hy ↦ ?_⟩,
    L, hLd, hLz, fun y hy ℓ h ↦ Subtype.ext (hL y hy ℓ ℓ.property h)⟩
  have h1 : χ₀ y = 1 := interior_subset (hχ₀1 hy)
  exact (ContDiffMapSupportedIn.coe_of_support_subset _ _ y).trans (by simp [h1])

/-- **Uniform independence of the cutoff.** If `T` is microlocally smooth at `(x, ξ)`, then there
are a neighbourhood `U` of `x` and an open cone `Γ` containing `ξ` on which the decay of every order
`N` holds uniformly over the cutoffs supported in `U` with bounded derivatives: for some `r` and
`C`, every test function `φ` supported in `U` whose derivatives of order at most `r` are bounded by
`B` satisfies `(1 + ‖η‖) ^ N ‖T (φ e_η)‖ ≤ C B` for `η ∈ Γ`. This is the form in which the decay
applies to cutoffs that depend on the frequency `η` itself. -/
theorem IsMicrolocallySmoothAt.exists_nhds_cone_forall_one_add_norm_pow_mul_norm_localFourier_le
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (h : T.IsMicrolocallySmoothAt x ξ) :
    ∃ U ∈ 𝓝 x, ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ N : ℕ, ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → ∀ B : ℝ,
        (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) →
          ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C * B := by
  borelize E
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 h
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U₀, hU₀, Γ₀, hΓ₀, hξ₀, hcone₀, hdecay₀⟩ := h.exists_nhds_cone
  obtain ⟨Γ, hΓ, hξ, hcone, c, hc, hΓΓ₀⟩ := hΓ₀.exists_cone_closedBall_subset hcone₀ hξ₀
  obtain ⟨K, K₁, hKU, hK₁x, hK₁K, ⟨χ, hχ1⟩, L, _, _, hL⟩ := exists_compacts_cutoff_lattice hx hU₀
  have hKΩ : (K : Set E) ⊆ Ω := hKU.trans inter_subset_right
  -- The localized Fourier transform of `T` with the fixed cutoff `χ` decays on `Γ₀`.
  let χT : 𝓓(Ω, ℂ) := ofSupportedIn hKΩ χ
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T χT
  refine ⟨K₁, hK₁x, Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  obtain ⟨D, hD0, hD⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum (𝕜 := ℂ)
    (fun m : ZLattice.dual L ↦ (m : E)) hF hc hΓΓ₀
    (hdecay₀ χT (χ.tsupport_subset.trans (hKU.trans inter_subset_left)) N)
  obtain ⟨r, C₁, hC₁0, hC₁⟩ :=
    ContDiffMapSupportedIn.exists_tsum_one_add_norm_pow_mul_norm_fourier_le (K := K)
      (ZLattice.dual L) (N + 2 * k)
  refine ⟨r, D * (‖(ZLattice.covolume L : ℂ)⁻¹‖ * C₁), by positivity, fun φ hφ B hB η hη ↦ ?_⟩
  -- Expand `φ` in the modulations of `χ`; the coefficients decay uniformly in `φ`.
  let φK : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset φ.contDiff
    ((subset_tsupport _).trans (hφ.trans hK₁K))
  have hsum := hasSum_localFourier_ofSupportedIn T hKΩ L hL (φ := φK) (χ := χ)
    (fun y hy ↦ hχ1 y (hφ (subset_tsupport _ (by simpa [φK] using hy)))) η
  have hS : ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K r φK ≤ B :=
    ContDiffMapSupportedIn.supSeminorm_le_of_forall_norm_iteratedFDeriv_le
      ((norm_nonneg _).trans (hB 0 (Nat.zero_le _) x)) hB
  have hsumm := (ContDiffMapSupportedIn.summable_one_add_norm_pow_mul_norm_fourier
    (ZLattice.dual L) φK (N + 2 * k)).mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖
  refine (hD _ (hsumm.congr fun m ↦ by rw [norm_mul]; ring) η hη _ hsum).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hD0
  calc ∑' m : ZLattice.dual L, (1 + ‖(m : E)‖) ^ (N + 2 * k) *
        ‖(ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (φK : E → ℂ) m‖
      = ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ∑' m : ZLattice.dual L,
          (1 + ‖(m : E)‖) ^ (N + 2 * k) * ‖𝓕 (φK : E → ℂ) m‖ := by
        rw [← tsum_mul_left]
        congr 1 with m
        rw [norm_mul]
        ring
    _ ≤ ‖(ZLattice.covolume L : ℂ)⁻¹‖ * (C₁ * B) := by
        gcongr
        exact (hC₁ φK).trans (by gcongr)
    _ = ‖(ZLattice.covolume L : ℂ)⁻¹‖ * C₁ * B := by ring

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
  choose U hU Γ hΓ hξΓ hcone hdecay using fun x : K ↦ (h x x.property).exists_nhds_cone
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
      exact ⟨C, fun η hη ↦ hC η (mem_iInter₂.1 hη x x.property)⟩
  choose C hC using hpiece
  refine ⟨∑ i, C i, fun η hη ↦ ?_⟩
  rw [← hsum, localFourier_sum_cutoff]
  calc (1 + ‖η‖) ^ N * ‖∑ i, T.localFourier (ψs i) η‖
      ≤ ∑ i, (1 + ‖η‖) ^ N * ‖T.localFourier (ψs i) η‖ := by
        rw [← Finset.mul_sum]
        gcongr
        exact norm_sum_le _ _
    _ ≤ ∑ i, C i := Finset.sum_le_sum fun i _ ↦ hC i η hη

/-- **Rapid decay on a closed cone.** If `V` is a closed cone of frequencies such that no point of
the wave front set of `T` lies over the support of `φ` in a direction of `V`, then the localized
Fourier transform `η ↦ T (φ e_η)` decreases rapidly on all of `V`: for every `N` there is a
constant `C` with `(1 + ‖η‖)^N ‖T (φ e_η)‖ ≤ C` for `η ∈ V`. -/
theorem exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint {T : 𝓓'(Ω, ℂ)}
    {φ : 𝓓(Ω, ℂ)} {V : Set E} (hV : IsClosed V) (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ V, t • η ∈ V)
    (h : Disjoint (tsupport φ ×ˢ V) T.waveFrontSet) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ η ∈ V, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C := by
  -- Around each direction of `V` of norm one there is an open cone of rapid decay; for the other
  -- unit vectors take the empty cone.
  have hdir (ξ : sphere (0 : E) 1) : ∃ Γ : Set E, IsOpen Γ ∧ ((ξ : E) ∈ V → (ξ : E) ∈ Γ) ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C := by
    by_cases hξV : (ξ : E) ∈ V
    · obtain ⟨W, -, hKW, Γ, hΓ, hξΓ, hconeΓ, hdecay⟩ :=
        exists_isOpen_cone_forall_decay_of_isCompact φ.hasCompactSupport.isCompact
          (ξ := (ξ : E)) fun x hx ↦ by
            by_contra hns
            exact h.ne_of_mem (mk_mem_prod hx hξV) (mem_waveFrontSet_iff.2
              ⟨φ.tsupport_subset hx, ne_zero_of_mem_unit_sphere ξ, hns⟩) rfl
      exact ⟨Γ, hΓ, fun _ ↦ hξΓ, hconeΓ, hdecay φ (hKW.trans subset_union_left) N⟩
    · exact ⟨∅, isOpen_empty, fun h ↦ (hξV h).elim, by simp, 0, by simp⟩
  choose Γ hΓ hξΓ hconeΓ C hC using hdir
  -- Finitely many of these cones cover the nonzero vectors of `V`.
  obtain ⟨t, ht⟩ := TauCeti.exists_finset_diff_singleton_subset_biUnion hV hcone hΓ hξΓ hconeΓ
  exact TauCeti.exists_forall_le_of_diff_singleton_subset_biUnion ht fun ξ _ ↦ hC ξ

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
