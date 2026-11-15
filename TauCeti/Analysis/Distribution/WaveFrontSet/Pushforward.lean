/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization

/-!
# The wave front set of a pushforward along a linear map

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`, let `χ` be a test function on `Ω` and let `A : E →L[ℝ] E'` be a linear map to another
such space. The pushforward `A_* (χ T)` (`Distribution.cutoffPushforwardCLM`) pairs a test function
`ψ` with `T` through `χ • (ψ ∘ A)`; when `χ = 1` near the support of `T` it is the pushforward
`A_* T` of the compactly supported distribution `T`. This file proves (Hörmander I,
Theorem 8.2.13, here for linear maps)

`WF(A_* (χ T)) ⊆ {(A x, η) | x ∈ supp χ ∩ supp T, Aᵀ η = 0 ∨ (x, Aᵀ η) ∈ WF(T)}`,

where `Aᵀ = A†` is the transpose of `A` for the inner products. Linear maps include the
projections `E × D → E`, along which pushforward is integration over the fibres, and the zero
map.

The term with `Aᵀ η = 0` cannot be omitted: it records the directions `η` normal to the range of
`A`, in which the pushforward can be singular even when `T` is smooth. Along the zero map, or any
constant map `x ↦ y₀`, the pushforward is the point mass `T χ • δ_{y₀}`
(`Distribution.cutoffPushforwardCLM_const`), whose wave front set is `{y₀} × (E' \ {0})` as soon
as `T χ ≠ 0` (`Distribution.waveFrontSet_cutoffPushforwardCLM_const`).

Frequencies are transported by the transpose. Since `⟪A x, ζ⟫ = ⟪x, Aᵀ ζ⟫`, the localized Fourier
transform of `A_* (χ T)` with cutoff `ψ` at `ζ` is that of `T` with cutoff `χ • (ψ ∘ A)` at
`Aᵀ ζ` (`Distribution.localFourier_cutoffPushforwardCLM`). If `T` is microlocally smooth at
`(x, Aᵀ η)` for every `x` in the compact fibre `supp χ ∩ supp T ∩ A⁻¹ {y}`, there are one
neighbourhood of the fibre and one open cone around `Aᵀ η` on which every cutoff supported there
decays rapidly (`Distribution.exists_nhdsSet_cone_of_forall_isMicrolocallySmoothAt`), and cutoffs
`ψ` supported close enough to `y` give such cutoffs `χ • (ψ ∘ A)`. On the open cone of the `ζ`
with `Aᵀ ζ` in that cone and `c ‖ζ‖ < ‖Aᵀ ζ‖`, which contains `η` for small `c > 0` when
`Aᵀ η ≠ 0`, rapid decay in `Aᵀ ζ` is rapid decay in `ζ`.

## Main results

* `Distribution.localFourier_cutoffPushforwardCLM`: the localized Fourier transform of a
  pushforward along a linear map.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front set bound for the
  pushforward along a linear map.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_const`: the pushforward along a constant map is
  singular at its value in every direction.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2, Theorem 8.2.13 (the wave front set of the pushforward of a distribution
  with compact support).
-/

public section

noncomputable section

open Filter Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace InnerProduct

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'}
  {χ : 𝓓(Ω, ℝ)}

section Transpose

variable [CompleteSpace E] [CompleteSpace E'] {A : E →L[ℝ] E'}
  {hA : ContDiffOn ℝ (⊤ : ℕ∞) A Ω}

/-- **The localized Fourier transform of a pushforward along a linear map** `A`: with cutoff `ψ`
at the frequency `ζ`, it is the localized Fourier transform of `T` with cutoff `χ • (ψ ∘ A)` at the
transposed frequency `(A†) ζ`. -/
theorem localFourier_cutoffPushforwardCLM (T : 𝓓'(Ω, ℂ)) (ψ : 𝓓(Ω', ℂ)) (ζ : E') :
    (cutoffPushforwardCLM χ A hA T).localFourier ψ ζ =
      T.localFourier (cutoffCompCLM χ A hA ψ) ((A†) ζ) := by
  rw [localFourier_def, complexPairing_cutoffPushforwardCLM]
  refine (localFourier_eq T _ fun x ↦ ?_).symm
  simp [bilinLeftCLM_apply, ContinuousLinearMap.adjoint_inner_right, mul_assoc,
    TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]

end Transpose

/-- **The pushforward along a constant map** `x ↦ y₀` of a distribution with `T χ ≠ 0` has wave
front set `{y₀} × (E' \ {0})`, even when `T` is smooth. For `y₀ = 0` this is the zero linear map,
whose transpose vanishes, so the bound of `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`
is attained and its term with `A† η = 0` cannot be omitted. -/
theorem waveFrontSet_cutoffPushforwardCLM_const [FiniteDimensional ℝ E'] {y₀ : E'} (hy₀ : y₀ ∈ Ω')
    {hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : E ↦ y₀) Ω} {T : 𝓓'(Ω, ℂ)} (hT : T χ ≠ 0) :
    (cutoffPushforwardCLM (Ω' := Ω') χ (fun _ ↦ y₀) hc T).waveFrontSet = {y₀} ×ˢ {0}ᶜ := by
  rw [cutoffPushforwardCLM_const, waveFrontSet_smul hT, waveFrontSet_delta hy₀]

/-- Rapid decay on an open cone `Γ` around `B η ≠ 0` pulls back along the linear map `B` to rapid
decay on an open cone around `η`: on the `ζ` with `B ζ ∈ Γ` and `c ‖ζ‖ < ‖B ζ‖`, powers of
`1 + ‖ζ‖` are controlled by powers of `1 + ‖B ζ‖`. -/
private theorem exists_cone_forall_decay_comp {B : E' →L[ℝ] E} {η : E'} (hBη : B η ≠ 0)
    {Γ : Set E} (hΓ : IsOpen Γ) (hηΓ : B η ∈ Γ) (hcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ, t • ξ ∈ Γ) :
    ∃ Γ' : Set E', IsOpen Γ' ∧ η ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ', t • ζ ∈ Γ') ∧
      ∀ f : E → ℂ, (∀ N : ℕ, ∃ C, ∀ ξ ∈ Γ, (1 + ‖ξ‖) ^ N * ‖f ξ‖ ≤ C) →
        ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ', (1 + ‖ζ‖) ^ N * ‖f (B ζ)‖ ≤ C := by
  have hη : η ≠ 0 := fun h ↦ hBη (by simp [h])
  set c := ‖B η‖ / (2 * ‖η‖) with hc_def
  have hc : 0 < c := div_pos (norm_pos_iff.2 hBη) (by positivity)
  refine ⟨{ζ | B ζ ∈ Γ ∧ c * ‖ζ‖ < ‖B ζ‖}, (hΓ.preimage B.continuous).inter
      (isOpen_lt (continuous_const.mul continuous_norm) B.continuous.norm),
    ⟨hηΓ, ?_⟩, fun t ht ζ hζ ↦ ⟨?_, ?_⟩, fun f hf N ↦ ?_⟩
  · rw [hc_def, div_mul_eq_mul_div, mul_comm (2 : ℝ), ← div_div, mul_div_assoc,
      div_self (norm_ne_zero_iff.2 hη), mul_one]
    exact half_lt_self (norm_pos_iff.2 hBη)
  · simpa only [map_smul] using hcone t ht _ hζ.1
  · rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm]
    exact mul_lt_mul_of_pos_left hζ.2 ht
  obtain ⟨C, hC⟩ := hf N
  refine ⟨max 1 c⁻¹ ^ N * C, fun ζ hζ ↦ ?_⟩
  have hζB : 1 + ‖ζ‖ ≤ max 1 c⁻¹ * (1 + ‖B ζ‖) := by
    have h1 : ‖ζ‖ ≤ c⁻¹ * ‖B ζ‖ := by
      rw [le_inv_mul_iff₀ hc]
      exact hζ.2.le
    have h2 : c⁻¹ * ‖B ζ‖ ≤ max 1 c⁻¹ * ‖B ζ‖ := by gcongr; exact le_max_right _ _
    nlinarith [le_max_left 1 c⁻¹, norm_nonneg (B ζ)]
  calc (1 + ‖ζ‖) ^ N * ‖f (B ζ)‖ ≤ (max 1 c⁻¹ * (1 + ‖B ζ‖)) ^ N * ‖f (B ζ)‖ := by gcongr
    _ = max 1 c⁻¹ ^ N * ((1 + ‖B ζ‖) ^ N * ‖f (B ζ)‖) := by rw [mul_pow, mul_assoc]
    _ ≤ max 1 c⁻¹ ^ N * C := by gcongr; exact hC _ hζ.1

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {A : E →L[ℝ] E'}
  {hA : ContDiffOn ℝ (⊤ : ℕ∞) A Ω}

/-- **The wave front set of a pushforward along a linear map** (Hörmander I, Theorem 8.2.13). A
covector `(y, η)` in the wave front set of the pushforward `A_* (χ T)` lies over a point `x` of
`supp χ ∩ supp T` with `A x = y`, at which either the transposed covector `(A†) η` vanishes or
`(x, (A†) η)` lies in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM (Ω' := Ω') χ A hA T).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, A x = p.1 ∧
        ((A†) p.2 = 0 ∨ (x, (A†) p.2) ∈ T.waveFrontSet)} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨hy, -, hns⟩ := mem_waveFrontSet_iff.1 hp
  by_contra hcon
  simp only [mem_ofPred_eq, not_exists, not_and, not_or] at hcon
  refine hns ?_
  have hS : IsCompact (tsupport χ ∩ dsupport T) :=
    χ.hasCompactSupport.isCompact.inter_right isClosed_dsupport
  -- The part `K` of `supp χ ∩ supp T` over `y` is compact.
  have hK : IsCompact (tsupport χ ∩ dsupport T ∩ A ⁻¹' {y}) :=
    hS.inter_right (isClosed_singleton.preimage A.continuous)
  rcases (tsupport χ ∩ dsupport T ∩ A ⁻¹' {y}).eq_empty_or_nonempty with hK0 | ⟨x₀, hx₀⟩
  · -- Over `y` there is no support: the pushforward vanishes near `y`.
    refine isMicrolocallySmoothAt_of_notMem_dsupport hy (fun hyT ↦ ?_) η
    obtain ⟨x, hxS, rfl⟩ := dsupport_cutoffPushforwardCLM_subset T hyT
    exact hK0.subset ⟨hxS, rfl⟩
  have hAη : (A†) η ≠ 0 := (hcon x₀ hx₀.1 hx₀.2).1
  have hsmooth (x : E) (hx : x ∈ tsupport χ ∩ dsupport T ∩ A ⁻¹' {y}) :
      T.IsMicrolocallySmoothAt x ((A†) η) := by
    have h := (hcon x hx.1 hx.2).2
    simp only [mem_waveFrontSet_iff, not_and, not_not] at h
    exact h (χ.tsupport_subset hx.1.1) hAη
  obtain ⟨V, hV, Γ, hΓ, hξΓ, hcone, hdecay⟩ :=
    exists_nhdsSet_cone_of_forall_isMicrolocallySmoothAt hK hsmooth
  -- Over a neighbourhood of `y`, the part of `supp χ ∩ supp T` lies in `V`.
  have hW : IsClosed (A '' (tsupport χ ∩ dsupport T ∩ (interior V)ᶜ)) :=
    ((hS.inter_right isOpen_interior.isClosed_compl).image A.continuous).isClosed
  have hyW : y ∉ A '' (tsupport χ ∩ dsupport T ∩ (interior V)ᶜ) := by
    rintro ⟨x, ⟨hxS, hxV⟩, rfl⟩
    exact hxV (subset_interior_iff_mem_nhdsSet.2 hV ⟨hxS, rfl⟩)
  obtain ⟨ψ, hψ, hψy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hW.isOpen_compl.mem_nhds hyW) (Ω'.isOpen.mem_nhds hy)) inter_subset_right (1 : ℂ)
  have hψV : tsupport (cutoffCompCLM χ A hA ψ) ⊆ V ∪ (dsupport T)ᶜ := fun z hz ↦ by
    obtain ⟨hzχ, hzψ⟩ := tsupport_cutoffCompCLM_subset ψ hz
    by_contra hzV
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hzV
    exact (hψ hzψ).1 ⟨z, ⟨⟨hzχ, hzV.2⟩, fun h ↦ hzV.1 (interior_subset h)⟩, rfl⟩
  -- Decay in `(A†) ζ` on `Γ` is decay in `ζ` on a cone around `η`.
  obtain ⟨Γ', hΓ', hηΓ', hcone', hdecay'⟩ := exists_cone_forall_decay_comp hAη hΓ hξΓ hcone
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψy], Γ', hΓ', hηΓ', hcone', fun N ↦ ?_⟩
  simpa only [localFourier_cutoffPushforwardCLM] using hdecay' _ (hdecay _ hψV) N

end Distribution
