/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The wave front set of a pushforward along a linear map

Let `A : E →L[ℝ] E'` be a linear map between finite-dimensional real inner product spaces, `T` a
complex distribution on an open set `Ω ⊆ E` and `χ` a test function on `Ω`. The pushforward of
`T` with cutoff `χ` is the distribution `A_* T : φ ↦ T (χ (φ ∘ A))` on an open set `Ω' ⊆ E'`
(`Distribution.cutoffPushforwardCLM`); it is the pushforward of `T` when `χ = 1` near the support
of `T`. Since `𝐞 (-⟪A x, η⟫) = 𝐞 (-⟪x, Aᵀ η⟫)`, its localized Fourier transform at `η` is a
localized Fourier transform of `T` at `Aᵀ η`. This gives the wave front set bound

`WF(A_* T) ⊆ {(A x, η) | x ∈ supp χ ∩ supp T, (x, Aᵀ η) ∈ WF(T) or Aᵀ η = 0}`.

The covectors with `Aᵀ η = 0` are those conormal to the image of `A`; they cannot be omitted:
pushing forward along a constant map produces a point mass, whose wave front set contains every
nonzero covector at the point, even when `T` is a smooth function
(`Distribution.waveFrontSet_cutoffPushforwardCLM_const`).

## Main results

* `Distribution.localFourier_cutoffPushforwardCLM`: the localized Fourier transform of `A_* T`
  with cutoff `φ` at `η` is that of `T` with cutoff `χ (φ ∘ A)` at `Aᵀ η`.
* `Distribution.isMicrolocallySmoothAt_cutoffPushforwardCLM`: `A_* T` is microlocally smooth at
  `(y, η)` if `Aᵀ η ≠ 0` and `T` is microlocally smooth at `(x, Aᵀ η)` for every `x` in
  `supp χ ∩ supp T` with `A x = y`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front set bound above.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_const`: along a constant map `x ↦ c`, the
  pushforward is a multiple of the point mass at `c` with wave front set `{c} × (E' \ {0})`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (wave front sets under pushforward and other operations).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, arXiv:1409.7662v2, for the pushforward bound with its
  zero-covector term.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace InnerProduct

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'} {χ : 𝓓(Ω, ℝ)} {A : E →L[ℝ] E'}
  {hA : ContDiffOn ℝ (⊤ : ℕ∞) A Ω}

/-- **Localized Fourier transforms of a pushforward along a linear map.** The localized Fourier
transform of `A_* T` with cutoff `φ` at the frequency `η` is that of `T` with the pulled-back
cutoff `χ (φ ∘ A)` at the frequency `Aᵀ η`. -/
theorem localFourier_cutoffPushforwardCLM (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω', ℂ)) (η : E') :
    (cutoffPushforwardCLM χ A hA Ω' T).localFourier φ η =
      T.localFourier (cutoffCompCLM χ A hA φ) ((A†) η) := by
  rw [localFourier_def, complexPairing_cutoffPushforwardCLM]
  refine (localFourier_eq _ _ fun x ↦ ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    ContinuousLinearMap.adjoint_inner_right, mul_assoc]

omit [FiniteDimensional ℝ E] in
/-- A cutoff at `y ∈ Ω'` whose pullback with cutoff `χ` has support meeting `supp T` only inside a
given open set `W`, provided `W` contains every point of `supp χ ∩ supp T` lying over `y`. -/
private theorem exists_cutoffCompCLM_inter_dsupport_subset {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} (T : 𝓓'(Ω, ℂ)) {y : E'} (hy : y ∈ Ω') {W : Set E}
    (hW : IsOpen W) (hKW : ∀ x ∈ tsupport χ ∩ dsupport T, Φ x = y → x ∈ W) :
    ∃ φ : 𝓓(Ω', ℂ), φ y ≠ 0 ∧ tsupport (cutoffCompCLM χ Φ hΦ φ) ∩ dsupport T ⊆ W := by
  -- The points of `supp χ ∩ supp T` outside `W` have compact image, which misses `y`.
  have hbad : IsCompact (Φ '' ((tsupport χ ∩ dsupport T) \ W)) :=
    ((χ.hasCompactSupport.isCompact.inter_right isClosed_dsupport).diff hW).image_of_continuousOn
      (hΦ.continuousOn.mono (sdiff_subset.trans (inter_subset_left.trans χ.tsupport_subset)))
  have hyb : y ∉ Φ '' ((tsupport χ ∩ dsupport T) \ W) := by
    rintro ⟨x, ⟨hxK, hxW⟩, hxy⟩
    exact hxW (hKW x hxK hxy)
  obtain ⟨φ, hφ, hφy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hbad.isClosed.isOpen_compl.mem_nhds hyb) (Ω'.isOpen.mem_nhds hy))
    inter_subset_right (1 : ℂ)
  refine ⟨φ, by simp [hφy], fun x ⟨hx, hxT⟩ ↦ by_contra fun hxW ↦ ?_⟩
  obtain ⟨hxχ, hxφ⟩ := tsupport_cutoffCompCLM_subset φ hx
  exact (hφ hxφ).1 ⟨x, ⟨⟨hxχ, hxT⟩, hxW⟩, rfl⟩

/-- **Microlocal smoothness of a pushforward along a linear map.** Let `y ∈ Ω'`. If `Aᵀ η ≠ 0`
and `T` is microlocally smooth at `(x, Aᵀ η)` for every `x` in `supp χ ∩ supp T` with `A x = y`,
then `A_* T` is microlocally smooth at `(y, η)`. When no such `x` exists, `A_* T` vanishes near
`y` and the condition on `Aᵀ η` is vacuous. -/
theorem isMicrolocallySmoothAt_cutoffPushforwardCLM {T : 𝓓'(Ω, ℂ)} {y η : E'} (hy : y ∈ Ω')
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, A x = y →
      (A†) η ≠ 0 ∧ T.IsMicrolocallySmoothAt x ((A†) η)) :
    (cutoffPushforwardCLM χ A hA Ω' T).IsMicrolocallySmoothAt y η := by
  by_cases hξ : (A†) η = 0
  · -- No point of `supp χ ∩ supp T` lies over `y`, so a cutoff at `y` kills `A_* T`.
    obtain ⟨φ, hφy, hφ⟩ := exists_cutoffCompCLM_inter_dsupport_subset T hy isOpen_empty
      fun x hx hxy ↦ ((h x hx hxy).1 hξ).elim
    refine isMicrolocallySmoothAt_of_forall_decay hφy (fun N ↦ ⟨0, fun η' ↦ ?_⟩) η
    rw [localFourier_cutoffPushforwardCLM,
      localFourier_eq_zero_of_disjoint (disjoint_iff_inter_eq_empty.2 (subset_empty_iff.1 hφ))]
    simp
  -- Otherwise `T` has rapidly decreasing localized Fourier transforms near `Aᵀ η`.
  have hW : IsOpen {x | T.IsMicrolocallySmoothAt x ((A†) η)} :=
    (isOpen_setOf_isMicrolocallySmoothAt T).preimage (continuous_id.prodMk continuous_const)
  obtain ⟨φ, hφy, hφ⟩ := exists_cutoffCompCLM_inter_dsupport_subset T hy hW
    fun x hx hxy ↦ (h x hx hxy).2
  obtain ⟨Γ, hΓ, hξΓ, hcone, hdecay⟩ :=
    exists_cone_decay_of_forall_isMicrolocallySmoothAt fun x hx ↦ hφ hx
  -- On the cone `{η' | Aᵀ η' ∈ Γ, c ‖η'‖ < ‖Aᵀ η'‖}`, decay in `Aᵀ η'` is decay in `η'`.
  have hη : 0 < ‖η‖ := norm_pos_iff.2 fun h0 ↦ hξ (by simp [h0])
  have hξ' : 0 < ‖(A†) η‖ := norm_pos_iff.2 hξ
  set c := ‖(A†) η‖ / (2 * ‖η‖) with hc_def
  have hc : 0 < c := by positivity
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, hφy, (A†) ⁻¹' Γ ∩ {η' | c * ‖η'‖ < ‖(A†) η'‖},
    (hΓ.preimage (A†).continuous).inter (isOpen_lt (by fun_prop) (by fun_prop)), ⟨hξΓ, ?_⟩,
    fun t ht η' ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun N ↦ ?_⟩
  · have hcη : c * ‖η‖ = ‖(A†) η‖ / 2 := by
      rw [hc_def]
      field_simp
    rw [mem_ofPred_eq]
    linarith
  · simpa [map_smul] using hcone t ht _ h1
  · rw [mem_ofPred_eq] at h2 ⊢
    rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm]
    exact mul_lt_mul_of_pos_left h2 ht
  obtain ⟨C, hC⟩ := hdecay N
  refine ⟨(1 + c⁻¹) ^ N * C, fun η' ⟨h1, h2⟩ ↦ ?_⟩
  rw [mem_ofPred_eq] at h2
  have hle : 1 + ‖η'‖ ≤ (1 + c⁻¹) * (1 + ‖(A†) η'‖) := by
    have h3 : ‖η'‖ ≤ c⁻¹ * ‖(A†) η'‖ := by
      rw [le_inv_mul_iff₀ hc]
      exact h2.le
    nlinarith [norm_nonneg ((A†) η'), inv_pos.2 hc]
  rw [localFourier_cutoffPushforwardCLM]
  calc (1 + ‖η'‖) ^ N * ‖T.localFourier (cutoffCompCLM χ A hA φ) ((A†) η')‖
      ≤ ((1 + c⁻¹) * (1 + ‖(A†) η'‖)) ^ N *
          ‖T.localFourier (cutoffCompCLM χ A hA φ) ((A†) η')‖ := by
        gcongr
    _ = (1 + c⁻¹) ^ N *
          ((1 + ‖(A†) η'‖) ^ N * ‖T.localFourier (cutoffCompCLM χ A hA φ) ((A†) η')‖) := by
        rw [mul_pow, mul_assoc]
    _ ≤ (1 + c⁻¹) ^ N * C := by
        gcongr
        exact hC _ h1

/-- **The wave front set of a pushforward along a linear map.** A
covector `(y, η)` in the wave front set of `A_* T` lies over a point `x` of `supp χ ∩ supp T`
with `A x = y`, at which either `(x, Aᵀ η)` lies in the wave front set of `T` or `Aᵀ η = 0`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ A hA Ω' T).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, A x = p.1 ∧
        ((x, (A†) p.2) ∈ T.waveFrontSet ∨ (A†) p.2 = 0)} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨hy, -, hns⟩ := mem_waveFrontSet_iff.1 hp
  by_contra hcon
  refine hns (isMicrolocallySmoothAt_cutoffPushforwardCLM hy fun x hx hxy ↦ ?_)
  simp only [mem_ofPred_eq, not_exists, not_and, not_or] at hcon
  obtain ⟨hWF, hξ⟩ := hcon x hx hxy
  exact ⟨hξ, not_not.1 fun hn ↦ hWF (mem_waveFrontSet_iff.2 ⟨χ.tsupport_subset hx.1, hξ, hn⟩)⟩

omit [FiniteDimensional ℝ E] in
/-- **The zero-covector term is attained.** Along a constant map `x ↦ c` with `c ∈ Ω'`, the
pushforward of `T` with `T χ ≠ 0` is a nonzero multiple of the point mass at `c`, so its wave
front set is `{c} × (E' \ {0})` whatever the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_const {c : E'} (hc : c ∈ Ω') {T : 𝓓'(Ω, ℂ)}
    (hT : T χ ≠ 0) :
    (cutoffPushforwardCLM χ (fun _ ↦ c) contDiffOn_const Ω' T).waveFrontSet = {c} ×ˢ {0}ᶜ := by
  have h : cutoffPushforwardCLM χ (fun _ ↦ c) contDiffOn_const Ω' T =
      T χ • mapCLM ofRealCLM (delta c : 𝓓'(Ω', ℝ)) := by
    ext φ
    rw [cutoffPushforwardCLM_const_apply]
    simp [mul_comm]
  rw [h, waveFrontSet_smul hT, waveFrontSet_delta hc]

end Distribution
