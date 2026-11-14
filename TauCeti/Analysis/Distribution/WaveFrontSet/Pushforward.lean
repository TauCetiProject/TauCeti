/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.PositiveDefinite.FourierAtom
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization

/-!
# The wave front set of a pushforward along a linear map

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`, and let `χ` be a test function equal to one near the support of `T`, which is then
compact. For a continuous linear map `A : E →L[ℝ] E'` the pushforward `A_* T` is the distribution
`f ↦ T (χ (f ∘ A))` on an open set `Ω'` of `E'` (`Distribution.cutoffPushforwardCLM`). This file
proves Hörmander's bound for its wave front set:

`WF(A_* T) ⊆ {(A x, η) | x ∈ supp T, Aᵀ η = 0 or (x, Aᵀ η) ∈ WF(T)}`.

Its proof rests on the identity `(A_* T)^(η) = T (χ (f ∘ A) e_(Aᵀ η))` for localized Fourier
transforms (`Distribution.localFourier_cutoffPushforwardCLM`): the characters of `E'` pull back
along `A` to the characters of `E` at the transposed frequency. Over a point `y`, `T` decays rapidly
in one cone around `Aᵀ η` for all cutoffs supported near the compact set `supp T ∩ A⁻¹ {y}`
(`Distribution.exists_isOpen_cone_forall_decay_of_isCompact`), and a cutoff around `y` pulls back
to such a cutoff. Since `Aᵀ η ≠ 0`, the frequencies `η'` near the ray of `η` satisfy
`‖η'‖ ≤ c ‖Aᵀ η'‖`, so decay in `Aᵀ η'` is decay in `η'`.

The covectors with `Aᵀ η = 0` cannot be omitted, even for smooth `T`: along a constant map with
value `c` the pushforward of `T` is the multiple `T χ` of the point mass at `c`, and when `T χ ≠ 0`
its wave front set is `{c} × (E' \ {0})` (`Distribution.waveFrontSet_cutoffPushforwardCLM_const`).
The differential of a constant map has zero transpose; for `c = 0` the constant map is the linear
map `0`, to which the bound above applies through its term `Aᵀ η = 0`. When `A` is surjective,
`Aᵀ` is injective and these covectors do not occur.

## Main results

* `Distribution.localFourier_cutoffPushforwardCLM`: localized Fourier transforms of `A_* T` are
  localized Fourier transforms of `T` at the transposed frequency.
* `Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM`: if `Aᵀ η ≠ 0` and `T` is
  microlocally smooth at `(x, Aᵀ η)` for every `x ∈ supp T` with `A x = y`, then `A_* T` is
  microlocally smooth at `(y, η)`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front bound above.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: for surjective `A`,
  `WF(A_* T) ⊆ {(A x, η) | (x, Aᵀ η) ∈ WF(T)}`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_const`: the pushforward along a constant map
  with value `c` has wave front set `{c} × (E' \ {0})` whenever `T χ ≠ 0`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.13 (the wave front set of a pushforward).
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace InnerProduct

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω' : Opens E'}

section Linear

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

/-- **Localized Fourier transforms of a pushforward.** The localized Fourier transform of the
pushforward `A_* T` along a linear map `A`, with cutoff `f`, at the frequency `η`, is that of `T`
with the cutoff `χ (f ∘ A)` at the transposed frequency `Aᵀ η`. -/
theorem localFourier_cutoffPushforwardCLM (A : E →L[ℝ] E') (T : 𝓓'(Ω, ℂ)) (f : 𝓓(Ω', ℂ))
    (η : E') :
    (cutoffPushforwardCLM χ A A.contDiff.contDiffOn T : 𝓓'(Ω', ℂ)).localFourier f η =
      T.localFourier (cutoffCompCLM χ A A.contDiff.contDiffOn f) ((A†) η) := by
  rw [localFourier_eq _ f (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (TauCeti.contDiff_fourierAtom η) f) fun x => by
      simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply],
    complexPairing_cutoffPushforwardCLM]
  refine (localFourier_eq _ _ fun x => ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    ContinuousLinearMap.adjoint_inner_right, mul_assoc]

/-- **Microlocal smoothness of a pushforward.** Let `χ` be equal to one near the support of `T`,
`y ∈ Ω'` and `Aᵀ η ≠ 0`. If `T` is microlocally smooth at `(x, Aᵀ η)` for every `x` in its support
with `A x = y`, then the pushforward `A_* T` is microlocally smooth at `(y, η)`. -/
theorem IsMicrolocallySmoothAt.cutoffPushforwardCLM {A : E →L[ℝ] E'} {T : 𝓓'(Ω, ℂ)} {y η : E'}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hy : y ∈ Ω') (hη : (A†) η ≠ 0)
    (h : ∀ x ∈ dsupport T, A x = y → T.IsMicrolocallySmoothAt x ((A†) η)) :
    (Distribution.cutoffPushforwardCLM χ A A.contDiff.contDiffOn T :
      𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt y η := by
  set D := dsupport T
  set ξ₀ := (A†) η
  have hD : IsCompact D := (isCompact_dsupport_and_subset_of_eventually_eq_one hχ).1
  -- `T` decays uniformly in a cone `Γ₀ ∋ Aᵀ η` over a neighbourhood `W` of `D ∩ A⁻¹ {y}`.
  obtain ⟨W, hW, hKW, Γ₀, hΓ₀, hξ₀, hcone₀, hdecay₀⟩ :=
    exists_isOpen_cone_forall_decay_of_isCompact
      (hD.inter_right (isClosed_singleton.preimage A.continuous))
      fun x hx => h x hx.1 hx.2
  -- The compact set `A (D \ W)` misses `y`, so a cutoff `f` around `y` pulls back into `W ∪ Dᶜ`.
  have hC : IsCompact (A '' (D \ W)) := (hD.diff hW).image A.continuous
  have hyC : y ∉ A '' (D \ W) := fun ⟨x, ⟨hxD, hxW⟩, hxy⟩ => hxW (hKW ⟨hxD, hxy⟩)
  obtain ⟨f, hf, hfy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hC.isClosed.isOpen_compl.mem_nhds hyC) (Ω'.isOpen.mem_nhds hy))
    inter_subset_right (1 : ℂ)
  set ψ := cutoffCompCLM χ A A.contDiff.contDiffOn f
  have hψ : tsupport ψ ⊆ W ∪ Dᶜ := fun z hz => by
    by_contra hzW
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hzW
    exact (hf (tsupport_cutoffCompCLM_subset f hz).2).1 ⟨z, ⟨hzW.2, hzW.1⟩, rfl⟩
  -- The cone `Γ'` of frequencies `η'` with `Aᵀ η' ∈ Γ₀` and `‖η'‖ ≤ c ‖Aᵀ η'‖` carries the decay.
  have hη0 : 0 < ‖η‖ := norm_pos_iff.2 fun h0 => hη (by simp [ξ₀, h0])
  have hξ0 : 0 < ‖ξ₀‖ := norm_pos_iff.2 hη
  set c := 2 * ‖η‖ / ‖ξ₀‖
  have hc : 0 ≤ c := by positivity
  refine isMicrolocallySmoothAt_iff.2 ⟨f, by simp [hfy],
    (A†) ⁻¹' Γ₀ ∩ {η' | ‖η'‖ * ‖ξ₀‖ < 2 * ‖η‖ * ‖(A†) η'‖},
    (hΓ₀.preimage (A†).continuous).inter (isOpen_lt (by fun_prop) (by fun_prop)),
    ⟨hξ₀, by rw [mem_ofPred_eq]; nlinarith⟩, fun t ht η' ⟨h1, h2⟩ => ⟨?_, ?_⟩,
    fun N => ?_⟩
  · simpa using hcone₀ t ht _ h1
  · simp only [mem_ofPred_eq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h2 ⊢
    nlinarith
  · obtain ⟨C, hC⟩ := hdecay₀ ψ hψ N
    refine ⟨(1 + c) ^ N * C, fun η' ⟨h1, h2⟩ => ?_⟩
    rw [mem_ofPred_eq] at h2
    rw [localFourier_cutoffPushforwardCLM]
    have hle : ‖η'‖ ≤ c * ‖(A†) η'‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hξ0]
      linarith
    have hle' : 1 + ‖η'‖ ≤ (1 + c) * (1 + ‖(A†) η'‖) := by
      nlinarith [norm_nonneg ((A†) η')]
    calc (1 + ‖η'‖) ^ N * ‖T.localFourier ψ ((A†) η')‖
        ≤ ((1 + c) * (1 + ‖(A†) η'‖)) ^ N * ‖T.localFourier ψ ((A†) η')‖ := by gcongr
      _ = (1 + c) ^ N * ((1 + ‖(A†) η'‖) ^ N * ‖T.localFourier ψ ((A†) η')‖) := by
          rw [mul_pow, mul_assoc]
      _ ≤ (1 + c) ^ N * C := by
          gcongr
          exact hC _ h1

/-- **The wave front set of a pushforward** (Hörmander I, Theorem 8.2.13, along a linear map).
If `χ` is equal to one near the support of `T`, every covector `(y, η)` in the wave front set of
the pushforward `A_* T` lies over a point `x` of the support of `T` with `A x = y`, at which either
`Aᵀ η = 0` or `(x, Aᵀ η)` lies in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset (A : E →L[ℝ] E') (T : 𝓓'(Ω, ℂ))
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (cutoffPushforwardCLM χ A A.contDiff.contDiffOn T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ dsupport T, A x = p.1 ∧ ((A†) p.2 = 0 ∨ (x, (A†) p.2) ∈ T.waveFrontSet)} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨⟨x₀, ⟨-, hx₀⟩, hx₀y⟩, -⟩ :=
    prod_mono (dsupport_cutoffPushforwardCLM_subset T) subset_rfl
      (waveFrontSet_subset_dsupport _ hp)
  obtain ⟨hy, -, hS⟩ := mem_waveFrontSet_iff.1 hp
  by_cases hη : (A†) η = 0
  · exact ⟨x₀, hx₀, hx₀y, Or.inl hη⟩
  by_contra hne
  refine hS (IsMicrolocallySmoothAt.cutoffPushforwardCLM hχ hy hη fun x hx hxy => ?_)
  have hxΩ : x ∈ Ω := (isCompact_dsupport_and_subset_of_eventually_eq_one hχ).2 hx
  by_contra hT
  exact hne ⟨x, hx, hxy, Or.inr (mem_waveFrontSet_iff.2 ⟨hxΩ, hη, hT⟩)⟩

/-- **Pushforward along a surjective linear map.** If `A` is surjective, its transpose is
injective, and every covector `(y, η)` in the wave front set of `A_* T` lies over a point `x` of
the support of `T` with `A x = y` and `(x, Aᵀ η)` in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective {A : E →L[ℝ] E'}
    (hA : Surjective A) (T : 𝓓'(Ω, ℂ)) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (cutoffPushforwardCLM χ A A.contDiff.contDiffOn T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ dsupport T, A x = p.1 ∧ (x, (A†) p.2) ∈ T.waveFrontSet} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨x, hx, hxy, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset A T hχ hp
  refine ⟨x, hx, hxy, h.resolve_left fun h0 => (mem_waveFrontSet_iff.1 hp).2.1 ?_⟩
  obtain ⟨z, hz⟩ := hA η
  have h := ContinuousLinearMap.adjoint_inner_left A z η
  rw [h0, inner_zero_left, hz] at h
  exact inner_self_eq_zero.1 h.symm

end Linear

section Const

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

/-- **The zero covectors cannot be omitted.** Pushing `T` forward along the constant map with
value `c ∈ Ω'` gives the multiple `T χ` of the point mass at `c`; if `T χ ≠ 0`, its wave front set
is `{c} × (E' \ {0})`, whatever the wave front set of `T`. The differential of a constant map is
zero, so the transpose of the differential kills every covector. For `c = 0` the constant map is
the linear map `0`, and all these covectors come from the term `Aᵀ η = 0` of
`Distribution.waveFrontSet_cutoffPushforwardCLM_subset`. -/
theorem waveFrontSet_cutoffPushforwardCLM_const (T : 𝓓'(Ω, ℂ)) (hT : T χ ≠ 0) {c : E'}
    (hc : c ∈ Ω') :
    (cutoffPushforwardCLM χ (fun _ => c) contDiffOn_const T : 𝓓'(Ω', ℂ)).waveFrontSet =
      {c} ×ˢ {0}ᶜ := by
  have h : (cutoffPushforwardCLM χ (fun _ => c) contDiffOn_const T : 𝓓'(Ω', ℂ)) =
      T χ • mapCLM ofRealCLM (delta c : 𝓓'(Ω', ℝ)) := by
    ext f
    rw [cutoffPushforwardCLM_const_apply]
    simp [mul_comm]
  rw [h, waveFrontSet_smul hT, waveFrontSet_delta hc]

end Const

end Distribution
