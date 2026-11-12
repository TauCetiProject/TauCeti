/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization

/-!
# The wave front set of a pushforward along a linear map

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`, let `χ` be a test function on `Ω`, and let `A : E →L[ℝ] E'` be a linear map to another
such space. The pushforward `A_* (χ T)` is the distribution `φ ↦ T (χ (φ ∘ A))` on an open set
`Ω' ⊆ E'` (`Distribution.cutoffPushforwardCLM`); when `χ = 1` near the support of `T` it is the
pushforward `A_* T` of the compactly supported distribution `T`, and for a projection it is
integration over the fibres. This file proves the wave front set bound

`WF(A_* (χ T)) ⊆ {(A x, η) : x ∈ supp χ ∩ supp T, (x, Aᵀ η) ∈ WF(T) or Aᵀ η = 0}`,

where `Aᵀ = A†` is the transpose of `A`, computed with the inner products.

The proof rests on the identity of localized Fourier transforms
`(A_* (χ T)) (φ e_η) = T (χ (φ ∘ A) e_{Aᵀ η})` (`Distribution.localFourier_cutoffPushforwardCLM`),
since `⟪A x, η⟫ = ⟪x, Aᵀ η⟫`. If `(y, η)` is not in the right-hand side, either no point of
`supp χ ∩ supp T` lies over `y`, or `Aᵀ η ≠ 0` and `T` is microlocally smooth at `(x, Aᵀ η)` for
every such point `x`. In the second case, rapid decay holds uniformly for cutoffs whose support
meets `supp T` in a neighbourhood `U` of these points
(`Distribution.exists_isOpen_cone_of_forall_isMicrolocallySmoothAt`), and on a cone around `η` on
which `‖η‖ ≤ C ‖Aᵀ η‖` the decay transfers from `Aᵀ η` to `η`. A cutoff `φ` supported close
enough to `y` makes `χ (φ ∘ A)` meet `supp T` only inside `U`.

The term `Aᵀ η = 0` cannot be dropped: along a constant map every frequency is annihilated, and
the pushforward of `χ T` is the point mass `T(χ) δ_{y₀}`, whose wave front set is
`{y₀} × (E' \ {0})` even when `T` is smooth
(`Distribution.waveFrontSet_cutoffPushforwardCLM_const`).
For a surjective `A`, the transpose is injective and this term contributes nothing
(`Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`).

## Main results

* `Distribution.localFourier_cutoffPushforwardCLM`: the localized Fourier transform of a
  pushforward along a linear map.
* `Distribution.isMicrolocallySmoothAt_cutoffPushforwardCLM`: microlocal smoothness of the
  pushforward at `(y, η)` from that of `T` at `(x, Aᵀ η)` for the points `x` over `y`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front set bound above.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: its form for a surjective
  linear map, with no zero-covector term.
* `Distribution.cutoffPushforwardCLM_const`, `Distribution.waveFrontSet_cutoffPushforwardCLM_const`:
  the pushforward along a constant map is a point mass, and its wave front set is the whole fibre.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (operations on distributions and their wave front sets).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2.
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction ContinuousLinearMap
open scoped Distributions Topology InnerProduct RealInnerProductSpace

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'} {χ : 𝓓(Ω, ℝ)}

section Linear

variable {A : E →L[ℝ] E'} {hA : ContDiffOn ℝ (⊤ : ℕ∞) A Ω}

/-- The localized Fourier transform of the pushforward of `χ T` along a linear map `A` at the
frequency `η` is the localized Fourier transform of `T`, with cutoff `χ (φ ∘ A)`, at the transposed
frequency `A† η`. -/
theorem localFourier_cutoffPushforwardCLM (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω', ℂ)) (η : E') :
    (cutoffPushforwardCLM χ A hA T : 𝓓'(Ω', ℂ)).localFourier φ η =
      T.localFourier (cutoffCompCLM χ A hA φ) ((A†) η) := by
  rw [localFourier_def, complexPairing_cutoffPushforwardCLM]
  refine (localFourier_eq T _ fun x ↦ ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    adjoint_inner_right, mul_assoc]

/-- **Microlocal smoothness of a pushforward along a linear map.** Let `y ∈ Ω'`. Suppose that for
every point `x` of `supp χ ∩ supp T` over `y` the transposed frequency `A† η` is nonzero and `T` is
microlocally smooth at `(x, A† η)`. Then the pushforward of `χ T` along `A` is microlocally smooth
at `(y, η)`. When no point lies over `y` the hypothesis is vacuous and the pushforward vanishes
near `y`. -/
theorem isMicrolocallySmoothAt_cutoffPushforwardCLM {T : 𝓓'(Ω, ℂ)} {y η : E'} (hy : y ∈ Ω')
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, A x = y →
      (A†) η ≠ 0 ∧ T.IsMicrolocallySmoothAt x ((A†) η)) :
    (cutoffPushforwardCLM χ A hA T : 𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt y η := by
  set L := tsupport χ ∩ dsupport T
  have hL : IsCompact L := χ.hasCompactSupport.inter_right isClosed_dsupport
  -- Rapid decay at the transposed frequencies, for cutoffs meeting `supp T` inside some `U`
  -- containing the points of `L` over `y`.
  obtain ⟨U, hU, hLU, Γ, hΓ, hηΓ, hcone, hdecay⟩ : ∃ U, IsOpen U ∧ (∀ x ∈ L, A x = y → x ∈ U) ∧
      ∃ Γ : Set E', IsOpen Γ ∧ η ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ) ∧
      ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ∩ dsupport T ⊆ U →
        ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ N * ‖T.localFourier ψ ((A†) ζ)‖ ≤ C := by
    rcases eq_or_ne ((A†) η) 0 with h0 | h0
    · -- No point of `L` lies over `y`, so the cutoffs are supported off `supp T`.
      refine ⟨∅, isOpen_empty, fun x hx hxy ↦ ((h x hx hxy).1 h0).elim, univ, isOpen_univ,
        mem_univ _, fun _ _ _ _ ↦ mem_univ _, fun ψ hψ N ↦ ⟨0, fun ζ _ ↦ ?_⟩⟩
      rw [localFourier_eq_zero_of_disjoint (disjoint_iff_inter_eq_empty.2 (subset_empty_iff.1 hψ))]
      simp
    obtain ⟨U, hU, hKU, Γ, hΓ, hξΓ, hcone, hdecay⟩ :=
      exists_isOpen_cone_of_forall_isMicrolocallySmoothAt
        (hL.inter_right (isClosed_singleton.preimage A.continuous))
        fun x hx ↦ (h x hx.1 hx.2).2
    -- On the cone `c ‖ζ‖ < 2 ‖A† ζ‖` around `η`, the weight `1 + ‖ζ‖` is controlled by
    -- `1 + ‖A† ζ‖`.
    have hη : η ≠ 0 := fun h ↦ h0 (by simp [h])
    set c := ‖(A†) η‖ / ‖η‖
    have hc : 0 < c := div_pos (norm_pos_iff.2 h0) (norm_pos_iff.2 hη)
    refine ⟨U, hU, fun x hx hxy ↦ hKU ⟨hx, hxy⟩, ((A†) ⁻¹' Γ) ∩ {ζ | c * ‖ζ‖ < 2 * ‖(A†) ζ‖},
      (hΓ.preimage (A†).continuous).inter (isOpen_lt (by fun_prop) (by fun_prop)),
      ⟨hξΓ, ?_⟩, fun t ht ζ hζ ↦ ⟨?_, ?_⟩, fun ψ hψ N ↦ ?_⟩
    · have : c * ‖η‖ = ‖(A†) η‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.2 hη)
      simp only [mem_ofPred_eq, this]
      linarith [norm_pos_iff.2 h0]
    · simpa [map_smul] using hcone t ht _ hζ.1
    · have := hζ.2
      simp only [mem_ofPred_eq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at this ⊢
      nlinarith
    obtain ⟨C, hC⟩ := hdecay ψ hψ N
    set M := max 1 (2 / c)
    refine ⟨M ^ N * C, fun ζ hζ ↦ ?_⟩
    have hM : 1 + ‖ζ‖ ≤ M * (1 + ‖(A†) ζ‖) := by
      have h2 : c * ‖ζ‖ ≤ c * (2 / c * ‖(A†) ζ‖) := by
        rw [← mul_assoc, mul_div_cancel₀ _ hc.ne']
        exact (hζ.2 : c * ‖ζ‖ < 2 * ‖(A†) ζ‖).le
      nlinarith [le_of_mul_le_mul_left h2 hc, le_max_left 1 (2 / c), le_max_right 1 (2 / c),
        norm_nonneg ((A†) ζ)]
    calc (1 + ‖ζ‖) ^ N * ‖T.localFourier ψ ((A†) ζ)‖
        ≤ (M * (1 + ‖(A†) ζ‖)) ^ N * ‖T.localFourier ψ ((A†) ζ)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hM N) (norm_nonneg _)
      _ = M ^ N * ((1 + ‖(A†) ζ‖) ^ N * ‖T.localFourier ψ ((A†) ζ)‖) := by
          rw [mul_pow, mul_assoc]
      _ ≤ M ^ N * C := by gcongr; exact hC _ hζ.1
  -- A cutoff near `y` avoiding the image of the points of `L` outside `U`.
  have hLU' : IsCompact (A '' (L \ U)) := (hL.diff hU).image A.continuous
  have hyLU : y ∉ A '' (L \ U) := by
    rintro ⟨x, hx, rfl⟩
    exact hx.2 (hLU x hx.1 rfl)
  obtain ⟨φ, hφ, hφy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hLU'.isClosed.isOpen_compl.mem_nhds hyLU) (Ω'.isOpen.mem_nhds hy))
    inter_subset_right (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφy], Γ, hΓ, hηΓ, hcone, fun N ↦ ?_⟩
  -- The composed cutoff meets `supp T` only inside `U`.
  have hψ : tsupport (cutoffCompCLM χ A hA φ) ∩ dsupport T ⊆ U := by
    rintro x ⟨hx, hxT⟩
    obtain ⟨hxχ, hxφ⟩ := tsupport_cutoffCompCLM_subset φ hx
    by_contra hxU
    exact (hφ hxφ).1 ⟨x, ⟨⟨hxχ, hxT⟩, hxU⟩, rfl⟩
  obtain ⟨C, hC⟩ := hdecay _ hψ N
  exact ⟨C, fun ζ hζ ↦ by simpa [localFourier_cutoffPushforwardCLM] using hC ζ hζ⟩

/-- **The wave front set of a pushforward along a linear map**: a point `(y, η)` of the wave front
set of the pushforward of `χ T` along `A` lies over a point `x` of `supp χ ∩ supp T` with
`A x = y`, at which either `(x, A† η)` is in the wave front set of `T` or `A† η = 0`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ A hA T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, A x = p.1 ∧
        ((x, (A†) p.2) ∈ T.waveFrontSet ∨ (A†) p.2 = 0)} := by
  rintro ⟨y, η⟩ hyη
  obtain ⟨hy, -, hS⟩ := mem_waveFrontSet_iff.1 hyη
  by_contra hp
  simp only [mem_ofPred_eq, not_exists, not_and, not_or] at hp
  refine hS (isMicrolocallySmoothAt_cutoffPushforwardCLM hy fun x hx hxy ↦ ?_)
  obtain ⟨hWF, h0⟩ := hp x hx hxy
  exact ⟨h0, by_contra fun hns ↦ hWF (mem_waveFrontSet_iff.2 ⟨χ.tsupport_subset hx.1, h0, hns⟩)⟩

/-- **The wave front set of a pushforward along a surjective linear map**: the transpose is then
injective, so every point `(y, η)` of the wave front set of the pushforward of `χ T` comes from a
point `(x, A† η)` of the wave front set of `T` with `A x = y`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective (hsurj : Surjective A)
    (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ A hA T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, A x = p.1 ∧ (x, (A†) p.2) ∈ T.waveFrontSet} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨x, hx, hxp, hWF | h0⟩ := waveFrontSet_cutoffPushforwardCLM_subset T hp
  · exact ⟨x, hx, hxp, hWF⟩
  -- The kernel of `A†` is the orthogonal complement of the range of `A`, which is everything.
  have hker : η ∈ (A†).ker := by simpa using h0
  rw [← A.orthogonal_range, LinearMap.range_eq_top.2 hsurj, Submodule.top_orthogonal_eq_bot,
    Submodule.mem_bot] at hker
  exact ((mem_waveFrontSet_iff.1 hp).2.1 hker).elim

end Linear

section Const

variable {y₀ : E'} {hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : E ↦ y₀) Ω}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The pushforward of `χ T` along the constant map at `y₀` is the point mass at `y₀` with weight
`T χ`. -/
theorem cutoffPushforwardCLM_const (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ (fun _ : E ↦ y₀) hc T : 𝓓'(Ω', ℂ)) =
      T χ • mapCLM ofRealCLM (delta y₀ : 𝓓'(Ω', ℝ)) := by
  ext φ
  have hφ : cutoffCompCLM χ (fun _ : E ↦ y₀) hc φ = φ y₀ • χ := by
    ext x
    simp [mul_comm]
  simp [hφ, mul_comm]

omit [FiniteDimensional ℝ E] in
/-- **The zero-covector term is attained.** Along the constant map at `y₀ ∈ Ω'`, every frequency
is annihilated by the transpose, and if `T χ ≠ 0` the pushforward of `χ T` has the whole fibre
`{y₀} × (E' \ {0})` as wave front set, even when `T` itself is smooth. -/
theorem waveFrontSet_cutoffPushforwardCLM_const {T : 𝓓'(Ω, ℂ)} (hy₀ : y₀ ∈ Ω') (hT : T χ ≠ 0) :
    (cutoffPushforwardCLM χ (fun _ : E ↦ y₀) hc T : 𝓓'(Ω', ℂ)).waveFrontSet = {y₀} ×ˢ {0}ᶜ := by
  rw [cutoffPushforwardCLM_const, waveFrontSet_smul hT, waveFrontSet_delta hy₀]

end Const

end Distribution
