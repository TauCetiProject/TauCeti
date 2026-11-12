/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone

/-!
# The wave front set of a pushforward along a linear map

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`, let `χ` be a test function on `Ω` and let `L : E → E'` be linear. The pushforward of
`χ T` along `L` is the distribution `g ↦ T (χ (g ∘ L))` (`Distribution.cutoffPushforwardCLM`). Its
wave front set satisfies

`WF (L_* (χ T)) ⊆ {(L x, η) | x ∈ supp χ ∩ supp T, (x, L† η) ∈ WF T or L† η = 0}`

(`Distribution.waveFrontSet_cutoffPushforwardCLM_subset`), where `L†` is the adjoint of `L`. The
second alternative records the covectors `η` vanishing on the range of `L`, which a pushforward can
create from nothing: pushing a smooth compactly supported density forward to a point produces a
multiple of the point mass, whose wave front set is every nonzero covector there. When `L` is
surjective, `L† η` never vanishes for `η ≠ 0` and only the first alternative remains
(`Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`); for a projection
`E × D → E` this is the wave front set of integration over the fibres.

Since `⟪L x, η⟫ = ⟪x, L† η⟫`, the Fourier atom `e_η ∘ L` is the atom `e_(L† η)`, so the localized
Fourier transform of the pushforward with cutoff `g` at `η` is that of `T` with cutoff
`χ (g ∘ L)` at `L† η` (`Distribution.localFourier_cutoffPushforwardCLM`). Rapid decay of the
latter in the direction `L† η₀` is uniform over the compact set of positions involved
(`Distribution.exists_cone_forall_decay_of_forall_isMicrolocallySmoothAt`), and on a narrow cone
around `η₀` the norm of `η` is controlled by that of `L† η` (`TauCeti.exists_cone_decay_mul`).

## Main declarations

* `Distribution.localFourier_cutoffPushforwardCLM`: localized Fourier transforms of a pushforward
  along a linear map.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front set of a pushforward
  along a linear map.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: the same along a surjective
  linear map, without the zero-covector term.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.2 (wave front sets
  under the operations on distributions, including integration over the fibres of a projection).
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'}

/-- The localized Fourier transform of a pushforward along a linear map `L`, with cutoff `g` at
the frequency `η`, is the localized Fourier transform of `T` with cutoff `χ (g ∘ L)` at the
frequency `L† η`. -/
theorem localFourier_cutoffPushforwardCLM (χ : 𝓓(Ω, ℝ)) (L : E →L[ℝ] E') (T : 𝓓'(Ω, ℂ))
    (g : 𝓓(Ω', ℂ)) (η : E') :
    (cutoffPushforwardCLM χ L L.contDiff.contDiffOn T).localFourier g η =
      T.localFourier (cutoffCompCLM χ L L.contDiff.contDiffOn g) (L.adjoint η) := by
  rw [localFourier_def, complexPairing_cutoffPushforwardCLM]
  refine (localFourier_eq T _ fun x ↦ ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    ContinuousLinearMap.adjoint_inner_right, mul_assoc]

/-- **The wave front set of a pushforward along a linear map.** If `(y, η)` lies in the wave front
set of the pushforward `L_* (χ T)` of a complex distribution `T` along a linear map `L`, then
`y = L x` for a point `x` of the support of `χ` and of `T` such that either `(x, L† η)` lies in the
wave front set of `T`, or `L† η = 0`, that is, `η` vanishes on the range of `L`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset (χ : 𝓓(Ω, ℝ)) (L : E →L[ℝ] E')
    (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM (Ω' := Ω') χ L L.contDiff.contDiffOn T).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, L x = p.1 ∧
        ((x, L.adjoint p.2) ∈ T.waveFrontSet ∨ L.adjoint p.2 = 0)} := by
  rintro ⟨y, η₀⟩ hp
  obtain ⟨hy, -, hns⟩ := mem_waveFrontSet_iff.1 hp
  by_contra hcon
  apply hns
  set ξ₀ := L.adjoint η₀
  set K := tsupport χ ∩ dsupport T
  have hK : IsCompact K := χ.hasCompactSupport.isCompact.inter_right isClosed_dsupport
  -- The positions at which `T` is microlocally smooth in the direction `ξ₀ ≠ 0`.
  set S : Set E := {x | ξ₀ ≠ 0 ∧ T.IsMicrolocallySmoothAt x ξ₀}
  have hS : IsOpen S := by
    by_cases h0 : ξ₀ = 0
    · simp [S, h0]
    · simpa [S, h0] using (isOpen_setOf_isMicrolocallySmoothAt T).preimage
        (continuous_id.prodMk continuous_const : Continuous fun x : E ↦ (x, ξ₀))
  -- Every point of `K` over `y` lies in `S`.
  have hKS : ∀ x ∈ K, L x = y → x ∈ S := by
    intro x hx hxy
    by_contra hxS
    refine hcon ⟨x, hx, hxy, ?_⟩
    by_cases h0 : ξ₀ = 0
    · exact Or.inr h0
    · exact Or.inl (mem_waveFrontSet_iff.2 ⟨χ.tsupport_subset hx.1, h0, fun hsm ↦ hxS ⟨h0, hsm⟩⟩)
  -- A cutoff `g` at `y` whose support misses the image of the rest of `K`.
  have hKS' : IsCompact (L '' (K \ S)) := (hK.diff hS).image L.continuous
  have hyKS : y ∉ L '' (K \ S) := by
    rintro ⟨x, ⟨hxK, hxS⟩, hxy⟩
    exact hxS (hKS x hxK hxy)
  have hW : (L '' (K \ S))ᶜ ∩ Ω' ∈ 𝓝 y :=
    inter_mem (hKS'.isClosed.isOpen_compl.mem_nhds hyKS) (Ω'.isOpen.mem_nhds hy)
  obtain ⟨g, hgW, hgy⟩ := exists_tsupport_subset_apply_eq (n := ⊤) hW inter_subset_right (1 : ℂ)
  set φ := cutoffCompCLM χ L L.contDiff.contDiffOn g
  have hφS : ∀ x ∈ tsupport φ ∩ dsupport T, x ∈ S := by
    rintro x ⟨hxφ, hxT⟩
    have hx := tsupport_cutoffCompCLM_subset g hxφ
    by_contra hxS
    exact (hgW hx.2).1 ⟨x, ⟨⟨hx.1, hxT⟩, hxS⟩, rfl⟩
  refine isMicrolocallySmoothAt_iff.2 ⟨g, by simp [hgy], ?_⟩
  by_cases h0 : ξ₀ = 0
  · -- No point of the support of `T` lies over `y`: the localized transform vanishes.
    refine ⟨univ, isOpen_univ, mem_univ _, fun _ _ _ _ ↦ mem_univ _, fun N ↦ ⟨0, fun η _ ↦ ?_⟩⟩
    rw [localFourier_cutoffPushforwardCLM, localFourier_eq_zero_of_disjoint T
      (disjoint_left.2 fun x hxφ hxT ↦ (hφS x ⟨hxφ, hxT⟩).1 h0), norm_zero, mul_zero]
  · -- Decay in the direction `L† η₀ ≠ 0` gives decay on a cone around `η₀`.
    obtain ⟨Γ, hΓ, hξΓ, hcone, hdecay⟩ :=
      exists_cone_forall_decay_of_forall_isMicrolocallySmoothAt (φ := φ) fun x hx ↦ (hφS x hx).2
    obtain ⟨Γ', hΓ', hη₀Γ', hcone', hdecay'⟩ := TauCeti.exists_cone_decay_mul L.adjoint
      (ContinuousLinearMap.id ℝ E') (fun _ ↦ le_add_of_nonneg_left (norm_nonneg _)) hΓ hcone hξΓ
      h0 hdecay (h := fun _ ↦ (1 : ℂ)) ⟨1, 0, fun _ ↦ by simp⟩
    refine ⟨Γ', hΓ', hη₀Γ', hcone', fun N ↦ ?_⟩
    obtain ⟨C, hC⟩ := hdecay' N
    exact ⟨C, fun η hη ↦ by simpa [localFourier_cutoffPushforwardCLM] using hC η hη⟩

/-- **The wave front set of a pushforward along a surjective linear map**, such as a projection
`E × D → E`: if `(y, η)` lies in the wave front set of `L_* (χ T)`, then `y = L x` for a point `x`
of the support of `χ` and of `T` with `(x, L† η)` in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective (χ : 𝓓(Ω, ℝ)) {L : E →L[ℝ] E'}
    (hL : Surjective L) (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM (Ω' := Ω') χ L L.contDiff.contDiffOn T).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, L x = p.1 ∧ (x, L.adjoint p.2) ∈ T.waveFrontSet} := by
  intro p hp
  obtain ⟨x, hx, hxp, h | h⟩ := waveFrontSet_cutoffPushforwardCLM_subset χ L T hp
  · exact ⟨x, hx, hxp, h⟩
  · -- The kernel of `L†` is the orthogonal complement of the range of `L`, which is zero.
    have hmem : p.2 ∈ (LinearMap.range (L : E →ₗ[ℝ] E'))ᗮ := by
      rw [ContinuousLinearMap.orthogonal_range]
      exact h
    rw [LinearMap.range_eq_top.2 hL, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hmem
    exact absurd hmem (mem_waveFrontSet_iff.1 hp).2.1

end Distribution
