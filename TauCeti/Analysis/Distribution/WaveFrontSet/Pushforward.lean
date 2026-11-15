/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.NonlinearPhase
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The wave front set of a pushforward along a smooth map

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`, let `χ` be a test function on `Ω`, and let `Φ : E → E'` be smooth on `Ω`. The
pushforward `Φ_* (χ T)` is the distribution `f ↦ T (χ (f ∘ Φ))` on an open set `Ω'` of `E'`
(`Distribution.cutoffPushforwardCLM`); when `χ` is equal to one near the support of `T`, which is
then compact, it is the pushforward `Φ_* T`, and for a projection it is integration over the
fibres. This file proves Hörmander's bound for its wave front set:

`WF(Φ_* (χ T)) ⊆ {(Φ x, η) | x ∈ supp χ ∩ supp T, Φ'(x)ᵀ η = 0 or (x, Φ'(x)ᵀ η) ∈ WF(T)}`.

The localized Fourier transform of `Φ_* (χ T)` with cutoff `f` at `η` is the pairing of `T` with
`χ (f ∘ Φ) 𝐞 (-⟪Φ ·, η⟫)`. Over a point `y`, the compact set `supp χ ∩ supp T ∩ Φ⁻¹ {y}` is covered
by finitely many neighbourhoods on which such pairings decay rapidly in a cone around `η`
(`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone_decay_phase`), and a cutoff `f` around `y`
pulls back to a sum of cutoffs supported in these neighbourhoods and off the support of `T`.

For a linear map `A` the localized Fourier transforms of `A_* T` are localized Fourier transforms
of `T` at the transposed frequency (`Distribution.localFourier_cutoffPushforwardCLM`).

The covectors with `Φ'(x)ᵀ η = 0` cannot be omitted, even for smooth `T`: along a constant map with
value `c` the pushforward of `T` is the multiple `T χ` of the point mass at `c`, and when `T χ ≠ 0`
its wave front set is `{c} × (E' \ {0})` (`Distribution.waveFrontSet_cutoffPushforwardCLM_const`).
The differential of a constant map is zero, so all these covectors come from the term
`Φ'(x)ᵀ η = 0`. When `Φ` is a submersion, `Φ'(x)ᵀ` is injective and these covectors do not occur.

## Main results

* `Distribution.localFourier_cutoffPushforwardCLM`: localized Fourier transforms of `A_* T` along
  a linear map `A` are localized Fourier transforms of `T` at the transposed frequency.
* `Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM`: if `Φ'(x)ᵀ η ≠ 0` and `T` is
  microlocally smooth at `(x, Φ'(x)ᵀ η)` for every `x ∈ supp χ ∩ supp T` with `Φ x = y`, then
  `Φ_* (χ T)` is microlocally smooth at `(y, η)`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front bound above.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: when `Φ'(x)` is
  surjective on `supp χ`, `WF(Φ_* (χ T)) ⊆ {(Φ x, η) | x ∈ supp χ ∩ supp T, (x, Φ'(x)ᵀ η) ∈ WF(T)}`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_const`: the pushforward along a constant map
  with value `c` has wave front set `{c} × (E' \ {0})` whenever `T χ ≠ 0`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.13 (the wave front set of a pushforward).
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace InnerProduct ContDiff FourierTransform

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

end Linear

section Smooth

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

omit [FiniteDimensional ℝ E'] in
/-- A cutoff `ψ` modulated along a map `Φ` smooth on `Ω`: the test functions
`ψ 𝐞 (-⟪Φ ·, η⟫)`. -/
private theorem exists_modulate_comp {Φ : E → E'} (hΦ : ContDiffOn ℝ ∞ Φ Ω) (ψ : 𝓓(Ω, ℂ)) :
    ∃ g : E' → 𝓓(Ω, ℂ), ∀ η x, g η x = ψ x * 𝐞 (-⟪Φ x, η⟫) := by
  -- A smooth map `Φ₁` on `E` equal to `Φ` near the support of `ψ`.
  obtain ⟨χ₁, hχ₁, -⟩ := exists_eventually_eq_one (n := ⊤) ψ.hasCompactSupport.isCompact
    ψ.tsupport_subset
  have hΦ₁ : ContDiff ℝ ∞ fun x ↦ χ₁ x • Φ x :=
    hΦ.contDiff_smul_of_tsupport_subset Ω.isOpen χ₁.contDiff.contDiffOn χ₁.tsupport_subset
  refine ⟨fun η ↦ bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    ((TauCeti.contDiff_fourierAtom η).comp hΦ₁) ψ, fun η x ↦ ?_⟩
  by_cases hx : ψ x = 0
  · simp [bilinLeftCLM_apply, hx]
  have h1 : χ₁ x = 1 := hχ₁.self_of_nhdsSet x (subset_tsupport _ hx)
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', Function.comp_apply,
    TauCeti.fourierAtom_eq_fourierChar, h1, one_smul]

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
/-- The localized Fourier transform of `Φ_* (χ T)` with cutoff `f`, after splitting the pulled-back
cutoff `χ (f ∘ Φ)` into pieces `ψ i`, is the sum of the pairings of `T` with the pieces modulated
along `Φ`. -/
private theorem localFourier_cutoffPushforwardCLM_eq_sum {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} (T : 𝓓'(Ω, ℂ)) {f : 𝓓(Ω', ℂ)} {ι : Type*} [Fintype ι]
    {ψ : ι → 𝓓(Ω, ℂ)} (hψ : ∑ i, ψ i = cutoffCompCLM χ Φ hΦ f) {g : ι → E' → 𝓓(Ω, ℂ)}
    (hg : ∀ i η x, g i η x = ψ i x * 𝐞 (-⟪Φ x, η⟫)) (η : E') :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).localFourier f η =
      ∑ i, T.complexPairing (g i η) := by
  rw [localFourier_def, complexPairing_cutoffPushforwardCLM, ← map_sum]
  congr 1
  ext x
  have hx := congrArg (fun φ : 𝓓(Ω, ℂ) ↦ φ x) hψ
  simp only [sum_apply] at hx
  simp only [sum_apply, hg, ← Finset.sum_mul, hx, cutoffCompCLM_apply, bilinLeftCLM_apply,
    ContinuousLinearMap.mul_apply', TauCeti.fourierAtom_eq_fourierChar, real_smul]
  ring

/-- **Microlocal smoothness of a pushforward along a smooth map.** Let `Φ` be smooth on `Ω` and
`y ∈ Ω'`. If for every `x ∈ supp χ ∩ supp T` with `Φ x = y` the covector `Φ'(x)ᵀ η` is nonzero
and `T` is microlocally smooth at `(x, Φ'(x)ᵀ η)`, then the pushforward `Φ_* (χ T)` is
microlocally smooth at `(y, η)`. -/
theorem IsMicrolocallySmoothAt.cutoffPushforwardCLM {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} {T : 𝓓'(Ω, ℂ)} {y η : E'} (hy : y ∈ Ω')
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, Φ x = y →
      ((fderiv ℝ Φ x)†) η ≠ 0 ∧ T.IsMicrolocallySmoothAt x (((fderiv ℝ Φ x)†) η)) :
    (Distribution.cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt y η := by
  classical
  set D := tsupport χ ∩ dsupport T
  have hD : IsCompact D := χ.hasCompactSupport.inter_right isClosed_dsupport
  have hDΩ : D ⊆ Ω := inter_subset_left.trans χ.tsupport_subset
  have hΦD : ContinuousOn Φ D := hΦ.continuousOn.mono hDΩ
  have hK : IsCompact (D ∩ Φ ⁻¹' {y}) := hD.of_isClosed_subset
    (hΦD.preimage_isClosed_of_isClosed hD.isClosed isClosed_singleton) inter_subset_left
  -- Over the fibre `D ∩ Φ⁻¹ {y}`, the local estimate gives finitely many neighbourhoods and cones.
  choose U hU Γ hΓ hηΓ hcone hdecay using fun x : (D ∩ Φ ⁻¹' {y} : Set E) ↦
    (h x x.2.1 x.2.2).2.exists_nhds_cone_decay_phase hΦ (hDΩ x.2.1) (h x x.2.1 x.2.2).1
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x ↦ interior (U x))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU ⟨x, hx⟩)⟩
  set W := ⋃ x ∈ t, interior (U x)
  -- A cutoff `f` around `y` whose pullback `ψ = χ (f ∘ Φ)` meets `supp T` only inside `W`.
  have hyC : y ∉ Φ '' (D \ W) := fun ⟨x, ⟨hxD, hxW⟩, hxy⟩ ↦ hxW (ht ⟨hxD, hxy⟩)
  obtain ⟨f, hf, hfy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (((hD.diff (isOpen_biUnion fun _ _ ↦ isOpen_interior)).image_of_continuousOn
      (hΦD.mono sdiff_subset)).isClosed.isOpen_compl.mem_nhds hyC) (Ω'.isOpen.mem_nhds hy))
    inter_subset_right (1 : ℂ)
  set ψ := cutoffCompCLM χ Φ hΦ f
  have hψ : tsupport ψ ⊆ ⋃ i : Option t, i.elim (dsupport T)ᶜ fun x ↦ interior (U x) := by
    intro z hz
    obtain ⟨hzχ, hzf⟩ := tsupport_cutoffCompCLM_subset f hz
    by_cases hzT : z ∈ dsupport T
    · by_contra hzW
      refine (hf hzf).1 ⟨z, ⟨⟨hzχ, hzT⟩, fun hz' ↦ hzW ?_⟩, rfl⟩
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz'
      exact mem_iUnion.2 ⟨some ⟨x, hx⟩, hzx⟩
    · exact mem_iUnion.2 ⟨none, hzT⟩
  -- Split `ψ` into pieces supported in these neighbourhoods and one piece off the support of `T`.
  obtain ⟨s, ψs, hψs, hsum, -⟩ := ψ.exists_sum_subordinate _
    (fun i ↦ i.rec isClosed_dsupport.isOpen_compl fun _ ↦ isOpen_interior) hψ
  choose g hg using fun i : s ↦ exists_modulate_comp hΦ (ψs i)
  refine isMicrolocallySmoothAt_iff.2 ⟨f, by simp [hfy], ⋂ x ∈ t, Γ x,
    isOpen_biInter_finset fun x _ ↦ hΓ x, mem_iInter₂.2 fun x _ ↦ hηΓ x,
    fun r hr ζ hζ ↦ mem_iInter₂.2 fun x hx ↦ hcone x r hr ζ (mem_iInter₂.1 hζ x hx),
    fun N ↦ ?_⟩
  simp only [localFourier_cutoffPushforwardCLM_eq_sum T hsum fun i ↦ hg i]
  -- Each piece decays on the intersection of the cones.
  refine TauCeti.exists_one_add_norm_pow_mul_norm_sum_le _ fun i _ ↦ ?_
  obtain ⟨i, hi⟩ := i
  cases i with
  | none => exact ⟨0, fun ζ _ ↦ by
      rw [complexPairing_eq_zero_of_disjoint_dsupport T (disjoint_left.2 fun z hz ↦ hψs ⟨none, hi⟩
        (closure_mono (fun z hz' ↦ left_ne_zero_of_mul (by rwa [Function.mem_support, hg] at hz'))
          hz)), norm_zero, mul_zero]⟩
  | some x =>
    obtain ⟨C, hC⟩ := hdecay x (ψs ⟨some x, hi⟩) (g ⟨some x, hi⟩)
      ((hψs _).trans interior_subset) (hg _) N
    exact ⟨C, fun ζ hζ ↦ hC ζ (mem_iInter₂.1 hζ x x.2)⟩

/-- **The wave front set of a pushforward along a smooth map** (Hörmander I, Theorem 8.2.13).
Every covector `(y, η)` in the wave front set of the pushforward `Φ_* (χ T)` along a map `Φ`
smooth on `Ω` lies over a point `x` of `supp χ ∩ supp T` with `Φ x = y`, at which either
`Φ'(x)ᵀ η = 0` or `(x, Φ'(x)ᵀ η)` lies in the wave front set of `T`. When `χ` is equal to one near
the support of `T`, this is the bound for the pushforward `Φ_* T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset {Φ : E → E'}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, Φ x = p.1 ∧
        (((fderiv ℝ Φ x)†) p.2 = 0 ∨ (x, ((fderiv ℝ Φ x)†) p.2) ∈ T.waveFrontSet)} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨hy, -, hS⟩ := mem_waveFrontSet_iff.1 hp
  by_contra hne
  refine hS (IsMicrolocallySmoothAt.cutoffPushforwardCLM hy fun x hx hxy ↦ ⟨fun h0 ↦
    hne ⟨x, hx, hxy, Or.inl h0⟩, ?_⟩)
  by_contra hT
  exact hne ⟨x, hx, hxy, Or.inr (mem_waveFrontSet_iff.2 ⟨χ.tsupport_subset hx.1,
    fun h0 ↦ hne ⟨x, hx, hxy, Or.inl h0⟩, hT⟩)⟩

/-- **Pushforward along a submersion.** If the differential of `Φ` is surjective at every point of
the support of `χ`, its transpose is injective there, and every covector `(y, η)` in the wave front
set of `Φ_* (χ T)` lies over a point `x` of `supp χ ∩ supp T` with `Φ x = y` and
`(x, Φ'(x)ᵀ η)` in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} (hsurj : ∀ x ∈ tsupport χ, Surjective (fderiv ℝ Φ x))
    (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, Φ x = p.1 ∧
        (x, ((fderiv ℝ Φ x)†) p.2) ∈ T.waveFrontSet} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨x, hx, hxy, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset hΦ T hp
  refine ⟨x, hx, hxy, h.resolve_left fun h0 ↦ (mem_waveFrontSet_iff.1 hp).2.1 ?_⟩
  obtain ⟨z, hz⟩ := hsurj x hx.1 η
  have h := ContinuousLinearMap.adjoint_inner_left (fderiv ℝ Φ x) z η
  rw [h0, inner_zero_left, hz] at h
  exact inner_self_eq_zero.1 h.symm

end Smooth

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
    rw [cutoffPushforwardCLM_const]
    ext f
    simp [mul_comm]
  rw [h, waveFrontSet_smul hT, waveFrontSet_delta hc]

end Const

end Distribution
