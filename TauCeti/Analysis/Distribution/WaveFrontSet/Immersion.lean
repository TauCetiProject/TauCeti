/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Pushforward
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Fourier.Inversion
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Topology.Compactness.Compact

/-!
# The wave front set of a smooth density pushed forward along an immersion

Let `Φ : E → E'` be smooth on an open set `Ω` of a finite-dimensional real inner product space,
and let `χ` be a test function on `Ω`. Pushing the smooth density `χ dx` forward along `Φ` gives
the distribution

`f ↦ ∫ χ x f (Φ x) dx`

on an open set `Ω'` of `E'`, the pushforward `Φ_* (χ T)` of the constant function `T = 1`
(`Distribution.cutoffPushforwardCLM`). When `Φ` is an immersion, injective on `supp χ`, this is a
smooth density with weight `χ` on the immersed submanifold parametrized by `Φ`; for a constant map
it is a multiple of a point mass. This file shows that its wave front set lies in the conormal set
of `Φ` over `supp χ`, and that over a point `Φ x₀` with `χ x₀ ≠ 0`, `DΦ(x₀)` injective and no other
preimage in `supp χ` it is exactly the conormal space of the image. The measure on the graph of a
smooth map over a subspace, with a nowhere vanishing weight, is treated globally in
`Distribution.waveFrontSet_smulLeftCLM_ofFun_one_map_graph`; here the immersion is arbitrary and
the weight compactly supported, which is the form taken by a smooth density on a submanifold read
in charts.

* `Distribution.waveFrontSet_cutoffPushforwardCLM_ofFun_one_subset`: every covector `(y, η)` in the
  wave front set lies over a point `x ∈ supp χ` with `Φ x = y` and `DΦ(x)ᵀ η = 0`. This is
  Hörmander's bound for pushforwards (`Distribution.waveFrontSet_cutoffPushforwardCLM_subset`), as a
  smooth function has empty wave front set.
* `Distribution.mem_waveFrontSet_cutoffPushforwardCLM_ofFun_one`: conversely, if `χ x₀ ≠ 0`, the
  derivative `DΦ(x₀)` is injective and no other point of `supp χ` is mapped to `Φ x₀`, then every
  nonzero covector `η` with `DΦ(x₀)ᵀ η = 0` gives a covector `(Φ x₀, η)` of the wave front set.
* `Distribution.mem_waveFrontSet_cutoffPushforwardCLM_ofFun_one_iff`: so over such a point the
  wave front set is exactly the conormal space `{η ≠ 0 | DΦ(x₀)ᵀ η = 0}` of the image.

The hypothesis that `Φ x₀` has no other preimage in `supp χ` cannot be dropped, since two sheets
through `Φ x₀` can cancel: on `Ω = ℝ \ {0}` the map `Φ x = (|x|, 0)` into `ℝ²` is an immersion,
and for an odd weight `χ` the pushforward `f ↦ ∫ χ x f (|x|, 0) dx` is zero, although every
`(0, η₂)` with `η₂ ≠ 0` is conormal to the image at `Φ x₀`.

## The argument

For a linear injective map `A` the lower bound
(`Distribution.not_isMicrolocallySmoothAt_cutoffPushforwardCLM_continuousLinearMap_ofFun_one`) is a
computation with the Fourier transform: the localized Fourier transform of `A_* (χ T)` with cutoff
`f` at `η` is the Fourier transform of `χ (f ∘ A)` at `Aᵀ η`
(`Distribution.localFourier_cutoffPushforwardCLM`). Along the frequencies
`t η + w` with `Aᵀ η = 0` it does not depend on `t`, so rapid decay in a cone around `η` forces the
Fourier transform of `χ (f ∘ A)` to vanish at every `Aᵀ w`, that is everywhere, since `Aᵀ` is
surjective. Hence `χ (f ∘ A) = 0`, which fails at `x₀` when `χ x₀ ≠ 0` and `f (A x₀) ≠ 0`.

For a general immersion, let `A = DΦ(x₀)`. By the local normal form of an immersion
(`ContDiffOn.exists_openPartialHomeomorph_comp_fderiv_eq`), `Φ = Θ ∘ A` for a smooth change of
variables `Θ` near `A x₀` whose derivative there, and hence that of its inverse at `Φ x₀`, is the
identity.
Near `Φ x₀` the pushforward along `Θ⁻¹` of the distribution `Φ_* (χ T)`, cut off by a test
function `κ` around `Φ x₀`, is the pushforward `A_* (χ (κ ∘ Φ) T)` along the linear map `A`: on the
support of the integrand `Θ⁻¹ (Φ x) = A x`, because the points of `supp χ` mapped near `Φ x₀` lie
near `x₀`. Pushforward along `Θ⁻¹` preserves microlocal smoothness at `(Φ x₀, η)`, carrying it to
`(A x₀, η)` (`Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM`), so the linear case
applies.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 and Example 8.2.5 (a smooth density on a submanifold has the
  conormal bundle as wave front set) and Theorem 8.2.13 (the wave front set of a pushforward).
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology RealInnerProductSpace InnerProduct FourierTransform ContDiff

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'} {χ : 𝓓(Ω, ℝ)}

/-- **A smooth density on a subspace is singular in its conormal directions.** Let `A` be an
injective linear map and `χ` a test function with `χ x₀ ≠ 0`. The pushforward `A_* (χ dx)` of the
smooth density `χ dx` is not microlocally smooth at `(A x₀, η)` for any nonzero `η` with
`Aᵀ η = 0`. -/
theorem not_isMicrolocallySmoothAt_cutoffPushforwardCLM_continuousLinearMap_ofFun_one
    {A : E →L[ℝ] E'} (hA : Injective A) {x₀ : E} (hχ : χ x₀ ≠ 0) {η : E'} (hη : η ≠ 0)
    (hAη : (A†) η = 0) :
    ¬ (cutoffPushforwardCLM χ A A.contDiff.contDiffOn
      (ofFun Ω (1 : E → ℂ) volume ⊤) : 𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt (A x₀) η := by
  intro hS
  obtain ⟨f, hf, Γ, hΓ, hηΓ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hS
  obtain ⟨C, hC⟩ := hdecay 1
  set φ := cutoffCompCLM χ A A.contDiff.contDiffOn f
  -- The transpose of `A` is surjective, since `A` is injective.
  have hsurj : Surjective (A†) := by
    have h := (A†).orthogonal_range
    rw [ContinuousLinearMap.adjoint_adjoint, LinearMap.ker_eq_bot.2 hA,
      Submodule.orthogonal_eq_bot_iff] at h
    exact LinearMap.range_eq_top.1 h
  -- The localized Fourier transform of the constant function `1` is a Fourier transform.
  have hloc (ξ : E) : (ofFun Ω (1 : E → ℂ) volume ⊤).localFourier φ ξ = 𝓕 (fun y => φ y) ξ := by
    simpa only [Pi.one_apply, mul_one] using
      localFourier_ofFun (f := 1) ((locallyIntegrable_const 1).locallyIntegrableOn _) φ ξ
  -- Along the frequencies `t η + w` the localized Fourier transform is `𝓕 φ (Aᵀ w)`, independently
  -- of `t`, so rapid decay in a cone around `η` forces it to vanish.
  have hF : 𝓕 (fun y => φ y) = 0 := by
    ext v
    obtain ⟨w, rfl⟩ := hsurj v
    refine hΓ.eq_zero_of_forall_smul_add_eq (g := localFourier _ f) (w := w) hηΓ hη hcone
      (fun ξ hξ => by simpa only [pow_one] using hC ξ hξ) fun t => ?_
    rw [localFourier_cutoffPushforwardCLM, map_add, map_smul, hAη, smul_zero, zero_add, hloc]
  -- By Fourier inversion `χ (f ∘ A) = 0`, which fails at `x₀`.
  have hcont : Continuous (fun y => φ y) := φ.contDiff.continuous
  have h0 := congrFun (hcont.eq_zero_of_fourier_eq_zero
    (hcont.integrable_of_hasCompactSupport φ.hasCompactSupport) hF) x₀
  simp only [φ, cutoffCompCLM_apply, Pi.zero_apply, smul_eq_zero] at h0
  exact h0.elim hχ hf

/-- **The wave front set of a pushed-forward smooth density lies in the conormal set.** Every
covector `(y, η)` in the wave front set of the pushforward `Φ_* (χ dx)` of the smooth density
`χ dx` lies over a point `x ∈ supp χ` with `Φ x = y` and `DΦ(x)ᵀ η = 0`. -/
theorem waveFrontSet_cutoffPushforwardCLM_ofFun_one_subset {Φ : E → E'}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) :
    (cutoffPushforwardCLM χ Φ hΦ (ofFun Ω (1 : E → ℂ) volume ⊤) : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | p.1 ∈ Ω' ∧ p.2 ≠ 0 ∧ ∃ x ∈ tsupport χ, Φ x = p.1 ∧ ((fderiv ℝ Φ x)†) p.2 = 0} := by
  rintro ⟨y, ξ⟩ hp
  obtain ⟨hy, hξ, -⟩ := mem_waveFrontSet_iff.1 hp
  obtain ⟨x, hx, hxp, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset _ hp
  have h1 : (ofFun Ω (1 : E → ℂ) volume ⊤).waveFrontSet = ∅ :=
    waveFrontSet_ofFun_eq_empty contDiffOn_const
  rw [h1] at h
  exact ⟨hy, hξ, x, hx.1, hxp, h.resolve_right (notMem_empty _)⟩

/-- **A smooth density on an immersed submanifold is singular in its conormal directions.** Let
`Φ` be smooth on `Ω` with injective derivative at `x₀`, let `χ x₀ ≠ 0`, and suppose that no other
point of `supp χ` is mapped to `Φ x₀`. Then every nonzero covector `η` with `DΦ(x₀)ᵀ η = 0`, that is
conormal to the image of `Φ` at `Φ x₀`, gives a covector `(Φ x₀, η)` of the wave front set of the
pushforward `Φ_* (χ dx)` of the smooth density `χ dx`. -/
theorem mem_waveFrontSet_cutoffPushforwardCLM_ofFun_one {Φ : E → E'}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) {x₀ : E} (hχ : χ x₀ ≠ 0) (hx₀ : Φ x₀ ∈ Ω')
    (hinj : Injective (fderiv ℝ Φ x₀)) (hfib : ∀ x ∈ tsupport χ, Φ x = Φ x₀ → x = x₀)
    {η : E'} (hη : η ≠ 0) (hη₀ : ((fderiv ℝ Φ x₀)†) η = 0) :
    (Φ x₀, η) ∈
      (cutoffPushforwardCLM χ Φ hΦ (ofFun Ω (1 : E → ℂ) volume ⊤) : 𝓓'(Ω', ℂ)).waveFrontSet := by
  refine mem_waveFrontSet_iff.2 ⟨hx₀, hη, fun hT => ?_⟩
  have hx₀Ω : x₀ ∈ Ω := χ.tsupport_subset (subset_tsupport _ hχ)
  set A := fderiv ℝ Φ x₀
  set z₀ := A x₀
  -- Near `z₀`, `Φ = θ ∘ A` for a change of variables `θ` with derivative the identity at `z₀`.
  obtain ⟨θ, hz₀θ, hθA, hθd₀, -, hθc⟩ := hΦ.exists_openPartialHomeomorph_comp_fderiv_eq Ω.isOpen
    hx₀Ω (by simp) (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj)
  have hy : Φ x₀ ∈ θ.target := hθA x₀ ▸ θ.map_source hz₀θ
  have hθsymm : θ.symm (Φ x₀) = z₀ := hθA x₀ ▸ θ.left_inv hz₀θ
  -- The derivative of the inverse at `Φ x₀` is the identity.
  have hθd : fderiv ℝ θ.symm (Φ x₀) = ContinuousLinearMap.id ℝ E' := by
    have h := θ.hasFDerivAt_symm hy (f' := ContinuousLinearEquiv.refl ℝ E')
      (by rw [ContinuousLinearEquiv.coe_refl, hθsymm]; exact hθd₀)
    rw [h.fderiv, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl]
  -- On `N₀ = A⁻¹ (source θ)` the inverse of `θ` undoes `Φ` to `A`.
  set N₀ : Set E := A ⁻¹' θ.source
  have hN₀ : IsOpen N₀ := θ.open_source.preimage A.continuous
  have hθΦ (x : E) (hx : x ∈ N₀) : θ.symm (Φ x) = A x := by
    rw [← hθA x]
    exact θ.left_inv hx
  -- The points of `supp χ` mapped near `Φ x₀` lie in `N₀`.
  obtain ⟨O, hO, hON⟩ :=
    χ.hasCompactSupport.isCompact.exists_mem_nhds_inter_preimage_subset_of_forall_eq
      (hΦ.continuousOn.mono χ.tsupport_subset) hN₀ fun x hx hxy => (hfib x hx hxy ▸ hz₀θ : x ∈ N₀)
  -- A cutoff `κ` around `Φ x₀`, supported in `O` and in the target of `θ`.
  let Ω'' : Opens E' := ⟨θ.target ∩ Ω', θ.open_target.inter Ω'.isOpen⟩
  have hΩ'' : Ω'' ≤ Ω' := fun _ hz => hz.2
  have hyΩ'' : Φ x₀ ∈ Ω'' := ⟨hy, hx₀⟩
  obtain ⟨κ, hκ, hκy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hO (Ω''.isOpen.mem_nhds hyΩ''))
    inter_subset_right (1 : ℝ)
  have hθc' : ContDiffOn ℝ (⊤ : ℕ∞) θ.symm Ω'' := hθc.mono fun _ hz => hz.1
  -- Pushing the restriction of `Φ_* (χ dx)` forward along `θ⁻¹` with the cutoff `κ` gives the
  -- pushforward of `χ (κ ∘ Φ) dx` along `A`, since `θ⁻¹ ∘ Φ = A` on the support of the integrand.
  set T := (cutoffPushforwardCLM χ Φ hΦ (ofFun Ω (1 : E → ℂ) volume ⊤) : 𝓓'(Ω', ℂ))
  have hS : (cutoffPushforwardCLM κ θ.symm hθc' (restrictCLM T : 𝓓'(Ω'', ℂ)) :
      𝓓'((⊤ : Opens E'), ℂ)) = cutoffPushforwardCLM (cutoffCompCLM χ Φ hΦ κ) A
        A.contDiff.contDiffOn (ofFun Ω (1 : E → ℂ) volume ⊤) := by
    rw [restrictCLM_cutoffPushforwardCLM hΩ'']
    refine cutoffPushforwardCLM_cutoffPushforwardCLM_of_eqOn (fun x hx => hθΦ x ?_) _
    exact hON ⟨hx.1, (hκ hx.2).1⟩
  -- Microlocal smoothness of `Φ_* (χ dx)` at `(Φ x₀, η)` would carry over to `(A x₀, η)`.
  have hsmooth : (cutoffPushforwardCLM κ θ.symm hθc' (restrictCLM T : 𝓓'(Ω'', ℂ)) :
      𝓓'((⊤ : Opens E'), ℂ)).IsMicrolocallySmoothAt z₀ η := by
    refine IsMicrolocallySmoothAt.cutoffPushforwardCLM (mem_univ _) fun x hx hxz => ?_
    have hxt : x ∈ θ.target := (κ.tsupport_subset hx.1).1
    obtain rfl : x = Φ x₀ := by rw [← θ.right_inv hxt, hxz, hθA]
    rw [hθd, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
    exact ⟨hη, (isMicrolocallySmoothAt_restrictCLM_iff hΩ'' hyΩ'').2 hT⟩
  rw [hS] at hsmooth
  refine not_isMicrolocallySmoothAt_cutoffPushforwardCLM_continuousLinearMap_ofFun_one hinj ?_ hη
    hη₀ hsmooth
  simp [cutoffCompCLM_apply, hκy, hχ]

/-- **The wave front set over a point of an immersed submanifold is its conormal space.** Let `Φ`
be smooth on `Ω` with injective derivative at `x₀`, let `χ x₀ ≠ 0`, and suppose that no other
point of `supp χ` is mapped to `Φ x₀ ∈ Ω'`. Then the covectors at `Φ x₀` in the wave front set of
the pushforward `Φ_* (χ dx)` are exactly the nonzero `η` with `DΦ(x₀)ᵀ η = 0`, the covectors
conormal to the image of `Φ`. -/
theorem mem_waveFrontSet_cutoffPushforwardCLM_ofFun_one_iff {Φ : E → E'}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) {x₀ : E} (hχ : χ x₀ ≠ 0) (hx₀ : Φ x₀ ∈ Ω')
    (hinj : Injective (fderiv ℝ Φ x₀)) (hfib : ∀ x ∈ tsupport χ, Φ x = Φ x₀ → x = x₀)
    {η : E'} :
    (Φ x₀, η) ∈
        (cutoffPushforwardCLM χ Φ hΦ (ofFun Ω (1 : E → ℂ) volume ⊤) : 𝓓'(Ω', ℂ)).waveFrontSet ↔
      η ≠ 0 ∧ ((fderiv ℝ Φ x₀)†) η = 0 := by
  refine ⟨fun h => ?_, fun ⟨hη, hη₀⟩ =>
    mem_waveFrontSet_cutoffPushforwardCLM_ofFun_one hΦ hχ hx₀ hinj hfib hη hη₀⟩
  obtain ⟨-, hη, x, hx, hxy, hxη⟩ := waveFrontSet_cutoffPushforwardCLM_ofFun_one_subset hΦ h
  obtain rfl := hfib x hx hxy
  exact ⟨hη, hxη⟩

end Distribution
