/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
public import TauCeti.Geometry.Symplectic.JHolomorphic.AdaptedChart
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy

/-!
# Accumulating coincidences of pseudoholomorphic discs

Let `J` be an almost complex structure of class `C²` on a finite-dimensional real normed space
`V`, written in coordinates, and let `u₀, u₁ : ℂ → V` be `J`-holomorphic discs,
`∂ₛu + J(u) ∂ₜu = 0`, with `u₀` immersed at `a₀`. If the images of `u₀` near `a₀` and of `u₁`
near `b₀` meet at points `u₁ ζ` with `ζ ≠ b₀` accumulating at `b₀`, then near `b₀` the disc `u₁`
is a reparametrization of `u₀`: `u₁ = u₀ ∘ φ` for a holomorphic `φ` with `φ b₀ = a₀`
(`TauCeti.exists_analyticAt_eventuallyEq_comp_of_frequently_mem_image`, and
`TauCeti.exists_analyticAt_eventuallyEq_comp_of_tendsto` for sequences of coincidences
`u₀ (z k) = u₁ (ζ k)` with `z k → a₀`, `ζ k → b₀` and `ζ k ≠ b₀`). The disc `u₁` may be
critical at `b₀`, and then so is `φ`: for `u₀ z = (z, 0)` and `u₁ ζ = (ζ², 0)` the factor is
`φ ζ = ζ²`.

This is McDuff–Salamon's Lemma 2.4.3, the local input for the factorization of a
pseudoholomorphic curve through a simple one. Their proof is followed here. In the coordinates
adapted to `u₀` of `TauCeti.exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le`, the disc `u₀`
is the zero section `a ↦ (a, 0)` of `ℂ × N`, and the structure read in the chart is `i` along it
and differs from `i` by at most `C ‖w‖` at `(a, w)`. Write `u₁ = (φ, b)` in these coordinates.

* The normal component satisfies `‖∂ₛb + i ∂ₜb‖ ≤ C ‖∂ₜ(φ, b)‖ ‖b‖`
  (`TauCeti.norm_snd_add_I_smul_snd_le`), so by Carleman's similarity principle for this
  differential inequality (`TauCeti.hasSimilarityFactorizationAt_of_norm_le`) it has a similarity
  factorization (`TauCeti.hasSimilarityFactorizationAt_snd_of_norm_sub_le`).
* Hence `b` either vanishes near `b₀` or has no zeros in a punctured neighbourhood of `b₀`. A
  coincidence `u₁ ζ = u₀ a` with `a` near `a₀` is a zero of `b`, so `b` vanishes near `b₀`.
* Then `u₁ ζ = u₀ (φ ζ)`, and along the zero section the structure read in the chart is `i`, so
  the Cauchy–Riemann equation of `u₁` makes `φ` holomorphic.

The normal frame of the adapted coordinates is the orthogonal complement, in a complex frame of
`J(u₀ a₀)`, of the complex tangent line of `u₀` at `a₀`
(`TauCeti.exists_euclideanSpace_bijective_coprod`). The disc `u₀` is assumed of class `C²`,
the regularity of the adapted coordinates; for `J` of class `C²` this follows from elliptic
regularity, which is not used here.

## Main results

* `TauCeti.hasSimilarityFactorizationAt_snd_of_norm_sub_le`: in coordinates where the structure
  is `i` to first order along the zero section of `ℂ × N`, the normal component of a disc has a
  similarity factorization.
* `TauCeti.exists_analyticAt_eventuallyEq_comp_of_frequently_mem_image`: accumulating
  coincidences force `u₁ = u₀ ∘ φ` near `b₀` for a holomorphic `φ`.
* `TauCeti.exists_analyticAt_eventuallyEq_comp_of_tendsto`: the same for convergent sequences of
  coincidences.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section 2.4, Lemma 2.4.3.
-/

public section

open Complex Filter Metric Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {J : V → V →L[ℝ] V}
  {u₀ u₁ : ℂ → V} {U U₁ : Set ℂ} {Ω : Set V} {a₀ b₀ : ℂ}

section NormalComponent

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N]

/-- **The normal component of a nearly standard disc has a similarity factorization.** Let
`ψ : ℂ → ℂ × N` be `C¹` on an open set `Ω₁` and solve `∂ₛψ + A ∂ₜψ = 0` for a field `A` of
endomorphisms of `ℂ × N` which is multiplication by `i` to first order along the zero section:
`‖A ζ - i‖ ≤ C ‖(ψ ζ).2‖`. Then the normal component `b = (ψ ·).2` satisfies the differential
inequality `‖∂ₛb + i ∂ₜb‖ ≤ C ‖∂ₜψ‖ ‖b‖`, and so has a similarity factorization at every point
of `Ω₁`. -/
theorem hasSimilarityFactorizationAt_snd_of_norm_sub_le {ψ : ℂ → ℂ × N}
    {A : ℂ → ℂ × N →L[ℝ] ℂ × N} {Ω₁ : Set ℂ} {C : ℝ} (hΩ₁ : IsOpen Ω₁)
    (hψ : ContDiffOn ℝ 1 ψ Ω₁)
    (hA : ∀ ζ ∈ Ω₁, ‖A ζ - I • ContinuousLinearMap.id ℝ (ℂ × N)‖ ≤ C * ‖(ψ ζ).2‖)
    (hCR : ∀ ζ ∈ Ω₁, fderiv ℝ ψ ζ 1 + A ζ (fderiv ℝ ψ ζ I) = 0) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ Ω₁) :
    HasSimilarityFactorizationAt (fun ζ ↦ (ψ ζ).2) ζ₀ := by
  have hDψ : ContinuousOn (fderiv ℝ ψ) Ω₁ := hψ.continuousOn_fderiv_of_isOpen hΩ₁ le_rfl
  refine hasSimilarityFactorizationAt_of_norm_le (η := fun ζ ↦ (ψ ζ).2)
    (M := fun ζ ↦ C * ‖fderiv ℝ ψ ζ I‖) hΩ₁ (contDiff_snd.comp_contDiffOn hψ) (fun z hz ↦ ?_)
    (fun ζ hζ ↦ ?_) hζ₀
  · -- `C ‖∂ₜψ‖` is continuous, hence locally bounded.
    have hz : ContinuousAt (fun w ↦ C * ‖fderiv ℝ ψ w I‖) z := continuousAt_const.mul
      ((hDψ.clm_apply continuousOn_const).continuousAt (hΩ₁.mem_nhds hz)).norm
    exact ⟨_, (hz.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h ↦ h.le⟩
  · rw [((hψ.differentiableOn one_ne_zero ζ hζ).differentiableAt
      (hΩ₁.mem_nhds hζ)).hasFDerivAt.snd.fderiv]
    refine (norm_snd_add_I_smul_snd_le (hA ζ hζ) (hCR ζ hζ)).trans_eq ?_
    ring

/-- **Accumulating coincidences in a prescribed normal frame.** The form of
`TauCeti.exists_analyticAt_eventuallyEq_comp_of_frequently_mem_image` in which the normal frame
`W` of the adapted coordinates is given. -/
private theorem exists_analyticAt_eventuallyEq_comp_of_frame [CompleteSpace V] [CompleteSpace N]
    {W : N →L[ℝ] V}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (ha₀ : a₀ ∈ U) (hu₀ : ContDiffOn ℝ 2 u₀ U)
    (hJ : ContDiffOn ℝ 2 J Ω) (hu₀Ω : MapsTo u₀ U Ω)
    (hsq : ∀ a ∈ U, ∀ v, J (u₀ a) (J (u₀ a) v) = -v)
    (hCR₀ : ∀ a ∈ U, fderiv ℝ u₀ a 1 + J (u₀ a) (fderiv ℝ u₀ a I) = 0)
    (hW : ∀ w, J (u₀ a₀) (W w) = W (I • w))
    (hbij : Function.Bijective ((fderiv ℝ u₀ a₀).coprod W)) (hU₁ : IsOpen U₁) (hb₀ : b₀ ∈ U₁)
    (hu₁ : ContDiffOn ℝ 1 u₁ U₁)
    (hCR₁ : ∀ ζ ∈ U₁, fderiv ℝ u₁ ζ 1 + J (u₁ ζ) (fderiv ℝ u₁ ζ I) = 0)
    (hub : u₁ b₀ = u₀ a₀) (hacc : ∀ S ∈ 𝓝 a₀, ∃ᶠ ζ in 𝓝[≠] b₀, u₁ ζ ∈ u₀ '' S) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ b₀ ∧ φ b₀ = a₀ ∧ u₁ =ᶠ[𝓝 b₀] u₀ ∘ φ := by
  obtain ⟨e, he, h₀, -, -, hc, hcs, hstd, C, hC⟩ :=
    exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le hU hΩ ha₀ le_rfl hu₀ hJ hu₀Ω hsq hCR₀
      hW hbij
  -- The chart sends the disc `u₀` to the zero section.
  have he0 (a : ℂ) : e (a, 0) = u₀ a := by rw [he, holomorphicNormalExtension_zero]
  have hsymm0 (a : ℂ) (ha : (a, (0 : N)) ∈ e.source) : e.symm (u₀ a) = (a, 0) := by
    rw [← he0 a, e.left_inv ha]
  -- An open set `Ω₁ ∋ b₀` on which `u₁` reads as `ψ` in the chart, with the normal control.
  obtain ⟨t, htC, ht, h₀t⟩ := _root_.eventually_nhds_iff.1 hC
  set Ω₁ := U₁ ∩ u₁ ⁻¹' (e.target ∩ e.symm ⁻¹' t)
  have hΩ₁o : IsOpen Ω₁ :=
    hu₁.continuousOn.isOpen_inter_preimage hU₁ (e.isOpen_inter_preimage_symm ht)
  have hb₀Ω₁ : b₀ ∈ Ω₁ := ⟨hb₀, by
    rw [mem_preimage, hub, ← he0 a₀, mem_inter_iff, mem_preimage, e.left_inv h₀]
    exact ⟨e.map_source h₀, h₀t⟩⟩
  set ψ : ℂ → ℂ × N := e.symm ∘ u₁ with hψ
  have hψc : ContDiffOn ℝ 1 ψ Ω₁ :=
    (hcs.of_le one_le_two).comp (hu₁.mono inter_subset_left) fun ζ hζ ↦ hζ.2.1
  have hCRψ {ζ : ℂ} (hζ : ζ ∈ Ω₁) :
      fderiv ℝ ψ ζ 1 + e.pullbackEnd J (ψ ζ) (fderiv ℝ ψ ζ I) = 0 := by
    have hζs : e.symm (u₁ ζ) ∈ e.source := e.map_target hζ.2.1
    exact e.fderiv_add_pullbackEnd_fderiv_eq_zero hζ.2.1
      ((hu₁.differentiableOn one_ne_zero ζ hζ.1).differentiableAt (hU₁.mem_nhds hζ.1))
      ((hc.differentiableOn two_ne_zero _ hζs).differentiableAt (e.open_source.mem_nhds hζs))
      ((hcs.differentiableOn two_ne_zero _ hζ.2.1).differentiableAt
        (e.open_target.mem_nhds hζ.2.1)) (hCR₁ ζ hζ.1)
  -- The normal component of `ψ` has a similarity factorization, and its zeros accumulate at
  -- `b₀`, so it vanishes near `b₀`.
  have hfac := hasSimilarityFactorizationAt_snd_of_norm_sub_le hΩ₁o hψc
    (fun ζ hζ ↦ htC (ψ ζ) hζ.2.2) (fun ζ hζ ↦ hCRψ hζ) hb₀Ω₁
  have hS : (fun a : ℂ ↦ (a, (0 : N))) ⁻¹' e.source ∈ 𝓝 a₀ :=
    (Continuous.prodMk_left (0 : N)).continuousAt.preimage_mem_nhds (e.open_source.mem_nhds h₀)
  have hb0 : ∀ᶠ ζ in 𝓝 b₀, (ψ ζ).2 = 0 :=
    hfac.eventually_eq_zero_or_eventually_ne_zero.resolve_right fun h ↦ by
      obtain ⟨ζ, ⟨a, ha, hζa⟩, h2⟩ := ((hacc _ hS).and_eventually h).exists
      exact h2 (by rw [hψ, Function.comp_apply, ← hζa, hsymm0 a ha])
  -- Where the normal component vanishes, `u₁ = u₀ ∘ φ` and `φ` is holomorphic.
  have hev : ∀ᶠ ζ in 𝓝 b₀, ζ ∈ Ω₁ ∧ ψ ζ = ((ψ ζ).1, 0) :=
    (hΩ₁o.eventually_mem hb₀Ω₁).and (hb0.mono fun ζ h ↦ Prod.ext rfl h)
  refine ⟨fun ζ ↦ (ψ ζ).1, analyticAt_iff_eventually_differentiableAt.2
    (hev.mono fun ζ ⟨hζ, hψeq⟩ ↦ ?_), ?_, hev.mono fun ζ ⟨hζ, hψeq⟩ ↦ ?_⟩
  · have hCR := hCRψ hζ
    rw [hψeq, hstd _ (hψeq ▸ e.map_target hζ.2.1)] at hCR
    refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
      ((hψc.differentiableOn one_ne_zero ζ hζ).differentiableAt (hΩ₁o.mem_nhds hζ))).2
      ((smul_eq_zero_iff_right (two_ne_zero' ℂ)).1 ?_)).fst
    rw [← fderiv_apply_one_add_I_smul_fderiv_apply_I]
    simpa using hCR
  · simp only [hψ, Function.comp_apply, hub, hsymm0 a₀ h₀]
  · rw [Function.comp_apply, ← he0 (ψ ζ).1, ← hψeq, hψ, Function.comp_apply, e.right_inv hζ.2.1]

end NormalComponent

omit [NormedSpace ℝ V] in
/-- The coincidences of `u₁` with `u₀` accumulate at `u₁ b₀`, so this point lies on `u₀`. -/
private theorem eq_of_frequently_mem_image (hu₀ : ContinuousAt u₀ a₀) (hu₁ : ContinuousAt u₁ b₀)
    (hacc : ∀ S ∈ 𝓝 a₀, ∃ᶠ ζ in 𝓝[≠] b₀, u₁ ζ ∈ u₀ '' S) : u₁ b₀ = u₀ a₀ := by
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hS : u₀ ⁻¹' ball (u₀ a₀) (ε / 2) ∈ 𝓝 a₀ := hu₀.preimage_mem_nhds (ball_mem_nhds _ (by
    positivity))
  have hev : ∀ᶠ ζ in 𝓝[≠] b₀, u₁ ζ ∈ ball (u₁ b₀) (ε / 2) :=
    nhdsWithin_le_nhds (hu₁.eventually (ball_mem_nhds _ (half_pos hε)))
  obtain ⟨ζ, ⟨a, ha, hζa⟩, hζ⟩ := ((hacc _ hS).and_eventually hev).exists
  calc dist (u₁ b₀) (u₀ a₀) ≤ dist (u₁ b₀) (u₁ ζ) + dist (u₁ ζ) (u₀ a₀) := dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · rw [dist_comm]
          exact (mem_ball.1 hζ).le
        · rw [← hζa]
          exact (mem_ball.1 ha).le
    _ = ε := add_halves ε

/-- **Accumulating coincidences factor a pseudoholomorphic disc** (McDuff–Salamon, Lemma 2.4.3).
Let `J` be of class `C²` on an open set `Ω` of a finite-dimensional real normed space `V`, and let
`u₀` be a `J`-holomorphic disc of class `C²` on an open `U ∋ a₀` with values in `Ω`, where
`J(u₀ a)² = -1`, and with `du₀(a₀) ≠ 0`. Let `u₁` be a `J`-holomorphic disc of class `C¹` on an
open `U₁ ∋ b₀`. Suppose that for every neighbourhood `S` of `a₀` the points `ζ ≠ b₀` with
`u₁ ζ ∈ u₀ (S)` accumulate at `b₀`. Then there is a function `φ`, holomorphic at `b₀`, with
`φ b₀ = a₀` and `u₁ = u₀ ∘ φ` near `b₀`. -/
theorem exists_analyticAt_eventuallyEq_comp_of_frequently_mem_image [FiniteDimensional ℝ V]
    (hU : IsOpen U) (hΩ : IsOpen Ω) (ha₀ : a₀ ∈ U) (hu₀ : ContDiffOn ℝ 2 u₀ U)
    (hJ : ContDiffOn ℝ 2 J Ω) (hu₀Ω : MapsTo u₀ U Ω)
    (hsq : ∀ a ∈ U, ∀ v, J (u₀ a) (J (u₀ a) v) = -v)
    (hCR₀ : ∀ a ∈ U, fderiv ℝ u₀ a 1 + J (u₀ a) (fderiv ℝ u₀ a I) = 0)
    (hdu₀ : fderiv ℝ u₀ a₀ ≠ 0) (hU₁ : IsOpen U₁) (hb₀ : b₀ ∈ U₁) (hu₁ : ContDiffOn ℝ 1 u₁ U₁)
    (hCR₁ : ∀ ζ ∈ U₁, fderiv ℝ u₁ ζ 1 + J (u₁ ζ) (fderiv ℝ u₁ ζ I) = 0)
    (hacc : ∀ S ∈ 𝓝 a₀, ∃ᶠ ζ in 𝓝[≠] b₀, u₁ ζ ∈ u₀ '' S) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ b₀ ∧ φ b₀ = a₀ ∧ u₁ =ᶠ[𝓝 b₀] u₀ ∘ φ := by
  have := FiniteDimensional.completeSpace ℝ V
  have hub : u₁ b₀ = u₀ a₀ := eq_of_frequently_mem_image
    (hu₀.continuousOn.continuousAt (hU.mem_nhds ha₀))
    (hu₁.continuousOn.continuousAt (hU₁.mem_nhds hb₀)) hacc
  obtain ⟨n, W, hW, hbij⟩ :=
    exists_euclideanSpace_bijective_coprod
      (ContinuousLinearMap.ext fun v ↦ by simpa using hsq a₀ ha₀ v) (hCR₀ a₀ ha₀) hdu₀
  exact exists_analyticAt_eventuallyEq_comp_of_frame hU hΩ ha₀ hu₀ hJ hu₀Ω hsq hCR₀ hW hbij hU₁
    hb₀ hu₁ hCR₁ hub hacc

/-- **Accumulating coincidences factor a pseudoholomorphic disc**, for sequences
(McDuff–Salamon, Lemma 2.4.3). Under the hypotheses on `J`, `u₀` and `u₁` of
`TauCeti.exists_analyticAt_eventuallyEq_comp_of_frequently_mem_image`, if
`u₀ (z k) = u₁ (ζ k)` with `z k → a₀`, `ζ k → b₀` and `ζ k ≠ b₀`, then `u₁ = u₀ ∘ φ` near `b₀`
for a function `φ` holomorphic at `b₀` with `φ b₀ = a₀`. -/
theorem exists_analyticAt_eventuallyEq_comp_of_tendsto [FiniteDimensional ℝ V]
    (hU : IsOpen U) (hΩ : IsOpen Ω) (ha₀ : a₀ ∈ U) (hu₀ : ContDiffOn ℝ 2 u₀ U)
    (hJ : ContDiffOn ℝ 2 J Ω) (hu₀Ω : MapsTo u₀ U Ω)
    (hsq : ∀ a ∈ U, ∀ v, J (u₀ a) (J (u₀ a) v) = -v)
    (hCR₀ : ∀ a ∈ U, fderiv ℝ u₀ a 1 + J (u₀ a) (fderiv ℝ u₀ a I) = 0)
    (hdu₀ : fderiv ℝ u₀ a₀ ≠ 0) (hU₁ : IsOpen U₁) (hb₀ : b₀ ∈ U₁) (hu₁ : ContDiffOn ℝ 1 u₁ U₁)
    (hCR₁ : ∀ ζ ∈ U₁, fderiv ℝ u₁ ζ 1 + J (u₁ ζ) (fderiv ℝ u₁ ζ I) = 0) {z ζ : ℕ → ℂ}
    (hz : Tendsto z atTop (𝓝 a₀)) (hζ : Tendsto ζ atTop (𝓝 b₀)) (hζb₀ : ∀ k, ζ k ≠ b₀)
    (hzζ : ∀ k, u₀ (z k) = u₁ (ζ k)) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ b₀ ∧ φ b₀ = a₀ ∧ u₁ =ᶠ[𝓝 b₀] u₀ ∘ φ := by
  refine exists_analyticAt_eventuallyEq_comp_of_frequently_mem_image hU hΩ ha₀ hu₀ hJ hu₀Ω hsq
    hCR₀ hdu₀ hU₁ hb₀ hu₁ hCR₁ fun S hS ↦ ?_
  have hζ' : Tendsto ζ atTop (𝓝[≠] b₀) := tendsto_nhdsWithin_iff.2 ⟨hζ, .of_forall hζb₀⟩
  exact hζ'.frequently ((hz.eventually hS).frequently.mono fun k hk ↦ ⟨z k, hk, hzζ k⟩)

end TauCeti
