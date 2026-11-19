/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.JHolomorphic.AdaptedChart
import Mathlib.Analysis.Complex.Conformal
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.InnerProductSpace.RankOne
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.RankOne

/-!
# Accumulating coincidences of pseudoholomorphic discs factor locally

Let `J : V → (V →L[ℝ] V)` be an almost complex structure of class `C²` on a finite-dimensional
real normed space, written in coordinates, and let `u₀, u₁ : ℂ → V` be `J`-holomorphic discs,
`∂ₛu + J(u) ∂ₜu = 0`, with `u₀ 0 = u₁ 0` and `du₀(0) ≠ 0`. If there are exact coincidences
`u₀ (z_ν) = u₁ (ζ_ν)` with `z_ν, ζ_ν → 0` and `ζ_ν ≠ 0`, then near `0` the second disc factors
through the first: `u₁ = u₀ ∘ φ` for a holomorphic `φ` with `φ 0 = 0`
(`TauCeti.exists_eqOn_comp_of_cauchyRiemann`). This is McDuff–Salamon's Lemma 2.4.3, the local
input to the factorization of a curve through a simple one. The second disc may be critical at
`0`: `u₀ (z) = (z, 0)` and `u₁ (ζ) = (ζ², 0)` factor through `φ (ζ) = ζ²`.

The proof works in the coordinates adapted to `u₀` of
`TauCeti.exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le`, in which `u₀` is the zero
section `a ↦ (a, 0)` and the structure read in the chart differs from `i` by at most a constant
times the normal coordinate.

* **A complex normal frame.** The structure `J(u₀ 0)` makes `V` a complex vector space in which
  `du₀(0)` spans a complex line; a complex frame of its orthogonal complement, read in a frame
  `ℂᵐ → V` turning `J(u₀ 0)` into `i`, is the frame `W` the adapted chart needs
  (`TauCeti.exists_euclideanSpace_bijective_coprod`).
* **The normal component vanishes.** In the chart, `u₁` becomes `(a, b)` and `b` satisfies
  `‖∂ₛb + i ∂ₜb‖ ≤ C ‖b‖ ‖∂ₜ(a, b)‖` (`TauCeti.norm_snd_add_I_smul_snd_le`). So `b` solves the
  linear equation `∂ₛb + i ∂ₜb + C' b = 0` for the bounded rank-one coefficient
  `C' = -(∂ₛb + i ∂ₜb) b* / ‖b‖²`, and by Carleman's similarity principle its zeros are isolated
  unless it vanishes identically. The coincidences are zeros of `b` accumulating at `0`, so
  `b = 0` near `0` (`TauCeti.eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le`).
* **The tangential component is holomorphic.** On the zero section the structure read in the
  chart is `i`, so the curve equation for `(a, 0)` says that `a` is holomorphic, and
  `u₁ = u₀ ∘ a`.

No Micallef–White normal form is used.

## Main results

* `TauCeti.exists_euclideanSpace_bijective_coprod`: complex normal frames along an immersed disc.
* `TauCeti.eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le`: a solution of
  `‖∂ₛb + i ∂ₜb‖ ≤ M ‖b‖`, `M` locally bounded above, whose zeros accumulate at a point of a
  connected domain vanishes on the domain.
* `TauCeti.exists_eqOn_comp_of_cauchyRiemann`: McDuff–Salamon's Lemma 2.4.3.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section 2.4, Lemma 2.4.3 and its proof.
-/

public noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff InnerProductSpace

namespace TauCeti

/-! ### Complex normal frames -/

section Frame

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Complex normal frames.** Let `A` be a complex structure on a finite-dimensional real normed
space `V`, `A² = -1`, and `D : ℂ → V` a nonzero real-linear map satisfying the Cauchy–Riemann
equation `D 1 + A (D i) = 0`. Then some real-linear `W : ℂⁿ → V` intertwines `i` with `A` and
spans a complement of the line `D (ℂ)`: the map `(α, w) ↦ D α + W w` is bijective. This is the
frame consumed by `TauCeti.exists_holomorphicAdaptedChart`, for `D` the derivative of a
pseudoholomorphic disc at an immersed point. -/
theorem exists_euclideanSpace_bijective_coprod {A : V →L[ℝ] V}
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) {D : ℂ →L[ℝ] V} (hD : D 1 + A (D I) = 0)
    (hD0 : D ≠ 0) :
    ∃ (n : ℕ) (W : EuclideanSpace ℂ (Fin n) →L[ℝ] V),
      (∀ w, A (W w) = W (I • w)) ∧ Function.Bijective (D.coprod W) := by
  obtain ⟨m, Ψ, hΨ⟩ := A.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul hA
  have hΨI (x : EuclideanSpace ℂ (Fin m)) : A (Ψ x) = Ψ (I • x) := by simpa using congr($hΨ x)
  have hA' (v : V) : A (A v) = -v := by simpa using congr($hA v)
  -- in the frame `Ψ`, the map `D` is `α ↦ α v`
  set v := Ψ.symm (D 1) with hv
  have hDI : D I = A (D 1) := by
    rw [eq_neg_of_add_eq_zero_left hD, map_neg, hA', neg_neg]
  have hDα (α : ℂ) : D α = Ψ (α • v) := by
    rw [← re_smul_add_im_smul, map_add, map_smul, map_smul, ← hΨI, hv,
      ContinuousLinearEquiv.apply_symm_apply, ← hDI]
    exact LinearMap.apply_eq_re_smul_one_add_im_smul_I (D : ℂ →ₗ[ℝ] V) α
  have hv0 : v ≠ 0 := fun h ↦ hD0 (ContinuousLinearMap.ext fun α ↦ by simp [hDα, h])
  -- the frame is an orthonormal frame of the orthogonal complement of `v`
  set K := (ℂ ∙ v)ᗮ
  let b := stdOrthonormalBasis ℂ K
  let ι : EuclideanSpace ℂ (Fin (Module.finrank ℂ K)) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    K.subtypeL ∘L (b.repr.symm : _ →L[ℂ] K)
  refine ⟨Module.finrank ℂ K, (Ψ : EuclideanSpace ℂ (Fin m) →L[ℝ] V) ∘L ι.restrictScalars ℝ,
    fun w ↦ by simp [hΨI], ?_⟩
  have hιK (w) : ι w ∈ K := (b.repr.symm w).2
  have hcoprod (p : ℂ × EuclideanSpace ℂ (Fin (Module.finrank ℂ K))) :
      D.coprod ((Ψ : EuclideanSpace ℂ (Fin m) →L[ℝ] V) ∘L ι.restrictScalars ℝ) p =
        Ψ (p.1 • v + ι p.2) := by
    simp [hDα]
  refine ⟨fun p q hpq ↦ ?_, fun y ↦ ?_⟩
  · -- injectivity: pair with `v`
    rw [hcoprod, hcoprod, Ψ.injective.eq_iff] at hpq
    have hin := congrArg (fun x ↦ ⟪v, x⟫_ℂ) hpq
    simp only [inner_add_right, inner_smul_right,
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hιK _), add_zero] at hin
    have h1 : p.1 = q.1 := mul_right_cancel₀ (inner_self_ne_zero.2 hv0) hin
    rw [h1, add_right_inj] at hpq
    exact Prod.ext h1 (b.repr.symm.injective (Subtype.ext hpq))
  · -- surjectivity: split `Ψ⁻¹ y` along `v` and its orthogonal complement
    set x := Ψ.symm y
    set α : ℂ := ⟪v, x⟫_ℂ / ⟪v, v⟫_ℂ
    have hxK : x - α • v ∈ K := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
        div_mul_cancel₀ _ (inner_self_ne_zero.2 hv0), sub_self]
    refine ⟨(α, b.repr ⟨x - α • v, hxK⟩), ?_⟩
    simp [ι, x, hDα]

end Frame

/-! ### Accumulating zeros of the normal component -/

section Normal

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N]

/-- **Accumulating zeros of a nearly holomorphic map.** Let `b : ℂ → N` be of class `C¹` on a
connected open set `Ω`, with values in a finite-dimensional complex inner product space, and
satisfy `‖∂ₛb + i ∂ₜb‖ ≤ M ‖b‖` on `Ω` for a function `M` locally bounded above. If the zeros of
`b` accumulate at a point of `Ω`, then `b` vanishes on `Ω`. In the proof of McDuff–Salamon's
Lemma 2.4.3, `b` is the normal component of a pseudoholomorphic disc in coordinates adapted to
another one. -/
theorem eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {b : ℂ → N} {M : ℂ → ℝ} (hb : ContDiffOn ℝ 1 b Ω)
    (hM : ∀ z ∈ Ω, ∃ K, ∀ᶠ w in 𝓝 z, M w ≤ K)
    (hineq : ∀ z ∈ Ω, ‖fderiv ℝ b z 1 + I • fderiv ℝ b z I‖ ≤ M z * ‖b z‖) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (hfreq : ∃ᶠ z in 𝓝[≠] z₀, b z = 0) : EqOn b 0 Ω := by
  -- the defect `g = -(∂ₛb + i ∂ₜb)` is absorbed by the rank-one coefficient `C' = g b* / ‖b‖²`
  set g : ℂ → N := fun z ↦ -(fderiv ℝ b z 1 + I • fderiv ℝ b z I) with hg
  set C : ℂ → N →L[ℝ] N := fun z ↦ (rankOneDivNormSq ℂ (g z) (b z)).restrictScalars ℝ with hC
  have hDb : ContinuousOn (fderiv ℝ b) Ω := hb.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hgc : ContinuousOn g Ω :=
    ((hDb.clm_apply continuousOn_const).add
      ((hDb.clm_apply continuousOn_const).const_smul I)).neg
  have hCb (z : ℂ) (hz : z ∈ Ω) : C z (b z) = g z := by
    by_cases h0 : b z = 0
    · have h := hineq z hz
      rw [h0, norm_zero, mul_zero, norm_le_zero_iff] at h
      have hg0 : g z = 0 := by simp only [hg, h, neg_zero]
      simp [hC, h0, hg0]
    · simp only [hC, ContinuousLinearMap.coe_restrictScalars', rankOneDivNormSq_apply_self _ h0]
  have hne := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn (C := C) hΩ hΩc hb
    ((ContinuousLinearMap.restrictScalarsL ℂ _ _ ℝ ℂ).continuous.comp_aestronglyMeasurable
      ((hgc.aestronglyMeasurable hΩ.measurableSet).rankOneDivNormSq
        (hb.continuousOn.aestronglyMeasurable hΩ.measurableSet)))
    (fun z hz ↦ ?_) (fun z hz ↦ by rw [hCb z hz, hg, add_neg_cancel])
  · -- the zeros accumulate at `z₀`, so the codiscreteness alternative fails
    by_contra hb0
    obtain ⟨z, hz, hbz⟩ : ∃ z ∈ Ω, b z ≠ 0 := by
      by_contra h
      push Not at h
      exact hb0 fun z hz ↦ h z hz
    have hdisj : ∀ᶠ w in 𝓝[≠] z₀, w ∉ Ω \ {w | b w ≠ 0} :=
      disjoint_principal_right.1 (mem_codiscreteWithin.1 (hne ⟨z, hz, hbz⟩) z₀ hz₀)
    have hΩz : ∀ᶠ w in 𝓝[≠] z₀, w ∈ Ω := nhdsWithin_le_nhds (hΩ.mem_nhds hz₀)
    obtain ⟨w, hbw, hdis, hwΩ⟩ := (hfreq.and_eventually (hdisj.and hΩz)).exists
    exact hdis ⟨hwΩ, fun h ↦ h hbw⟩
  · -- the coefficient is locally bounded, by `max K 0`
    obtain ⟨K, hK⟩ := hM z hz
    refine ⟨max K 0, ?_⟩
    filter_upwards [hK, hΩ.mem_nhds hz] with w hwK hwΩ
    rw [hC, ContinuousLinearMap.norm_restrictScalars, norm_rankOneDivNormSq]
    by_cases h0 : b w = 0
    · simp [h0]
    refine div_le_of_le_mul₀ (norm_nonneg _) (le_max_right _ _) ?_
    rw [hg, norm_neg]
    exact (hineq w hwΩ).trans (mul_le_mul_of_nonneg_right (le_max_of_le_left hwK) (norm_nonneg _))

/-- **The normal component of a disc in adapted coordinates.** In coordinates `ℂ × N`, let `v` be
a `C¹` solution of `∂ₛv + A(v) ∂ₜv = 0` on a connected open set `Ω`, for a structure `A` within
`C ‖p.2‖` of `i` along `v`. If the zeros of the normal component `(v ·).2` accumulate at a point of
`Ω`, the normal component vanishes on `Ω`. -/
private theorem eqOn_zero_snd_of_cauchyRiemann {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {v : ℂ → ℂ × N} {A : ℂ × N → ℂ × N →L[ℝ] ℂ × N} {C : ℝ}
    (hv : ContDiffOn ℝ 1 v Ω) (hCR : ∀ w ∈ Ω, fderiv ℝ v w 1 + A (v w) (fderiv ℝ v w I) = 0)
    (hA : ∀ w ∈ Ω, ‖A (v w) - I • ContinuousLinearMap.id ℝ (ℂ × N)‖ ≤ C * ‖(v w).2‖)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hfreq : ∃ᶠ w in 𝓝[≠] z₀, (v w).2 = 0) :
    EqOn (fun w ↦ (v w).2) 0 Ω := by
  refine eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le hΩ hΩc hv.snd
    (M := fun w ↦ C * ‖fderiv ℝ v w I‖) (fun w hw ↦ ?_) (fun w hw ↦ ?_) hz₀ hfreq
  · -- `M` is continuous, hence locally bounded above
    have hcont : ContinuousAt (fun w ↦ C * ‖fderiv ℝ v w I‖) w :=
      continuousAt_const.mul ((((hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
        continuousOn_const).continuousAt (hΩ.mem_nhds hw)).norm)
    exact ⟨_, hcont.eventually_mem (Iic_mem_nhds (lt_add_one _))⟩
  · rw [((hv.differentiableOn one_ne_zero w hw).differentiableAt
      (hΩ.mem_nhds hw)).hasFDerivAt.snd.fderiv]
    calc ‖(fderiv ℝ v w 1).2 + I • (fderiv ℝ v w I).2‖
        ≤ C * ‖(v w).2‖ * ‖fderiv ℝ v w I‖ := norm_snd_add_I_smul_snd_le (hA w hw) (hCR w hw)
      _ = C * ‖fderiv ℝ v w I‖ * ‖(v w).2‖ := by ring

end Normal

/-! ### The local factorization -/

section Factorization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {J : V → V →L[ℝ] V}

/-- **The Cauchy–Riemann equation in a chart.** If `u` solves `∂ₛu + J(u) ∂ₜu = 0` at `ζ` and
`u ζ` lies in the target of a chart `e` differentiable there, then `e⁻¹ ∘ u` solves the equation
for the structure read in the chart, `e.pullbackEnd J`. -/
private theorem cauchyRiemann_symm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : OpenPartialHomeomorph E V} {u : ℂ → V} {ζ : ℂ} (hu : DifferentiableAt ℝ u ζ)
    (ht : u ζ ∈ e.target) (he : DifferentiableAt ℝ e (e.symm (u ζ)))
    (hes : DifferentiableAt ℝ e.symm (u ζ))
    (hCR : fderiv ℝ u ζ 1 + J (u ζ) (fderiv ℝ u ζ I) = 0) :
    fderiv ℝ (fun w ↦ e.symm (u w)) ζ 1 +
      e.pullbackEnd J (e.symm (u ζ)) (fderiv ℝ (fun w ↦ e.symm (u w)) ζ I) = 0 := by
  have hp := e.map_target ht
  have hep : e (e.symm (u ζ)) = u ζ := e.right_inv ht
  have hD : fderiv ℝ (fun w ↦ e.symm (u w)) ζ = (fderiv ℝ e.symm (u ζ)).comp (fderiv ℝ u ζ) :=
    (hes.hasFDerivAt.comp ζ hu.hasFDerivAt).fderiv
  have hes' : DifferentiableAt ℝ e.symm (e (e.symm (u ζ))) := by rwa [hep]
  have hinv (v : V) : fderiv ℝ e (e.symm (u ζ)) (fderiv ℝ e.symm (u ζ) v) = v := by
    simpa only [hep] using e.fderiv_apply_fderiv_symm_apply_of_mem_source hp he hes' v
  rw [OpenPartialHomeomorph.pullbackEnd_apply, hD, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hep, hinv, ← map_add, hCR, map_zero]

/-- **The tangential component is holomorphic.** If a disc `v` in `ℂ × N` solves the
Cauchy–Riemann equation for the standard structure `i` at `w`, its first component is complex
differentiable at `w`. -/
private theorem differentiableAt_fst_of_cauchyRiemann {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℂ N] {v : ℂ → ℂ × N} {w : ℂ} (hv : DifferentiableAt ℝ v w)
    (hCR : fderiv ℝ v w 1 + (I • ContinuousLinearMap.id ℝ (ℂ × N)) (fderiv ℝ v w I) = 0) :
    DifferentiableAt ℂ (fun w ↦ (v w).1) w := by
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨hv.fst, ?_⟩
  have h1 := congrArg Prod.fst hCR
  simp only [Prod.fst_add, smul_apply, ContinuousLinearMap.id_apply, Prod.smul_fst, smul_eq_mul,
    Prod.fst_zero] at h1
  rw [hv.hasFDerivAt.fst.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  linear_combination -I * h1 + (fderiv ℝ v w I).1 * I_sq

variable [FiniteDimensional ℝ V]

/-- **Accumulating coincidences factor** (McDuff–Salamon, Lemma 2.4.3). Let `J` be of class `C²`
on an open set `Ω ⊆ V`, let `u₀` be of class `C²` on an open `U₀ ∋ 0` with values in `Ω` and
`u₁` of class `C¹` on an open `U₁ ∋ 0`, both solving `∂ₛu + J(u) ∂ₜu = 0`, with `J(u₀)² = -1`.
Suppose `du₀(0) ≠ 0` and `u₀ (z ν) = u₁ (ζ ν)` for sequences `z ν, ζ ν → 0` with `ζ ν ≠ 0`.
Then near `0` the disc `u₁` is `u₀ ∘ φ` for a holomorphic `φ` with `φ 0 = 0`, taking values in
`U₀`. The map `φ` may be critical at `0`. -/
theorem exists_eqOn_comp_of_cauchyRiemann {Ω : Set V} {U₀ U₁ : Set ℂ} {u₀ u₁ : ℂ → V}
    (hΩ : IsOpen Ω) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (h0₀ : 0 ∈ U₀) (h0₁ : 0 ∈ U₁)
    (hJ : ContDiffOn ℝ 2 J Ω) (hu₀ : ContDiffOn ℝ 2 u₀ U₀) (hu₀Ω : MapsTo u₀ U₀ Ω)
    (hu₁ : ContDiffOn ℝ 1 u₁ U₁) (hsq : ∀ z ∈ U₀, ∀ v, J (u₀ z) (J (u₀ z) v) = -v)
    (hCR₀ : ∀ z ∈ U₀, fderiv ℝ u₀ z 1 + J (u₀ z) (fderiv ℝ u₀ z I) = 0)
    (hCR₁ : ∀ ζ ∈ U₁, fderiv ℝ u₁ ζ 1 + J (u₁ ζ) (fderiv ℝ u₁ ζ I) = 0)
    (hdu₀ : fderiv ℝ u₀ 0 ≠ 0) {z ζ : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 0))
    (hζ : Tendsto ζ atTop (𝓝 0)) (hζ0 : ∀ ν, ζ ν ≠ 0) (heq : ∀ ν, u₀ (z ν) = u₁ (ζ ν)) :
    ∃ ε > 0, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball 0 ε) ∧ φ 0 = 0 ∧
      MapsTo φ (ball 0 ε) U₀ ∧ EqOn u₁ (u₀ ∘ φ) (ball 0 ε) := by
  have := FiniteDimensional.completeSpace ℝ V
  have hu₁c : ContinuousAt u₁ 0 := hu₁.continuousOn.continuousAt (hU₁.mem_nhds h0₁)
  have h01 : u₀ 0 = u₁ 0 := tendsto_nhds_unique
    ((hu₀.continuousOn.continuousAt (hU₀.mem_nhds h0₀)).tendsto.comp hz)
    ((hu₁c.tendsto.comp hζ).congr fun ν ↦ (heq ν).symm)
  -- the coordinates adapted to `u₀`, with the normal control of the structure
  obtain ⟨n, W, hW, hbij⟩ := exists_euclideanSpace_bijective_coprod
    (ContinuousLinearMap.ext fun v ↦ by simpa using hsq 0 h0₀ v) (hCR₀ 0 h0₀) hdu₀
  obtain ⟨e, he, h₀, hsU, -, hc, hcs, hstd, C, hC⟩ :=
    exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le hU₀ hΩ h0₀ le_rfl hu₀ hJ hu₀Ω hsq
      hCR₀ hW hbij
  have he0 (a : ℂ) : e (a, 0) = u₀ a := by rw [he, holomorphicNormalExtension_zero]
  have ht : u₁ 0 ∈ e.target := h01 ▸ he0 0 ▸ e.map_source h₀
  -- `u₁` in the chart, on a disc where the normal control applies
  set v : ℂ → ℂ × EuclideanSpace ℂ (Fin n) := fun w ↦ e.symm (u₁ w) with hv
  have hv0 : v 0 = (0, 0) := by simp only [hv, ← h01, ← he0 0, e.left_inv h₀]
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem (hU₁.mem_nhds h0₁)
    (hu₁c.preimage_mem_nhds (e.open_target.mem_nhds ht)))
    (((e.continuousAt_symm ht).comp hu₁c).preimage_mem_nhds (hv0 ▸ hC)))
  have hvC : ContDiffOn ℝ 1 v (ball 0 r) :=
    (hcs.of_le (by norm_num)).comp (hu₁.mono fun w hw ↦ (hrB hw).1.1) fun w hw ↦ (hrB hw).1.2
  have hCRv (w) (hw : w ∈ ball (0 : ℂ) r) :
      fderiv ℝ v w 1 + e.pullbackEnd J (v w) (fderiv ℝ v w I) = 0 :=
    cauchyRiemann_symm_comp ((hu₁.differentiableOn one_ne_zero w (hrB hw).1.1).differentiableAt
        (hU₁.mem_nhds (hrB hw).1.1)) (hrB hw).1.2
      ((hc.differentiableOn (by norm_num)).differentiableAt
        (e.open_source.mem_nhds (e.map_target (hrB hw).1.2)))
      ((hcs.differentiableOn (by norm_num)).differentiableAt
        (e.open_target.mem_nhds (hrB hw).1.2)) (hCR₁ w (hrB hw).1.1)
  -- the coincidences are zeros of the normal component accumulating at `0`, so it vanishes
  have hev : ∀ᶠ ν in atTop, (v (ζ ν)).2 = 0 := by
    filter_upwards [(hz.prodMk_nhds (tendsto_const_nhds (x := (0 : EuclideanSpace ℂ (Fin n))))
      ).eventually (e.open_source.mem_nhds h₀)] with ν hν
    simp only [hv, ← heq ν, ← he0, e.left_inv hν]
  have hb0 := eqOn_zero_snd_of_cauchyRiemann isOpen_ball (convex_ball _ _).isPreconnected hvC
    hCRv (fun w hw ↦ (hrB hw).2) (mem_ball_self hr)
    ((tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hζ
      (Eventually.of_forall hζ0)).frequently hev.frequently)
  -- so `u₁ = u₀ ∘ a` for the tangential component `a`, which is holomorphic
  have hvφ (w) (hw : w ∈ ball (0 : ℂ) r) : v w = ((v w).1, 0) := Prod.ext rfl (hb0 hw)
  have hsrc (w) (hw : w ∈ ball (0 : ℂ) r) :
      ((v w).1, (0 : EuclideanSpace ℂ (Fin n))) ∈ e.source :=
    hvφ w hw ▸ e.map_target (hrB hw).1.2
  refine ⟨r, hr, fun w ↦ (v w).1, fun w hw ↦ ?_, by simp [hv0], fun w hw ↦ (hsU (hsrc w hw)).1,
    fun w hw ↦ ?_⟩
  · have hCR := hCRv w hw
    rw [hvφ w hw, hstd _ (hsrc w hw)] at hCR
    exact (differentiableAt_fst_of_cauchyRiemann
      ((hvC.differentiableOn one_ne_zero w hw).differentiableAt (isOpen_ball.mem_nhds hw))
      hCR).differentiableWithinAt
  · rw [Function.comp_apply, ← he0, ← hvφ w hw]
    exact (e.right_inv (hrB hw).1.2).symm

end Factorization

end TauCeti
