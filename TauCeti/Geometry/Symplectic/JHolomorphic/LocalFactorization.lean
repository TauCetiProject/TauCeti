/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.JHolomorphic.AdaptedChart
import Mathlib.Analysis.Complex.Conformal
import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
import TauCeti.Analysis.Complex.CauchyRiemann.NearlyHolomorphic
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy

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
  (`TauCeti.exists_euclideanSpace_bijective_coprod`, in
  `TauCeti/Geometry/Symplectic/Complex/Module/Conjugacy.lean`).
* **The normal component vanishes.** In the chart, `u₁` becomes `(a, b)` and `b` satisfies
  `‖∂ₛb + i ∂ₜb‖ ≤ C ‖b‖ ‖∂ₜ(a, b)‖` (`TauCeti.norm_snd_add_I_smul_snd_le`). So `b` solves the
  linear equation `∂ₛb + i ∂ₜb + C' b = 0` for the bounded rank-one coefficient
  `C' = -(∂ₛb + i ∂ₜb) b* / ‖b‖²`, and by Carleman's similarity principle its zeros are isolated
  unless it vanishes identically. The coincidences are zeros of `b` accumulating at `0`, so
  `b = 0` near `0` (`TauCeti.eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le`, in
  `TauCeti/Analysis/Complex/CauchyRiemann/NearlyHolomorphic.lean`).
* **The tangential component is holomorphic.** The equation transported into the chart
  (`OpenPartialHomeomorph.fderiv_symm_comp_add_pullbackEnd_eq_zero`) holds for the structure
  read in the chart, which is `i` on the zero section. So `(a, 0)` solves the Cauchy–Riemann
  equation for `i`, its component `a` is holomorphic, and `u₁ = u₀ ∘ a`.

No Micallef–White normal form is used.

## Main results

* `TauCeti.exists_eqOn_comp_of_cauchyRiemann`: McDuff–Salamon's Lemma 2.4.3.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section 2.4, Lemma 2.4.3 and its proof.
-/

public noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff InnerProductSpace

namespace TauCeti

/-! ### Accumulating zeros of the normal component -/

section Normal

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N]

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
  obtain ⟨hM, hle⟩ := norm_fderiv_snd_add_I_smul_le_of_contDiffOn hΩ (A := fun w ↦ A (v w)) hv
    hCR hA
  exact eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le hΩ hΩc hv.snd hM hle hz₀ hfreq

end Normal

/-! ### The local factorization -/

section Factorization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {J : V → V →L[ℝ] V}

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
    e.fderiv_symm_comp_add_pullbackEnd_eq_zero (hrB hw).1.2
      ((hu₁.differentiableOn one_ne_zero w (hrB hw).1.1).differentiableAt
        (hU₁.mem_nhds (hrB hw).1.1))
      ((hc.differentiableOn (by norm_num)).differentiableAt
        (e.open_source.mem_nhds (e.map_target (hrB hw).1.2)))
      ((hcs.differentiableOn (by norm_num)).differentiableAt (e.open_target.mem_nhds (hrB hw).1.2))
      (hCR₁ w (hrB hw).1.1)
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
  · -- in the chart `v` solves the Cauchy–Riemann equation for `i`, so it is holomorphic
    have hCR := hCRv w hw
    rw [hvφ w hw, hstd _ (hsrc w hw)] at hCR
    simp only [smul_apply, ContinuousLinearMap.id_apply] at hCR
    refine (differentiableAt_complex_iff_differentiableAt_real.2
      ⟨(hvC.differentiableOn one_ne_zero w hw).differentiableAt (isOpen_ball.mem_nhds hw), ?_⟩
      ).fst.differentiableWithinAt
    rw [eq_neg_of_add_eq_zero_left hCR, smul_neg, smul_smul, I_mul_I, neg_one_smul, neg_neg]
  · rw [Function.comp_apply, ← he0, ← hvφ w hw]
    exact (e.right_inv (hrB hw).1.2).symm

end Factorization

end TauCeti
