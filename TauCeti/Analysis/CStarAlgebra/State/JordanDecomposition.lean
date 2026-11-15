/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.RCLike.Extend
import TauCeti.Analysis.CStarAlgebra.State.Extension
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach

/-!
# Grothendieck–Jordan decomposition of continuous linear functionals on C⋆-algebras

Every self-adjoint continuous linear functional `ψ : A →L[ℂ] ℂ` (`∀ a, ψ (star a) = star (ψ a)`) on
a possibly nonunital C⋆-algebra `A` decomposes as a difference

`ψ = (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ)`

of two positive continuous linear functionals `φ₁, φ₂ : A →P[ℂ] ℂ` with exact norm additivity
`‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ = ‖ψ‖`
(`ContinuousLinearMap.exists_eq_sub_positiveContinuousLinearMap`). Splitting an arbitrary functional
into its self-adjoint real and imaginary parts expresses every `ψ : A →L[ℂ] ℂ` as a linear
combination `(φ₁ - φ₂) + I • (φ₃ - φ₄)` of four positive functionals of norm at most `‖ψ‖`
(`ContinuousLinearMap.exists_eq_linearCombination_positiveContinuousLinearMap`). Consequently, a net
or filter in `A` converges weakly to `0` under all continuous complex- or real-linear functionals as
soon as it converges to `0` under every positive continuous linear functional
(`ContinuousLinearMap.tendsto_zero_of_forall_positiveContinuousLinearMap`,
`ContinuousLinearMap.tendsto_real_zero_of_forall_positiveContinuousLinearMap`).

## Proof strategy

We avoid the enveloping von Neumann algebra `A**` and prove the decomposition directly by weak-*
Hahn–Banach separation on the unitization `B = A⁺¹`:

1. In a nontrivial unital C⋆-algebra `B`, the set
   `K = {t • ω₁ - (1 - t) • ω₂ | t ∈ [0, 1], ω₁, ω₂ ∈ stateSpace B} ⊆ WeakDual ℂ B`
   is convex and weak-* compact (hence weak-* closed), being the continuous image of
   `[0, 1] × stateSpace B × stateSpace B`.
2. If a contractive self-adjoint functional `ψ₀` were outside `K`, geometric Hahn–Banach together
   with `WeakDual.exists_forall_apply_eq_apply` would produce a self-adjoint `x : B` with
   `|(ω x).re| < u < (ψ₀ x).re ≤ ‖x‖` for every `ω ∈ stateSpace B`. Choosing a spectral value
   `μ ∈ spectrum ℂ x` of modulus `‖x‖`, realizing `μ` as a character on `StarAlgebra.elemental ℂ x`,
   and extending that state via `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq` yields
   `|(ω x).re| = ‖x‖`, a contradiction.
3. For possibly nonunital `A`, extending `ψ : A →L[ℂ] ℂ` isometrically to `A⁺¹` via Hahn–Banach,
   symmetrizing `(z ↦ 2⁻¹ • (Ψ z + star (Ψ (star z))))`, decomposing on `A⁺¹`, and restricting back
   along `Unitization.inrNonUnitalStarAlgHom ℂ A` preserves exact norm additivity.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.6.3.4.
* Gert K. Pedersen, *C*-Algebras and their Automorphism Groups*, Theorem 3.2.5.
* Shôichirô Sakai, *C*-Algebras and W*-Algebras*, Proposition 1.14.3.
-/

public section

open Filter Set Topology Unitization WeakDual
open scoped CStarAlgebra ComplexOrder

namespace ContinuousLinearMap

section StarDual

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [InvolutiveStar 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [StarAddMonoid E] [NormedStarGroup E]
  [StarModule 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [StarAddMonoid F] [NormedStarGroup F]
  [StarModule 𝕜 F]

/-- Conjugate-adjoint map `(starDual ψ) x = star (ψ (star x))` of a continuous `𝕜`-linear map
between normed star `𝕜`-modules, bundled as a continuous `𝕜`-linear map of the same operator norm.
-/
def starDual (ψ : E →L[𝕜] F) : E →L[𝕜] F where
  toFun x := star (ψ (star x))
  map_add' x y := by simp
  map_smul' c x := by simp
  cont := continuous_star.comp (ψ.continuous.comp continuous_star)

/-- Evaluation of `ContinuousLinearMap.starDual`. -/
@[simp]
theorem starDual_apply (ψ : E →L[𝕜] F) (x : E) : ψ.starDual x = star (ψ (star x)) :=
  (rfl)

/-- `ContinuousLinearMap.starDual` is an involution. -/
@[simp]
theorem starDual_starDual (ψ : E →L[𝕜] F) : ψ.starDual.starDual = ψ := by
  ext x
  simp

/-- `ContinuousLinearMap.starDual` preserves the operator norm. -/
@[simp]
theorem norm_starDual (ψ : E →L[𝕜] F) : ‖ψ.starDual‖ = ‖ψ‖ := by
  have hle (φ : E →L[𝕜] F) : ‖φ.starDual‖ ≤ ‖φ‖ :=
    opNorm_le_bound _ (norm_nonneg φ) fun x => by simpa using φ.le_opNorm (star x)
  exact le_antisymm (hle ψ) (by simpa using hle ψ.starDual)

end StarDual

section UnitalHelper

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- In a nontrivial unital C⋆-algebra, every self-adjoint element `x` admits a state `ω` attaining
`|(ω x).re| = ‖x‖`: pick a spectral value of modulus `‖x‖` on `StarAlgebra.elemental ℂ x`, view it
as a character, and extend that state to `B`. -/
private theorem exists_mem_stateSpace_abs_re_eq_norm [Nontrivial B] {x : B}
    (hx : IsSelfAdjoint x) : ∃ ω ∈ TauCeti.stateSpace B, |(ω x).re| = ‖x‖ := by
  let S : StarSubalgebra ℂ B := StarAlgebra.elemental ℂ x
  have : IsClosed (S : Set B) := StarAlgebra.elemental.isClosed ℂ x
  have : IsStarNormal x := hx.isStarNormal
  obtain ⟨μ, hμ_spec, hμ_norm⟩ := spectrum.exists_nnNorm_eq_spectralRadius (a := x)
  have hμ_abs : ‖μ‖ = ‖x‖ := by
    have := congrArg (ENNReal.toReal ∘ (↑)) hμ_norm
    simpa [Function.comp_def, hx.toReal_spectralRadius_complex_eq_norm] using this
  have hμ_re : (μ.re : ℂ) = μ := (hx.mem_spectrum_eq_re hμ_spec).symm
  let xS : S := ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩
  have hμS : μ ∈ spectrum ℂ xS := by rwa [StarSubalgebra.spectrum_eq]
  obtain ⟨χ, hχ⟩ := (WeakDual.CharacterSpace.mem_spectrum_iff_exists (a := xS) (z := μ)).1 hμS
  have hχ_state : TauCeti.pullbackFunctional S χ
      (StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ)) ∈ TauCeti.stateSpace S := by
    refine TauCeti.mapsTo_pullbackFunctional_stateSpace χ ?_
    rw [TauCeti.stateSpace_complex]
    exact mem_singleton _
  obtain ⟨ω, hω, hω_ext⟩ := StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq S hχ_state
  refine ⟨ω, hω, ?_⟩
  have hωx : ω x = μ := (hω_ext xS).trans (by simpa [TauCeti.pullbackFunctional_apply] using hχ)
  rw [hωx, ← hμ_re, Complex.ofReal_re, ← Real.norm_eq_abs, ← Complex.norm_real, hμ_re, hμ_abs]

/-- On a nontrivial unital C⋆-algebra, every contractive self-adjoint functional belongs to the
weak-* compact convex set `{t • ω₁ - (1 - t) • ω₂ | t ∈ [0, 1], ω₁, ω₂ ∈ stateSpace B}`. -/
private theorem exists_mem_stateSpace_sub_of_norm_le_one [Nontrivial B] {ψ : B →L[ℂ] ℂ}
    (hψ : ∀ b, ψ (star b) = star (ψ b)) (hnorm : ‖ψ‖ ≤ 1) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ ω₁ ∈ TauCeti.stateSpace B, ∃ ω₂ ∈ TauCeti.stateSpace B,
      ψ = t • toStrongDual ω₁ - (1 - t) • toStrongDual ω₂ := by
  let S := TauCeti.stateSpace B
  obtain ⟨ω₀, hω₀⟩ := TauCeti.stateSpace_nonempty (A := B)
  let Φ : ℝ × WeakDual ℂ B × WeakDual ℂ B → WeakDual ℂ B :=
    fun p => p.1 • p.2.1 - (1 - p.1) • p.2.2
  let K : Set (WeakDual ℂ B) := Φ '' (Icc (0 : ℝ) 1 ×ˢ (S ×ˢ S))
  have hK_compact : IsCompact K :=
    (isCompact_Icc.prod (TauCeti.isCompact_stateSpace.prod TauCeti.isCompact_stateSpace)).image
      (by fun_prop)
  have hK_conv : Convex ℝ K := by
    rintro _ ⟨⟨t₁, ω₁, ω₂⟩, ⟨⟨ht₁₀, ht₁₁⟩, hω₁, hω₂⟩, rfl⟩
      _ ⟨⟨t₂, η₁, η₂⟩, ⟨⟨ht₂₀, ht₂₁⟩, hη₁, hη₂⟩, rfl⟩ a b ha hb hab
    dsimp only at ht₁₀ ht₁₁ hω₁ hω₂ ht₂₀ ht₂₁ hη₁ hη₂ ⊢
    let t := a * t₁ + b * t₂
    have ht₀ : 0 ≤ t := by positivity
    have h1t : 1 - t = a * (1 - t₁) + b * (1 - t₂) := by dsimp [t]; linarith
    have ht₁' : t ≤ 1 := by linarith [show 0 ≤ 1 - t by rw [h1t]; positivity]
    obtain ⟨ξ₁, hξ₁, hξ₁_eq⟩ : ∃ ξ₁ ∈ S, t • ξ₁ = (a * t₁) • ω₁ + (b * t₂) • η₁ := by
      rcases ht₀.eq_or_lt with h0 | hpos
      · have ht0 : t = 0 := h0.symm
        have hat : a * t₁ = 0 := by nlinarith
        have hbt : b * t₂ = 0 := by nlinarith
        refine ⟨ω₀, hω₀, DFunLike.ext _ _ fun x => ?_⟩
        simp [ht0, hat, hbt]
      · refine ⟨(a * t₁ / t) • ω₁ + (b * t₂ / t) • η₁,
          TauCeti.convex_stateSpace hω₁ hη₁ (by positivity) (by positivity) ?_,
          DFunLike.ext _ _ fun x => ?_⟩
        · rw [← add_div, div_eq_one_iff_eq hpos.ne']
        · have htℂ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
          simp only [add_apply, smul_apply, Complex.real_smul, Complex.ofReal_div,
            Complex.ofReal_mul]
          field_simp [htℂ]
    obtain ⟨ξ₂, hξ₂, hξ₂_eq⟩ :
        ∃ ξ₂ ∈ S, (1 - t) • ξ₂ = (a * (1 - t₁)) • ω₂ + (b * (1 - t₂)) • η₂ := by
      have h1t₀ : 0 ≤ 1 - t := sub_nonneg.2 ht₁'
      rcases h1t₀.eq_or_lt with h0 | hpos
      · have ht1 : 1 - t = 0 := h0.symm
        have hat : a * (1 - t₁) = 0 := by nlinarith [h1t]
        have hbt : b * (1 - t₂) = 0 := by nlinarith [h1t]
        refine ⟨ω₀, hω₀, DFunLike.ext _ _ fun x => ?_⟩
        simp [ht1, hat, hbt]
      · refine ⟨(a * (1 - t₁) / (1 - t)) • ω₂ + (b * (1 - t₂) / (1 - t)) • η₂,
          TauCeti.convex_stateSpace hω₂ hη₂ (by positivity) (by positivity) ?_,
          DFunLike.ext _ _ fun x => ?_⟩
        · rw [← add_div, ← h1t, div_self hpos.ne']
        · have htℂ : ((1 - t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
          simp only [add_apply, smul_apply, Complex.real_smul, Complex.ofReal_div,
            Complex.ofReal_mul]
          field_simp [htℂ]
    refine ⟨(t, ξ₁, ξ₂), ⟨⟨ht₀, ht₁'⟩, hξ₁, hξ₂⟩, DFunLike.ext _ _ fun x => ?_⟩
    have hsub_apply (u v : WeakDual ℂ B) : (u - v) x = u x - v x := rfl
    dsimp only [Φ]
    rw [hξ₁_eq, hξ₂_eq]
    simp only [hsub_apply, add_apply, smul_apply, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hmem : StrongDual.toWeakDual ψ ∈ K := by
    by_contra hnot
    let K' : Set (WeakBilin (topDualPairing ℂ B)) := K
    have hK'_conv : Convex ℝ K' := fun _ hx _ hy _ _ ha hb hab => hK_conv hx hy ha hb hab
    have hK'_closed : IsClosed K' := hK_compact.isClosed
    have hnot' : (StrongDual.toWeakDual ψ : WeakBilin (topDualPairing ℂ B)) ∉ K' := hnot
    obtain ⟨l, u, hlK, hlψ⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hK'_conv hK'_closed hnot'
    obtain ⟨z, rfl⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ B) l
    have heval (φ : WeakDual ℂ B) :
        (WeakBilin.eval (topDualPairing ℂ B) z) (φ : WeakBilin (topDualPairing ℂ B)) = φ z := rfl
    let x : B := (2⁻¹ : ℝ) • (z + star z)
    have hx_sa : IsSelfAdjoint x := by
      rw [IsSelfAdjoint]
      simp [x, star_smul, star_add, add_comm]
    have hstate_star (ω : WeakDual ℂ B) (hω : ω ∈ S) : (ω x).re = (ω z).re := by
      let p : B →ₚ[ℂ] ℂ := .mk₀ (toStrongDual ω : B →ₗ[ℂ] ℂ) fun _ =>
        TauCeti.map_nonneg_of_mem_stateSpace hω
      have hp : ω (star z) = star (ω z) := map_star p z
      have hsmul (b : B) : ω ((2⁻¹ : ℝ) • b) = (2⁻¹ : ℝ) • ω b :=
        (toStrongDual ω).map_smul_of_tower (2⁻¹ : ℝ) b
      simp only [x, smul_add, map_add, hsmul, hp, Complex.real_smul, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re]
      ring
    have hψx : (ψ x).re = (ψ z).re := by
      simp [x, hψ z]
      ring
    obtain ⟨ω, hω, hω_abs⟩ := exists_mem_stateSpace_abs_re_eq_norm hx_sa
    have hpos : (ω x).re < u := by
      have hωK : (ω : WeakBilin (topDualPairing ℂ B)) ∈ K' :=
        ⟨(1, ω, ω), ⟨⟨zero_le_one, le_rfl⟩, hω, hω⟩, DFunLike.ext _ _ fun b => by
          change ((1 : ℝ) • ω b - (1 - (1 : ℝ)) • ω b) = ω b
          simp⟩
      have h1 := hlK ω hωK
      rw [heval ω, RCLike.re_eq_complex_re] at h1
      exact (hstate_star ω hω).trans_lt h1
    have hneg : -(ω x).re < u := by
      have hωK : (-ω : WeakBilin (topDualPairing ℂ B)) ∈ K' :=
        ⟨(0, ω, ω), ⟨⟨le_rfl, zero_le_one⟩, hω, hω⟩, DFunLike.ext _ _ fun b => by
          change ((0 : ℝ) • ω b - (1 - (0 : ℝ)) • ω b) = -ω b
          simp⟩
      have h1 := hlK (-ω) hωK
      rw [heval (-ω), RCLike.re_eq_complex_re] at h1
      have hneg_apply : (-ω : WeakDual ℂ B) z = -ω z := rfl
      rw [hneg_apply, Complex.neg_re, ← hstate_star ω hω] at h1
      exact h1
    have hlt_u : ‖x‖ < u := by
      rw [← hω_abs]
      exact abs_lt.2 ⟨by linarith, hpos⟩
    have hu_le : u < ‖x‖ := by
      have h1 := hlψ
      rw [heval (StrongDual.toWeakDual ψ), RCLike.re_eq_complex_re] at h1
      have hpsi_apply : (StrongDual.toWeakDual ψ : WeakDual ℂ B) z = ψ z := rfl
      rw [hpsi_apply, ← hψx] at h1
      refine h1.trans_le ((Complex.re_le_norm (ψ x)).trans ?_)
      exact (ψ.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) hnorm)
    exact (hlt_u.trans hu_le).false
  obtain ⟨⟨t, ω₁, ω₂⟩, ⟨ht, hω₁, hω₂⟩, hEq⟩ := hmem
  refine ⟨t, ht, ω₁, hω₁, ω₂, hω₂, ?_⟩
  ext b
  exact DFunLike.congr_fun hEq.symm b

end UnitalHelper

section Decomposition

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Grothendieck–Jordan decomposition for self-adjoint functionals on a C⋆-algebra.**
Every continuous linear functional `ψ : A →L[ℂ] ℂ` satisfying `∀ a, ψ (star a) = star (ψ a)` on a
possibly nonunital C⋆-algebra `A` decomposes as the difference `φ₁ - φ₂` of two positive continuous
linear functionals `φ₁, φ₂ : A →P[ℂ] ℂ` with `‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ = ‖ψ‖`. -/
theorem exists_eq_sub_positiveContinuousLinearMap {ψ : A →L[ℂ] ℂ}
    (hψ : ∀ a, ψ (star a) = star (ψ a)) :
    ∃ φ₁ φ₂ : A →P[ℂ] ℂ, ψ = (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ) ∧
      ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ = ‖ψ‖ := by
  by_cases h0 : ψ = 0
  · refine ⟨0, 0, by simp [h0], by simp [h0]⟩
  have hnorm_pos : 0 < ‖ψ‖ := norm_pos_iff.2 h0
  let ι : A →ₗᵢ[ℂ] A⁺¹ :=
    { toLinearMap := (Unitization.inrNonUnitalStarAlgHom ℂ A : A →ₗ[ℂ] A⁺¹)
      norm_map' := fun a => Unitization.norm_inr a }
  obtain ⟨Ψ₀, hΨ₀_ext, hΨ₀_norm⟩ := ι.exists_extension_norm_eq ψ
  let Ψ : A⁺¹ →L[ℂ] ℂ := (2⁻¹ : ℝ) • (Ψ₀ + Ψ₀.starDual)
  have hΨ_ext (a : A) : Ψ (a : A⁺¹) = ψ a := by
    have h1 : Ψ₀ (a : A⁺¹) = ψ a := DFunLike.congr_fun hΨ₀_ext a
    have h2 : Ψ₀ (star (a : A⁺¹)) = ψ (star a) := by
      rw [← Unitization.inr_star]
      exact DFunLike.congr_fun hΨ₀_ext (star a)
    simp only [Ψ, smul_apply, add_apply, starDual_apply, h1, h2, hψ a, star_star]
    rw [← two_smul ℝ (ψ a), ← mul_smul]
    norm_num
  have hΨ_sa (z : A⁺¹) : Ψ (star z) = star (Ψ z) := by
    simp [Ψ, Complex.real_smul, star_add, add_comm]
  have hΨ_norm : ‖Ψ‖ ≤ ‖ψ‖ := by
    calc
      ‖Ψ‖ = (2⁻¹ : ℝ) * ‖Ψ₀ + Ψ₀.starDual‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ (2⁻¹ : ℝ) * (‖Ψ₀‖ + ‖Ψ₀.starDual‖) := by gcongr; exact norm_add_le _ _
      _ = ‖ψ‖ := by rw [norm_starDual, hΨ₀_norm]; ring
  let Ψ₁ : A⁺¹ →L[ℂ] ℂ := ‖ψ‖⁻¹ • Ψ
  have hΨ₁_sa (z : A⁺¹) : Ψ₁ (star z) = star (Ψ₁ z) := by
    simp [Ψ₁, Complex.real_smul, hΨ_sa z]
  have hΨ₁_norm : ‖Ψ₁‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hnorm_pos.le)]
    exact (inv_mul_le_iff₀ hnorm_pos).2 (by simpa using hΨ_norm)
  obtain ⟨t, ⟨ht₀, ht₁⟩, ω₁, hω₁, ω₂, hω₂, hΨ₁_eq⟩ :=
    exists_mem_stateSpace_sub_of_norm_le_one hΨ₁_sa hΨ₁_norm
  let j : A →P[ℂ] A⁺¹ := .ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hc₁ : 0 ≤ ‖ψ‖ * t := mul_nonneg hnorm_pos.le ht₀
  have hc₂ : 0 ≤ ‖ψ‖ * (1 - t) := mul_nonneg hnorm_pos.le (sub_nonneg.2 ht₁)
  let φ₁ : A →P[ℂ] ℂ := .mk₀ ((‖ψ‖ * t) • ((toStrongDual ω₁).comp (j : A →L[ℂ] A⁺¹))) fun a ha =>
    smul_nonneg hc₁ (TauCeti.map_nonneg_of_mem_stateSpace hω₁ (j.map_nonneg ha))
  let φ₂ : A →P[ℂ] ℂ :=
    .mk₀ ((‖ψ‖ * (1 - t)) • ((toStrongDual ω₂).comp (j : A →L[ℂ] A⁺¹))) fun a ha =>
      smul_nonneg hc₂ (TauCeti.map_nonneg_of_mem_stateSpace hω₂ (j.map_nonneg ha))
  have hsub : ψ = (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ) := by
    ext a
    have heval : ‖ψ‖⁻¹ • ψ a = t • ω₁ (a : A⁺¹) - (1 - t) • ω₂ (a : A⁺¹) := by
      simpa [Ψ₁, hΨ_ext a] using DFunLike.congr_fun hΨ₁_eq (a : A⁺¹)
    have hmul := congrArg ((‖ψ‖ : ℝ) • ·) heval
    rw [← mul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul, smul_sub, ← mul_smul,
      ← mul_smul] at hmul
    exact hmul
  refine ⟨φ₁, φ₂, hsub, le_antisymm ?_ ?_⟩
  · have hj_norm : ‖(j : A →L[ℂ] A⁺¹)‖ ≤ 1 :=
      opNorm_le_bound _ zero_le_one fun a => by simp [j, Unitization.norm_inr]
    have hp₁_le : ‖(φ₁ : A →L[ℂ] ℂ)‖ ≤ ‖ψ‖ * t := by
      rw [PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, norm_smul,
        Real.norm_of_nonneg hc₁]
      refine mul_le_of_le_one_right hc₁ ?_
      exact (opNorm_comp_le _ _).trans <| by
        rw [TauCeti.norm_toStrongDual_of_mem_stateSpace hω₁, one_mul]
        exact hj_norm
    have hp₂_le : ‖(φ₂ : A →L[ℂ] ℂ)‖ ≤ ‖ψ‖ * (1 - t) := by
      rw [PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, norm_smul,
        Real.norm_of_nonneg hc₂]
      refine mul_le_of_le_one_right hc₂ ?_
      exact (opNorm_comp_le _ _).trans <| by
        rw [TauCeti.norm_toStrongDual_of_mem_stateSpace hω₂, one_mul]
        exact hj_norm
    linarith
  · calc
      ‖ψ‖ = ‖(φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ)‖ := congrArg norm hsub
      _ ≤ ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ := norm_sub_le _ _

/-- **Four-part positivity decomposition of a continuous linear functional on a C⋆-algebra.**
Every `ψ : A →L[ℂ] ℂ` on a possibly nonunital C⋆-algebra writes as
`(φ₁ - φ₂) + Complex.I • (φ₃ - φ₄)` for four positive continuous linear functionals
`φ₁, φ₂, φ₃, φ₄ : A →P[ℂ] ℂ` satisfying `‖φ₁‖ + ‖φ₂‖ ≤ ‖ψ‖` and `‖φ₃‖ + ‖φ₄‖ ≤ ‖ψ‖`. -/
theorem exists_eq_linearCombination_positiveContinuousLinearMap (ψ : A →L[ℂ] ℂ) :
    ∃ φ₁ φ₂ φ₃ φ₄ : A →P[ℂ] ℂ,
      ψ = ((φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ)) +
        Complex.I • ((φ₃ : A →L[ℂ] ℂ) - (φ₄ : A →L[ℂ] ℂ)) ∧
      ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ ≤ ‖ψ‖ ∧
      ‖(φ₃ : A →L[ℂ] ℂ)‖ + ‖(φ₄ : A →L[ℂ] ℂ)‖ ≤ ‖ψ‖ := by
  let ψRe : A →L[ℂ] ℂ := (2⁻¹ : ℝ) • (ψ + ψ.starDual)
  let ψIm : A →L[ℂ] ℂ := (-(2⁻¹ : ℝ) * Complex.I) • (ψ - ψ.starDual)
  have hRe_sa (a : A) : ψRe (star a) = star (ψRe a) := by
    simp [ψRe, Complex.real_smul, star_add, add_comm]
  have hIm_sa (a : A) : ψIm (star a) = star (ψIm a) := by
    simp only [ψIm, smul_apply, sub_apply, starDual_apply, star_star, smul_eq_mul, star_mul,
      star_sub, Complex.star_def, map_neg, Complex.conj_I, Complex.conj_ofReal,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    push_cast
    ring
  have hRe_norm : ‖ψRe‖ ≤ ‖ψ‖ := by
    calc
      ‖ψRe‖ = (2⁻¹ : ℝ) * ‖ψ + ψ.starDual‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ (2⁻¹ : ℝ) * (‖ψ‖ + ‖ψ.starDual‖) := by gcongr; exact norm_add_le _ _
      _ = ‖ψ‖ := by rw [norm_starDual]; ring
  have hIm_norm : ‖ψIm‖ ≤ ‖ψ‖ := by
    calc
      ‖ψIm‖ = ‖(-(2⁻¹ : ℝ) * Complex.I : ℂ)‖ * ‖ψ - ψ.starDual‖ := norm_smul _ _
      _ = (2⁻¹ : ℝ) * ‖ψ - ψ.starDual‖ := by simp
      _ ≤ (2⁻¹ : ℝ) * (‖ψ‖ + ‖ψ.starDual‖) := by gcongr; exact norm_sub_le _ _
      _ = ‖ψ‖ := by rw [norm_starDual]; ring
  obtain ⟨φ₁, φ₂, hRe_eq, hRe_sum⟩ := exists_eq_sub_positiveContinuousLinearMap hRe_sa
  obtain ⟨φ₃, φ₄, hIm_eq, hIm_sum⟩ := exists_eq_sub_positiveContinuousLinearMap hIm_sa
  refine ⟨φ₁, φ₂, φ₃, φ₄, ?_, hRe_sum.trans_le hRe_norm, hIm_sum.trans_le hIm_norm⟩
  rw [← hRe_eq, ← hIm_eq]
  ext a
  simp only [ψRe, ψIm, add_apply, smul_apply, sub_apply, starDual_apply, smul_eq_mul,
    Complex.real_smul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- If a function into a C⋆-algebra tends to `0` along a filter under every positive continuous
linear functional `A →P[ℂ] ℂ`, then it tends to `0` under every continuous complex-linear functional
`A →L[ℂ] ℂ`. -/
theorem tendsto_zero_of_forall_positiveContinuousLinearMap {ι : Type*} {l : Filter ι} {f : ι → A}
    (h : ∀ φ : A →P[ℂ] ℂ, Tendsto (fun i => φ (f i)) l (𝓝 0)) (ψ : A →L[ℂ] ℂ) :
    Tendsto (fun i => ψ (f i)) l (𝓝 0) := by
  obtain ⟨φ₁, φ₂, φ₃, φ₄, rfl, -, -⟩ := exists_eq_linearCombination_positiveContinuousLinearMap ψ
  have h12 : Tendsto (fun i => (φ₁ (f i) - φ₂ (f i) : ℂ)) l (𝓝 0) := by
    simpa using (h φ₁).sub (h φ₂)
  have h34 : Tendsto (fun i => Complex.I • (φ₃ (f i) - φ₄ (f i) : ℂ)) l (𝓝 0) := by
    simpa using ((h φ₃).sub (h φ₄)).const_smul Complex.I
  simpa using h12.add h34

/-- If a function into a C⋆-algebra tends to `0` along a filter under every positive continuous
linear functional `A →P[ℂ] ℂ`, then it tends to `0` under every continuous real-linear functional
`A →L[ℝ] ℝ`. -/
theorem tendsto_real_zero_of_forall_positiveContinuousLinearMap {ι : Type*} {l : Filter ι}
    {f : ι → A} (h : ∀ φ : A →P[ℂ] ℂ, Tendsto (fun i => φ (f i)) l (𝓝 0)) (g : A →L[ℝ] ℝ) :
    Tendsto (fun i => g (f i)) l (𝓝 0) := by
  have hℂ := tendsto_zero_of_forall_positiveContinuousLinearMap h
    (StrongDual.extendRCLike g : A →L[ℂ] ℂ)
  simpa [Function.comp_def, StrongDual.extendRCLike_apply] using
    (Complex.continuous_re.tendsto 0).comp hℂ

end Decomposition

end ContinuousLinearMap
