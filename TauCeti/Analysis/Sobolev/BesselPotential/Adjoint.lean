/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Distribution.SchwartzSpace.ReciprocalWeight
import TauCeti.Analysis.Sobolev.BesselPotential.Conjugation
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Formal adjoints on the Bessel-potential scale

Let `E` be a finite-dimensional real inner product space and `F`, `G` complex Hilbert spaces. An
operator `A` between Schwartz functions has a *formal adjoint* `A'` when
`∫ ⟪A u, v⟫ = ∫ ⟪u, A' v⟫` for all Schwartz functions `u` and `v`, as differential and
pseudodifferential operators do. This file proves that if `A` is bounded `H^s → H^r` on Schwartz
functions, then `A'` is bounded `H^{-r} → H^{-s}` **with the same constant**, and that the bounded
extension of `A'` is the adjoint of the bounded extension of `A` under the `L²` pairing of `H^{-s}`
with `H^s`.

The `H^s` norm of a Schwartz function is the `L²` norm of `⟨ζ⟩ ^ s 𝓕 u`, and the weights
`⟨ζ⟩ ^ s` and `⟨ζ⟩ ^ (-s)` are reciprocal, so these statements are the Bessel case of the duality
of Fourier-weighted norms in `TauCeti.Analysis.Distribution.SchwartzSpace.ReciprocalWeight`.

## Main declarations

* `SchwartzMap.norm_toBesselPotentialSpaceCLM_le_of_integral_inner_eq`: if
  `‖A u‖_{H^r} ≤ C ‖u‖_{H^s}` for every `u`, then `‖A' v‖_{H^{-s}} ≤ C ‖v‖_{H^{-r}}` for every `v`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_le_of_integral_mul_eq`: the same bound for a transpose
  `Aᵗ` for the bilinear pairing `∫ u v` of scalar Schwartz functions,
  `∫ (A u) v = ∫ u (Aᵗ v)`, since conjugation is isometric on every `H^σ`.
* `SchwartzMap.HasSobolevExtension.of_integral_inner_eq`: if `A` extends to `H^s → H^r`, then `A'`
  extends to `H^{-r} → H^{-s}`.
* `BesselPotentialSpace.inner_toLp_eq_of_integral_inner_eq`: the extensions `T` of `A` and `T'` of
  `A'` satisfy `⟪T' g, f⟫ = ⟪g, T f⟫` for the `L²` pairing of `H^{-σ}` with `H^σ`, for all
  `f ∈ H^s` and `g ∈ H^{-r}`.
* `BesselPotentialSpace.toLpₗᵢ_comp_comp_symm_eq_adjoint`: equivalently, read through the
  isometries `H^σ ≃ L²` given by the Bessel potentials, `T'` is the Hilbert adjoint of `T`; hence
  `‖T'‖ = ‖T‖` (`BesselPotentialSpace.opNorm_eq_of_integral_inner_eq`).

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the dual of `H_s` is `H_{-s}`).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (duality and transposes on the Sobolev scale).
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap BesselPotentialSpace InnerProductSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

namespace SchwartzMap

/-- **Transpose bound with the same constant.** Let `A'` be a formal adjoint of `A`,
`∫ ⟪A u, v⟫ = ∫ ⟪u, A' v⟫`. If `‖A u‖_{H^r} ≤ C ‖u‖_{H^s}` for every Schwartz function `u`, then
`‖A' v‖_{H^{-s}} ≤ C ‖v‖_{H^{-r}}` for every Schwartz function `v`. -/
theorem norm_toBesselPotentialSpaceCLM_le_of_integral_inner_eq {s r C : ℝ} (hC : 0 ≤ C)
    {A : 𝓢(E, F) → 𝓢(E, G)} {A' : 𝓢(E, G) → 𝓢(E, F)}
    (hA : ∀ u v, ∫ x, ⟪A u x, v x⟫_ℂ = ∫ x, ⟪u x, A' v x⟫_ℂ)
    (hAC : ∀ u, ‖toBesselPotentialSpaceCLM r 2 (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s 2 u‖)
    (v : 𝓢(E, G)) :
    ‖toBesselPotentialSpaceCLM (-s) 2 (A' v)‖ ≤ C * ‖toBesselPotentialSpaceCLM (-r) 2 v‖ := by
  simp only [norm_toBesselPotentialSpaceCLM] at hAC ⊢
  exact eLpNorm_smul_fourier_le_of_integral_inner_eq (by fun_prop)
    (TauCeti.one_add_norm_sq_rpow_neg_mul_rpow · s) (by fun_prop) (by fun_prop)
    (TauCeti.one_add_norm_sq_rpow_neg_mul_rpow · r) hA hC hAC v

/-- **Transpose bound for the bilinear pairing.** Let `Aᵗ` be a transpose of `A` for the bilinear
pairing `∫ u v` of scalar Schwartz functions, `∫ (A u) v = ∫ u (Aᵗ v)`. If
`‖A u‖_{H^r} ≤ C ‖u‖_{H^s}` for every `u`, then `‖Aᵗ v‖_{H^{-s}} ≤ C ‖v‖_{H^{-r}}` for every `v`. -/
theorem norm_toBesselPotentialSpaceCLM_le_of_integral_mul_eq {s r C : ℝ} (hC : 0 ≤ C)
    {A At : 𝓢(E, ℂ) → 𝓢(E, ℂ)} (hA : ∀ u v, ∫ x, A u x * v x = ∫ x, u x * At v x)
    (hAC : ∀ u, ‖toBesselPotentialSpaceCLM r 2 (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s 2 u‖)
    (v : 𝓢(E, ℂ)) :
    ‖toBesselPotentialSpaceCLM (-s) 2 (At v)‖ ≤ C * ‖toBesselPotentialSpaceCLM (-r) 2 v‖ := by
  -- Conjugation is isometric on every `H^σ`.
  have hconj (σ : ℝ) (f : 𝓢(E, ℂ)) :
      ‖toBesselPotentialSpaceCLM σ 2 (conjCLM f)‖ = ‖toBesselPotentialSpaceCLM σ 2 f‖ := by
    rw [conjCLM_eq_conjPostcompCLM, toBesselPotentialSpaceCLM_conjPostcompCLM,
      BesselPotentialSpace.norm_conjPostcomp_apply _ (by simp)]
  -- `w ↦ conj (Aᵗ (conj w))` is a formal adjoint of `A`.
  have hadj (u w : 𝓢(E, ℂ)) :
      ∫ x, ⟪A u x, w x⟫_ℂ = ∫ x, ⟪u x, conjCLM (At (conjCLM w)) x⟫_ℂ := by
    have h := congrArg (starRingEnd ℂ) (hA u (conjCLM w))
    simp only [← integral_conj, map_mul, conjCLM_apply, RCLike.conj_conj] at h
    simp only [RCLike.inner_apply, conjCLM_apply]
    simpa only [mul_comm] using h
  simpa only [hconj, conjCLM_conjCLM] using
    norm_toBesselPotentialSpaceCLM_le_of_integral_inner_eq hC hadj hAC (conjCLM v)

/-- **Formal adjoints extend to the dual orders.** If `A` extends to a bounded operator
`H^s → H^r` and `A'` is a formal adjoint of `A`, then `A'` extends to a bounded operator
`H^{-r} → H^{-s}`. -/
theorem HasSobolevExtension.of_integral_inner_eq {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)}
    {A' : 𝓢(E, G) →L[ℂ] 𝓢(E, F)} {s r : ℝ} (hA : HasSobolevExtension A s r)
    (hAA' : ∀ u v, ∫ x, ⟪A u x, v x⟫_ℂ = ∫ x, ⟪u x, A' v x⟫_ℂ) :
    HasSobolevExtension A' (-r) (-s) := by
  obtain ⟨C, hC, hAC⟩ := hasSobolevExtension_iff_exists_norm_le.1 hA
  exact hasSobolevExtension_iff_exists_norm_le.2
    ⟨C, hC, norm_toBesselPotentialSpaceCLM_le_of_integral_inner_eq hC hAA' hAC⟩

end SchwartzMap

namespace BesselPotentialSpace

open SchwartzMap

/-- **The extension of a formal adjoint is the adjoint of the extension.** Let `A'` be a formal
adjoint of `A`, and let `T : H^s → H^r` and `T' : H^{-r} → H^{-s}` be bounded operators extending
`A` and `A'`. Then `⟪T' g, f⟫ = ⟪g, T f⟫` for all `f ∈ H^s` and `g ∈ H^{-r}`, for the `L²` pairing
`⟪a, b⟫ = ⟪J^{-σ} a, J^σ b⟫_{L²}` of `a ∈ H^{-σ}` with `b ∈ H^σ`, which extends `∫ ⟪a, b⟫` from
Schwartz functions (`SchwartzMap.inner_toLp_toBesselPotentialSpaceCLM_neg`). -/
theorem inner_toLp_eq_of_integral_inner_eq {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)}
    {A' : 𝓢(E, G) →L[ℂ] 𝓢(E, F)} {s r : ℝ} {T : H^{s}(E, F) →L[ℂ] H^{r}(E, G)}
    {T' : H^{-r}(E, G) →L[ℂ] H^{-s}(E, F)}
    (hT : T ∘L toBesselPotentialSpaceCLM s 2 = toBesselPotentialSpaceCLM r 2 ∘L A)
    (hT' : T' ∘L toBesselPotentialSpaceCLM (-r) 2 = toBesselPotentialSpaceCLM (-s) 2 ∘L A')
    (hAA' : ∀ u v, ∫ x, ⟪A u x, v x⟫_ℂ = ∫ x, ⟪u x, A' v x⟫_ℂ) (f : H^{s}(E, F))
    (g : H^{-r}(E, G)) :
    ⟪(T' g).toLp, f.toLp⟫_ℂ = ⟪g.toLp, (T f).toLp⟫_ℂ := by
  -- Both sides are continuous in `f` and `g`, so it suffices to take Schwartz functions.
  refine (denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top).induction_on f
    (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ ?_
  refine (denseRange_toBesselPotentialSpaceCLM (p := 2) (-r) ENNReal.ofNat_ne_top).induction_on g
    (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ ?_
  have hTu := congr($hT u)
  have hTv := congr($hT' v)
  simp only [ContinuousLinearMap.comp_apply] at hTu hTv
  rw [hTu, hTv, inner_toLp_toBesselPotentialSpaceCLM_neg s,
    inner_toLp_toBesselPotentialSpaceCLM_neg r]
  -- `∫ ⟪A' v, u⟫` is the conjugate of `∫ ⟪u, A' v⟫ = ∫ ⟪A u, v⟫`.
  rw [← integral_inner_conj_symm, ← hAA', integral_inner_conj_symm]

/-- **The extension of a formal adjoint is the Hilbert adjoint.** Let `A'` be a formal adjoint of
`A`, and let `T : H^s → H^r` and `T' : H^{-r} → H^{-s}` be bounded operators extending `A` and
`A'`. Read through the isometries `H^σ ≃ L²` given by the Bessel potentials, `T'` is the Hilbert
adjoint of `T`. -/
theorem toLpₗᵢ_comp_comp_symm_eq_adjoint {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)}
    {A' : 𝓢(E, G) →L[ℂ] 𝓢(E, F)} {s r : ℝ} {T : H^{s}(E, F) →L[ℂ] H^{r}(E, G)}
    {T' : H^{-r}(E, G) →L[ℂ] H^{-s}(E, F)}
    (hT : T ∘L toBesselPotentialSpaceCLM s 2 = toBesselPotentialSpaceCLM r 2 ∘L A)
    (hT' : T' ∘L toBesselPotentialSpaceCLM (-r) 2 = toBesselPotentialSpaceCLM (-s) 2 ∘L A')
    (hAA' : ∀ u v, ∫ x, ⟪A u x, v x⟫_ℂ = ∫ x, ⟪u x, A' v x⟫_ℂ) :
    (toLpₗᵢ E F (-s) 2 : H^{-s}(E, F) →L[ℂ] Lp F 2 (volume : Measure E)) ∘L
        T' ∘L ((toLpₗᵢ E G (-r) 2).symm :
          Lp G 2 (volume : Measure E) →L[ℂ] H^{-r}(E, G)) =
      ContinuousLinearMap.adjoint
        ((toLpₗᵢ E G r 2 : H^{r}(E, G) →L[ℂ] Lp G 2 (volume : Measure E)) ∘L
          T ∘L ((toLpₗᵢ E F s 2).symm :
            Lp F 2 (volume : Measure E) →L[ℂ] H^{s}(E, F))) := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y ↦ ?_
  have h := inner_toLp_eq_of_integral_inner_eq hT hT' hAA'
    ((toLpₗᵢ E F s 2).symm y) ((toLpₗᵢ E G (-r) 2).symm x)
  simp only [← toLpₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply] at h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h

/-- **The extension of a formal adjoint has the same norm.** Let `A'` be a formal adjoint of `A`,
and let `T : H^s → H^r` and `T' : H^{-r} → H^{-s}` be bounded operators extending `A` and `A'`.
Then `‖T'‖ = ‖T‖`. -/
theorem opNorm_eq_of_integral_inner_eq {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)}
    {A' : 𝓢(E, G) →L[ℂ] 𝓢(E, F)} {s r : ℝ} {T : H^{s}(E, F) →L[ℂ] H^{r}(E, G)}
    {T' : H^{-r}(E, G) →L[ℂ] H^{-s}(E, F)}
    (hT : T ∘L toBesselPotentialSpaceCLM s 2 = toBesselPotentialSpaceCLM r 2 ∘L A)
    (hT' : T' ∘L toBesselPotentialSpaceCLM (-r) 2 = toBesselPotentialSpaceCLM (-s) 2 ∘L A')
    (hAA' : ∀ u v, ∫ x, ⟪A u x, v x⟫_ℂ = ∫ x, ⟪u x, A' v x⟫_ℂ) :
    ‖T'‖ = ‖T‖ := by
  have h := congr(‖$(toLpₗᵢ_comp_comp_symm_eq_adjoint hT hT' hAA')‖)
  simpa only [LinearIsometryEquiv.norm_map, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv] using h

end BesselPotentialSpace
