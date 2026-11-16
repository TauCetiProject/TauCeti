/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Star.LinearMap
import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Unitization extensions and Jordan decomposition of bounded functionals

This file supplies two structural facts about continuous linear functionals on a possibly
nonunital C⋆-algebra `A`.

## Canonical extension to the unitization

Every positive continuous linear functional `ω : A →P[ℂ] ℂ` extends canonically to a positive
functional `ω.extendUnitization : Unitization ℂ A →P[ℂ] ℂ` of the same norm via
`ω.extendUnitization (c, a) = c * ‖ω‖ + ω a`. Boundedness by `‖ω‖` follows immediately from taking
the limit of `‖ω (c • e + e * a)‖ = ‖ω ((e : A⁺¹) * x)‖ ≤ ‖ω‖ ‖x‖` along an increasing approximate
unit `e`, and positivity then follows from `ContinuousLinearMap.monotone_iff_opNorm_eq_map_one`.
Moreover, the GNS classes `[e]` converge in norm to the cyclic vector `[1]` of `ω.extendUnitization`
(`PositiveContinuousLinearMap.tendsto_toGNS_inr_extendUnitization`), so restricting the GNS
representation of `ω.extendUnitization` to `A` remains nondegenerate
(`PositiveContinuousLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom_extendUnitization_comp_inr`).

## Jordan and four-positive decompositions

Every bounded self-adjoint (Hermitian) linear functional `φ : A →L[ℂ] ℂ` admits a norm-preserving
Jordan decomposition `φ = ω₁ - ω₂` with `ω₁, ω₂ : A →P[ℂ] ℂ` and `‖ω₁‖ + ‖ω₂‖ = ‖φ‖`
(`ContinuousLinearMap.exists_sub_positiveContinuousLinearMap_of_map_star`). For unital algebras
this is proved by separating `φ` from the weak-* compact convex set
`{s • η₁ - t • η₂ | 0 ≤ s, 0 ≤ t, s + t ≤ 1, η₁, η₂ ∈ stateSpace D}` via Hahn–Banach and testing
against a spectral norm-attaining state; the nonunital case follows by norm-preserving Hahn–Banach
extension to `Unitization ℂ A` and symmetrization.

Splitting an arbitrary `φ : A →L[ℂ] ℂ` into its Hermitian and skew-Hermitian parts gives the
four-positive decomposition (`ContinuousLinearMap.exists_four_positiveContinuousLinearMap`).
Consequently, a net in `A` converges weakly if and only if it converges under every positive
continuous linear functional
(`TauCeti.CStarAlgebra.tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap`).

## References

* B. Blackadar, *Operator Algebras*, II.6.2.5 and II.6.3.4.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorems 3.3.9 and 4.3.6.
-/

public section

noncomputable section

open Filter Set Topology Unitization
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Along any increasing approximate unit `e`, the values `ω (e * e)` of a positive continuous
linear functional tend to `‖ω‖`. -/
theorem tendsto_mul_self_nhds_opNorm (ω : A →P[ℂ] ℂ) {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e => ω (e * e)) l (𝓝 (‖(ω : A →L[ℂ] ℂ)‖ : ℂ)) := by
  by_cases h0 : ‖(ω : A →L[ℂ] ℂ)‖ = 0
  · have hω : (ω : A →L[ℂ] ℂ) = 0 := norm_eq_zero.mp h0
    have hval : ∀ x, ω x = 0 := fun x => by
      simpa using DFunLike.congr_fun hω x
    simpa [h0, hval] using tendsto_const_nhds
  have hpos : 0 < ‖(ω : A →L[ℂ] ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hlim : Tendsto (fun e => ‖ω e‖) l (𝓝 ‖(ω : A →L[ℂ] ℂ)‖) := by
    simpa [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using
      (ω.tendsto_nhds_opNorm hl).norm
  have hnorm : Tendsto (fun e => ‖ω (e * e)‖) l (𝓝 ‖(ω : A →L[ℂ] ℂ)‖) := by
    have hlo : Tendsto (fun e => ‖ω e‖ ^ 2 / ‖(ω : A →L[ℂ] ℂ)‖) l (𝓝 ‖(ω : A →L[ℂ] ℂ)‖) := by
      have h := (hlim.pow 2).div_const ‖(ω : A →L[ℂ] ℂ)‖
      rwa [sq, mul_div_cancel_right₀ _ h0] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hlim ?_ ?_
    · filter_upwards [hl.eventually_nonneg] with e he
      have hsq : star e * e = e * e := by rw [he.isSelfAdjoint.star_eq]
      rw [div_le_iff₀ hpos, mul_comm, ← hsq]
      exact ω.norm_map_sq_le_opNorm_mul e
    · filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
      refine CStarAlgebra.norm_le_norm_of_le_of_nonneg (ω.mono ?_) (ω.map_nonneg ?_)
      · exact CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he₀ he₁
      · simpa [he₀.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
  refine hnorm.ofReal.congr' ?_
  filter_upwards [hl.eventually_nonneg] with e he₀
  have hsq : 0 ≤ e * e := by simpa [he₀.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
  exact Complex.norm_of_nonneg' (ω.map_nonneg hsq)

/-- The underlying continuous linear functional of `extendUnitization`: `x ↦ x.fst * ‖ω‖ + ω x.snd`.
It has operator norm bounded by `‖ω‖`, hence equal to `‖ω‖` since it sends `1` to `‖ω‖`. -/
private def extendUnitizationCLM (ω : A →P[ℂ] ℂ) : Unitization ℂ A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd
      map_add' := fun x y => by
        simp only [Unitization.fst_add, Unitization.snd_add, map_add]
        ring
      map_smul' := fun c x => by
        simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul, smul_eq_mul,
          RingHom.id_apply]
        ring }
    ‖(ω : A →L[ℂ] ℂ)‖
    fun x => by
      have hl := CStarAlgebra.increasingApproximateUnit A
      have hconv : Tendsto (fun e : A => x.fst * ω e + ω (e * x.snd))
          (CStarAlgebra.approximateUnit A) (𝓝 (x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd)) :=
        ((ω.tendsto_nhds_opNorm hl).const_mul x.fst).add
          ((ω.continuous.tendsto x.snd).comp (hl.tendsto_mul_right x.snd))
      refine le_of_tendsto (hx := hl.neBot) hconv.norm ?_
      filter_upwards [hl.eventually_norm] with e he
      have hmul : ((x.fst • e + e * x.snd : A) : A⁺¹) = (e : A⁺¹) * x := by
        conv_rhs => rw [← Unitization.inl_fst_add_inr_snd_eq x]
        rw [mul_add, ← Unitization.algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one]
        simp [Unitization.inr_add, Unitization.inr_smul, Unitization.inr_mul]
      have hval : x.fst * ω e + ω (e * x.snd) = ω (x.fst • e + e * x.snd) := by
        simp [map_add, map_smul]
      calc ‖x.fst * ω e + ω (e * x.snd)‖
          = ‖(ω : A →L[ℂ] ℂ) (x.fst • e + e * x.snd)‖ := by
            rw [hval, PositiveContinuousLinearMap.coe_toContinuousLinearMap]
        _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * ‖x.fst • e + e * x.snd‖ := (ω : A →L[ℂ] ℂ).le_opNorm _
        _ = ‖(ω : A →L[ℂ] ℂ)‖ * ‖(e : A⁺¹) * x‖ := by
          rw [← Unitization.norm_inr (𝕜 := ℂ), hmul]
        _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * (‖(e : A⁺¹)‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * ‖x‖ := by
          rw [Unitization.norm_inr]
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg x) he) (norm_nonneg _)

private theorem opNorm_extendUnitizationCLM (ω : A →P[ℂ] ℂ) :
    ‖extendUnitizationCLM ω‖ = ‖(ω : A →L[ℂ] ℂ)‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) ?_
  have h1 : extendUnitizationCLM ω 1 = (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
    simp [extendUnitizationCLM]
  have hle := (extendUnitizationCLM ω).le_opNorm 1
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hle
  have hnorm1 : ‖(1 : Unitization ℂ A)‖ = 1 := norm_one
  rwa [hnorm1, mul_one] at hle

/-- The canonical norm-preserving extension of a positive continuous linear functional
`ω : A →P[ℂ] ℂ` to `Unitization ℂ A`, given by `x ↦ x.fst * ‖ω‖ + ω x.snd`. -/
def extendUnitization (ω : A →P[ℂ] ℂ) : Unitization ℂ A →P[ℂ] ℂ :=
  { toContinuousLinearMap := extendUnitizationCLM ω
    monotone' := (ContinuousLinearMap.monotone_iff_opNorm_eq_map_one
      (f := extendUnitizationCLM ω)).mpr <| by
        rw [opNorm_extendUnitizationCLM]
        simp [extendUnitizationCLM] }

@[simp]
theorem extendUnitization_apply (ω : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    ω.extendUnitization x = x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd :=
  (rfl)

theorem extendUnitization_inr (ω : A →P[ℂ] ℂ) (a : A) :
    ω.extendUnitization (a : Unitization ℂ A) = ω a := by
  simp

theorem extendUnitization_one (ω : A →P[ℂ] ℂ) :
    ω.extendUnitization 1 = (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
  simp

@[simp]
theorem extendUnitization_zero :
    (0 : A →P[ℂ] ℂ).extendUnitization = 0 := by
  ext x
  simp [PositiveContinuousLinearMap.toContinuousLinearMap_zero]

@[simp]
theorem opNorm_extendUnitization (ω : A →P[ℂ] ℂ) :
    ‖(ω.extendUnitization : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(ω : A →L[ℂ] ℂ)‖ :=
  opNorm_extendUnitizationCLM ω

/-- Restricting `ω.extendUnitization` along `Unitization.inrNonUnitalStarAlgHom ℂ A` recovers
`ω`. -/
@[simp]
theorem extendUnitization_comp_inr (ω : A →P[ℂ] ℂ) :
    ω.extendUnitization.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)) = ω := by
  ext a
  simp

/-- Along any increasing approximate unit `e` of `A`, the GNS classes `[e]` converge in norm to
the cyclic GNS vector `[1]` of `ω.extendUnitization`. -/
theorem tendsto_toGNS_inr_extendUnitization (ω : A →P[ℂ] ℂ) {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e : A => ω.extendUnitization.toPositiveLinearMap.toGNS (e : Unitization ℂ A)) l
      (𝓝 ω.extendUnitization.toPositiveLinearMap.gnsVector) := by
  set f := ω.extendUnitization.toPositiveLinearMap
  rw [tendsto_iff_norm_sub_tendsto_zero]
  suffices hsq : Tendsto (fun e : A => ‖f.toGNS (e : A⁺¹) - f.gnsVector‖ ^ 2) l (𝓝 0) by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Real.sqrt_zero, Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h
  have hval : ∀ᶠ e : A in l,
      (‖f.toGNS (e : A⁺¹) - f.gnsVector‖ ^ 2 : ℂ) =
        ω (e * e) - 2 * ω e + (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
    filter_upwards [hl.eventually_nonneg] with e he
    have hdiff : f.toGNS (e : A⁺¹) - f.gnsVector = f.toGNS ((e : A⁺¹) - 1) := by
      simp only [map_sub, PositiveLinearMap.gnsVector_def, PositiveLinearMap.toGNS_apply]
    rw [hdiff, f.norm_toGNS_sq]
    have hstar : star ((e : A⁺¹) - 1) = (e : A⁺¹) - 1 := by
      rw [star_sub, star_one, ← Unitization.inr_star, he.isSelfAdjoint.star_eq]
    rw [hstar]
    have hexp : ((e : A⁺¹) - 1) * ((e : A⁺¹) - 1) =
        ((e * e : A) : A⁺¹) - (2 : ℂ) • (e : A⁺¹) + 1 := by
      rw [Unitization.inr_mul, two_smul]
      noncomm_ring
    rw [hexp, map_add, map_sub, map_smul]
    simp [f]
  have hlimC : Tendsto (fun e : A => (‖f.toGNS (e : A⁺¹) - f.gnsVector‖ ^ 2 : ℂ)) l (𝓝 0) := by
    refine Tendsto.congr' (hval.mono fun _ h => h.symm) ?_
    have h := ((ω.tendsto_mul_self_nhds_opNorm hl).sub
      ((ω.tendsto_nhds_opNorm hl).const_mul 2)).add
      (tendsto_const_nhds (x := (‖(ω : A →L[ℂ] ℂ)‖ : ℂ)))
    have h0 : (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) - 2 * ↑‖(ω : A →L[ℂ] ℂ)‖ + ↑‖(ω : A →L[ℂ] ℂ)‖ = 0 := by
      ring
    rwa [h0] at h
  simpa [Function.comp_def, ← Complex.ofReal_pow] using
    (Complex.continuous_re.tendsto 0).comp hlimC

/-- Restricting the GNS representation of `ω.extendUnitization` to `A` yields a nondegenerate
representation on `ω.extendUnitization.toPositiveLinearMap.GNS`. -/
theorem isNondegenerate_gnsNonUnitalStarAlgHom_extendUnitization_comp_inr (ω : A →P[ℂ] ℂ) :
    (ω.extendUnitization.toPositiveLinearMap.gnsNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)).IsNondegenerate := by
  set f := ω.extendUnitization.toPositiveLinearMap
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_forall_apply_eq_zero]
  intro ξ hξ
  have hinner_inr : ∀ a : A, ⟪f.toGNS (a : A⁺¹), ξ⟫_ℂ = 0 := fun a => by
    have h := hξ (star a)
    simp only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply] at h
    rw [PositiveLinearMap.toGNS_apply, ← f.gnsNonUnitalStarAlgHom_apply_gnsVector,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, ← Unitization.inr_star, h, inner_zero_right]
  have hinner_one : ⟪f.gnsVector, ξ⟫_ℂ = 0 := by
    have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have hlim := ((innerSL ℂ ξ).continuous.tendsto _).comp
      (ω.tendsto_toGNS_inr_extendUnitization hl)
    have hlim' : Tendsto (fun e : A => ⟪f.toGNS (e : A⁺¹), ξ⟫_ℂ)
        (CStarAlgebra.approximateUnit A) (𝓝 ⟪f.gnsVector, ξ⟫_ℂ) := by
      have hconj := (continuous_star.tendsto _).comp hlim
      simpa [Function.comp_def] using hconj
    exact tendsto_nhds_unique hlim' <|
      (tendsto_const_nhds (x := (0 : ℂ))).congr fun e => (hinner_inr e).symm
  have hinner_all : ∀ x : A⁺¹, ⟪f.toGNS x, ξ⟫_ℂ = 0 := fun x => by
    nth_rw 1 [← Unitization.inl_fst_add_inr_snd_eq x]
    have hinl : Unitization.inl x.fst = x.fst • (1 : A⁺¹) := by
      rw [← Unitization.algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one]
    rw [hinl, map_add, map_smul, inner_add_left, inner_smul_left,
      PositiveLinearMap.toGNS_apply, ← PositiveLinearMap.gnsVector_def, hinner_one,
      hinner_inr, mul_zero, add_zero]
  refine ext_inner_left ℂ fun η => ?_
  rw [inner_zero_right]
  refine f.denseRange_toGNS.induction_on η ?_ hinner_all
  exact isClosed_eq ((continuous_star.comp (innerSL ℂ ξ).continuous).congr fun v => by simp)
    continuous_const

end PositiveContinuousLinearMap

namespace ContinuousLinearMap

section JordanDecomposition

/-- The weak-* compact convex set `{s • η₁ - t • η₂ | s, t ≥ 0, s + t ≤ 1, η₁, η₂ ∈ S(D)}` of
sub-unit signed convex combinations of states on a unital C⋆-algebra `D`. -/
private def stateDiffHull (D : Type*) [CStarAlgebra D] [PartialOrder D] :
    Set (WeakDual ℂ D) :=
  (fun p : (ℝ × ℝ) × WeakDual ℂ D × WeakDual ℂ D => p.1.1 • p.2.1 - p.1.2 • p.2.2) ''
    ({p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ×ˢ
      (TauCeti.stateSpace D ×ˢ TauCeti.stateSpace D))

private theorem isCompact_stateDiffHull {D : Type*} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] : IsCompact (stateDiffHull D) := by
  have hΔ : IsCompact {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
    refine (isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      |>.of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
    · rintro ⟨s, t⟩ ⟨hs, ht, hst⟩
      exact ⟨⟨hs, by linarith⟩, ⟨ht, by linarith⟩⟩
  have hsmul : Continuous (fun p : ℝ × WeakDual ℂ D => p.1 • p.2) := by
    have : (fun p : ℝ × WeakDual ℂ D => p.1 • p.2) = fun p => (p.1 : ℂ) • p.2 := by
      funext p
      exact WeakDual.real_smul_eq_coe_smul p.1 p.2
    rw [this]
    exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
  have hF : Continuous (fun p : (ℝ × ℝ) × WeakDual ℂ D × WeakDual ℂ D =>
      p.1.1 • p.2.1 - p.1.2 • p.2.2) :=
    (hsmul.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).sub
    (hsmul.comp ((continuous_snd.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd)))
  exact (hΔ.prod (TauCeti.isCompact_stateSpace.prod TauCeti.isCompact_stateSpace)).image hF

private theorem convex_stateDiffHull {D : Type*} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] [Nontrivial D] : Convex ℝ (stateDiffHull D) := by
  rintro _ ⟨⟨⟨s₁, t₁⟩, η₁, θ₁⟩, ⟨⟨hs₁, ht₁, hst₁⟩, hη₁, hθ₁⟩, rfl⟩
    _ ⟨⟨⟨s₂, t₂⟩, η₂, θ₂⟩, ⟨⟨hs₂, ht₂, hst₂⟩, hη₂, hθ₂⟩, rfl⟩
    a b ha hb hab
  obtain ⟨ω₀, hω₀⟩ := TauCeti.stateSpace_nonempty (A := D)
  have combine : ∀ {u₁ u₂ : ℝ} {μ₁ μ₂ : WeakDual ℂ D},
      0 ≤ u₁ → 0 ≤ u₂ → μ₁ ∈ TauCeti.stateSpace D → μ₂ ∈ TauCeti.stateSpace D →
      ∃ μ ∈ TauCeti.stateSpace D, (a * u₁ + b * u₂) • μ = a • (u₁ • μ₁) + b • (u₂ • μ₂) := by
    intro u₁ u₂ μ₁ μ₂ hu₁ hu₂ hμ₁ hμ₂
    set u := a * u₁ + b * u₂
    have hu_nonneg : 0 ≤ u := by positivity
    rcases hu_nonneg.eq_or_lt with hu0 | hu_pos
    · have h1 : a * u₁ = 0 := by nlinarith
      have h2 : b * u₂ = 0 := by nlinarith
      refine ⟨ω₀, hω₀, DFunLike.ext _ _ fun d => ?_⟩
      simp only [← hu0, add_apply, WeakDual.real_smul_apply]
      push_cast
      have h1' : (a : ℂ) * (u₁ : ℂ) = 0 := by exact_mod_cast h1
      have h2' : (b : ℂ) * (u₂ : ℂ) = 0 := by exact_mod_cast h2
      linear_combination -(μ₁ d) * h1' - (μ₂ d) * h2'
    · refine ⟨(a * u₁ / u) • μ₁ + (b * u₂ / u) • μ₂,
        TauCeti.convex_stateSpace hμ₁ hμ₂ (by positivity) (by positivity)
          (by rw [← add_div, div_self hu_pos.ne']), DFunLike.ext _ _ fun d => ?_⟩
      simp only [add_apply, WeakDual.real_smul_apply]
      push_cast
      have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
      field_simp [huC]
  obtain ⟨η, hη, hη_eq⟩ := combine hs₁ hs₂ hη₁ hη₂
  obtain ⟨θ, hθ, hθ_eq⟩ := combine ht₁ ht₂ hθ₁ hθ₂
  refine ⟨((a * s₁ + b * s₂, a * t₁ + b * t₂), η, θ),
    ⟨⟨by positivity, by positivity, by nlinarith⟩, hη, hθ⟩, ?_⟩
  simp only [hη_eq, hθ_eq, smul_sub]
  abel

private theorem toWeakDual_mem_stateDiffHull_of_norm_eq_one
    {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
    {ψ : D →L[ℂ] ℂ} (hψ_norm : ‖ψ‖ = 1) (hψ_star : ∀ a, ψ (star a) = star (ψ a)) :
    StrongDual.toWeakDual ψ ∈ stateDiffHull D := by
  by_contra hnot
  obtain ⟨L, u, hLu, huψ⟩ :=
    @RCLike.geometric_hahn_banach_closed_point ℂ (WeakDual ℂ D) _ _ _ (stateDiffHull D)
      _ _ _ _ _ _ WeakDual.instLocallyConvexSpaceReal convex_stateDiffHull
      isCompact_stateDiffHull.isClosed hnot
  obtain ⟨x, hx⟩ := WeakDual.exists_forall_apply_eq_apply L
  let h : D := (2 : ℂ)⁻¹ • (x + star x)
  have hh_sa : IsSelfAdjoint h := by
    rw [IsSelfAdjoint, star_smul, star_add, star_star, add_comm]
    simp [h]
  have hre_eq : ∀ (η : WeakDual ℂ D), (∀ a, η (star a) = star (η a)) →
      (η h).re = (η x).re := fun η hη => by
    have h1 : η h = ((η x).re : ℂ) := by
      simp only [h, map_smul, map_add, hη x, Complex.star_def, Complex.add_conj]
      push_cast
      ring
    rw [h1, Complex.ofReal_re]
  have hψ_re : u < (ψ h).re := by
    have h1 : u < (StrongDual.toWeakDual ψ x).re := by simpa [hx] using huψ
    rwa [← hre_eq (StrongDual.toWeakDual ψ) hψ_star] at h1
  have hstate_lt : ∀ ω : D →P[ℂ] ℂ, ‖(ω : D →L[ℂ] ℂ)‖ = 1 → |(ω h).re| < u := fun ω hω => by
    have hω_mem : StrongDual.toWeakDual (ω : D →L[ℂ] ℂ) ∈ TauCeti.stateSpace D :=
      ω.toWeakDual_mem_stateSpace_iff.mpr hω
    have hpos_mem : StrongDual.toWeakDual (ω : D →L[ℂ] ℂ) ∈ stateDiffHull D :=
      ⟨((1, 0), StrongDual.toWeakDual (ω : D →L[ℂ] ℂ), StrongDual.toWeakDual (ω : D →L[ℂ] ℂ)),
        ⟨⟨zero_le_one, le_rfl, by norm_num⟩, hω_mem, hω_mem⟩,
        by simp [WeakDual.real_smul_eq_coe_smul]⟩
    have hneg_mem : -StrongDual.toWeakDual (ω : D →L[ℂ] ℂ) ∈ stateDiffHull D :=
      ⟨((0, 1), StrongDual.toWeakDual (ω : D →L[ℂ] ℂ), StrongDual.toWeakDual (ω : D →L[ℂ] ℂ)),
        ⟨⟨le_rfl, zero_le_one, by norm_num⟩, hω_mem, hω_mem⟩,
        by simp [WeakDual.real_smul_eq_coe_smul]⟩
    have hω_re : (ω h).re = (ω x).re := by
      simpa using hre_eq (StrongDual.toWeakDual (ω : D →L[ℂ] ℂ)) fun a => by
        simpa using map_star ω a
    have h1 : (ω h).re < u := by
      have := hLu _ hpos_mem
      simpa [hx, hω_re] using this
    have h2 : -(ω h).re < u := by
      have := hLu _ hneg_mem
      rw [hx, RCLike.re_to_complex, ← map_neg, StrongDual.toWeakDual_apply, neg_apply,
        Complex.neg_re] at this
      simpa [hω_re] using this
    exact abs_lt.mpr ⟨by linarith, h1⟩
  have : IsStarNormal h := hh_sa.isStarNormal
  have hnorm_lt : ‖h‖ < u := by
    open TauCeti.CStarAlgebra in
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum h hh_sa with hr | hr
    · obtain ⟨ω, -, hω_norm, hω_pow⟩ :=
        exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum
          (spectrum.algebraMap_mem ℂ hr)
      have hωh : ω h = (‖h‖ : ℂ) := by simpa using hω_pow 0 1
      have hlt := hstate_lt ω hω_norm
      rwa [hωh, Complex.ofReal_re, abs_of_nonneg (norm_nonneg h)] at hlt
    · obtain ⟨ω, -, hω_norm, hω_pow⟩ :=
        exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum
          (spectrum.algebraMap_mem ℂ hr)
      have hωh : ω h = -(‖h‖ : ℂ) := by simpa using hω_pow 0 1
      have hlt := hstate_lt ω hω_norm
      rwa [hωh, Complex.neg_re, Complex.ofReal_re, abs_neg, abs_of_nonneg (norm_nonneg h)] at hlt
  have hle : (ψ h).re ≤ ‖h‖ :=
    (Complex.re_le_norm (ψ h)).trans <| by simpa [hψ_norm] using ψ.le_opNorm h
  linarith

/-- On a unital C⋆-algebra, every bounded Hermitian functional admits a norm-preserving Jordan
decomposition `φ = ω₁ - ω₂` into positive functionals with `‖ω₁‖ + ‖ω₂‖ = ‖φ‖`. -/
private theorem exists_sub_positiveContinuousLinearMap_unital
    {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (φ : D →L[ℂ] ℂ) (hφ : ∀ a, φ (star a) = star (φ a)) :
    ∃ ω₁ ω₂ : D →P[ℂ] ℂ, (∀ a, φ a = ω₁ a - ω₂ a) ∧
      ‖(ω₁ : D →L[ℂ] ℂ)‖ + ‖(ω₂ : D →L[ℂ] ℂ)‖ = ‖φ‖ := by
  by_cases hφ0 : φ = 0
  · refine ⟨0, 0, fun a => by simp [hφ0], by simp [hφ0]⟩
  have : Nontrivial D := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hφ0 (ext fun a => by simp [Subsingleton.elim a 0])
  have hφ_pos : 0 < ‖φ‖ := norm_pos_iff.mpr hφ0
  set ψ : D →L[ℂ] ℂ := (‖φ‖⁻¹ : ℂ) • φ
  have hψ_norm : ‖ψ‖ = 1 := by simp [ψ, norm_smul, inv_mul_cancel₀ hφ_pos.ne']
  have hψ_star : ∀ a, ψ (star a) = star (ψ a) := fun a => by
    simp [ψ, hφ a, Complex.conj_ofReal]
  obtain ⟨⟨⟨s, t⟩, η₁, η₂⟩, ⟨⟨hs, ht, hst⟩, hη₁, hη₂⟩, hF_eq⟩ :=
    toWeakDual_mem_stateDiffHull_of_norm_eq_one hψ_norm hψ_star
  let ω₁ : D →P[ℂ] ℂ :=
    .mk₀ ((‖φ‖ * s : ℝ) • WeakDual.toStrongDual η₁) fun a ha => by
      simpa [Complex.real_smul] using
        mul_nonneg (Complex.zero_le_real.mpr (mul_nonneg (norm_nonneg φ) hs))
          (TauCeti.map_nonneg_of_mem_stateSpace hη₁ ha)
  let ω₂ : D →P[ℂ] ℂ :=
    .mk₀ ((‖φ‖ * t : ℝ) • WeakDual.toStrongDual η₂) fun a ha => by
      simpa [Complex.real_smul] using
        mul_nonneg (Complex.zero_le_real.mpr (mul_nonneg (norm_nonneg φ) ht))
          (TauCeti.map_nonneg_of_mem_stateSpace hη₂ ha)
  have hdecomp : ∀ a, φ a = ω₁ a - ω₂ a := fun a => by
    have h1 : (s : ℂ) * η₁ a - (t : ℂ) * η₂ a = (‖φ‖ : ℂ)⁻¹ * φ a := by
      have h0 : (WeakDual.toStrongDual (s • η₁ - t • η₂)) a = ψ a :=
        DFunLike.congr_fun hF_eq a
      simpa only [map_sub, sub_apply, WeakDual.toStrongDual_apply,
        WeakDual.real_smul_apply, Complex.real_smul, ψ, smul_apply, smul_eq_mul] using h0
    have h2 : φ a = (‖φ‖ : ℂ) * ((s : ℂ) * η₁ a - (t : ℂ) * η₂ a) := by
      rw [h1, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hφ_pos.ne', Complex.ofReal_one, one_mul]
    rw [h2]
    simp [ω₁, ω₂, Complex.real_smul]
    ring
  have hnorm_sum_le : ‖(ω₁ : D →L[ℂ] ℂ)‖ + ‖(ω₂ : D →L[ℂ] ℂ)‖ ≤ ‖φ‖ := by
    have h1 : ‖(ω₁ : D →L[ℂ] ℂ)‖ = ‖φ‖ * s := by
      rw [PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, norm_smul,
        Real.norm_of_nonneg (mul_nonneg (norm_nonneg φ) hs),
        TauCeti.norm_toStrongDual_of_mem_stateSpace hη₁, mul_one]
    have h2 : ‖(ω₂ : D →L[ℂ] ℂ)‖ = ‖φ‖ * t := by
      rw [PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, norm_smul,
        Real.norm_of_nonneg (mul_nonneg (norm_nonneg φ) ht),
        TauCeti.norm_toStrongDual_of_mem_stateSpace hη₂, mul_one]
    rw [h1, h2, ← mul_add]
    exact mul_le_of_le_one_right (norm_nonneg φ) hst
  have hφ_le_sum : ‖φ‖ ≤ ‖(ω₁ : D →L[ℂ] ℂ)‖ + ‖(ω₂ : D →L[ℂ] ℂ)‖ := by
    have heq : φ = (ω₁ : D →L[ℂ] ℂ) - (ω₂ : D →L[ℂ] ℂ) := ext hdecomp
    rw [heq]
    exact norm_sub_le _ _
  exact ⟨ω₁, ω₂, hdecomp, le_antisymm hnorm_sum_le hφ_le_sum⟩

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem opNorm_ofConv_star_toConv_le {B : Type*} [NonUnitalCStarAlgebra B]
    (φ : B →L[ℂ] ℂ) : ‖(star (WithConv.toConv φ)).ofConv‖ ≤ ‖φ‖ :=
  opNorm_le_bound _ (norm_nonneg φ) fun x => by
    rw [ContinuousLinearMap.intrinsicStar_apply, norm_star]
    exact (φ.le_opNorm (star x)).trans_eq (by rw [norm_star])

/-- **Jordan decomposition of bounded Hermitian functionals.** Every continuous linear functional
`φ : A →L[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra satisfying `φ (star a) = star (φ a)` is the
difference `ω₁ - ω₂` of two positive continuous linear functionals with `‖ω₁‖ + ‖ω₂‖ = ‖φ‖`. -/
theorem exists_sub_positiveContinuousLinearMap_of_map_star (φ : A →L[ℂ] ℂ)
    (hφ : ∀ a, φ (star a) = star (φ a)) :
    ∃ ω₁ ω₂ : A →P[ℂ] ℂ, (∀ a, φ a = ω₁ a - ω₂ a) ∧
      ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ = ‖φ‖ := by
  let i : A →ₗᵢ[ℂ] Unitization ℂ A :=
    ⟨Unitization.inrHom ℂ ℂ A, fun a => Unitization.norm_inr a⟩
  obtain ⟨ψ₀, hψ₀_ext, hψ₀_norm⟩ := i.exists_extension_norm_eq φ
  have hψ₀_apply : ∀ a : A, ψ₀ (a : A⁺¹) = φ a := fun a => DFunLike.congr_fun hψ₀_ext a
  let ψ₀Star : Unitization ℂ A →L[ℂ] ℂ := (star (WithConv.toConv ψ₀)).ofConv
  let ψ : Unitization ℂ A →L[ℂ] ℂ := (2 : ℂ)⁻¹ • (ψ₀ + ψ₀Star)
  have hψ_star : ∀ x, ψ (star x) = star (ψ x) := fun x => by
    simp only [ψ, ψ₀Star, smul_apply, add_apply, ContinuousLinearMap.intrinsicStar_apply,
      star_star, smul_eq_mul, star_mul', star_add, star_inv₀, star_ofNat, add_comm]
  have hψ_ext : ∀ a : A, ψ (a : A⁺¹) = φ a := fun a => by
    have h2 : ψ₀Star (a : A⁺¹) = φ a := by
      dsimp only [ψ₀Star]
      rw [ContinuousLinearMap.intrinsicStar_apply, ← Unitization.inr_star,
        hψ₀_apply (star a), hφ a, star_star]
    simp only [ψ, smul_apply, add_apply, hψ₀_apply a, h2, smul_eq_mul]
    ring
  have hψ_norm : ‖ψ‖ = ‖φ‖ := by
    refine le_antisymm ?_ ?_
    · calc ‖ψ‖ = ‖(2 : ℂ)⁻¹‖ * ‖ψ₀ + ψ₀Star‖ := norm_smul _ _
        _ ≤ 2⁻¹ * (‖ψ₀‖ + ‖ψ₀Star‖) := by
          rw [norm_inv, Complex.norm_ofNat]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
        _ ≤ 2⁻¹ * (‖ψ₀‖ + ‖ψ₀‖) := by gcongr; exact opNorm_ofConv_star_toConv_le ψ₀
        _ = ‖φ‖ := by rw [hψ₀_norm]; ring
    · exact opNorm_le_bound _ (norm_nonneg ψ) fun a => by
        rw [← hψ_ext a]
        exact (ψ.le_opNorm (a : A⁺¹)).trans_eq (by rw [Unitization.norm_inr])
  obtain ⟨η₁, η₂, hη_eq, hη_norm⟩ := exists_sub_positiveContinuousLinearMap_unital ψ hψ_star
  let j : A →P[ℂ] Unitization ℂ A := .ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let ω₁ : A →P[ℂ] ℂ := η₁.comp j
  let ω₂ : A →P[ℂ] ℂ := η₂.comp j
  have hω_eq : ∀ a, φ a = ω₁ a - ω₂ a := fun a => by
    simp [ω₁, ω₂, j, ← hψ_ext a, hη_eq (a : A⁺¹)]
  have hω_le : ∀ η : Unitization ℂ A →P[ℂ] ℂ,
      ‖((η.comp j : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ ≤ ‖(η : Unitization ℂ A →L[ℂ] ℂ)‖ := fun η =>
    opNorm_le_bound _ (norm_nonneg _) fun a => by
      have h := (η : Unitization ℂ A →L[ℂ] ℂ).le_opNorm (a : A⁺¹)
      rwa [Unitization.norm_inr] at h
  have hsum_le : ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ :=
    (add_le_add (hω_le η₁) (hω_le η₂)).trans (by rw [hη_norm, hψ_norm])
  have hφ_le : ‖φ‖ ≤ ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ := by
    have heq : φ = (ω₁ : A →L[ℂ] ℂ) - (ω₂ : A →L[ℂ] ℂ) := ext hω_eq
    rw [heq]
    exact norm_sub_le _ _
  exact ⟨ω₁, ω₂, hω_eq, le_antisymm hsum_le hφ_le⟩

/-- **Four-positive decomposition of bounded linear functionals.** Every continuous linear
functional `φ : A →L[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra is a complex linear combination
`φ = (ω₁ - ω₂) + i (ω₃ - ω₄)` of four positive continuous linear functionals with
`‖ω₁‖ + ‖ω₂‖ ≤ ‖φ‖` and `‖ω₃‖ + ‖ω₄‖ ≤ ‖φ‖`. -/
theorem exists_four_positiveContinuousLinearMap (φ : A →L[ℂ] ℂ) :
    ∃ ω₁ ω₂ ω₃ ω₄ : A →P[ℂ] ℂ,
      (∀ a, φ a = (ω₁ a - ω₂ a) + Complex.I * (ω₃ a - ω₄ a)) ∧
      ‖(ω₁ : A →L[ℂ] ℂ)‖ + ‖(ω₂ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ ∧
      ‖(ω₃ : A →L[ℂ] ℂ)‖ + ‖(ω₄ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ := by
  let φStar : A →L[ℂ] ℂ := (star (WithConv.toConv φ)).ofConv
  let φR : A →L[ℂ] ℂ := (2 : ℂ)⁻¹ • (φ + φStar)
  let φI : A →L[ℂ] ℂ := (2 * Complex.I)⁻¹ • (φ - φStar)
  have hφR_star : ∀ a, φR (star a) = star (φR a) := fun a => by
    simp only [φR, φStar, smul_apply, add_apply, ContinuousLinearMap.intrinsicStar_apply,
      star_star, smul_eq_mul, star_mul', star_add, star_inv₀, star_ofNat]
    ring
  have hφI_star : ∀ a, φI (star a) = star (φI a) := fun a => by
    simp only [φI, φStar, smul_apply, sub_apply, ContinuousLinearMap.intrinsicStar_apply,
      star_star, smul_eq_mul, star_mul', star_sub, star_inv₀, star_ofNat, Complex.star_def,
      Complex.conj_I, RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring
  have hφR_norm : ‖φR‖ ≤ ‖φ‖ := by
    calc ‖φR‖ = ‖(2 : ℂ)⁻¹‖ * ‖φ + φStar‖ := norm_smul _ _
      _ ≤ 2⁻¹ * (‖φ‖ + ‖φStar‖) := by
        rw [norm_inv, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ 2⁻¹ * (‖φ‖ + ‖φ‖) := by gcongr; exact opNorm_ofConv_star_toConv_le φ
      _ = ‖φ‖ := by ring
  have hφI_norm : ‖φI‖ ≤ ‖φ‖ := by
    calc ‖φI‖ = ‖(2 * Complex.I)⁻¹‖ * ‖φ - φStar‖ := norm_smul _ _
      _ ≤ 2⁻¹ * (‖φ‖ + ‖φStar‖) := by
        rw [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ 2⁻¹ * (‖φ‖ + ‖φ‖) := by gcongr; exact opNorm_ofConv_star_toConv_le φ
      _ = ‖φ‖ := by ring
  obtain ⟨ω₁, ω₂, hR_eq, hR_norm⟩ := φR.exists_sub_positiveContinuousLinearMap_of_map_star hφR_star
  obtain ⟨ω₃, ω₄, hI_eq, hI_norm⟩ := φI.exists_sub_positiveContinuousLinearMap_of_map_star hφI_star
  refine ⟨ω₁, ω₂, ω₃, ω₄, fun a => ?_, hR_norm.trans_le hφR_norm, hI_norm.trans_le hφI_norm⟩
  rw [← hR_eq a, ← hI_eq a]
  simp only [φR, φI, smul_apply, add_apply, sub_apply, smul_eq_mul]
  have h2I : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  field_simp [h2I]
  ring

end JordanDecomposition

end ContinuousLinearMap

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A net in a C⋆-algebra converges weakly if and only if its image under every positive continuous
linear functional converges. -/
theorem tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap
    {ι : Type*} {l : Filter ι} {u : ι → A} {x : A} :
    Tendsto (fun i => toWeakSpace ℂ A (u i)) l (𝓝 (toWeakSpace ℂ A x)) ↔
      ∀ ω : A →P[ℂ] ℂ, Tendsto (fun i => ω (u i)) l (𝓝 (ω x)) := by
  rw [TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto]
  refine ⟨fun h ω => h (ω : A →L[ℂ] ℂ), fun h φ => ?_⟩
  obtain ⟨ω₁, ω₂, ω₃, ω₄, hφ, -, -⟩ := φ.exists_four_positiveContinuousLinearMap
  simp_rw [hφ]
  exact ((h ω₁).sub (h ω₂)).add (((h ω₃).sub (h ω₄)).const_mul Complex.I)

end TauCeti.CStarAlgebra

end
