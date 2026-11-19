/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.ContMDiff
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# The logarithmic gauge is a biholomorphism of punctured families

Let `P : D_t → (Λ →ₗ[ℤ] E)` be a `C^n` family of full period lattices over the disc `D_t` of
radius `r ^ m`, with family of tori `Y = (D_t × E)/Λ`, and let `X = (D_z × E)/Λ` be its pullback
along `z ↦ z ^ m` (`TauCeti.powPullbackPeriod`), on which the `m`-th roots of unity act by the
normalized pure translation `ζ • [z, e] = [ζ z, e + (log ζ / 2πi) • P (z ^ m) l]`
(`TauCeti.logTranslationMulAction`). When this action is free, a condition on the central torus
only (`TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff`), the orbit space
`Q = X / C_m` is a `C^n` manifold for the quotient atlas
(`TauCeti.isManifold_torusFamilyAffineQuotient`), and `Y` is a `C^n` manifold
(`TauCeti.isManifold_torusFamily`).

Over the punctured disc, the logarithmic gauge
`[[z, e]] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]` is an equivalence
`Q* ≃ Y*` (`TauCeti.torusFamilyLogGaugeEquiv`). This file proves that it is a `C^n`
diffeomorphism (`TauCeti.torusFamilyLogGaugeDiffeomorph`) of the open submanifolds
`Q* = {t ≠ 0}` (`TauCeti.logTranslationQuotientPuncturedOpens`) and `Y* = {t ≠ 0}`
(`TauCeti.torusFamilyPuncturedOpens`). With holomorphic periods and `n = ω` it is a
biholomorphism: the punctured cyclic quotient is biholomorphic, over the punctured disc, to the
punctured family it was built from. The period family `P` varies throughout.

Near a point of `Q*`, the gauge is the upstairs gauge `TauCeti.torusFamilyLogGauge`, holomorphic
off the central fibre (`TauCeti.contMDiffAt_torusFamilyLogGauge`), composed with a local inverse
of the orbit map `X → Q`, a local biholomorphism. Near a point `[t₀, e₀]` of `Y*` the inverse is
`[t, e] ↦ [[w t, e + (L t / 2πi) • P t l]]` for the holomorphic branch
`L t = log z₀ + (1 / m) log (t / t₀)` of the logarithm of an `m`-th root `w t = exp (L t)` of
`t`, where `z₀ ^ m = t₀`, composed with a local inverse of the orbit map `D_t × E → Y`.

## Main definitions

* `TauCeti.torusFamilyPuncturedOpens`: the punctured family `Y*` as an open subset of `Y`.
* `TauCeti.logTranslationQuotientPuncturedOpens`: the punctured cyclic quotient `Q*` as an open
  subset of `Q`.
* `TauCeti.torusFamilyLogGaugeDiffeomorph`: the logarithmic gauge as a `C^n` diffeomorphism
  `Q* ≃ Y*`.

## Main results

* `TauCeti.torusFamilyLogGaugeDiffeomorph_mk`, `TauCeti.torusFamilyLogGaugeDiffeomorph_symm_mk`:
  the diffeomorphism and its inverse on representatives, with any root and branch.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*,
  second edition, Chapter V, section on logarithmic transformations.
-/

public section

open MulAction Complex TopologicalSpace
open scoped Manifold ContDiff Real

namespace TauCeti

/-! ### The punctured families as open subsets -/

section Opens

variable {m : ℕ} {r : ℝ} {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  [TopologicalSpace E] (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)

/-- **The punctured family** `Y* = {t ≠ 0}`: the open subset of the family of tori
`Y = (D_t × E)/Λ` lying over the punctured disc. -/
@[expose] def torusFamilyPuncturedOpens :
    letI := periodAddAction P
    Opens (AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)) :=
  letI := periodAddAction P
  ⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtypeVal.comp (continuous_torusFamilyProjection P))
      continuous_const⟩

@[simp] theorem mem_torusFamilyPuncturedOpens
    {y : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)} :
    y ∈ torusFamilyPuncturedOpens P ↔
      ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0 :=
  Iff.rfl

variable [NeZero m] [Module ℂ E] (l : Λ)

/-- **The punctured cyclic quotient** `Q* = {t ≠ 0}`: the open subset of the orbit space
`Q = X / C_m` of the normalized pure translation action `TauCeti.logTranslationMulAction` on
which the coordinate `t = z ^ m` (`TauCeti.torusFamilyCyclicQuotientProjection`) is nonzero. -/
@[expose] def logTranslationQuotientPuncturedOpens :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    Opens (orbitRel.Quotient (rootsOfUnity m ℂ)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := logTranslationMulAction P l
  ⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (logTranslationSection_mul P l) q ≠ 0}, by
    rw [torusFamilyCyclicQuotientProjection_eq_torusFamilyAffineQuotientLift]
    exact isOpen_ne_fun (continuous_torusFamilyAffineQuotientLift _ _ _ _ _ _ _ _ _
      ((continuous_pow m).comp continuous_subtypeVal)) continuous_const⟩

@[simp] theorem mem_logTranslationQuotientPuncturedOpens
    {q : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))} :
    q ∈ logTranslationQuotientPuncturedOpens P l ↔
      torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l) q ≠ 0 :=
  Iff.rfl

end Opens

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E) (l : Λ)
  [FiniteDimensional ℂ E] [∀ t, DiscreteTopology (LinearMap.range (P t))]
  [∀ t, IsZLattice ℝ (LinearMap.range (P t))] {n : ℕ∞ω}
  (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun t ↦ P t l) (hinj : ∀ t, Function.Injective (P t))

/-! ### The logarithmic gauge is a diffeomorphism -/

variable (hr : 0 ≤ r)
  (hfree : letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))

/-- The orbit map `X → Q` of the normalized action is a `C^n` local diffeomorphism. -/
private theorem isLocalDiffeomorph_logTranslationQuotient_mk :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    IsLocalDiffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (Quotient.mk (orbitRel (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) :=
  isLocalDiffeomorph_torusFamilyAffineQuotient_mk (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l ↦ contMDiff_powPullbackPeriod P (hP l)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l) (fun _ ↦ contMDiff_snd)
    (contMDiff_logTranslationSection P hP hinj l) hfree

/-- The logarithmic gauge `Q* → Y*` is `C^n`. Near the orbit of a point `x₀` over `z₀ ≠ 0`, it is
the upstairs gauge `TauCeti.torusFamilyLogGauge` composed with a local inverse of the orbit map
`X → Q`. -/
private theorem contMDiff_torusFamilyLogGaugeEquiv :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    ContMDiff (M := logTranslationQuotientPuncturedOpens P l) (M' := torusFamilyPuncturedOpens P)
      (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (torusFamilyLogGaugeEquiv P l hr) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
    (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
  rintro ⟨q₀, hq₀⟩
  obtain ⟨x₀, rfl⟩ := Quotient.mk_surjective q₀
  have hx₀ :
      ((torusFamilyProjection (powPullbackPeriod m r P) x₀ : rootsOfUnityBall m r) : ℂ) ≠ 0 :=
    fun h ↦ (mem_logTranslationQuotientPuncturedOpens P l).1 hq₀ (by
      rw [torusFamilyCyclicQuotientProjection_mk, h, zero_pow (NeZero.ne m)])
  refine (ContMDiffAt.subtypeVal_comp_iff (torusFamilyPuncturedOpens P) _ _).1 ?_
  exact (isLocalDiffeomorph_logTranslationQuotient_mk P l hP hinj hfree x₀).contMDiffAt_of_forall_eq
    le_rfl _ hq₀ (contMDiffAt_torusFamilyLogGauge P hP hinj l hx₀)
    fun x hx ↦ torusFamilyLogGaugeEquiv_mk P l hr x hx

/-- **The inverse of the logarithmic gauge in local form.** Near `(t₀, e₀)` with `t₀ ≠ 0`, the
inverse of the logarithmic gauge composed with the orbit map `D_t × E → Y` is the `C^n` map
`(t, e) ↦ [[w t, e + (L t / 2πi) • P t l]]`, for the holomorphic branch
`L t = log z₀ + (1 / m) log (t / z₀ ^ m)` of the logarithm of the `m`-th root `w t = exp (L t)`
of `t`, where `z₀ ^ m = t₀`. -/
private theorem exists_contMDiffAt_eq_torusFamilyLogGaugeEquiv_symm_mk
    {t₀ : Metric.ball (0 : ℂ) (r ^ m)} (ht₀ : (t₀ : ℂ) ≠ 0) (e₀ : E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    ∃ F : Metric.ball (0 : ℂ) (r ^ m) × E → orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)),
      ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n F (t₀, e₀) ∧
        ∀ t e (ht : ((torusFamilyProjection P (Quotient.mk _ (t, e)) :
          Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0),
          F (t, e) = (torusFamilyLogGaugeEquiv P l hr).symm ⟨Quotient.mk _ (t, e), ht⟩ := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
    (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
  set z₀ := rootsOfUnityBall.rootMap hr t₀
  have hz₀m : (z₀ : ℂ) ^ m = t₀ := by
    rw [← rootsOfUnityBall.coe_powMap, rootsOfUnityBall.powMap_rootMap]
  have hz₀ : (z₀ : ℂ) ≠ 0 := fun h ↦ ht₀ (by rw [← hz₀m, h, zero_pow (NeZero.ne m)])
  let L : ℂ → ℂ := fun t ↦ log z₀ + (m : ℂ)⁻¹ * log (t / (z₀ : ℂ) ^ m)
  let w : Metric.ball (0 : ℂ) (r ^ m) → rootsOfUnityBall m r := fun t ↦
    ⟨exp (L t), exp_log_add_inv_mul_log_div_pow_mem_rootsOfUnityBall hz₀ t⟩
  have hL₀ : ContDiffAt ℂ n L t₀ :=
    contDiffAt_const.add (contDiffAt_const.mul ((Complex.contDiffAt_log
      (by rw [hz₀m, div_self ht₀]; exact one_mem_slitPlane)).comp _
        (contDiffAt_id.div_const _)))
  have hLc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n (fun t : Metric.ball (0 : ℂ) (r ^ m) ↦ L t) t₀ :=
    hL₀.contMDiffAt.comp t₀ contMDiff_subtypeVal_ball.contMDiffAt
  -- The root `w` is `C^n` because its composite with the inclusion of the disc is `exp ∘ L`.
  have hwc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n w t₀ :=
    contMDiffWithinAt_univ.1 <| ContMDiffWithinAt.of_comp_isLocalDiffeomorph
      (isLocalDiffeomorph_coe_rootsOfUnityBall (w t₀))
      (Topology.IsInducing.subtypeVal.continuousAt_iff.2 hLc.continuousAt.cexp).continuousWithinAt
      (contDiff_exp.contMDiff.contMDiffAt.comp t₀ hLc).contMDiffWithinAt
  have h₂ : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ, E) n
      (fun p : Metric.ball (0 : ℂ) (r ^ m) × E ↦ p.2 + (L p.1 / (2 * π * I)) • P p.1 l)
      (t₀, e₀) :=
    contMDiffAt_snd.add (ContMDiffAt.smul (I := 𝓘(ℂ))
      (((hL₀.div_const (2 * π * I)).contMDiffAt.comp t₀
        contMDiff_subtypeVal_ball.contMDiffAt).comp (t₀, e₀) contMDiffAt_fst)
      ((hP l).contMDiffAt.comp (t₀, e₀) contMDiffAt_fst))
  refine ⟨fun p ↦ Quotient.mk _ (Quotient.mk _ (w p.1, p.2 + (L p.1 / (2 * π * I)) • P p.1 l)),
    (isLocalDiffeomorph_logTranslationQuotient_mk P l hP hinj hfree).contMDiff.contMDiffAt.comp _
      ((isLocalDiffeomorph_torusFamily_mk _ (fun z ↦ powPullbackPeriod_injective P z (hinj _))
        (fun l ↦ contMDiff_powPullbackPeriod P (hP l))).contMDiff.contMDiffAt.comp _
        ((hwc.comp (t₀, e₀) contMDiffAt_fst).prodMk h₂)), fun t e ht ↦ ?_⟩
  have ht' : (t : ℂ) ≠ 0 := by rwa [torusFamilyProjection_mk] at ht
  refine (torusFamilyLogGaugeEquiv_symm_mk P l hr (Subtype.ext ?_) rfl e ht).symm
  rw [rootsOfUnityBall.coe_powMap]
  exact exp_log_add_inv_mul_log_div_pow hz₀ ht'

/-- The inverse `Y* → Q*` of the logarithmic gauge is `C^n`: near each point it is the local form
`TauCeti.exists_contMDiffAt_eq_torusFamilyLogGaugeEquiv_symm_mk` composed with a local inverse of
the orbit map `D_t × E → Y`. -/
private theorem contMDiff_torusFamilyLogGaugeEquiv_symm :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    ContMDiff (M := torusFamilyPuncturedOpens P) (M' := logTranslationQuotientPuncturedOpens P l)
      (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (torusFamilyLogGaugeEquiv P l hr).symm := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
    (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
  rintro ⟨y₀, hy₀⟩
  obtain ⟨⟨t₀, e₀⟩, rfl⟩ := Quotient.mk_surjective y₀
  have ht₀ : (t₀ : ℂ) ≠ 0 := by
    rwa [mem_torusFamilyPuncturedOpens, torusFamilyProjection_mk] at hy₀
  obtain ⟨F, hF, hFeq⟩ :=
    exists_contMDiffAt_eq_torusFamilyLogGaugeEquiv_symm_mk P l hP hinj hr hfree ht₀ e₀
  refine (ContMDiffAt.subtypeVal_comp_iff (logTranslationQuotientPuncturedOpens P l) _ _).1 ?_
  exact (isLocalDiffeomorph_torusFamily_mk P hinj hP (t₀, e₀)).contMDiffAt_of_forall_eq le_rfl _
    hy₀ hF fun p hp ↦ (hFeq p.1 p.2 hp).symm

/-- **The logarithmic gauge is a diffeomorphism.** Let `P` be a `C^n` family of full period
lattices over the disc of radius `r ^ m`, and suppose the normalized pure translation action of the
`m`-th roots of unity on its pullback `X` along `z ↦ z ^ m` is free, so that `Q = X / C_m` is a
`C^n` manifold. Then the logarithmic gauge
`[[z, e]] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]` is a `C^n` diffeomorphism from the punctured
cyclic quotient `Q* = {t ≠ 0}` onto the punctured family `Y* = {t ≠ 0}`, lying over the identity
of the punctured disc (`TauCeti.coe_torusFamilyProjection_torusFamilyLogGaugeEquiv`). With
holomorphic periods and `n = ω` it is a biholomorphism. Its underlying equivalence is
`TauCeti.torusFamilyLogGaugeEquiv`. -/
noncomputable def torusFamilyLogGaugeDiffeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    logTranslationQuotientPuncturedOpens P l ≃ₘ^n⟮𝓘(ℂ).prod 𝓘(ℂ, E), 𝓘(ℂ).prod 𝓘(ℂ, E)⟯
      torusFamilyPuncturedOpens P :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  letI := logTranslationMulAction P l
  letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
    (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
  { toEquiv := torusFamilyLogGaugeEquiv P l hr
    contMDiff_toFun := contMDiff_torusFamilyLogGaugeEquiv P l hP hinj hr hfree
    contMDiff_invFun := contMDiff_torusFamilyLogGaugeEquiv_symm P l hP hinj hr hfree }

/-- The diffeomorphism has the underlying equivalence `TauCeti.torusFamilyLogGaugeEquiv`. -/
@[simp] theorem torusFamilyLogGaugeDiffeomorph_toEquiv :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    (torusFamilyLogGaugeDiffeomorph P l hP hinj hr hfree).toEquiv =
      torusFamilyLogGaugeEquiv P l hr :=
  (rfl)

/-- The diffeomorphism is the function `TauCeti.torusFamilyLogGaugeEquiv`. -/
@[simp] theorem coe_torusFamilyLogGaugeDiffeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    ⇑(torusFamilyLogGaugeDiffeomorph P l hP hinj hr hfree) = torusFamilyLogGaugeEquiv P l hr :=
  (rfl)

/-- The inverse of the diffeomorphism is the inverse of `TauCeti.torusFamilyLogGaugeEquiv`. -/
@[simp] theorem coe_torusFamilyLogGaugeDiffeomorph_symm :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    ⇑(torusFamilyLogGaugeDiffeomorph P l hP hinj hr hfree).symm =
      (torusFamilyLogGaugeEquiv P l hr).symm :=
  (rfl)

/-- The logarithmic gauge on the class of a point over `z ≠ 0`. -/
theorem torusFamilyLogGaugeDiffeomorph_mk
    (x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) (hx) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    (torusFamilyLogGaugeDiffeomorph P l hP hinj hr hfree ⟨Quotient.mk _ x, hx⟩ :
        AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)) =
      torusFamilyLogGauge P l x :=
  torusFamilyLogGaugeEquiv_mk P l hr x hx

/-- The logarithmic gauge lies over the identity of the punctured disc: the image of a point of
`Q*` with coordinate `t` lies over `t`. -/
theorem coe_torusFamilyProjection_torusFamilyLogGaugeDiffeomorph
    (q : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      logTranslationQuotientPuncturedOpens P l) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    ((torusFamilyProjection P (torusFamilyLogGaugeDiffeomorph P l hP hinj hr hfree q).val :
      Metric.ball (0 : ℂ) (r ^ m)) : ℂ) =
      torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l) q.val :=
  coe_torusFamilyProjection_torusFamilyLogGaugeEquiv P l hr q

/-- **The inverse of the logarithmic gauge**, with any root and branch: if `z ^ m = t` and
`exp L = z`, it sends `[t, e]` to the class of `[z, e + (L / 2πi) • P t l]`. -/
theorem torusFamilyLogGaugeDiffeomorph_symm_mk {t : Metric.ball (0 : ℂ) (r ^ m)}
    {z : rootsOfUnityBall m r} (hz : rootsOfUnityBall.powMap m r z = t) {L : ℂ}
    (hL : exp L = (z : ℂ)) (e : E) (ht) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _)) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous) (fun _ ↦ continuous_snd)
      (fun ζ ↦ (contMDiff_logTranslationSection P hP hinj l ζ).continuous) hfree
    ((torusFamilyLogGaugeDiffeomorph P l hP hinj hr hfree).symm ⟨Quotient.mk _ (t, e), ht⟩ :
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) =
      Quotient.mk _ (Quotient.mk _ (z, e + (L / (2 * π * I)) • P t l)) :=
  torusFamilyLogGaugeEquiv_symm_mk P l hr hz hL e ht

end TauCeti
