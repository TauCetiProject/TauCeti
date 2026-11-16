/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.ContMDiff
public import TauCeti.Algebra.Module.ZLattice.Family.RotatedDisc

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# The downstairs logarithmic gauge diffeomorphism

Let `D_t` be the disc of radius `r ^ m` about `0` in `ℂ` and `P : D_t → (Λ →ₗ[ℤ] E)` a `C^n`
family of full period lattices, with family of tori `Y = (D_t × E)/Λ`. Pulling back along
`z ↦ z ^ m` from the disc `D_z` of radius `r` gives the family `X = (D_z × E)/Λ` carrying the
normalized pure translation action `TauCeti.logTranslationMulAction` for a lattice vector `l : Λ`,
`ζ • [z, e] = [ζ z, e + (log ζ / 2πi) • P (z ^ m) l]`.

This file upgrades the logarithmic gauge homeomorphism `TauCeti.torusFamilyLogGaugeHomeomorph` on
the punctured cyclic quotient `Q* ⊆ Q = X / C_m` to a `C^n` diffeomorphism onto the punctured
family `Y* ⊆ Y` over `D_t*` (a biholomorphism when `n = ω` and `P` is holomorphic):

* **Freeness.** Over a disc of positive radius with injective central periods,
  `TauCeti.logTranslationMulAction` is free exactly when the class of `l` in `Λ ⧸ mΛ` has exact
  additive order `m` (`TauCeti.isCancelSMul_logTranslationMulAction_iff`).
* **Downstairs diffeomorphism.** For `C^n` periods, each normalized translation section is `C^n`
  (`TauCeti.contMDiff_logTranslationSection`), and when the action is free the logarithmic gauge
  `[[z, e]] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]` is a `C^n` diffeomorphism
  `TauCeti.torusFamilyLogGaugeDiffeomorph : Q* ≃ₘ^n Y*` between the punctured open submanifolds
  over `D_t*`.

## Main definitions

* `TauCeti.logTranslationQuotientChartedSpace`: the quotient atlas on `Q = X / C_m` for a free
  normalized pure translation action.
* `TauCeti.torusFamilyLogGaugeDiffeomorph`: the downstairs `C^n` diffeomorphism (biholomorphism for
  `n = ω`) `Q* ≃ₘ^n Y*` over `D_t*`.

## Main results

* `TauCeti.isCancelSMul_logTranslationMulAction_iff`: freeness of `logTranslationMulAction` is
  exact order `m` of `[l]` in `Λ ⧸ mΛ`.
* `TauCeti.continuous_logTranslationSection`, `TauCeti.contMDiff_logTranslationSection`:
  continuity and `C^n` regularity of the normalized translation sections.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, and A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*.
-/

public section

open MulAction Set Filter Topology Complex
open scoped Manifold ContDiff Real

namespace TauCeti

/-! ### Freeness and continuity of the normalized action -/

section NormalizedAction

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  [Module ℂ E] (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)

/-- **Freeness of the normalized action.** Over a disc of positive radius whose central periods
`P 0` are injective, the normalized pure translation action for `l : Λ` is free exactly when the
class of `l` in `Λ ⧸ mΛ` has exact additive order `m`. -/
theorem isCancelSMul_logTranslationMulAction_iff (hr : 0 < r)
    (hinj : Function.Injective (P ⟨0, mem_ball_zero_iff.2 (by simpa using pow_pos hr m)⟩))
    (l : Λ) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) ↔
      addOrderOf (Submodule.Quotient.mk l : QuotSMulTop (m : ℤ) Λ) = m := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := logTranslationMulAction P l
  let u₀ : rootsOfUnityBall m r := ⟨0, mem_rootsOfUnityBall.2 (by simpa using hr)⟩
  have hu₀ : (u₀ : ℂ) = 0 := rfl
  have hpow₀ : rootsOfUnityBall.powMap m r u₀ =
      ⟨0, mem_ball_zero_iff.2 (by simpa using pow_pos hr m)⟩ :=
    Subtype.ext (by simp [u₀, zero_pow (NeZero.ne m)])
  have hprimℂ : IsPrimitiveRoot (exp (2 * π * I / m)) m :=
    Complex.isPrimitiveRoot_exp m (NeZero.ne m)
  let ζ : rootsOfUnity m ℂ := hprimℂ.toRootsOfUnity
  have hζval : exp (2 * π * I / m) = ((ζ : ℂˣ) : ℂ) := hprimℂ.val_toRootsOfUnity_coe.symm
  have hζprim : IsPrimitiveRoot ζ m := by
    rw [IsPrimitiveRoot.iff_orderOf, ← Subgroup.orderOf_coe, ← orderOf_units, ← hζval]
    exact hprimℂ.eq_orderOf.symm
  have hmE : Function.Injective fun v : E ↦ m • v := fun v w h ↦ by
    dsimp only at h
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact smul_right_injective E (Nat.cast_ne_zero.2 (NeZero.ne m)) h
  have hβ : logTranslationSection P l ζ u₀ =
      Quotient.mk _ (u₀, (m : ℂ)⁻¹ • powPullbackPeriod m r P u₀ l) := by
    rw [logTranslationSection_eq_mk_of_exp_eq P l hζval,
      smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ, div_div_cancel_left₀ two_pi_I_ne_zero]
  have hl : powPullbackPeriod m r P u₀ l =
      m • ((m : ℂ)⁻¹ • powPullbackPeriod m r P u₀ l) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (NeZero.ne m))]
  exact isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_mk_eq
    (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
    (powPullbackPeriod m r P) (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ)
    (powPullbackPeriod_smul_apply P) (logTranslationSection P l)
    (torusFamilyProjection_logTranslationSection P l) (logTranslationSection_mul P l)
    hu₀ hζprim (fun _ ↦ rfl) (by simpa only [powPullbackPeriod_apply, hpow₀] using hinj)
    hmE hβ hl

/-- Each translation section of the normalized pure translation action is continuous for continuous
periods. -/
theorem continuous_logTranslationSection [TopologicalSpace E] [ContinuousSMul ℂ E] {l : Λ}
    (hcont : Continuous fun t ↦ P t l) (ζ : rootsOfUnity m ℂ) :
    letI := periodAddAction (powPullbackPeriod m r P)
    Continuous (logTranslationSection P l ζ) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  have heq : logTranslationSection P l ζ = fun z ↦
      Quotient.mk _ (ζ • z, (log ((ζ : ℂˣ) : ℂ) / (2 * π * I)) • powPullbackPeriod m r P z l) :=
    funext fun z ↦ logTranslationSection_eq_mk_of_exp_eq P l (exp_log (ζ : ℂˣ).ne_zero) z
  rw [heq]
  exact continuous_quotient_mk'.comp
    ((continuous_const_smul ζ).prodMk
      (continuous_const.smul (continuous_powPullbackPeriod P hcont)))

end NormalizedAction

/-! ### The downstairs logarithmic gauge diffeomorphism -/

section DownstairsDiffeomorph

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)
  [∀ t, DiscreteTopology (LinearMap.range (P t))]
  [∀ t, IsZLattice ℝ (LinearMap.range (P t))]
  (hinj : ∀ t, Function.Injective (P t))

/-- The quotient atlas `TauCeti.torusFamilyAffineQuotientChartedSpace` specialized to the
normalized pure translation action `TauCeti.logTranslationMulAction`. -/
@[expose, instance_reducible]
noncomputable def logTranslationQuotientChartedSpace
    (hcont : ∀ l', Continuous fun t ↦ P t l') (l : Λ)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ChartedSpace (ModelProd ℂ E)
      (orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
  torusFamilyAffineQuotientChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun _ _ ↦ AddMonoidHom.id E) (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ)
    (powPullbackPeriod_smul_apply P) (logTranslationSection P l)
    (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun l' ↦ continuous_powPullbackPeriod P (hcont l'))
    (fun _ ↦ continuous_snd)
    (fun ζ ↦ continuous_logTranslationSection P (hcont l) ζ) hfree

variable {n : ℕ∞ω} (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun t ↦ P t l)

/-- Each translation section of the normalized pure translation action is `C^n` for a `C^n` period
family (holomorphic for `n = ω`). -/
theorem contMDiff_logTranslationSection (l : Λ) (ζ : rootsOfUnity m ℂ) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (logTranslationSection P l ζ) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  have heq : logTranslationSection P l ζ = fun z ↦
      Quotient.mk _ (ζ • z, (log ((ζ : ℂˣ) : ℂ) / (2 * π * I)) • powPullbackPeriod m r P z l) :=
    funext fun z ↦ logTranslationSection_eq_mk_of_exp_eq P l (exp_log (ζ : ℂˣ).ne_zero) z
  rw [heq]
  exact (isLocalDiffeomorph_torusFamily_mk (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
      (fun l' ↦ contMDiff_powPullbackPeriod P (hP l'))).contMDiff.comp
    ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := n) ζ).prodMk
      ((contMDiff_const (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (c := log ((ζ : ℂˣ) : ℂ) / (2 * π * I))).smul
        (contMDiff_powPullbackPeriod P (hP l))))

/-- The forward logarithmic gauge `Q* → Y*` is `C^n` for the open-submanifold atlases inherited
from `Q` and `Y`. -/
private theorem contMDiff_torusFamilyLogGaugeEquiv (l : Λ) (hr : 0 ≤ r)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
        TopologicalSpace.Opens _)
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (torusFamilyLogGaugeEquiv P l hr) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
  let UY : TopologicalSpace.Opens _ :=
    ⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
      isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UY
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  let UQ : TopologicalSpace.Opens _ :=
    ⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l) q ≠ 0},
      isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UQ
  refine (ContMDiff.subtypeVal_comp_iff UY _).1 fun q ↦ ?_
  rcases q with ⟨qval, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep qval
  have hx : ((torusFamilyProjection (powPullbackPeriod m r P) x :
      rootsOfUnityBall m r) : ℂ) ≠ 0 := fun h ↦
    hq (by rw [torusFamilyCyclicQuotientProjection_mk, h, zero_pow (NeZero.ne m)])
  refine (contMDiffAt_extend_subtypeVal_iff (U := UQ)
    (fun _ ↦ torusFamilyLogGauge P l x)).1 ?_
  have hmk := isLocalDiffeomorph_torusFamilyAffineQuotient_mk (H := ℂ) (I := 𝓘(ℂ))
    (powPullbackPeriod m r P) (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l' ↦ contMDiff_powPullbackPeriod P (hP l')) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun _ ↦ contMDiff_snd) (fun ζ ↦ contMDiff_logTranslationSection P hinj hP l ζ) hfree x
  rw [← hmk.contMDiffAt_comp_iff le_rfl]
  refine (contMDiffAt_torusFamilyLogGauge P hP hinj l hx).congr_of_eventuallyEq ?_
  have hopen : IsOpen {x' : AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E) |
      ((torusFamilyProjection (powPullbackPeriod m r P) x' : rootsOfUnityBall m r) : ℂ) ≠ 0} :=
    isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection _))
      continuous_const
  filter_upwards [hopen.mem_nhds hx] with x' hx'
  have hq' : torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (logTranslationSection_mul P l) (Quotient.mk _ x') ≠ 0 := by
    rw [torusFamilyCyclicQuotientProjection_mk]
    exact pow_ne_zero m hx'
  exact (Subtype.val_injective.extend_apply _ _ (⟨Quotient.mk _ x', hq'⟩ : UQ)).trans
    (torusFamilyLogGaugeEquiv_mk P l hr x' hq')

/-- The inverse logarithmic gauge `Y* → Q*` is `C^n` for the open-submanifold atlases inherited
from `Y` and `Q`: near any `[t₀, e₀]` with `t₀ ≠ 0`, it agrees with the local holomorphic branch
`log z₀ + m⁻¹ * log (t / z₀ ^ m)`. -/
private theorem contMDiff_torusFamilyLogGaugeEquiv_symm (l : Λ) (hr : 0 ≤ r)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
        TopologicalSpace.Opens _)
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (torusFamilyLogGaugeEquiv P l hr).symm := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
  let UY : TopologicalSpace.Opens _ :=
    ⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
      isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UY
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  let UQ : TopologicalSpace.Opens _ :=
    ⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l) q ≠ 0},
      isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UQ
  refine (ContMDiff.subtypeVal_comp_iff UQ _).1 fun y ↦ ?_
  rcases y with ⟨yval, hy⟩
  obtain ⟨⟨t₀, e₀⟩, rfl⟩ := Quotient.exists_rep yval
  have ht₀ : (t₀ : ℂ) ≠ 0 := by rwa [torusFamilyProjection_mk] at hy
  set z₀ := rootsOfUnityBall.rootMap hr t₀
  have hz₀m : (z₀ : ℂ) ^ m = t₀ := by
    rw [← rootsOfUnityBall.coe_powMap, rootsOfUnityBall.powMap_rootMap]
  have hz₀ : (z₀ : ℂ) ≠ 0 := fun h ↦ ht₀ (by rw [← hz₀m, h, zero_pow (NeZero.ne m)])
  -- Extend the inverse arbitrarily across `t = 0` so we can descend through the orbit map of `Y`.
  refine (contMDiffAt_extend_subtypeVal_iff (U := UY)
    (fun _ ↦ Quotient.mk _ (Quotient.mk _ (z₀, 0)))).1 ?_
  rw [← (isLocalDiffeomorph_torusFamily_mk P hinj hP (t₀, e₀)).contMDiffAt_comp_iff le_rfl]
  -- Near `t₀`, use the holomorphic branch `L t = log z₀ + m⁻¹ * log (t / z₀ ^ m)`.
  let L : ℂ → ℂ := fun t ↦ log z₀ + (m : ℂ)⁻¹ * log (t / (z₀ : ℂ) ^ m)
  have hmem (t : Metric.ball (0 : ℂ) (r ^ m)) : exp (L t) ∈ rootsOfUnityBall m r := by
    by_cases ht : (t : ℂ) = 0
    · simp only [L, ht, zero_div, log_zero, mul_zero, add_zero, exp_log hz₀]
      exact z₀.2
    · rw [mem_rootsOfUnityBall, ← pow_lt_pow_iff_left₀ (norm_nonneg _) hr (NeZero.ne m),
        ← norm_pow, exp_log_add_inv_mul_log_div_pow hz₀ ht, ← mem_ball_zero_iff]
      exact t.2
  let w : Metric.ball (0 : ℂ) (r ^ m) → rootsOfUnityBall m r := fun t ↦ ⟨exp (L t), hmem t⟩
  have hw {t : Metric.ball (0 : ℂ) (r ^ m)} (ht : (t : ℂ) ≠ 0) :
      rootsOfUnityBall.powMap m r (w t) = t :=
    Subtype.ext (by rw [rootsOfUnityBall.coe_powMap]; exact exp_log_add_inv_mul_log_div_pow hz₀ ht)
  have hLc : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) n
      (fun p : Metric.ball (0 : ℂ) (r ^ m) × E ↦ L p.1) (t₀, e₀) := by
    apply contMDiffAt_const.add
    apply contMDiffAt_const.mul
    exact (Complex.contDiffAt_log (x := 1) one_mem_slitPlane).contMDiffAt.comp_of_eq
      ((contDiff_id.div_const ((z₀ : ℂ) ^ m)).contMDiff.comp
        (contMDiff_subtypeVal_ball.comp contMDiff_fst)).contMDiffAt
      (by simp [hz₀m, ht₀])
  have hwc : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) n
      (fun p : Metric.ball (0 : ℂ) (r ^ m) × E ↦ w p.1) (t₀, e₀) := by
    have hval := isLocalDiffeomorph_coe_rootsOfUnityBall (m := m) (r := r) (n := n) (w t₀)
    have hexp : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) n
        (fun p : Metric.ball (0 : ℂ) (r ^ m) × E ↦ exp (L p.1)) (t₀, e₀) :=
      Complex.contDiff_exp.contMDiff.contMDiffAt.comp _ hLc
    refine (hval.contMDiffAt_localInverse.comp (t₀, e₀) hexp).congr_of_eventuallyEq ?_
    filter_upwards [hexp.continuousAt.preimage_mem_nhds
      hval.localInverse_eventuallyEq_right] with p hp
    exact Subtype.ext hp.symm
  have hmkQ := (isLocalDiffeomorph_torusFamilyAffineQuotient_mk (H := ℂ) (I := 𝓘(ℂ))
    (powPullbackPeriod m r P) (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l' ↦ contMDiff_powPullbackPeriod P (hP l')) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun _ ↦ contMDiff_snd) (fun ζ ↦ contMDiff_logTranslationSection P hinj hP l ζ) hfree).contMDiff
  have hmkX := (isLocalDiffeomorph_torusFamily_mk (powPullbackPeriod m r P)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l' ↦ contMDiff_powPullbackPeriod P (hP l'))).contMDiff
  have hs : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (fun p : Metric.ball (0 : ℂ) (r ^ m) × E ↦
        (Quotient.mk _ (Quotient.mk _ (w p.1, p.2 + (L p.1 / (2 * π * I)) • P p.1 l)) :
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) (t₀, e₀) :=
    (hmkQ.comp hmkX).contMDiffAt.comp (t₀, e₀)
      (hwc.prodMk (contMDiffAt_snd.add
        ((hLc.div_const (2 * π * I)).smul ((hP l).comp contMDiff_fst).contMDiffAt)))
  refine hs.congr_of_eventuallyEq ?_
  have hopen : IsOpen {p : Metric.ball (0 : ℂ) (r ^ m) × E | (p.1 : ℂ) ≠ 0} :=
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
  filter_upwards [hopen.mem_nhds ht₀] with p hp
  have hp' : ((torusFamilyProjection P (Quotient.mk _ p) : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0 :=
    by rwa [torusFamilyProjection_mk]
  exact (Subtype.val_injective.extend_apply _ _ (⟨Quotient.mk _ p, hp'⟩ : UY)).trans
    (torusFamilyLogGaugeEquiv_symm_mk P l hr (hw hp) rfl p.2 hp')

/-- **The downstairs logarithmic gauge diffeomorphism.** For a `C^n` family of full period lattices
`P` over `D_t` and a free normalized pure translation action for `l : Λ`, the logarithmic gauge
`[[z, e]] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]` is a `C^n` diffeomorphism between the
punctured open submanifolds `Q* ⊆ Q` and `Y* ⊆ Y` over `D_t*`. For holomorphic periods (`n = ω`),
this is a biholomorphism over `D_t*`. -/
noncomputable def torusFamilyLogGaugeDiffeomorph (l : Λ) (hr : 0 ≤ r)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
        TopologicalSpace.Opens _)
    Diffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E))
      {q : orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) //
        torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0}
      {y : AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E) //
        ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0} n :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
  letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
    (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
      isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := logTranslationMulAction P l
  letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
    (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l) q ≠ 0},
      isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
      TopologicalSpace.Opens _)
  { toEquiv := torusFamilyLogGaugeEquiv P l hr
    contMDiff_toFun := contMDiff_torusFamilyLogGaugeEquiv P hinj hP l hr hfree
    contMDiff_invFun := contMDiff_torusFamilyLogGaugeEquiv_symm P hinj hP l hr hfree }

/-- The diffeomorphism `torusFamilyLogGaugeDiffeomorph` has underlying equivalence
`torusFamilyLogGaugeEquiv`. -/
@[simp] theorem torusFamilyLogGaugeDiffeomorph_toEquiv (l : Λ) (hr : 0 ≤ r) (hfree) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
        TopologicalSpace.Opens _)
    (torusFamilyLogGaugeDiffeomorph P hinj hP l hr hfree).toEquiv =
      torusFamilyLogGaugeEquiv P l hr := (rfl)

/-- The diffeomorphism `torusFamilyLogGaugeDiffeomorph` has underlying homeomorphism
`torusFamilyLogGaugeHomeomorph`. -/
@[simp] theorem torusFamilyLogGaugeDiffeomorph_toHomeomorph (l : Λ) (hr : 0 ≤ r) (hfree) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
        TopologicalSpace.Opens _)
    (torusFamilyLogGaugeDiffeomorph P hinj hP l hr hfree).toHomeomorph =
      torusFamilyLogGaugeHomeomorph P l hr (fun l' ↦ (hP l').continuous) :=
  Homeomorph.ext fun q ↦
    (congrFun (coe_torusFamilyLogGaugeHomeomorph P l hr (fun l' ↦ (hP l').continuous)) q).symm

/-- Coercing `torusFamilyLogGaugeDiffeomorph` to a function gives `torusFamilyLogGaugeEquiv`. -/
@[simp] theorem coe_torusFamilyLogGaugeDiffeomorph (l : Λ) (hr : 0 ≤ r) (hfree) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
        TopologicalSpace.Opens _)
    ⇑(torusFamilyLogGaugeDiffeomorph P hinj hP l hr hfree) =
      torusFamilyLogGaugeEquiv P l hr := (rfl)

/-- Coercing the inverse of `torusFamilyLogGaugeDiffeomorph` to a function gives the inverse of
`torusFamilyLogGaugeEquiv`. -/
@[simp] theorem coe_torusFamilyLogGaugeDiffeomorph_symm (l : Λ) (hr : 0 ≤ r) (hfree) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{q | torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩ :
        TopologicalSpace.Opens _)
    ⇑(torusFamilyLogGaugeDiffeomorph P hinj hP l hr hfree).symm =
      (torusFamilyLogGaugeEquiv P l hr).symm := (rfl)

/-- The downstairs logarithmic gauge diffeomorphism lies over the identity of the punctured disc. -/
theorem coe_torusFamilyProjection_torusFamilyLogGaugeDiffeomorph (l : Λ) (hr : 0 ≤ r) (hfree) (q) :
    letI := periodAddAction P
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    ((torusFamilyProjection P (torusFamilyLogGaugeDiffeomorph P hinj hP l hr hfree q).1 :
        Metric.ball (0 : ℂ) (r ^ m)) : ℂ) =
      torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l) q.1 :=
  coe_torusFamilyProjection_torusFamilyLogGaugeEquiv P l hr q

end DownstairsDiffeomorph

end TauCeti
