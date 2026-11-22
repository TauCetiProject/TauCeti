/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.ContMDiff
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# The logarithmic gauge is a diffeomorphism

Let `P : D_t → (Λ →ₗ[ℤ] E)` be a `C^n` family of full lattices over the disc `D_t` of radius
`r ^ m`, with family of tori `Y = (D_t × E)/Λ`, and let `X = (D_z × E)/Λ` be its pullback along
`z ↦ z ^ m` from the disc `D_z` of radius `r`. Fix `l : Λ` and suppose that the normalized pure
translation action `TauCeti.logTranslationMulAction` of the `m`-th roots of unity on `X` is free,
so that the cyclic quotient `Q = X / C_m` carries its quotient atlas
(`TauCeti.logTranslationQuotientChartedSpace`) and is a `C^n` manifold
(`TauCeti.isManifold_torusFamilyAffineQuotient`).

The punctured parts `Q* = {t ≠ 0}` of `Q` (`TauCeti.torusFamilyCyclicQuotientNonzeroOpens`) and
`Y* = {t ≠ 0}` of `Y` (`TauCeti.torusFamilyNonzeroOpens`) are open subsets, and carry the
induced open-subset atlases. This file proves that the logarithmic gauge
`TauCeti.torusFamilyLogGaugeEquiv : Q* ≃ Y*`,
`[[z, e]] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]`, is a `C^n` diffeomorphism
(`TauCeti.torusFamilyLogGaugeDiffeomorph`); for holomorphic periods and `n = ω` it is a
biholomorphism of complex manifolds over the punctured disc `D_t*`. It also proves that the
canonical identification between the cyclic quotients for `l + m • μ` and `l` is a `C^n`
diffeomorphism (`TauCeti.logTranslationQuotientAddNsmulDiffeomorph`). The period family keeps
varying throughout.

Both directions are computed locally through the orbit maps, which are local diffeomorphisms.
Upstairs, the gauge is `C^n` off the central fibre (`TauCeti.contMDiffAt_torusFamilyLogGauge`).
Its inverse is `[t, e] ↦ [[z, e + (L / 2πi) • P t l]]` for any `m`-th root `z` of `t` and any
logarithm `L` of `z` (`TauCeti.torusFamilyLogGaugeEquiv_symm_mk`); near `t₀ ≠ 0` the branch
`L t = log z₀ + (1 / m) log (t / z₀ ^ m)` of the logarithm of an `m`-th root of `t` is
holomorphic, and with `z = exp (L t)` the formula is `C^n`.

## Main definitions

* `TauCeti.torusFamilyLogGaugeDiffeomorph`: the logarithmic gauge `Q* ≃ Y*` as a `C^n`
  diffeomorphism, a biholomorphism for holomorphic data.
* `TauCeti.logTranslationQuotientAddNsmulDiffeomorph`: canonical identification of the cyclic
  quotient manifolds for `l + m • μ` and `l`.

## Main results

* `TauCeti.torusFamilyLogGaugeDiffeomorph_mk`, `TauCeti.torusFamilyLogGaugeDiffeomorph_symm_mk`:
  the diffeomorphism and its inverse on representatives, with any root and branch.
* `TauCeti.coe_torusFamilyProjection_torusFamilyLogGaugeDiffeomorph`: it lies over the identity
  of the punctured disc.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*.
-/

public section

open MulAction Complex Filter Topology TopologicalSpace
open scoped Manifold ContDiff Real

namespace TauCeti

/-! ### The downstairs logarithmic gauge diffeomorphism -/

section

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E) {n : ℕ∞ω}
  (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun t ↦ P t l)
  [∀ t, DiscreteTopology (LinearMap.range (P t))]
  [∀ t, IsZLattice ℝ (LinearMap.range (P t))]
  (hinj : ∀ t, Function.Injective (P t))

/-- The cyclic-quotient orbit map `X → Q` is a `C^n` local diffeomorphism for any free normalized
pure translation action. -/
private theorem isLocalDiffeomorph_logTranslationQuotient_mk (l : Λ)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    IsLocalDiffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (Quotient.mk (orbitRel (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  exact isLocalDiffeomorph_torusFamilyAffineQuotient_mk (H := ℂ) (I := 𝓘(ℂ))
    (powPullbackPeriod m r P) (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    (fun l' ↦ contMDiff_powPullbackPeriod P (hP l')) (fun _ _ ↦ AddMonoidHom.id E)
    (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
    (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
    (fun _ ↦ contMDiff_snd) (contMDiff_logTranslationSection P hP hinj l) hfree

section

variable (l : Λ) (hr : 0 ≤ r)
  (hfree : letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P l
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))

/-- A map out of the cyclic quotient which agrees with the logarithmic gauge on the punctured
part is `C^n` at the class of every point over `z ≠ 0`. -/
private theorem contMDiffAt_of_eq_torusFamilyLogGaugeEquiv
    (F : letI := periodAddAction P
      letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) →
        AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E))
    (hF : letI := periodAddAction P
      letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      ∀ q hq, F q = torusFamilyLogGaugeEquiv P l hr ⟨q, hq⟩)
    {x₀ : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)}
    (hx₀ : ((torusFamilyProjection (powPullbackPeriod m r P) x₀ : rootsOfUnityBall m r) : ℂ) ≠ 0) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n F (Quotient.mk _ x₀) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  rw [← (isLocalDiffeomorph_logTranslationQuotient_mk P hP hinj l hfree x₀).contMDiffAt_comp_iff
    le_rfl]
  have hopen : IsOpen {x : AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E) |
      ((torusFamilyProjection (powPullbackPeriod m r P) x : rootsOfUnityBall m r) : ℂ) ≠ 0} :=
    isOpen_ne_fun (continuous_subtypeVal.comp (continuous_torusFamilyProjection _))
      continuous_const
  refine (contMDiffAt_torusFamilyLogGauge P hP hinj l hx₀).congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hx₀] with x hx
  have hq : torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (logTranslationSection_mul P l) (Quotient.mk _ x) ≠ 0 := by
    rw [torusFamilyCyclicQuotientProjection_mk]
    exact pow_ne_zero m hx
  rw [Function.comp_apply, hF _ hq, torusFamilyLogGaugeEquiv_mk]

/-- A map out of the family `Y` which agrees with the inverse of the logarithmic gauge on the
punctured part is `C^n` at the class of every point over `t ≠ 0`. -/
private theorem contMDiffAt_of_eq_torusFamilyLogGaugeEquiv_symm
    (F : letI := periodAddAction P
      letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E) →
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
    (hF : letI := periodAddAction P
      letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      ∀ y hy, F y = (torusFamilyLogGaugeEquiv P l hr).symm ⟨y, hy⟩)
    {t₀ : Metric.ball (0 : ℂ) (r ^ m)} (ht₀ : (t₀ : ℂ) ≠ 0) (e₀ : E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n F (Quotient.mk _ (t₀, e₀)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  rw [← (isLocalDiffeomorph_torusFamily_mk P hinj hP (t₀, e₀)).contMDiffAt_comp_iff le_rfl]
  -- Near `t₀`, use a `C^n` local `m`-th root `w t` of `t` and a `C^n` logarithm `L t`.
  obtain ⟨w, L, hw, hL, hLw⟩ :=
    rootsOfUnityBall.exists_contMDiffAt_powMap_eq_and_exp_eq (n := n) hr ht₀
  have hπ := ((isLocalDiffeomorph_logTranslationQuotient_mk P hP hinj l hfree).contMDiff.comp
    (isLocalDiffeomorph_torusFamily_mk (powPullbackPeriod m r P)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
      (fun l ↦ contMDiff_powPullbackPeriod P (hP l))).contMDiff)
  refine (hπ.contMDiffAt.comp (t₀, e₀) ((hw.comp (t₀, e₀) contMDiffAt_fst).prodMk
    (contMDiffAt_snd.add (((hL.comp (t₀, e₀) contMDiffAt_fst).div_const (2 * π * I)).smul
      ((hP l).comp contMDiff_fst).contMDiffAt)))).congr_of_eventuallyEq ?_
  have hopen : IsOpen {p : Metric.ball (0 : ℂ) (r ^ m) × E | (p.1 : ℂ) ≠ 0} :=
    isOpen_ne_fun (continuous_subtypeVal.comp continuous_fst) continuous_const
  filter_upwards [hopen.mem_nhds ht₀] with p hp
  obtain ⟨t, e⟩ := p
  have hy : ((torusFamilyProjection P (Quotient.mk _ (t, e)) :
      Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0 := by
    rwa [torusFamilyProjection_mk]
  rw [Function.comp_apply, hF _ hy,
    torusFamilyLogGaugeEquiv_symm_mk P l hr (hLw t hp).1 (hLw t hp).2]
  rfl

/-- The logarithmic gauge is `C^n` from the punctured cyclic quotient to the punctured family. -/
private theorem contMDiff_torusFamilyLogGaugeEquiv :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (torusFamilyLogGaugeEquiv P l hr) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (logTranslationSection_mul P l))
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
  intro q
  -- Pass to the ambient manifolds, through the inclusions of the open subsets.
  refine (TauCeti.ContMDiffAt.subtypeVal_comp_iff
    (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    (torusFamilyLogGaugeEquiv P l hr) q).1 ?_
  refine (contMDiffAt_extend_subtypeVal_iff
    (U := torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (logTranslationSection_mul P l))
    (fun _ ↦ (torusFamilyLogGaugeEquiv P l hr q).val)).1 ?_
  obtain ⟨q, hq⟩ := q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  refine contMDiffAt_of_eq_torusFamilyLogGaugeEquiv P hP hinj l hr hfree _
    (fun q hq ↦ Subtype.val_injective.extend_apply _ _ ⟨q, hq⟩) fun h ↦ hq ?_
  rw [torusFamilyCyclicQuotientProjection_mk, h, zero_pow (NeZero.ne m)]

/-- The inverse of the logarithmic gauge is `C^n` from the punctured family to the punctured cyclic
quotient. -/
private theorem contMDiff_torusFamilyLogGaugeEquiv_symm :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (torusFamilyLogGaugeEquiv P l hr).symm := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (logTranslationSection_mul P l))
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
  intro y
  refine (TauCeti.ContMDiffAt.subtypeVal_comp_iff
    (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
      (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (logTranslationSection_mul P l))
    (torusFamilyLogGaugeEquiv P l hr).symm y).1 ?_
  refine (contMDiffAt_extend_subtypeVal_iff
    (U := torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    (fun _ ↦ ((torusFamilyLogGaugeEquiv P l hr).symm y).val)).1 ?_
  obtain ⟨y, hy⟩ := y
  obtain ⟨⟨t, e⟩, rfl⟩ := Quotient.exists_rep y
  exact contMDiffAt_of_eq_torusFamilyLogGaugeEquiv_symm P hP hinj l hr hfree _
    (fun y hy ↦ Subtype.val_injective.extend_apply _ _ ⟨y, hy⟩)
    (by rwa [torusFamilyProjection_mk] at hy) e

/-- **The logarithmic gauge is a diffeomorphism.** For a `C^n` family of periods `P` over the disc
of radius `r ^ m` and `l : Λ` such that the normalized pure translation action
`TauCeti.logTranslationMulAction` on the pulled-back family `X` is free, the logarithmic gauge
`[[z, e]] ↦ [z ^ m, e - (log z / 2πi) • P (z ^ m) l]` from the punctured cyclic quotient
`Q* = {t ≠ 0}` of `Q = X / C_m` to the punctured family `Y* = {t ≠ 0}`
(`TauCeti.torusFamilyLogGaugeEquiv`) is a `C^n` diffeomorphism for the open-subset atlases
induced by the quotient atlases of `Q` and `Y`. For holomorphic periods and `n = ω` it is a
biholomorphism of complex manifolds, lying over the identity of the punctured disc
(`TauCeti.coe_torusFamilyProjection_torusFamilyLogGaugeEquiv`). -/
noncomputable def torusFamilyLogGaugeDiffeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    Diffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E))
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal) n :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  letI := periodAddAction (powPullbackPeriod m r P)
  letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  letI := logTranslationMulAction P l
  letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  letI := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
  letI := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
  { toEquiv := torusFamilyLogGaugeEquiv P l hr
    contMDiff_toFun := contMDiff_torusFamilyLogGaugeEquiv P hP hinj l hr hfree
    contMDiff_invFun := contMDiff_torusFamilyLogGaugeEquiv_symm P hP hinj l hr hfree }

/-- The diffeomorphism has the underlying equivalence `TauCeti.torusFamilyLogGaugeEquiv`. -/
@[simp] theorem torusFamilyLogGaugeDiffeomorph_toEquiv :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    (torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree).toEquiv =
      torusFamilyLogGaugeEquiv P l hr :=
  (rfl)

/-- The diffeomorphism has the logarithmic gauge `TauCeti.torusFamilyLogGaugeEquiv` as its
underlying map. -/
@[simp] theorem coe_torusFamilyLogGaugeDiffeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    ⇑(torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree) = torusFamilyLogGaugeEquiv P l hr :=
  (rfl)

/-- The inverse of the diffeomorphism is the inverse of the logarithmic gauge, computed by
`TauCeti.torusFamilyLogGaugeEquiv_symm_mk`. -/
@[simp] theorem coe_torusFamilyLogGaugeDiffeomorph_symm :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    ⇑(torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree).symm =
      (torusFamilyLogGaugeEquiv P l hr).symm :=
  (rfl)

/-- The diffeomorphism `torusFamilyLogGaugeDiffeomorph` has underlying homeomorphism
`torusFamilyLogGaugeHomeomorph`. -/
@[simp] theorem torusFamilyLogGaugeDiffeomorph_toHomeomorph :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    (torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree).toHomeomorph =
      torusFamilyLogGaugeHomeomorph P l hr (fun l' ↦ (hP l').continuous) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ := logTranslationMulAction P l
  let _ := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
  let _ := Opens.instChartedSpace (H := ModelProd ℂ E)
    (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
  exact Homeomorph.ext fun q ↦ by
    rw [Diffeomorph.coe_toHomeomorph, coe_torusFamilyLogGaugeDiffeomorph,
      coe_torusFamilyLogGaugeHomeomorph]

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
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    (torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree ⟨Quotient.mk _ x, hx⟩ :
        AddAction.orbitRel.Quotient Λ (Metric.ball (0 : ℂ) (r ^ m) × E)) =
      torusFamilyLogGauge P l x :=
  torusFamilyLogGaugeEquiv_mk P l hr x hx

/-- The logarithmic gauge lies over the identity of the punctured disc: the image of a point of
`Q*` with coordinate `t` lies over `t`. -/
theorem coe_torusFamilyProjection_torusFamilyLogGaugeDiffeomorph
    (q : torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E)
        (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
      (fun l ↦ (contMDiff_powPullbackPeriod P (hP l)).continuous)
      (fun z ↦ powPullbackPeriod_injective P z (hinj _))
    letI := logTranslationMulAction P l
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    ((torusFamilyProjection P (torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree q).val :
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
    letI := logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyCyclicQuotientNonzeroOpens (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l))
    letI := Opens.instChartedSpace (H := ModelProd ℂ E)
      (torusFamilyNonzeroOpens Subtype.val P continuous_subtypeVal)
    ((torusFamilyLogGaugeDiffeomorph P hP hinj l hr hfree).symm ⟨Quotient.mk _ (t, e), ht⟩ :
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) =
      Quotient.mk _ (Quotient.mk _ (z, e + (L / (2 * π * I)) • P t l)) :=
  torusFamilyLogGaugeEquiv_symm_mk P l hr hz hL e ht

end

/-! ### Smooth quotient identification under `l ↦ l + m • μ` -/

/-- The canonical identification between the cyclic quotient manifolds for `l + m • μ` and `l` is a
`C^n` diffeomorphism (biholomorphism for `n = ω`). -/
noncomputable def logTranslationQuotientAddNsmulDiffeomorph (l μ : Λ)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P (l + m • μ);
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P l;
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    Diffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E))
      (letI := logTranslationMulAction P (l + m • μ);
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
      (letI := logTranslationMulAction P l;
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) n := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P (l + m • μ);
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
      (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P l;
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  have hmk₁ := isLocalDiffeomorph_logTranslationQuotient_mk P hP hinj (l + m • μ)
    (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
  have hmk₂ := isLocalDiffeomorph_logTranslationQuotient_mk P hP hinj l hfree
  have hto :
      (logTranslationQuotientAddNsmulEquiv P l μ :
          (letI := logTranslationMulAction P (l + m • μ);
            orbitRel.Quotient (rootsOfUnity m ℂ)
              (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) →
          (letI := logTranslationMulAction P l;
            orbitRel.Quotient (rootsOfUnity m ℂ)
              (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) ∘
        (letI := logTranslationMulAction P (l + m • μ); Quotient.mk _) =
      (letI := logTranslationMulAction P l; Quotient.mk _) :=
    funext (logTranslationQuotientAddNsmulEquiv_mk P l μ)
  have hinv :
      ((logTranslationQuotientAddNsmulEquiv P l μ).symm :
          (letI := logTranslationMulAction P l;
            orbitRel.Quotient (rootsOfUnity m ℂ)
              (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) →
          (letI := logTranslationMulAction P (l + m • μ);
            orbitRel.Quotient (rootsOfUnity m ℂ)
              (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) ∘
        (letI := logTranslationMulAction P l; Quotient.mk _) =
      (letI := logTranslationMulAction P (l + m • μ); Quotient.mk _) :=
    funext (logTranslationQuotientAddNsmulEquiv_symm_mk P l μ)
  exact
    { toEquiv := logTranslationQuotientAddNsmulEquiv P l μ
      contMDiff_toFun :=
        (hmk₁.contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 (hto ▸ hmk₂.contMDiff)
      contMDiff_invFun :=
        (hmk₂.contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 (hinv ▸ hmk₁.contMDiff) }

/-- The underlying equivalence of `logTranslationQuotientAddNsmulDiffeomorph` is
`logTranslationQuotientAddNsmulEquiv`. -/
@[simp] theorem logTranslationQuotientAddNsmulDiffeomorph_toEquiv (l μ : Λ) (hfree) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P (l + m • μ);
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P l;
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    (logTranslationQuotientAddNsmulDiffeomorph P hP hinj l μ hfree).toEquiv =
      logTranslationQuotientAddNsmulEquiv P l μ := (rfl)

end

end TauCeti
