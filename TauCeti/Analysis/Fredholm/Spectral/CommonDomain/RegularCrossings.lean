/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.Matrix.HermitianSignature.Crossing
import TauCeti.Analysis.Fredholm.Spectral.Crossing
import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The regular-crossing formula on a compactly embedded common domain

Let `ι : D →L H` be a compact operator from a real Banach space `D` into a real Hilbert space `H`,
and let `A : ℝ → (D →L H)` be a continuous path of operators symmetric through `ι`,
`⟪A t x, ι y⟫ = ⟪ι x, A t y⟫`, each with some invertible shift `c₀ ι - A t`. This is how a path of
unbounded self-adjoint operators with common domain and compact resolvent is given, such as the
asymptotic operators `J₀ ∂ₜ + S(t)` of the Floer equation with `D = H¹` and `H = L²`. Its spectral
flow is `TauCeti.domainSpectralFlow ι A a b`.

A *crossing* is a time `t` at which `A t` is not injective. If `A` has a derivative `A'` at `t`,
the **crossing form** at `t` is the quadratic form `x ↦ ⟪A' x, ι x⟫` on the kernel of `A t`
(`ContinuousLinearMap.domainCrossingForm ι (A t) A'`), and the crossing is *regular* when this
form is nondegenerate. This file proves **Robbin and Salamon's regular-crossing formula** for this
spectral flow: if the endpoints `A a` and `A b` are injective and every crossing is regular, there
are finitely many crossings, and

`domainSpectralFlow ι A a b = ∑ᶠ t ∈ (a, b), (sigPos Γₜ - sigNeg Γₜ)`

(`TauCeti.domainSpectralFlow_eq_finsum_sigPos_sub_sigNeg_domainCrossingForm`), where `Γₜ` is the
crossing form at `t`. Positive crossings count positively.

The formula is reduced to the regular-crossing formula for bounded paths
(`TauCeti.Analysis.Fredholm.Spectral.RegularCrossings`) through the shifted resolvent transforms
`τ_c (A t) = c A t (c ι - A t)⁻¹` that define the spectral flow. At a shift `c ≠ 0` with
`c ι - A t₀` invertible:

* the kernel of `τ_c (A t₀)` is `ι (ker A t₀)`
  (`ContinuousLinearMap.ker_shiftedResolventTransform`);
* the transforms have derivative `c² ι R A' R` at `t₀`, for `R = (c ι - A t₀)⁻¹`
  (`HasDerivAt.shiftedResolventTransform`);
* `x ↦ ι x` identifies the crossing form of `A` at `t₀` with the crossing form of the transforms,
  `y ↦ ⟪(c² ι R A' R) y, y⟫` on `ker τ_c (A t₀)`
  (`ContinuousLinearMap.domainCrossingForm_equivalent_crossingForm_shiftedResolventTransform`).
  For `A x = 0` one has `R (ι x) = c⁻¹ x`, and for `w = R (A' x)` the symmetry of `A t₀` gives
  `c ⟪ι w, ι x⟫ = ⟪(c ι - A t₀) w, ι x⟫ = ⟪A' x, ι x⟫`.

So a regular crossing of `A` is a regular crossing of the transforms, and near it the spectral flow
of `A` jumps by the signature of its crossing form
(`TauCeti.eventually_domainSpectralFlow_eq_sigPos_sub_sigNeg_domainCrossingForm`). Regular
crossings are isolated (`TauCeti.eventually_ker_eq_bot_of_domainCrossingForm_nondegenerate`), and
an injective `A t` is invertible, since its shifts are invertible exactly when they are injective;
so a path without crossings has no spectral flow
(`TauCeti.domainSpectralFlow_eq_zero_of_forall_ker_eq_bot`), and the crossings in `[a, b]` are
finitely many (`TauCeti.finite_setOf_ker_ne_bot_of_domainCrossingForm`). Concatenation adds the
jumps.

## Main definitions

* `ContinuousLinearMap.domainCrossingForm ι A A'`: the crossing form `x ↦ ⟪A' x, ι x⟫` on the
  kernel of `A`.

## Main results

* `ContinuousLinearMap.domainCrossingForm_equivalent_crossingForm_shiftedResolventTransform`: the
  crossing form of `A` is equivalent to that of its shifted resolvent transforms.
* `TauCeti.eventually_domainSpectralFlow_eq_sigPos_sub_sigNeg_domainCrossingForm`: the spectral
  flow across a regular crossing is the signature of its crossing form.
* `TauCeti.eventually_ker_eq_bot_of_domainCrossingForm_nondegenerate`: regular crossings are
  isolated.
* `TauCeti.domainSpectralFlow_eq_zero_of_forall_ker_eq_bot`: a path without crossings has no
  spectral flow.
* `TauCeti.finite_setOf_ker_ne_bot_of_domainCrossingForm`: a path with regular crossings has
  finitely many crossings.
* `TauCeti.domainSpectralFlow_eq_finsum_sigPos_sub_sigNeg_domainCrossingForm`: the
  regular-crossing formula.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Theorem 4.21 (the spectral flow as a sum of crossing signatures) and
  Section 4 (paths of self-adjoint operators on a compactly embedded common domain).
-/

public section

open Filter Metric Set Topology
open scoped InnerProductSpace

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

namespace ContinuousLinearMap

/-- The **crossing form** of an operator `A : D →L H` on a common domain `D`, embedded in `H` by
`ι`, with respect to a derivative `A'`: the quadratic form `x ↦ ⟪A' x, ι x⟫` on the kernel of `A`.
For a path `A` of operators symmetric through `ι` with derivative `A'` at a crossing `t₀`, the
crossing form of `A t₀` and `A'` governs how the eigenvalues of `A t` cross `0` as `t` passes
`t₀`. -/
noncomputable def domainCrossingForm (ι A A' : D →L[ℝ] H) : QuadraticForm ℝ A.ker :=
  ((innerSL ℝ).bilinearComp A' ι).toBilinForm.toQuadraticMap.restrict A.ker

/-- The crossing form evaluates `⟪A' x, ι x⟫` on the kernel. -/
@[simp]
theorem domainCrossingForm_apply (ι A A' : D →L[ℝ] H) (x : A.ker) :
    ι.domainCrossingForm A A' x = ⟪A' x, ι x⟫_ℝ := by
  simp [domainCrossingForm]

variable {ι A A' : D →L[ℝ] H} {c : ℝ}

/-- Over `ℝ` the coercion `RCLike.ofReal` is the identity, so the shift `(c : 𝕜) • ι - A` of the
`RCLike` shifted resolvent theory at `𝕜 = ℝ` is the real shift `c • ι - A`. -/
private theorem isInvertible_ofReal_smul_sub_iff :
    ((RCLike.ofReal c : ℝ) • ι - A).IsInvertible ↔ (c • ι - A).IsInvertible := by
  rw [RCLike.ofReal_real_eq_id, id]

/-- At an invertible shift `c ι - A`, `ι` is injective on the kernel of `A`: a vector `x` with
`A x = 0` and `ι x = 0` is sent to `0` by `c ι - A`. -/
private theorem injective_comp_subtype_ker (h : (c • ι - A).IsInvertible) :
    Function.Injective ((ι : D →ₗ[ℝ] H) ∘ₗ A.ker.subtype) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨x, hx⟩ hιx
  have hAx : A x = 0 := hx
  rw [LinearMap.mem_ker] at hιx
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, coe_coe] at hιx
  simpa using h.injective (a₁ := x) (a₂ := 0) (by simp [hAx, hιx])

/-- At an invertible shift `c ι - A` with `c ≠ 0`, `x ↦ ι x` is a linear equivalence from the
kernel of `A` onto the kernel of the bilinear form of the shifted resolvent transform. -/
private noncomputable def kerEquivKerShiftedResolventTransform (h : (c • ι - A).IsInvertible)
    (hc : c ≠ 0) :
    A.ker ≃ₗ[ℝ] (((innerSL ℝ).comp (ι.shiftedResolventTransform A c) : H →L[ℝ] H →L[ℝ] ℝ) :
      H →ₗ[ℝ] H →L[ℝ] ℝ).ker :=
  (LinearEquiv.ofInjective _ (injective_comp_subtype_ker h)).trans <| LinearEquiv.ofEq _ _ <| by
    rw [ker_innerSL_comp, ker_shiftedResolventTransform (isInvertible_ofReal_smul_sub_iff.2 h) hc,
      LinearMap.range_comp,
      Submodule.range_subtype]

private theorem kerEquivKerShiftedResolventTransform_apply (h : (c • ι - A).IsInvertible)
    (hc : c ≠ 0) (x : A.ker) :
    (kerEquivKerShiftedResolventTransform h hc x : H) = ι x :=
  rfl

/-- **The crossing form of the shifted resolvent transforms.** Let `A` be symmetric through `ι`,
with `c ι - A` invertible at a shift `c ≠ 0`, and let `R = (c ι - A)⁻¹`. Then `x ↦ ι x` is an
isometry from the crossing form `x ↦ ⟪A' x, ι x⟫` on the kernel of `A` onto the crossing form
`y ↦ ⟪(c² ι R A' R) y, y⟫` on the kernel of the shifted resolvent transform `τ_c A`. Here
`c² ι R A' R` is the derivative of the transforms along a path with derivative `A'`
(`HasDerivAt.shiftedResolventTransform`). -/
theorem domainCrossingForm_equivalent_crossingForm_shiftedResolventTransform (hc : c ≠ 0)
    (h : (c • ι - A).IsInvertible) (hsymm : ∀ x y, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) :
    (ι.domainCrossingForm A A').Equivalent
      (crossingForm ((innerSL ℝ).comp (ι.shiftedResolventTransform A c))
        ((innerSL ℝ).comp (c ^ 2 • (ι ∘L (c • ι - A).inverse ∘L A' ∘L (c • ι - A).inverse)))) := by
  refine ⟨⟨kerEquivKerShiftedResolventTransform h hc, fun ⟨x, hx⟩ ↦ ?_⟩⟩
  have hAx : A x = 0 := hx
  set R := (c • ι - A).inverse
  -- `R (ι x) = c⁻¹ x`, since `c ι - A` sends `c⁻¹ x` to `ι x`.
  have hRι : R (ι x) = c⁻¹ • x := by
    refine h.injective ?_
    rw [h.self_apply_inverse]
    simp [hAx, smul_smul, inv_mul_cancel₀ hc]
  -- With `w = R (A' x)`, `c ⟪ι w, ι x⟫ = ⟪(c ι - A) w, ι x⟫ = ⟪A' x, ι x⟫` by symmetry.
  have hw : c * ⟪ι (R (A' x)), ι x⟫_ℝ = ⟪A' x, ι x⟫_ℝ := by
    calc c * ⟪ι (R (A' x)), ι x⟫_ℝ = ⟪(c • ι - A) (R (A' x)), ι x⟫_ℝ := by
          rw [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left, hsymm, hAx,
            inner_zero_right, sub_zero]
      _ = ⟪A' x, ι x⟫_ℝ := by rw [h.self_apply_inverse]
  simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, crossingForm_apply,
    kerEquivKerShiftedResolventTransform_apply, comp_apply, innerSL_apply_apply, smul_apply, hRι,
    map_smul, domainCrossingForm_apply, smul_eq_mul, ← hw]
  field_simp

end ContinuousLinearMap

namespace TauCeti

open ContinuousLinearMap

variable [CompleteSpace D] [CompleteSpace H] {ι : D →L[ℝ] H} {A : ℝ → D →L[ℝ] H}
  {A' : D →L[ℝ] H} {t₀ : ℝ}

omit [CompleteSpace H] in
/-- Around a time `t₀` at which `A` is continuous nearby, symmetric nearby and has an invertible
shift, a single shift `c ≠ 0` is admissible on a whole ball around `t₀`, on which `A` is
continuous and symmetric. -/
private theorem exists_ball_isInvertible_smul_sub (hι : IsCompactOperator ι)
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t)
    (hsymm : ∀ᶠ t in 𝓝 t₀, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∃ c₀ : ℝ, (c₀ • ι - A t₀).IsInvertible) :
    ∃ c : ℝ, c ≠ 0 ∧ ∃ ε > 0, ∀ t ∈ ball t₀ ε, ContinuousAt A t ∧ (c • ι - A t).IsInvertible ∧
      ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ := by
  obtain ⟨c₀, hc₀⟩ := h₀
  obtain ⟨c, hc, hinv⟩ := ι.exists_mem_Ioo_eventually_isInvertible_ofReal_smul_sub hι
    (s := univ) hA.self_of_nhds.continuousWithinAt hc₀ zero_lt_one
  rw [nhdsWithin_univ] at hinv
  replace hinv := hinv.mono fun _ ↦ isInvertible_ofReal_smul_sub_iff.1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hA.and (hinv.and hsymm))
  exact ⟨c, hc.1.ne', ε, hε, fun t ht ↦ ⟨(hball t ht).1, (hball t ht).2.1, (hball t ht).2.2⟩⟩

/-- On a ball on which a shift `c ≠ 0` is admissible and `A` is continuous and symmetric through a
compact `ι`, the shifted resolvent transforms at `c` are continuous and self-adjoint near `t₀` and
Fredholm at `t₀`. These are the hypotheses of the local regular-crossing theory for bounded
paths. -/
private theorem shiftedResolventTransform_regular (hι : IsCompactOperator ι) {c ε : ℝ}
    (hc : c ≠ 0) (hε : 0 < ε) (hball : ∀ t ∈ ball t₀ ε, ContinuousAt A t ∧
      (c • ι - A t).IsInvertible ∧ ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ) :
    (∀ᶠ t in 𝓝 t₀, ContinuousAt (fun t ↦ ι.shiftedResolventTransform (A t) c) t) ∧
      (∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (ι.shiftedResolventTransform (A t) c)) ∧
      (ι.shiftedResolventTransform (A t₀) c).IsFredholm := by
  have hcont : ContinuousOn (fun t ↦ ι.shiftedResolventTransform (A t) c) (ball t₀ ε) :=
    ContinuousOn.shiftedResolventTransform (fun t ht ↦ (hball t ht).1.continuousWithinAt)
      fun t ht ↦ (hball t ht).2.1
  refine ⟨eventually_of_mem (ball_mem_nhds t₀ hε) fun t ht ↦ hcont.continuousAt
      (isOpen_ball.mem_nhds ht),
    eventually_of_mem (ball_mem_nhds t₀ hε) fun t ht ↦
      ι.isSelfAdjoint_shiftedResolventTransform (hball t ht).2.2,
    ι.isFredholm_shiftedResolventTransform hι hc (hball t₀ (mem_ball_self hε)).2.1⟩

omit [CompleteSpace H] in
/-- At a regular crossing `t₀` of a path continuous and symmetric near `t₀` with an invertible
shift at `t₀`, a single shift `c ≠ 0` is admissible on a ball around `t₀`, on which `A` is
continuous and symmetric. The crossing form of `A` at `t₀` is equivalent to that of the shifted
resolvent transforms at `c`, which is therefore nondegenerate. -/
private theorem exists_ball_domainCrossingForm_equivalent (hι : IsCompactOperator ι)
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t)
    (hsymm : ∀ᶠ t in 𝓝 t₀, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∃ c₀ : ℝ, (c₀ • ι - A t₀).IsInvertible)
    (hreg : (ι.domainCrossingForm (A t₀) A').Nondegenerate) :
    ∃ c : ℝ, c ≠ 0 ∧ ∃ ε > 0, (∀ t ∈ ball t₀ ε, ContinuousAt A t ∧ (c • ι - A t).IsInvertible ∧
      ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ) ∧
      (ι.domainCrossingForm (A t₀) A').Equivalent
        (crossingForm ((innerSL ℝ).comp (ι.shiftedResolventTransform (A t₀) c))
          ((innerSL ℝ).comp
            (c ^ 2 • (ι ∘L (c • ι - A t₀).inverse ∘L A' ∘L (c • ι - A t₀).inverse)))) ∧
      (crossingForm ((innerSL ℝ).comp (ι.shiftedResolventTransform (A t₀) c))
          ((innerSL ℝ).comp (c ^ 2 •
            (ι ∘L (c • ι - A t₀).inverse ∘L A' ∘L (c • ι - A t₀).inverse)))).Nondegenerate := by
  obtain ⟨c, hc, ε, hε, hball⟩ := exists_ball_isInvertible_smul_sub hι hA hsymm h₀
  have h₀' := hball t₀ (mem_ball_self hε)
  obtain ⟨e⟩ := domainCrossingForm_equivalent_crossingForm_shiftedResolventTransform (A' := A') hc
    h₀'.2.1 h₀'.2.2
  exact ⟨c, hc, ε, hε, hball, ⟨e⟩, e.nondegenerate_iff.1 hreg⟩

/-- **The spectral flow across a regular crossing.** Let `ι` be compact, and let `A` be continuous
and symmetric through `ι` near `t₀`, with an invertible shift at `t₀` and a derivative `A'` at
`t₀` whose crossing form `x ↦ ⟪A' x, ι x⟫` on the kernel of `A t₀` is nondegenerate. Then for `a`
just below and `b` just above `t₀`, the spectral flow of `A` from `a` to `b` is the signature of
the crossing form. -/
theorem eventually_domainSpectralFlow_eq_sigPos_sub_sigNeg_domainCrossingForm
    (hι : IsCompactOperator ι) (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t)
    (hsymm : ∀ᶠ t in 𝓝 t₀, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∃ c₀ : ℝ, (c₀ • ι - A t₀).IsInvertible) (hd : HasDerivAt A A' t₀)
    (hreg : (ι.domainCrossingForm (A t₀) A').Nondegenerate) :
    ∀ᶠ a in 𝓝[<] t₀, ∀ᶠ b in 𝓝[>] t₀, domainSpectralFlow ι A a b =
      (sigPos (ι.domainCrossingForm (A t₀) A') : ℤ) - sigNeg (ι.domainCrossingForm (A t₀) A') := by
  obtain ⟨c, hc, ε, hε, hball, ⟨e⟩, hτreg⟩ :=
    exists_ball_domainCrossingForm_equivalent hι hA hsymm h₀ hreg
  obtain ⟨hτc, hτsa, hτF⟩ := shiftedResolventTransform_regular hι hc hε hball
  -- The transforms cross regularly at `t₀`, and their spectral flow jumps by the signature.
  filter_upwards [eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm hτc hτsa hτF
      (hd.shiftedResolventTransform (hball t₀ (mem_ball_self hε)).2.1) hτreg,
    Ioo_mem_nhdsLT (show t₀ - ε < t₀ by linarith)] with a ha haε
  filter_upwards [ha, Ioo_mem_nhdsGT (show t₀ < t₀ + ε by linarith)] with b hb hbε
  -- On `[a, b]` the shift `c` is admissible, so the spectral flow is that of the transforms.
  have hsub : Icc a b ⊆ ball t₀ ε := by
    rw [Real.ball_eq_Ioo]
    exact Icc_subset_Ioo haε.1 hbε.2
  rw [domainSpectralFlow_eq_spectralFlow_shiftedResolventTransform hι (haε.2.trans hbε.1).le
    (fun t ht ↦ (hball t (hsub ht)).1.continuousWithinAt) (fun t ht ↦ (hball t (hsub ht)).2.2) hc
    (fun t ht ↦ isInvertible_ofReal_smul_sub_iff.2 (hball t (hsub ht)).2.1), hb,
    (QuadraticMap.Equivalent.sigPos_eq ⟨e⟩), (QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩)]

/-- **Regular crossings are isolated.** Under the hypotheses of
`TauCeti.eventually_domainSpectralFlow_eq_sigPos_sub_sigNeg_domainCrossingForm`, `A t` is
injective for every `t ≠ t₀` near `t₀`. -/
theorem eventually_ker_eq_bot_of_domainCrossingForm_nondegenerate (hι : IsCompactOperator ι)
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t)
    (hsymm : ∀ᶠ t in 𝓝 t₀, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∃ c₀ : ℝ, (c₀ • ι - A t₀).IsInvertible) (hd : HasDerivAt A A' t₀)
    (hreg : (ι.domainCrossingForm (A t₀) A').Nondegenerate) :
    ∀ᶠ t in 𝓝[≠] t₀, (A t).ker = ⊥ := by
  obtain ⟨c, hc, ε, hε, hball, -, hτreg⟩ :=
    exists_ball_domainCrossingForm_equivalent hι hA hsymm h₀ hreg
  obtain ⟨hτc, hτsa, hτF⟩ := shiftedResolventTransform_regular hι hc hε hball
  filter_upwards [eventually_ker_eq_bot_of_crossingForm_nondegenerate hτc hτsa hτF
      (hd.shiftedResolventTransform (hball t₀ (mem_ball_self hε)).2.1) hτreg,
    nhdsWithin_le_nhds (ball_mem_nhds t₀ hε)] with t hτ ht
  -- `ker τ_c (A t) = ι (ker A t)`, and `ι` is injective on `ker A t`.
  have hinv := (hball t ht).2.1
  rw [ker_shiftedResolventTransform (isInvertible_ofReal_smul_sub_iff.2 hinv) hc] at hτ
  rw [eq_bot_iff]
  intro x hx
  have hιx : ι x = 0 := by
    have hmem := Submodule.mem_map_of_mem (f := (ι : D →ₗ[ℝ] H)) hx
    rwa [hτ, Submodule.mem_bot] at hmem
  simpa using injective_comp_subtype_ker hinv (a₁ := ⟨x, hx⟩) (a₂ := 0) (by simp [hιx])

/-- **A path without crossings has no spectral flow.** If every `A t` with `t ∈ [a, b]` is
injective, the spectral flow of `A` from `a` to `b` vanishes. -/
theorem domainSpectralFlow_eq_zero_of_forall_ker_eq_bot (hι : IsCompactOperator ι) {a b : ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible)
    (hker : ∀ t ∈ Icc a b, (A t).ker = ⊥) : domainSpectralFlow ι A a b = 0 :=
  domainSpectralFlow_eq_zero_of_forall_isInvertible hι hab hA hsymm fun t ht ↦ by
    obtain ⟨c₀, hc₀⟩ := h₀ t ht
    exact (isInvertible_iff_injective_of_isInvertible_smul_sub hι hc₀).2
      (LinearMap.ker_eq_bot.1 (hker t ht))

omit [CompleteSpace D] [CompleteSpace H] in
/-- At an interior time of `[a, b]`, a path continuous and symmetric on `[a, b]` is continuous and
symmetric at all nearby times. -/
private theorem eventually_continuousAt_and_symm {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) :
    (∀ᶠ t in 𝓝 t₀, ContinuousAt A t) ∧ ∀ᶠ t in 𝓝 t₀, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ :=
  ⟨eventually_of_mem (Ioo_mem_nhds ht₀.1 ht₀.2) fun _ ht ↦
      hA.continuousAt (Icc_mem_nhds ht.1 ht.2),
    eventually_of_mem (Icc_mem_nhds ht₀.1 ht₀.2) hsymm⟩

omit [CompleteSpace D] [CompleteSpace H] in
/-- A crossing in `[a, b]` of a path injective at both endpoints lies in `(a, b)`. -/
private theorem mem_Ioo_of_ker_ne_bot {a b : ℝ} (ha : (A a).ker = ⊥) (hb : (A b).ker = ⊥)
    {t : ℝ} (ht : t ∈ Icc a b) (hnt : (A t).ker ≠ ⊥) : t ∈ Ioo a b :=
  ⟨lt_of_le_of_ne ht.1 fun h ↦ hnt (h ▸ ha), lt_of_le_of_ne ht.2 fun h ↦ hnt (h ▸ hb)⟩

/-- **A path with regular crossings has finitely many crossings.** Let `ι` be compact and `A` a
continuous path of operators symmetric through `ι` over `[a, b]`, each with an invertible shift,
and injective at both endpoints. If at every crossing `t ∈ (a, b)`, where `A t` is not injective,
the path has a derivative `A' t` with nondegenerate crossing form, then the crossings in `[a, b]`
form a finite set. -/
theorem finite_setOf_ker_ne_bot_of_domainCrossingForm (hι : IsCompactOperator ι) {a b : ℝ}
    {A' : ℝ → D →L[ℝ] H} (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) (ha : (A a).ker = ⊥)
    (hb : (A b).ker = ⊥) (hderiv : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ → HasDerivAt A (A' t) t)
    (hreg : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ → (ι.domainCrossingForm (A t) (A' t)).Nondegenerate) :
    {t ∈ Icc a b | (A t).ker ≠ ⊥}.Finite := by
  rw [← inter_ofPred_eq_sep, ← compl_ofPred, ← sdiff_eq]
  -- The injective times are codiscrete in the compact interval `[a, b]`.
  refine isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin <|
    mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun z hz ↦ ?_
  suffices h : ∀ᶠ t in 𝓝[≠] z, t ∈ Icc a b → (A t).ker = ⊥ from
    mem_of_superset h fun t ht ↦ (em (t ∈ Icc a b)).imp ht id
  by_cases hnz : (A z).ker = ⊥
  · -- `A z` is invertible, and so is `A t` for every `t ∈ [a, b]` near `z`.
    obtain ⟨c₀, hc₀⟩ := h₀ z hz
    have hinv := (isInvertible_iff_injective_of_isInvertible_smul_sub hι hc₀).2
      (LinearMap.ker_eq_bot.1 hnz)
    have hopen := eventually_nhdsWithin_iff.1 <| (hA z hz).eventually hinv.eventually_nhds
    filter_upwards [nhdsWithin_le_nhds hopen] with t ht htI
    exact LinearMap.ker_eq_bot.2 (ht htI).injective
  · -- A crossing lies in `(a, b)`, and regular crossings are isolated.
    have hz' : z ∈ Ioo a b := mem_Ioo_of_ker_ne_bot ha hb hz hnz
    obtain ⟨hcont, hsymm'⟩ := eventually_continuousAt_and_symm hA hsymm hz'
    filter_upwards [eventually_ker_eq_bot_of_domainCrossingForm_nondegenerate hι hcont hsymm'
      (h₀ z hz) (hderiv z hz' hnz) (hreg z hz' hnz)] with t ht _ using ht

/-- Around a regular crossing `s ∈ (a, b)`, there are times `t₁ < s < t₂` in `(a, b)`, with `t₁`
above every point of a finite set `S` of times below `s`, such that the spectral flow from `t₁` to
`t₂` is the signature of the crossing form at `s`. -/
private theorem exists_domainSpectralFlow_eq_sigPos_sub_sigNeg_domainCrossingForm
    (hι : IsCompactOperator ι) {a b s : ℝ} {A' : D →L[ℝ] H} {S : Finset ℝ}
    (hA : ContinuousOn A (Icc a b)) (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) (hs : s ∈ Ioo a b)
    (hd : HasDerivAt A A' s) (hΓ : (ι.domainCrossingForm (A s) A').Nondegenerate)
    (hlt : ∀ x ∈ S, x < s) :
    ∃ t₁ t₂, t₁ ∈ Ioo a s ∧ (∀ x ∈ S, x < t₁) ∧ t₂ ∈ Ioo s b ∧ domainSpectralFlow ι A t₁ t₂ =
      (sigPos (ι.domainCrossingForm (A s) A') : ℤ) - sigNeg (ι.domainCrossingForm (A s) A') := by
  obtain ⟨hcont, hsymm'⟩ := eventually_continuousAt_and_symm hA hsymm hs
  have hleft : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s ∧ ∀ x ∈ S, x < t :=
    (eventually_mem_set.2 (Ioo_mem_nhdsLT hs.1)).and <| (eventually_all_finset S).2 fun x hx ↦
      (eventually_mem_set.2 (Ioo_mem_nhdsLT (hlt x hx))).mono fun t ht ↦ ht.1
  obtain ⟨t₁, ⟨ht₁, hSt₁⟩, hjump⟩ := (hleft.and
    (eventually_domainSpectralFlow_eq_sigPos_sub_sigNeg_domainCrossingForm hι hcont hsymm'
      (h₀ s (Ioo_subset_Icc_self hs)) hd hΓ)).exists
  obtain ⟨t₂, ht₂, hjump⟩ := ((eventually_mem_set.2 (Ioo_mem_nhdsGT hs.2)).and hjump).exists
  exact ⟨t₁, t₂, ht₁, hSt₁, ht₂, hjump⟩

/-- The regular-crossing formula for a finite set `S` of regular crossings in `(a, b)` outside which
the path is injective, by induction on `S` from its largest element. -/
private theorem domainSpectralFlow_eq_sum_domainCrossingForm_of_finset (hι : IsCompactOperator ι)
    {a : ℝ} {A' : ℝ → D →L[ℝ] H} (S : Finset ℝ) :
    ∀ b, a ≤ b → ContinuousOn A (Icc a b) →
      (∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ) →
      (∀ t ∈ Icc a b, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) →
      (∀ t ∈ Icc a b, t ∉ S → (A t).ker = ⊥) →
      (∀ t ∈ S, t ∈ Ioo a b ∧ HasDerivAt A (A' t) t ∧
        (ι.domainCrossingForm (A t) (A' t)).Nondegenerate) →
      domainSpectralFlow ι A a b = ∑ t ∈ S,
        ((sigPos (ι.domainCrossingForm (A t) (A' t)) : ℤ) -
          sigNeg (ι.domainCrossingForm (A t) (A' t))) := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro b hab hA hsymm h₀ hker _
    rw [Finset.sum_empty]
    exact domainSpectralFlow_eq_zero_of_forall_ker_eq_bot hι hab hA hsymm h₀ fun t ht ↦
      hker t ht (Finset.notMem_empty t)
  | insert s S hlt ih =>
    intro b _ hA hsymm h₀ hker hS
    obtain ⟨⟨has, hsb⟩, hd, hΓ⟩ := hS s (Finset.mem_insert_self s S)
    -- Choose `t₁ < s < t₂`, with `t₁` above every other crossing, such that the spectral flow from
    -- `t₁` to `t₂` is the signature of the crossing form at `s`.
    obtain ⟨t₁, t₂, ⟨hat₁, ht₁s⟩, hSt₁, ⟨hst₂, ht₂b⟩, hjump⟩ :=
      exists_domainSpectralFlow_eq_sigPos_sub_sigNeg_domainCrossingForm hι hA hsymm h₀ ⟨has, hsb⟩
        hd hΓ hlt
    -- On `[t₂, b]` there is no crossing, so there is no spectral flow there.
    have hright : domainSpectralFlow ι A t₂ b = 0 := by
      have hsub : Icc t₂ b ⊆ Icc a b := Icc_subset_Icc (has.trans hst₂).le le_rfl
      refine domainSpectralFlow_eq_zero_of_forall_ker_eq_bot hι ht₂b.le (hA.mono hsub)
        (fun t ht ↦ hsymm t (hsub ht)) (fun t ht ↦ h₀ t (hsub ht))
        fun t ht ↦ hker t (hsub ht) ?_
      rw [Finset.mem_insert, not_or]
      exact ⟨(hst₂.trans_le ht.1).ne', fun htS ↦ (hlt t htS).not_gt (hst₂.trans_le ht.1)⟩
    -- On `[a, t₁]` the crossings are those of `S`, and the induction hypothesis applies.
    have hsub : Icc a t₁ ⊆ Icc a b := Icc_subset_Icc le_rfl (ht₁s.trans hsb).le
    have hinit := ih t₁ hat₁.le (hA.mono hsub) (fun t ht ↦ hsymm t (hsub ht))
      (fun t ht ↦ h₀ t (hsub ht))
      (fun t ht htS ↦ hker t (hsub ht) (by
        rw [Finset.mem_insert, not_or]
        exact ⟨(ht.2.trans_lt ht₁s).ne, htS⟩))
      (fun t htS ↦ ⟨⟨(hS t (Finset.mem_insert_of_mem htS)).1.1, hSt₁ t htS⟩,
        (hS t (Finset.mem_insert_of_mem htS)).2⟩)
    -- Concatenate the spectral flows over `[a, t₁]`, `[t₁, t₂]` and `[t₂, b]`.
    have ht₁t₂ : t₁ ≤ t₂ := (ht₁s.trans hst₂).le
    have hsub₂ : Icc a t₂ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₂b.le
    rw [domainSpectralFlow_add_adjacent_intervals hι (hat₁.le.trans ht₁t₂) ht₂b.le hA hsymm h₀,
      domainSpectralFlow_add_adjacent_intervals hι hat₁.le ht₁t₂ (hA.mono hsub₂)
        (fun t ht ↦ hsymm t (hsub₂ ht)) (fun t ht ↦ h₀ t (hsub₂ ht)),
      hinit, hjump, hright, Finset.sum_insert fun h ↦ (hlt s h).false]
    ring

/-- **The regular-crossing formula for the spectral flow on a common domain** (Robbin–Salamon).
Let `ι : D →L H` be a compact operator from a real Banach space into a real Hilbert space, and
`A` a continuous path of operators `D →L H` over `[a, b]`, symmetric through `ι`, each with an
invertible shift `c₀ ι - A t`, and injective (hence invertible) at both endpoints. Suppose that
every crossing `t ∈ (a, b)`, a time at which `A t` is not injective, is regular: `A` has a
derivative `A' t` at `t`, and the crossing form `Γₜ : x ↦ ⟪A' t x, ι x⟫` on the kernel of `A t` is
nondegenerate. Then the spectral flow of `A` is the sum over the crossings of the signatures
`sigPos Γₜ - sigNeg Γₜ`. Times at which `A t` is injective contribute zero to the sum, and there
are only finitely many crossings (`TauCeti.finite_setOf_ker_ne_bot_of_domainCrossingForm`). -/
theorem domainSpectralFlow_eq_finsum_sigPos_sub_sigNeg_domainCrossingForm
    (hι : IsCompactOperator ι) {a b : ℝ} {A' : ℝ → D →L[ℝ] H} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫_ℝ = ⟪ι x, A t y⟫_ℝ)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : ℝ, (c₀ • ι - A t).IsInvertible) (ha : (A a).ker = ⊥)
    (hb : (A b).ker = ⊥) (hderiv : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ → HasDerivAt A (A' t) t)
    (hreg : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ → (ι.domainCrossingForm (A t) (A' t)).Nondegenerate) :
    domainSpectralFlow ι A a b = ∑ᶠ t ∈ Ioo a b,
      ((sigPos (ι.domainCrossingForm (A t) (A' t)) : ℤ) -
        sigNeg (ι.domainCrossingForm (A t) (A' t))) := by
  have hfin := finite_setOf_ker_ne_bot_of_domainCrossingForm hι hA hsymm h₀ ha hb hderiv hreg
  have hS : ∀ t, t ∈ hfin.toFinset ↔ t ∈ Icc a b ∧ (A t).ker ≠ ⊥ := by simp
  rw [domainSpectralFlow_eq_sum_domainCrossingForm_of_finset hι hfin.toFinset b hab hA hsymm h₀
    (fun t ht htS ↦ not_not.1 fun hnt ↦ htS ((hS t).2 ⟨ht, hnt⟩))
    (fun t htS ↦ by
      obtain ⟨ht, hnt⟩ := (hS t).1 htS
      have hIoo := mem_Ioo_of_ker_ne_bot ha hb ht hnt
      exact ⟨hIoo, hderiv t hIoo hnt, hreg t hIoo hnt⟩)]
  refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
  ext t
  simp only [mem_inter_iff, Finset.mem_coe, hS, Function.mem_support]
  refine and_congr_left fun hft ↦ ?_
  -- Only crossings contribute: at an injective time the crossing form lives on the zero space.
  have hnt : (A t).ker ≠ ⊥ := fun hnt ↦ hft <| by
    have h₀ : Module.finrank ℝ (A t).ker = 0 := by rw [hnt, finrank_bot]
    have hpos := sigPos_le_finrank (ι.domainCrossingForm (A t) (A' t))
    have hneg := sigPos_le_finrank (-ι.domainCrossingForm (A t) (A' t))
    rw [sigPos_neg] at hneg
    omega
  exact ⟨fun ht ↦ ⟨Ioo_subset_Icc_self ht, hnt⟩, fun ⟨ht, _⟩ ↦ mem_Ioo_of_ker_ne_bot ha hb ht hnt⟩

end TauCeti
