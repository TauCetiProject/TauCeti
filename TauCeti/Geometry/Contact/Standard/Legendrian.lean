/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Contact.Standard
public import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Legendrian curves in the standard contact space `ℝ³`

This file works out the Legendrian curves of the three-dimensional standard contact space, in its
two coordinate presentations: `ℝ × ℝ × ℝ` with coordinates `(q, p, z)` and the one-jet form
`dz - p dq` (`TauCeti.innerProductContactForm ℝ`), and with coordinates `(x, y, z)` and the form
`dz - x dy` (`TauCeti.standardContactForm`).

**Fronts.** A curve `t ↦ (q t, p t, z t)` is tangent to `ker (dz - p dq)` at a point where it is
differentiable exactly when `z' = p q'`
(`TauCeti.range_mfderiv_le_kerDistribution_innerProductContactForm_iff`,
`TauCeti.isHorizontalMap_innerProductContactForm_iff`). Its **front** is its projection
`t ↦ (q t, z t)` to the `(q, z)`-plane. For a Legendrian curve the front is immersed at `t`
exactly when `q' ≠ 0` (`TauCeti.deriv_prodMk_ne_zero_iff_of_deriv_eq_mul`), and there the curve is
recovered from its front as the slope `p = z' / q'`. Where the front is the graph of `z = f(q)`,
the curve is the one-jet `(q, f'(q), f(q))` of `f` (`TauCeti.eq_deriv_of_eventuallyEq_comp`).
Hence two Legendrian curves with the same front and continuous momenta agree wherever the front is
immersed on a dense set of times (`TauCeti.eqOn_of_deriv_eq_mul_of_subset_closure`), in particular
when the front is immersed outside a set of isolated times
(`TauCeti.eqOn_of_deriv_eq_mul_of_eventually_ne`). The hypothesis
cannot be dropped: the lines `t ↦ (0, t, 0)` and `t ↦ (0, 2 t, 0)` are different Legendrian
embeddings with the same front, a single point
(`TauCeti.exists_isLegendrianEmbedding_ne_of_front_eq`).

**The `y`-axis.** In `(ℝ³, dz - x dy)` the `y`-axis `{x = z = 0}` is a Legendrian embedding of
`ℝ` (`TauCeti.isLegendrianEmbedding_standardContactForm_yAxis`). The coordinate swap
`(q, p, z) ↦ (p, q, z)` carries the zero section `{p = z = 0}` of the one-jet space onto it and is
a strict contactomorphism: it pulls `dz - x dy` back to `dz - p dq` exactly
(`TauCeti.mpullback_standardContactForm_swap`). The map `(q, p, z) ↦ (-p, q, z)` also carries the
zero section onto the `y`-axis, but it pulls `dz - x dy` back to `dz + p dq`
(`TauCeti.mpullback_standardContactForm_neg_swap_apply`), so it is not strict for these forms
(`TauCeti.mpullback_standardContactForm_neg_swap_ne`). Likewise, for the contact form
`eˣ (dz - x dy)`, which has the same kernel, the swap pulls the form back to `eᵖ (dz - p dq)`
(`TauCeti.mpullback_swap_apply_of_eq_exp_smul_standardContactForm`), a contactomorphism of the
kernels that is not strict (`TauCeti.mpullback_swap_ne_of_eq_exp_smul_standardContactForm`).
Strictness is a property of the chosen contact forms, not of the contact structures.

**Isotropic submanifolds are curves.** A smooth map into `(ℝ³, ker (dz - x dy))` that is tangent
to the contact structure and immersive at some point has a source of dimension at most one: no
surface is tangent to the standard contact structure
(`TauCeti.IsHorizontalMap.finrank_le_one_of_standardContactForm`).

## References

* H. Geiges, *Contact geometry*, in *Handbook of Differential Geometry*, Vol. II, Elsevier, 2006,
  315–382 (arXiv:math/0307242), Lemma 2.45 (Legendrian curves and their fronts, in the
  coordinates `(x, y) = (-p, q)`).
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, American Mathematical Society, 1997, Section 43.
-/

public section

noncomputable section

open Set Filter Function Module
open scoped Manifold Topology ContDiff

namespace TauCeti

/-! ### Horizontal curves for `dz - p dq` -/

/-- The differential of a curve in `ℝ × ℝ × ℝ` with velocity `γ'` at `t` sends `s` to `s • γ'`. -/
private theorem mfderiv_apply_of_hasDerivAt {γ : ℝ → ℝ × ℝ × ℝ} {γ' : ℝ × ℝ × ℝ} {t : ℝ}
    (h : HasDerivAt γ γ' t) (s : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) γ t s : ℝ × ℝ × ℝ) = s • γ' := by
  rw [mfderiv_eq_fderiv, h.hasFDerivAt.fderiv]
  -- The identifications of the tangent spaces with the model spaces are the identity.
  rfl

/-- **Horizontal curves for `dz - p dq`.** At a point where it is differentiable, the curve
`t ↦ (q t, p t, z t)` of `ℝ × ℝ × ℝ` has its tangent line in the kernel of the one-jet contact form
`dz - p dq` exactly when `z' = p q'`. -/
theorem range_mfderiv_le_kerDistribution_innerProductContactForm_iff {q p z : ℝ → ℝ} {t : ℝ}
    (hq : DifferentiableAt ℝ q t) (hp : DifferentiableAt ℝ p t) (hz : DifferentiableAt ℝ z t) :
    LinearMap.range (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
        (fun s ↦ (q s, p s, z s)) t).toLinearMap ≤
        (innerProductContactForm ℝ).kerDistribution (q t, p t, z t) ↔
      deriv z t = p t * deriv q t := by
  have hd := HasDerivAt.prodMk hq.hasDerivAt (HasDerivAt.prodMk hp.hasDerivAt hz.hasDerivAt)
  -- The differential sends `s` to `s (q', p', z')`, which lies in the kernel iff `s z' = p s q'`.
  have hmem (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun s ↦ (q s, p s, z s)) t s ∈
      (innerProductContactForm ℝ).kerDistribution (q t, p t, z t) ↔
      s * deriv z t = p t * (s * deriv q t) := by
    rw [mem_kerDistribution_innerProductContactForm, mfderiv_apply_of_hasDerivAt hd s,
      Real.inner_apply]
    simp
  rw [LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
  exact ⟨fun h ↦ by simpa using (hmem 1).1 (h (1 : ℝ)),
    fun h (s : ℝ) ↦ (hmem s).2 (by rw [h]; ring)⟩

/-- **Horizontal curves for `dz - p dq`.** A differentiable curve `t ↦ (q t, p t, z t)` of
`ℝ × ℝ × ℝ` is tangent to the kernel of the one-jet contact form `dz - p dq` exactly when
`z' = p q'` at every time. -/
theorem isHorizontalMap_innerProductContactForm_iff {q p z : ℝ → ℝ} (hq : Differentiable ℝ q)
    (hp : Differentiable ℝ p) (hz : Differentiable ℝ z) :
    IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
        (fun s ↦ (q s, p s, z s)) ↔
      ∀ t, deriv z t = p t * deriv q t :=
  isHorizontalMap_iff_range_mfderiv_le.trans <| forall_congr' fun t ↦
    range_mfderiv_le_kerDistribution_innerProductContactForm_iff (hq t) (hp t) (hz t)

/-! ### Fronts of Legendrian curves -/

/-- **The front of a Legendrian curve is immersed exactly where `q' ≠ 0`.** If `z' = p q'` at `t`,
the front `s ↦ (q s, z s)` has nonzero velocity at `t` exactly when `q' ≠ 0` there: a vertical
front velocity `(0, z')` with `z' ≠ 0` is impossible. -/
theorem deriv_prodMk_ne_zero_iff_of_deriv_eq_mul {q p z : ℝ → ℝ} {t : ℝ}
    (hq : DifferentiableAt ℝ q t) (hz : DifferentiableAt ℝ z t)
    (h : deriv z t = p t * deriv q t) :
    deriv (fun s ↦ (q s, z s)) t ≠ 0 ↔ deriv q t ≠ 0 := by
  rw [(HasDerivAt.prodMk hq.hasDerivAt hz.hasDerivAt).deriv, Ne, Prod.mk_eq_zero, h]
  constructor
  · rintro h' hq0
    exact h' ⟨hq0, by rw [hq0, mul_zero]⟩
  · exact fun hq0 h' ↦ hq0 h'.1

/-- **Where the front is a graph, a Legendrian curve is a one-jet.** If `z' = p q'` at `t`,
`q' ≠ 0` there, and near `t` the front lies on the graph of a function `f` differentiable at
`q t`, that is `z = f ∘ q` near `t`, then `p t = f'(q t)`: the point `(q t, p t, z t)` of the curve
is the one-jet `(q t, f'(q t), f(q t))` of `f`. -/
theorem eq_deriv_of_eventuallyEq_comp {q p z f : ℝ → ℝ} {t : ℝ} (hq : DifferentiableAt ℝ q t)
    (hf : DifferentiableAt ℝ f (q t)) (hzf : z =ᶠ[𝓝 t] f ∘ q)
    (h : deriv z t = p t * deriv q t) (hq0 : deriv q t ≠ 0) : p t = deriv f (q t) := by
  have hz : deriv z t = deriv f (q t) * deriv q t := by
    rw [hzf.deriv_eq, deriv_comp t hf hq]
  exact mul_right_cancel₀ hq0 (h.symm.trans hz)

/-- **A Legendrian curve is determined by its front.** Let `(q, p₁, z)` and `(q, p₂, z)` be curves
with the same front `(q, z)`, both satisfying `z' = pᵢ q'` on a set `U`, with `p₁` and `p₂`
continuous on `U`. If the times of `U` where the front is immersed, `q' ≠ 0`, are dense in `U`,
then `p₁ = p₂` on `U`: the momentum is the slope `z' / q'` of the front there, and extends by
continuity. -/
theorem eqOn_of_deriv_eq_mul_of_subset_closure {q p₁ p₂ z : ℝ → ℝ} {U : Set ℝ}
    (h₁ : ∀ t ∈ U, deriv z t = p₁ t * deriv q t) (h₂ : ∀ t ∈ U, deriv z t = p₂ t * deriv q t)
    (hp₁ : ContinuousOn p₁ U) (hp₂ : ContinuousOn p₂ U)
    (hU : U ⊆ closure {t ∈ U | deriv q t ≠ 0}) : EqOn p₁ p₂ U :=
  Set.EqOn.of_subset_closure (s := {t ∈ U | deriv q t ≠ 0})
    (fun t ht ↦ mul_right_cancel₀ ht.2 ((h₁ t ht.1).symm.trans (h₂ t ht.1))) hp₁ hp₂
    (fun _ ht ↦ ht.1) hU

/-- **A Legendrian curve is determined by its front when the front is immersed outside isolated
times.** Let `(q, p₁, z)` and `(q, p₂, z)` be curves with the same front `(q, z)`, both satisfying
`z' = pᵢ q'` on an open set `U`, with `p₁` and `p₂` continuous on `U`. If every time of `U` where
the front fails to be immersed, `q' = 0`, is isolated among such times, then `p₁ = p₂` on `U`. -/
theorem eqOn_of_deriv_eq_mul_of_eventually_ne {q p₁ p₂ z : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h₁ : ∀ t ∈ U, deriv z t = p₁ t * deriv q t) (h₂ : ∀ t ∈ U, deriv z t = p₂ t * deriv q t)
    (hp₁ : ContinuousOn p₁ U) (hp₂ : ContinuousOn p₂ U)
    (hq : ∀ t ∈ U, deriv q t = 0 → ∀ᶠ s in 𝓝[≠] t, deriv q s ≠ 0) : EqOn p₁ p₂ U := by
  refine eqOn_of_deriv_eq_mul_of_subset_closure h₁ h₂ hp₁ hp₂ fun t ht ↦ ?_
  by_cases ht0 : deriv q t = 0
  · -- Near a critical time, the front is immersed at every other time of `U`.
    have hU' : ∀ᶠ s in 𝓝[≠] t, s ∈ U := nhdsWithin_le_nhds (hU.mem_nhds ht)
    have hev : ∀ᶠ s in 𝓝[≠] t, s ∈ {s ∈ U | deriv q s ≠ 0} := hU'.and (hq t ht ht0)
    exact mem_closure_iff_frequently.2 (hev.frequently.filter_mono nhdsWithin_le_nhds)
  · exact subset_closure ⟨ht, ht0⟩

/-! ### Lines through the origin -/

/-- A line `t ↦ t • v` of `ℝ × ℝ × ℝ`, with `v ≠ 0`, along which `v` lies in the kernel of a
contact form, is a Legendrian embedding of `ℝ` for that kernel. -/
private theorem isLegendrianEmbedding_smul {α : SmoothForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ 1}
    (hα : α.IsContactForm) {v : ℝ × ℝ × ℝ} (hv : v ≠ 0)
    (hvα : ∀ t : ℝ, (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (t • v)) ∈ α.kerDistribution (t • v)) :
    IsLegendrianEmbedding 𝓘(ℝ, ℝ) α.kerDistribution (fun t : ℝ ↦ t • v) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hdf (t s : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun s : ℝ ↦ s • v) t s : ℝ × ℝ × ℝ) = s • v :=
    mfderiv_apply_of_hasDerivAt (hd t) s
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ (fun s : ℝ ↦ s • v) :=
    (contDiff_id.smul contDiff_const).contMDiff
  have himm : Manifold.IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ (fun s : ℝ ↦ s • v) :=
    hsmooth.isImmersion_of_injective_mfderiv (by simp) fun t (s s' : ℝ) hss' ↦
      smul_left_injective ℝ hv ((hdf t s).symm.trans (hss'.trans (hdf t s')))
  have hhor : IsHorizontalMap 𝓘(ℝ, ℝ) α.kerDistribution (fun s : ℝ ↦ s • v) := by
    refine isHorizontalMap_iff.2 fun t (s : ℝ) ↦ ?_
    -- The differential sends `s` to `s • v`, a multiple of the kernel vector `v`.
    have hs : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun s : ℝ ↦ s • v) t s =
        s • (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (t • v)) :=
      hdf t s
    rw [hs]
    exact Submodule.smul_mem _ _ (hvα t)
  exact ⟨⟨hα.isContactDistribution_kerDistribution, himm, hhor,
    by simp [Module.finrank_prod]⟩, (isClosedEmbedding_smul_left hv).isEmbedding⟩

/-- **Legendrian lines of `dz - p dq`.** For `c ≠ 0`, the line `t ↦ (0, c t, 0)` of
`ℝ × ℝ × ℝ`, along the `p`-axis, is a Legendrian embedding of `ℝ` for the kernel of the one-jet
contact form `dz - p dq`. -/
theorem isLegendrianEmbedding_innerProductContactForm_pAxis {c : ℝ} (hc : c ≠ 0) :
    IsLegendrianEmbedding 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t : ℝ ↦ ((0 : ℝ), c * t, (0 : ℝ))) := by
  have h : (fun t : ℝ ↦ ((0 : ℝ), c * t, (0 : ℝ))) = fun t : ℝ ↦ t • ((0, c, 0) : ℝ × ℝ × ℝ) := by
    funext t
    simp [mul_comm]
  rw [h]
  exact isLegendrianEmbedding_smul (isContactForm_innerProductContactForm ℝ) (by simp [hc])
    fun t ↦ (mem_kerDistribution_innerProductContactForm ℝ).2 (by simp)

/-- **Fronts do not determine Legendrian curves without an immersion condition.** The lines
`t ↦ (0, t, 0)` and `t ↦ (0, 2 t, 0)` of `ℝ × ℝ × ℝ` are Legendrian embeddings of `ℝ` for the
kernel of `dz - p dq`, with the same front `t ↦ (q, z) = (0, 0)`, a single point, but they are
different curves. Their fronts are immersed at no time. -/
theorem exists_isLegendrianEmbedding_ne_of_front_eq :
    ∃ γ₁ γ₂ : ℝ → ℝ × ℝ × ℝ,
      IsLegendrianEmbedding 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution γ₁ ∧
      IsLegendrianEmbedding 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution γ₂ ∧
      (∀ t, (γ₁ t).1 = (γ₂ t).1 ∧ (γ₁ t).2.2 = (γ₂ t).2.2) ∧ γ₁ ≠ γ₂ :=
  ⟨_, _, isLegendrianEmbedding_innerProductContactForm_pAxis one_ne_zero,
    isLegendrianEmbedding_innerProductContactForm_pAxis two_ne_zero, fun _ ↦ ⟨rfl, rfl⟩,
    fun h ↦ by simpa using congrArg (fun γ ↦ (γ 1).2.1) h⟩

/-- **The `y`-axis is Legendrian.** In `(ℝ³, dz - x dy)`, the `y`-axis `t ↦ (0, t, 0)` is a
Legendrian embedding of `ℝ` for the standard contact structure, the kernel of `dz - x dy`
(`TauCeti.kerDistribution_standardContactForm`). -/
theorem isLegendrianEmbedding_standardContactForm_yAxis :
    IsLegendrianEmbedding 𝓘(ℝ, ℝ) standardContactForm.kerDistribution
      (fun t : ℝ ↦ ((0 : ℝ), t, (0 : ℝ))) := by
  have h : (fun t : ℝ ↦ ((0 : ℝ), t, (0 : ℝ))) = fun t : ℝ ↦ t • ((0, 1, 0) : ℝ × ℝ × ℝ) := by
    funext t
    simp
  rw [h]
  exact isLegendrianEmbedding_smul isContactForm_standardContactForm (by simp) fun t ↦
    SmoothForm.mem_kerDistribution.2 ((standardContactForm_apply _ _).trans (by simp))

/-! ### Strict and non-strict models of the `y`-axis -/

/-- The map `(q, p, z) ↦ (-p, q, z)` as a continuous linear map. -/
private def negSwapCLM : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  (-(ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

private theorem coe_negSwapCLM : ⇑negSwapCLM = fun x : ℝ × ℝ × ℝ ↦ (-x.2.1, x.1, x.2.2) :=
  (rfl)

/-- **A strict model of the `y`-axis.** The coordinate swap `(q, p, z) ↦ (p, q, z)`, which carries
the zero section `{p = z = 0}` of the one-jet space onto the `y`-axis, pulls the standard contact
form `dz - x dy` back to the one-jet form `dz - p dq` exactly: it is a strict contactomorphism. -/
theorem mpullback_standardContactForm_swap :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun x : ℝ × ℝ × ℝ ↦ (x.2.1, x.1, x.2.2))
      standardContactForm.val = (innerProductContactForm ℝ).val := by
  -- The swap is an involution, and pulls `dz - p dq` back to `dz - x dy`.
  have hs : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
      (fun x : ℝ × ℝ × ℝ ↦ (x.2.1, x.1, x.2.2)) :=
    (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd) :
      ContDiff ℝ 1 _).contMDiff.mdifferentiable one_ne_zero
  rw [← mpullback_innerProductContactForm_real, ← mpullback_comp hs hs]
  exact mpullback_id _

/-- The map `(q, p, z) ↦ (-p, q, z)`, which also carries the zero section of the one-jet space onto
the `y`-axis, pulls the standard contact form `dz - x dy` back to `dz + p dq`. -/
theorem mpullback_standardContactForm_neg_swap_apply (x : ℝ × ℝ × ℝ)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) x) :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun x : ℝ × ℝ × ℝ ↦ (-x.2.1, x.1, x.2.2))
      standardContactForm.val x ![v] = v.2.2 + x.2.1 * v.1 := by
  rw [mpullback_apply_one, standardContactForm_apply, ← coe_negSwapCLM, negSwapCLM.mfderiv_eq]
  -- The tangent space of `ℝ × ℝ × ℝ` is `ℝ × ℝ × ℝ` by definition, and the coordinates of
  -- `negSwapCLM v` are those of `v`, permuted, with the second coordinate negated.
  simp only [neg_mul, sub_neg_eq_add]
  rfl

/-- The map `(q, p, z) ↦ (-p, q, z)` is not a strict contactomorphism from `dz - p dq` to
`dz - x dy`: it pulls `dz - x dy` back to `dz + p dq`, not to `dz - p dq`. -/
theorem mpullback_standardContactForm_neg_swap_ne :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun x : ℝ × ℝ × ℝ ↦ (-x.2.1, x.1, x.2.2))
      standardContactForm.val ≠ (innerProductContactForm ℝ).val := by
  intro h
  -- Evaluate both forms on `∂_q` at the point `(0, 1, 0)`.
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) ((0, 1, 0) : ℝ × ℝ × ℝ),
      v = ((1, 0, 0) : ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  have h' : mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun x : ℝ × ℝ × ℝ ↦ (-x.2.1, x.1, x.2.2))
      standardContactForm.val (0, 1, 0) ![v] = (innerProductContactForm ℝ).val (0, 1, 0) ![v] := by
    rw [h]
  rw [mpullback_standardContactForm_neg_swap_apply, innerProductContactForm_apply,
    Real.inner_apply, hv] at h'
  norm_num at h'

/-- **Strictness depends on the contact form.** For the contact form `β = eˣ (dz - x dy)`, which has
the same kernel as `dz - x dy`, the coordinate swap `(q, p, z) ↦ (p, q, z)` pulls `β` back to
`eᵖ (dz - p dq)`. Here `β` is given through its values. -/
theorem mpullback_swap_apply_of_eq_exp_smul_standardContactForm
    {β : SmoothForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ 1}
    (hβ : ∀ y : ℝ × ℝ × ℝ, β.val y = Real.exp y.1 • standardContactForm.val y)
    (x : ℝ × ℝ × ℝ) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) x) :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun x : ℝ × ℝ × ℝ ↦ (x.2.1, x.1, x.2.2)) β.val x
      ![v] = Real.exp x.2.1 * (innerProductContactForm ℝ).val x ![v] := by
  have h : mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
      (fun x : ℝ × ℝ × ℝ ↦ (x.2.1, x.1, x.2.2)) standardContactForm.val x ![v] =
        (innerProductContactForm ℝ).val x ![v] := by
    rw [mpullback_standardContactForm_swap]
  rw [mpullback_apply_one] at h ⊢
  rw [hβ, ContinuousAlternatingMap.smul_apply, smul_eq_mul, h]

/-- For the contact form `β = eˣ (dz - x dy)`, the coordinate swap `(q, p, z) ↦ (p, q, z)` is a
contactomorphism of the kernels which is not strict: it does not pull `β` back to `dz - p dq`.
Here `β` is given through its values. -/
theorem mpullback_swap_ne_of_eq_exp_smul_standardContactForm
    {β : SmoothForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ 1}
    (hβ : ∀ y : ℝ × ℝ × ℝ, β.val y = Real.exp y.1 • standardContactForm.val y) :
    mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun x : ℝ × ℝ × ℝ ↦ (x.2.1, x.1, x.2.2))
      β.val ≠ (innerProductContactForm ℝ).val := by
  intro h
  -- Evaluate both forms on `∂_z` at the point `(0, 1, 0)`, where `eᵖ = e ≠ 1`.
  obtain ⟨v, hv⟩ : ∃ v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) ((0, 1, 0) : ℝ × ℝ × ℝ),
      v = ((0, 0, 1) : ℝ × ℝ × ℝ) := ⟨_, rfl⟩
  have h' : mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun x : ℝ × ℝ × ℝ ↦ (x.2.1, x.1, x.2.2))
      β.val (0, 1, 0) ![v] = (innerProductContactForm ℝ).val (0, 1, 0) ![v] := by
    rw [h]
  rw [mpullback_swap_apply_of_eq_exp_smul_standardContactForm hβ, innerProductContactForm_apply,
    Real.inner_apply, hv] at h'
  norm_num at h'

/-! ### Isotropic submanifolds of `ℝ³` -/

/-- **No surface is tangent to the standard contact structure of `ℝ³`.** A map into `ℝ³` that is
tangent to `ker (dz - x dy)`, of class `C²` at `y` and with injective differential at `y`, has a
source of dimension at most one. -/
theorem IsHorizontalMap.finrank_le_one_of_standardContactForm {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
    {f : N → ℝ × ℝ × ℝ} (hf : IsHorizontalMap J standardContactForm.kerDistribution f) {y : N}
    (hfy : ContMDiffAt J 𝓘(ℝ, ℝ × ℝ × ℝ) 2 f y)
    (hinj : Injective (mfderiv J 𝓘(ℝ, ℝ × ℝ × ℝ) f y)) : finrank ℝ E' ≤ 1 := by
  have h := hf.two_mul_finrank_add_one_le (n := 1)
    isContactForm_standardContactForm.isContactDistribution_kerDistribution le_rfl hfy hinj
  simp only [Module.finrank_prod, Module.finrank_self] at h
  omega

end TauCeti
