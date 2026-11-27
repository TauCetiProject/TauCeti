/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Contact.Standard
public import TauCeti.Topology.Codiscrete
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Legendrian curves in the standard contact space and their fronts

The standard contact form on `V × V × ℝ`, with coordinates `(q, p, z)`, is
`α = dz - ⟪p, dq⟫` (`TauCeti.innerProductContactForm`). A differentiable curve
`t ↦ (q t, p t, z t)` is horizontal for its kernel exactly when

`z' = ⟪p, q'⟫`

at every time (`TauCeti.isHorizontalMap_innerProductContactForm_iff`).

This file specialises to `V = ℝ`, the space `ℝ³` with the form `dz - p dq`, where a curve
`(q, p, z)` is horizontal exactly when `z' = p q'`
(`TauCeti.isHorizontalMap_innerProductContactForm_real_iff`). A smooth curve is then a Legendrian
immersion exactly when moreover `(q', p') ≠ 0` at every time
(`TauCeti.isLegendrianImmersion_innerProductContactForm_real_iff`).

The **front** of a curve `(q, p, z)` is its projection `t ↦ (q t, z t)` to the `(q, z)`-plane.
Along a horizontal curve the front has velocity `(q', p q')`, so it is singular exactly where
`q' = 0` (`TauCeti.deriv_prodMk_eq_zero_iff_of_isHorizontalMap_innerProductContactForm`). Where it
is regular it determines the momentum as its slope, `p = z' / q'`
(`TauCeti.eq_div_deriv_of_isHorizontalMap_innerProductContactForm`). In particular a curve whose
front is the graph of a function `f`, `t ↦ (t, p t, f t)`, is horizontal exactly when `p = f'`, so
that it is the one-jet `t ↦ (t, f' t, f t)`
(`TauCeti.isHorizontalMap_innerProductContactForm_graph_iff`), a Legendrian embedding when `f` is
smooth (`TauCeti.isLegendrianEmbedding_innerProductContactForm_oneJet`).

Curves are parametrized by `ℝ`, which is diffeomorphic to every open interval; horizontality does
not depend on the parametrization (`TauCeti.isHorizontalMap_comp_diffeomorph_iff`).

Since the momentum is continuous, a horizontal curve whose front is regular on a dense set of
times, for instance outside a closed discrete set, is determined by its front
(`TauCeti.eq_of_isHorizontalMap_innerProductContactForm_of_dense`,
`TauCeti.eq_of_isHorizontalMap_innerProductContactForm_of_codiscrete`). Without that condition it
is not: the lines `t ↦ (0, c t, 0)` along the momentum axis are Legendrian embeddings for every
`c ≠ 0` (`TauCeti.isLegendrianEmbedding_innerProductContactForm_momentumLine`), and they all have
the one-point front `(0, 0)`.

## References

* H. Geiges, *Contact geometry*, in Handbook of Differential Geometry, vol. 2, North-Holland,
  2006, 315–382, arXiv:math/0307242, Lemma 2.45 (a Legendrian curve is determined by its front;
  stated there for the form `dz + x dy`, which is `dz - p dq` in the coordinates
  `(x, y) = (-p, q)`).
-/

public section

open Set Filter Function
open scoped Manifold InnerProductSpace ContDiff

namespace TauCeti

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {q p : ℝ → V} {z : ℝ → ℝ} {t : ℝ} {q' p' : V} {z' : ℝ}

/-- The tangent image of a curve `(q, p, z)` in `V × V × ℝ` at a time `t` where its components
have derivatives `q'`, `p'` and `z'` lies in the kernel of the standard contact form
`dz - ⟪p, dq⟫` exactly when `z' = ⟪p, q'⟫`. -/
theorem range_mfderiv_le_kerDistribution_innerProductContactForm_iff
    (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t) (hz : HasDerivAt z z' t) :
    LinearMap.range (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V × V × ℝ) (fun s ↦ (q s, p s, z s)) t).toLinearMap ≤
        (innerProductContactForm V).kerDistribution (q t, p t, z t) ↔
      z' = ⟪p t, q'⟫_ℝ := by
  have hγ : HasDerivAt (fun s ↦ (q s, p s, z s)) (q', p', z') t := hq.prodMk (hp.prodMk hz)
  -- The tangent image of `c` is `c • (q', p', z')`, read in the model space. Here and below a
  -- real number `c` is a tangent vector of `ℝ`, whose tangent spaces are `ℝ` by definition.
  have hv (c : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V × V × ℝ) (fun s ↦ (q s, p s, z s)) t c = c • (q', p', z') :=
    hγ.hasFDerivAt.mfderiv_apply c
  rw [LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
  simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
  refine ⟨fun h ↦ ?_, fun h (c : ℝ) ↦ (mem_kerDistribution_innerProductContactForm V).2 ?_⟩
  · have h1 := (mem_kerDistribution_innerProductContactForm V).1 (h (1 : ℝ))
    rw [hv] at h1
    simpa using h1
  · rw [hv c]
    simp [h, inner_smul_right]

/-- A differentiable curve `t ↦ (q t, p t, z t)` in `V × V × ℝ` is horizontal for the standard
contact structure `ker (dz - ⟪p, dq⟫)` exactly when `z' = ⟪p, q'⟫` at every time. -/
theorem isHorizontalMap_innerProductContactForm_iff (hq : Differentiable ℝ q)
    (hp : Differentiable ℝ p) (hz : Differentiable ℝ z) :
    IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm V).kerDistribution
        (fun t ↦ (q t, p t, z t)) ↔
      ∀ t, deriv z t = ⟪p t, deriv q t⟫_ℝ :=
  isHorizontalMap_iff_range_mfderiv_le.trans <| forall_congr' fun t ↦
    range_mfderiv_le_kerDistribution_innerProductContactForm_iff
    (hq t).hasDerivAt (hp t).hasDerivAt (hz t).hasDerivAt

end InnerProductSpace

section Real

variable {q p z : ℝ → ℝ}

/-- On `ℝ³` with the contact form `dz - p dq`, a differentiable curve `t ↦ (q t, p t, z t)` is
horizontal exactly when `z' = p q'` at every time. -/
theorem isHorizontalMap_innerProductContactForm_real_iff (hq : Differentiable ℝ q)
    (hp : Differentiable ℝ p) (hz : Differentiable ℝ z) :
    IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
        (fun t ↦ (q t, p t, z t)) ↔
      ∀ t, deriv z t = p t * deriv q t := by
  simp only [isHorizontalMap_innerProductContactForm_iff hq hp hz, Real.inner_apply]

/-- On `ℝ³` with the contact form `dz - p dq`, a smooth curve `t ↦ (q t, p t, z t)` is a Legendrian
immersion exactly when `z' = p q'` and `(q', p') ≠ 0` at every time. Since `z'` is determined by
`q'`, the velocity `(q', p', z')` vanishes exactly when `q'` and `p'` do. -/
theorem isLegendrianImmersion_innerProductContactForm_real_iff (hq : ContDiff ℝ ∞ q)
    (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) :
    IsLegendrianImmersion 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
        (fun t ↦ (q t, p t, z t)) ↔
      ∀ t, deriv z t = p t * deriv q t ∧ (deriv q t ≠ 0 ∨ deriv p t ≠ 0) := by
  have hor := isHorizontalMap_innerProductContactForm_real_iff (hq.differentiable (by simp))
    (hp.differentiable (by simp)) (hz.differentiable (by simp))
  -- The tangent map at `t` sends `c` to `c • (q', p', z')`, so it is injective exactly when the
  -- velocity is nonzero. A real number `c` is a tangent vector of `ℝ`, whose tangent spaces are
  -- `ℝ` by definition.
  have hinj (t : ℝ) : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun s ↦ (q s, p s, z s)) t) ↔
      (deriv q t, deriv p t, deriv z t) ≠ 0 := by
    have hγ : HasDerivAt (fun s ↦ (q s, p s, z s)) (deriv q t, deriv p t, deriv z t) t :=
      ((hq.differentiable (by simp) t).hasDerivAt.prodMk
        ((hp.differentiable (by simp) t).hasDerivAt.prodMk
          (hz.differentiable (by simp) t).hasDerivAt))
    have hv (c : ℝ) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (fun s ↦ (q s, p s, z s)) t c =
        c • (deriv q t, deriv p t, deriv z t) :=
      hγ.hasFDerivAt.mfderiv_apply c
    refine ⟨fun h h0 ↦ ?_, fun h c₁ c₂ hc ↦ ?_⟩
    · exact one_ne_zero (α := ℝ)
        (h (a₁ := (1 : ℝ)) (a₂ := (0 : ℝ)) (by rw [hv, hv, h0, smul_zero, smul_zero]))
    · rw [hv c₁, hv c₂] at hc
      exact smul_left_injective ℝ h hc
  have hγ : ContDiff ℝ ∞ (fun t ↦ (q t, p t, z t)) := hq.prodMk (hp.prodMk hz)
  refine ⟨fun h t ↦ ⟨hor.1 h.isHorizontalMap t, ?_⟩, fun h ↦ ⟨?_, ?_, hor.2 fun t ↦ (h t).1, ?_⟩⟩
  · have hne := (hinj t).1 (h.isImmersion.mfderiv_injective (by simp) t)
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hne (by simp [hor.1 h.isHorizontalMap t, hc.1, hc.2])
  · exact SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution.1
      (isContactForm_innerProductContactForm ℝ)
  · refine (contMDiff_iff_contDiff.2 hγ).isImmersion_of_injective_mfderiv (by simp) fun t ↦ ?_
    refine (hinj t).2 fun h0 ↦ ?_
    simp only [Prod.mk_eq_zero] at h0
    rcases (h t).2 with h1 | h1
    · exact h1 h0.1
    · exact h1 h0.2.1
  · simp

/-- Along a horizontal curve of `ℝ³`, the front `t ↦ (q t, z t)` has velocity `(q', p q')`, so it
is singular exactly at the times where `q' = 0`. -/
theorem deriv_prodMk_eq_zero_iff_of_isHorizontalMap_innerProductContactForm
    (hq : Differentiable ℝ q) (hp : Differentiable ℝ p) (hz : Differentiable ℝ z)
    (h : IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ (q t, p t, z t))) (t : ℝ) :
    deriv (fun s ↦ (q s, z s)) t = 0 ↔ deriv q t = 0 := by
  have hfront : HasDerivAt (fun s ↦ (q s, z s)) (deriv q t, deriv z t) t :=
    (hq t).hasDerivAt.prodMk (hz t).hasDerivAt
  rw [hfront.deriv, (isHorizontalMap_innerProductContactForm_real_iff hq hp hz).1 h t,
    Prod.mk_eq_zero]
  exact ⟨And.left, fun h0 ↦ ⟨h0, by rw [h0, mul_zero]⟩⟩

/-- **The front determines the momentum where it is regular.** Along a horizontal curve of `ℝ³`,
at a time where `q' ≠ 0` the momentum is the slope `p = z' / q'` of the front. -/
theorem eq_div_deriv_of_isHorizontalMap_innerProductContactForm
    (hq : Differentiable ℝ q) (hp : Differentiable ℝ p) (hz : Differentiable ℝ z)
    (h : IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ (q t, p t, z t))) {t : ℝ} (ht : deriv q t ≠ 0) :
    p t = deriv z t / deriv q t := by
  rw [(isHorizontalMap_innerProductContactForm_real_iff hq hp hz).1 h t,
    mul_div_cancel_right₀ _ ht]

/-- **Fronts that are graphs.** A curve `t ↦ (t, p t, f t)` of `ℝ³`, whose front is the graph of
`f`, is horizontal exactly when `p = f'`, that is, when it is the one-jet `t ↦ (t, f' t, f t)`. -/
theorem isHorizontalMap_innerProductContactForm_graph_iff {f : ℝ → ℝ} (hp : Differentiable ℝ p)
    (hf : Differentiable ℝ f) :
    IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
        (fun t ↦ (t, p t, f t)) ↔ p = deriv f := by
  rw [isHorizontalMap_innerProductContactForm_real_iff (q := fun t ↦ t) differentiable_id hp hf,
    funext_iff]
  simp [eq_comm]

/-- The one-jet `t ↦ (t, f' t, f t)` of a smooth function `f` is a Legendrian embedding of `ℝ`
into `ℝ³` with the contact form `dz - p dq`. -/
theorem isLegendrianEmbedding_innerProductContactForm_oneJet {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    IsLegendrianEmbedding 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ (t, deriv f t, f t)) := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.1 hf).2
  refine ⟨(isLegendrianImmersion_innerProductContactForm_real_iff (q := fun t ↦ t) contDiff_id
    hf' hf).2 fun t ↦ ⟨by simp, Or.inl (by simp)⟩, ?_⟩
  exact Function.LeftInverse.isEmbedding (f := Prod.fst) (fun _ ↦ rfl) continuous_fst
    (continuous_id.prodMk (hf'.continuous.prodMk hf.continuous))

/-- **A Legendrian curve is determined by its front** (Geiges, Lemma 2.45). Two differentiable
horizontal curves `(q, p₁, z)` and `(q, p₂, z)` of `ℝ³` with the same front `(q, z)` coincide when
the front is regular, `q' ≠ 0`, on a dense set of times: there `p₁ = z' / q' = p₂`, and the
momenta are continuous. -/
theorem eq_of_isHorizontalMap_innerProductContactForm_of_dense {p₁ p₂ : ℝ → ℝ}
    (hq : Differentiable ℝ q) (hp₁ : Differentiable ℝ p₁) (hp₂ : Differentiable ℝ p₂)
    (hz : Differentiable ℝ z)
    (h₁ : IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ (q t, p₁ t, z t)))
    (h₂ : IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ (q t, p₂ t, z t)))
    (hdense : Dense {t | deriv q t ≠ 0}) :
    p₁ = p₂ := by
  refine Continuous.ext_on hdense hp₁.continuous hp₂.continuous fun t ht ↦ ?_
  rw [eq_div_deriv_of_isHorizontalMap_innerProductContactForm hq hp₁ hz h₁ ht,
    eq_div_deriv_of_isHorizontalMap_innerProductContactForm hq hp₂ hz h₂ ht]

/-- **A Legendrian curve is determined by its front** (Geiges, Lemma 2.45). Two differentiable
horizontal curves `(q, p₁, z)` and `(q, p₂, z)` of `ℝ³` with the same front `(q, z)` coincide when
the front is regular, `q' ≠ 0`, outside a discrete closed set of times. -/
theorem eq_of_isHorizontalMap_innerProductContactForm_of_codiscrete {p₁ p₂ : ℝ → ℝ}
    (hq : Differentiable ℝ q) (hp₁ : Differentiable ℝ p₁) (hp₂ : Differentiable ℝ p₂)
    (hz : Differentiable ℝ z)
    (h₁ : IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ (q t, p₁ t, z t)))
    (h₂ : IsHorizontalMap 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ (q t, p₂ t, z t)))
    (hcod : {t | deriv q t ≠ 0} ∈ codiscrete ℝ) :
    p₁ = p₂ := by
  refine eq_of_isHorizontalMap_innerProductContactForm_of_dense hq hp₁ hp₂ hz h₁ h₂ ?_
  rw [dense_iff_closure_eq, ← univ_subset_iff]
  simpa using isOpen_univ.subset_closure_inter_of_mem_codiscreteWithin hcod

/-- For `c ≠ 0`, the line `t ↦ (0, c t, 0)` along the momentum axis is a Legendrian embedding of
`ℝ` into `ℝ³` with the contact form `dz - p dq`. Its front is the single point `(0, 0)`, so for
`c = 1` and `c = 2` two different Legendrian embeddings have the same front: without regularity of
the front on a dense set, a Legendrian curve is not determined by its front. -/
theorem isLegendrianEmbedding_innerProductContactForm_momentumLine {c : ℝ} (hc : c ≠ 0) :
    IsLegendrianEmbedding 𝓘(ℝ, ℝ) (innerProductContactForm ℝ).kerDistribution
      (fun t ↦ ((0 : ℝ), c * t, (0 : ℝ))) := by
  refine ⟨(isLegendrianImmersion_innerProductContactForm_real_iff (q := fun _ ↦ 0)
    (z := fun _ ↦ 0) contDiff_const (contDiff_const.mul contDiff_id) contDiff_const).2
    fun t ↦ ⟨by simp, Or.inr (by simp [hc])⟩, ?_⟩
  exact Function.LeftInverse.isEmbedding (f := fun x ↦ x.2.1 / c) (fun t ↦ by simp [hc])
    (by fun_prop) (by fun_prop)

end Real

end TauCeti
