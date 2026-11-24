/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.InnerProductSpace.Indefinite
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.Normed.Module.NegativeSubspace

/-!
# Polar factors of negative blocks along a composition

On the product `E × F` of a finite-dimensional real inner product space `E` and a real normed
space `F`, consider the split quadratic form `Q(u, v) = -‖u‖² + ‖v‖²`. Let `A` be an operator
mapping the open negative cone `‖v‖ < ‖u‖` into itself, for instance one preserving `Q`, and let
`C : E →L[ℝ] E × F` be an *isometric negative column*, `‖(C u).1‖² - ‖(C u).2‖² = ‖u‖²`, such as
the negative column `u ↦ B (u, 0)` of another operator `B` preserving `Q`. The negative blocks
`fst ∘ A ∘ inl`, `fst ∘ C` and `fst ∘ A ∘ C` are invertible, and their polar factors `h`, `g` and
`k` are orthogonal. In general `k ≠ h g`: polar factors are not multiplicative. The two have
determinants of the same sign (`ContinuousLinearMap.sign_det_fst_comp_comp_of_norm_snd_lt`), but
over a parameter space that only gives a path for each value of the parameter, chosen
independently.

This file joins `h g` to `k` by an explicit path of polar factors, continuous in the operators
(`ContinuousLinearMap.exists_path_polarFactor_fst_comp_comp`). The path is the polar factor of the
segment of operators

`(1 - t) • (fst ∘ A ∘ inl) ∘ g + t • (fst ∘ A ∘ C)`, `0 ≤ t ≤ 1`,

which is `fst ∘ A` applied to the segment of columns `(1 - t) • (inl ∘ g) + t • C`. These columns
stay strictly negative for `Q` (`ContinuousLinearMap.norm_smul_snd_lt_norm_segment_polarFactor`):
writing `fst ∘ C = g P` with `P = |fst ∘ C|` positive, the first component is
`g ((1 - t) u + t P u)`, while `Q (C u) = -‖u‖²` bounds the second component. Since `A` maps the
open negative cone into itself, it keeps these columns off `0 × F`, so every operator of the
segment is invertible, and the polar factor depends continuously on invertible operators
(`ContinuousLinearMap.continuousOn_polarFactor`). At `t = 0` the polar factor of
`(fst ∘ A ∘ inl) ∘ g` is `h g` because `g` is orthogonal
(`ContinuousLinearMap.polarFactor_comp_linearIsometryEquiv`).

For the derivatives `A₀₁` and `A₁₂` at the centre of the transitions between three Morse charts,
with `C = A₁₂ ∘ inl`, this joins the composite `h₀₁ h₁₂` of the chart comparisons to the direct
comparison `h₀₂` of the first and last chart, through linear isometries depending continuously on
the charts.

## Main results

* `ContinuousLinearMap.norm_smul_snd_lt_norm_segment_polarFactor`: the segment from
  `inl ∘ polar (fst ∘ C)` to an isometric negative column `C` stays in the negative cone.
* `ContinuousLinearMap.exists_path_polarFactor_fst_comp_comp`: a path of linear isometries,
  continuous in a parameter, from `polar (fst ∘ A ∘ inl) ∘ polar (fst ∘ C)` to
  `polar (fst ∘ A ∘ C)`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Lemma 3.6 and Remark 3.3, the comparison of the negative discs of two Morse charts.
-/

public section

open Set Function unitInterval
open scoped RealInnerProductSpace

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Column

variable (C : E →L[ℝ] E × F) (hC : ∀ u, ‖(C u).1‖ ^ 2 - ‖(C u).2‖ ^ 2 = ‖u‖ ^ 2)

include hC

/-- **The segment from the polar factor to an isometric negative column stays negative.** Let `C`
be an isometric negative column, `‖(C u).1‖² - ‖(C u).2‖² = ‖u‖²`, with negative block
`N = fst ∘ C` and polar factor `g` of `N`. For `0 ≤ t ≤ 1` and `u ≠ 0`, the column
`(1 - t) • (g u, 0) + t • C u` lies in the open negative cone `‖v‖ < ‖w‖` of `(w, v) ∈ E × F`. -/
theorem norm_smul_snd_lt_norm_segment_polarFactor {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {u : E}
    (hu : u ≠ 0) :
    ‖t • (C u).2‖ < ‖(1 - t) • (fst ℝ E F ∘L C).polarFactor u + t • (C u).1‖ := by
  set N := fst ℝ E F ∘L C
  have hN (u : E) : N u = (C u).1 := rfl
  -- Writing `N = g P`, the first component is `g ((1 - t) u + t P u)`, of norm
  -- `‖(1 - t) u + t P u‖`, and `P` is positive with `‖P u‖ = ‖N u‖`.
  have hfst : (1 - t) • N.polarFactor u + t • (C u).1 =
      N.polarFactor ((1 - t) • u + t • N.modulus u) := by
    rw [map_add, map_smul, map_smul, polarFactor_modulus_apply, hN]
  rw [hfst, norm_polarFactor_apply_of_injective N (C.isInvertible_fst_of_norm_sq_sub hC).injective]
  have hip : 0 ≤ ⟪u, N.modulus u⟫ := by
    rw [real_inner_comm]
    exact N.isPositive_modulus.inner_nonneg_left u
  have hsq : ‖t • (C u).2‖ ^ 2 < ‖(1 - t) • u + t • N.modulus u‖ ^ 2 := by
    simp only [norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right,
      norm_modulus_apply, hN, Real.norm_eq_abs, abs_of_nonneg ht₀,
      abs_of_nonneg (sub_nonneg.2 ht₁)]
    have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
    nlinarith [hC u, mul_nonneg (mul_nonneg (sub_nonneg.2 ht₁) ht₀) hip, sq_nonneg (1 - 2 * t),
      mul_pos hu' hu']
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

end Column

/-- **A path from the composite of two polar factors to the polar factor of the composite.** Let
`A x` be operators of `E × F` mapping the open negative cone `‖v‖ < ‖u‖` into itself, such as
operators preserving `Q(u, v) = -‖u‖² + ‖v‖²`, and let `C x` be isometric negative columns,
`‖(C x u).1‖² - ‖(C x u).2‖² = ‖u‖²`, both continuous in a parameter `x`. Write `h x`, `g x` and
`k x` for the polar factors of the negative blocks `fst ∘ A x ∘ inl`, `fst ∘ C x` and
`fst ∘ A x ∘ C x`. Then there are linear isometric equivalences `γ x t`, `t ∈ [0, 1]`, of `E`,
jointly continuous in `x` and `t` for the operator norm, with `γ x 0 = h x ∘ g x` and
`γ x 1 = k x`. -/
theorem exists_path_polarFactor_fst_comp_comp {X : Type*} [TopologicalSpace X]
    {A : X → E × F →L[ℝ] E × F} (hAc : Continuous A)
    (hA : ∀ x (z : E × F), ‖z.2‖ < ‖z.1‖ → ‖(A x z).2‖ < ‖(A x z).1‖)
    {C : X → E →L[ℝ] E × F} (hCc : Continuous C)
    (hC : ∀ x u, ‖(C x u).1‖ ^ 2 - ‖(C x u).2‖ ^ 2 = ‖u‖ ^ 2) :
    ∃ γ : X → I → (E ≃ₗᵢ[ℝ] E),
      Continuous (fun q : X × I ↦ (γ q.1 q.2 : E →L[ℝ] E)) ∧
      (∀ x, ⇑(γ x 0) = (fst ℝ E F ∘L A x ∘L inl ℝ E F).polarFactor ∘L
        (fst ℝ E F ∘L C x).polarFactor) ∧
      ∀ x, ⇑(γ x 1) = (fst ℝ E F ∘L A x ∘L C x).polarFactor := by
  -- The polar factor of an injective endomorphism of `E` is a linear isometric equivalence.
  let iso (T : E →L[ℝ] E) (hT : Injective T) : E ≃ₗᵢ[ℝ] E :=
    (T.polarIsometry hT).toLinearIsometryEquiv rfl
  -- The negative blocks `fst ∘ C x` are invertible, so their polar factors are orthogonal and
  -- depend continuously on `x`.
  have hNinj (x : X) : Injective (fst ℝ E F ∘L C x) :=
    ((C x).isInvertible_fst_of_norm_sq_sub (hC x)).injective
  have hgc : Continuous fun x ↦ (fst ℝ E F ∘L C x).polarFactor :=
    continuousOn_polarFactor.comp_continuous (by fun_prop)
      fun x ↦ isUnit_modulus_iff_injective.2 (hNinj x)
  -- The segment of columns from `inl ∘ g x` to `C x` stays in the negative cone, so after `A x`
  -- its negative blocks are injective.
  set L : X → ℝ → E →L[ℝ] E × F := fun x t ↦
    (1 - t) • (inl ℝ E F ∘L (fst ℝ E F ∘L C x).polarFactor) + t • C x
  have hLc : Continuous fun q : X × I ↦ L q.1 q.2 :=
    ((continuous_const.sub (continuous_subtypeVal.comp continuous_snd)).smul
      (continuous_const.clm_comp (hgc.comp continuous_fst))).add
      ((continuous_subtypeVal.comp continuous_snd).smul (hCc.comp continuous_fst))
  have hTinj (x : X) (t : I) : Injective (fst ℝ E F ∘L A x ∘L L x t) :=
    (A x ∘L L x t).injective_fst_comp_of_norm_snd_lt fun u hu ↦ hA x _ <| by
      simpa [L] using
        (C x).norm_smul_snd_lt_norm_segment_polarFactor (hC x) t.property.1 t.property.2 hu
  refine ⟨fun x t ↦ iso _ (hTinj x t), ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · refine (continuousOn_polarFactor.comp_continuous
      (continuous_const.clm_comp ((hAc.comp continuous_fst).clm_comp hLc))
      fun q ↦ isUnit_modulus_iff_injective.2 (hTinj q.1 q.2)).congr fun q ↦ ?_
    ext u
    simp [iso]
  · -- At `t = 0` the operator is `(fst ∘ A x ∘ inl) ∘ g x`, with `g x` orthogonal.
    have h0 : fst ℝ E F ∘L A x ∘L L x 0 =
        (fst ℝ E F ∘L A x ∘L inl ℝ E F) ∘L (iso _ (hNinj x) : E →L[ℝ] E) := by
      ext u
      simp [L, iso]
    simp only [iso, LinearIsometry.coe_toLinearIsometryEquiv, coe_polarIsometry,
      Set.Icc.coe_zero]
    rw [h0, polarFactor_comp_linearIsometryEquiv]
    ext u
    simp [iso]
  · simp [iso, L]

end ContinuousLinearMap
