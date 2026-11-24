/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.ComplexLineCone
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Mass control of approximately positive fields by a taming form

Let `ξ` be a field of two-vectors on a measure space `X`, for instance the density of a current
of degree two on a four-manifold, and let `J x` be an orthogonal almost complex structure at each
point. If a two-form `Ω` tames every `J x`, `Ω(v, J v) ≥ c₀ ‖v‖²`, and is bounded by `B`, then the
pointwise estimate `TauCeti.AlmostComplexStructure.mul_norm_le_inner_add_mul_infDist_positiveCone`
integrates to

`c₀ ∫ ‖ξ‖ ≤ ∫ ⟪Ω, ξ⟫ + (B + c₀) ∫ dist(ξ, positiveCone)`

(`TauCeti.AlmostComplexStructure.mul_integral_norm_le_integral_inner_add_mul_integral_infDist`):
the total norm is controlled by the pairing with `Ω` and the integrated distance to the cone of
positive `(1,1)`-forms of `J`.

In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, the pairing of
the dilated curvature current with a taming form `Ω = K π^*ω_C + dλ` is a topological quantity,
`K m area(C)` for a current of transverse flux `m`. Its product-chart form is
`TauCeti.integral_wedge_smul_compContinuousLinearMap_fst_add_extDeriv`, and its global form over a
σ-compact preconnected surface with trivial normal line is
`TauCeti.integralTopForm_wedge_smul_mpullback_fst_add_mextDerivₗ`.
The cone defect is
bounded by a small error plus a small multiple of the mass itself. A second theorem absorbs that
multiple: if `∫ dist(ξ, positiveCone) ≤ ε + δ ∫ ‖ξ‖` with `(B + c₀) δ < c₀`, then

`∫ ‖ξ‖ ≤ (∫ ⟪Ω, ξ⟫ + (B + c₀) ε) / (c₀ - (B + c₀) δ)`

(`TauCeti.AlmostComplexStructure.integral_norm_le_div_of_integral_infDist_le`).

**Currents given by two-forms.** A current of degree two with a density is a field `T` of
two-forms, and its pairing with `Ω` is the integral of the top form `T ∧ Ω`, not of an inner
product. On an oriented four-dimensional space let `ξ_T` be the two-vector representing `T`,
`T(u, w) = ⟪ξ_T, u ∧ w⟫`, the representation in which the cone defect of the cutoff current is
estimated. On a positively oriented orthonormal basis `b`, `(T ∧ Ω)(b) = ⟪ξ_Ω, ⋆ξ_T⟫`
(`Orientation.wedge_apply_orthonormalBasis_eq_inner`). The Hodge star is an isometry and, when
`J` is compatible with the orientation, preserves the cone of positive `(1,1)`-forms
(`TauCeti.AlmostComplexStructure.infDist_hodgeStar_positiveCone`), so the two estimates above,
applied to `⋆ξ_T`, hold with the wedge pairing:

`c₀ ∫ ‖ξ_T‖ ≤ ∫ (T ∧ Ω)(b) + (B + c₀) ∫ dist(ξ_T, positiveCone)`

(`TauCeti.AlmostComplexStructure.mul_integral_norm_le_integral_wedge_add_mul_integral_infDist`),
and the absorbed form
`TauCeti.AlmostComplexStructure.integral_norm_le_integral_wedge_add_mul_div_of_integral_infDist_le`.
These are the forms in which the integral of `T ∧ Ω` can be replaced by its topological value
`K m area(C)`.

The norm here is the inner product norm of two-vectors, which bounds the mass norm of the
corresponding current up to a constant depending only on the dimension. The pointwise mass of a
current is the mass norm of its two-vector density (here `⋆ξ_T`, which has the same inner product
norm as `ξ_T`), the norm dual to the comass of forms. On an `n`-dimensional space the comass is
at most the inner product norm (`ContinuousAlternatingMap.norm_le_sqrt_alternatingFormInner_self`)
and at least `1 / √(n choose 2)` times it
(`ContinuousAlternatingMap.sqrt_alternatingFormInner_self_le`), so dually the mass norm lies
between the inner product norm and `√(n choose 2)` times it.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open MeasureTheory Metric Module exteriorPower
open scoped RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : X → AlmostComplexStructure V} {c₀ B : ℝ}

section TwoVector

variable {Ω ξ : X → ⋀[ℝ]^2 V}

/-- **Mass control by a taming form and the cone defect.** If, almost everywhere, `J x` is
orthogonal, `Ω x` tames it with constant `c₀ ≥ 0` and `‖Ω x‖ ≤ B`, then a field `ξ` of two-vectors
satisfies `c₀ ∫ ‖ξ‖ ≤ ∫ ⟪Ω, ξ⟫ + (B + c₀) ∫ dist(ξ, positiveCone)`. -/
theorem mul_integral_norm_le_integral_inner_add_mul_integral_infDist
    (hJ : ∀ᵐ x ∂μ, ∀ v w, ⟪J x v, J x w⟫ = ⟪v, w⟫) (hc₀ : 0 ≤ c₀)
    (hΩ : ∀ᵐ x ∂μ, ∀ v, c₀ * ‖v‖ ^ 2 ≤ ⟪Ω x, ιMulti ℝ 2 ![v, J x v]⟫)
    (hB : ∀ᵐ x ∂μ, ‖Ω x‖ ≤ B) (hξ : Integrable (fun x ↦ ‖ξ x‖) μ)
    (hP : Integrable (fun x ↦ ⟪Ω x, ξ x⟫) μ)
    (hD : Integrable (fun x ↦ infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V))) μ) :
    c₀ * ∫ x, ‖ξ x‖ ∂μ ≤ ∫ x, ⟪Ω x, ξ x⟫ ∂μ +
      (B + c₀) * ∫ x, infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V)) ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hP (hD.const_mul _)]
  refine integral_mono_ae (hξ.const_mul _) (hP.add (hD.const_mul _)) ?_
  filter_upwards [hJ, hΩ, hB] with x hJx hΩx hBx
  have h := mul_norm_le_inner_add_mul_infDist_positiveCone hJx hc₀ hΩx (ξ x)
  have hd := infDist_nonneg (x := ξ x) (s := ((J x).positiveCone : Set (⋀[ℝ]^2 V)))
  nlinarith

/-- **Absorption of a small multiple of the mass.** Under the hypotheses of
`TauCeti.AlmostComplexStructure.mul_integral_norm_le_integral_inner_add_mul_integral_infDist`, with
`0 ≤ B`, suppose the cone defect is at most `ε` plus a small multiple `δ` of the total norm,
`∫ dist(ξ, positiveCone) ≤ ε + δ ∫ ‖ξ‖`, where `(B + c₀) δ < c₀`. Then
`∫ ‖ξ‖ ≤ (∫ ⟪Ω, ξ⟫ + (B + c₀) ε) / (c₀ - (B + c₀) δ)`. -/
theorem integral_norm_le_div_of_integral_infDist_le
    (hJ : ∀ᵐ x ∂μ, ∀ v w, ⟪J x v, J x w⟫ = ⟪v, w⟫) (hc₀ : 0 ≤ c₀)
    (hΩ : ∀ᵐ x ∂μ, ∀ v, c₀ * ‖v‖ ^ 2 ≤ ⟪Ω x, ιMulti ℝ 2 ![v, J x v]⟫)
    (hB₀ : 0 ≤ B) (hB : ∀ᵐ x ∂μ, ‖Ω x‖ ≤ B) (hξ : Integrable (fun x ↦ ‖ξ x‖) μ)
    (hP : Integrable (fun x ↦ ⟪Ω x, ξ x⟫) μ)
    (hD : Integrable (fun x ↦ infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V))) μ)
    {ε δ : ℝ}
    (hDle : ∫ x, infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V)) ∂μ ≤
      ε + δ * ∫ x, ‖ξ x‖ ∂μ)
    (hδ : (B + c₀) * δ < c₀) :
    ∫ x, ‖ξ x‖ ∂μ ≤ (∫ x, ⟪Ω x, ξ x⟫ ∂μ + (B + c₀) * ε) / (c₀ - (B + c₀) * δ) := by
  have h := mul_integral_norm_le_integral_inner_add_mul_integral_infDist hJ hc₀ hΩ hB hξ hP hD
  have hA : 0 ≤ B + c₀ := add_nonneg hB₀ hc₀
  have h' := mul_le_mul_of_nonneg_left hDle hA
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end TwoVector

/-! ### Currents given by fields of two-forms -/

section Form

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  {b : OrthonormalBasis (Fin 4) ℝ V} (hb : b.toBasis.orientation = o)
  {T Ω : X → V [⋀^Fin 2]→L[ℝ] ℝ}

include hkl hb in
/-- **Mass control of a field of two-forms by its wedge pairing with a taming form.** Let `T` and
`Ω` be fields of two-forms on an oriented four-dimensional real inner product space, and write
`ξ_T` for the two-vector representing `T`, `T(u, w) = ⟪ξ_T, u ∧ w⟫`. Suppose that, almost
everywhere, `J x` has a positively oriented unitary frame, `Ω x` tames `J x` with constant
`c₀ ≥ 0` and the two-vector representing `Ω x` has norm at most `B`. Then, for a positively
oriented orthonormal basis `b`,

`c₀ ∫ ‖ξ_T‖ ≤ ∫ (T ∧ Ω)(b) + (B + c₀) ∫ dist(ξ_T, positiveCone)`. -/
theorem mul_integral_norm_le_integral_wedge_add_mul_integral_infDist
    (hJ : ∀ᵐ x ∂μ, ∃ e : OrthonormalBasis (Fin 4) ℝ V,
      J x (e 0) = e 1 ∧ J x (e 2) = e 3 ∧ e.toBasis.orientation = o)
    (hc₀ : 0 ≤ c₀) (hΩ : ∀ᵐ x ∂μ, ∀ v, c₀ * ‖v‖ ^ 2 ≤ Ω x ![v, J x v])
    (hB : ∀ᵐ x ∂μ, ‖(alternatingFormEquiv V 2).symm (Ω x)‖ ≤ B)
    (hT : Integrable (fun x ↦ ‖(alternatingFormEquiv V 2).symm (T x)‖) μ)
    (hP : Integrable (fun x ↦ (T x).wedge (Ω x) b) μ)
    (hD : Integrable (fun x ↦ infDist ((alternatingFormEquiv V 2).symm (T x))
      ((J x).positiveCone : Set (⋀[ℝ]^2 V))) μ) :
    c₀ * ∫ x, ‖(alternatingFormEquiv V 2).symm (T x)‖ ∂μ ≤ ∫ x, (T x).wedge (Ω x) b ∂μ +
      (B + c₀) * ∫ x, infDist ((alternatingFormEquiv V 2).symm (T x))
        ((J x).positiveCone : Set (⋀[ℝ]^2 V)) ∂μ := by
  -- Apply the two-vector estimate to `⋆ξ_T`, which pairs with the two-vector of `Ω` to `T ∧ Ω`.
  set ξ : X → ⋀[ℝ]^2 V := fun x ↦ o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (T x))
  have hnorm (x : X) : ‖ξ x‖ = ‖(alternatingFormEquiv V 2).symm (T x)‖ := o.norm_hodgeStar hkl _
  have hpair (x : X) : ⟪(alternatingFormEquiv V 2).symm (Ω x), ξ x⟫ = (T x).wedge (Ω x) b :=
    (o.wedge_apply_orthonormalBasis_eq_inner even_two hkl b hb (T x) (Ω x)).symm
  have hdist : ∀ᵐ x ∂μ, infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V)) =
      infDist ((alternatingFormEquiv V 2).symm (T x)) ((J x).positiveCone : Set (⋀[ℝ]^2 V)) := by
    filter_upwards [hJ] with x ⟨e, h₀, h₂, he⟩
    exact infDist_hodgeStar_positiveCone h₀ h₂ hkl he _
  have h := mul_integral_norm_le_integral_inner_add_mul_integral_infDist (ξ := ξ)
    (hJ.mono fun x ⟨e, h₀, h₂, _⟩ ↦ inner_apply_apply_of_orthonormalBasis h₀ h₂) hc₀
    (hΩ.mono fun x hx v ↦ by rw [inner_alternatingFormEquiv_symm_ιMulti]; exact hx v) hB
    (by simpa only [hnorm] using hT) (by simpa only [hpair] using hP)
    (hD.congr (hdist.mono fun x hx ↦ hx.symm))
  simp only [hnorm, hpair] at h
  rwa [integral_congr_ae hdist] at h

include hkl hb in
/-- **Absorption of a small multiple of the mass, for the wedge pairing.** Under the hypotheses of
`TauCeti.AlmostComplexStructure.mul_integral_norm_le_integral_wedge_add_mul_integral_infDist`,
with `0 ≤ B`, suppose the cone defect is at most `ε` plus a small multiple `δ` of the total norm,
`∫ dist(ξ_T, positiveCone) ≤ ε + δ ∫ ‖ξ_T‖`, where `(B + c₀) δ < c₀`. Then

`∫ ‖ξ_T‖ ≤ (∫ (T ∧ Ω)(b) + (B + c₀) ε) / (c₀ - (B + c₀) δ)`. -/
theorem integral_norm_le_integral_wedge_add_mul_div_of_integral_infDist_le
    (hJ : ∀ᵐ x ∂μ, ∃ e : OrthonormalBasis (Fin 4) ℝ V,
      J x (e 0) = e 1 ∧ J x (e 2) = e 3 ∧ e.toBasis.orientation = o)
    (hc₀ : 0 ≤ c₀) (hΩ : ∀ᵐ x ∂μ, ∀ v, c₀ * ‖v‖ ^ 2 ≤ Ω x ![v, J x v]) (hB₀ : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖(alternatingFormEquiv V 2).symm (Ω x)‖ ≤ B)
    (hT : Integrable (fun x ↦ ‖(alternatingFormEquiv V 2).symm (T x)‖) μ)
    (hP : Integrable (fun x ↦ (T x).wedge (Ω x) b) μ)
    (hD : Integrable (fun x ↦ infDist ((alternatingFormEquiv V 2).symm (T x))
      ((J x).positiveCone : Set (⋀[ℝ]^2 V))) μ) {ε δ : ℝ}
    (hDle : ∫ x, infDist ((alternatingFormEquiv V 2).symm (T x))
        ((J x).positiveCone : Set (⋀[ℝ]^2 V)) ∂μ ≤
      ε + δ * ∫ x, ‖(alternatingFormEquiv V 2).symm (T x)‖ ∂μ)
    (hδ : (B + c₀) * δ < c₀) :
    ∫ x, ‖(alternatingFormEquiv V 2).symm (T x)‖ ∂μ ≤
      (∫ x, (T x).wedge (Ω x) b ∂μ + (B + c₀) * ε) / (c₀ - (B + c₀) * δ) := by
  have h := mul_integral_norm_le_integral_wedge_add_mul_integral_infDist hkl hb hJ hc₀ hΩ hB hT
    hP hD
  have h' := mul_le_mul_of_nonneg_left hDle (add_nonneg hB₀ hc₀)
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end Form

end TauCeti.AlmostComplexStructure
