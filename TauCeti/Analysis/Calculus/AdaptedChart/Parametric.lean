/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.AdaptedChart

/-!
# Adapted charts depending on a parameter

Let `γ : V → W` parametrize a submanifold of a normed space `W` and let `J (z, ·)` be a field of
endomorphisms of `W` depending on a parameter `z ∈ P`, with `J (z, ·)² = -1` along `γ`. The
parametric adapted extension
`Φ ((z, x), y) = (z, γ x + J (z, γ x) (Dγ x y))`
is the adapted normal extension of `TauCeti.adaptedNormalExtension` for `J (z, ·)`, carried
along with the parameter. It is itself a normal extension, of the parametrization
`(z, x) ↦ (z, γ x)` of `P × γ (V)` by the frame `y ↦ (0, J (z, γ x) (Dγ x y))`. When `J` is `C^ℓ`
jointly in `(z, w)` and the image of `Dγ x₀` is maximal totally real for `J (z₀, γ x₀)`, the
inverse function theorem inverts `Φ` near `((z₀, x₀), 0)` with a `C^ℓ` inverse, jointly in the
parameter (`TauCeti.exists_parametricAdaptedChart`). This is McDuff–Salamon Exercise B.4.10
with parameters: a family of adapted charts `ψ_z` depending `C^ℓ` on `z`, each adapted to
`J (z, ·)`.

The chart preserves the parameter, in both directions
(`OpenPartialHomeomorph.fst_fst_symm_of_coe_eq_parametricAdaptedNormalExtension`). Flattening is
`OpenPartialHomeomorph.isImage_of_coe_eq_normalExtension` for the normal extension above. The
structure is carried along by the endomorphism field `(z, w) ↦ id × J (z, w)`
(`ContinuousLinearMap.prodMap`), acting as the identity on the parameter and as `J (z, w)` on
`W`; pulled back by the chart, it is the identity on the parameter and the standard structure
`(v, w) ↦ (-w, v)` on `V × V`, along the zero section
(`OpenPartialHomeomorph.pullbackEnd_prodMap_of_coe_eq_parametricAdaptedNormalExtension`), and it
is `C^(ℓ-1)` by `OpenPartialHomeomorph.contDiffOn_pullbackEnd`.

## Main declarations

* `TauCeti.parametricAdaptedNormalExtension`: the adapted extension carried along a parameter.
* `TauCeti.exists_parametricAdaptedChart`: the inverse function theorem for it.
* `TauCeti.parametricAdaptedNormalExtension_inl`: in the flat model with the standard structure
  it is the identity, up to the grouping of the coordinates.
* `OpenPartialHomeomorph.pullbackEnd_prodMap_of_coe_eq_parametricAdaptedNormalExtension`:
  along the zero section the pulled-back structure is standard.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace TauCeti

section Extension

variable {𝕜 P V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The adapted normal extension carried along a parameter:
`((z, x), y) ↦ (z, γ x + J (z, γ x) (Dγ x y))`. It is the normal extension of the parametrization
`(z, x) ↦ (z, γ x)` by the frame `y ↦ (0, J (z, γ x) (Dγ x y))`. -/
def parametricAdaptedNormalExtension (γ : V → W) (J : P × W → W →L[𝕜] W) :
    (P × V) × V → P × W :=
  normalExtension (Prod.map id γ)
    (fun q ↦ (ContinuousLinearMap.inr 𝕜 P W).comp ((J (Prod.map id γ q)).comp (fderiv 𝕜 γ q.2)))

/-- Express the parametric adapted extension as a normal extension. -/
theorem parametricAdaptedNormalExtension_eq_normalExtension (γ : V → W)
    (J : P × W → W →L[𝕜] W) :
    parametricAdaptedNormalExtension γ J = normalExtension (Prod.map id γ)
      (fun q ↦ (ContinuousLinearMap.inr 𝕜 P W).comp
        ((J (Prod.map id γ q)).comp (fderiv 𝕜 γ q.2))) := by
  rw [parametricAdaptedNormalExtension]

/-- The parametric adapted extension is the adapted extension for `J (z, ·)` in the second
component, and keeps the parameter in the first. -/
@[simp]
theorem parametricAdaptedNormalExtension_apply (γ : V → W) (J : P × W → W →L[𝕜] W)
    (p : (P × V) × V) :
    parametricAdaptedNormalExtension γ J p =
      (p.1.1, adaptedNormalExtension γ (fun w ↦ J (p.1.1, w)) (p.1.2, p.2)) := by
  obtain ⟨⟨z, x⟩, y⟩ := p
  simp [parametricAdaptedNormalExtension_eq_normalExtension, normalExtension_apply,
    adaptedNormalExtension_apply]

/-- In the flat model `V ⊆ V × V` with the standard structure at every parameter, the parametric
adapted extension forgets nothing: it is `((z, x), y) ↦ (z, (x, y))`. -/
@[simp]
theorem parametricAdaptedNormalExtension_inl :
    parametricAdaptedNormalExtension (ContinuousLinearMap.inl 𝕜 V V)
      (fun _ : P × (V × V) ↦ (-ContinuousLinearMap.snd 𝕜 V V).prod
        (ContinuousLinearMap.fst 𝕜 V V)) = fun p ↦ (p.1.1, (p.1.2, p.2)) := by
  funext p
  rw [parametricAdaptedNormalExtension_apply, adaptedNormalExtension_inl, id]

end Extension

section Chart

variable {𝕜 P V W : Type*} [RCLike 𝕜] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {γ : V → W} {J : P × W → W →L[𝕜] W}

/-- **Parametric adapted charts exist.** Let `γ` be `C^(ℓ+1)` on an open `U` and `J` be `C^ℓ`
jointly in `(z, w)` on an open `Ω ⊆ P × W` containing `(z, γ x)` for `z` in an open `Z` and
`x ∈ U`, with `1 ≤ ℓ`. If at `x₀ ∈ U` the tangent map `Dγ x₀` is injective with image maximal
totally real for `J (z₀, γ x₀)`, `z₀ ∈ Z`, and `J (z₀, γ x₀)² = -1`, then the parametric adapted
extension restricts to a partial homeomorphism around `((z₀, x₀), 0)` with source in
`(Z × U) × V`, target in `Ω`, and which is `C^ℓ` with `C^ℓ` inverse. -/
theorem exists_parametricAdaptedChart [CompleteSpace P] [CompleteSpace V] [CompleteSpace W]
    {Z : Set P} {U : Set V} {Ω : Set (P × W)} {z₀ : P} {x₀ : V} {ℓ : ℕ∞ω} (hZ : IsOpen Z)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Z) (hx₀ : x₀ ∈ U) (hℓ : 1 ≤ ℓ)
    (hγ : ContDiffOn 𝕜 (ℓ + 1) γ U) (hJ : ContDiffOn 𝕜 ℓ J Ω)
    (hγΩ : ∀ z ∈ Z, ∀ x ∈ U, (z, γ x) ∈ Ω)
    (hsq : ∀ v, J (z₀, γ x₀) (J (z₀, γ x₀) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x₀))
    (htr : IsMaximalTotallyReal (J (z₀, γ x₀)).toLinearMap (fderiv 𝕜 γ x₀).range) :
    ∃ e : OpenPartialHomeomorph ((P × V) × V) (P × W),
      ⇑e = parametricAdaptedNormalExtension γ J ∧ ((z₀, x₀), 0) ∈ e.source ∧
      e.source ⊆ (Z ×ˢ U) ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn 𝕜 ℓ e e.source ∧ ContDiffOn 𝕜 ℓ e.symm e.target := by
  have hγℓ : ContDiffOn 𝕜 ℓ γ U := hγ.of_le le_self_add
  have hγ₁ : ContDiffAt 𝕜 1 γ x₀ := (hγℓ.contDiffAt (hU.mem_nhds hx₀)).of_le hℓ
  have hJc : ContinuousAt (fun w ↦ J (z₀, w)) (γ x₀) :=
    (hJ.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ z₀ hz₀ x₀ hx₀))).comp
      (Continuous.prodMk_right z₀).continuousAt
  -- The frame of the adapted extension for `J (z₀, ·)` at `(x₀, 0)` is invertible.
  obtain ⟨D, hD⟩ := (isInvertible_fderiv_adaptedNormalExtension_zero_iff hγ₁ hJc hsq hinj).2 htr
  rw [fderiv_adaptedNormalExtension_zero hγ₁ hJc] at hD
  have hZU : MapsTo Prod.snd (Z ×ˢ U) U := fun q hq ↦ hq.2
  have hγ' : ContDiffOn 𝕜 ℓ (Prod.map id γ) (Z ×ˢ U) :=
    contDiffOn_id.prodMap hγℓ
  have hmaps : MapsTo (Prod.map id γ) (Z ×ˢ U) Ω := fun q hq ↦ hγΩ _ hq.1 _ hq.2
  have hA : ContDiffOn 𝕜 ℓ
      (fun q : P × V ↦ (ContinuousLinearMap.inr 𝕜 P W).comp
        ((J (Prod.map id γ q)).comp (fderiv 𝕜 γ q.2))) (Z ×ˢ U) :=
    contDiffOn_const.clm_comp ((hJ.comp hγ' hmaps).clm_comp
      ((hγ.fderiv_of_isOpen hU le_rfl).comp contDiffOn_snd hZU))
  -- The frame of the parametric extension is the identity on `P` times that frame.
  have hframe : ((fderiv 𝕜 (Prod.map id γ) (z₀, x₀)).coprod
      ((ContinuousLinearMap.inr 𝕜 P W).comp
        ((J (z₀, γ x₀)).comp (fderiv 𝕜 γ x₀)))).IsInvertible := by
    have hd := (hasFDerivAt_id (𝕜 := 𝕜) z₀).prodMap (z₀, x₀)
      (hγ₁.differentiableAt one_ne_zero).hasFDerivAt
    refine ⟨(ContinuousLinearEquiv.prodAssoc 𝕜 P V V).trans
      ((ContinuousLinearEquiv.refl 𝕜 P).prodCongr D), ?_⟩
    rw [hd.fderiv]
    refine ContinuousLinearMap.ext fun p ↦ Prod.ext ?_ ?_
    · simp
    · have h := DFunLike.congr_fun hD (p.1.2, p.2)
      simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply] at h
      simp [← h]
  obtain ⟨e, he, h₀, hsU, htΩ, hc, hcs⟩ :=
    exists_normalExtensionChart (hZ.prod hU) hΩ ⟨hz₀, hx₀⟩ hℓ hγ' hA hmaps hframe
  exact ⟨e, he.trans (parametricAdaptedNormalExtension_eq_normalExtension γ J).symm, h₀, hsU,
    htΩ, hc, hcs⟩

end Chart

end TauCeti

namespace OpenPartialHomeomorph

variable {𝕜 P V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {γ : V → W} {J : P × W → W →L[𝕜] W} {e : OpenPartialHomeomorph ((P × V) × V) (P × W)}

/-- **The parametric chart preserves the parameter.** -/
theorem fst_fst_symm_of_coe_eq_parametricAdaptedNormalExtension
    (he : ⇑e = TauCeti.parametricAdaptedNormalExtension γ J) {q : P × W} (hq : q ∈ e.target) :
    (e.symm q).1.1 = q.1 := by
  have h := congrArg Prod.fst (e.right_inv hq)
  rwa [he, TauCeti.parametricAdaptedNormalExtension_apply] at h

/-- **The pulled-back structure is standard on the zero section.** At a point `((z, x), 0)` of
the source of a parametric adapted chart where `J (z, ·)² = -1` at `γ x`, the field
`(z, w) ↦ id × J (z, w)`, acting as the identity on the parameter and as `J (z, w)` on `W`, pulled
back by the chart is the identity on the parameter and the standard structure `(v, w) ↦ (-w, v)`
on `V × V`. -/
theorem pullbackEnd_prodMap_of_coe_eq_parametricAdaptedNormalExtension
    (he : ⇑e = TauCeti.parametricAdaptedNormalExtension γ J) {z : P} {x : V}
    (hx : ((z, x), 0) ∈ e.source) (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (z, γ x))
    (hsq : ∀ v, J (z, γ x) (J (z, γ x) v) = -v) (hs : DifferentiableAt 𝕜 e.symm (z, γ x))
    (p : (P × V) × V) :
    e.pullbackEnd (fun q ↦ (ContinuousLinearMap.id 𝕜 P).prodMap (J q)) ((z, x), 0) p =
      ((p.1.1, -p.2), p.1.2) := by
  set S : (P × V) × V →L[𝕜] (P × V) × V :=
    (((ContinuousLinearMap.fst 𝕜 P V).comp (ContinuousLinearMap.fst 𝕜 (P × V) V)).prod
      (-ContinuousLinearMap.snd 𝕜 (P × V) V)).prod
      ((ContinuousLinearMap.snd 𝕜 P V).comp (ContinuousLinearMap.fst 𝕜 (P × V) V)) with hS
  have hd := (hasFDerivAt_id (𝕜 := 𝕜) z).prodMap (z, x)
    (hγ.differentiableAt one_ne_zero).hasFDerivAt
  have hA : ContinuousAt (fun q : P × V ↦ (ContinuousLinearMap.inr 𝕜 P W).comp
      ((J (Prod.map id γ q)).comp (fderiv 𝕜 γ q.2))) (z, x) :=
    continuousAt_const.clm_comp ((ContinuousAt.comp (f := Prod.map id γ) hJ
      (continuousAt_id.prodMap hγ.continuousAt)).clm_comp
      ((hγ.continuousAt_fderiv one_ne_zero).comp continuousAt_snd))
  have h := e.pullbackEnd_of_coe_eq_normalExtension
    (J := fun q ↦ (ContinuousLinearMap.id 𝕜 P).prodMap (J q)) (S := S)
    (he.trans (TauCeti.parametricAdaptedNormalExtension_eq_normalExtension γ J)) hx hd hA
    (fun q ↦ ?_) hs
  · rw [h, hS]
    simp
  · ext
    · simp [hS]
    · simp only [hS, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.comp_apply, Prod.snd_add, ContinuousLinearMap.coe_prodMap',
        Prod.map_apply, id_eq, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        neg_apply, map_add, map_neg, hsq]
      abel

end OpenPartialHomeomorph
