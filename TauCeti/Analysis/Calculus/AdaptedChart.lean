/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Calculus.FDeriv.Equiv
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Analysis.Calculus.NormalExtension
public import TauCeti.LinearAlgebra.TotallyReal.Frame

/-!
# Charts adapted to a totally real parametrization

Let `γ : V → W` parametrize a submanifold of a real normed space `W` and let `J` be a field of
endomorphisms of `W` with `J² = -1` along `γ`. The adapted normal extension
`Φ (x, y) = γ x + J (γ x) (Dγ x y)` of `TauCeti.adaptedNormalExtension` has derivative
`(v, w) ↦ Dγ x v + J (γ x) (Dγ x w)` along the zero section. This file shows that this
derivative is invertible exactly when `Dγ x` is injective with maximal totally real image, and
inverts `Φ` near such a point. The inverse `ψ = Φ⁻¹` is the chart of McDuff–Salamon
Exercise B.4.10 in the model case `M = W`, `L = γ (V)`.

The chart is packaged as an `OpenPartialHomeomorph (V × V) W` whose underlying map is `Φ`; the
coordinates on `V × V` are the model coordinates, with the zero section `V × {0}` playing the
role of `ℝⁿ ⊆ ℂⁿ` and `(v, w) ↦ (-w, v)` the role of multiplication by `i`. Every property
below is stated for an arbitrary such partial homeomorphism, so a consumer may shrink the chart
freely.

* Flattening: the chart sends the zero section of its source onto the parametrized
  submanifold, and nothing else in its source onto it.
* Intertwining: along the submanifold, the derivative of `ψ` turns `J` into the standard
  structure.
* Pushforward: the field `e.pullbackEnd J p = Dψ (e p) ∘ J (e p) ∘ De p`, the structure
  `ψ_* J` in model coordinates, is `C^n` whenever the chart is `C^(n+1)` and `J` is `C^n`;
  so for a `C^ℓ` structure and a `C^(ℓ+1)` parametrization it is `C^(ℓ-1)`. It equals the
  standard structure on the zero section.

## Main declarations

* `OpenPartialHomeomorph.pullbackEnd`: the pullback of an endomorphism field along a partial
  homeomorphism, as a field on its source.
* `OpenPartialHomeomorph.contDiffOn_pullbackEnd`: the pullback costs one derivative.
* `TauCeti.isInvertible_fderiv_adaptedNormalExtension_zero_iff`: the derivative of the adapted
  extension on the zero section is invertible exactly for maximal totally real tangent spaces.
* `TauCeti.exists_adaptedChart`: the inverse function theorem for the adapted extension, with a
  `C^ℓ` inverse on the whole target.
* `OpenPartialHomeomorph.isImage_of_coe_eq_adaptedNormalExtension`: flattening.
* `OpenPartialHomeomorph.fderiv_symm_apply_of_coe_eq_adaptedNormalExtension`: intertwining.
* `OpenPartialHomeomorph.pullbackEnd_of_coe_eq_adaptedNormalExtension`: the pushed-forward
  structure is standard on the zero section.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
* [The PseudoholomorphicCurveAnalysis roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/PseudoholomorphicCurveAnalysis/README.md),
  PH2.3.
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff

section PartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace OpenPartialHomeomorph

variable {e : OpenPartialHomeomorph E F}

/-- The pullback `(e^* J) p = (De_p)⁻¹ ∘ J (e p) ∘ De_p` of an endomorphism field along a
partial homeomorphism, as a field on its source. The inverse of `De_p` is written as the
derivative of `e.symm`, so no inversion of operators is involved. -/
def pullbackEnd (e : OpenPartialHomeomorph E F) (J : F → F →L[ℝ] F) (p : E) : E →L[ℝ] E :=
  (fderiv ℝ e.symm (e p)).comp ((J (e p)).comp (fderiv ℝ e p))

/-- Evaluate a pulled-back endomorphism field. -/
theorem pullbackEnd_apply (J : F → F →L[ℝ] F) (p v : E) :
    e.pullbackEnd J p v = fderiv ℝ e.symm (e p) (J (e p) (fderiv ℝ e p v)) := by
  simp only [pullbackEnd, ContinuousLinearMap.comp_apply]

/-- **Pulling back costs one derivative.** If a partial homeomorphism and its inverse are
`C^ℓ` and the field `J` is `C^n` on the target with `n + 1 ≤ ℓ`, the pulled-back field is
`C^n` on the source. -/
theorem contDiffOn_pullbackEnd {J : F → F →L[ℝ] F} {ℓ n : ℕ∞ω}
    (he : ContDiffOn ℝ ℓ e e.source) (hes : ContDiffOn ℝ ℓ e.symm e.target)
    (hJ : ContDiffOn ℝ n J e.target) (hn : n + 1 ≤ ℓ) :
    ContDiffOn ℝ n (e.pullbackEnd J) e.source := by
  have he' := he.of_le (le_self_add.trans hn)
  exact ((hes.fderiv_of_isOpen e.open_target hn).comp he' e.mapsTo).clm_comp
    ((hJ.comp he' e.mapsTo).clm_comp (he.fderiv_of_isOpen e.open_source hn))

/-- The derivative of `e` is complex linear from the pulled-back structure to `J`. -/
theorem fderiv_comp_pullbackEnd (J : F → F →L[ℝ] F) {p : E} (hp : p ∈ e.source)
    (he : DifferentiableAt ℝ e p) (hs : DifferentiableAt ℝ e.symm (e p)) :
    (fderiv ℝ e p).comp (e.pullbackEnd J p) = (J (e p)).comp (fderiv ℝ e p) := by
  have h := e.fderiv_comp_fderiv_symm (e.map_source hp)
    (by rwa [e.left_inv hp]) hs
  rw [e.left_inv hp] at h
  rw [pullbackEnd, ← ContinuousLinearMap.comp_assoc, h, ContinuousLinearMap.id_comp]

end OpenPartialHomeomorph

end PartialHomeomorph

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {γ : V → W} {J : W → W →L[ℝ] W}

/-- **The adapted extension is a local diffeomorphism exactly at maximal totally real points.**
For an injective tangent map `Dγ x` and `J² = -1` at `γ x`, the derivative of the adapted
extension at `(x, 0)` is invertible if and only if the image of `Dγ x` is maximal totally real
for `J (γ x)`. -/
theorem isInvertible_fderiv_adaptedNormalExtension_zero_iff [CompleteSpace V] [CompleteSpace W]
    {x : V} (hγ : ContDiffAt ℝ 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hinj : Function.Injective (fderiv ℝ γ x)) :
    (fderiv ℝ (adaptedNormalExtension γ J) (x, 0)).IsInvertible ↔
      IsMaximalTotallyReal (J (γ x)).toLinearMap (fderiv ℝ γ x).range := by
  have hJinj : Function.Injective (J (γ x)) := fun a b h ↦ by
    simpa [hsq] using congrArg (J (γ x)) h
  rw [← bijective_coprod_iff_isMaximalTotallyReal_range hinj (hJinj.comp hinj),
    fderiv_adaptedNormalExtension_zero hγ hJ]
  set D := (fderiv ℝ γ x).coprod ((J (γ x)).comp (fderiv ℝ γ x))
  change D.IsInvertible ↔ Function.Bijective D
  refine ⟨ContinuousLinearMap.IsInvertible.bijective, fun h ↦ ?_⟩
  exact ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr h.1)
    (LinearMap.range_eq_top.mpr h.2), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- **Adapted charts exist.** Let `γ` be `C^(ℓ+1)` on an open `U` and `J` be `C^ℓ` on an open `Ω`
containing `γ (U)`, with `1 ≤ ℓ`. If at `x₀ ∈ U` the tangent map `Dγ x₀` is injective with
image maximal totally real for `J (γ x₀)`, and `J (γ x₀)² = -1`, then the adapted extension
restricts to a partial homeomorphism around `(x₀, 0)` with source in `U × V`, target in `Ω`,
and which is `C^ℓ` with `C^ℓ` inverse. Its inverse is the adapted chart. -/
theorem exists_adaptedChart [CompleteSpace V] [CompleteSpace W] {U : Set V} {Ω : Set W}
    {x₀ : V} {ℓ : ℕ∞ω} (hU : IsOpen U) (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ U) (hℓ : 1 ≤ ℓ)
    (hγ : ContDiffOn ℝ (ℓ + 1) γ U) (hJ : ContDiffOn ℝ ℓ J Ω) (hγΩ : MapsTo γ U Ω)
    (hsq : ∀ v, J (γ x₀) (J (γ x₀) v) = -v) (hinj : Function.Injective (fderiv ℝ γ x₀))
    (htr : IsMaximalTotallyReal (J (γ x₀)).toLinearMap (fderiv ℝ γ x₀).range) :
    ∃ e : OpenPartialHomeomorph (V × V) W, ⇑e = adaptedNormalExtension γ J ∧
      (x₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn ℝ ℓ e e.source ∧ ContDiffOn ℝ ℓ e.symm e.target := by
  have hΦ : ContDiffOn ℝ ℓ (adaptedNormalExtension γ J) (U ×ˢ univ) :=
    contDiffOn_adaptedNormalExtension hU hγ hJ hγΩ
  have hs : IsOpen ((U ×ˢ univ) ∩ adaptedNormalExtension γ J ⁻¹' Ω) :=
    hΦ.continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ) hΩ
  have hmem : (x₀, (0 : V)) ∈ (U ×ˢ univ) ∩ adaptedNormalExtension γ J ⁻¹' Ω :=
    ⟨⟨hx₀, mem_univ _⟩, by simpa only [mem_preimage, adaptedNormalExtension_zero] using hγΩ hx₀⟩
  have hγ₁ : ContDiffAt ℝ 1 γ x₀ :=
    (hγ.contDiffAt (hU.mem_nhds hx₀)).of_le (hℓ.trans le_self_add)
  have hJc : ContinuousAt J (γ x₀) := hJ.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ hx₀))
  obtain ⟨E, hE⟩ := (isInvertible_fderiv_adaptedNormalExtension_zero_iff hγ₁ hJc hsq hinj).2 htr
  obtain ⟨e, he, hx, hsub, hsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph (hΦ.mono inter_subset_left) hs hmem hℓ hE
  refine ⟨e, he, hx, fun p hp ↦ (hsub hp).1, fun y hy ↦ ?_, ?_, hsymm⟩
  · rw [← e.right_inv hy, he]
    exact (hsub (e.map_target hy)).2
  · rw [he]
    exact hΦ.mono fun p hp ↦ (hsub hp).1

end TauCeti

namespace OpenPartialHomeomorph

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {γ : V → W} {J : W → W →L[ℝ] W}
  {e : OpenPartialHomeomorph (V × V) W}

/-- An adapted chart inverts the parametrization on the zero section of its source. -/
theorem symm_apply_of_coe_eq_adaptedNormalExtension (he : ⇑e = TauCeti.adaptedNormalExtension γ J)
    {x : V} (hx : (x, 0) ∈ e.source) : e.symm (γ x) = (x, 0) := by
  rw [← TauCeti.adaptedNormalExtension_zero γ J x, ← he, e.left_inv hx]

/-- **Flattening.** A point of the source of an adapted chart is sent into the parametrized
submanifold `γ {x | (x, 0) ∈ e.source}` exactly when it lies on the zero section. -/
theorem isImage_of_coe_eq_adaptedNormalExtension (he : ⇑e = TauCeti.adaptedNormalExtension γ J) :
    e.IsImage {p | p.2 = 0} (γ '' {x | (x, 0) ∈ e.source}) := by
  intro p hp
  constructor
  · rintro ⟨x, hx, hxp⟩
    have h : e (x, 0) = e p := by rw [he, TauCeti.adaptedNormalExtension_zero, hxp, he]
    exact (congrArg Prod.snd (e.injOn hx hp h)).symm
  · intro h0
    have hp' : p = (p.1, 0) := Prod.ext rfl h0
    refine ⟨p.1, ?_, ?_⟩
    · change (p.1, (0 : V)) ∈ e.source
      rwa [← hp']
    · rw [hp', he, TauCeti.adaptedNormalExtension_zero]

/-- **Intertwining.** Along the parametrized submanifold, the derivative of an adapted chart
turns `J` into the standard structure `(v, w) ↦ (-w, v)`, provided `J² = -1` there. -/
theorem fderiv_symm_apply_of_coe_eq_adaptedNormalExtension
    (he : ⇑e = TauCeti.adaptedNormalExtension γ J) {x : V} (hx : (x, 0) ∈ e.source)
    (hγ : ContDiffAt ℝ 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hs : DifferentiableAt ℝ e.symm (γ x)) (w : W) :
    fderiv ℝ e.symm (γ x) (J (γ x) w) =
      (-(fderiv ℝ e.symm (γ x) w).2, (fderiv ℝ e.symm (γ x) w).1) := by
  have hsymm := e.symm_apply_of_coe_eq_adaptedNormalExtension he hx
  have hD := TauCeti.hasFDerivAt_adaptedNormalExtension_zero hγ hJ
  rw [← he] at hD
  have hγt : γ x ∈ e.target := by
    rw [← TauCeti.adaptedNormalExtension_zero γ J x, ← he]
    exact e.map_source hx
  have hright := e.fderiv_comp_fderiv_symm hγt (by rw [hsymm]; exact hD.differentiableAt) hs
  have hleft := e.fderiv_symm_comp_fderiv hγt (by rw [hsymm]; exact hD.differentiableAt) hs
  rw [hsymm] at hright hleft
  set D := fderiv ℝ e (x, 0)
  set D' := fderiv ℝ e.symm (γ x)
  have hw : D (D' w) = w := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : W →L[ℝ] W ↦ L w) hright
  have hint := TauCeti.fderiv_adaptedNormalExtension_intertwines hγ hJ hsq (D' w).1 (D' w).2
  rw [← he] at hint
  change D (-(D' w).2, (D' w).1) = J (γ x) (D ((D' w).1, (D' w).2)) at hint
  calc D' (J (γ x) w) = D' (J (γ x) (D ((D' w).1, (D' w).2))) := by rw [Prod.mk.eta, hw]
    _ = D' (D (-(D' w).2, (D' w).1)) := by rw [hint]
    _ = (-(D' w).2, (D' w).1) := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun L : V × V →L[ℝ] V × V ↦ L (-(D' w).2, (D' w).1)) hleft

/-- **The pushed-forward structure is standard on the zero section.** At a point `(x, 0)` of
the source of an adapted chart where `J² = -1`, the pulled-back structure is
`(v, w) ↦ (-w, v)`. -/
theorem pullbackEnd_of_coe_eq_adaptedNormalExtension
    (he : ⇑e = TauCeti.adaptedNormalExtension γ J) {x : V} (hx : (x, 0) ∈ e.source)
    (hγ : ContDiffAt ℝ 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hs : DifferentiableAt ℝ e.symm (γ x)) :
    e.pullbackEnd J (x, 0) =
      (-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V) := by
  have hD := TauCeti.hasFDerivAt_adaptedNormalExtension_zero hγ hJ
  rw [← he] at hD
  have hex : e (x, 0) = γ x := by rw [he, TauCeti.adaptedNormalExtension_zero]
  have hγt : γ x ∈ e.target := hex ▸ e.map_source hx
  have hleft := e.fderiv_symm_comp_fderiv hγt
    (by rw [← hex, e.left_inv hx]; exact hD.differentiableAt) hs
  rw [← hex, e.left_inv hx, hex] at hleft
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : fderiv ℝ e.symm (γ x) (fderiv ℝ e (x, 0) v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : V × V →L[ℝ] V × V ↦ L v) hleft
  rw [pullbackEnd_apply, hex,
    e.fderiv_symm_apply_of_coe_eq_adaptedNormalExtension he hx hγ hJ hsq hs, hv]
  simp

end OpenPartialHomeomorph

namespace TauCeti

/-! ### Checks -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **No loss of regularity in the flat case.** For the real locus `V × {0}` of `V × V` with
the standard structure, every adapted chart is the identity and pulls the standard structure
back to itself on its whole source. -/
theorem pullbackEnd_of_coe_eq_adaptedNormalExtension_inl
    {e : OpenPartialHomeomorph (V × V) (V × V)}
    (he : ⇑e = adaptedNormalExtension (ContinuousLinearMap.inl ℝ V V)
      (fun _ ↦ (-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V)))
    {p : V × V} (hp : p ∈ e.source) :
    e.pullbackEnd (fun _ ↦ (-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V))
      p = (-ContinuousLinearMap.snd ℝ V V).prod (ContinuousLinearMap.fst ℝ V V) := by
  rw [adaptedNormalExtension_inl] at he
  have hep : e p = p := by rw [he, id]
  have hsymm : e.symm =ᶠ[𝓝 p] id := by
    filter_upwards [e.open_target.mem_nhds (hep ▸ e.map_source hp)] with y hy
    simpa [he] using e.right_inv hy
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [OpenPartialHomeomorph.pullbackEnd_apply, hep, hsymm.fderiv_eq, he, fderiv_id]
  simp

/-- **The totally real hypothesis is needed.** For the complex line `ℂ × {0}` in `ℂ²` with
multiplication by `i`, the adapted extension has non-invertible derivative everywhere on the
zero section: `(i, -1)` lies in its kernel. -/
theorem not_isInvertible_fderiv_adaptedNormalExtension_complexLine (x : ℂ) :
    ¬ (fderiv ℝ (adaptedNormalExtension (ContinuousLinearMap.inl ℝ ℂ ℂ)
      (fun _ ↦ Complex.I • ContinuousLinearMap.id ℝ (ℂ × ℂ))) (x, 0)).IsInvertible := by
  intro h
  rw [fderiv_adaptedNormalExtension_zero (ContinuousLinearMap.inl ℝ ℂ ℂ).contDiff.contDiffAt
    continuousAt_const, ContinuousLinearMap.fderiv] at h
  have h0 := h.bijective.1 (a₁ := (Complex.I, -1)) (a₂ := 0) (by ext <;> simp)
  simpa using congrArg Prod.snd h0

end TauCeti
