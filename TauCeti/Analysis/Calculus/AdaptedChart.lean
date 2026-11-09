/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Analysis.Calculus.NormalExtension
public import TauCeti.LinearAlgebra.TotallyReal.Frame

/-!
# Charts adapted to a totally real parametrization

Let `γ : V → W` parametrize a submanifold of a normed space `W` and let `J` be a field of
endomorphisms of `W` with `J² = -1` along `γ`. The adapted normal extension
`Φ (x, y) = γ x + J (γ x) (Dγ x y)` of `TauCeti.adaptedNormalExtension` has derivative
`(v, w) ↦ Dγ x v + J (γ x) (Dγ x w)` along the zero section. Over `ℝ` or `ℂ`, this file shows
that this derivative is invertible exactly when `Dγ x` is injective with maximal totally real
image, and inverts `Φ` near such a point. The inverse `ψ = Φ⁻¹` is the chart of McDuff–Salamon
Exercise B.4.10 in the model case `M = W`, `L = γ (V)`.

The chart is packaged as an `OpenPartialHomeomorph (V × V) W` whose underlying map is `Φ`; the
coordinates on `V × V` are the model coordinates, with the zero section `V × {0}` playing the
role of `ℝⁿ ⊆ ℂⁿ` and `(v, w) ↦ (-w, v)` the role of multiplication by `i`. Every property
below the existence statements is stated for an arbitrary such partial homeomorphism, so a
consumer may shrink the chart freely, and over an arbitrary nontrivially normed field.

* Flattening: the chart sends the zero section of its source onto the parametrized
  submanifold, and nothing else in its source onto it. When `γ` induces the topology of the open
  parameter set `U`, as an embedding does, the chart can be shrunk so that the zero section of
  its source goes onto all of `γ (U)` inside its target: `ψ (γ (U)) = ψ (target) ∩ (V × {0})`.
* Intertwining: along the submanifold, the derivative of `ψ` turns `J` into the standard
  structure.
* Pushforward: the field `e.pullbackEnd J p = Dψ (e p) ∘ J (e p) ∘ De p`, the structure
  `ψ_* J` in model coordinates, is `C^n` whenever the chart is `C^(n+1)` and `J` is `C^n`
  (`OpenPartialHomeomorph.contDiffOn_pullbackEnd`); so for a `C^ℓ` structure and a
  `C^(ℓ+1)` parametrization it is `C^(ℓ-1)`. It equals the standard structure on the zero
  section.

## Main declarations

* `TauCeti.isInvertible_fderiv_adaptedNormalExtension_zero_iff`: the derivative of the adapted
  extension on the zero section is invertible exactly for maximal totally real tangent spaces.
* `TauCeti.exists_adaptedChart`: the inverse function theorem for the adapted extension, with a
  `C^ℓ` inverse on the whole target.
* `TauCeti.exists_adaptedChart_of_isInducing`: for an embedded submanifold, an adapted chart
  that flattens all of `γ (U)` inside its target.
* `OpenPartialHomeomorph.isImage_of_coe_eq_adaptedNormalExtension`,
  `OpenPartialHomeomorph.isImage_image_of_coe_eq_adaptedNormalExtension`: flattening.
* `OpenPartialHomeomorph.fderiv_symm_apply_of_coe_eq_adaptedNormalExtension`: intertwining.
* `OpenPartialHomeomorph.pullbackEnd_of_coe_eq_adaptedNormalExtension`: the pushed-forward
  structure is standard on the zero section.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace TauCeti

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] {γ : V → W} {J : W → W →L[𝕜] W}

/-- **The derivative of the adapted extension on the zero section is invertible exactly at
maximal totally real points.** For an injective tangent map `Dγ x` and `J² = -1` at `γ x`,
the derivative of the adapted extension at `(x, 0)` is invertible if and only if the image of
`Dγ x` is maximal totally real for `J (γ x)`. -/
theorem isInvertible_fderiv_adaptedNormalExtension_zero_iff [CompleteSpace V] [CompleteSpace W]
    {x : V} (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x)) :
    (fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0)).IsInvertible ↔
      IsMaximalTotallyReal (J (γ x)).toLinearMap (fderiv 𝕜 γ x).range := by
  have hJinj : Function.Injective (J (γ x)) := fun a b h ↦ by
    simpa [hsq] using congrArg (J (γ x)) h
  set D := (fderiv 𝕜 γ x).coprod ((J (γ x)).comp (fderiv 𝕜 γ x))
  -- The continuous and the algebraic doubled frames have the same underlying function.
  have hD : ⇑((fderiv 𝕜 γ x).toLinearMap.coprod ((J (γ x)).toLinearMap.comp
      (fderiv 𝕜 γ x).toLinearMap)) = ⇑D := by
    funext p
    simp [D, ContinuousLinearMap.coprod_apply]
  rw [← bijective_coprod_iff_isMaximalTotallyReal_range hinj (hJinj.comp hinj), hD,
    fderiv_adaptedNormalExtension_zero hγ hJ]
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
    (hγ : ContDiffOn 𝕜 (ℓ + 1) γ U) (hJ : ContDiffOn 𝕜 ℓ J Ω) (hγΩ : MapsTo γ U Ω)
    (hsq : ∀ v, J (γ x₀) (J (γ x₀) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x₀))
    (htr : IsMaximalTotallyReal (J (γ x₀)).toLinearMap (fderiv 𝕜 γ x₀).range) :
    ∃ e : OpenPartialHomeomorph (V × V) W, ⇑e = adaptedNormalExtension γ J ∧
      (x₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn 𝕜 ℓ e e.source ∧ ContDiffOn 𝕜 ℓ e.symm e.target := by
  have hΦ : ContDiffOn 𝕜 ℓ (adaptedNormalExtension γ J) (U ×ˢ univ) :=
    contDiffOn_adaptedNormalExtension hU hγ hJ hγΩ
  have hs : IsOpen ((U ×ˢ univ) ∩ adaptedNormalExtension γ J ⁻¹' Ω) :=
    hΦ.continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ) hΩ
  have hmem : (x₀, (0 : V)) ∈ (U ×ˢ univ) ∩ adaptedNormalExtension γ J ⁻¹' Ω :=
    ⟨⟨hx₀, mem_univ _⟩, by simpa only [mem_preimage, adaptedNormalExtension_zero] using hγΩ hx₀⟩
  have hγ₁ : ContDiffAt 𝕜 1 γ x₀ :=
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

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] {γ : V → W} {J : W → W →L[𝕜] W}
  {e : OpenPartialHomeomorph (V × V) W}

/-- An adapted chart inverts the parametrization on the zero section of its source. -/
theorem symm_apply_of_coe_eq_adaptedNormalExtension (he : ⇑e = TauCeti.adaptedNormalExtension γ J)
    {x : V} (hx : (x, 0) ∈ e.source) : e.symm (γ x) = (x, 0) := by
  rw [← TauCeti.adaptedNormalExtension_zero γ J x, ← he, e.left_inv hx]

/-- An adapted chart sends the zero section of its source into its target along `γ`. -/
theorem mem_target_of_coe_eq_adaptedNormalExtension
    (he : ⇑e = TauCeti.adaptedNormalExtension γ J) {x : V} (hx : (x, 0) ∈ e.source) :
    γ x ∈ e.target := by
  rw [← TauCeti.adaptedNormalExtension_zero γ J x, ← he]
  exact e.map_source hx

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
    · rw [mem_ofPred_eq, ← hp']
      exact hp
    · rw [hp', he, TauCeti.adaptedNormalExtension_zero]

/-- **Flattening of the whole parametrized piece.** If the source of an adapted chart lies over
`U` and every point `γ x` of its target with `x ∈ U` comes from the zero section of its source,
then a point of the source is sent into `γ (U)` exactly when it lies on the zero section. -/
theorem isImage_image_of_coe_eq_adaptedNormalExtension
    (he : ⇑e = TauCeti.adaptedNormalExtension γ J) {U : Set V} (hsU : e.source ⊆ U ×ˢ univ)
    (hU : ∀ x ∈ U, γ x ∈ e.target → (x, 0) ∈ e.source) :
    e.IsImage {p | p.2 = 0} (γ '' U) := by
  intro p hp
  constructor
  · rintro ⟨x, hx, hxp⟩
    have hxt : γ x ∈ e.target := by
      rw [hxp]
      exact e.map_source hp
    have h : e (x, 0) = e p := by rw [he, TauCeti.adaptedNormalExtension_zero, hxp, he]
    exact (congrArg Prod.snd (e.injOn (hU x hx hxt) hp h)).symm
  · intro h0
    have hp' : p = (p.1, 0) := Prod.ext rfl h0
    refine ⟨p.1, (hsU hp).1, ?_⟩
    rw [hp', he, TauCeti.adaptedNormalExtension_zero]

/-- **Intertwining.** Along the parametrized submanifold, the derivative of an adapted chart
turns `J` into the standard structure `(v, w) ↦ (-w, v)`, provided `J² = -1` there. -/
theorem fderiv_symm_apply_of_coe_eq_adaptedNormalExtension
    (he : ⇑e = TauCeti.adaptedNormalExtension γ J) {x : V} (hx : (x, 0) ∈ e.source)
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hs : DifferentiableAt 𝕜 e.symm (γ x)) (w : W) :
    fderiv 𝕜 e.symm (γ x) (J (γ x) w) =
      (-(fderiv 𝕜 e.symm (γ x) w).2, (fderiv 𝕜 e.symm (γ x) w).1) := by
  have hsymm := e.symm_apply_of_coe_eq_adaptedNormalExtension he hx
  have hγt := e.mem_target_of_coe_eq_adaptedNormalExtension he hx
  have hD := TauCeti.hasFDerivAt_adaptedNormalExtension_zero hγ hJ
  rw [← he] at hD
  have hd : DifferentiableAt 𝕜 e (e.symm (γ x)) := by rw [hsymm]; exact hD.differentiableAt
  have hright := e.fderiv_apply_fderiv_symm_apply hγt hd hs w
  have hleft := e.fderiv_symm_apply_fderiv_apply hγt hd hs
  rw [hsymm] at hright hleft
  have hint := TauCeti.fderiv_adaptedNormalExtension_intertwines hγ hJ hsq
    (fderiv 𝕜 e.symm (γ x) w).1 (fderiv 𝕜 e.symm (γ x) w).2
  rw [← he, Prod.mk.eta, hright] at hint
  rw [← hint, hleft]

/-- **The pushed-forward structure is standard on the zero section.** At a point `(x, 0)` of
the source of an adapted chart where `J² = -1`, the pulled-back structure is
`(v, w) ↦ (-w, v)`. -/
theorem pullbackEnd_of_coe_eq_adaptedNormalExtension
    (he : ⇑e = TauCeti.adaptedNormalExtension γ J) {x : V} (hx : (x, 0) ∈ e.source)
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hs : DifferentiableAt 𝕜 e.symm (γ x)) :
    e.pullbackEnd J (x, 0) =
      (-ContinuousLinearMap.snd 𝕜 V V).prod (ContinuousLinearMap.fst 𝕜 V V) := by
  have hsymm := e.symm_apply_of_coe_eq_adaptedNormalExtension he hx
  have hγt := e.mem_target_of_coe_eq_adaptedNormalExtension he hx
  have hD := TauCeti.hasFDerivAt_adaptedNormalExtension_zero hγ hJ
  rw [← he] at hD
  have hd : DifferentiableAt 𝕜 e (e.symm (γ x)) := by rw [hsymm]; exact hD.differentiableAt
  have hleft := e.fderiv_symm_apply_fderiv_apply hγt hd hs
  rw [hsymm] at hleft
  have hex : e (x, 0) = γ x := by rw [he, TauCeti.adaptedNormalExtension_zero]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [pullbackEnd_apply, hex,
    e.fderiv_symm_apply_of_coe_eq_adaptedNormalExtension he hx hγ hJ hsq hs, hleft]
  simp

end OpenPartialHomeomorph

namespace TauCeti

section Embedded

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] {γ : V → W} {J : W → W →L[𝕜] W}

/-- **Adapted charts along an embedded totally real submanifold.** If moreover `γ` induces the
topology of `U`, as an embedding restricted to `U` does, the chart of `TauCeti.exists_adaptedChart`
can be chosen so that its zero section goes onto all of `γ (U)` inside its target: a point of
its source is sent into `γ (U)` exactly when it lies on the zero section. -/
theorem exists_adaptedChart_of_isInducing [CompleteSpace V] [CompleteSpace W] {U : Set V}
    {Ω : Set W} {x₀ : V} {ℓ : ℕ∞ω} (hU : IsOpen U) (hΩ : IsOpen Ω) (hx₀ : x₀ ∈ U) (hℓ : 1 ≤ ℓ)
    (hγ : ContDiffOn 𝕜 (ℓ + 1) γ U) (hJ : ContDiffOn 𝕜 ℓ J Ω) (hγΩ : MapsTo γ U Ω)
    (hsq : ∀ v, J (γ x₀) (J (γ x₀) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x₀))
    (htr : IsMaximalTotallyReal (J (γ x₀)).toLinearMap (fderiv 𝕜 γ x₀).range)
    (hind : Topology.IsInducing fun x : U ↦ γ x) :
    ∃ e : OpenPartialHomeomorph (V × V) W, ⇑e = adaptedNormalExtension γ J ∧
      (x₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn 𝕜 ℓ e e.source ∧ ContDiffOn 𝕜 ℓ e.symm e.target ∧
      e.IsImage {p | p.2 = 0} (γ '' U) := by
  obtain ⟨e, he, h₀, hsU, htΩ, hc, hcs⟩ :=
    exists_adaptedChart hU hΩ hx₀ hℓ hγ hJ hγΩ hsq hinj htr
  have hγe (x : V) : e (x, 0) = γ x := by rw [he, adaptedNormalExtension_zero]
  -- The parameters in `U` whose zero-section point lies in the source are cut out by an open `O`.
  obtain ⟨O, hO, hOS⟩ := hind.isOpen_iff.mp
    (e.open_source.preimage (by fun_prop : Continuous fun y : U ↦ ((y : V), (0 : V))))
  have hmem (x : V) (hx : x ∈ U) : γ x ∈ O ↔ (x, 0) ∈ e.source :=
    Set.ext_iff.mp hOS ⟨x, hx⟩
  -- Shrinking the source to `e ⁻¹' O` removes the points of `γ (U)` not reached from the zero
  -- section.
  let e' := e.restrOpen (e.source ∩ e ⁻¹' O) (e.isOpen_inter_preimage hO)
  have hsrc : e'.source ⊆ e.source := fun p hp ↦ hp.1
  have htgt : e'.target ⊆ e.target := fun a ha ↦ ha.1
  have hsrc' (x : V) (hx : x ∈ U) (hxe : (x, 0) ∈ e.source) : (x, 0) ∈ e'.source := by
    refine ⟨hxe, hxe, ?_⟩
    rw [mem_preimage, hγe]
    exact (hmem x hx).mpr hxe
  have he' : ⇑e' = adaptedNormalExtension γ J := he
  refine ⟨e', he', hsrc' x₀ hx₀ h₀, hsrc.trans hsU, htgt.trans htΩ, hc.mono hsrc,
    hcs.mono htgt, e'.isImage_image_of_coe_eq_adaptedNormalExtension he' (hsrc.trans hsU)
    fun x hx ha ↦ ?_⟩
  have hO : γ x ∈ O := by
    have h := ha.2.2
    rwa [mem_preimage, e.right_inv ha.1] at h
  exact hsrc' x hx ((hmem x hx).mp hO)

end Embedded

/-! ### Examples: the flat case and the complex line -/

/-- **No loss of regularity in the flat case.** For the real locus `V × {0}` of `V × V` with
the standard structure, every adapted chart is the identity and pulls the standard structure
back to itself on its whole source. -/
theorem pullbackEnd_of_coe_eq_adaptedNormalExtension_inl {𝕜 V : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {e : OpenPartialHomeomorph (V × V) (V × V)}
    (he : ⇑e = adaptedNormalExtension (ContinuousLinearMap.inl 𝕜 V V)
      (fun _ ↦ (-ContinuousLinearMap.snd 𝕜 V V).prod (ContinuousLinearMap.fst 𝕜 V V)))
    {p : V × V} (hp : p ∈ e.source) :
    e.pullbackEnd (fun _ ↦ (-ContinuousLinearMap.snd 𝕜 V V).prod (ContinuousLinearMap.fst 𝕜 V V))
      p = (-ContinuousLinearMap.snd 𝕜 V V).prod (ContinuousLinearMap.fst 𝕜 V V) := by
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
