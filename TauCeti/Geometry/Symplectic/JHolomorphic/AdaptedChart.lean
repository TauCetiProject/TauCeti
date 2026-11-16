/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Analysis.Calculus.NormalExtension
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.LinearAlgebra.Complex.Module

/-!
# Coordinates adapted to a pseudoholomorphic disc

Let `J : V → (V →L[ℝ] V)` be an almost complex structure on a real normed space `V`, written in
coordinates, and let `u : ℂ → V` be a `J`-holomorphic disc: `∂ₛu + J(u) ∂ₜu = 0`. Near a point
`a₀` where `u` is an immersion, this file constructs coordinates `(a, w) ∈ ℂ × N`, with `N` a
complex normed space, in which `u` becomes the zero section `a ↦ (a, 0)` and `J` becomes the
standard complex structure `i` along it. These are the adapted coordinates in which
McDuff and Salamon compare two pseudoholomorphic discs through a common point (Lemmas 2.4.2 and
2.4.3).

The coordinates are the inverse of the map

`Φ (a, w) = u a + Θ_a w`,  `Θ_a w = ½ (W w - J(u a) W (i w))`

(`TauCeti.holomorphicNormalExtension`), where `W : N →L[ℝ] V` is a real-linear frame of normal
directions which is complex-linear at the base point, `J(u a₀) W = W i`, and spans a complement
of the tangent line of `u` there. The frame `Θ_a` (`TauCeti.holomorphicNormalFrame`) is the
complex-linear part of `W` for the structures `i` on `N` and `J(u a)` on `V`: wherever
`J(u a)² = -1` it satisfies `J(u a) Θ_a = Θ_a i`, and it equals `W` at `a₀`; the same
projection, applied to automorphisms of `V` rather than to normal frames, is
`TauCeti.standardFrame`. So `Φ` is affine in the normal variable, and its
derivative along the zero section, `(α, ω) ↦ du_a α + Θ_a ω`, intertwines `i` with `J(u a)`
as soon as `u` is `J`-holomorphic at `a`. Only `u` and `J ∘ u` enter `Φ`, not the derivative of
`u`, so for `u` and `J` of class `C^ℓ` the coordinates are of class `C^ℓ`.

* **Existence.** By the inverse function theorem `Φ` restricts to a `C^ℓ` partial homeomorphism
  around `(a₀, 0)` with `C^ℓ` inverse (`TauCeti.exists_holomorphicAdaptedChart`). Every further
  statement holds for an arbitrary such partial homeomorphism, so the chart may be shrunk freely.
* **Flattening.** The chart sends a point of its source into the disc exactly when the point
  lies on the zero section
  (`OpenPartialHomeomorph.isImage_of_coe_eq_holomorphicNormalExtension`).
* **The structure along the disc.** The structure read in the chart,
  `e.pullbackEnd J (a, w) = DΦ⁻¹ ∘ J(Φ (a, w)) ∘ DΦ`, is `i` on the zero section
  (`OpenPartialHomeomorph.pullbackEnd_of_coe_eq_holomorphicNormalExtension`).
* **Normal control.** For `u` and `J` of class `C²` the structure read in the chart is `C¹`, so it
  differs from `i` by at most a constant times the normal coordinate:
  `‖e.pullbackEnd J (a, w) - i‖ ≤ C ‖w‖` near `(a₀, 0)`
  (`TauCeti.exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le`). Consequently the normal
  component `b` of a pseudoholomorphic disc `(a, b)` written in these coordinates satisfies the
  differential inequality `‖∂ₛb + i ∂ₜb‖ ≤ C ‖b‖ ‖∂ₜ(a, b)‖`
  (`TauCeti.norm_snd_add_I_smul_snd_le` with `ε = C ‖b‖`), which is what makes the similarity
  principle apply to `b` in the proof of McDuff–Salamon Lemma 2.4.3.

In the integrable model, `V = ℂ × N` with the structure `i`, the disc `a ↦ (a, 0)` and the frame
`w ↦ (0, w)`, the map `Φ` is the identity (`TauCeti.holomorphicNormalExtension_inl_inr`).

## Main declarations

* `TauCeti.holomorphicNormalFrame`: the complex-linear normal frame `Θ_a`, the complex-linear
  part (`TauCeti.complexLinearPart`) of `W`.
* `TauCeti.holomorphicNormalExtension`: the map `Φ (a, w) = u a + Θ_a w`.
* `TauCeti.hasFDerivAt_holomorphicNormalExtension_zero` and
  `TauCeti.coprod_holomorphicNormalFrame_apply_I_smul`: the derivative along the zero section and
  its complex linearity.
* `TauCeti.exists_holomorphicAdaptedChart`: the adapted chart.
* `OpenPartialHomeomorph.pullbackEnd_of_coe_eq_holomorphicNormalExtension`: in the chart, the
  structure is standard along the disc.
* `TauCeti.exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le`: the normal Lipschitz control.
* `TauCeti.norm_snd_add_I_smul_snd_le`: the resulting Cauchy–Riemann inequality for the normal
  component.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section 2.4, Lemmas 2.4.2 and 2.4.3.
-/

public noncomputable section

open Set Filter Complex
open scoped Topology ContDiff

namespace TauCeti

variable {V N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup N]
  [NormedSpace ℂ N]

/-! ### The complex-linear normal frame -/

/-- The **complex-linear normal frame** along a disc `u`: the complex-linear part
`Θ_a = ½ (W - J(u a) ∘ W ∘ i)` of a real-linear frame `W : N →L[ℝ] V`, for the structure `i` on
`N` and `J(u a)` on `V` (`TauCeti.coe_holomorphicNormalFrame`). Where `J(u a)² = -1` it
intertwines `i` with `J(u a)` (`TauCeti.apply_holomorphicNormalFrame_apply`), and it equals `W`
where `W` already does (`TauCeti.holomorphicNormalFrame_eq_self`). -/
def holomorphicNormalFrame (J : V → V →L[ℝ] V) (u : ℂ → V) (W : N →L[ℝ] V) (a : ℂ) :
    N →L[ℝ] V :=
  (2 : ℝ)⁻¹ • (W - (J (u a)).comp (W.comp (I • ContinuousLinearMap.id ℝ N)))

variable {J : V → V →L[ℝ] V} {u : ℂ → V} {W : N →L[ℝ] V} {a : ℂ}

/-- `Θ_a w = ½ (W w - J(u a) (W (i w)))`. -/
theorem holomorphicNormalFrame_apply (J : V → V →L[ℝ] V) (u : ℂ → V) (W : N →L[ℝ] V) (a : ℂ)
    (w : N) :
    holomorphicNormalFrame J u W a w = (2 : ℝ)⁻¹ • (W w - J (u a) (W (I • w))) := by
  simp [holomorphicNormalFrame]

/-- As a linear map, the normal frame is the complex-linear part of `W` for the structures `i`
on `N` and `J(u a)` on `V`. -/
theorem coe_holomorphicNormalFrame (J : V → V →L[ℝ] V) (u : ℂ → V) (W : N →L[ℝ] V) (a : ℂ) :
    (holomorphicNormalFrame J u W a : N →ₗ[ℝ] V) =
      complexLinearPart ((I • ContinuousLinearMap.id ℝ N : N →L[ℝ] N) : N →ₗ[ℝ] N)
        (J (u a) : V →ₗ[ℝ] V) W :=
  LinearMap.ext fun w ↦ by simp [holomorphicNormalFrame_apply]

/-- **The normal frame is complex-linear.** Where `J(u a)² = -1`, the frame `Θ_a` intertwines
multiplication by `i` with `J(u a)`. -/
theorem apply_holomorphicNormalFrame_apply (hsq : ∀ v, J (u a) (J (u a) v) = -v) (w : N) :
    J (u a) (holomorphicNormalFrame J u W a w) = holomorphicNormalFrame J u W a (I • w) := by
  have h := (isComplexLinear_complexLinearPart
    (J := ((I • ContinuousLinearMap.id ℝ N : N →L[ℝ] N) : N →ₗ[ℝ] N)) (J' := (J (u a) : V →ₗ[ℝ] V))
    (LinearMap.ext fun w ↦ by simp [smul_smul]) (LinearMap.ext fun v ↦ by simp [hsq])
    (W : N →ₗ[ℝ] V)).apply w
  rw [← coe_holomorphicNormalFrame] at h
  simpa using h.symm

/-- Where `W` is already complex-linear for `i` and `J(u a)`, the normal frame is `W`. -/
theorem holomorphicNormalFrame_eq_self (hsq : ∀ v, J (u a) (J (u a) v) = -v)
    (hW : ∀ w, J (u a) (W w) = W (I • w)) : holomorphicNormalFrame J u W a = W := by
  have h := IsComplexLinear.complexLinearPart_eq (J := ((I • ContinuousLinearMap.id ℝ N :
    N →L[ℝ] N) : N →ₗ[ℝ] N)) (J' := (J (u a) : V →ₗ[ℝ] V)) (F := (W : N →ₗ[ℝ] V))
    (isComplexLinear_of_apply fun w ↦ by simpa using (hW w).symm)
    (LinearMap.ext fun v ↦ by simp [hsq])
  rw [← coe_holomorphicNormalFrame] at h
  exact ContinuousLinearMap.coe_injective h

/-- The normal frame is continuous where `u` is continuous and `J` is continuous at `u a`. -/
theorem continuousAt_holomorphicNormalFrame (hJ : ContinuousAt J (u a)) (hu : ContinuousAt u a)
    (W : N →L[ℝ] V) : ContinuousAt (holomorphicNormalFrame J u W) a := by
  unfold holomorphicNormalFrame
  exact (continuousAt_const.sub ((hJ.comp hu).clm_comp
    (continuousAt_const (y := W.comp (I • ContinuousLinearMap.id ℝ N))))).const_smul
    ((2 : ℝ)⁻¹)

/-- The normal frame is as regular as `u` and `J ∘ u`: it costs no derivative of `u`. -/
theorem contDiffOn_holomorphicNormalFrame {U : Set ℂ} {Ω : Set V} {n : ℕ∞ω}
    (hu : ContDiffOn ℝ n u U) (hJ : ContDiffOn ℝ n J Ω) (huΩ : MapsTo u U Ω) (W : N →L[ℝ] V) :
    ContDiffOn ℝ n (holomorphicNormalFrame J u W) U := by
  unfold holomorphicNormalFrame
  exact (contDiffOn_const.sub ((hJ.comp hu huΩ).clm_comp
    (contDiffOn_const (c := W.comp (I • ContinuousLinearMap.id ℝ N))))).const_smul
    ((2 : ℝ)⁻¹)

/-! ### The adapted extension -/

/-- The **adapted extension** `Φ (a, w) = u a + Θ_a w` of a disc `u` by the complex-linear normal
frame of `W`. Its local inverse near an immersed point is the chart of coordinates adapted to
`u` (`TauCeti.exists_holomorphicAdaptedChart`). -/
def holomorphicNormalExtension (J : V → V →L[ℝ] V) (u : ℂ → V) (W : N →L[ℝ] V) : ℂ × N → V :=
  normalExtension u (holomorphicNormalFrame J u W)

/-- `Φ (a, w) = u a + Θ_a w`. -/
@[simp]
theorem holomorphicNormalExtension_apply (J : V → V →L[ℝ] V) (u : ℂ → V) (W : N →L[ℝ] V)
    (p : ℂ × N) :
    holomorphicNormalExtension J u W p = u p.1 + holomorphicNormalFrame J u W p.1 p.2 :=
  normalExtension_apply u _ p

/-- The adapted extension agrees with the disc on the zero section. -/
theorem holomorphicNormalExtension_zero (J : V → V →L[ℝ] V) (u : ℂ → V) (W : N →L[ℝ] V)
    (a : ℂ) : holomorphicNormalExtension J u W (a, 0) = u a :=
  normalExtension_zero u _ a

/-- The adapted extension is `C^n` on `U × N` for `u` of class `C^n` on `U` and `J` of class `C^n`
on a set containing `u (U)`. -/
theorem contDiffOn_holomorphicNormalExtension {U : Set ℂ} {Ω : Set V} {n : ℕ∞ω}
    (hu : ContDiffOn ℝ n u U) (hJ : ContDiffOn ℝ n J Ω) (huΩ : MapsTo u U Ω) (W : N →L[ℝ] V) :
    ContDiffOn ℝ n (holomorphicNormalExtension J u W) (U ×ˢ univ) := by
  have hfst : MapsTo (Prod.fst : ℂ × N → ℂ) (U ×ˢ univ) U := fun _ hp ↦ hp.1
  exact ((hu.comp contDiffOn_fst hfst).add
    (((contDiffOn_holomorphicNormalFrame hu hJ huΩ W).comp contDiffOn_fst hfst).clm_apply
      contDiffOn_snd)).congr fun p _ ↦ holomorphicNormalExtension_apply J u W p

/-- **The derivative along the zero section.** At `(a, 0)` the adapted extension has derivative
`(α, ω) ↦ du_a α + Θ_a ω`; this needs only continuity of `J` at `u a`. -/
theorem hasFDerivAt_holomorphicNormalExtension_zero {Du : ℂ →L[ℝ] V} (hu : HasFDerivAt u Du a)
    (hJ : ContinuousAt J (u a)) (W : N →L[ℝ] V) :
    HasFDerivAt (holomorphicNormalExtension J u W) (Du.coprod (holomorphicNormalFrame J u W a))
      (a, 0) :=
  hasFDerivAt_normalExtension_zero hu (continuousAt_holomorphicNormalFrame hJ hu.continuousAt W)

/-- **The derivative along the zero section is complex-linear.** If `u` satisfies the
Cauchy–Riemann equation `Du 1 + J(u a) (Du i) = 0` at `a` and `J(u a)² = -1`, the map
`(α, ω) ↦ Du α + Θ_a ω` intertwines multiplication by `i` on `ℂ × N` with `J(u a)`. -/
theorem coprod_holomorphicNormalFrame_apply_I_smul {Du : ℂ →L[ℝ] V}
    (hsq : ∀ v, J (u a) (J (u a) v) = -v) (hCR : Du 1 + J (u a) (Du I) = 0) (p : ℂ × N) :
    Du.coprod (holomorphicNormalFrame J u W a) (I • p) =
      J (u a) (Du.coprod (holomorphicNormalFrame J u W a) p) := by
  have hDu := (LinearMap.forall_apply_I_mul_eq_iff (Du : ℂ →ₗ[ℝ] V)
    (A := (J (u a) : V →ₗ[ℝ] V)) hsq).2 hCR p.1
  simp only [ContinuousLinearMap.coe_coe] at hDu
  rw [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.coprod_apply, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, hDu, ← apply_holomorphicNormalFrame_apply hsq, map_add]

/-! ### The adapted chart -/

/-- **Adapted charts exist.** Let `u` be `C^ℓ` on an open `U ∋ a₀` and `J` be `C^ℓ` on an open
`Ω ⊇ u (U)`, with `1 ≤ ℓ` and `J(u a₀)² = -1`. Let `W : N →L[ℝ] V` be complex-linear for `i` and
`J(u a₀)`, with `(α, ω) ↦ du_{a₀} α + W ω` bijective from `ℂ × N` to `V`: the tangent line of `u`
at `a₀` and the image of `W` are complementary. Then the adapted extension restricts to a
partial homeomorphism around `(a₀, 0)` with source in `U × N`, target in `Ω`, and which is `C^ℓ`
with `C^ℓ` inverse. Its inverse is the chart of coordinates adapted to `u`. -/
theorem exists_holomorphicAdaptedChart [CompleteSpace V] [CompleteSpace N] {U : Set ℂ}
    {Ω : Set V} {a₀ : ℂ} {ℓ : ℕ∞ω} (hU : IsOpen U) (hΩ : IsOpen Ω) (ha₀ : a₀ ∈ U)
    (hℓ : 1 ≤ ℓ) (hu : ContDiffOn ℝ ℓ u U) (hJ : ContDiffOn ℝ ℓ J Ω) (huΩ : MapsTo u U Ω)
    (hsq : ∀ v, J (u a₀) (J (u a₀) v) = -v) (hW : ∀ w, J (u a₀) (W w) = W (I • w))
    (hbij : Function.Bijective ((fderiv ℝ u a₀).coprod W)) :
    ∃ e : OpenPartialHomeomorph (ℂ × N) V, ⇑e = holomorphicNormalExtension J u W ∧
      (a₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn ℝ ℓ e e.source ∧ ContDiffOn ℝ ℓ e.symm e.target := by
  have hΦ : ContDiffOn ℝ ℓ (holomorphicNormalExtension J u W) (U ×ˢ univ) :=
    contDiffOn_holomorphicNormalExtension hu hJ huΩ W
  have hs : IsOpen ((U ×ˢ univ) ∩ holomorphicNormalExtension J u W ⁻¹' Ω) :=
    hΦ.continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ) hΩ
  have hmem : (a₀, (0 : N)) ∈ (U ×ˢ univ) ∩ holomorphicNormalExtension J u W ⁻¹' Ω :=
    ⟨⟨ha₀, mem_univ _⟩, by
      simpa only [mem_preimage, holomorphicNormalExtension_zero] using (huΩ ha₀)⟩
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact absurd hℓ (by simp)
  have hdu : HasFDerivAt u (fderiv ℝ u a₀) a₀ :=
    ((hu.differentiableOn hℓ0).differentiableAt
      (hU.mem_nhds ha₀)).hasFDerivAt
  have hJc : ContinuousAt J (u a₀) := hJ.continuousOn.continuousAt (hΩ.mem_nhds (huΩ ha₀))
  have hD : fderiv ℝ (holomorphicNormalExtension J u W) (a₀, 0) = (fderiv ℝ u a₀).coprod W := by
    rw [(hasFDerivAt_holomorphicNormalExtension_zero hdu hJc W).fderiv,
      holomorphicNormalFrame_eq_self hsq hW]
  obtain ⟨e, he, hx, hsub, hsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph
    (hΦ.mono inter_subset_left) hs hmem hℓ
    (e := ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2))
    (by rw [ContinuousLinearEquiv.coe_ofBijective, hD])
  refine ⟨e, he, hx, fun p hp ↦ (hsub hp).1, fun y hy ↦ ?_, ?_, hsymm⟩
  · rw [← e.right_inv hy, he]
    exact (hsub (e.map_target hy)).2
  · rw [he]
    exact hΦ.mono fun p hp ↦ (hsub hp).1

end TauCeti

namespace OpenPartialHomeomorph

open TauCeti

variable {V N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup N]
  [NormedSpace ℂ N] {J : V → V →L[ℝ] V} {u : ℂ → V} {W : N →L[ℝ] V}
  {e : OpenPartialHomeomorph (ℂ × N) V}

/-- An adapted chart inverts the disc on the zero section of its source. -/
theorem symm_apply_of_coe_eq_holomorphicNormalExtension
    (he : ⇑e = holomorphicNormalExtension J u W) {a : ℂ} (ha : (a, 0) ∈ e.source) :
    e.symm (u a) = (a, 0) := by
  rw [← holomorphicNormalExtension_zero J u W a, ← he, e.left_inv ha]

/-- **Flattening.** A point of the source of an adapted chart is sent into the disc
`u {a | (a, 0) ∈ e.source}` exactly when it lies on the zero section. -/
theorem isImage_of_coe_eq_holomorphicNormalExtension
    (he : ⇑e = holomorphicNormalExtension J u W) :
    e.IsImage {p | p.2 = 0} (u '' {a | (a, 0) ∈ e.source}) := by
  intro p hp
  constructor
  · rintro ⟨a, ha, hap⟩
    have h : e (a, 0) = e p := by rw [he, holomorphicNormalExtension_zero, hap, he]
    exact (congrArg Prod.snd (e.injOn ha hp h)).symm
  · intro h0
    have hp' : p = (p.1, 0) := Prod.ext rfl h0
    refine ⟨p.1, ?_, ?_⟩
    · rw [mem_ofPred_eq, ← hp']
      exact hp
    · rw [hp', he, holomorphicNormalExtension_zero]

/-- **The structure is standard along the disc.** At a point `(a, 0)` of the source of an
adapted chart where `u` satisfies the Cauchy–Riemann equation and `J(u a)² = -1`, the structure
read in the chart is multiplication by `i`. -/
theorem pullbackEnd_of_coe_eq_holomorphicNormalExtension
    (he : ⇑e = holomorphicNormalExtension J u W) {a : ℂ} (ha : (a, 0) ∈ e.source)
    (hu : DifferentiableAt ℝ u a) (hJ : ContinuousAt J (u a))
    (hsq : ∀ v, J (u a) (J (u a) v) = -v) (hCR : fderiv ℝ u a 1 + J (u a) (fderiv ℝ u a I) = 0)
    (hs : DifferentiableAt ℝ e.symm (u a)) :
    e.pullbackEnd J (a, 0) = I • ContinuousLinearMap.id ℝ (ℂ × N) := by
  have hD := hasFDerivAt_holomorphicNormalExtension_zero hu.hasFDerivAt hJ W
  rw [← he] at hD
  have hea : e (a, 0) = u a := by rw [he, holomorphicNormalExtension_zero]
  have hs' : DifferentiableAt ℝ e.symm (e (a, 0)) := by rwa [hea]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [pullbackEnd_apply, hD.fderiv, hea, ← coprod_holomorphicNormalFrame_apply_I_smul hsq hCR,
    ← hD.fderiv, ← hea, e.fderiv_symm_apply_fderiv_apply_of_mem_source ha hD.differentiableAt hs']
  simp

end OpenPartialHomeomorph

namespace TauCeti

variable {V N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup N]
  [NormedSpace ℂ N] {J : V → V →L[ℝ] V} {u : ℂ → V} {W : N →L[ℝ] V}

/-- **Adapted charts with normal control** (McDuff–Salamon, Lemma 2.4.2). Let `u` be a
`J`-holomorphic disc of class `C^ℓ` on an open `U ∋ a₀`, `J` an almost complex structure of class
`C^ℓ` on an open `Ω ⊇ u (U)`, with `2 ≤ ℓ`, and `W` as in `TauCeti.exists_holomorphicAdaptedChart`.
Then there is an adapted chart, `C^ℓ` with `C^ℓ` inverse, in which the structure is multiplication
by `i` along the zero section of its source and differs from `i`, near `(a₀, 0)`, by at most a
constant times the normal coordinate. -/
theorem exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le [CompleteSpace V]
    [CompleteSpace N] {U : Set ℂ} {Ω : Set V} {a₀ : ℂ} {ℓ : ℕ∞ω} (hU : IsOpen U)
    (hΩ : IsOpen Ω) (ha₀ : a₀ ∈ U) (hℓ : 2 ≤ ℓ) (hu : ContDiffOn ℝ ℓ u U)
    (hJ : ContDiffOn ℝ ℓ J Ω) (huΩ : MapsTo u U Ω) (hsq : ∀ a ∈ U, ∀ v, J (u a) (J (u a) v) = -v)
    (hCR : ∀ a ∈ U, fderiv ℝ u a 1 + J (u a) (fderiv ℝ u a I) = 0)
    (hW : ∀ w, J (u a₀) (W w) = W (I • w))
    (hbij : Function.Bijective ((fderiv ℝ u a₀).coprod W)) :
    ∃ e : OpenPartialHomeomorph (ℂ × N) V, ⇑e = holomorphicNormalExtension J u W ∧
      (a₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn ℝ ℓ e e.source ∧ ContDiffOn ℝ ℓ e.symm e.target ∧
      (∀ a, (a, 0) ∈ e.source → e.pullbackEnd J (a, 0) = I • ContinuousLinearMap.id ℝ (ℂ × N)) ∧
      ∃ C : ℝ, ∀ᶠ p in 𝓝 (a₀, (0 : N)),
        ‖e.pullbackEnd J p - I • ContinuousLinearMap.id ℝ (ℂ × N)‖ ≤ C * ‖p.2‖ := by
  have hℓ₁ : 1 ≤ ℓ := le_trans (by norm_num) hℓ
  obtain ⟨e, he, h₀, hsU, htΩ, hc, hcs⟩ := exists_holomorphicAdaptedChart hU hΩ ha₀ hℓ₁ hu hJ
    huΩ (hsq a₀ ha₀) hW hbij
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact absurd hℓ₁ (by simp)
  -- The structure read in the chart is `i` on the zero section of the source.
  have hstd (a : ℂ) (ha : (a, 0) ∈ e.source) :
      e.pullbackEnd J (a, 0) = I • ContinuousLinearMap.id ℝ (ℂ × N) := by
    have haU : a ∈ U := (hsU ha).1
    have hut : u a ∈ e.target := by
      rw [← holomorphicNormalExtension_zero J u W a, ← he]
      exact e.map_source ha
    exact e.pullbackEnd_of_coe_eq_holomorphicNormalExtension he ha
      ((hu.differentiableOn hℓ0).differentiableAt (hU.mem_nhds haU))
      (hJ.continuousOn.continuousAt (hΩ.mem_nhds (huΩ haU))) (hsq a haU) (hCR a haU)
      ((hcs.differentiableOn hℓ0).differentiableAt (e.open_target.mem_nhds hut))
  refine ⟨e, he, h₀, hsU, htΩ, hc, hcs, hstd, ?_⟩
  -- The structure read in the chart is `C¹`, hence Lipschitz near `(a₀, 0)`.
  have hC1 : ContDiffAt ℝ 1 (e.pullbackEnd J) (a₀, 0) :=
    (e.contDiffOn_pullbackEnd hc hcs ((hJ.of_le (le_trans (by norm_num) hℓ)).mono htΩ)
      (by rw [one_add_one_eq_two]; exact hℓ)).contDiffAt (e.open_source.mem_nhds h₀)
  obtain ⟨K, t, ht, hK⟩ := hC1.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (e.open_source.mem_nhds h₀))
  refine ⟨K, Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, fun p hp ↦ ?_⟩⟩
  -- The point `(p.1, 0)` of the zero section below `p` lies in the same ball.
  have hp0 : (p.1, (0 : N)) ∈ Metric.ball (a₀, (0 : N)) r := by
    rw [Metric.mem_ball, Prod.dist_eq] at hp ⊢
    simp only [dist_self, max_eq_left dist_nonneg]
    exact lt_of_le_of_lt (le_max_left _ _) hp
  rw [← hstd p.1 (hrt hp0).2]
  have hsub : p - (p.1, 0) = (0, p.2) := Prod.ext (sub_self _) (sub_zero _)
  calc ‖e.pullbackEnd J p - e.pullbackEnd J (p.1, 0)‖
      ≤ K * ‖p - (p.1, 0)‖ := hK.norm_sub_le (hrt hp).1 (hrt hp0).1
    _ = K * ‖p.2‖ := by rw [hsub, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]

/-- **The normal Cauchy–Riemann inequality.** Let `A` be an endomorphism of `ℂ × N` within `ε` of
multiplication by `i`. If the derivative `D` of a disc `(a, b)` satisfies the Cauchy–Riemann
equation `D 1 + A (D i) = 0` for `A`, its normal component satisfies
`‖∂ₛb + i ∂ₜb‖ ≤ ε ‖∂ₜ(a, b)‖`. With the structure read in an adapted chart at the point
`(a, b)` of the disc, `ε = C ‖b‖` by
`TauCeti.exists_holomorphicAdaptedChart_norm_pullbackEnd_sub_le`, which gives
`‖∂ₛb + i ∂ₜb‖ ≤ C ‖b‖ ‖∂ₜ(a, b)‖`. -/
theorem norm_snd_add_I_smul_snd_le {A : ℂ × N →L[ℝ] ℂ × N} {ε : ℝ}
    (hA : ‖A - I • ContinuousLinearMap.id ℝ (ℂ × N)‖ ≤ ε) {D : ℂ →L[ℝ] ℂ × N}
    (hCR : D 1 + A (D I) = 0) : ‖(D 1).2 + I • (D I).2‖ ≤ ε * ‖D I‖ := by
  have h : D 1 + I • D I = -((A - I • ContinuousLinearMap.id ℝ (ℂ × N)) (D I)) := by
    have hsub : (A - I • ContinuousLinearMap.id ℝ (ℂ × N)) (D I) = A (D I) - I • D I := by simp
    rw [hsub, eq_neg_of_add_eq_zero_left hCR]
    abel
  calc ‖(D 1).2 + I • (D I).2‖ = ‖(D 1 + I • D I).2‖ := rfl
    _ ≤ ‖D 1 + I • D I‖ := norm_snd_le _
    _ = ‖(A - I • ContinuousLinearMap.id ℝ (ℂ × N)) (D I)‖ := by rw [h, norm_neg]
    _ ≤ ‖A - I • ContinuousLinearMap.id ℝ (ℂ × N)‖ * ‖D I‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖D I‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)

/-! ### Check: the integrable model -/

/-- **The integrable model.** For `V = ℂ × N` with the structure `i`, the disc `a ↦ (a, 0)` and
the frame `w ↦ (0, w)`, the adapted extension is the identity. -/
theorem holomorphicNormalExtension_inl_inr :
    holomorphicNormalExtension (fun _ ↦ I • ContinuousLinearMap.id ℝ (ℂ × N))
      (ContinuousLinearMap.inl ℝ ℂ N) (ContinuousLinearMap.inr ℝ ℂ N) = id := by
  funext p
  have hf : holomorphicNormalFrame (fun _ ↦ I • ContinuousLinearMap.id ℝ (ℂ × N))
      (ContinuousLinearMap.inl ℝ ℂ N) (ContinuousLinearMap.inr ℝ ℂ N) p.1 =
      ContinuousLinearMap.inr ℝ ℂ N :=
    holomorphicNormalFrame_eq_self (fun v ↦ by simp [smul_smul])
      (fun w ↦ by ext <;> simp)
  rw [holomorphicNormalExtension_apply, hf]
  ext <;> simp

end TauCeti
