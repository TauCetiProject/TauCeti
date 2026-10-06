/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.Morse.Lemma
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Pseudo-gradient fields adapted to a Morse function

Let `f` be a smooth function on a boundaryless smooth manifold `M` modelled on a
finite-dimensional real normed space `E`. A vector field `X` on `M` is a
**pseudo-gradient field adapted to `f`** when

* `X` is smooth;
* `f` strictly decreases along `X` away from the critical points: `df(X) < 0` wherever `df ≠ 0`;
* near each critical point `x` there is a Morse chart (`TauCeti.MorseChart`) in which `X` is the
  negative gradient of the quadratic normal form: if `f = f x + (1/2) Σᵢ wᵢ zᵢ²` in the
  coordinates `z = L (ψ y)`, then `X` reads `z ↦ (-wᵢ zᵢ)ᵢ`.

This is the class of vector fields with which Audin and Damian build Morse homology. Near a
critical point the flow of an adapted pseudo-gradient is linear in the Morse chart, so its local
stable and unstable sets are exactly the coordinate planes. All the analysis is global.

## Main declarations

* `TauCeti.mderivAlong`: the derivative of a real function along a vector field, as a real number.
* `TauCeti.IsAdaptedPseudoGradient`: the definition.
* `TauCeti.hasDerivAt_comp_of_isMIntegralCurve`: along an integral curve of `X`, the derivative of
  `f` is `mderivAlong f X`.
* `TauCeti.isInvertible_mfderiv_of_mem_maximalAtlas`: the derivative of a chart of the maximal
  atlas is invertible on its source.
* `TauCeti.IsAdaptedPseudoGradient.eq_zero_iff`: the zeros of an adapted pseudo-gradient are
  exactly the critical points of `f`.
* `TauCeti.IsAdaptedPseudoGradient.antitone_comp`: `f` is antitone along every integral curve.
* `TauCeti.IsAdaptedPseudoGradient.strictAnti_comp`: `f` is strictly antitone along an integral
  curve that never meets a critical point.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Definition 2.2.1 (pseudo-gradient fields) and Section 2.2.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The derivative `df_x(X x)` of a real function `f` along a vector field `X` at `x`, as a real
number. The differential takes values in `TangentSpace 𝓘(ℝ) (f x)`, which is `ℝ` by definition
but carries none of its order structure, so the value is read back in `ℝ` here. -/
noncomputable def mderivAlong (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : M) : ℝ :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x (X x)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Unfold `mderivAlong`. -/
theorem mderivAlong_def (x : M) : mderivAlong f X x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x (X x) := by
  rw [mderivAlong]

/-- A vector field `X` is a **pseudo-gradient field adapted to `f`** when it is smooth, `f`
strictly decreases along it away from the critical points, and near each critical point there is
a Morse chart in which it is the negative gradient `z ↦ (-wᵢ zᵢ)ᵢ` of the quadratic normal form
`(1/2) Σᵢ wᵢ zᵢ²`. -/
structure IsAdaptedPseudoGradient (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Prop where
  contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
    (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M))
  mderivAlong_neg : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 → mderivAlong f X x < 0
  exists_morseChart : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
    ∃ φ : MorseChart E f x, ∀ y ∈ φ.toChart.source,
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative of a chart of the maximal atlas is invertible on its source. -/
theorem isInvertible_mfderiv_of_mem_maximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : M} (hy : y ∈ e.source) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).IsInvertible := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have := isInvertible_mfderiv_extend he1 hy
  have hext : (e.extend 𝓘(ℝ, E) : M → E) = e := by ext z; simp
  rwa [hext] at this

variable {γ : ℝ → M}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Along an integral curve of `X`, the derivative of `f` is `df(X)`. -/
theorem hasDerivAt_comp_of_isMIntegralCurve (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hγ : IsMIntegralCurve γ X) (t : ℝ) :
    HasDerivAt (f ∘ γ) (mderivAlong f X (γ t)) t := by
  have hfγ : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (γ t)) :=
    (hf.mdifferentiable (by simp) (γ t)).hasMFDerivAt
  have hcomp := hfγ.comp t (hγ t)
  rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
  rw [hasDerivAt_iff_hasFDerivAt]
  refine hcomp.congr_fderiv (ContinuousLinearMap.ext_ring ?_)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) ((1 : ℝ) • X (γ t)) =
    (1 : ℝ) • mderivAlong f X (γ t)
  rw [one_smul, one_smul]
  rfl


namespace IsAdaptedPseudoGradient

omit [FiniteDimensional ℝ E] in
/-- An adapted pseudo-gradient does not vanish at a regular point of `f`. -/
theorem ne_zero_of_mfderiv_ne_zero (hX : IsAdaptedPseudoGradient f X) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) : X x ≠ 0 := by
  intro h0
  have := hX.mderivAlong_neg x hx
  rw [mderivAlong, h0, map_zero] at this
  exact lt_irrefl _ this

omit [FiniteDimensional ℝ E] in
/-- An adapted pseudo-gradient vanishes at every critical point of `f`: in the Morse chart it is
the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, which vanishes at the centre. -/
theorem eq_zero_of_mfderiv_eq_zero (hX : IsAdaptedPseudoGradient f X) {x : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) : X x = 0 := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  have h := hφ x φ.mem_source
  rw [φ.apply_self, map_zero] at h
  simp only [Pi.zero_apply, mul_zero, neg_zero] at h
  have h0 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x (X x) = 0 := φ.coord.map_eq_zero_iff.1 h
  have hinv := isInvertible_mfderiv_of_mem_maximalAtlas φ.mem_maximalAtlas φ.mem_source
  rw [← hinv.inverse_apply_self (X x), h0, map_zero]

omit [FiniteDimensional ℝ E] in
/-- **The zeros of an adapted pseudo-gradient are the critical points of `f`.** -/
theorem eq_zero_iff (hX : IsAdaptedPseudoGradient f X) {x : M} :
    X x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ hX.ne_zero_of_mfderiv_ne_zero hx h, hX.eq_zero_of_mfderiv_eq_zero⟩

omit [FiniteDimensional ℝ E] in
/-- **`f` is antitone along every integral curve of an adapted pseudo-gradient.** -/
theorem antitone_comp (hX : IsAdaptedPseudoGradient f X) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hγ : IsMIntegralCurve γ X) : Antitone (f ∘ γ) := by
  refine antitone_of_hasDerivAt_nonpos (hasDerivAt_comp_of_isMIntegralCurve hf hγ) fun t ↦ ?_
  by_cases ht : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) = 0
  · rw [mderivAlong, ht]
    exact le_rfl
  · exact (hX.mderivAlong_neg _ ht).le

omit [FiniteDimensional ℝ E] in
/-- **`f` is strictly antitone along an integral curve of an adapted pseudo-gradient that never
meets a critical point.** -/
theorem strictAnti_comp (hX : IsAdaptedPseudoGradient f X) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hγ : IsMIntegralCurve γ X) (hcrit : ∀ t, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) ≠ 0) :
    StrictAnti (f ∘ γ) :=
  strictAnti_of_hasDerivAt_neg (hasDerivAt_comp_of_isMIntegralCurve hf hγ) fun t ↦
    hX.mderivAlong_neg _ (hcrit t)

end IsAdaptedPseudoGradient

end TauCeti
