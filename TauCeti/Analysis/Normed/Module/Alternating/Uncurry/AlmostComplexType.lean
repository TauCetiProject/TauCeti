/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.AlmostComplexType
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Alternation and the `(p,q)` type of complex-valued forms

Let `J` be a continuous real-linear endomorphism of a real normed space `E` with `J² = -1`. The
exterior derivative of a differential form is the alternation
`ContinuousAlternatingMap.alternatizeUncurryFin` of its derivative. This file shows how the
alternation interacts with the type decomposition of complex-valued forms for `J`.

The derivation `J.alternatingDerivation` of `(k+1)`-forms corresponds under alternation to
`θ ↦ θ ∘ J + J.alternatingDerivation ∘ θ` on families `θ : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F` of
`k`-forms. Using it, the main theorem identifies the types that can occur in the alternation of a
first-order variation of a form of type `(p,q)` along a varying `J`: only `(p+2,q-1)`, `(p+1,q)`,
`(p,q+1)` and `(p-1,q+2)`. The proof only uses that the type-`(P,Q)` projection turns the
derivation of `J` into multiplication by `(P - Q) * I`: the components of the six alternations
built from the variation satisfy a linear system whose determinant is
`(t² + 1)(t² + 9)`, `t = ((P - Q) - (p - q)) * I`, and this is nonzero for every other type.

On an almost complex manifold this is the pointwise reason why the exterior derivative of a form
of type `(p,q)` has components of these four types only.

## Main declarations

* `ContinuousLinearMap.alternatingDerivation_eq_fderivCompContinuousLinearMap`: the derivation of
  an endomorphism is a derivative of pullback, hence continuous linear in the endomorphism.
* `ContinuousLinearMap.alternatingDerivation_alternatizeUncurryFin`: alternation intertwines the
  derivations.
* `ContinuousAlternatingMap.IsOfType.typeProjection_alternatizeUncurryFin_eq_zero`: the four
  bidegrees.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public section

noncomputable section

open Complex Function Polynomial
open ContinuousAlternatingMap (alternatizeUncurryFin alternatizeUncurryFin_apply)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

namespace ContinuousLinearMap

/-- On normed spaces, the derivation induced by `J` is the derivative at the identity, in the
direction `J`, of pullback of alternating maps. -/
theorem alternatingDerivation_eq_fderivCompContinuousLinearMap (J : E →L[ℝ] E)
    (φ : E [⋀^Fin k]→L[ℝ] F) :
    J.alternatingDerivation φ = φ.fderivCompContinuousLinearMap (.id ℝ E) J := by
  ext v
  rw [ContinuousLinearMap.alternatingDerivation_apply,
    ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg φ (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

/-- Alternation intertwines the derivation induced by `J` on `(k+1)`-forms with the derivation
`θ ↦ θ ∘ J + J.alternatingDerivation ∘ θ` of families of `k`-forms, where `θ'` is any family
agreeing pointwise with `J.alternatingDerivation ∘ θ`. -/
theorem alternatingDerivation_alternatizeUncurryFin (J : E →L[ℝ] E)
    {θ θ' : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F} (hθ : ∀ v, J.alternatingDerivation (θ v) = θ' v) :
    J.alternatingDerivation (alternatizeUncurryFin θ) =
      alternatizeUncurryFin (θ ∘L J) + alternatizeUncurryFin θ' := by
  ext v
  simp only [alternatingDerivation_apply, alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.add_apply, comp_apply, ← hθ, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fin.sum_univ_succAbove _ i]
  simp [update_of_ne, Fin.removeNth_apply]

/-- The derivation of `J` and the type projections commute. -/
private lemma typeProjection_alternatingDerivation {J : E →L[ℝ] E} (hJ : ∀ v, J (J v) = -v)
    {P Q : ℕ} (x : E [⋀^Fin k]→L[ℝ] F) :
    J.typeProjection P Q (J.alternatingDerivation x) =
      (((P : ℂ) - Q) * I) • J.typeProjection P Q x := by
  rw [← alternatingDerivation_typeProjection hJ, typeProjection_eq_aeval]
  have h := ((commute_X (typePolynomial k P Q)).map
    (aeval (J.alternatingDerivation : Module.End ℂ (E [⋀^Fin k]→L[ℝ] F)))).eq
  rw [aeval_X] at h
  exact (LinearMap.congr_fun h x).symm

/-- In the type-`(P,Q)` component, alternation intertwines the derivation of `J`, which acts there
by `(P - Q) * I`, with `θ ↦ θ ∘ J + J.alternatingDerivation ∘ θ`. -/
private lemma smul_typeProjection_alternatizeUncurryFin {J : E →L[ℝ] E} (hJ : ∀ v, J (J v) = -v)
    {P Q : ℕ} {θ θ' : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F}
    (hθ : ∀ v, J.alternatingDerivation (θ v) = θ' v) :
    (((P : ℂ) - Q) * I) • J.typeProjection P Q (alternatizeUncurryFin θ) =
      J.typeProjection P Q (alternatizeUncurryFin (θ ∘L J)) +
        J.typeProjection P Q (alternatizeUncurryFin θ') := by
  rw [← typeProjection_alternatingDerivation hJ, alternatingDerivation_alternatizeUncurryFin J hθ,
    map_add]

/-- The shift `t = ((P - Q) - (p - q)) * I` between the eigenvalues of types `(P,Q)` and `(p,q)`,
for `P + Q = p + q + 1`, is `(2 (P - p) - 1) * I`. It is a root of `(t² + 1)(t² + 9)` only when
`P - p ∈ {-1, 0, 1, 2}`. -/
private lemma typeShift_poly_ne_zero {p q P Q : ℕ} (hPQ : P + Q = p + q + 1)
    (hP : P + 1 < p ∨ p + 2 < P) :
    (((P : ℂ) - Q) * I - ((p : ℂ) - q) * I) ^ 4 +
      10 * (((P : ℂ) - Q) * I - ((p : ℂ) - q) * I) ^ 2 + 9 ≠ 0 := by
  set n : ℤ := 2 * P - 2 * p - 1 with hn
  have hk : (P : ℂ) + Q = p + q + 1 := by exact_mod_cast hPQ
  have htn : ((P : ℂ) - Q) * I - ((p : ℂ) - q) * I = (n : ℂ) * I := by
    rw [hn]
    push_cast
    linear_combination (-I) * hk
  have hn5 : 25 ≤ n ^ 2 := by
    rcases hP with h | h <;> nlinarith
  rw [htn]
  have h : ((n : ℂ) * I) ^ 4 + 10 * ((n : ℂ) * I) ^ 2 + 9 = ((n ^ 4 - 10 * n ^ 2 + 9 : ℤ) : ℂ) := by
    push_cast
    linear_combination ((n : ℂ) ^ 4 * (I ^ 2 - 1) + 10 * (n : ℂ) ^ 2) * I_sq
  rw [h, Int.cast_ne_zero]
  nlinarith

/-- The linear system satisfied by the type-`(P,Q)` components of the six alternations built from
a first-order variation: if `t` is not a root of `(t² + 1)(t² + 9)`, its only solution has
`x₁ = 0`. -/
private lemma eq_zero_of_typeShift {V : Type*} [AddCommGroup V] [Module ℂ V] {t : ℂ}
    (ht : t ^ 4 + 10 * t ^ 2 + 9 ≠ 0) {x₁ x₂ y₁ y₂ z₁ z₂ : V} (f₁ : t • x₁ = x₂ - y₁)
    (f₂ : t • x₂ = -x₁ - y₂) (f₃ : t • y₁ = y₂ + (2 : ℂ) • z₁)
    (f₄ : t • y₂ = -y₁ + (2 : ℂ) • z₂) (f₅ : t • z₁ = z₂ - (2 : ℂ) • y₁)
    (f₆ : t • z₂ = -z₁ - (2 : ℂ) • y₂) : x₁ = 0 := by
  have g₂ : (t ^ 2) • x₁ = -x₁ - (2 : ℂ) • y₂ - (2 : ℂ) • z₁ := by
    linear_combination (norm := module) t • f₁ + f₂ - f₃
  have g₃ : (t ^ 3) • x₁ = -x₂ + (7 : ℂ) • y₁ - (6 : ℂ) • z₂ := by
    linear_combination (norm := module) t • g₂ - f₁ - (2 : ℂ) • f₄ - (2 : ℂ) • f₅
  have hpoly : (t ^ 4 + 10 * t ^ 2 + 9) • x₁ = 0 := by
    linear_combination (norm := module)
      t • g₃ - f₂ + (7 : ℂ) • f₃ - (6 : ℂ) • f₆ + (10 : ℂ) • g₂
  exact (smul_eq_zero.1 hpoly).resolve_left ht

end ContinuousLinearMap

namespace ContinuousAlternatingMap

open ContinuousLinearMap

/-- For a form `ω` of type `(p,q)` and an endomorphism `X` anticommuting with `J`, the derivation
of `J` acts on `X.alternatingDerivation ω` as `(p - q) * I` up to twice the derivation of `X ∘ J`.
Since `X ∘ J` also anticommutes with `J`, this is why `X` moves the type by `(±1,∓1)`. -/
private lemma IsOfType.alternatingDerivation_alternatingDerivation_of_anticomm {J X : E →L[ℝ] E}
    {ω : E [⋀^Fin k]→L[ℝ] F} {p q : ℕ} (hω : ω.IsOfType J p q)
    (hX : ∀ w, X (J w) = -J (X w)) :
    J.alternatingDerivation (X.alternatingDerivation ω) =
      (((p : ℂ) - q) * I) • X.alternatingDerivation ω +
        (2 : ℂ) • (X ∘L J).alternatingDerivation ω := by
  have h := alternatingDerivation_alternatingDerivation_sub J X ω
  have hJX : J ∘L X = -(X ∘L J) := by ext w; simp [hX]
  rw [hω.alternatingDerivation_eq, map_smul, hJX,
    alternatingDerivation_eq_fderivCompContinuousLinearMap (-(X ∘L J)), map_neg,
    ← alternatingDerivation_eq_fderivCompContinuousLinearMap] at h
  linear_combination (norm := module) h

/-- **Four bidegrees.** Let `ω` be a form of type `(p,q)` for `J` with `J² = -1`, and let
`(η, A)` be a first-order variation of the pair `(ω, J)` preserving this: `A v` anticommutes with
`J`, which is the derivative of `J² = -1`, and `J.alternatingDerivation (η v) +
(A v).alternatingDerivation ω = (p - q) * I • η v`, which is the derivative of the type equation.
Then the alternation of `η` has no component of type `(P,Q)` unless `P - p ∈ {-1, 0, 1, 2}`: its
only components are of types `(p+2,q-1)`, `(p+1,q)`, `(p,q+1)` and `(p-1,q+2)`.

Applied to the derivatives of a form and of an almost complex structure in a chart, this is the
splitting of the exterior derivative into its four bidegrees. -/
theorem IsOfType.typeProjection_alternatizeUncurryFin_eq_zero
    {J : E →L[ℝ] E} (hJ : ∀ v, J (J v) = -v) {ω : E [⋀^Fin k]→L[ℝ] F} {p q : ℕ}
    (hω : ω.IsOfType J p q) {A : E →L[ℝ] E →L[ℝ] E} (hA : ∀ v w, A v (J w) = -J (A v w))
    {η : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F}
    (hη : ∀ v, J.alternatingDerivation (η v) + (A v).alternatingDerivation ω =
      (((p : ℂ) - q) * I) • η v)
    {P Q : ℕ} (hP : P + 1 < p ∨ p + 2 < P) :
    J.typeProjection P Q (alternatizeUncurryFin η) = 0 := by
  by_cases hPQ : P + Q = k + 1
  swap
  · simp [typeProjection_eq_zero hJ hPQ]
  set c : ℂ := ((p : ℂ) - q) * I
  -- The derivation `X ↦ X.alternatingDerivation ω` is continuous linear in the endomorphism, so
  -- `β v = (A v).alternatingDerivation ω` and `γ v = (A v ∘ J).alternatingDerivation ω` are
  -- continuous linear in `v`.
  let D : (E →L[ℝ] E) →L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
    fderivCompContinuousLinearMapCLM F (.id ℝ E) ω
  have hD (X : E →L[ℝ] E) : X.alternatingDerivation ω = D X :=
    alternatingDerivation_eq_fderivCompContinuousLinearMap X ω
  let β := D ∘L A
  let γ := D ∘L ((compL ℝ E E E).flip J ∘L A)
  have hβ (v : E) : J.alternatingDerivation (β v) = c • β v + (2 : ℂ) • γ v := by
    simpa [β, γ, ← hD] using hω.alternatingDerivation_alternatingDerivation_of_anticomm (hA v)
  have hγ (v : E) : J.alternatingDerivation (γ v) = c • γ v - (2 : ℂ) • β v := by
    have hBJ : (A v ∘L J) ∘L J = -A v := by ext w; simp [hJ]
    have h := hω.alternatingDerivation_alternatingDerivation_of_anticomm
      (X := A v ∘L J) fun w ↦ by simp [hA, hJ]
    rw [hBJ, hD (-A v), map_neg] at h
    simp only [γ, β, ContinuousLinearMap.comp_apply, compL_apply, flip_apply, ← hD, h]
    module
  have hη' (v : E) : J.alternatingDerivation (η v) = c • η v - β v := by
    simp only [β, ContinuousLinearMap.comp_apply, ← hD]
    exact eq_sub_of_add_eq (hη v)
  have halt_sub (θ₁ θ₂ : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) :
      alternatizeUncurryFin (θ₁ - θ₂) = alternatizeUncurryFin θ₁ - alternatizeUncurryFin θ₂ :=
    map_sub (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F) θ₁ θ₂
  have hJJ (θ : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) :
      alternatizeUncurryFin ((θ ∘L J) ∘L J) = -alternatizeUncurryFin θ := by
    have h : (θ ∘L J) ∘L J = -θ := by ext v; simp [hJ]
    rw [h]
    exact map_neg (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F) θ
  -- The type-`(P,Q)` components of the alternations of `η`, `β`, `γ` and of their compositions
  -- with `J` satisfy a linear system whose determinant does not vanish.
  have e1 := smul_typeProjection_alternatizeUncurryFin (P := P) (Q := Q) hJ (θ := η)
    (θ' := c • η - β) fun v ↦ by simp [hη']
  have e2 := smul_typeProjection_alternatizeUncurryFin (P := P) (Q := Q) hJ (θ := η ∘L J)
    (θ' := c • (η ∘L J) - β ∘L J) fun v ↦ by simp [hη']
  have e3 := smul_typeProjection_alternatizeUncurryFin (P := P) (Q := Q) hJ (θ := β)
    (θ' := c • β + (2 : ℂ) • γ) fun v ↦ by simp [hβ]
  have e4 := smul_typeProjection_alternatizeUncurryFin (P := P) (Q := Q) hJ (θ := β ∘L J)
    (θ' := c • (β ∘L J) + (2 : ℂ) • (γ ∘L J)) fun v ↦ by simp [hβ]
  have e5 := smul_typeProjection_alternatizeUncurryFin (P := P) (Q := Q) hJ (θ := γ)
    (θ' := c • γ - (2 : ℂ) • β) fun v ↦ by simp [hγ]
  have e6 := smul_typeProjection_alternatizeUncurryFin (P := P) (Q := Q) hJ (θ := γ ∘L J)
    (θ' := c • (γ ∘L J) - (2 : ℂ) • (β ∘L J)) fun v ↦ by simp [hγ]
  simp only [halt_sub, alternatizeUncurryFin_add, alternatizeUncurryFin_smul, hJJ, map_add,
    map_sub, map_smul, map_neg] at e1 e2 e3 e4 e5 e6
  exact eq_zero_of_typeShift (t := ((P : ℂ) - Q) * I - c)
    (x₂ := J.typeProjection P Q (alternatizeUncurryFin (η ∘L J)))
    (y₁ := J.typeProjection P Q (alternatizeUncurryFin β))
    (y₂ := J.typeProjection P Q (alternatizeUncurryFin (β ∘L J)))
    (z₁ := J.typeProjection P Q (alternatizeUncurryFin γ))
    (z₂ := J.typeProjection P Q (alternatizeUncurryFin (γ ∘L J)))
    (typeShift_poly_ne_zero (hPQ.trans (by rw [hω.add_eq])) hP)
    (by linear_combination (norm := module) e1) (by linear_combination (norm := module) e2)
    (by linear_combination (norm := module) e3) (by linear_combination (norm := module) e4)
    (by linear_combination (norm := module) e5) (by linear_combination (norm := module) e6)

end ContinuousAlternatingMap
