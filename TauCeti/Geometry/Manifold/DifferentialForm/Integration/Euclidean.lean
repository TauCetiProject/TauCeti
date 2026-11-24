/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Integrals of top forms through parametrizations by `ℝᵖ`

Against the standard orientation of `ℝᵖ = EuclideanSpace ℝ (Fin p)`
(`TauCeti.Manifold.Orientation.euclideanSpace p`), in which the standard basis `(e₁, …, eₚ)` is
positive, the integral of an integrable top form `ψ` on `ℝᵖ` is the Lebesgue integral of
`ψ(e₁, …, eₚ)` (`TauCeti.integralTopForm_euclideanSpace_eq_integral`).

Let `N` be a `p`-dimensional manifold with an orientation `o`, and let `g : ℝᵖ → N` be an open
embedding on an open set `U ⊆ ℝᵖ` that preserves orientation there from the standard orientation
to `o`. Then an integrable top form `φ` on `N` supported in the image `g(K)` of a closed set
`K ⊆ U` integrates to

`∫_N φ = ∫_K (g^*φ)(e₁, …, eₚ) dx`

(`TauCeti.integralTopForm_eq_setIntegral_mpullback`). The proof moves the integral to `U` by
change of variables along the open embedding `U → N`, and then to `ℝᵖ`, on which the pullback
`g^*φ`, cut off outside `U`, is a top form vanishing outside `K`.

## Main results

* `TauCeti.integralTopForm_euclideanSpace_eq_integral`: `∫_{ℝᵖ} ψ = ∫ ψ(e₁, …, eₚ) dx`.
* `TauCeti.integralTopForm_eq_setIntegral_mpullback`: `∫_N φ = ∫_K (g^*φ)(e₁, …, eₚ) dx` for an
  orientation-preserving parametrization `g` of a neighbourhood of the support of `φ`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 16.6 and its proof.
-/

public section

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped Manifold

namespace TauCeti

/-- Against the standard orientation of `ℝᵖ`, the oriented integral of an integrable top form is
the Lebesgue integral of its value on the standard basis. -/
theorem integralTopForm_euclideanSpace_eq_integral {p : ℕ}
    {ψ : RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (EuclideanSpace ℝ (Fin p)) ℝ p}
    (hψ : IntegrableTopForm ψ) :
    integralTopForm (Manifold.Orientation.euclideanSpace p) ψ =
      ∫ x, ψ x fun i ↦ EuclideanSpace.single i 1 := by
  rw [Manifold.Orientation.euclideanSpace_eq_model,
    integralTopForm_model_eq_integral_of_integrableTopForm _ _ hψ _ rfl,
    OrthonormalBasis.addHaar_eq_volume]
  refine integral_congr_ae (ae_of_all _ fun x ↦ congrArg (ψ x) (funext fun i ↦ ?_))
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I 1 N] {p : ℕ}

/-- **Integration through an oriented parametrization by `ℝᵖ`.** Let `g : ℝᵖ → N` be an open
embedding on an open set `U ⊆ ℝᵖ` which preserves orientation there from the standard orientation
of `ℝᵖ` to `o`. Then an integrable top form on `N` supported in the image of a closed set
`K ⊆ U` integrates to `∫_N φ = ∫_K (g^*φ)(e₁, …, eₚ) dx`. -/
theorem integralTopForm_eq_setIntegral_mpullback (o : Manifold.Orientation I N (Fin p))
    {U : Opens (EuclideanSpace ℝ (Fin p))} {K : Set (EuclideanSpace ℝ (Fin p))} (hK : IsClosed K)
    (hKU : K ⊆ U) {g : EuclideanSpace ℝ (Fin p) → N}
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace p) o g x)
    {φ : RoughForm I N ℝ p} (hφ : IntegrableTopForm φ)
    (hsupp : _root_.tsupport (α := E [⋀^Fin p]→L[ℝ] ℝ) φ ⊆ g '' K) :
    integralTopForm o φ =
      ∫ x in K, mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g φ x
        fun i ↦ EuclideanSpace.single i 1 := by
  classical
  let std := Manifold.Orientation.euclideanSpace p
  have hgd (x : U) : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g x :=
    mdifferentiableAt_of_isInvertible_mfderiv (ho x x.property).isInvertible_mfderiv
  -- The pullback of `φ` along `g`, cut off outside `U`, is a top form on `ℝᵖ` which vanishes
  -- outside `K`.
  let ψ : RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (EuclideanSpace ℝ (Fin p)) ℝ p := fun y ↦
    if y ∈ U then mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g φ y else 0
  have hψK (y : EuclideanSpace ℝ (Fin p)) (hy : y ∉ K) : ψ y = 0 := by
    by_cases hyU : y ∈ U
    · by_cases hφy : φ (g y) = 0
      · ext v
        simp [ψ, hyU, mpullback_apply, hφy]
      · obtain ⟨z, hz, hzy⟩ := hsupp (subset_tsupport _ hφy)
        have hzy' : z = y :=
          congrArg Subtype.val (hg.injective (a₁ := ⟨z, hKU hz⟩) (a₂ := ⟨y, hyU⟩) hzy)
        exact absurd (hzy' ▸ hz) hy
    · simp [ψ, hyU]
  have hψs : Function.support (M := EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) ψ ⊆ K :=
    fun y hy ↦ by_contra fun h ↦ hy (hψK y h)
  have hψU : _root_.tsupport (α := EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) ψ ⊆ U :=
    (closure_minimal hψs hK).trans hKU
  -- Restricted to `U`, it is the pullback of `φ` along the open embedding `U → N`.
  have hres : mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      ((↑) : U → EuclideanSpace ℝ (Fin p)) ψ =
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))) φ := by
    funext x
    rw [mpullback_comp_at (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero) (hgd x)]
    ext v
    simp [ψ, x.property]
  have hrange : _root_.tsupport (α := E [⋀^Fin p]→L[ℝ] ℝ) φ ⊆
      range (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))) := by
    rintro _ hy
    obtain ⟨z, hz, rfl⟩ := hsupp hy
    exact ⟨⟨z, hKU hz⟩, rfl⟩
  have hoU (x : U) : Manifold.Orientation.IsOrientationPreservingAt (std.restrict U) o
      (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))) x :=
    (ho x x.property).comp (std.isOrientationPreservingAt_restrict U x)
  have hψi : IntegrableTopForm ψ := by
    rwa [← U.integrableTopForm_mpullback_subtypeVal_iff hψU, hres,
      hg.integrableTopForm_mpullback_iff (fun x ↦ (hoU x).isInvertible_mfderiv)
        (by simpa using o.card_eq) hrange]
  rw [← hg.integralTopForm_mpullback_of_isOrientationPreservingAt hoU hrange, ← hres,
    integralTopForm_mpullback_subtypeVal std U hψU, integralTopForm_euclideanSpace_eq_integral hψi,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [hψK y hy]; rfl]
  refine setIntegral_congr_fun hK.measurableSet fun x hx ↦ ?_
  simp only [ψ, show x ∈ U from hKU hx, ↓reduceIte]

end TauCeti
