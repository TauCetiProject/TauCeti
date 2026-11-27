/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Cohomology
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Tangent.Basic

/-!
# The first cohomology of the tangent bundle of `ℂPᵐ⁺¹` along a line

Let `ℓ' : ℂℙ¹ → ℂPᵐ⁺¹` be a line, `[v] ↦ [f v]` for an injective linear map `f : ℂ² → ℂᵐ⁺²`. The
pullback `ℓ'* TℂPᵐ⁺¹` of the tangent bundle of `ℂPᵐ⁺¹` is `𝒪(2) ⊕ 𝒪(1)ᵐ`
(`Projectivization.exists_continuousLinearEquiv_pullback_map_tangentSpace_twistSumCore_lineTwist`),
and the first Čech cohomology of a split bundle on `ℂℙ¹` vanishes when every twist is at least
`-1` (`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le`),
so `H¹(ℂℙ¹, ℓ'* TℂPᵐ⁺¹) = 0`. This is the vanishing of `H¹(C, u* TℂPⁿ)` on the line component `u`
of a genus-zero stable map in the class of a line, on which the regularity of such maps rests
(Fulton–Pandharipande, Lemma 10).

## Main declarations

* `Projectivization.isZero_holomorphicSectionCechCohomology_one_pullback_map_tangentSpace`:
  `H¹(ℂℙ¹, ℓ'* TℂPᵐ⁺¹) = 0` for every line `ℓ'`.
* `Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace`:
  its case of the coordinate line `ℓ`.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10, for the regularity of lines.
-/

public section

open CategoryTheory CategoryTheory.Limits
open TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {m : ℕ}

/-- **`H¹(ℂℙ¹, ℓ'* TℂPᵐ⁺¹) = 0` for every line `ℓ'`.** Let `ℓ'` be an analytic map
`ℂℙ¹ → ℂPᵐ⁺¹` sending `[v]` to `[f v]` for an injective linear map `f : ℂ² → ℂᵐ⁺²`, a line of
`ℂPᵐ⁺¹`. The first Čech cohomology of the sheaf of holomorphic sections of the pullback
`ℓ'* TℂPᵐ⁺¹` of the tangent bundle vanishes: `ℓ'* TℂPᵐ⁺¹ ≅ 𝒪(2) ⊕ 𝒪(1)ᵐ`
(`Projectivization.exists_continuousLinearEquiv_pullback_map_tangentSpace_twistSumCore_lineTwist`),
and `H¹(ℂℙ¹, 𝒪(k)) = 0` for `k ≥ -1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_pullback_map_tangentSpace
    (f : (Fin 2 → ℂ) →ₗ[ℂ] Fin (m + 2) → ℂ) (hf : Function.Injective f)
    (ℓ' : C^ω⟮𝓘(ℂ, Fin 1 → ℂ), ℙ ℂ (Fin 2 → ℂ); 𝓘(ℂ, Fin (m + 1) → ℂ),
      ℙ ℂ (Fin (m + 2) → ℂ)⟯)
    (hℓ' : ∀ x, ℓ' x = map f hf x) :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      ((ℓ' : ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (Fin (m + 2) → ℂ)) *ᵖ
        (TangentSpace 𝓘(ℂ, Fin (m + 1) → ℂ))) 1) := by
  obtain ⟨e, he⟩ :=
    exists_continuousLinearEquiv_pullback_map_tangentSpace_twistSumCore_lineTwist f hf ℓ' hℓ'
  refine (isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le
    (k := lineTwist m) fun l ↦ ?_).of_iso
    ((Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin 2 → ℂ))) (ModuleCat.{0} ℂ) 1).mapIso
      ((sheafToPresheaf _ _).mapIso (holomorphicSectionSheaf.isoOfLinearEquiv
        (fun x ↦ (e x).toLinearEquiv) he (contMDiff_bundle_symm e he))))
  refine Fin.cases ?_ (fun l ↦ ?_) l
  · rw [lineTwist_zero]
    norm_num
  · rw [lineTwist_succ]
    norm_num

variable (m) in
/-- **`H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`.** The first Čech cohomology of the sheaf of holomorphic sections
of the pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line
`ℓ : ℂℙ¹ → ℂPᵐ⁺¹` vanishes. This is the case `ℓ' = ℓ` of
`Projectivization.isZero_holomorphicSectionCechCohomology_one_pullback_map_tangentSpace`. -/
theorem isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (CoordLineTangentSpace ℂ m) 1) :=
  isZero_holomorphicSectionCechCohomology_one_pullback_map_tangentSpace _
    (coordLineEmbedding_injective m) coordLineContMDiffMap fun x ↦ by
      induction x using Projectivization.ind with
      | h v hv => rw [coe_coordLineContMDiffMap, coordLine_mk, map_mk]

end Projectivization
