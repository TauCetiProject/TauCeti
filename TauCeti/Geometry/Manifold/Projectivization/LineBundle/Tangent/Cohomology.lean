/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Sum.Cohomology
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Tangent

/-!
# The first cohomology of the tangent bundle of `ℂℙᵐ⁺¹` along a line

Let `ℓ : ℂℙ¹ → ℂℙᵐ⁺¹` be the coordinate line `[v₀ : v₁] ↦ [v₀ : v₁ : 0 : ⋯ : 0]`
(`Projectivization.coordLine`). Its pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle splits
holomorphically as `𝒪(2) ⊕ 𝒪(1)ᵐ` (`Projectivization.coordLineTangentDiffeomorph`). This file
carries the splitting to the sheaves of holomorphic sections
(`Projectivization.coordLineTangentSheafIso`) and concludes that the first Čech cohomology
`H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹)` vanishes
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace`), since
`H¹(ℂℙ¹, 𝒪(k)) = 0` for `k = 2` and `k = 1`.

The first cohomology of `u* TX` is the cokernel of the linearized Cauchy–Riemann operator at a
holomorphic sphere `u` for an integrable complex structure, so its vanishing says that the line
`ℓ` is a regular holomorphic sphere in `ℂℙᵐ⁺¹`, the input to the regularity of the moduli space of
lines (Fulton–Pandharipande, Lemma 10).

## Main declarations

* `Projectivization.coordLineTangentSheafIso m`: the sheaf of holomorphic sections of
  `ℓ* TℂPᵐ⁺¹` is isomorphic to that of `𝒪(2) ⊕ 𝒪(1)ᵐ`.
* `Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace m`:
  `H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, AMS Colloquium
  Publications 52, Section 3.3 (regularity of holomorphic spheres for integrable structures).
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable (m : ℕ)

/-- **The sheaf of holomorphic sections of `ℓ* TℂPᵐ⁺¹` is that of `𝒪(2) ⊕ 𝒪(1)ᵐ`.** The isomorphism
of sheaves of holomorphic sections on `ℂℙ¹` induced by the holomorphic splitting
`Projectivization.coordLineTangentEquiv` of the tangent bundle of `ℂℙᵐ⁺¹` along the coordinate line
`ℓ`. -/
def coordLineTangentSheafIso :
    holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ) (CoordLineTangentSpace ℂ m) ≅
      holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := 1) (lineTwist m)).Fiber :=
  holomorphicSectionSheaf.isoOfLinearEquiv (fun x ↦ (coordLineTangentEquiv x).toLinearEquiv)
    contMDiff_coordLineTangentEquiv
    ((coordLineTangentDiffeomorph (𝕜 := ℂ) (m := m) ω).symm.contMDiff.congr fun q ↦
      (coordLineTangentDiffeomorph_symm_apply ω q).symm)

variable {m}

/-- The isomorphism takes a section of `ℓ* TℂPᵐ⁺¹` to its image under the fibrewise splitting. -/
@[simp]
theorem coordLineTangentSheafIso_hom_app_apply {U : (Opens (TopCat.of (ℙ ℂ (Fin 2 → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (CoordLineTangentSpace ℂ m)).obj.obj U) (x : ↥(unop U)) :
    (coordLineTangentSheafIso m).hom.hom.app U s x = coordLineTangentEquiv x (s x) :=
  holomorphicSectionSheaf.isoOfLinearEquiv_hom_app_apply _ _ _ s x

/-- The inverse isomorphism takes a section of `𝒪(2) ⊕ 𝒪(1)ᵐ` to its image under the inverse of the
fibrewise splitting. -/
@[simp]
theorem coordLineTangentSheafIso_inv_app_apply {U : (Opens (TopCat.of (ℙ ℂ (Fin 2 → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := 1) (lineTwist m)).Fiber).obj.obj U) (x : ↥(unop U)) :
    (coordLineTangentSheafIso m).inv.hom.app U s x = (coordLineTangentEquiv x).symm (s x) :=
  holomorphicSectionSheaf.isoOfLinearEquiv_inv_app_apply _ _ _ s x

variable (m)

/-- **`H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`.** The first Čech cohomology of the sheaf of holomorphic sections of
the pullback of the tangent bundle of `ℂℙᵐ⁺¹` along the coordinate line `ℓ` vanishes: the bundle is
`𝒪(2) ⊕ 𝒪(1)ᵐ`, and `H¹(ℂℙ¹, 𝒪(k)) = 0` for `k ≥ -1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (CoordLineTangentSpace ℂ m) 1) :=
  (isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le fun l ↦ by
      cases l using Fin.cases <;> simp).of_iso
    ((Topology.cechCohomology _ _ 1).mapIso ((sheafToPresheaf _ _).mapIso
      (coordLineTangentSheafIso m)))

end Projectivization
