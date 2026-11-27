/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Cohomology
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Tangent.Basic

/-!
# The first cohomology of `ℓ* TℂPᵐ⁺¹` on the complex projective line

The pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle along the coordinate line `ℓ : ℂℙ¹ → ℂPᵐ⁺¹` is
`𝒪(2) ⊕ 𝒪(1)ᵐ` (`Projectivization.coordLineTangentDiffeomorph`), so the sheaves of holomorphic
sections agree (`Projectivization.coordLineTangentSectionIso`). Since `H¹(ℂℙ¹, 𝒪(k)) = 0` for
`k ≥ -1`, this gives `H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace`). This is
the cohomological vanishing behind the regularity of the lines of `ℂPⁿ` as holomorphic spheres
(Fulton–Pandharipande, Lemma 10); identifying `H¹(ℂℙ¹, u* TℂPⁿ)` with the cokernel of the
linearized Cauchy–Riemann operator along `u` is not done here.

## Main declarations

* `Projectivization.coordLineTangentSectionIso`: the sheaf of holomorphic sections of
  `ℓ* TℂPᵐ⁺¹` is that of `𝒪(2) ⊕ 𝒪(1)ᵐ`.
* `Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace`:
  `H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10, for the regularity of lines.
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §29.
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable (m : ℕ)

/-- The sheaf of holomorphic sections of the pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle along the
coordinate line `ℓ` is isomorphic to the sheaf of holomorphic sections of `𝒪(2) ⊕ 𝒪(1)ᵐ`, by the
fibrewise isomorphisms `Projectivization.coordLineTangentEquiv`. -/
def coordLineTangentSectionIso :
    holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ) (CoordLineTangentSpace ℂ m) ≅
      holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := 1) (lineTwist m)).Fiber :=
  holomorphicSectionSheaf.isoOfLinearEquiv (fun x ↦ (coordLineTangentEquiv x).toLinearEquiv)
    contMDiff_coordLineTangentEquiv <|
      (coordLineTangentDiffeomorph (𝕜 := ℂ) (m := m) ω).symm.contMDiff.congr fun q ↦
        (coordLineTangentDiffeomorph_symm_apply ω q).symm

@[simp]
theorem coordLineTangentSectionIso_hom_app_apply
    {U : (Opens (TopCat.of (ℙ ℂ (Fin 2 → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (CoordLineTangentSpace ℂ m)).obj.obj U) (x : ↥(unop U)) :
    (coordLineTangentSectionIso m).hom.hom.app U s x = coordLineTangentEquiv x (s x) :=
  holomorphicSectionSheaf.isoOfLinearEquiv_hom_app_apply _ _ _ s x

@[simp]
theorem coordLineTangentSectionIso_inv_app_apply
    {U : (Opens (TopCat.of (ℙ ℂ (Fin 2 → ℂ))))ᵒᵖ}
    (s : (holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (twistSumCore (𝕜 := ℂ) (n := 1) (lineTwist m)).Fiber).obj.obj U) (x : ↥(unop U)) :
    (coordLineTangentSectionIso m).inv.hom.app U s x = (coordLineTangentEquiv x).symm (s x) :=
  holomorphicSectionSheaf.isoOfLinearEquiv_inv_app_apply _ _ _ s x

/-- **`H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`.** The first Čech cohomology of the sheaf of holomorphic sections
of the pullback of the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line `ℓ` vanishes, since
`ℓ* TℂPᵐ⁺¹ ≅ 𝒪(2) ⊕ 𝒪(1)ᵐ` and `H¹(ℂℙ¹, 𝒪(k)) = 0` for `k ≥ -1`. -/
theorem isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (CoordLineTangentSpace ℂ m) 1) := by
  refine (isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le (lineTwist m)
    fun l ↦ ?_).of_iso
    ((Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin 2 → ℂ))) (ModuleCat.{0} ℂ) 1).mapIso
      ((sheafToPresheaf _ _).mapIso (coordLineTangentSectionIso m)))
  cases l using Fin.cases <;> simp

end Projectivization
