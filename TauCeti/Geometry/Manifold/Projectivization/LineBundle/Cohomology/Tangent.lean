/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Cohomology.Sum
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle.Tangent

/-!
# The first cohomology of the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line vanishes

Let `ℓ : ℂℙ¹ → ℂℙᵐ⁺¹` be the coordinate line `[v₀ : v₁] ↦ [v₀ : v₁ : 0 : ⋯ : 0]`
(`Projectivization.coordLine`). The pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle
(`Projectivization.CoordLineTangentSpace`) is holomorphically the split bundle `𝒪(2) ⊕ 𝒪(1)ᵐ`
(`Projectivization.coordLineTangentDiffeomorph`), so the sheaves of holomorphic sections of the two
bundles are isomorphic (`Projectivization.coordLineTangentSectionIso`), and so are their Čech
cohomologies in every degree (`Projectivization.coordLineTangentCechCohomologyIso`). All the
twists `2, 1, …, 1` are at least `-1`, so the first Čech cohomology of the split bundle vanishes
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le`), and
hence `H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`
(`Projectivization.isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace`).

The group `H¹(ℂℙ¹, u* TX)` is the cokernel of the linearized Cauchy–Riemann operator of a
holomorphic sphere `u` in a complex manifold `X` with its integrable complex structure, so its
vanishing says that the coordinate line is a regular holomorphic sphere in `ℂPᵐ⁺¹`. That
identification of the cokernel is not made here.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, Lemma 10 (the vanishing of `H¹(C, μ* T_X)` for genus-zero maps to convex
  targets such as `ℙʳ`).
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §5.
-/

public noncomputable section

open Bundle CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable (m : ℕ)

/-- The sheaf of holomorphic sections of the pullback `ℓ* TℂPᵐ⁺¹` of the tangent bundle along the
coordinate line is isomorphic to the sheaf of holomorphic sections of `𝒪(2) ⊕ 𝒪(1)ᵐ`, by the
fibrewise isomorphisms `Projectivization.coordLineTangentEquiv`. -/
def coordLineTangentSectionIso :
    holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ) (CoordLineTangentSpace ℂ m) ≅
      holomorphicSectionSheaf 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := 1) (lineTwist m)).Fiber :=
  holomorphicSectionSheaf.isoOfLinearEquiv (fun x ↦ (coordLineTangentEquiv x).toLinearEquiv)
    contMDiff_coordLineTangentEquiv <|
      (coordLineTangentDiffeomorph (𝕜 := ℂ) (m := m) ω).symm.contMDiff.congr fun q ↦
        (coordLineTangentDiffeomorph_symm_apply (m := m) ω q).symm

variable {m}

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

variable (m)

/-- **`Hᵖ(ℂℙ¹, ℓ* TℂPᵐ⁺¹) ≅ Hᵖ(ℂℙ¹, 𝒪(2) ⊕ 𝒪(1)ᵐ)`.** The Čech cohomology of the pullback of
the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line is that of the split bundle
`𝒪(2) ⊕ 𝒪(1)ᵐ`, in every degree: the image of `Projectivization.coordLineTangentSectionIso`. -/
def coordLineTangentCechCohomologyIso (p : ℕ) :
    holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
        (CoordLineTangentSpace ℂ m) p ≅
      holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
        (twistSumCore (𝕜 := ℂ) (n := 1) (lineTwist m)).Fiber p :=
  (Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin 2 → ℂ))) (ModuleCat.{0} ℂ) p).mapIso
    ((sheafToPresheaf _ _).mapIso (coordLineTangentSectionIso m))

@[simp]
theorem coordLineTangentCechCohomologyIso_hom (p : ℕ) :
    (coordLineTangentCechCohomologyIso m p).hom =
      (Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin 2 → ℂ))) (ModuleCat.{0} ℂ) p).map
        (coordLineTangentSectionIso m).hom.hom :=
  (rfl)

@[simp]
theorem coordLineTangentCechCohomologyIso_inv (p : ℕ) :
    (coordLineTangentCechCohomologyIso m p).inv =
      (Topology.cechCohomology (TopCat.of (ℙ ℂ (Fin 2 → ℂ))) (ModuleCat.{0} ℂ) p).map
        (coordLineTangentSectionIso m).inv.hom :=
  (rfl)

/-- **`H¹(ℂℙ¹, ℓ* TℂPᵐ⁺¹) = 0`.** The first Čech cohomology of the sheaf of holomorphic sections of
the pullback of the tangent bundle of `ℂPᵐ⁺¹` along the coordinate line vanishes. -/
theorem isZero_holomorphicSectionCechCohomology_one_coordLineTangentSpace :
    IsZero (holomorphicSectionCechCohomology 𝓘(ℂ, Fin 1 → ℂ) (Fin (m + 1) → ℂ)
      (CoordLineTangentSpace ℂ m) 1) :=
  (isZero_holomorphicSectionCechCohomology_one_twistSumCore_of_neg_one_le
    (Fin.cases (by simp) fun _ ↦ by simp)).of_iso (coordLineTangentCechCohomologyIso m 1)

end Projectivization
