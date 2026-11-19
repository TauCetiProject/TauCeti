/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sphere.Basic
import TauCeti.Topology.Sheaves.Cech.Functoriality

/-!
# Riemann surfaces of analytic genus zero are the Riemann sphere

A compact connected Riemann surface `X` whose holomorphic structure sheaf has finite-dimensional
first Čech cohomology has analytic genus `g_an = dim H¹(X, 𝒪)` equal to `0` exactly when it is
biholomorphic to the Riemann sphere `OnePoint ℂ`
(`TauCeti.RiemannSurface.analyticGenus_eq_zero_iff_nonempty_diffeomorph_onePoint`).

* **Genus zero gives the sphere.** For a point `p`, Riemann–Roch for divisor sheaves
  (`TauCeti.RiemannSurface.degree_add_one_sub_analyticGenus_le_finrank_divisorSheaf`) gives
  `h⁰(𝒪(p)) ≥ deg p + 1 - g_an = 2`. So `𝒪(p)` has a section which is not constant: a
  meromorphic function with at most a simple pole at `p` and holomorphic elsewhere. As a finite
  holomorphic map to the sphere it has degree one
  (`TauCeti.RiemannSurface.exists_finiteHolomorphicMap_degree_eq_one_of_analyticGenus_eq_zero`),
  hence is a biholomorphism (`TauCeti.RiemannSurface.biholomorphOfDegreeEqOne`).
* **The sphere has genus zero.** The analytic genus is invariant under biholomorphisms
  (`Diffeomorph.analyticGenus_eq`): precomposition with a biholomorphism `φ : X ≃ Y` identifies
  the structure sheaf of `Y` with the pushforward of that of `X`
  (`TauCeti.holomorphicStructureSheafModules.isIso_homOfContMDiff`), and Čech cohomology pulls
  back along it onto that of `X` (`TopCat.Hom.epi_cechCohomologyPullback`). Applied to `φ` and
  to `φ.symm`, this gives surjections in both directions between `H¹(X, 𝒪)` and `H¹(Y, 𝒪)`, so
  their dimensions agree, whether or not they are finite. On the sphere `H¹(𝒪) = 0`
  (`TauCeti.RiemannSurface.analyticGenus_onePoint`).

The biholomorphism to the sphere can be normalized at three distinct marked points, which it then
sends to `0`, `1` and `∞` in exactly one way (`Diffeomorph.existsUnique_apply_eq_zero_one_infty`).

The finiteness of `H¹(X, 𝒪)` is an analytic theorem which is not proved in this library; as in
`TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch` it is an explicit instance
argument. The comparison of the analytic genus with the topological genus
`TauCeti.RiemannSurface.genus` is not made here.

## Main results

* `Diffeomorph.analyticGenus_eq`: biholomorphic Riemann surfaces have the same analytic genus.
* `TauCeti.RiemannSurface.analyticGenus_onePoint`: the Riemann sphere has analytic genus `0`.
* `TauCeti.RiemannSurface.analyticGenus_eq_zero_iff_nonempty_diffeomorph_onePoint`: a compact
  connected Riemann surface with finite-dimensional `H¹(X, 𝒪)` has analytic genus `0` exactly when
  it is biholomorphic to the Riemann sphere.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer, 1981, §16 (a compact Riemann
  surface of genus zero is biholomorphic to the Riemann sphere, by the Riemann–Roch theorem) and
  Theorem 13.5 (`H¹(ℙ¹, 𝒪) = 0`).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold ContDiff

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  {n : WithTop ℕ∞}

namespace TauCeti.RiemannSurface

/-- Precomposition with a biholomorphism `φ : X ≃ Y` maps the first Čech cohomology of the
structure sheaf of `Y` onto that of `X`. -/
private theorem exists_surjective_cechCohomology_one (φ : X ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y) (hn : n ≠ 0) :
    ∃ e : (cechCohomology (TopCat.of Y) (ModuleCat.{0} ℂ) 1).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) Y).obj →ₗ[ℂ]
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj, Function.Surjective e := by
  have hφ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ := (φ.contMDiff.mdifferentiable hn).contMDiff
  have hφ' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ.symm := (φ.symm.contMDiff.mdifferentiable hn).contMDiff
  have := holomorphicStructureSheafModules.isIso_homOfContMDiff 𝓘(ℂ) X φ hφ φ.symm hφ'
    φ.symm_apply_apply φ.apply_symm_apply
  have hepi := TopCat.Hom.epi_cechCohomologyPullback (TopCat.ofHom ⟨φ, hφ.continuous⟩) 1
    (holomorphicStructureSheafModules.homOfContMDiff 𝓘(ℂ) X φ hφ) φ.toHomeomorph.isInducing
    φ.surjective
  exact ⟨_, (ModuleCat.epi_iff_surjective _).1 hepi⟩

end TauCeti.RiemannSurface

open TauCeti TauCeti.RiemannSurface in
/-- **The analytic genus is a biholomorphism invariant.** Biholomorphic Riemann surfaces have
first Čech cohomology of their structure sheaves of the same dimension. -/
theorem Diffeomorph.analyticGenus_eq (φ : X ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y) (hn : n ≠ 0) :
    analyticGenus X = analyticGenus Y := by
  obtain ⟨e₁, he₁⟩ := exists_surjective_cechCohomology_one φ hn
  obtain ⟨e₂, he₂⟩ := exists_surjective_cechCohomology_one φ.symm hn
  rw [analyticGenus_def, analyticGenus_def]
  by_cases hX : FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
    (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)
  · have := Module.Finite.of_surjective e₂ he₂
    exact le_antisymm (LinearMap.finrank_le_finrank_of_surjective he₁)
      (LinearMap.finrank_le_finrank_of_surjective he₂)
  · have hY := fun h : FiniteDimensional ℂ ((cechCohomology (TopCat.of Y) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) Y).obj) ↦ hX (Module.Finite.of_surjective e₁ he₁)
    rw [Module.finrank_of_not_finite hX, Module.finrank_of_not_finite hY]

namespace TauCeti.RiemannSurface

/-- **The Riemann sphere has analytic genus zero**, since `H¹(ℙ¹, 𝒪) = 0`. -/
@[simp]
theorem analyticGenus_onePoint : analyticGenus (OnePoint ℂ) = 0 :=
  analyticGenus_eq_finrank_divisorCechCohomology.trans finrank_divisorCechCohomology_zero_one_sphere

variable [CompactSpace X] [T2Space X] [ConnectedSpace X]
  [FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
  (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)]

/-- **Riemann surfaces of genus zero are the Riemann sphere.** A compact connected Riemann surface
with finite-dimensional `H¹(X, 𝒪)` has analytic genus `0` exactly when it is biholomorphic to the
Riemann sphere `OnePoint ℂ`. -/
theorem analyticGenus_eq_zero_iff_nonempty_diffeomorph_onePoint :
    analyticGenus X = 0 ↔ Nonempty (X ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ) := by
  refine ⟨fun h ↦ ?_, fun ⟨φ⟩ ↦ (φ.analyticGenus_eq (by simp)).trans analyticGenus_onePoint⟩
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_degree_eq_one_of_analyticGenus_eq_zero h
  exact ⟨biholomorphOfDegreeEqOne F hF⟩

end TauCeti.RiemannSurface
