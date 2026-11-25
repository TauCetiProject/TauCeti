/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.RingTheory.Grassmannian.Chart.Plucker
public import TauCeti.RingTheory.Grassmannian.Plucker
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The Plücker morphism of the Grassmannian scheme

Let `M` be a module over a commutative ring `R` and `k` a natural number. This file constructs the
**Plücker morphism** `G(k, M) ⟶ G(1, ⋀ᵏ M)` over `Spec R` between the Grassmannian schemes
`Module.Grassmannian.scheme R M k` and `Module.Grassmannian.scheme R (⋀[R]^k M) 1`, the latter
the projective bundle `P(⋀ᵏ M)` of rank-one quotients. On points over an `R`-algebra `A` it sends
the point classifying `N ⊆ A ⊗[R] M` to the point classifying the kernel of
`⋀ᵏ_A (A ⊗[R] M) → ⋀ᵏ_A ((A ⊗[R] M) ⧸ N)`, read in `A ⊗[R] ⋀ᵏ M`
(`Module.Grassmannian.pluckerBaseChange`): the universal exterior-power quotient
`⋀ᵏ (A ⊗[R] M) → ⋀ᵏ Q = det Q`, where `Q = (A ⊗[R] M) ⧸ N` is the universal quotient.

The point map is natural in `A` (`Module.Grassmannian.pluckerBaseChange_map`), so it is composition
with a morphism of schemes (`Module.Grassmannian.homOfPoints`).

On the chart of `G(k, M)` at `x : Fin k → M`, the Plücker morphism is `Spec` of the Plücker map on
charts `Module.Grassmannian.ChartAlgebra.pluckerChartHom R x` followed by the chart of
`G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`; since that ring map is surjective, `Spec` of it is a closed
immersion.

## Main definitions

* `Module.Grassmannian.pluckerHom R M k`: the Plücker morphism `G(k, M) ⟶ G(1, ⋀ᵏ M)`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_pluckerHom`: the characterisation of `pluckerHom` on
  points.
* `Module.Grassmannian.pluckerHom_toSpec`: `pluckerHom` lies over `Spec R`.
* `Module.Grassmannian.specMap_pluckerChartHom_chartι`: `pluckerHom` on the standard charts.
* `Module.Grassmannian.isClosedImmersion_specMap_pluckerChartHom`: on the standard charts,
  `pluckerHom` is `Spec` of a surjective ring map, hence a closed immersion.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  the Grassmannian and its Plücker embedding.
* U. Görtz, T. Wedhorn, *Algebraic Geometry I* (Vieweg+Teubner, 2010), Chapter 8, for the
  standard charts of the Grassmannian and the Plücker embedding.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

-- the naturality of the point map of `pluckerHom`
private lemma toSchemeHom_pluckerBaseChange_map (S T : Type u) [CommRing S] [Algebra R S]
    [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (N : G(k, S ⊗[R] M; S)) :
    toSchemeHom (pluckerBaseChange (map f N)) =
      Spec.map (CommRingCat.ofHom (f : S →+* T)) ≫ toSchemeHom (pluckerBaseChange N) := by
  rw [pluckerBaseChange_map, toSchemeHom_map]

variable (R M k) in
/-- **The Plücker morphism** `G(k, M) ⟶ G(1, ⋀ᵏ M)` over `Spec R`: it sends the point classifying
`N ⊆ A ⊗[R] M` over an `R`-algebra `A` to the point classifying the kernel of
`⋀ᵏ (A ⊗[R] M) → ⋀ᵏ ((A ⊗[R] M) ⧸ N)`, read in `A ⊗[R] ⋀ᵏ M`
(`Module.Grassmannian.toSchemeHom_comp_pluckerHom`). -/
noncomputable def pluckerHom : scheme R M k ⟶ scheme R (⋀[R]^k M) 1 :=
  homOfPoints (fun _ _ _ N ↦ toSchemeHom (pluckerBaseChange N)) toSchemeHom_pluckerBaseChange_map

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **`pluckerHom` on points.** The morphism classifying `N` over an `R`-algebra `A`, composed with
`pluckerHom`, classifies the Plücker point of `N`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_pluckerHom (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ pluckerHom R M k = toSchemeHom (pluckerBaseChange N) :=
  toSchemeHom_comp_homOfPoints _ toSchemeHom_pluckerBaseChange_map N

variable (R M k) in
/-- `pluckerHom` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem pluckerHom_toSpec : pluckerHom R M k ≫ toSpec R (⋀[R]^k M) 1 = toSpec R M k := by
  refine scheme_hom_ext fun A _ _ N ↦ ?_
  rw [toSchemeHom_comp_pluckerHom_assoc, toSchemeHom_toSpec, toSchemeHom_toSpec]

open ChartAlgebra

variable (R) in
/-- **The Plücker morphism on charts.** On the chart of `G(k, M)` at `x`, the Plücker morphism is
`Spec` of `pluckerChartHom R x` followed by the chart of `G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`. -/
@[reassoc]
theorem specMap_pluckerChartHom_chartι (x : Fin k → M) :
    Spec.map (CommRingCat.ofHom (pluckerChartHom R x :
        ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →+* ChartAlgebra R x)) ≫
      chartι R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) =
    chartι R x ≫ pluckerHom R M k := by
  rw [← toSchemeHom_chartHomEquiv_id x, toSchemeHom_comp_pluckerHom,
    pluckerBaseChange_chartHomEquiv_id, ← toSchemeHom_chartHomEquiv_id, ← toSchemeHom_map,
    ← chartHomEquiv_comp, AlgHom.comp_id]

variable (R) in
/-- `Spec` of the Plücker map on charts is a closed immersion. -/
theorem isClosedImmersion_specMap_pluckerChartHom (x : Fin k → M) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (pluckerChartHom R x :
      ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →+* ChartAlgebra R x))) :=
  IsClosedImmersion.spec_of_surjective _ (pluckerChartHom_surjective R x)

end Module.Grassmannian
