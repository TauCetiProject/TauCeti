/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.EulerCharacteristic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch
public import TauCeti.Analysis.Complex.RiemannSurface.Genus
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic

/-!
# A finite map to the sphere and the degree of the canonical divisor

Let `X` be a compact connected Riemann surface with `H¹(X, 𝒪)` finite-dimensional, of dimension
the analytic genus `g`.
Riemann–Roch for the divisor `(g + 1) · x` of a point gives at least two independent global
sections, and a non-constant one is a finite holomorphic map `X → ℙ¹` of degree at most `g + 1`
(`TauCeti.RiemannSurface.exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one`). This is
Forster's construction of a finite meromorphic map from Riemann–Roch.

Pulling back the canonical divisor `-2[∞]` of the sphere along such a map produces a canonical
divisor of `X` (`TauCeti.RiemannSurface.exists_isCanonicalDivisor`). The same map discharges the
existence hypothesis of the comparison with the Euler characteristic: when `X` has finite CW type,
every canonical divisor has degree `-χ(X)`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_eulerChar_of_finiteDimensional`).

In analytic genus zero the divisor of a single point already has two sections, giving a
finite map `X → ℙ¹` of degree one
(`TauCeti.RiemannSurface.exists_finiteHolomorphicMap_degree_eq_one_of_analyticGenus_eq_zero`).
A degree-one map is unramified
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.ramificationDegree_eq_zero_of_degree_eq_one`), so
the topological Riemann–Hurwitz formula over the sphere gives `χ(X) = 2` and topological genus
`0` (`TauCeti.RiemannSurface.eulerChar_eq_two_of_analyticGenus_eq_zero`,
`TauCeti.RiemannSurface.genus_eq_zero_of_analyticGenus_eq_zero`).

Identifying `deg K = 2g - 2` for the analytic genus needs Serre duality and is not done here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16 (existence of meromorphic functions from Riemann–Roch) and §17 (the canonical divisor and the
  Riemann–Hurwitz formula).
-/

public section

open CategoryTheory Opposite OnePoint TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry

namespace FiniteHolomorphicMap

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  [T2Space Y]

/-- **A degree-one map is unramified.** Every local multiplicity of a finite holomorphic map from
a compact Riemann surface is at most its degree, so for degree one there is no ramification. -/
theorem ramificationDegree_eq_zero_of_degree_eq_one {f : FiniteHolomorphicMap X Y}
    (hf : degree f = 1) : ramificationDegree f = 0 := by
  rw [ramificationDegree_def]
  exact finsum_eq_zero_of_forall_eq_zero fun x ↦
    Nat.sub_eq_zero_of_le (hf ▸ localMultiplicity_le_degree f x)

end FiniteHolomorphicMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
  [FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
    (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)]

/-- Riemann–Roch for an effective divisor of degree greater than the analytic genus gives a
finite holomorphic map to the sphere whose poles are bounded by the divisor. -/
private theorem exists_finiteHolomorphicMap_of_analyticGenus_lt_degree {D : WeilDivisor X}
    (hD : (analyticGenus X : ℤ) < WeilDivisor.degree D) :
    ∃ F : FiniteHolomorphicMap X (OnePoint ℂ),
      ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun y ↦ OnePoint.affineChart (F y)) x := by
  refine exists_finiteHolomorphicMap_of_one_lt_finrank_divisorSections D ?_
  have h := degree_add_one_sub_analyticGenus_le_finrank_divisorSheaf D
  rw [(divisorSheafSectionsEquiv D ⊤).finrank_eq] at h
  omega

/-- **A finite map to the sphere from Riemann–Roch.** A compact connected Riemann surface with
finite-dimensional `H¹(X, 𝒪)` admits a finite holomorphic map to `ℙ¹` of degree at most
`g_an + 1`: Riemann–Roch gives two independent sections of `𝒪((g_an + 1) · x)` for any point
`x`. -/
theorem exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one :
    ∃ F : FiniteHolomorphicMap X (OnePoint ℂ), degree F ≤ analyticGenus X + 1 := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := X)
  have hdeg : WeilDivisor.degree ((analyticGenus X + 1) • WeilDivisor.ofPoint x) =
      analyticGenus X + 1 := by
    simp [map_nsmul, WeilDivisor.degree_ofPoint]
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_of_analyticGenus_lt_degree
    (D := (analyticGenus X + 1) • WeilDivisor.ofPoint x) (by omega)
  refine ⟨F, ?_⟩
  have := F.degree_le_degree_of_neg_le_meromorphicOrderAt
    (nsmul_nonneg (WeilDivisor.ofPoint_nonneg x) _) hF
  rw [hdeg] at this
  omega

/-- **Existence of a canonical divisor.** A compact connected Riemann surface with
finite-dimensional `H¹(X, 𝒪)` has a canonical divisor: pull back `-2[∞]` along a finite map to
`ℙ¹` constructed by Riemann–Roch and add its ramification divisor. -/
theorem exists_isCanonicalDivisor : ∃ K : WeilDivisor X, IsCanonicalDivisor K := by
  obtain ⟨F, -⟩ := exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one (X := X)
  obtain ⟨K, hK, -⟩ :=
    F.exists_isCanonicalDivisor_degree_eq_neg_two_mul_degree_add_ramificationDegree
  exact ⟨K, hK⟩

/-- **The degree of a canonical divisor is minus the Euler characteristic.** On a compact
connected Riemann surface of finite CW type with finite-dimensional `H¹(X, 𝒪)`, every canonical
divisor `K` has `deg K = -χ(X)`. The finite map to `ℙ¹` needed for the comparison is constructed by
Riemann–Roch. -/
theorem IsCanonicalDivisor.degree_eq_neg_eulerChar_of_finiteDimensional [FiniteCWType X]
    {K : WeilDivisor X} (hK : IsCanonicalDivisor K) : WeilDivisor.degree K = -eulerChar X := by
  obtain ⟨F, -⟩ := exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one (X := X)
  exact hK.degree_eq_neg_eulerChar F

/-- **Analytic genus zero gives a degree-one map to the sphere.** If `H¹(X, 𝒪) = 0` on a compact
connected Riemann surface, Riemann–Roch gives two independent sections of `𝒪(x)` for a point `x`,
hence a finite holomorphic map `X → ℙ¹` of degree one. -/
theorem exists_finiteHolomorphicMap_degree_eq_one_of_analyticGenus_eq_zero
    (h : analyticGenus X = 0) : ∃ F : FiniteHolomorphicMap X (OnePoint ℂ), degree F = 1 := by
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one (X := X)
  have := degree_pos F
  exact ⟨F, by omega⟩

/-- **Analytic genus zero gives Euler characteristic two.** A compact connected Riemann surface
of finite CW type with `H¹(X, 𝒪) = 0` has `χ(X) = 2`: a degree-one map to `ℙ¹` is unramified, so
the topological Riemann–Hurwitz formula gives `χ(X) = 2 · 1 - 0`. -/
theorem eulerChar_eq_two_of_analyticGenus_eq_zero [FiniteCWType X] (h : analyticGenus X = 0) :
    eulerChar X = 2 := by
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_degree_eq_one_of_analyticGenus_eq_zero h
  rw [F.eulerChar_eq_two_mul_degree_sub_ramificationDegree, hF,
    F.ramificationDegree_eq_zero_of_degree_eq_one hF]
  norm_num

/-- **Analytic genus zero gives topological genus zero**, for a compact connected Riemann surface
of finite CW type. -/
theorem genus_eq_zero_of_analyticGenus_eq_zero [FiniteCWType X] (h : analyticGenus X = 0) :
    genus X = 0 :=
  genus_eq_of_eulerChar_eq (by rw [eulerChar_eq_two_of_analyticGenus_eq_zero h]; norm_num)

end TauCeti.RiemannSurface
