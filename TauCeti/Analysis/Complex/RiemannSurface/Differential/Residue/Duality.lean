/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.EulerCharacteristic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Pairing
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Twist
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.MittagLeffler
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus

/-!
# The injectivity half of Serre duality on a compact Riemann surface

Let `X` be a compact connected Hausdorff Riemann surface and `D` a divisor on `X`. The residue
pairing `⟨μ, ω⟩ = ∑_x Res_x(μ_x ω)` of Mittag-Leffler distributions `μ` relative to `D` with
global sections `ω` of `Ω_{-D}` (`TauCeti.RiemannSurface.PrincipalParts.residuePairing`) vanishes
on the principal parts of meromorphic functions, by the residue theorem. These are exactly the
distributions killed by the Mittag-Leffler connecting map `PrincipalParts D → H¹(X, 𝒪_D)`
(`TauCeti.RiemannSurface.exact_principalParts_mittagLefflerConnecting`). So the pairing descends
to the image of the connecting map (`TauCeti.RiemannSurface.serreDualityPairing`):

`im (PrincipalParts D → H¹(X, 𝒪_D)) × H⁰(X, Ω_{-D}) → ℂ`.

A nonzero `ω` pairs nontrivially with a principal part supported at a single point
(`TauCeti.RiemannSurface.PrincipalParts.exists_residuePairing_single_ne_zero`), so the induced map
from `H⁰(X, Ω_{-D})` to the dual of that image is injective
(`TauCeti.RiemannSurface.serreDualityMap_injective`). This is the injectivity of the Serre duality
map (Forster, Theorem 17.6), proved without the surjectivity of the connecting map (Forster,
Theorem 17.3), which is not available here. It gives `h⁰(Ω_{-D}) ≤ h¹(𝒪_D)` whenever `H¹(X, 𝒪_D)`
is finite-dimensional.

With Riemann–Roch for divisor sheaves this has two consequences when `H¹(X, 𝒪)` is
finite-dimensional:

* every canonical divisor `K` has `deg K ≤ 2 g_an - 2`, from `h⁰(K) ≤ h¹(𝒪) = g_an` and
  `1 = h⁰(𝒪) ≤ h¹(𝒪_K)`;
* comparing with the topological formula `deg K = -χ(X)`, the topological genus is at most the
  analytic genus (`TauCeti.RiemannSurface.genus_le_analyticGenus`).

Equality in both, which is the remaining content of Serre duality, needs the surjectivity of the
duality map.

## Main results

* `TauCeti.RiemannSurface.serreDualityPairing`, `serreDualityPairing_rangeRestrict`: the descended
  pairing and its value on the class of a distribution.
* `TauCeti.RiemannSurface.serreDualityMap_injective`: injectivity of the Serre duality map.
* `TauCeti.RiemannSurface.finrank_differentialSections_neg_le`: `h⁰(Ω_{-D}) ≤ h¹(𝒪_D)`.
* `TauCeti.RiemannSurface.finrank_holomorphicOneForms_le_analyticGenus`: `h⁰(Ω) ≤ g_an`.
* `TauCeti.RiemannSurface.IsCanonicalDivisor.degree_le_two_mul_analyticGenus_sub_two`:
  `deg K ≤ 2 g_an - 2`.
* `TauCeti.RiemannSurface.genus_le_analyticGenus`: the topological genus is at most `g_an`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (Theorem 17.6, injectivity of the duality map, and Theorem 17.9, Serre duality).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [T2Space X] [ConnectedSpace X]

section Duality

variable (D : WeilDivisor X)

/-- The residue pairing vanishes on Mittag-Leffler distributions killed by the connecting map:
these are principal parts of meromorphic functions, whose residues add up to zero. -/
theorem ker_mittagLefflerConnecting_le_ker_residuePairing :
    LinearMap.ker (mittagLefflerConnecting D) ≤
      LinearMap.ker (PrincipalParts.residuePairing D) := by
  intro μ hμ
  obtain ⟨f, rfl⟩ := ((exact_principalParts_mittagLefflerConnecting D) μ).1 hμ
  exact LinearMap.mem_ker.2 (LinearMap.ext fun ω ↦
    PrincipalParts.residuePairing_principalParts_eq_zero f ω)

/-- Distributions with the same image under the connecting map have the same residue pairing. -/
theorem residuePairing_eq_of_mittagLefflerConnecting_eq {μ ν : PrincipalParts D}
    (h : mittagLefflerConnecting D μ = mittagLefflerConnecting D ν) :
    PrincipalParts.residuePairing D μ = PrincipalParts.residuePairing D ν := by
  rw [← sub_eq_zero, ← map_sub]
  exact LinearMap.mem_ker.1 (ker_mittagLefflerConnecting_le_ker_residuePairing D
    (LinearMap.mem_ker.2 (by rw [map_sub, h, sub_self])))

/-- **The Serre duality pairing** on the image of the Mittag-Leffler connecting map
`PrincipalParts D → H¹(X, 𝒪_D)`: the class of a distribution `μ` pairs with `ω ∈ H⁰(X, Ω_{-D})`
by the residue pairing `⟨μ, ω⟩`, which does not depend on `μ` within its class. -/
def serreDualityPairing :
    LinearMap.range (mittagLefflerConnecting D) →ₗ[ℂ] differentialSections (-D) ⊤ →ₗ[ℂ] ℂ where
  toFun ξ := PrincipalParts.residuePairing D (LinearMap.mem_range.1 ξ.property).choose
  map_add' ξ η := by
    rw [← map_add]
    refine residuePairing_eq_of_mittagLefflerConnecting_eq D ?_
    rw [map_add, (LinearMap.mem_range.1 ξ.property).choose_spec,
      (LinearMap.mem_range.1 η.property).choose_spec,
      (LinearMap.mem_range.1 (ξ + η).property).choose_spec, Submodule.coe_add]
  map_smul' c ξ := by
    rw [RingHom.id_apply, ← map_smul]
    refine residuePairing_eq_of_mittagLefflerConnecting_eq D ?_
    rw [map_smul, (LinearMap.mem_range.1 ξ.property).choose_spec,
      (LinearMap.mem_range.1 (c • ξ).property).choose_spec, Submodule.coe_smul]

/-- The Serre duality pairing of the class of a distribution `μ` is the residue pairing of `μ`. -/
@[simp]
theorem serreDualityPairing_rangeRestrict (μ : PrincipalParts D)
    (ω : differentialSections (-D) ⊤) :
    serreDualityPairing D ((mittagLefflerConnecting D).rangeRestrict μ) ω =
      PrincipalParts.residuePairing D μ ω :=
  congrArg (· ω) (residuePairing_eq_of_mittagLefflerConnecting_eq D
    (LinearMap.mem_range.1 ((mittagLefflerConnecting D).rangeRestrict μ).property).choose_spec)

variable {D} in
/-- **A nonzero section of `Ω_{-D}` pairs nontrivially with some cohomology class**: with the class
of a principal part supported at any single point. -/
theorem exists_serreDualityPairing_ne_zero {ω : differentialSections (-D) ⊤} (hω : ω ≠ 0) :
    ∃ ξ, serreDualityPairing D ξ ω ≠ 0 := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty X)
  obtain ⟨m, hm⟩ := PrincipalParts.exists_residuePairing_single_ne_zero hω a
  exact ⟨(mittagLefflerConnecting D).rangeRestrict (DFinsupp.single a m), by
    rwa [serreDualityPairing_rangeRestrict]⟩

/-- **The Serre duality map** `H⁰(X, Ω_{-D}) → (im (PrincipalParts D → H¹(X, 𝒪_D)))^*`, sending
`ω` to the functional `ξ ↦ ⟨ξ, ω⟩`. -/
def serreDualityMap :
    differentialSections (-D) ⊤ →ₗ[ℂ] Module.Dual ℂ (LinearMap.range (mittagLefflerConnecting D)) :=
  (serreDualityPairing D).flip

@[simp]
theorem serreDualityMap_apply (ω : differentialSections (-D) ⊤)
    (ξ : LinearMap.range (mittagLefflerConnecting D)) :
    serreDualityMap D ω ξ = serreDualityPairing D ξ ω :=
  (rfl)

/-- **Injectivity of the Serre duality map** (Forster, Theorem 17.6). -/
theorem serreDualityMap_injective : Function.Injective (serreDualityMap D) := by
  refine (injective_iff_map_eq_zero _).2 fun ω hω ↦ by_contra fun hω₀ ↦ ?_
  obtain ⟨ξ, hξ⟩ := exists_serreDualityPairing_ne_zero hω₀
  exact hξ (by rw [← serreDualityMap_apply, hω, LinearMap.zero_apply])

/-- **`h⁰(Ω_{-D}) ≤ h¹(𝒪_D)`.** When `H¹(X, 𝒪_D)` is finite-dimensional, the injectivity of the
Serre duality map bounds the dimension of `H⁰(X, Ω_{-D})` by that of `H¹(X, 𝒪_D)`. -/
theorem finrank_differentialSections_neg_le [FiniteDimensional ℂ (divisorCechCohomology D 1)] :
    Module.finrank ℂ (differentialSections (-D) ⊤) ≤
      Module.finrank ℂ (divisorCechCohomology D 1) :=
  (LinearMap.finrank_le_finrank_of_injective (serreDualityMap_injective D)).trans
    (Subspace.dual_finrank_eq.le.trans (Submodule.finrank_le _))

end Duality

omit [T2Space X] [ConnectedSpace X] in
/-- On a compact Riemann surface, the sections of `Ω_D` have the dimension of the global sections
of `𝒪_(D + K)` for every canonical divisor `K`. -/
theorem IsCanonicalDivisor.finrank_differentialSections_eq {K : WeilDivisor X}
    (hK : IsCanonicalDivisor K) (D : WeilDivisor X) :
    Module.finrank ℂ (differentialSections D ⊤) =
      Module.finrank ℂ ((divisorSheaf (D + K)).obj.obj (op ⊤)) := by
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK.exists_divisor_eq
  exact (differentialSheafSectionsEquiv D ⊤).finrank_eq.symm.trans
    (((sheafToPresheaf _ _).mapIso (differentialSheafIsoDivisorSheafAdd ω hω hω₀ D)).app
      (op ⊤)).toLinearEquiv.finrank_eq

section AnalyticGenus

variable [FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
  (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)]

/-- **`h⁰(Ω) ≤ g_an`.** On a compact connected Riemann surface with finite-dimensional
`H¹(X, 𝒪)`, the holomorphic `1`-forms have dimension at most the analytic genus. -/
theorem finrank_holomorphicOneForms_le_analyticGenus :
    Module.finrank ℂ (holomorphicOneForms X) ≤ analyticGenus X := by
  have h := finrank_differentialSections_neg_le (0 : WeilDivisor X)
  rw [neg_zero, differentialSectionsZeroEquiv.finrank_eq] at h
  rwa [analyticGenus_eq_finrank_divisorCechCohomology]

/-- **`deg K ≤ 2 g_an - 2`.** On a compact connected Riemann surface with finite-dimensional
`H¹(X, 𝒪)`, every canonical divisor `K` has degree at most `2 g_an - 2`. -/
theorem IsCanonicalDivisor.degree_le_two_mul_analyticGenus_sub_two {K : WeilDivisor X}
    (hK : IsCanonicalDivisor K) : WeilDivisor.degree K ≤ 2 * analyticGenus X - 2 := by
  -- `h⁰(K) = h⁰(Ω) ≤ h¹(𝒪) = g_an` and `1 = h⁰(𝒪) = h⁰(Ω_{-K}) ≤ h¹(𝒪_K)`.
  have h₀ := finrank_differentialSections_neg_le (0 : WeilDivisor X)
  rw [neg_zero, hK.finrank_differentialSections_eq, zero_add,
    ← analyticGenus_eq_finrank_divisorCechCohomology] at h₀
  have h₁ := finrank_differentialSections_neg_le K
  rw [hK.finrank_differentialSections_eq, neg_add_cancel, finrank_divisorSheaf_zero] at h₁
  have hRR := finrank_divisorSheaf_euler_characteristic K
  omega

/-- **The topological genus is at most the analytic genus.** On a compact connected Riemann
surface with finite-dimensional `H¹(X, 𝒪)`, `genus X ≤ g_an`, from `deg K = -χ(X)` and
`deg K ≤ 2 g_an - 2` for a canonical divisor `K`. -/
theorem genus_le_analyticGenus : genus X ≤ analyticGenus X := by
  obtain ⟨F, -⟩ := exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one (X := X)
  obtain ⟨K, hK, hdeg⟩ :=
    F.exists_isCanonicalDivisor_degree_eq_neg_two_mul_degree_add_ramificationDegree
  have hle := hK.degree_le_two_mul_analyticGenus_sub_two
  rw [hdeg, F.neg_two_mul_degree_add_ramificationDegree_eq_neg_eulerChar] at hle
  rw [genus_def]
  omega

end AnalyticGenus

end TauCeti.RiemannSurface
