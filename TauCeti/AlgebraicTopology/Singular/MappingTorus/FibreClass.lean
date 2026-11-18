/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The fibre class of a mapping torus and its dual class

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus, with singular homology and
cohomology taken with coefficients in a commutative ring `k`. The Wang sequence

  `Hₙ₊₁(F) ⟶ Hₙ₊₁(F) ⟶ Hₙ₊₁(T_φ) ⟶ Hₙ(F) ⟶ Hₙ(F)`,

with maps `𝟙 - φ_*`, the fibre inclusion `i_*` and the Wang connecting morphism, shows that if
`φ_*` is the identity on `Hₙ₊₁(F)` and `𝟙 - φ_*` is injective on `Hₙ(F)`, the fibre inclusion is an
isomorphism `Hₙ₊₁(F) ≅ Hₙ₊₁(T_φ)` (`bijective_homologyMap_fibreInclusionChainMap`): its kernel is
the image of `𝟙 - φ_* = 0`, and the connecting morphism vanishes because its composite with the
injective map `𝟙 - φ_*` does. The same sequence shows that `Hₙ₊₁(T_φ)` is finitely generated when
`Hₙ₊₁(F)` and `Hₙ(F)` are, over a noetherian ring (`finite_homology_succ`).

Now let `k` be a principal ideal domain and suppose `Hₙ₊₂(F)` is free of rank one on a class `σ`
fixed by `φ_*`, that `𝟙 - φ_*` is injective on `Hₙ₊₁(F)`, and that `Hₙ₊₁(F)` and `Hₙ(F)` are
finitely generated. Then `Hₙ₊₂(T_φ)` is free of rank one on the fibre class `i_* σ`. By the
universal coefficient theorem there is a class `v ∈ Hⁿ⁺²(T_φ; k)` with `⟨v, i_* σ⟩ = 1`, and the
classes of `Hⁿ⁺²(T_φ; k)` pairing to zero with `i_* σ` are exactly the torsion classes, because the
`Ext` term `Ext¹(Hₙ₊₁(T_φ), k)` of a finitely generated module is torsion
(`TopCat.singularKronecker_eq_zero_iff_mem_torsion`). Hence every `x ∈ Hⁿ⁺²(T_φ; k)` is
`⟨x, i_* σ⟩ v` up to torsion (`exists_singularKronecker_apply_eq_one_and_sub_mem_torsion`), and
`v` is determined by `⟨v, i_* σ⟩ = 1` up to torsion.

The case `n = 0` is the second cohomology of a surface mapping torus. Let `F` be a closed connected
oriented surface with fundamental class `[F]`, `φ` an orientation-preserving homeomorphism, and
suppose `φ_*` has no eigenvalue one on `H₁(F; ℤ)`, that is `det (1 - φ_*) ≠ 0`. For the free module
`H₁(F; ℤ)` this is the injectivity of `1 - φ_*`, and with rational coefficients it is the condition
`b₁(T_φ) = 1` (`TauCeti.MappingTorus.finrank_homology_one_eq_one_iff`). Then
`H₂(T_φ; ℤ) = ℤ i_*[F]`, there is a lift `v ∈ H²(T_φ; ℤ)` with `⟨v, [F]⟩ = 1`, and
`H²(T_φ; ℤ) = ℤ v ⊕ torsion` (`exists_singularKronecker_apply_eq_one_and_sub_mem_torsion_two`), with
all torsion labels retained. Over `ℤ`, membership in the torsion submodule is having finite
additive order (`Submodule.torsion_int`). Together with the decomposition of the second cohomology
of a product with a circle (`TopCat.singularCohomologySphereProdSlantEquiv`), this is the basis
`v, [ds ∧ dt]` modulo torsion in which the Seiberg–Witten line labels of `S¹ × T_φ` are written.

## Main results

* `TauCeti.MappingTorus.bijective_homologyMap_fibreInclusionChainMap`: the fibre inclusion is an
  isomorphism `Hₙ₊₁(F) ≅ Hₙ₊₁(T_φ)` when `φ_* = 𝟙` on `Hₙ₊₁(F)` and `𝟙 - φ_*` is injective on
  `Hₙ(F)`.
* `TauCeti.MappingTorus.finite_homology_succ`: `Hₙ₊₁(T_φ)` is finitely generated when `Hₙ₊₁(F)`
  and `Hₙ(F)` are, over a noetherian ring.
* `TauCeti.MappingTorus.mem_torsion_iff_singularKronecker_apply_eq_zero`: a class of
  `Hⁿ⁺²(T_φ; k)` is torsion exactly when it pairs to zero with the fibre class.
* `TauCeti.MappingTorus.exists_singularKronecker_apply_eq_one_and_sub_mem_torsion`: there is a
  class `v` with `⟨v, i_* σ⟩ = 1`, and `x - ⟨x, i_* σ⟩ v` is torsion for every class `x`.
* `TauCeti.MappingTorus.exists_singularKronecker_apply_eq_one_and_sub_mem_torsion_two`: the case
  `n = 0`, for a path-connected fibre.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence, and
  Section 3.1, Theorem 3.2, for the universal coefficient theorem.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w

namespace TauCeti.MappingTorus

section CommRing

variable {k : Type w} [CommRing k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The fibre inclusion of a mapping torus is an isomorphism** `Hₙ₊₁(F) ≅ Hₙ₊₁(T_φ)` when the
monodromy is the identity on `Hₙ₊₁(F)` and `𝟙 - φ_*` is injective on `Hₙ(F)`. -/
theorem bijective_homologyMap_fibreInclusionChainMap (n : ℕ)
    (hφ : (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom = LinearMap.id)
    (hinj : LinearMap.ker
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom) = ⊥) :
    Function.Bijective (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom := by
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, ker_homologyMap_fibreInclusionChainMap, hφ, sub_self,
      LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, range_homologyMap_fibreInclusionChainMap, LinearMap.ker_eq_top]
    refine LinearMap.ext fun y ↦ LinearMap.ker_eq_bot.1 hinj ?_
    have := congrArg (fun f ↦ f.hom y)
      (wangδ_comp_homologyMap_wangEndomorphism φ (ModuleCat.of k k) n)
    simpa [homologyMap_wangEndomorphism] using this

/-- **Finite generation of the homology of a mapping torus**: over a noetherian ring, `Hₙ₊₁(T_φ)`
is finitely generated when `Hₙ₊₁(F)` and `Hₙ(F)` are. -/
instance finite_homology_succ [IsNoetherianRing k] (n : ℕ)
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))]
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology n)] :
    Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (wangδ φ (ModuleCat.of k k) n).hom
    (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, ← range_homologyMap_fibreInclusionChainMap, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

end CommRing

section PrincipalIdealDomain

variable {k : Type w} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k] {F : Type w}
  [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The torsion classes of `Hⁿ⁺²(T_φ)` are those pairing to zero with the fibre class**: over a
principal ideal domain, if `Hₙ₊₂(F)` is generated by a class `σ` fixed by `φ_*`, `𝟙 - φ_*` is
injective on `Hₙ₊₁(F)`, and `Hₙ₊₁(T_φ)` is finitely generated (for instance because `Hₙ₊₁(F)` and
`Hₙ(F)` are, `finite_homology_succ`), a class `x ∈ Hⁿ⁺²(T_φ; k)` is torsion exactly when
`⟨x, i_* σ⟩ = 0`. -/
theorem mem_torsion_iff_singularKronecker_apply_eq_zero (n : ℕ)
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1))]
    (hinj : LinearMap.ker
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom) = ⊥)
    {σ : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 2)}
    (hσ : Function.Surjective (LinearMap.toSpanSingleton k _ σ))
    (hφσ : (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 2)).hom σ = σ)
    (x : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) (n + 2)) :
    x ∈ Submodule.torsion k ((TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
      (ModuleCat.of k k) (n + 2)) ↔
      ((TopCat.of (MappingTorus φ)).singularKronecker k (n + 2) x).hom
        ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 2)).hom σ) = 0 := by
  have : Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) (n + 1)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))) := ‹_›
  rw [← TopCat.singularKronecker_eq_zero_iff_mem_torsion]
  refine ⟨fun h ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  -- The fibre class generates `Hₙ₊₂(T_φ)`, since the fibre inclusion is onto.
  have hφ : (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 2)).hom = LinearMap.id := by
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨c, rfl⟩ := hσ y
    simp [hφσ]
  ext y
  obtain ⟨z, rfl⟩ := (bijective_homologyMap_fibreInclusionChainMap φ (n + 1) hφ hinj).2 y
  obtain ⟨c, rfl⟩ := hσ z
  simp only [LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero]
  exact ((LinearMap.map_smul _ c _).trans (congrArg (c • ·) h)).trans (smul_zero c)

/-- **The dual of the fibre class of a mapping torus**: over a principal ideal domain, if
`Hₙ₊₂(F)` is free of rank one on a class `σ` fixed by `φ_*`, `𝟙 - φ_*` is injective on `Hₙ₊₁(F)`,
and `Hₙ₊₁(T_φ)` is finitely generated (for instance because `Hₙ₊₁(F)` and `Hₙ(F)` are,
`finite_homology_succ`), there is a class `v ∈ Hⁿ⁺²(T_φ; k)` with `⟨v, i_* σ⟩ = 1`, and every
`x ∈ Hⁿ⁺²(T_φ; k)` agrees with `⟨x, i_* σ⟩ v` up to torsion. -/
theorem exists_singularKronecker_apply_eq_one_and_sub_mem_torsion (n : ℕ)
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1))]
    (hinj : LinearMap.ker
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom) = ⊥)
    {σ : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 2)}
    (hσ : Function.Bijective (LinearMap.toSpanSingleton k _ σ))
    (hφσ : (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 2)).hom σ = σ) :
    ∃ v : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
        (ModuleCat.of k k) (n + 2),
      ((TopCat.of (MappingTorus φ)).singularKronecker k (n + 2) v).hom
          ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 2)).hom σ) = 1 ∧
        ∀ x : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
            (ModuleCat.of k k) (n + 2),
          x - ((TopCat.of (MappingTorus φ)).singularKronecker k (n + 2) x).hom
            ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 2)).hom σ) • v ∈
          Submodule.torsion k ((TopCat.of (MappingTorus φ)).singularCohomology
            (ModuleCat.of k k) k (ModuleCat.of k k) (n + 2)) := by
  have hφ : (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 2)).hom = LinearMap.id := by
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨c, rfl⟩ := hσ.2 y
    simp [hφσ]
  -- `Hₙ₊₂(T_φ)` is free of rank one on the fibre class `i_* σ`; `g` is its coordinate.
  let e := LinearEquiv.ofBijective
    ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 2)).hom ∘ₗ
      LinearMap.toSpanSingleton k _ σ)
    ((bijective_homologyMap_fibreInclusionChainMap φ (n + 1) hφ hinj).comp hσ)
  let g : ((singularHomologyFunctor (ModuleCat.{w} k) (n + 2)).obj (ModuleCat.of k k)).obj
      (TopCat.of (MappingTorus φ)) ⟶ ModuleCat.of k k := ModuleCat.ofHom e.symm.toLinearMap
  obtain ⟨v, hv⟩ := (TopCat.of (MappingTorus φ)).singularKronecker_surjective (ModuleCat.of k k)
    (ModuleCat.of k k) (n + 2) g
  have he : e 1 = (homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 2)).hom σ := by
    simp [e]
  have hgσ : g.hom ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 2)).hom σ) =
      1 :=
    (congrArg g.hom he.symm).trans (e.symm_apply_apply 1)
  refine ⟨v, by rw [hv, hgσ], fun x ↦ ?_⟩
  refine (mem_torsion_iff_singularKronecker_apply_eq_zero φ n hinj hσ.2 hφσ _).2 ?_
  -- `⟨x - c v, i_* σ⟩ = c - c ⟨v, i_* σ⟩ = 0` for `c = ⟨x, i_* σ⟩`.
  simp only [map_sub, map_smul, ModuleCat.hom_sub, ModuleCat.hom_smul, hv]
  refine (LinearMap.sub_apply _ _ _).trans (sub_eq_zero.2 (Eq.symm ?_))
  refine (LinearMap.smul_apply _ _ _).trans ?_
  rw [hgσ, smul_eq_mul, mul_one]

/-- **The second cohomology of a surface mapping torus**: over a principal ideal domain, for a
path-connected fibre `F` with `H₁(F)` finitely generated, `𝟙 - φ_*` injective on `H₁(F)`, and
`H₂(F)` free of rank one on a class `σ` fixed by `φ_*`, there is a class `v ∈ H²(T_φ; k)` with
`⟨v, i_* σ⟩ = 1`, and every `x ∈ H²(T_φ; k)` agrees with `⟨x, i_* σ⟩ v` up to torsion. For a closed
connected oriented surface, an orientation-preserving `φ` and `k = ℤ`, this is the lift
`v ∈ H²(T_φ; ℤ)` with `⟨v, [F]⟩ = 1` spanning `H²(T_φ; ℤ)` modulo torsion when `b₁(T_φ) = 1`. -/
theorem exists_singularKronecker_apply_eq_one_and_sub_mem_torsion_two [PathConnectedSpace F]
    [Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 1)]
    (hinj : LinearMap.ker
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 1).hom) = ⊥)
    {σ : (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 2}
    (hσ : Function.Bijective (LinearMap.toSpanSingleton k _ σ))
    (hφσ : (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) 2).hom σ = σ) :
    ∃ v : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
        (ModuleCat.of k k) 2,
      ((TopCat.of (MappingTorus φ)).singularKronecker k 2 v).hom
          ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) 2).hom σ) = 1 ∧
        ∀ x : (TopCat.of (MappingTorus φ)).singularCohomology (ModuleCat.of k k) k
            (ModuleCat.of k k) 2,
          x - ((TopCat.of (MappingTorus φ)).singularKronecker k 2 x).hom
            ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) 2).hom σ) • v ∈
          Submodule.torsion k ((TopCat.of (MappingTorus φ)).singularCohomology
            (ModuleCat.of k k) k (ModuleCat.of k k) 2) := by
  -- `H₀(F; k) ≅ k` through the augmentation, since `F` is path-connected.
  have : Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology 0) :=
    Module.Finite.equiv
      (asIso ((TopCat.of F).singularHomology₀ε (ModuleCat.of k k))).toLinearEquiv.symm
  exact exists_singularKronecker_apply_eq_one_and_sub_mem_torsion φ 0 hinj hσ hφσ

end PrincipalIdealDomain

end TauCeti.MappingTorus
