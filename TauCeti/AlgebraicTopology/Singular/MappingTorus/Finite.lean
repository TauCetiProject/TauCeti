/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType

/-!
# Finitely generated homology of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus, with singular homology taken with
coefficients in a module `M` over a noetherian ring `k`. The Wang sequence

  `Hₙ₊₁(F; M) ⟶ Hₙ₊₁(T_φ; M) ⟶ Hₙ(F; M)`,

with maps the fibre inclusion and the Wang connecting morphism, is exact
(`TauCeti.MappingTorus.wang_exact₃`), and the fibre inclusion is onto on `H₀`. So if the homology
of `F` is finitely generated in degrees `n + 1` and `n`, that of `T_φ` is finitely generated in
degree `n + 1`: it is an extension of a submodule of `Hₙ(F; M)` by a quotient of `Hₙ₊₁(F; M)`
(`TauCeti.MappingTorus.finite_singularHomology_succ`).

In particular the mapping torus of a self-homeomorphism of a space of finite CW type, such as a
compact manifold (`TauCeti.FiniteCWType.of_isManifold`), has finitely generated homology in every
degree with finitely generated coefficients (`TauCeti.MappingTorus.finite_singularHomology`). For
`k = ℤ`, every subgroup of its second homology is then finitely generated: this applies to the
group of classes swept out by loops of sections of the mapping torus, the deck group of the covering
spaces of Floer theory for a symplectomorphism.

## Main results

* `TauCeti.MappingTorus.finite_singularHomology_zero`,
  `TauCeti.MappingTorus.finite_singularHomology_succ`: finite generation of `H₀(T_φ; M)` and
  `Hₙ₊₁(T_φ; M)` from that of the homology of the fibre.
* `TauCeti.MappingTorus.finite_singularHomology`: the mapping torus of a self-homeomorphism of a
  space of finite CW type has finitely generated homology.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, Example 2.48,
  the Wang sequence of a mapping torus.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomologicalComplex

universe w

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F) {k : Type w} [Ring k]
  [IsNoetherianRing k] (M : ModuleCat.{w} k)

omit [IsNoetherianRing k] in
/-- **The degree-zero homology of a mapping torus is finitely generated** when that of the fibre is:
the fibre inclusion is onto on `H₀`. -/
theorem finite_singularHomology_zero
    [Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) 0).obj M).obj (TopCat.of F))] :
    Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{w} k) 0).obj M).obj (TopCat.of (MappingTorus φ))) :=
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex, on
  -- which the Wang sequence is stated.
  have : Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj M).obj
      (TopCat.of F)).homology 0) := ‹_›
  Module.Finite.of_surjective (homologyMap (fibreInclusionChainMap φ M) 0).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- **Finite generation of the homology of a mapping torus through the Wang sequence.** If
`Hₙ₊₁(F; M)` and `Hₙ(F; M)` are finitely generated, so is `Hₙ₊₁(T_φ; M)`: the image of the fibre
in it is a quotient of `Hₙ₊₁(F; M)`, and the quotient by that image embeds in `Hₙ(F; M)` through the
Wang connecting morphism. -/
theorem finite_singularHomology_succ (n : ℕ)
    [Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{w} k) (n + 1)).obj M).obj (TopCat.of F))]
    [Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) n).obj M).obj (TopCat.of F))] :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) (n + 1)).obj M).obj
      (TopCat.of (MappingTorus φ))) :=
  -- `singularHomologyFunctor` is by definition the homology of the singular chain complex, on
  -- which the Wang sequence is stated.
  have : Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj M).obj
      (TopCat.of F)).homology (n + 1)) := ‹_›
  have : Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj M).obj
      (TopCat.of F)).homology n) := ‹_›
  have := isNoetherian_of_range_eq_ker (homologyMap (fibreInclusionChainMap φ M) (n + 1)).hom
    (wangδ φ M n).hom (wang_exact₃ φ M n).moduleCat_range_eq_ker
  (inferInstance : Module.Finite k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj M).obj
    (TopCat.of (MappingTorus φ))).homology (n + 1)))

/-- **The mapping torus of a self-homeomorphism of a space of finite CW type has finitely generated
homology**, in every degree, with finitely generated coefficients over a noetherian ring. This
applies to a compact manifold `F` (`TauCeti.FiniteCWType.of_isManifold`). -/
theorem finite_singularHomology [FiniteCWType F] [Module.Finite k M] (n : ℕ) :
    Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{w} k) n).obj M).obj (TopCat.of (MappingTorus φ))) := by
  have (m : ℕ) := TauCeti.finite_singularHomology_of_finiteCWType F M m
  cases n with
  | zero => exact finite_singularHomology_zero φ M
  | succ n => exact finite_singularHomology_succ φ M n

end TauCeti.MappingTorus
