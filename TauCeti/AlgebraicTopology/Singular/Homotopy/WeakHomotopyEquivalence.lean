/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Retraction
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Comparison.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Compression
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance

/-!
# Weak homotopy equivalences induce isomorphisms on singular homology

A weak homotopy equivalence `f : X → Y` induces a quasi-isomorphism of normalized cubical singular
chains, and hence isomorphisms `H_n(X; R) ≅ H_n(Y; R)` on singular homology with coefficients in
any ring `R` (Hatcher, *Algebraic Topology*, Proposition 4.21). No CW structure on `X` or `Y` is
needed.

The proof factors `f` through its mapping cylinder `M_f` as

  `X ≃ₜ (bottom face of M_f) ↪ M_f → Y`.

* The first map is a homeomorphism (`TauCeti.MappingCylinder.inclHomeomorph`).
* The last map, the projection, is a homotopy equivalence
  (`TauCeti.MappingCylinder.homotopyEquiv`), so it induces a chain homotopy equivalence of
  cubical chains.
* For the inclusion of the bottom face, every point of `M_f` is joined by a path to the bottom
  face, and the relative homotopy sets of the pair vanish because `f` is a weak homotopy
  equivalence
  (`ContinuousMap.IsWeakHomotopyEquivalence.subsingleton_relHomotopyGroup_mappingCylinder`). So
  the singular cubes of `M_f` deform into the bottom face, and the inclusion induces a chain
  homotopy equivalence of cubical chains
  (`TauCeti.isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup` and the cubical statement
  behind it).

The singular homology statement is then read off through the comparison of cubical and simplicial
singular chains.

The same factorization proves the statement with local coefficients: for a local coefficient
system `L` on `Y`, the map `H_n(X; f⁎L) ⟶ H_n(Y; L)` is an isomorphism. The bottom face of the
mapping cylinder is handled by the compression of cubical chains with local coefficients
(`TauCeti.quasiIso_normalizedTwistedCubicalChainComplexMap_subtypeVal_of_relHomotopyGroup`),
transported to simplicial chains through the comparison
`TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap`, which is natural in the space. The
other two factors are homotopy equivalences, which induce isomorphisms on homology with local
coefficients by homotopy invariance (`ContinuousMap.HomotopyEquiv.isIso_twistedHomologyMap`).

## Main results

* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_normalizedCubicalChainComplex_map`: a weak
  homotopy equivalence induces a quasi-isomorphism of normalized cubical chains.
* `ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularHomologyMap`: a weak homotopy
  equivalence induces isomorphisms on singular homology.
* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_twistedChainComplexMap`,
  `ContinuousMap.IsWeakHomotopyEquivalence.isIso_twistedHomologyMap`: the same with local
  coefficients.
* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_normalizedTwistedCubicalChainComplexMap`: the
  cubical form with local coefficients.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.21, and Section 3.H for homology with local coefficients.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti

universe u v

namespace ContinuousMap.IsWeakHomotopyEquivalence

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
  (k : Type u) [Ring k]

/-- **A weak homotopy equivalence induces a quasi-isomorphism of normalized cubical singular
chains.** -/
theorem quasiIso_normalizedCubicalChainComplex_map (hf : f.IsWeakHomotopyEquivalence) :
    QuasiIso ((normalizedCubicalChainComplex k).map (TopCat.ofHom f)) := by
  open MappingCylinder in
  let A : Set (TopCat.of (MappingCylinder f)) := Set.range (incl f)
  let ψ : X ≃ₜ A := inclHomeomorph f
  -- The three factors induce quasi-isomorphisms. The singular cubes of the mapping cylinder
  -- deform into the bottom face, and the other two factors are homotopy equivalences, whose
  -- forward maps are `ψ` (by definition) and `proj f`.
  have D := (nonempty_subspaceCubeDeformation_of_relHomotopyGroup
    (X := TopCat.of (MappingCylinder f)) (A := A) (n := ⊤)
    (exists_mem_range_incl_joined hf.exists_joined)
    fun k _ ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder (Fin k)).some
  have := D.quasiIso_normalizedCubicalChainComplex_map k
  have : QuasiIso ((normalizedCubicalChainComplex k).map (TopCat.ofHom (ψ : C(X, A)))) :=
    ψ.toHomotopyEquiv.quasiIso_normalizedCubicalChainComplex_map
  have : QuasiIso ((normalizedCubicalChainComplex k).map (TopCat.ofHom (proj f))) := by
    rw [← MappingCylinder.homotopyEquiv_toFun]
    exact (MappingCylinder.homotopyEquiv f).quasiIso_normalizedCubicalChainComplex_map
  -- `f` is the bottom face `X ≃ₜ A`, followed by the inclusion of `A` and the projection.
  rw [← proj_comp_subtypeVal_comp_inclHomeomorph (f := f), TopCat.ofHom_comp, TopCat.ofHom_comp,
    Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **A weak homotopy equivalence induces isomorphisms on singular homology** with coefficients in
any ring (Hatcher, Proposition 4.21). -/
theorem isIso_singularHomologyMap (hf : f.IsWeakHomotopyEquivalence) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      (TopCat.ofHom f)) := by
  have := hf.quasiIso_normalizedCubicalChainComplex_map k
  exact TopCat.isIso_singularHomologyMap_of_quasiIso _ n

end ContinuousMap.IsWeakHomotopyEquivalence

/-! ### Local coefficients -/

namespace ContinuousMap.IsWeakHomotopyEquivalence

open LocalCoefficientSystem

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
  {R : Type u} [Ring R]

/-- **A weak homotopy equivalence induces a quasi-isomorphism of singular chains with local
coefficients**: for every local coefficient system `L` on `Y`, the map of singular chain complexes
from `X` with coefficients in `f⁎L` to `Y` with coefficients in `L` is a quasi-isomorphism. -/
theorem quasiIso_twistedChainComplexMap (hf : f.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) :
    QuasiIso (twistedChainComplexMap (TopCat.ofHom f) L) := by
  let A : Set (TopCat.of (MappingCylinder f)) := Set.range (MappingCylinder.incl f)
  let ψ : X ≃ₜ A := MappingCylinder.inclHomeomorph f
  let i : TopCat.of A ⟶ TopCat.of (MappingCylinder f) := TopCat.ofHom (ContinuousMap.subtypeVal A)
  let p := TopCat.ofHom (MappingCylinder.homotopyEquiv f).toFun
  -- The singular cubes of the mapping cylinder deform into the bottom face, so its inclusion
  -- induces a quasi-isomorphism of cubical chains with local coefficients, and hence, through the
  -- comparison of cubical and simplicial chains, of singular chains.
  have : QuasiIso (twistedChainComplexMap i ((pullback p.hom).obj L)) := by
    have : QuasiIso (normalizedTwistedCubicalChainComplexMap i.hom ((pullback p.hom).obj L)) :=
      quasiIso_normalizedTwistedCubicalChainComplexMap_subtypeVal_of_relHomotopyGroup
        (MappingCylinder.exists_mem_range_incl_joined hf.exists_joined)
        (fun n ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder (Fin n)) _
    have h := twistedCubicalToSingularMap_naturality i ((pullback p.hom).obj L)
    have : QuasiIso (normalizedTwistedCubicalChainComplexMap i.hom ((pullback p.hom).obj L) ≫
        twistedCubicalToSingularMap ((pullback p.hom).obj L)) := inferInstance
    rw [h] at this
    exact quasiIso_of_comp_left (twistedCubicalToSingularMap _) _
  -- The other two factors of `f`, the bottom face `X ≃ₜ A` and the projection, are homotopy
  -- equivalences.
  have : QuasiIso (twistedChainComplexMap (TopCat.ofHom ψ.toHomotopyEquiv.toFun)
      ((pullback (i ≫ p).hom).obj L)) :=
    ψ.toHomotopyEquiv.quasiIso_twistedChainComplexMap _
  have : QuasiIso (twistedChainComplexMap p L) :=
    (MappingCylinder.homotopyEquiv f).quasiIso_twistedChainComplexMap L
  have hf' : TopCat.ofHom f = TopCat.ofHom ψ.toHomotopyEquiv.toFun ≫ i ≫ p := by
    ext x
    simp only [ψ, i, p, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
      ContinuousMap.subtypeVal_apply, MappingCylinder.homotopyEquiv_apply]
    exact (congrArg (· x) (MappingCylinder.proj_comp_subtypeVal_comp_inclHomeomorph (f := f))).symm
  rw [twistedChainComplexMap_congr _ _ hf', twistedChainComplexMap_comp,
    twistedChainComplexMap_comp]
  infer_instance

/-- **A weak homotopy equivalence induces isomorphisms on singular homology with local
coefficients**, the local-coefficient form of Hatcher, Proposition 4.21: for every local
coefficient system `L` on `Y`, the map `H_n(X; f⁎L) ⟶ H_n(Y; L)` is an isomorphism. -/
theorem isIso_twistedHomologyMap (hf : f.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) (n : ℕ) :
    IsIso (twistedHomologyMap (TopCat.ofHom f) L n) :=
  have := hf.quasiIso_twistedChainComplexMap L
  inferInstance

/-- **A weak homotopy equivalence induces a quasi-isomorphism of normalized cubical chains with
local coefficients.** -/
theorem quasiIso_normalizedTwistedCubicalChainComplexMap (hf : f.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) :
    QuasiIso (normalizedTwistedCubicalChainComplexMap (X := TopCat.of X) f L) := by
  have := hf.quasiIso_twistedChainComplexMap L
  have : QuasiIso (twistedCubicalToSingularMap ((pullback (TopCat.ofHom f).hom).obj L) ≫
      twistedChainComplexMap (TopCat.ofHom f) L) := inferInstance
  rw [← twistedCubicalToSingularMap_naturality] at this
  exact quasiIso_of_comp_right _ (twistedCubicalToSingularMap L)

end ContinuousMap.IsWeakHomotopyEquivalence
