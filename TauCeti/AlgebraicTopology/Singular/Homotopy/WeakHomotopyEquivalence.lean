/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Retraction

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

## Main results

* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_normalizedCubicalChainComplex_map`: a weak
  homotopy equivalence induces a quasi-isomorphism of normalized cubical chains.
* `ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularHomologyMap`: a weak homotopy
  equivalence induces isomorphisms on singular homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.21.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti

universe u

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
