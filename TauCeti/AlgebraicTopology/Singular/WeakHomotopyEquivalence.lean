/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Retraction
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Weak homotopy equivalences induce isomorphisms on singular homology

A weak homotopy equivalence `f : X → Y` induces a quasi-isomorphism of normalized cubical singular
chains and isomorphisms `H_n(X; R) ≅ H_n(Y; R)` on singular homology with coefficients in any ring
`R` (Hatcher, *Algebraic Topology*, Proposition 4.21, with constant coefficients).

The map `f` factors as the homeomorphism of `X` with the bottom face of its mapping cylinder `M_f`,
the inclusion of that face into `M_f`, and the projection `M_f → Y`. The projection is a homotopy
equivalence. Every point of `M_f` is joined by a path to the bottom face, and the relative homotopy
sets of `M_f` relative to the bottom face vanish
(`ContinuousMap.IsWeakHomotopyEquivalence.subsingleton_relHomotopyGroup_mappingCylinder`). So the
singular cubes of `M_f` deform into the bottom face, and its inclusion induces a chain homotopy
equivalence of normalized cubical chains
(`TauCeti.SubspaceCubeDeformation.quasiIso_normalizedCubicalChainComplex_map`). Homotopy
invariance handles the other two factors.

## Main results

* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_normalizedCubicalChainComplex_map`: a weak
  homotopy equivalence induces a quasi-isomorphism of normalized cubical chains.
* `ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularHomologyMap`: a weak homotopy equivalence
  induces isomorphisms on singular homology with coefficients in any ring.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.21, whose proof through the mapping cylinder and the deformation of
  singular chains into a subspace is the one followed here.
-/

public section

open CategoryTheory AlgebraicTopology Set TauCeti TauCeti.MappingCylinder

universe u

namespace ContinuousMap.IsWeakHomotopyEquivalence

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}

/-- The factorization of `f` through its mapping cylinder: the homeomorphism of `X` with the bottom
face, the inclusion of the bottom face, and the projection, each written as the forward map of the
equivalence that the corresponding invariance result is stated for. -/
private theorem ofHom_eq_comp_mappingCylinder :
    TopCat.ofHom f =
      TopCat.ofHom (inclHomeomorph f).toHomotopyEquiv.toFun ≫
        TopCat.ofHom (ContinuousMap.subtypeVal (range (incl f))) ≫
          TopCat.ofHom (MappingCylinder.homotopyEquiv f).toFun := by
  have hproj : (MappingCylinder.homotopyEquiv f).toFun = proj f :=
    ContinuousMap.ext homotopyEquiv_apply
  ext x
  simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
    Homeomorph.toHomotopyEquiv, hproj, ContinuousMap.subtypeVal_apply, ContinuousMap.coe_ofClass,
    inclHomeomorph_apply_coe]
  rw [← ContinuousMap.comp_apply (proj f), proj_comp_incl]

/-- The bottom face of the mapping cylinder of a weak homotopy equivalence is compressible: the
singular cubes of the mapping cylinder deform coherently into it. -/
private theorem nonempty_subspaceCubeDeformation_mappingCylinder
    (hf : f.IsWeakHomotopyEquivalence) :
    Nonempty (SubspaceCubeDeformation (X := TopCat.of (MappingCylinder f)) (range (incl f))) :=
  nonempty_subspaceCubeDeformation_of_relHomotopyGroup
    (exists_mem_range_incl_joined hf.exists_joined)
    (fun n b ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder (Fin n) b)

/-- **A weak homotopy equivalence induces a quasi-isomorphism of normalized cubical chains**, with
coefficients in any ring. -/
theorem quasiIso_normalizedCubicalChainComplex_map (hf : f.IsWeakHomotopyEquivalence)
    (k : Type u) [Ring k] :
    QuasiIso ((normalizedCubicalChainComplex k).map (TopCat.ofHom f)) := by
  obtain ⟨D⟩ := hf.nonempty_subspaceCubeDeformation_mappingCylinder
  have := D.quasiIso_normalizedCubicalChainComplex_map k
  have := (inclHomeomorph f).toHomotopyEquiv.quasiIso_normalizedCubicalChainComplex_map (k := k)
  have := (MappingCylinder.homotopyEquiv f).quasiIso_normalizedCubicalChainComplex_map (k := k)
  rw [ofHom_eq_comp_mappingCylinder, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **A weak homotopy equivalence induces isomorphisms on singular homology** `H_n(X; R) ≅
H_n(Y; R)` in every degree, with coefficients in any ring `R` (Hatcher, Proposition 4.21). -/
theorem isIso_singularHomologyMap (hf : f.IsWeakHomotopyEquivalence) (R : Type u) [Ring R]
    (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (TopCat.ofHom f)) := by
  obtain ⟨D⟩ := hf.nonempty_subspaceCubeDeformation_mappingCylinder
  have := D.isIso_singularHomologyMap R n
  have h₁ := ((inclHomeomorph f).toHomotopyEquiv.singularHomologyIso (ModuleCat.of R R) n).isIso_hom
  have h₂ := ((MappingCylinder.homotopyEquiv f).singularHomologyIso (ModuleCat.of R R) n).isIso_hom
  rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom] at h₁ h₂
  rw [ofHom_eq_comp_mappingCylinder, Functor.map_comp, Functor.map_comp]
  infer_instance

end ContinuousMap.IsWeakHomotopyEquivalence
