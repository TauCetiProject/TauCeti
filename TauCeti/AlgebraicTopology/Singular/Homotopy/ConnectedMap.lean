/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
public import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Relative
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# `n`-connected maps and singular homology

An `n`-connected map `f : X → Y` (`ContinuousMap.IsNConnected`) induces isomorphisms
`H_m(X; R) ≅ H_m(Y; R)` on singular homology for every `m < n`, and a surjection in degree `n`,
for every coefficient ring `R`. This is the range version of the fact that a weak homotopy
equivalence induces isomorphisms on homology
(`ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularHomologyMap`), which is the case of maps
that are `n`-connected for every `n`. No CW structure on `X` or `Y` is needed.

The proof factors `f` through its mapping cylinder `M_f` as

  `X ≃ₜ (bottom face of M_f) ↪ M_f → Y`.

The first map is a homeomorphism and the last a homotopy equivalence, so both induce isomorphisms
on homology. For the middle one, the relative homotopy groups `π_{k+1}(M_f, X)` vanish for
`k < n` (`ContinuousMap.IsNConnected.subsingleton_relHomotopyGroup_mappingCylinder`), so the
singular cubes of `M_f` deform into the bottom face below dimension `n + 1` and the relative
homology `H_m(M_f, X; R)` vanishes for `m ≤ n`
(`ContinuousMap.IsNConnected.isZero_singularHomology_mappingCylinder`). The long exact sequence of
the pair gives the stated range.

For the inclusion of the `n`-skeleton of a relative CW complex, which is `n`-connected
(`TauCeti.isNConnected_inclusion_skeletonLT`), this gives surjectivity on homology in degree `n`.
The isomorphisms below degree `n` are the classical statement that the skeleton carries the
homology of the complex (Hatcher, Lemma 2.34(c)), already available as
`TauCeti.isIso_homologyMap_skeletonBasePairToComplex_fst`.

## Main results

* `ContinuousMap.IsNConnected.isZero_singularHomology_mappingCylinder`: the relative homology of
  the mapping cylinder of an `n`-connected map, relative to its bottom face, vanishes up to
  degree `n`.
* `ContinuousMap.IsNConnected.isIso_singularHomologyMap`: an `n`-connected map induces
  isomorphisms on singular homology below degree `n`.
* `ContinuousMap.IsNConnected.epi_singularHomologyMap`: an `n`-connected map induces surjections
  on singular homology up to degree `n`.
* `TauCeti.epi_singularHomologyMap_inclusion_skeletonLT`: the inclusion of the `n`-skeleton of a
  relative CW complex induces surjections on singular homology up to degree `n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34, and Section 4.1, Proposition 4.21 and its proof.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Section 9.5.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u

namespace ContinuousMap.IsNConnected

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {n : ℕ}
  (R : Type u) [Ring R]

/-- The relative homotopy groups `π_(k+1)(M_f, X)` of the mapping cylinder of an `n`-connected
map vanish for `k < n`, in the form taken by the compression lemmas. -/
private theorem subsingleton_relHomotopyGroup_mappingCylinder_fin (hf : f.IsNConnected n)
    (k : ℕ) (hk : k + 1 < n + 1) (b : Set.range (MappingCylinder.incl f)) :
    Subsingleton (RelHomotopyGroup (Fin k)
      ⟨TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
        (Set.range (MappingCylinder.incl f)), b⟩) :=
  hf.subsingleton_relHomotopyGroup_mappingCylinder (Fin k) (by rw [Nat.card_fin]; lia) b

/-- **The mapping cylinder of an `n`-connected map is homologically `n`-connected relative to its
bottom face**: if `f : X → Y` is `n`-connected, then `H_m(M_f, X; R) = 0` for every `m ≤ n`, where
`X` is identified with the bottom face of the mapping cylinder `M_f`. -/
theorem isZero_singularHomology_mappingCylinder (hf : f.IsNConnected n) {m : ℕ} (hm : m ≤ n) :
    IsZero ((TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
      (Set.range (MappingCylinder.incl f))).singularHomology (ModuleCat.of R R) m) :=
  isZero_singularHomology_ofSubset_of_relHomotopyGroup (n := n + 1)
    (X := TopCat.of (MappingCylinder f)) (A := Set.range (MappingCylinder.incl f))
    (MappingCylinder.exists_mem_range_incl_joined hf.exists_joined)
    hf.subsingleton_relHomotopyGroup_mappingCylinder_fin R (by lia)

/-- The map induced on singular homology by `f` is the map induced by the inclusion of the bottom
face of the mapping cylinder, up to the isomorphisms induced by the homeomorphism of `X` with the
bottom face and by the projection of the mapping cylinder, which is a homotopy equivalence. -/
private theorem singularHomologyMap_eq (m : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map (TopCat.ofHom f) =
      ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
          (TopCat.ofHom (MappingCylinder.inclHomeomorph f :
            C(X, Set.range (MappingCylinder.incl f)))) ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
          (TopCat.ofHom (ContinuousMap.subtypeVal (Set.range (MappingCylinder.incl f)))) ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
          (TopCat.ofHom (MappingCylinder.proj f)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← TopCat.ofHom_comp, ← TopCat.ofHom_comp,
    ContinuousMap.comp_assoc, MappingCylinder.proj_comp_subtypeVal_comp_inclHomeomorph]

/-- The bottom face homeomorphism and the projection of the mapping cylinder induce isomorphisms
on singular homology. -/
private theorem isIso_singularHomologyMap_inclHomeomorph_proj (m : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (MappingCylinder.inclHomeomorph f :
          C(X, Set.range (MappingCylinder.incl f))))) ∧
      IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (MappingCylinder.proj f))) :=
  ⟨(MappingCylinder.inclHomeomorph f).toHomotopyEquiv.isWeakHomotopyEquivalence
      |>.isIso_singularHomologyMap (ModuleCat.of R R) m,
    (MappingCylinder.homotopyEquiv_toFun (f := f) ▸
      (MappingCylinder.homotopyEquiv f).isWeakHomotopyEquivalence).isIso_singularHomologyMap
        (ModuleCat.of R R) m⟩

/-- **An `n`-connected map induces isomorphisms on singular homology below degree `n`**: if
`f : X → Y` is `n`-connected, then `f_* : H_m(X; R) → H_m(Y; R)` is an isomorphism for every
`m < n` and every coefficient ring `R`. -/
theorem isIso_singularHomologyMap (hf : f.IsNConnected n) {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom f)) := by
  obtain ⟨_, _⟩ := isIso_singularHomologyMap_inclHomeomorph_proj (f := f) R m
  have := isIso_singularHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt (n := n + 1)
    (X := TopCat.of (MappingCylinder f)) (A := Set.range (MappingCylinder.incl f))
    (MappingCylinder.exists_mem_range_incl_joined hf.exists_joined)
    hf.subsingleton_relHomotopyGroup_mappingCylinder_fin R (m := m) (by lia)
  rw [singularHomologyMap_eq]
  infer_instance

/-- **An `n`-connected map induces surjections on singular homology up to degree `n`**: if
`f : X → Y` is `n`-connected, then `f_* : H_m(X; R) → H_m(Y; R)` is an epimorphism for every
`m ≤ n` and every coefficient ring `R`. -/
theorem epi_singularHomologyMap (hf : f.IsNConnected n) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom f)) := by
  obtain ⟨_, _⟩ := isIso_singularHomologyMap_inclHomeomorph_proj (f := f) R m
  have := epi_singularHomologyMap_subtypeVal_of_relHomotopyGroup (n := n + 1)
    (X := TopCat.of (MappingCylinder f)) (A := Set.range (MappingCylinder.incl f))
    (MappingCylinder.exists_mem_range_incl_joined hf.exists_joined)
    hf.subsingleton_relHomotopyGroup_mappingCylinder_fin R (m := m) (by lia)
  rw [singularHomologyMap_eq]
  infer_instance

end ContinuousMap.IsNConnected

namespace TauCeti

open Topology Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D] {n : ℕ}
  {A : Set X} (R : Type u) [Ring R]

/-- **The inclusion of the `n`-skeleton is surjective on homology up to degree `n`.** If `A` is the
`n`-skeleton `skeletonLT C (n + 1)` of a relative CW complex `C`, then the inclusion `A ↪ C`
induces an epimorphism `H_m(A; R) → H_m(C; R)` for every `m ≤ n`. -/
theorem epi_singularHomologyMap_inclusion_skeletonLT (hA : (skeletonLT C (n + 1) : Set X) = A)
    (hAC : A ⊆ C) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (ContinuousMap.inclusion hAC))) :=
  (isNConnected_inclusion_skeletonLT hA hAC).epi_singularHomologyMap R hm

end TauCeti
