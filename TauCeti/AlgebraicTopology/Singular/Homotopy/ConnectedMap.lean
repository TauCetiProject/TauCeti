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
for every coefficient ring `R`. The same holds with local coefficients: for every local coefficient
system `L` on `Y`, the map `H_m(X; f⁎L) → H_m(Y; L)` is an isomorphism for `m < n` and a
surjection for `m = n`. This is the range version of the fact that a weak homotopy equivalence
induces isomorphisms on homology
(`ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularHomologyMap` and
`ContinuousMap.IsWeakHomotopyEquivalence.isIso_twistedHomologyMap`), which is the case of maps
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

With local coefficients the deformation is used directly on chains. Below its dimension bound it
retracts the cubes of `M_f` onto cubes of the bottom face, transporting coefficients along the track
of the origin, and the swept cubes give the chain homotopy from the identity to this retraction
followed by the inclusion (`TauCeti.SubspaceCubeDeformation.twistedRetractChain`). In degrees where
both are defined this makes the inclusion of the bottom face surjective on homology, and injective
one degree lower (`TauCeti.epi_twistedHomologyMap_subtypeVal_of_relHomotopyGroup`,
`TauCeti.isIso_twistedHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt`).

For a map of pairs `(X, A) → (Y, B)` which is `n`-connected on the ambient spaces and
`(n - 1)`-connected on the subspaces, the five lemma in the long exact sequences of the two pairs
gives isomorphisms `H_m(X, A; R) ≅ H_m(Y, B; R)` for `m < n` and a surjection for `m = n`
(`TopPair.isIso_singularHomologyMap_of_isNConnected`,
`TopPair.epi_singularHomologyMap_of_isNConnected`).

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
* `ContinuousMap.IsNConnected.isIso_twistedHomologyMap`,
  `ContinuousMap.IsNConnected.epi_twistedHomologyMap`: an `n`-connected map induces isomorphisms
  on homology with local coefficients below degree `n`, and surjections up to degree `n`.
* `TopPair.isIso_singularHomologyMap_of_isNConnected`,
  `TopPair.epi_singularHomologyMap_of_isNConnected`: a map of pairs which is `n`-connected on the
  ambient spaces and `(n - 1)`-connected on the subspaces induces isomorphisms on relative singular
  homology below degree `n`, and surjections up to degree `n`.
* `TauCeti.epi_singularHomologyMap_inclusion_skeletonLT`: the inclusion of the `n`-skeleton of a
  relative CW complex induces surjections on singular homology up to degree `n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34, Section 3.H (homology with local coefficients), and Section 4.1,
  Proposition 4.21 and its proof.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Section 9.5.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u v

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

/-! ### Local coefficients -/

namespace ContinuousMap.IsNConnected

open LocalCoefficientSystem

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {n : ℕ}
  {R : Type u} [Ring R]

/-- A property of morphisms of modules that respects isomorphisms holds for the map induced by `f`
on homology with local coefficients as soon as it holds for the map induced by the inclusion of
the bottom face of the mapping cylinder: the homeomorphism of `X` with the bottom face and the
projection of the mapping cylinder are homotopy equivalences. -/
private theorem twistedHomologyMap_mem (P : MorphismProperty (ModuleCat.{v} R)) [P.RespectsIso]
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) (m : ℕ)
    (hi : P (twistedHomologyMap
      (TopCat.ofHom (ContinuousMap.subtypeVal (Set.range (MappingCylinder.incl f))))
      ((LocalCoefficientSystem.pullback (MappingCylinder.homotopyEquiv f).toFun).obj L) m)) :
    P (twistedHomologyMap (TopCat.ofHom f) L m) := by
  let A : Set (TopCat.of (MappingCylinder f)) := Set.range (MappingCylinder.incl f)
  let ψ : X ≃ₜ A := MappingCylinder.inclHomeomorph f
  let i : TopCat.of A ⟶ TopCat.of (MappingCylinder f) := TopCat.ofHom (ContinuousMap.subtypeVal A)
  let p := TopCat.ofHom (MappingCylinder.homotopyEquiv f).toFun
  have : QuasiIso (twistedChainComplexMap (TopCat.ofHom ψ.toHomotopyEquiv.toFun)
      ((LocalCoefficientSystem.pullback (i ≫ p).hom).obj L)) :=
    ψ.toHomotopyEquiv.quasiIso_twistedChainComplexMap _
  have : QuasiIso (twistedChainComplexMap p L) :=
    (MappingCylinder.homotopyEquiv f).quasiIso_twistedChainComplexMap L
  have hf' : TopCat.ofHom f = TopCat.ofHom ψ.toHomotopyEquiv.toFun ≫ i ≫ p := by
    ext x
    simp only [ψ, i, p, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
      ContinuousMap.subtypeVal_apply, MappingCylinder.homotopyEquiv_apply]
    exact (congrArg (· x) (MappingCylinder.proj_comp_subtypeVal_comp_inclHomeomorph (f := f))).symm
  rw [twistedHomologyMap, twistedChainComplexMap_congr _ _ hf', twistedChainComplexMap_comp,
    twistedChainComplexMap_comp]
  simp only [HomologicalComplex.homologyMap_comp]
  rw [P.cancel_left_of_respectsIso, P.cancel_left_of_respectsIso, P.cancel_left_of_respectsIso,
    P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact hi

/-- **An `n`-connected map induces isomorphisms on homology with local coefficients below degree
`n`**: if `f : X → Y` is `n`-connected, then for every local coefficient system `L` on `Y` the map
`f_* : H_m(X; f⁎L) → H_m(Y; L)` is an isomorphism for every `m < n`. -/
theorem isIso_twistedHomologyMap (hf : f.IsNConnected n)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) {m : ℕ} (hm : m < n) :
    IsIso (twistedHomologyMap (TopCat.ofHom f) L m) :=
  twistedHomologyMap_mem (MorphismProperty.isomorphisms _) L m
    (isIso_twistedHomologyMap_subtypeVal_of_relHomotopyGroup_of_add_one_lt (n := n + 1)
      (MappingCylinder.exists_mem_range_incl_joined hf.exists_joined)
      hf.subsingleton_relHomotopyGroup_mappingCylinder_fin _ (by lia))

/-- **An `n`-connected map induces surjections on homology with local coefficients up to degree
`n`**: if `f : X → Y` is `n`-connected, then for every local coefficient system `L` on `Y` the map
`f_* : H_m(X; f⁎L) → H_m(Y; L)` is an epimorphism for every `m ≤ n`. -/
theorem epi_twistedHomologyMap (hf : f.IsNConnected n)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) {m : ℕ} (hm : m ≤ n) :
    Epi (twistedHomologyMap (TopCat.ofHom f) L m) :=
  twistedHomologyMap_mem (MorphismProperty.epimorphisms _) L m
    (epi_twistedHomologyMap_subtypeVal_of_relHomotopyGroup (n := n + 1)
      (MappingCylinder.exists_mem_range_incl_joined hf.exists_joined)
      hf.subsingleton_relHomotopyGroup_mappingCylinder_fin _ (by lia))

end ContinuousMap.IsNConnected

/-! ### Pairs of spaces -/

namespace TopPair

variable {P P' : TopPair.{u}} (f : P ⟶ P') {n : ℕ} (R : Type u) [Ring R]

/-- **A map of pairs which is `n`-connected on the ambient spaces and `(n - 1)`-connected on the
subspaces induces isomorphisms on relative singular homology below degree `n`**: the map
`H_m(X, A; R) → H_m(Y, B; R)` is an isomorphism for every `m < n`, by the five lemma in the long
exact sequences of the two pairs. -/
theorem isIso_singularHomologyMap_of_isNConnected (hfst : (Hom.fst f).hom.IsNConnected n)
    (hsnd : (Hom.snd f).hom.IsNConnected (n - 1)) {m : ℕ} (hm : m < n) :
    IsIso (TopPair.singularHomologyMap f (ModuleCat.of R R) m) := by
  have h := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (SSetPair.chainComplexShortComplexMap (toSSetPair.map f) (ModuleCat.of R R))
    ((toSSetPair.obj P).shortExact_chainComplexShortComplex _)
    ((toSSetPair.obj P').shortExact_chainComplexShortComplex _) m
    (by
      rw [homologyMap_chainComplexShortComplexMap_τ₁]
      exact hsnd.epi_singularHomologyMap R (by lia))
    (by
      rw [homologyMap_chainComplexShortComplexMap_τ₂]
      exact hfst.isIso_singularHomologyMap R hm)
    (fun j hj ↦ by
      rw [homologyMap_chainComplexShortComplexMap_τ₁]
      exact hsnd.isIso_singularHomologyMap R (by simp at hj; lia))
    (fun j hj ↦ by
      rw [homologyMap_chainComplexShortComplexMap_τ₂]
      -- The objects of the rewritten goal are the homology of the terms of the chain sequence,
      -- which agree with the singular homology objects only after unfolding definitions, so
      -- instance search does not find `IsIso.mono_of_iso`; the instance is passed by hand.
      exact @IsIso.mono_of_iso _ _ _ _ _ (hfst.isIso_singularHomologyMap R (by simp at hj; lia)))
  rwa [SSetPair.chainComplexShortComplexMap_τ₃] at h

/-- **A map of pairs which is `n`-connected on the ambient spaces and `(n - 1)`-connected on the
subspaces induces surjections on relative singular homology up to degree `n`**: the map
`H_m(X, A; R) → H_m(Y, B; R)` is an epimorphism for every `m ≤ n`. -/
theorem epi_singularHomologyMap_of_isNConnected (hfst : (Hom.fst f).hom.IsNConnected n)
    (hsnd : (Hom.snd f).hom.IsNConnected (n - 1)) {m : ℕ} (hm : m ≤ n) :
    Epi (TopPair.singularHomologyMap f (ModuleCat.of R R) m) := by
  have h := HomologicalComplex.HomologySequence.epi_homologyMap_τ₃
    (SSetPair.chainComplexShortComplexMap (toSSetPair.map f) (ModuleCat.of R R))
    ((toSSetPair.obj P).shortExact_chainComplexShortComplex _)
    ((toSSetPair.obj P').shortExact_chainComplexShortComplex _) m
    (by
      rw [homologyMap_chainComplexShortComplexMap_τ₂]
      exact hfst.epi_singularHomologyMap R hm)
    (fun j hj ↦ by
      rw [homologyMap_chainComplexShortComplexMap_τ₁]
      exact hsnd.epi_singularHomologyMap R (by simp at hj; lia))
    (fun j hj ↦ by
      rw [homologyMap_chainComplexShortComplexMap_τ₂]
      -- As in `isIso_singularHomologyMap_of_isNConnected`, the instance is passed by hand.
      exact @IsIso.mono_of_iso _ _ _ _ _ (hfst.isIso_singularHomologyMap R (by simp at hj; lia)))
  rwa [SSetPair.chainComplexShortComplexMap_τ₃] at h

end TopPair
