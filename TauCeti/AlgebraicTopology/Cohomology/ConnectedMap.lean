/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# `n`-connected maps and singular cohomology

An `n`-connected map `f : X → Y` (`ContinuousMap.IsNConnected`) induces isomorphisms
`f^* : H^m(Y; M) ≅ H^m(X; M)` on singular cohomology for every `m < n`, and a monomorphism in
degree `n`, for every coefficient ring `R` and every `R`-module `M` of values
(`ContinuousMap.IsNConnected.isIso_singularCohomologyMap`,
`ContinuousMap.IsNConnected.mono_singularCohomologyMap`). This is the cohomological form of the
statement for singular homology (`ContinuousMap.IsNConnected.isIso_singularHomologyMap` and
`ContinuousMap.IsNConnected.epi_singularHomologyMap`), and the range version of the fact that a
weak homotopy equivalence induces isomorphisms on singular cohomology
(`ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularCohomologyMap`). No CW structure on `X` or
`Y` is needed.

The proof factors `f` through its mapping cylinder `M_f`, as for homology:

  `X ≃ₜ (bottom face of M_f) ↪ M_f → Y`.

The first map is a homeomorphism and the last a homotopy equivalence, so both induce isomorphisms
on cohomology. For the inclusion of the bottom face, the relative singular homology
`H_m(M_f, X; R)` vanishes for `m ≤ n`
(`ContinuousMap.IsNConnected.isZero_singularHomology_mappingCylinder`). The relative singular
chains are projective, since they are a direct summand of the free singular chains of `M_f`, so the
complex of relative singular cochains `Hom(C(M_f, X; R), M)` is exact in the same degrees
(`ChainComplex.exactAt_linearYonedaObj_of_projective`, through
`TopPair.isZero_singularCohomology_of_isZero_singularHomology`): the relative cohomology
`H^m(M_f, X; M)` vanishes for `m ≤ n`, whatever the module `M`
(`ContinuousMap.IsNConnected.isZero_singularCohomology_mappingCylinder`). No universal coefficient
theorem is involved. The long exact cohomology sequence of the pair `(M_f, X)` then makes
restriction to the bottom face injective in degrees `≤ n` and surjective in degrees `< n`.

For a map of pairs `(X, A) → (Y, B)` which is `n`-connected on the ambient spaces and
`(n - 1)`-connected on the subspaces, the five lemma in the long exact cohomology sequences of the
two pairs gives isomorphisms `H^m(Y, B; M) ≅ H^m(X, A; M)` for `m < n` and a monomorphism for
`m = n` (`TopPair.isIso_singularCohomologyMap_of_isNConnected`,
`TopPair.mono_singularCohomologyMap_of_isNConnected`).

Applied to the inclusion of the `n`-skeleton of a CW complex, which is `n`-connected
(`TauCeti.isNConnected_inclusion_skeletonLT`), this says that the skeleton carries the cohomology of
the complex below degree `n`.

## Main results

* `ContinuousMap.IsNConnected.isZero_singularCohomology_mappingCylinder`: the relative cohomology
  of the mapping cylinder of an `n`-connected map, relative to its bottom face, vanishes up to
  degree `n`.
* `ContinuousMap.IsNConnected.isIso_singularCohomologyMap`: an `n`-connected map induces
  isomorphisms on singular cohomology below degree `n`.
* `ContinuousMap.IsNConnected.mono_singularCohomologyMap`: an `n`-connected map induces
  monomorphisms on singular cohomology up to degree `n`.
* `TopPair.isIso_singularCohomologyMap_of_isNConnected`,
  `TopPair.mono_singularCohomologyMap_of_isNConnected`: the same for relative singular cohomology,
  along a map of pairs which is `n`-connected on the ambient spaces and `(n - 1)`-connected on the
  subspaces.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 and Section 4.1, Proposition 4.21 and its proof.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Section 9.5.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u

namespace ContinuousMap.IsNConnected

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {n : ℕ}
  (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

/-- **The mapping cylinder of an `n`-connected map is cohomologically `n`-connected relative to
its bottom face**: if `f : X → Y` is `n`-connected, then `H^m(M_f, X; M) = 0` for every `m ≤ n`
and every module `M`, where `X` is identified with the bottom face of the mapping cylinder `M_f`.
The relative singular chains are projective and exact in degrees `≤ n`, so their dual is exact in
the same degrees. -/
theorem isZero_singularCohomology_mappingCylinder (hf : f.IsNConnected n) {m : ℕ} (hm : m ≤ n) :
    IsZero ((TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
      (Set.range (MappingCylinder.incl f))).singularCohomology (ModuleCat.of R R) k M m) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of R R) M m
    fun _ hj ↦ hf.isZero_singularHomology_mappingCylinder R (hj.trans hm)

variable {R k M} in
/-- The map induced on singular cohomology by `f` is the map induced by the restriction to the
bottom face of the mapping cylinder, up to the isomorphisms induced by the projection of the
mapping cylinder, which is a homotopy equivalence, and by the homeomorphism of `X` with the bottom
face. -/
private theorem singularCohomologyMap_eq (m : ℕ) :
    TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M) (TopCat.ofHom f) m =
      TopCat.singularCohomologyMap (TopCat.ofHom (MappingCylinder.proj f)) m ≫
        TopCat.singularCohomologyMap
          (TopCat.ofHom (ContinuousMap.subtypeVal (Set.range (MappingCylinder.incl f)))) m ≫
        TopCat.singularCohomologyMap (TopCat.ofHom (MappingCylinder.inclHomeomorph f :
          C(X, Set.range (MappingCylinder.incl f)))) m := by
  rw [← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_comp]
  congr 2
  ext x
  exact (congrArg (· x) (MappingCylinder.proj_comp_subtypeVal_comp_inclHomeomorph (f := f))).symm

variable {R k M} in
/-- The projection of the mapping cylinder and the bottom face homeomorphism induce isomorphisms
on singular cohomology. -/
private theorem isIso_singularCohomologyMap_proj_inclHomeomorph (m : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
        (TopCat.ofHom (MappingCylinder.proj f)) m) ∧
      IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
        (TopCat.ofHom (MappingCylinder.inclHomeomorph f :
          C(X, Set.range (MappingCylinder.incl f)))) m) :=
  ⟨MappingCylinder.homotopyEquiv_toFun (f := f) ▸
      (MappingCylinder.homotopyEquiv f).isIso_singularCohomologyMap _ k M m,
    (MappingCylinder.inclHomeomorph f).toHomotopyEquiv.isIso_singularCohomologyMap _ k M m⟩

/-- **An `n`-connected map induces monomorphisms on singular cohomology up to degree `n`**: if
`f : X → Y` is `n`-connected, then `f^* : H^m(Y; M) → H^m(X; M)` is a monomorphism for every
`m ≤ n`, every coefficient ring `R` and every `R`-module `M`. -/
theorem mono_singularCohomologyMap (hf : f.IsNConnected n) {m : ℕ} (hm : m ≤ n) :
    Mono (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
      (TopCat.ofHom f) m) := by
  obtain ⟨_, _⟩ := isIso_singularCohomologyMap_proj_inclHomeomorph (f := f) (R := R) (k := k)
    (M := M) m
  -- In the exact sequence `H^m(M_f, X) ⟶ H^m(M_f) ⟶ H^m(X)` of the pair, the first term vanishes.
  have : Mono (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
      (TopCat.ofHom (ContinuousMap.subtypeVal (Set.range (MappingCylinder.incl f)))) m) :=
    ((TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
      (Set.range (MappingCylinder.incl f))).singularCohomology_exact_space _ k M m).mono_g
        ((hf.isZero_singularCohomology_mappingCylinder R k M hm).eq_of_src _ _)
  rw [singularCohomologyMap_eq]
  infer_instance

/-- **An `n`-connected map induces isomorphisms on singular cohomology below degree `n`**: if
`f : X → Y` is `n`-connected, then `f^* : H^m(Y; M) → H^m(X; M)` is an isomorphism for every
`m < n`, every coefficient ring `R` and every `R`-module `M`. -/
theorem isIso_singularCohomologyMap (hf : f.IsNConnected n) {m : ℕ} (hm : m < n) :
    IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
      (TopCat.ofHom f) m) := by
  obtain ⟨_, _⟩ := isIso_singularCohomologyMap_proj_inclHomeomorph (f := f) (R := R) (k := k)
    (M := M) m
  let P := TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
    (Set.range (MappingCylinder.incl f))
  let i : TopCat.of (Set.range (MappingCylinder.incl f)) ⟶ TopCat.of (MappingCylinder f) :=
    TopCat.ofHom (ContinuousMap.subtypeVal _)
  -- In the exact sequence `H^m(M_f, X) ⟶ H^m(M_f) ⟶ H^m(X) ⟶ H^(m+1)(M_f, X)` of the pair, the
  -- two outer terms vanish.
  have : Mono (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M) i m) :=
    (P.singularCohomology_exact_space _ k M m).mono_g
      ((hf.isZero_singularCohomology_mappingCylinder R k M hm.le).eq_of_src _ _)
  have : Epi (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M) i m) :=
    (P.singularCohomology_exact_subspace _ k M m (m + 1)).epi_f
      ((hf.isZero_singularCohomology_mappingCylinder R k M hm).eq_of_tgt _ _)
  have := isIso_of_mono_of_epi
    (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M) i m)
  rw [singularCohomologyMap_eq]
  infer_instance

end ContinuousMap.IsNConnected

/-! ### Pairs of spaces -/

namespace TopPair

variable {P P' : TopPair.{u}} (f : P ⟶ P') {n : ℕ} {R : Type u} [Ring R] {k : Type*} [Ring k]
  [Linear k (ModuleCat.{u} R)] {M : ModuleCat.{u} R}

variable (R k M)

/-- **A map of pairs which is `n`-connected on the ambient spaces and `(n - 1)`-connected on the
subspaces induces isomorphisms on relative singular cohomology below degree `n`**: the map
`H^m(Y, B; M) → H^m(X, A; M)` is an isomorphism for every `m < n`, by the five lemma in the long
exact cohomology sequences of the two pairs. -/
theorem isIso_singularCohomologyMap_of_isNConnected (hfst : (Hom.fst f).hom.IsNConnected n)
    (hsnd : (Hom.snd f).hom.IsNConnected (n - 1)) {m : ℕ} (hm : m < n) :
    IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M) f m) := by
  have h := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁
    (singularCochainComplexShortComplexMap (R := ModuleCat.of R R) (k := k) (M := M) f)
    (P'.shortExact_singularCochainComplexShortComplex _ k M)
    (P.shortExact_singularCochainComplexShortComplex _ k M) m
    (fun j hj ↦ by
      rw [homologyMap_singularCochainComplexShortComplexMap_τ₂]
      have := hfst.isIso_singularCohomologyMap R k M (m := j) (by simp at hj; lia)
      infer_instance)
    (fun j hj ↦ by
      rw [homologyMap_singularCochainComplexShortComplexMap_τ₃]
      exact hsnd.isIso_singularCohomologyMap R k M (by simp at hj; lia))
    (by
      rw [homologyMap_singularCochainComplexShortComplexMap_τ₂]
      exact hfst.isIso_singularCohomologyMap R k M hm)
    (by
      rw [homologyMap_singularCochainComplexShortComplexMap_τ₃]
      exact hsnd.mono_singularCohomologyMap R k M (by lia))
  rwa [singularCochainComplexShortComplexMap_τ₁] at h

/-- **A map of pairs which is `n`-connected on the ambient spaces and `(n - 1)`-connected on the
subspaces induces monomorphisms on relative singular cohomology up to degree `n`**: the map
`H^m(Y, B; M) → H^m(X, A; M)` is a monomorphism for every `m ≤ n`. -/
theorem mono_singularCohomologyMap_of_isNConnected (hfst : (Hom.fst f).hom.IsNConnected n)
    (hsnd : (Hom.snd f).hom.IsNConnected (n - 1)) {m : ℕ} (hm : m ≤ n) :
    Mono (TopPair.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M) f m) := by
  have h := HomologicalComplex.HomologySequence.mono_homologyMap_τ₁
    (singularCochainComplexShortComplexMap (R := ModuleCat.of R R) (k := k) (M := M) f)
    (P'.shortExact_singularCochainComplexShortComplex _ k M)
    (P.shortExact_singularCochainComplexShortComplex _ k M) m
    (fun j hj ↦ by
      rw [homologyMap_singularCochainComplexShortComplexMap_τ₂]
      have := hfst.isIso_singularCohomologyMap R k M (m := j) (by simp at hj; lia)
      infer_instance)
    (fun j hj ↦ by
      rw [homologyMap_singularCochainComplexShortComplexMap_τ₃]
      exact hsnd.mono_singularCohomologyMap R k M (by simp at hj; lia))
    (by
      rw [homologyMap_singularCochainComplexShortComplexMap_τ₂]
      exact hfst.mono_singularCohomologyMap R k M hm)
  rwa [singularCochainComplexShortComplexMap_τ₁] at h

end TopPair
