/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Cohomology.WeakHomotopyEquivalence
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

The same holds with local coefficients, for a local coefficient system `L` on `Y` with
projective fibres: `f^* : H^m(Y; L, M) → H^m(X; f⁎L, M)` is an isomorphism for `m < n` and a
monomorphism for `m = n` (`ContinuousMap.IsNConnected.isIso_twistedCohomologyMap`,
`ContinuousMap.IsNConnected.mono_twistedCohomologyMap`), and likewise for maps of pairs
(`TopPair.isIso_twistedCohomologyMap_of_isNConnected`,
`TopPair.mono_twistedCohomologyMap_of_isNConnected`). The proof is the same: the relative homology
`H_m(M_f, X; L)` vanishes for `m ≤ n`
(`ContinuousMap.IsNConnected.isZero_twistedHomology_mappingCylinder`), and the relative twisted
chains are projective when the fibres of `L` are, so the relative cohomology vanishes in the same
degrees (`TopPair.isZero_twistedCohomology_of_isZero_twistedHomology`). Projectivity of the fibres
is the hypothesis under which weak homotopy equivalences are known to induce isomorphisms on
cohomology with local coefficients
(`ContinuousMap.IsWeakHomotopyEquivalence.isIso_twistedCohomologyMap`), which is the case of maps
that are `n`-connected for every `n`.

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
* `ContinuousMap.IsNConnected.isZero_twistedCohomology_mappingCylinder`,
  `ContinuousMap.IsNConnected.isIso_twistedCohomologyMap`,
  `ContinuousMap.IsNConnected.mono_twistedCohomologyMap`,
  `TopPair.isIso_twistedCohomologyMap_of_isNConnected`,
  `TopPair.mono_twistedCohomologyMap_of_isNConnected`: the same statements with local coefficients
  with projective fibres.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Section 3.H (cohomology with local coefficients) and Section 4.1, Proposition 4.21
  and its proof.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Section 9.5.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u v

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

/-! ### Local coefficients -/

namespace ContinuousMap.IsNConnected

open LocalCoefficientSystem

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {n : ℕ}
  {R : Type u} [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{v} R)] (M : ModuleCat.{v} R)

/-- **The mapping cylinder of an `n`-connected map is cohomologically `n`-connected relative to its
bottom face, with local coefficients**: if `f : X → Y` is `n`-connected, then for every local
coefficient system `L` on the mapping cylinder `M_f` with projective fibres,
`H^m(M_f, X; L, M) = 0` for every `m ≤ n` and every module `M`, where `X` is identified with the
bottom face of `M_f`. -/
theorem isZero_twistedCohomology_mappingCylinder (hf : f.IsNConnected n)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of (MappingCylinder f)))
    [∀ x, Projective (L.obj x)] {m : ℕ} (hm : m ≤ n) :
    IsZero ((TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
      (Set.range (MappingCylinder.incl f))).twistedCohomology L k M m) :=
  let P := TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
    (Set.range (MappingCylinder.incl f))
  -- Read `L` as a system on the ambient space of the pair, which unfolds to `M_f` only up to
  -- instance transparency.
  let L' : LocalCoefficientSystem.{u, v, v} R P.fst := L
  have : ∀ x, Projective (L'.obj x) := ‹∀ x, Projective (L.obj x)›
  TopPair.isZero_twistedCohomology_of_isZero_twistedHomology P L' (k := k) M m
    fun _ hj ↦ hf.isZero_twistedHomology_mappingCylinder L (hj.trans hm)

variable {k M} in
/-- A property of morphisms of modules that respects isomorphisms holds for the map induced by `f`
on cohomology with local coefficients as soon as it holds for the map induced by the inclusion of
the bottom face of the mapping cylinder: the homeomorphism of `X` with the bottom face and the
projection of the mapping cylinder are homotopy equivalences. -/
private theorem twistedCohomologyMap_mem (P : MorphismProperty (ModuleCat.{v} k))
    [P.RespectsIso] (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) (m : ℕ)
    (hi : P (twistedCohomologyMap k M
      (TopCat.ofHom (ContinuousMap.subtypeVal (Set.range (MappingCylinder.incl f))))
      ((LocalCoefficientSystem.pullback (TopCat.ofHom (MappingCylinder.proj f)).hom).obj L) m)) :
    P (twistedCohomologyMap k M (TopCat.ofHom f) L m) := by
  let A : Set (TopCat.of (MappingCylinder f)) := Set.range (MappingCylinder.incl f)
  let ψ : TopCat.of X ⟶ TopCat.of A :=
    TopCat.ofHom (MappingCylinder.inclHomeomorph f : C(X, A))
  let i : TopCat.of A ⟶ TopCat.of (MappingCylinder f) := TopCat.ofHom (ContinuousMap.subtypeVal A)
  let p : TopCat.of (MappingCylinder f) ⟶ TopCat.of Y := TopCat.ofHom (MappingCylinder.proj f)
  have hf' : TopCat.ofHom f = ψ ≫ i ≫ p := by
    ext x
    exact (congrArg (· x) (MappingCylinder.proj_comp_subtypeVal_comp_inclHomeomorph (f := f))).symm
  have : IsIso (twistedCohomologyMap k M p L m) :=
    (MappingCylinder.homotopyEquiv_toFun (f := f) ▸
      (MappingCylinder.homotopyEquiv f).isWeakHomotopyEquivalence).isIso_twistedCohomologyMap
        k M L m
  have : IsIso (twistedCohomologyMap k M ψ
      ((LocalCoefficientSystem.pullback (i ≫ p).hom).obj L) m) :=
    (MappingCylinder.inclHomeomorph f).toHomotopyEquiv.isWeakHomotopyEquivalence
      |>.isIso_twistedCohomologyMap k M _ m
  -- Factor `f^*` through `p^*`, `i^*` and `ψ^*`, up to the coefficient isomorphisms comparing the
  -- pulled-back systems.
  rw [twistedCohomologyMap_congr k M _ L hf' m, twistedCohomologyMap_comp k M ψ (i ≫ p),
    twistedCohomologyMap_comp k M i p]
  simp only [Category.assoc]
  exact (P.cancel_left_of_respectsIso _ _).2 ((P.cancel_right_of_respectsIso _ _).2 hi)

/-- **An `n`-connected map induces monomorphisms on cohomology with local coefficients up to degree
`n`**: if `f : X → Y` is `n`-connected, then for every local coefficient system `L` on `Y` with
projective fibres the map `f^* : H^m(Y; L, M) → H^m(X; f⁎L, M)` is a monomorphism for every
`m ≤ n` and every module `M`. -/
theorem mono_twistedCohomologyMap (hf : f.IsNConnected n)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) [∀ y, Projective (L.obj y)] {m : ℕ}
    (hm : m ≤ n) : Mono (twistedCohomologyMap k M (TopCat.ofHom f) L m) := by
  let P := TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
    (Set.range (MappingCylinder.incl f))
  let L' : LocalCoefficientSystem.{u, v, v} R P.fst :=
    (LocalCoefficientSystem.pullback (TopCat.ofHom (MappingCylinder.proj f)).hom).obj L
  have : ∀ x, Projective (L'.obj x) := fun x ↦ projective_pullback_obj_obj _ L x
  -- In the exact sequence `H^m(M_f, X) ⟶ H^m(M_f) ⟶ H^m(X)` of the pair, the first term vanishes.
  exact twistedCohomologyMap_mem (MorphismProperty.monomorphisms _) L m <|
    (P.twistedCohomology_exact_space L' k M m).mono_g
      ((hf.isZero_twistedCohomology_mappingCylinder k M L' hm).eq_of_src _ _)

/-- **An `n`-connected map induces isomorphisms on cohomology with local coefficients below degree
`n`**: if `f : X → Y` is `n`-connected, then for every local coefficient system `L` on `Y` with
projective fibres the map `f^* : H^m(Y; L, M) → H^m(X; f⁎L, M)` is an isomorphism for every
`m < n` and every module `M`. -/
theorem isIso_twistedCohomologyMap (hf : f.IsNConnected n)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) [∀ y, Projective (L.obj y)] {m : ℕ}
    (hm : m < n) : IsIso (twistedCohomologyMap k M (TopCat.ofHom f) L m) := by
  let P := TopPair.ofSubset (X := TopCat.of (MappingCylinder f))
    (Set.range (MappingCylinder.incl f))
  let L' : LocalCoefficientSystem.{u, v, v} R P.fst :=
    (LocalCoefficientSystem.pullback (TopCat.ofHom (MappingCylinder.proj f)).hom).obj L
  have : ∀ x, Projective (L'.obj x) := fun x ↦ projective_pullback_obj_obj _ L x
  -- In the exact sequence `H^m(M_f, X) ⟶ H^m(M_f) ⟶ H^m(X) ⟶ H^(m+1)(M_f, X)` of the pair, the
  -- two outer terms vanish.
  have : Mono (twistedCohomologyMap k M P.map L' m) :=
    (P.twistedCohomology_exact_space L' k M m).mono_g
      ((hf.isZero_twistedCohomology_mappingCylinder k M L' hm.le).eq_of_src _ _)
  have : Epi (twistedCohomologyMap k M P.map L' m) :=
    (P.twistedCohomology_exact_subspace L' k M m (m + 1)).epi_f
      ((hf.isZero_twistedCohomology_mappingCylinder k M L' hm).eq_of_tgt _ _)
  exact twistedCohomologyMap_mem (MorphismProperty.isomorphisms _) L m
    (isIso_of_mono_of_epi (twistedCohomologyMap k M P.map L' m))

end ContinuousMap.IsNConnected

/-! ### Pairs of spaces with local coefficients -/

namespace TopPair

open LocalCoefficientSystem

variable {P P' : TopPair.{v}} (f : P ⟶ P') {n : ℕ} {R : Type u} [Ring R] (k : Type*) [Ring k]
  [Linear k (ModuleCat.{v} R)] (M : ModuleCat.{v} R)
  (L : LocalCoefficientSystem.{u, v, v} R P'.fst)

variable [∀ y, Projective (L.obj y)]

/-- **A map of pairs which is `n`-connected on the ambient spaces and `(n - 1)`-connected on the
subspaces induces isomorphisms on relative cohomology with local coefficients below degree `n`**:
for a local coefficient system `L` on `Y` with projective fibres, the map
`H^m(Y, B; L, M) → H^m(X, A; f⁎L, M)` is an isomorphism for every `m < n`, by the five lemma in the
long exact cohomology sequences of the two pairs. -/
theorem isIso_twistedCohomologyMap_of_isNConnected (hfst : (Hom.fst f).hom.IsNConnected n)
    (hsnd : (Hom.snd f).hom.IsNConnected (n - 1)) {m : ℕ} (hm : m < n) :
    IsIso (TopPair.twistedCohomologyMap k M f L m) := by
  have h := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₁
    (twistedCochainComplexShortComplexMap k M f L)
    (P'.shortExact_twistedCochainComplexShortComplex L k M)
    (P.shortExact_twistedCochainComplexShortComplex _ k M) m
    (fun j hj ↦ by
      rw [homologyMap_twistedCochainComplexShortComplexMap_τ₂]
      have : IsIso (LocalCoefficientSystem.twistedCohomologyMap k M (Hom.fst f) L j) :=
        hfst.isIso_twistedCohomologyMap k M L (m := j) (by simp at hj; lia)
      -- Instance search does not identify this map with the goal's, which is read off the short
      -- complex, so the instance is passed by hand.
      exact @IsIso.epi_of_iso _ _ _ _ _ this)
    (fun j hj ↦ homologyMap_twistedCochainComplexShortComplexMap_τ₃_mem k M f L
      (.isomorphisms _) j (hsnd.isIso_twistedCohomologyMap k M _ (by simp at hj; lia)))
    (by
      rw [homologyMap_twistedCochainComplexShortComplexMap_τ₂]
      exact hfst.isIso_twistedCohomologyMap k M L hm)
    (homologyMap_twistedCochainComplexShortComplexMap_τ₃_mem k M f L (.monomorphisms _) m
      (hsnd.mono_twistedCohomologyMap k M _ (by lia)))
  rwa [twistedCochainComplexShortComplexMap_τ₁] at h

/-- **A map of pairs which is `n`-connected on the ambient spaces and `(n - 1)`-connected on the
subspaces induces monomorphisms on relative cohomology with local coefficients up to degree `n`**:
for a local coefficient system `L` on `Y` with projective fibres, the map
`H^m(Y, B; L, M) → H^m(X, A; f⁎L, M)` is a monomorphism for every `m ≤ n`. -/
theorem mono_twistedCohomologyMap_of_isNConnected (hfst : (Hom.fst f).hom.IsNConnected n)
    (hsnd : (Hom.snd f).hom.IsNConnected (n - 1)) {m : ℕ} (hm : m ≤ n) :
    Mono (TopPair.twistedCohomologyMap k M f L m) := by
  have h := HomologicalComplex.HomologySequence.mono_homologyMap_τ₁
    (twistedCochainComplexShortComplexMap k M f L)
    (P'.shortExact_twistedCochainComplexShortComplex L k M)
    (P.shortExact_twistedCochainComplexShortComplex _ k M) m
    (fun j hj ↦ by
      rw [homologyMap_twistedCochainComplexShortComplexMap_τ₂]
      have : IsIso (LocalCoefficientSystem.twistedCohomologyMap k M (Hom.fst f) L j) :=
        hfst.isIso_twistedCohomologyMap k M L (m := j) (by simp at hj; lia)
      -- Instance search does not identify this map with the goal's, which is read off the short
      -- complex, so the instance is passed by hand.
      exact @IsIso.epi_of_iso _ _ _ _ _ this)
    (fun j hj ↦ homologyMap_twistedCochainComplexShortComplexMap_τ₃_mem k M f L
      (.monomorphisms _) j (hsnd.mono_twistedCohomologyMap k M _ (by simp at hj; lia)))
    (by
      rw [homologyMap_twistedCochainComplexShortComplexMap_τ₂]
      exact hfst.mono_twistedCohomologyMap k M L hm)
  rwa [twistedCochainComplexShortComplexMap_τ₁] at h

end TopPair
