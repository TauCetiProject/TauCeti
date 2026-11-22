/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.ChainComplex
public import TauCeti.Topology.Category.TopCat.WeakEquivalence
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.HomotopyInvariance
import TauCeti.AlgebraicTopology.Singular.Cubical.Compression.Retraction
import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Compression
import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic

/-!
# Weak homotopy equivalences induce isomorphisms on singular homology

A weak homotopy equivalence `f : X → Y` induces a quasi-isomorphism of normalized cubical singular
chains, and isomorphisms `H_n(X; M) ≅ H_n(Y; M)` on singular homology with coefficients in any
module `M` over any ring `R`, in particular in any abelian group (`R = ℤ`) (Hatcher, *Algebraic
Topology*, Proposition 4.21). No CW structure on `X` or `Y` is needed. The carrier of `M` lies in
the universe of `X` and `Y`, as in the local-coefficient statement below; `R` may lie in any
universe.

The proof of the cubical statement factors `f` through its mapping cylinder `M_f` as

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

The same factorization proves the statement with local coefficients, at the level of chains: for
every local coefficient system `L` on `Y`, the map of singular chains from `X` with coefficients in
`f⁎L` to `Y` with coefficients in `L` is a chain homotopy equivalence, so
`H_n(X; f⁎L) ⟶ H_n(Y; L)` is an isomorphism. The bottom face of the mapping cylinder is handled by
the compression of cubical chains with local coefficients, a chain homotopy equivalence
(`TauCeti.SubspaceCubeDeformation.normalizedTwistedCubicalChainComplexHomotopyEquiv`), transported
to simplicial chains through the chain homotopy equivalence
`TauCeti.LocalCoefficientSystem.twistedCubicalSingularHomotopyEquiv`, which is natural in the
space. The other two factors are homotopy equivalences, which induce chain homotopy equivalences of
chains with local coefficients by homotopy invariance
(`ContinuousMap.HomotopyEquiv.homotopyEquivalences_twistedChainComplexMap`). No projectivity of
the fibres of `L` is needed.

Singular homology with coefficients in a module `M` is homology with local coefficients in the
constant system at `M` (`TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso`), compatibly
with maps of spaces
(`TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso_hom_space_naturality`), so the
statement for singular homology is the case of a constant system.

On simplicial singular chains with coefficients in any module, a weak homotopy equivalence
induces a chain homotopy equivalence, the case of a constant coefficient system. The five lemma
gives a quasi-isomorphism of relative chains for a map of pairs which is a weak homotopy
equivalence on the ambient spaces and on the subspaces, both with constant and with local
coefficients. With coefficients in a projective module, or local coefficients in a system with
projective fibres, the relative chain modules are projective
(`TopPair.projective_twistedChainComplex_X`), and a quasi-isomorphism of `ℕ`-graded complexes of
projectives is a chain homotopy equivalence (Mathlib's `ChainComplex.quasiIso_iff_of_projective`).
These chain homotopy equivalences are what the dual statements for singular cohomology are deduced
from, in `TauCeti.AlgebraicTopology.Cohomology.WeakHomotopyEquivalence`.

## Main results

* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_normalizedCubicalChainComplex_map`: a weak
  homotopy equivalence induces a quasi-isomorphism of normalized cubical chains.
* `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_twistedChainComplexMap`: a weak
  homotopy equivalence induces a chain homotopy equivalence of singular chains with local
  coefficients in any system.
* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_twistedChainComplexMap`,
  `ContinuousMap.IsWeakHomotopyEquivalence.isIso_twistedHomologyMap`: hence a quasi-isomorphism,
  and isomorphisms on homology with local coefficients.
* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_normalizedTwistedCubicalChainComplexMap`: the
  cubical form with local coefficients.
* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_subsetTwistedChainComplexMap`: an inclusion of
  subspaces which is a weak homotopy equivalence induces a quasi-isomorphism of twisted chains,
  with the local system restricted to each subspace.
* `ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularHomologyMap`: a weak homotopy
  equivalence induces isomorphisms on singular homology with coefficients in any module.
* `TauCeti.TopCat.weakEquivalences_isInvertedBy_singularHomologyFunctor`: the morphism-property
  form stating that `singularHomologyFunctor` with coefficients in any module inverts
  `TauCeti.TopCat.weakEquivalences`.
* `ContinuousMap.IsWeakHomotopyEquivalence.quasiIso_chainComplexMap`,
  `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquivalences_chainComplexMap`: the induced map
  of simplicial singular chains with coefficients in any module is a quasi-isomorphism and a chain
  homotopy equivalence.
* `TopPair.quasiIso_singularChainComplexMap_of_isWeakHomotopyEquivalence`,
  `TopPair.isIso_singularHomologyMap_of_isWeakHomotopyEquivalence`,
  `TopPair.homotopyEquivalences_singularChainComplexMap_of_isWeakHomotopyEquivalence`: the
  relative versions for maps of pairs, the last with projective coefficients.
* `TopPair.quasiIso_twistedChainComplexMap_of_isWeakHomotopyEquivalence`,
  `TopPair.isIso_twistedHomologyMap_of_isWeakHomotopyEquivalence`,
  `TopPair.homotopyEquivalences_twistedChainComplexMap_of_isWeakHomotopyEquivalence`: the
  relative versions with local coefficients, the last in a system with projective fibres.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.21, and Section 3.H for homology with local coefficients.
-/

public section

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

end ContinuousMap.IsWeakHomotopyEquivalence

/-! ### Local coefficients -/

namespace ContinuousMap.IsWeakHomotopyEquivalence

open LocalCoefficientSystem

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
  {R : Type u} [Ring R]

/-- **A weak homotopy equivalence induces a chain homotopy equivalence of singular chains with
local coefficients**: for every local coefficient system `L` on `Y`, the map of singular chain
complexes from `X` with coefficients in `f⁎L` to `Y` with coefficients in `L` is a chain homotopy
equivalence. No projectivity is assumed of the fibres of `L`. -/
theorem homotopyEquivalences_twistedChainComplexMap (hf : f.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) :
    HomologicalComplex.homotopyEquivalences _ _ (twistedChainComplexMap (TopCat.ofHom f) L) := by
  let W := HomologicalComplex.homotopyEquivalences (ModuleCat.{v} R) (ComplexShape.down ℕ)
  let A : Set (TopCat.of (MappingCylinder f)) := Set.range (MappingCylinder.incl f)
  let ψ : X ≃ₜ A := MappingCylinder.inclHomeomorph f
  let i : TopCat.of A ⟶ TopCat.of (MappingCylinder f) := TopCat.ofHom (ContinuousMap.subtypeVal A)
  let p := TopCat.ofHom (MappingCylinder.homotopyEquiv f).toFun
  -- The singular cubes of the mapping cylinder deform into the bottom face.
  have hi : W (twistedChainComplexMap i ((pullback p.hom).obj L)) :=
    homotopyEquivalences_twistedChainComplexMap_subtypeVal_of_relHomotopyGroup
      (MappingCylinder.exists_mem_range_incl_joined hf.exists_joined)
      (fun n ↦ hf.subsingleton_relHomotopyGroup_mappingCylinder (Fin n)) _
  -- The other two factors of `f`, the bottom face `X ≃ₜ A` and the projection, are homotopy
  -- equivalences.
  have hψ : W (twistedChainComplexMap (TopCat.ofHom ψ.toHomotopyEquiv.toFun)
      ((pullback (i ≫ p).hom).obj L)) :=
    ψ.toHomotopyEquiv.homotopyEquivalences_twistedChainComplexMap _
  have hp : W (twistedChainComplexMap p L) :=
    (MappingCylinder.homotopyEquiv f).homotopyEquivalences_twistedChainComplexMap L
  have hf' : TopCat.ofHom f = TopCat.ofHom ψ.toHomotopyEquiv.toFun ≫ i ≫ p := by
    ext x
    simp only [ψ, i, p, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
      ContinuousMap.subtypeVal_apply, MappingCylinder.homotopyEquiv_apply]
    exact (congrArg (· x) (MappingCylinder.proj_comp_subtypeVal_comp_inclHomeomorph (f := f))).symm
  rw [twistedChainComplexMap_congr _ _ hf', twistedChainComplexMap_comp,
    twistedChainComplexMap_comp]
  have hiso {K M : ChainComplex (ModuleCat.{v} R) ℕ} (g : K ⟶ M) [IsIso g] : W g :=
    HomologicalComplex.homotopyEquivalences.of_isIso g
  exact W.comp_mem _ _ (hiso _) <| W.comp_mem _ _ (hiso _) <| W.comp_mem _ _ hψ <|
    W.comp_mem _ _ (hiso _) <| W.comp_mem _ _ hi hp

/-- **A weak homotopy equivalence induces a quasi-isomorphism of singular chains with local
coefficients**: for every local coefficient system `L` on `Y`, the map of singular chain complexes
from `X` with coefficients in `f⁎L` to `Y` with coefficients in `L` is a quasi-isomorphism. -/
theorem quasiIso_twistedChainComplexMap (hf : f.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) :
    QuasiIso (twistedChainComplexMap (TopCat.ofHom f) L) :=
  (HomologicalComplex.mem_quasiIso_iff _).1 <| homotopyEquivalences_le_quasiIso _ _ _
    (hf.homotopyEquivalences_twistedChainComplexMap L)

/-- **A weak homotopy equivalence induces isomorphisms on singular homology with local
coefficients**, the local-coefficient form of Hatcher, Proposition 4.21: for every local
coefficient system `L` on `Y`, the map `H_n(X; f⁎L) ⟶ H_n(Y; L)` is an isomorphism. -/
theorem isIso_twistedHomologyMap (hf : f.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} R (TopCat.of Y)) (n : ℕ) :
    IsIso (twistedHomologyMap (TopCat.ofHom f) L n) :=
  have := hf.quasiIso_twistedChainComplexMap L
  inferInstance

/-- **An inclusion of subspaces which is a weak homotopy equivalence induces a quasi-isomorphism
of singular chains with local coefficients**: if `A ⊆ B ⊆ Z` and the inclusion of `A` in `B` is a
weak homotopy equivalence, then for every local coefficient system `L` on `Z` the map of twisted
chains of `A` and of `B`, with `L` restricted to each, is a quasi-isomorphism. -/
theorem quasiIso_subsetTwistedChainComplexMap {Z : TopCat.{v}} {A B : Set Z} {h : A ⊆ B}
    (hf : (ContinuousMap.inclusion h).IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} R Z) :
    QuasiIso (subsetTwistedChainComplexMap L h) := by
  have := hf.quasiIso_twistedChainComplexMap
    ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L)
  rw [subsetTwistedChainComplexMap_def]
  -- The change of coefficients starts at the pullback along `(subtypeVal B).comp (inclusion h)`,
  -- which is the pullback along `subtypeVal A` only after unfolding, so instance search cannot
  -- see that it is an isomorphism and the instance is given explicitly.
  exact quasiIso_comp (hφ := @quasiIso_of_isIso _ _ _ _ _ _ _ _
    (isIso_twistedChainComplexCoefficientMap _) _ _) _ _

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

/-! ### Singular homology with coefficients in a module -/

/-- **A weak homotopy equivalence induces isomorphisms on singular homology** with coefficients in
any module `M` over any ring `R`, in particular in any abelian group (`R = ℤ`) (Hatcher,
Proposition 4.21). The carrier of `M` lies in the universe of `X` and `Y`; `R` may lie in any
universe. This is the case of the constant coefficient system at `M` in
`isIso_twistedHomologyMap`. -/
theorem isIso_singularHomologyMap (hf : f.IsWeakHomotopyEquivalence) (M : ModuleCat.{v} R)
    (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{v} R) n).obj M).map (TopCat.ofHom f)) := by
  have := hf.isIso_twistedHomologyMap ((constantFunctor (TopCat.of Y)).obj M) n
  have : IsIso (twistedHomologyMap (TopCat.ofHom f) ((constantFunctor (TopCat.of Y)).obj M) n ≫
      (twistedHomologyConstantIso (TopCat.of Y) M n).hom) := inferInstance
  rwa [twistedHomologyConstantIso_hom_space_naturality, isIso_comp_left_iff,
    isIso_comp_left_iff] at this

end ContinuousMap.IsWeakHomotopyEquivalence

namespace TauCeti.TopCat

/-- Singular homology with coefficients in any module `M` inverts weak homotopy equivalences
(`TauCeti.TopCat.weakEquivalences`). -/
theorem weakEquivalences_isInvertedBy_singularHomologyFunctor {R : Type u} [Ring R]
    (M : ModuleCat.{v} R) (n : ℕ) :
    weakEquivalences.{v}.IsInvertedBy ((singularHomologyFunctor (ModuleCat.{v} R) n).obj M) :=
  fun _ _ _ hf ↦ ((mem_weakEquivalences_iff _).1 hf).isIso_singularHomologyMap M n

end TauCeti.TopCat

/-! ### Simplicial singular chains and chain homotopy equivalences -/

namespace ContinuousMap.IsWeakHomotopyEquivalence

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
  {A : Type u} [Ring A]

/-- **A weak homotopy equivalence induces a quasi-isomorphism of singular chains** with
coefficients in any module `R`. -/
theorem quasiIso_chainComplexMap (hf : f.IsWeakHomotopyEquivalence) (R : ModuleCat.{v} A) :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) R) :=
  (quasiIso_iff _).2 fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2
    (hf.isIso_singularHomologyMap R n)

open LocalCoefficientSystem in
/-- **A weak homotopy equivalence induces a chain homotopy equivalence of singular chains** with
coefficients in any module `R`. This is the case of the constant coefficient system at `R` in
`homotopyEquivalences_twistedChainComplexMap`. -/
theorem homotopyEquivalences_chainComplexMap (hf : f.IsWeakHomotopyEquivalence)
    (R : ModuleCat.{v} A) :
    HomologicalComplex.homotopyEquivalences _ _
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) R) := by
  let W := HomologicalComplex.homotopyEquivalences (ModuleCat.{v} A) (ComplexShape.down ℕ)
  have hiso {K M : ChainComplex (ModuleCat.{v} A) ℕ} (g : K ⟶ M) [IsIso g] : W g :=
    HomologicalComplex.homotopyEquivalences.of_isIso g
  have h := W.comp_mem _ _
    (hf.homotopyEquivalences_twistedChainComplexMap ((constantFunctor (TopCat.of Y)).obj R))
    (hiso (twistedChainComplexConstantIso (TopCat.of Y) R).hom)
  rw [twistedChainComplexConstantIso_hom_space_naturality, ← Category.assoc] at h
  exact W.of_precomp (W' := W) _ _
    (W.comp_mem _ _ (hiso _) (hiso (twistedChainComplexConstantIso (TopCat.of X) R).hom)) h

end ContinuousMap.IsWeakHomotopyEquivalence

/-! ### Pairs of spaces -/

namespace TopPair

variable {P P' : TopPair.{v}} (f : P ⟶ P') {A : Type u} [Ring A]

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces a quasi-isomorphism of relative singular chains**, with coefficients in any
module `R`. -/
theorem quasiIso_singularChainComplexMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) (R : ModuleCat.{v} A) :
    QuasiIso (singularChainComplexMap f R) := by
  have : QuasiIso (SSet.chainComplexMap (toSSetPair.map f).left R) := by
    rw [toSSetPair_map_left]
    exact hsnd.quasiIso_chainComplexMap R
  have : QuasiIso (SSet.chainComplexMap (toSSetPair.map f).right R) := by
    rw [toSSetPair_map_right]
    exact hfst.quasiIso_chainComplexMap R
  exact SSetPair.quasiIso_chainComplexMap _ R

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces isomorphisms on relative singular homology** with coefficients in any module. -/
theorem isIso_singularHomologyMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) (R : ModuleCat.{v} A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap f R n) :=
  have := quasiIso_singularChainComplexMap_of_isWeakHomotopyEquivalence f hfst hsnd R
  inferInstanceAs (IsIso (HomologicalComplex.homologyMap (singularChainComplexMap f R) n))

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces a chain homotopy equivalence of relative singular chains** with coefficients in
a projective module. -/
theorem homotopyEquivalences_singularChainComplexMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence) (R : ModuleCat.{v} A) [Projective R] :
    HomologicalComplex.homotopyEquivalences _ _ (singularChainComplexMap f R) :=
  have := quasiIso_singularChainComplexMap_of_isWeakHomotopyEquivalence f hfst hsnd R
  (ChainComplex.quasiIso_iff_of_projective _).1 this

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces a quasi-isomorphism of relative singular chains with local coefficients**: for
every local coefficient system `L` on the ambient space of the target, the map from the relative
twisted chains of `P` with coefficients in the pullback of `L` to those of `P'` with coefficients
in `L` is a quasi-isomorphism. -/
theorem quasiIso_twistedChainComplexMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} A P'.fst) :
    QuasiIso (TopPair.twistedChainComplexMap f L) := by
  -- The absolute statements are about `TopCat.ofHom (Hom.snd f).hom` and systems on
  -- `TopCat.of P'.snd`; the ascriptions restate them for `Hom.snd f` and `P'.snd`.
  have hsnd₀ : QuasiIso (LocalCoefficientSystem.twistedChainComplexMap (Hom.snd f)
      (P'.subspaceSystem L)) := hsnd.quasiIso_twistedChainComplexMap (P'.subspaceSystem L)
  have hfst' : QuasiIso (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L) :=
    hfst.quasiIso_twistedChainComplexMap L
  exact quasiIso_twistedChainComplexMap_of_quasiIso f L

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces isomorphisms on relative singular homology with local coefficients**: for every
local coefficient system `L` on the ambient space of the target,
`H_n(X, A; f⁎L) ⟶ H_n(X', A'; L)` is an isomorphism. -/
theorem isIso_twistedHomologyMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} A P'.fst) (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap f L n) :=
  have := quasiIso_twistedChainComplexMap_of_isWeakHomotopyEquivalence f hfst hsnd L
  inferInstance

/-- **A map of pairs which is a weak homotopy equivalence on the ambient spaces and on the
subspaces induces a chain homotopy equivalence of relative singular chains with local
coefficients** in a local coefficient system `L` whose fibres are projective. -/
theorem homotopyEquivalences_twistedChainComplexMap_of_isWeakHomotopyEquivalence
    (hfst : (Hom.fst f).hom.IsWeakHomotopyEquivalence)
    (hsnd : (Hom.snd f).hom.IsWeakHomotopyEquivalence)
    (L : LocalCoefficientSystem.{u, v, v} A P'.fst) [∀ y, Projective (L.obj y)] :
    HomologicalComplex.homotopyEquivalences _ _ (TopPair.twistedChainComplexMap f L) :=
  (ChainComplex.quasiIso_iff_of_projective _).1
    (quasiIso_twistedChainComplexMap_of_isWeakHomotopyEquivalence f hfst hsnd L)

end TopPair
