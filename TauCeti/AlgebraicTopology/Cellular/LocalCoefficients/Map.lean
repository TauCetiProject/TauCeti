/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Homology
public import TauCeti.AlgebraicTopology.Cellular.Map
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality

/-!
# Cellular maps act on cellular chains with local coefficients

Let `f : C ⟶ C'` be a cellular map between relative CW complexes, so that `f` carries each
skeleton `Xⁿ` of `C` into the skeleton `X'ⁿ` of `C'`, and let `L` be a local coefficient system
on `C'`. Restricting `f` to the skeletal pairs and pulling `L` back along `f` gives maps

`Hₙ(Xⁿ, Xⁿ⁻¹; f*L) ⟶ Hₙ(X'ⁿ, X'ⁿ⁻¹; L)`

of cellular chain groups with local coefficients (`TauCeti.twistedCellularChainGroupMap`). They
commute with the cellular differentials
(`TauCeti.twistedCellularChainGroupMap_comp_twistedCellularDifferential`), so they form a chain map
`TauCeti.twistedCellularChainComplexMap` from the cellular chain complex of `C` with coefficients in
`f*L` to that of `C'` with coefficients in `L`. It is the local-coefficient form of
`TauCeti.cellularChainComplexMap`.

The identification of cellular homology with twisted singular homology is natural for these maps
(`TauCeti.twistedCellularSingularHomologyIso_hom_naturality`): the map induced on cellular homology
corresponds to the map `Hₙ(C, X⁻¹; f*L) ⟶ Hₙ(C', X'⁻¹; L)` induced by `f` on the twisted homology
of the complexes relative to their bases (`TauCeti.twistedHomologyComplexBasePairMap`). The same
holds for the identification of the cellular cycles with `Hₙ(Xⁿ, X⁻¹; L)`
(`TauCeti.twistedCellularCyclesIso_hom_naturality`). With coefficients in the local system of fibre
homology of a fibration over a CW complex, cellular homology computes the groups `H_p(B; H_q(F))`
of the second page of its Serre spectral sequence, and this is their naturality in the base.

The proof checks each step of the identification. The cellular differential is the connecting
morphism of the pair `(Xⁿ⁺¹, Xⁿ)` followed by the quotient to `(Xⁿ, Xⁿ⁻¹)`, and both are natural in
maps of pairs. Restricted to the skeleta, the pullback of `f*L` and that of `L` along the
restriction of `f` agree (`TauCeti.skeletonSystem_pullback_obj`), so the coefficients are matched by
equalities of local systems.

## Main definitions

* `TauCeti.twistedCellularChainGroupMap`: the map of cellular chain groups with local coefficients
  induced by a cellular map.
* `TauCeti.twistedCellularChainComplexMap`: the chain map they form.
* `TauCeti.twistedHomologySkeletonBasePairMap`, `TauCeti.twistedHomologyComplexBasePairMap`: the
  maps induced on twisted homology of the skeleta and of the whole complexes, relative to the base.

## Main results

* `TauCeti.twistedCellularChainGroupMap_comp_twistedCellularDifferential`: the maps of cellular
  chain groups commute with the cellular differentials.
* `TauCeti.twistedCellularChainGroupMap_id`, `TauCeti.twistedCellularChainGroupMap_comp`, and the
  same laws for `TauCeti.twistedHomologySkeletonBasePairMap` and
  `TauCeti.twistedHomologyComplexBasePairMap`: the identity and composition laws, with the pullbacks
  along the identity and along a composite matched by equalities of local systems.
* `TauCeti.twistedCellularCyclesIso_hom_naturality`: the identification of cellular cycles with
  `Hₙ(Xⁿ, X⁻¹; L)` is natural.
* `TauCeti.twistedCellularSingularHomologyIso_hom_naturality`: the identification of cellular
  homology with local coefficients with twisted singular homology is natural in cellular maps.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Theorem 2.35 and the cellular maps following it,
  and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

open LocalCoefficientSystem

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
  {R : Type u} [Ring R] (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C'))

/-! ### Matching the coefficient systems -/

/-- Restricting the pullback `f*L` to the `m`-th stage of the skeletal filtration of `C` is pulling
back the restriction of `L` to the `m`-th stage of `C'` along the restriction of `f`. -/
lemma skeletonSystem_pullback_obj (m : ℕ) :
    skeletonSystem C ((pullback f.hom).obj L) m =
      (pullback (skeletonMap C C' hf m).hom).obj (skeletonSystem C' L m) := by
  have h := congrArg TopCat.Hom.hom (skeletonMap_comp_inclusion_complex C C' hf m)
  simp only [TopCat.hom_comp, TopCat.hom_ofHom] at h
  -- Both systems are composites of the fundamental groupoid maps with `L`; `change` unfolds the
  -- pullback functors, which have no lemma rewriting `pullback g ⋙ pullback f` as an equality.
  change FundamentalGroupoid.map _ ⋙ (FundamentalGroupoid.map _ ⋙ L) =
    FundamentalGroupoid.map _ ⋙ (FundamentalGroupoid.map _ ⋙ L)
  rw [← Functor.assoc, ← Functor.assoc, ← FundamentalGroupoid.map_comp,
    ← FundamentalGroupoid.map_comp, h]

/-- `TauCeti.skeletonSystem_pullback_obj` for the ambient component of a skeletal pair map. -/
lemma skeletonSystem_pullback_obj_eq_pullback_skeletonPairMap (n : ℕ) :
    skeletonSystem C ((pullback f.hom).obj L) (n + 1) =
      (pullback (TopPair.Hom.fst (skeletonPairMap C C' hf n)).hom).obj
        (skeletonSystem C' L (n + 1)) := by
  rw [skeletonPairMap_fst]
  exact skeletonSystem_pullback_obj C C' hf L (n + 1)

/-- `TauCeti.skeletonSystem_pullback_obj` for the ambient component of a map of skeleta relative to
the base. -/
lemma skeletonSystem_pullback_obj_eq_pullback_skeletonBasePairMap (n : ℕ) :
    skeletonSystem C ((pullback f.hom).obj L) (n + 1) =
      (pullback (TopPair.Hom.fst (skeletonBasePairMap C C' hf n)).hom).obj
        (skeletonSystem C' L (n + 1)) := by
  rw [skeletonBasePairMap_fst]
  exact skeletonSystem_pullback_obj C C' hf L (n + 1)

/-- The pullback `f*L` is the pullback of `L` along the ambient component of the map of the whole
complexes relative to their bases. -/
lemma pullback_obj_eq_pullback_complexBasePairMap :
    (pullback f.hom).obj L =
      (pullback (TopPair.Hom.fst (complexBasePairMap C C' hf)).hom).obj L := by
  rw [complexBasePairMap_fst]
  -- `(complexBasePair C).fst` is `TopCat.of C` by definition.
  rfl

/-! ### The chain map -/

/-- The map `Hₙ(Xⁿ, Xⁿ⁻¹; f*L) ⟶ Hₙ(X'ⁿ, X'ⁿ⁻¹; L)` of cellular chain groups with local coefficients
induced by a cellular map `f`. -/
def twistedCellularChainGroupMap (n : ℕ) :
    twistedCellularChainGroup C ((pullback f.hom).obj L) n ⟶ twistedCellularChainGroup C' L n :=
  (skeletonPair C n).twistedHomologyCoefficientMap
      (eqToHom (skeletonSystem_pullback_obj_eq_pullback_skeletonPairMap C C' hf L n)) n ≫
    TopPair.twistedHomologyMap (skeletonPairMap C C' hf n) (skeletonSystem C' L (n + 1)) n

/-- The map of cellular chain groups is the relative twisted homology map of the skeletal pair map,
after matching the coefficient systems. -/
lemma twistedCellularChainGroupMap_def (n : ℕ) :
    twistedCellularChainGroupMap C C' hf L n =
      (skeletonPair C n).twistedHomologyCoefficientMap
          (eqToHom (skeletonSystem_pullback_obj_eq_pullback_skeletonPairMap C C' hf L n)) n ≫
        TopPair.twistedHomologyMap (skeletonPairMap C C' hf n) (skeletonSystem C' L (n + 1)) n :=
  (rfl)

section Generic

variable {P Q : TopPair.{w}} (g : P ⟶ Q) {s : P.fst ⟶ Q.fst} (hs : s = TopPair.Hom.fst g)
  {N N₀ N₁ : LocalCoefficientSystem.{u, w, max w v} R P.fst}
  {M S : LocalCoefficientSystem.{u, w, max w v} R Q.fst}

/-- The step of the comparison of cellular differentials after the connecting morphisms: a map of
twisted homology of ambient spaces, followed by the quotient to a relative group, is the quotient
followed by the relative map. It is stated for an arbitrary map of pairs and an arbitrary map `s`
equal to its ambient component, so that it applies to the restriction of a cellular map to the
subspace of the pair `(Xⁿ⁺¹, Xⁿ)`, which is the ambient space of `(Xⁿ, Xⁿ⁻¹)` only after
unfolding the skeletal pairs. -/
private lemma twistedHomologyMap_comp_twistedHomologyπ_comp_coefficientMap
    (a₁ : N ⟶ N₀) (a₂ : N₀ ⟶ (pullback s.hom).obj M) (c : M ⟶ S)
    (γ₁ : N ⟶ N₁) (γ₂ : N₁ ⟶ (pullback (TopPair.Hom.fst g).hom).obj S)
    (hγ : γ₁ ≫ γ₂ = a₁ ≫ a₂ ≫ (pullback s.hom).map c ≫
      eqToHom (congrArg (fun t : P.fst ⟶ Q.fst ↦ (pullback t.hom).obj S) hs)) (k : ℕ) :
    twistedHomologyCoefficientMap a₁ k ≫ twistedHomologyCoefficientMap a₂ k ≫
        twistedHomologyMap s M k ≫ Q.twistedHomologyπ M k ≫ Q.twistedHomologyCoefficientMap c k =
      P.twistedHomologyπ N k ≫ P.twistedHomologyCoefficientMap γ₁ k ≫
        P.twistedHomologyCoefficientMap γ₂ k ≫ TopPair.twistedHomologyMap g S k := by
  subst hs
  rw [TopPair.twistedHomologyπ_naturality_assoc, TopPair.twistedHomologyMap_naturality,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc, hγ]
  simp

end Generic

/-- **The maps of cellular chain groups induced by a cellular map commute with the cellular
differentials with local coefficients.** -/
@[reassoc]
lemma twistedCellularChainGroupMap_comp_twistedCellularDifferential (n : ℕ) :
    twistedCellularChainGroupMap C C' hf L (n + 1) ≫ twistedCellularDifferential C' L n =
      twistedCellularDifferential C ((pullback f.hom).obj L) n ≫
        twistedCellularChainGroupMap C C' hf L n := by
  rw [twistedCellularDifferential_eq_twistedHomologyδ_comp_twistedHomologyπ,
    twistedCellularDifferential_eq_twistedHomologyδ_comp_twistedHomologyπ,
    twistedCellularChainGroupMap, twistedCellularChainGroupMap]
  -- Move the coefficient identification and the map of pairs `(Xⁿ⁺¹, Xⁿ)` past the connecting
  -- morphisms, so that both sides start with the connecting morphism for `C`.
  have hδ := TopPair.twistedHomologyδ_naturality (skeletonPairMap C C' hf (n + 1))
    (skeletonSystem C' L (n + 1 + 1)) (n + 1) n rfl
  have h₁ := TopPair.twistedHomologyδ_naturality_coefficient (skeletonPair C (n + 1))
    (eqToHom (skeletonSystem_pullback_obj_eq_pullback_skeletonPairMap C C' hf L (n + 1)))
    (n + 1) n rfl
  simp only [Category.assoc]
  -- The skeletal pairs agree with the pairs of the lemmas above only after unfolding them, so
  -- `erw` is needed to rewrite.
  erw [← reassoc_of% hδ, ← reassoc_of% h₁]
  congr 1
  -- The subspace component of the map of `(Xⁿ⁺¹, Xⁿ)` is the ambient component of that of
  -- `(Xⁿ, Xⁿ⁻¹)`; the remaining coefficient maps identify fibres of `L` over equal points.
  have e : TopPair.Hom.snd (skeletonPairMap C C' hf (n + 1)) =
      TopPair.Hom.fst (skeletonPairMap C C' hf n) :=
    (skeletonPairMap_snd C C' hf (n + 1)).trans (skeletonPairMap_fst C C' hf n).symm
  refine (twistedHomologyMap_comp_twistedHomologyπ_comp_coefficientMap
    (skeletonPairMap C C' hf n) e _ _ (skeletonPairSubspaceSystemIso C' L (n + 1)).hom
    (skeletonPairSubspaceSystemIso C ((pullback f.hom).obj L) (n + 1)).hom
    (eqToHom (skeletonSystem_pullback_obj_eq_pullback_skeletonPairMap C C' hf L n)) ?_ n).trans
    (Category.assoc _ _ _).symm
  ext x : 2
  -- The composites of whiskered functors are matched only up to unfolding, so the components are
  -- computed with `erw`.
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    skeletonPairSubspaceSystemIso_hom_app, pullback_map_app, pullback_map_app,
    TopPair.subspaceSystemPullbackIso_hom_app, skeletonPairSubspaceSystemIso_hom_app,
    eqToHom_app, eqToHom_app, eqToHom_app, Category.id_comp, Category.id_comp, eqToHom_trans,
    eqToHom_trans]
  -- Both sides are now identifications of the same two fibres of `L`, stated over the skeletal
  -- pairs and their unfoldings, so they agree definitionally.
  rfl

/-- **A cellular map induces a chain map of cellular chain complexes with local coefficients**,
from the complex of `C` with coefficients in `f*L` to that of `C'` with coefficients in `L`. -/
def twistedCellularChainComplexMap :
    twistedCellularChainComplex C ((pullback f.hom).obj L) ⟶ twistedCellularChainComplex C' L :=
  ChainComplex.ofHom (fun n ↦
    eqToHom (twistedCellularChainComplex_X C _ n) ≫ twistedCellularChainGroupMap C C' hf L n ≫
      eqToHom (twistedCellularChainComplex_X C' L n).symm)
    (by
      intro n
      simp only [twistedCellularChainComplex_d, Category.assoc]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      simpa only [Category.assoc] using congrArg
        (fun a ↦ eqToHom (twistedCellularChainComplex_X C ((pullback f.hom).obj L) (n + 1)) ≫ a ≫
          eqToHom (twistedCellularChainComplex_X C' L n).symm)
        (twistedCellularChainGroupMap_comp_twistedCellularDifferential C C' hf L n))

/-- The components of the cellular chain map are the maps of cellular chain groups, transported
across `TauCeti.twistedCellularChainComplex_X`. -/
@[simp]
lemma twistedCellularChainComplexMap_f (n : ℕ) :
    (twistedCellularChainComplexMap C C' hf L).f n =
      eqToHom (twistedCellularChainComplex_X C _ n) ≫ twistedCellularChainGroupMap C C' hf L n ≫
        eqToHom (twistedCellularChainComplex_X C' L n).symm := (rfl)

/-! ### Naturality of the comparison with twisted singular homology -/

/-- The map `Hₖ(Xⁿ, X⁻¹; f*L) ⟶ Hₖ(X'ⁿ, X'⁻¹; L)` of the twisted homology of the skeleta relative to
the bases induced by a cellular map `f`. -/
def twistedHomologySkeletonBasePairMap (n k : ℕ) :
    (skeletonBasePair C n).twistedHomology (skeletonSystem C ((pullback f.hom).obj L) (n + 1)) k ⟶
      (skeletonBasePair C' n).twistedHomology (skeletonSystem C' L (n + 1)) k :=
  (skeletonBasePair C n).twistedHomologyCoefficientMap
      (eqToHom (skeletonSystem_pullback_obj_eq_pullback_skeletonBasePairMap C C' hf L n)) k ≫
    TopPair.twistedHomologyMap (skeletonBasePairMap C C' hf n) (skeletonSystem C' L (n + 1)) k

/-- The map of the twisted homology of the skeleta relative to the bases is the relative twisted
homology map of the restriction of `f`, after matching the coefficient systems. -/
lemma twistedHomologySkeletonBasePairMap_def (n k : ℕ) :
    twistedHomologySkeletonBasePairMap C C' hf L n k =
      (skeletonBasePair C n).twistedHomologyCoefficientMap
          (eqToHom (skeletonSystem_pullback_obj_eq_pullback_skeletonBasePairMap C C' hf L n)) k ≫
        TopPair.twistedHomologyMap (skeletonBasePairMap C C' hf n)
          (skeletonSystem C' L (n + 1)) k :=
  (rfl)

/-- The map `Hₖ(C, X⁻¹; f*L) ⟶ Hₖ(C', X'⁻¹; L)` of the twisted homology of the complexes relative to
their bases induced by a cellular map `f`. -/
def twistedHomologyComplexBasePairMap (k : ℕ) :
    (complexBasePair C).twistedHomology ((pullback f.hom).obj L) k ⟶
      (complexBasePair C').twistedHomology L k :=
  (complexBasePair C).twistedHomologyCoefficientMap
      (eqToHom (pullback_obj_eq_pullback_complexBasePairMap C C' hf L)) k ≫
    TopPair.twistedHomologyMap (complexBasePairMap C C' hf) L k

/-- The map of the twisted homology of the complexes relative to their bases is the relative
twisted homology map of `f`, after matching the coefficient systems. -/
lemma twistedHomologyComplexBasePairMap_def (k : ℕ) :
    twistedHomologyComplexBasePairMap C C' hf L k =
      (complexBasePair C).twistedHomologyCoefficientMap
          (eqToHom (pullback_obj_eq_pullback_complexBasePairMap C C' hf L)) k ≫
        TopPair.twistedHomologyMap (complexBasePairMap C C' hf) L k :=
  (rfl)

/-! ### Identity and composition laws -/

/-- The identity cellular map acts on the cellular chain groups with local coefficients as the
identification of the pullback of `L` along the identity with `L`. -/
@[simp]
lemma twistedCellularChainGroupMap_id (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C))
    (n : ℕ) :
    twistedCellularChainGroupMap C C (isCellular_id C) L n =
      (skeletonPair C n).twistedHomologyCoefficientMap
        (eqToHom (congrArg (skeletonSystem C · (n + 1)) (pullback_obj_id _ L))) n :=
  TopPair.twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_id _ (skeletonPairMap_id C n)
    _ _ n

/-- The identity cellular map acts on the twisted homology of the skeleta relative to the base as
the identification of the pullback of `L` along the identity with `L`. -/
@[simp]
lemma twistedHomologySkeletonBasePairMap_id
    (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C)) (n k : ℕ) :
    twistedHomologySkeletonBasePairMap C C (isCellular_id C) L n k =
      (skeletonBasePair C n).twistedHomologyCoefficientMap
        (eqToHom (congrArg (skeletonSystem C · (n + 1)) (pullback_obj_id _ L))) k :=
  TopPair.twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_id _
    (skeletonBasePairMap_id C n) _ _ k

/-- The identity cellular map acts on the twisted homology of the complex relative to its base as
the identification of the pullback of `L` along the identity with `L`. -/
@[simp]
lemma twistedHomologyComplexBasePairMap_id
    (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C)) (k : ℕ) :
    twistedHomologyComplexBasePairMap C C (isCellular_id C) L k =
      (complexBasePair C).twistedHomologyCoefficientMap (eqToHom (pullback_obj_id _ L)) k :=
  TopPair.twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_id _ (complexBasePairMap_id C)
    _ _ k

section Comp

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] {F : Set Z}
  (C'' : Set Z) [RelCWComplex C'' F]
  {g : TopCat.of C' ⟶ TopCat.of C''} (hg : IsCellular C' C'' g)

/-- The maps of cellular chain groups with local coefficients respect composition of cellular
maps, once the pullback of `L` along the composite is identified with the iterated pullback. -/
@[reassoc]
lemma twistedCellularChainGroupMap_comp
    (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C'')) (n : ℕ) :
    (skeletonPair C n).twistedHomologyCoefficientMap (eqToHom (congrArg (skeletonSystem C · (n + 1))
        (pullback_obj_comp f.hom g.hom L).symm)) n ≫
      twistedCellularChainGroupMap C C'' (IsCellular.comp C C' hf hg) L n =
    twistedCellularChainGroupMap C C' hf ((pullback g.hom).obj L) n ≫
      twistedCellularChainGroupMap C' C'' hg L n :=
  TopPair.twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_comp _ _ _
    (skeletonPairMap_comp C C' hf C'' hg n) _ _ _ _ n

/-- The maps of the twisted homology of the skeleta relative to the bases respect composition of
cellular maps, once the pullback of `L` along the composite is identified with the iterated
pullback. -/
@[reassoc]
lemma twistedHomologySkeletonBasePairMap_comp
    (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C'')) (n k : ℕ) :
    (skeletonBasePair C n).twistedHomologyCoefficientMap
        (eqToHom (congrArg (skeletonSystem C · (n + 1))
          (pullback_obj_comp f.hom g.hom L).symm)) k ≫
      twistedHomologySkeletonBasePairMap C C'' (IsCellular.comp C C' hf hg) L n k =
    twistedHomologySkeletonBasePairMap C C' hf ((pullback g.hom).obj L) n k ≫
      twistedHomologySkeletonBasePairMap C' C'' hg L n k :=
  TopPair.twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_comp _ _ _
    (skeletonBasePairMap_comp C C' hf C'' hg n) _ _ _ _ k

/-- The maps of the twisted homology of the complexes relative to their bases respect composition
of cellular maps, once the pullback of `L` along the composite is identified with the iterated
pullback. -/
@[reassoc]
lemma twistedHomologyComplexBasePairMap_comp
    (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C'')) (k : ℕ) :
    (complexBasePair C).twistedHomologyCoefficientMap
        (eqToHom (pullback_obj_comp f.hom g.hom L).symm) k ≫
      twistedHomologyComplexBasePairMap C C'' (IsCellular.comp C C' hf hg) L k =
    twistedHomologyComplexBasePairMap C C' hf ((pullback g.hom).obj L) k ≫
      twistedHomologyComplexBasePairMap C' C'' hg L k :=
  TopPair.twistedHomologyCoefficientMap_comp_twistedHomologyMap_of_eq_comp _ _ _
    (complexBasePairMap_comp C C' hf C'' hg) _ _ _ _ k

end Comp

/-- The map `Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` commutes with the maps induced by a cellular map. -/
@[reassoc]
lemma twistedCellularCyclesι_naturality (n : ℕ) :
    twistedCellularCyclesι C ((pullback f.hom).obj L) n ≫ twistedCellularChainGroupMap C C' hf L n =
      twistedHomologySkeletonBasePairMap C C' hf L n n ≫ twistedCellularCyclesι C' L n := by
  cases n with
  | zero =>
    rw [twistedCellularCyclesι_zero, twistedCellularCyclesι_zero, Category.id_comp,
      Category.comp_id, twistedCellularChainGroupMap, twistedHomologySkeletonBasePairMap]
    -- In degree `0` the skeletal pair and the skeletal pair relative to the base coincide only
    -- after unfolding them, so `erw` is needed to rewrite.
    have hg := (skeletonPairMap_fst C C' hf 0).trans (skeletonBasePairMap_fst C C' hf 0).symm
    erw [TopPair.twistedHomologyMap_congr (f := skeletonPairMap C C' hf 0) _ hg,
      ← TopPair.twistedHomologyCoefficientMap_comp_assoc, eqToHom_trans]
  | succ n =>
    rw [twistedCellularCyclesι_succ, twistedCellularCyclesι_succ, twistedCellularChainGroupMap,
      twistedHomologySkeletonBasePairMap]
    exact (TopTriple.twistedHomologyTotalToOuter_naturality_of_fst_eq
      (T := skeletonBaseTriple C n) (T' := skeletonBaseTriple C' n) _
      (skeletonPairMap C C' hf (n + 1)) (skeletonBasePairMap C C' hf (n + 1))
      ((skeletonBasePairMap_fst C C' hf (n + 1)).trans (skeletonPairMap_fst C C' hf (n + 1)).symm)
      _ _ (eqToHom_trans _ _) (n + 1)).trans (Category.assoc _ _ _).symm

/-- The map `Hₖ(Xⁿ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)` induced by the inclusion of the skeleton commutes with
the maps induced by a cellular map. -/
@[reassoc]
lemma twistedHomologySkeletonBasePairToComplex_naturality (n k : ℕ) :
    twistedHomologySkeletonBasePairToComplex C ((pullback f.hom).obj L) n k ≫
        twistedHomologyComplexBasePairMap C C' hf L k =
      twistedHomologySkeletonBasePairMap C C' hf L n k ≫
        twistedHomologySkeletonBasePairToComplex C' L n k := by
  rw [twistedHomologySkeletonBasePairToComplex_def, twistedHomologySkeletonBasePairToComplex_def,
    twistedHomologyComplexBasePairMap, twistedHomologySkeletonBasePairMap]
  have hw := congrArg TopPair.Hom.fst (skeletonBasePairMap_comp_toComplex C C' hf n)
  rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp] at hw
  exact (Category.assoc _ _ _).trans
    ((TopPair.twistedHomologyMap_comp_twistedHomologyMap_eq_of_fst_comp_eq
      (P := skeletonBasePair C n) (P' := complexBasePair C) (Q' := skeletonBasePair C' n)
      (Q := complexBasePair C') (skeletonBasePairToComplex C n) (complexBasePairMap C C' hf)
      (skeletonBasePairMap C C' hf n) (skeletonBasePairToComplex C' n) hw.symm _ _ _ _ k).trans
      (Category.assoc _ _ _).symm)

/-- The identification of the cellular cycles with local coefficients with `Hₙ(Xⁿ, X⁻¹; L)` is
natural in cellular maps. -/
@[reassoc]
lemma twistedCellularCyclesIso_hom_naturality (n : ℕ) :
    HomologicalComplex.cyclesMap (twistedCellularChainComplexMap C C' hf L) n ≫
        (twistedCellularCyclesIso C' L n).hom =
      (twistedCellularCyclesIso C ((pullback f.hom).obj L) n).hom ≫
        twistedHomologySkeletonBasePairMap C C' hf L n n := by
  apply (cancel_epi (twistedCellularCyclesIso C ((pullback f.hom).obj L) n).inv).1
  apply (cancel_mono ((twistedCellularCyclesIso C' L n).inv ≫
    (twistedCellularChainComplex C' L).iCycles n)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [HomologicalComplex.cyclesMap_i, twistedCellularCyclesIso_inv_comp_iCycles_assoc,
    twistedCellularCyclesIso_inv_comp_iCycles, twistedCellularChainComplexMap_f]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [twistedCellularCyclesι_naturality_assoc]

/-- The inverse identification of `Hₙ(Xⁿ, X⁻¹; L)` with the cellular cycles with local
coefficients is natural in cellular maps. -/
@[reassoc]
lemma twistedCellularCyclesIso_inv_naturality (n : ℕ) :
    twistedHomologySkeletonBasePairMap C C' hf L n n ≫ (twistedCellularCyclesIso C' L n).inv =
      (twistedCellularCyclesIso C ((pullback f.hom).obj L) n).inv ≫
        HomologicalComplex.cyclesMap (twistedCellularChainComplexMap C C' hf L) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (twistedCellularCyclesIso_hom_naturality C C' hf L n).symm

/-- **Cellular homology with local coefficients is naturally twisted singular homology**: under
the identifications `TauCeti.twistedCellularSingularHomologyIso`, the map induced on cellular
homology by a cellular map `f` is the map `Hₙ(C, X⁻¹; f*L) ⟶ Hₙ(C', X'⁻¹; L)` induced by `f`. -/
@[reassoc]
theorem twistedCellularSingularHomologyIso_hom_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (twistedCellularChainComplexMap C C' hf L) n ≫
        (twistedCellularSingularHomologyIso C' L n).hom =
      (twistedCellularSingularHomologyIso C ((pullback f.hom).obj L) n).hom ≫
        twistedHomologyComplexBasePairMap C C' hf L n := by
  apply (cancel_epi ((twistedCellularChainComplex C ((pullback f.hom).obj L)).homologyπ n)).1
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_comp_twistedCellularSingularHomologyIso_hom,
    homologyπ_comp_twistedCellularSingularHomologyIso_hom_assoc,
    twistedCellularCyclesIso_hom_naturality_assoc,
    twistedHomologySkeletonBasePairToComplex_naturality]

/-- The inverse identification of twisted singular homology with cellular homology with local
coefficients is natural in cellular maps. -/
@[reassoc]
theorem twistedCellularSingularHomologyIso_inv_naturality (n : ℕ) :
    twistedHomologyComplexBasePairMap C C' hf L n ≫
        (twistedCellularSingularHomologyIso C' L n).inv =
      (twistedCellularSingularHomologyIso C ((pullback f.hom).obj L) n).inv ≫
        HomologicalComplex.homologyMap (twistedCellularChainComplexMap C C' hf L) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (twistedCellularSingularHomologyIso_hom_naturality C C' hf L n).symm

end TauCeti
