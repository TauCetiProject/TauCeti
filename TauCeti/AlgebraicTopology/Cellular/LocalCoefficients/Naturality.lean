/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.LocalCoefficients.Homology

/-!
# Naturality of cellular homology with local coefficients in the coefficient system

Let `C ⊆ X` be a relative CW complex with skeleta `Xⁿ` and base `X⁻¹`, and let `η : L ⟶ K` be a
morphism of local coefficient systems on `C`. Restricting `η` to the skeleta
(`TauCeti.skeletonSystemMap`), it induces maps `Hₙ(Xⁿ, Xⁿ⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; K)` of cellular chain
groups (`TauCeti.twistedCellularChainGroupCoefficientMap`), and these commute with the cellular
differentials (`TauCeti.twistedCellularDifferential_naturality_coefficient`), because the
connecting morphisms of triples are natural in the coefficients
(`TopTriple.twistedHomologyδ_naturality_coefficient`). So `η` induces a map of cellular chain
complexes with local coefficients (`TauCeti.twistedCellularChainComplexCoefficientMap`), functorial
in `η`.

The identification of cellular homology with twisted relative singular homology,
`TauCeti.twistedCellularSingularHomologyIso`, is natural for these maps
(`TauCeti.twistedCellularSingularHomologyIso_hom_naturality_coefficient`): on cellular homology,
`η` acts as the map it induces on `Hₙ(C, X⁻¹; -)`. Every step of the identification, the cellular
cycles as `Hₙ(Xⁿ, X⁻¹; L)` (`TauCeti.twistedCellularCyclesIso_hom_naturality_coefficient`) and the
map induced by the inclusion of a skeleton
(`TauCeti.twistedHomologySkeletonBasePairToComplex_naturality_coefficient`), is built from maps of
pairs, connecting morphisms and changes of coefficients, which commute with `η`.

For a fibration over a CW complex, morphisms of local coefficient systems arise from maps of
fibrations over the base and from maps of coefficient modules, acting on the local systems of fibre
homology `b ↦ H_q(p⁻¹(b))`. This naturality is the cellular side of the naturality of the
identification of the second page of the Serre spectral sequence with `H_p(B; H_q(F))` under such
maps.

## Main definitions

* `TauCeti.skeletonSystemMap`: the restriction of `η` to the `n`-th stage of the skeletal
  filtration.
* `TauCeti.twistedCellularChainGroupCoefficientMap`: the map of cellular chain groups induced by
  `η`.
* `TauCeti.twistedCellularChainComplexCoefficientMap`: the map of cellular chain complexes induced
  by `η`.

## Main results

* `TauCeti.twistedCellularDifferential_naturality_coefficient`: the cellular differentials commute
  with the maps induced by `η`.
* `TauCeti.twistedCellularChainComplexCoefficientMap_id`,
  `TauCeti.twistedCellularChainComplexCoefficientMap_comp`: functoriality in `η`.
* `TauCeti.twistedCellularSingularHomologyIso_hom_naturality_coefficient`: the cellular–singular
  comparison with local coefficients is natural in the coefficient system.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 and Section 3.H.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {R : Type u} [Ring R] {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] {L K J : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C)}

/-- The restriction of a morphism of local coefficient systems on `C` to the stage
`skeletonObj C n` of the skeletal filtration. -/
abbrev skeletonSystemMap (η : L ⟶ K) (n : ℕ) : skeletonSystem C L n ⟶ skeletonSystem C K n :=
  (LocalCoefficientSystem.pullback (R := R) (X := skeletonObj C n) (Y := TopCat.of C)
    (ContinuousMap.inclusion (skeletonLT C (n : ℕ∞)).subset_complex)).map η

/-- The coefficient identification `TauCeti.skeletonPairSubspaceSystemIso` is natural in the
local coefficient system. -/
@[reassoc]
lemma skeletonPairSubspaceSystemIso_hom_naturality (η : L ⟶ K) (n : ℕ) :
    (LocalCoefficientSystem.pullback (skeletonPair C n).map.hom).map
        (skeletonSystemMap C η (n + 1)) ≫ (skeletonPairSubspaceSystemIso C K n).hom =
      (skeletonPairSubspaceSystemIso C L n).hom ≫ skeletonSystemMap C η n := by
  ext x : 2
  -- The subspace of `skeletonPair C n` is `skeletonObj C n` only up to unfolding the pair
  -- constructor, so the components are rewritten with `erw`; both sides are then `η` at the same
  -- point.
  erw [NatTrans.comp_app, NatTrans.comp_app, skeletonPairSubspaceSystemIso_hom_app,
    skeletonPairSubspaceSystemIso_hom_app, Category.comp_id]

/-- The map of cellular chain groups `Hₙ(Xⁿ, Xⁿ⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; K)` induced by a morphism
`η : L ⟶ K` of local coefficient systems on `C`. -/
def twistedCellularChainGroupCoefficientMap (η : L ⟶ K) (n : ℕ) :
    twistedCellularChainGroup C L n ⟶ twistedCellularChainGroup C K n :=
  (skeletonPair C n).twistedHomologyCoefficientMap (skeletonSystemMap C η (n + 1)) n

/-- The map of cellular chain groups induced by `η` is the change of coefficients along the
restriction of `η` to the `n`-skeleton. -/
lemma twistedCellularChainGroupCoefficientMap_def (η : L ⟶ K) (n : ℕ) :
    twistedCellularChainGroupCoefficientMap C η n =
      (skeletonPair C n).twistedHomologyCoefficientMap (skeletonSystemMap C η (n + 1)) n :=
  (rfl)

/-- The cellular differential with local coefficients commutes with the maps induced by a
morphism of local coefficient systems. -/
@[reassoc]
lemma twistedCellularDifferential_naturality_coefficient (η : L ⟶ K) (n : ℕ) :
    twistedCellularDifferential C L n ≫ twistedCellularChainGroupCoefficientMap C η n =
      twistedCellularChainGroupCoefficientMap C η (n + 1) ≫ twistedCellularDifferential C K n := by
  have hδ := (skeletonTriple C n).twistedHomologyδ_naturality_coefficient
    (skeletonSystem C L (n + 1 + 1)) (skeletonSystemMap C η (n + 1 + 1)) (n + 1) n rfl
  have hiso := (skeletonPair C n).twistedHomologyCoefficientMap_comp_eq_of_comp_eq
    (skeletonPairSubspaceSystemIso_hom_naturality C η (n + 1)) n
  rw [twistedCellularDifferential_def, twistedCellularDifferential_def,
    twistedCellularChainGroupCoefficientMap_def, twistedCellularChainGroupCoefficientMap_def]
  -- The pairs of the triple `skeletonTriple C n` are the skeletal pairs only up to unfolding the
  -- pair constructors, so the composites are matched by terms rather than by rewriting.
  calc _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (_ ≫ ·) hiso.symm
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ _) hδ
    _ = _ := Category.assoc _ _ _

/-- The map of cellular chain complexes with local coefficients induced by a morphism `η : L ⟶ K`
of local coefficient systems on `C`: in degree `n` it is the map
`Hₙ(Xⁿ, Xⁿ⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; K)` induced by `η`
(`TauCeti.twistedCellularChainGroupCoefficientMap`). -/
def twistedCellularChainComplexCoefficientMap (η : L ⟶ K) :
    twistedCellularChainComplex C L ⟶ twistedCellularChainComplex C K where
  f n := eqToHom (twistedCellularChainComplex_X C L n) ≫
    twistedCellularChainGroupCoefficientMap C η n ≫
      eqToHom (twistedCellularChainComplex_X C K n).symm
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [twistedCellularChainComplex_d, twistedCellularChainComplex_d]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [twistedCellularDifferential_naturality_coefficient_assoc]

/-- In degree `n`, the map of cellular chain complexes induced by `η` is the map of cellular chain
groups `TauCeti.twistedCellularChainGroupCoefficientMap`, transported across
`TauCeti.twistedCellularChainComplex_X`. -/
@[simp]
lemma twistedCellularChainComplexCoefficientMap_f (η : L ⟶ K) (n : ℕ) :
    (twistedCellularChainComplexCoefficientMap C η).f n =
      eqToHom (twistedCellularChainComplex_X C L n) ≫
        twistedCellularChainGroupCoefficientMap C η n ≫
          eqToHom (twistedCellularChainComplex_X C K n).symm :=
  (rfl)

variable (L) in
/-- The identity of a local coefficient system induces the identity of the cellular chain groups. -/
@[simp]
lemma twistedCellularChainGroupCoefficientMap_id (n : ℕ) :
    twistedCellularChainGroupCoefficientMap C (𝟙 L) n = 𝟙 _ :=
  (congrArg (fun φ ↦ (skeletonPair C n).twistedHomologyCoefficientMap φ n)
    (CategoryTheory.Functor.map_id _ _)).trans
      ((skeletonPair C n).twistedHomologyCoefficientMap_id _ n)

/-- The maps of cellular chain groups respect composition of morphisms of local coefficient
systems. -/
@[simp, reassoc]
lemma twistedCellularChainGroupCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (n : ℕ) :
    twistedCellularChainGroupCoefficientMap C (η ≫ θ) n =
      twistedCellularChainGroupCoefficientMap C η n ≫
        twistedCellularChainGroupCoefficientMap C θ n :=
  (congrArg (fun φ ↦ (skeletonPair C n).twistedHomologyCoefficientMap φ n)
    (CategoryTheory.Functor.map_comp _ _ _)).trans
      ((skeletonPair C n).twistedHomologyCoefficientMap_comp _ _ _ n)

variable (L) in
/-- The identity of a local coefficient system induces the identity of the cellular chain
complex. -/
@[simp]
lemma twistedCellularChainComplexCoefficientMap_id :
    twistedCellularChainComplexCoefficientMap C (𝟙 L) = 𝟙 _ := by
  ext n : 1
  simp

/-- The maps of cellular chain complexes respect composition of morphisms of local coefficient
systems. -/
@[simp, reassoc]
lemma twistedCellularChainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    twistedCellularChainComplexCoefficientMap C (η ≫ θ) =
      twistedCellularChainComplexCoefficientMap C η ≫
        twistedCellularChainComplexCoefficientMap C θ := by
  ext n : 1
  simp

/-- The map `Hₙ(Xⁿ, X⁻¹; L) ⟶ Hₙ(Xⁿ, Xⁿ⁻¹; L)` is natural in the local coefficient system. -/
@[reassoc]
lemma twistedCellularCyclesι_naturality_coefficient (η : L ⟶ K) (n : ℕ) :
    twistedCellularCyclesι C L n ≫ twistedCellularChainGroupCoefficientMap C η n =
      (skeletonBasePair C n).twistedHomologyCoefficientMap (skeletonSystemMap C η (n + 1)) n ≫
        twistedCellularCyclesι C K n := by
  cases n with
  | zero =>
    rw [twistedCellularCyclesι_zero, twistedCellularCyclesι_zero, Category.id_comp,
      Category.comp_id]
    -- In degree `0` the base pair `(X⁰, X⁻¹)` is the skeletal pair `(X⁰, X⁻¹)` by definition.
    rfl
  | succ n =>
    rw [twistedCellularCyclesι_succ, twistedCellularCyclesι_succ]
    exact (skeletonBaseTriple C n).twistedHomologyTotalToOuter_naturality_coefficient
      (skeletonSystem C L (n + 1 + 1)) (skeletonSystemMap C η (n + 1 + 1)) (n + 1)

/-- The identification `TauCeti.twistedCellularCyclesIso` of the cellular cycles with
`Hₙ(Xⁿ, X⁻¹; L)` is natural in the local coefficient system. -/
@[reassoc]
lemma twistedCellularCyclesIso_hom_naturality_coefficient (η : L ⟶ K) (n : ℕ) :
    HomologicalComplex.cyclesMap (twistedCellularChainComplexCoefficientMap C η) n ≫
        (twistedCellularCyclesIso C K n).hom =
      (twistedCellularCyclesIso C L n).hom ≫
        (skeletonBasePair C n).twistedHomologyCoefficientMap (skeletonSystemMap C η (n + 1)) n := by
  have hi (L : LocalCoefficientSystem.{u, w, max w v} R (TopCat.of C)) :
      (twistedCellularCyclesIso C L n).hom ≫ twistedCellularCyclesι C L n ≫
        eqToHom (twistedCellularChainComplex_X C L n).symm =
        (twistedCellularChainComplex C L).iCycles n := by
    rw [← twistedCellularCyclesIso_inv_comp_iCycles, Iso.hom_inv_id_assoc]
  rw [← cancel_mono ((twistedCellularCyclesIso C K n).inv ≫
    (twistedCellularChainComplex C K).iCycles n), Category.assoc, Iso.hom_inv_id_assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc, twistedCellularCyclesIso_inv_comp_iCycles,
    ← twistedCellularCyclesι_naturality_coefficient_assoc, ← hi L]
  simp

/-- Restricting a morphism of local coefficient systems to the `m`-skeleton commutes with the
identification `TauCeti.skeletonSystem_eq_pullback` of the restricted systems with pullbacks along
the inclusion of the `m`-skeleton as a map of pairs. -/
private lemma skeletonSystemMap_comp_eqToHom (η : L ⟶ K) (m : ℕ) :
    skeletonSystemMap C η (m + 1) ≫ eqToHom (skeletonSystem_eq_pullback C K m) =
      eqToHom (skeletonSystem_eq_pullback C L m) ≫
        (LocalCoefficientSystem.pullback
          (TopPair.Hom.fst (skeletonBasePairToComplex C m)).hom).map η := by
  have key : ∀ (g : C((skeletonBasePair C m).fst, (complexBasePair C).fst)),
      ContinuousMap.inclusion (skeletonLT C ((m + 1 : ℕ) : ℕ∞)).subset_complex = g → ∀
      (hL : skeletonSystem C L (m + 1) = (LocalCoefficientSystem.pullback g).obj L)
      (hK : skeletonSystem C K (m + 1) = (LocalCoefficientSystem.pullback g).obj K),
      skeletonSystemMap C η (m + 1) ≫ eqToHom hK =
        eqToHom hL ≫ (LocalCoefficientSystem.pullback g).map η := by
    rintro g rfl _ _
    -- The restricted systems are the pullbacks along the inclusion by definition, so both
    -- transports are identities.
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact key _ (by rw [skeletonBasePairToComplex_fst]; rfl) _ _

/-- The map `Hₖ(Xᵐ, X⁻¹; L) ⟶ Hₖ(C, X⁻¹; L)` induced by the inclusion of the `m`-skeleton is
natural in the local coefficient system. -/
@[reassoc]
lemma twistedHomologySkeletonBasePairToComplex_naturality_coefficient (η : L ⟶ K) (m k : ℕ) :
    (skeletonBasePair C m).twistedHomologyCoefficientMap (skeletonSystemMap C η (m + 1)) k ≫
        twistedHomologySkeletonBasePairToComplex C K m k =
      twistedHomologySkeletonBasePairToComplex C L m k ≫
        (complexBasePair C).twistedHomologyCoefficientMap η k := by
  have hmap := TopPair.twistedHomologyMap_naturality (skeletonBasePairToComplex C m) L η k
  have hcoef := (skeletonBasePair C m).twistedHomologyCoefficientMap_comp_eq_of_comp_eq
    (skeletonSystemMap_comp_eqToHom C η m) k
  rw [twistedHomologySkeletonBasePairToComplex_def, twistedHomologySkeletonBasePairToComplex_def]
  -- The coefficient maps live on `skeletonBasePair C m`, whose ambient space is the `m`-skeleton
  -- only up to unfolding the pair constructor, so the composites are matched by terms.
  calc _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ _) hcoef
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (_ ≫ ·) hmap.symm

/-- **Naturality of the cellular–singular comparison with local coefficients**: under
`TauCeti.twistedCellularSingularHomologyIso`, the map induced on cellular homology by a morphism
`η : L ⟶ K` of local coefficient systems is the map it induces on the twisted relative singular
homology `Hₙ(C, X⁻¹; -)` of the complex. -/
@[reassoc]
theorem twistedCellularSingularHomologyIso_hom_naturality_coefficient (η : L ⟶ K) (n : ℕ) :
    HomologicalComplex.homologyMap (twistedCellularChainComplexCoefficientMap C η) n ≫
        (twistedCellularSingularHomologyIso C K n).hom =
      (twistedCellularSingularHomologyIso C L n).hom ≫
        (complexBasePair C).twistedHomologyCoefficientMap η n := by
  rw [← cancel_epi ((twistedCellularChainComplex C L).homologyπ n),
    HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_comp_twistedCellularSingularHomologyIso_hom,
    homologyπ_comp_twistedCellularSingularHomologyIso_hom_assoc,
    twistedCellularCyclesIso_hom_naturality_coefficient_assoc,
    twistedHomologySkeletonBasePairToComplex_naturality_coefficient]

/-- An isomorphism of local coefficient systems induces an isomorphism of cellular chain
complexes with local coefficients. -/
instance isIso_twistedCellularChainComplexCoefficientMap (η : L ⟶ K) [IsIso η] :
    IsIso (twistedCellularChainComplexCoefficientMap C η) :=
  ⟨twistedCellularChainComplexCoefficientMap C (inv η), by
    rw [← twistedCellularChainComplexCoefficientMap_comp, IsIso.hom_inv_id,
      twistedCellularChainComplexCoefficientMap_id], by
    rw [← twistedCellularChainComplexCoefficientMap_comp, IsIso.inv_hom_id,
      twistedCellularChainComplexCoefficientMap_id]⟩

end TauCeti
