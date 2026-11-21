/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.MayerVietoris.Pair
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence
import TauCeti.AlgebraicTopology.Singular.MayerVietoris.FiniteUnion
import TauCeti.Topology.Connected.PathConnected
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton

/-!
# The Thom pair in the rank degree with coefficients in the orientation local system

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, and let `o(E)` be its
orientation local system (`TauCeti.VectorBundleOrientationCover.signLocalSystem`), pulled back to
the total space along the projection (`TauCeti.thomPairSignSystem`). Below the rank the homology of
the Thom pair with these coefficients vanishes (`TauCeti.isZero_twistedHomology_thomPair`). This
file computes the first group that does not vanish: over a compact base, and with coefficients in
any commutative ring `K`,

`Hᵣ(E, E₀; o(E)) ≅ H₀(B; K)`

(`TauCeti.thomPairSignHomologyFinrankIso`). No orientation of `E` is needed, only an orientation
`ω` of the model fibre, on which the isomorphism depends up to sign. It sends the fibre class over
`b` to the class of `b` (`TauCeti.thomPairSignHomologyFinrankIso_hom_apply`).
This is the rank degree of the Thom isomorphism `Hₙ₊ᵣ(E, E₀; π^*L) ≅ Hₙ(B; o(E) ⊗ L)` with local
coefficients, for `L = o(E)`, since `o(E) ⊗ o(E)` is the constant system. By the universal
coefficient theorem it is the group from which the Thom class of `E` with coefficients in its
orientation local system is obtained.

## The fibre classes

A linear trivialization `e` of the atlas and an orientation `ω` of the model fibre trivialize the
orientation local system over the base set of `e`: over `b`, evaluate at the orientation of `E_b`
which `e` reads as `ω` (`TauCeti.VectorBundleOrientationCover.signLocalSystemPullbackIsoOfMapsTo`).
Over a subset `W` of the base set this identifies `Hᵣ(E|_W, E₀|_W; o(E))` with the untwisted
homology `Hᵣ(E|_W, E₀|_W; K)` (`TauCeti.thomPairOverSignHomologyIso`). The fibre class over `x`
(`TauCeti.thomPairOverSignFiberClass`) is the class of the fibre pair over `x` which the
trivialization at `x` reads as the generator `TauCeti.complZeroPairGenerator` of
`Hᵣ(F, F ∖ {0}; K)`. Every trivialization `e'` of the atlas reads it the same way
(`TauCeti.thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass`): if `e'` reads the
orientations of `E_x` oppositely, both the trivialization of `o(E)` and the generator of the fibre
pair change sign, and the two signs cancel. This is what makes the fibre classes, unlike the
fibre classes with constant coefficients, independent of all choices but `ω`; replacing `ω` by
`-ω` negates them (`TauCeti.thomPairOverSignFiberClass_neg`).

## The proof

The map `H₀(W; K) ⟶ Hᵣ(E|_W, E₀|_W; o(E))` sends the class of a point to the fibre class over it
(`TauCeti.thomPairOverSignHomologyFinrankInv`). It is well defined since the fibre classes are
constant along paths (`TauCeti.thomPairOverSignFiberClassOver_eq_of_path`), which is read off
locally from the product. Over a subset of a trivializing set it is an isomorphism, by the
computation `Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)` for the product bundle. The Mayer–Vietoris
sequence of the Thom pairs over two open sets with local coefficients, read off the sequence of
two pairs (`TauCeti.LocalCoefficientSystem.pairTwistedMayerVietoris_exact₂`), ends in degree `r`,
since the homology vanishes below the rank, so the map is an isomorphism over every finite union
of trivializing open sets, by induction on their number
(`TauCeti.isIso_thomPairOverSignHomologyFinrankInv_biUnion`, an instance of the gluing argument
`TauCeti.isIso_biUnion_of_mayerVietoris`). A compact base is such a union.

The argument follows the computation of `Hᵣ(E, E₀; K)` with constant coefficients in
`TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology`, where the fibre classes must be chosen by
an orientation or by a ring with a single unit.

## Main results

* `TauCeti.thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass`: the fibre class over `x` is
  read by every trivialization of the atlas as the generator of the fibre pair.
* `TauCeti.isIso_thomPairOverSignHomologyFinrankInv_biUnion`:
  `H₀(W; K) ≅ Hᵣ(E|_W, E₀|_W; o(E))` for a finite union `W` of trivializing open sets.
* `TauCeti.thomPairSignHomologyFinrankIso`: `Hᵣ(E, E₀; o(E)) ≅ H₀(B; K)` over a compact base.
* `TauCeti.thomPairSignHomologyFinrankIso_hom_apply`: it sends the fibre class over `b` to the
  class of `b`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §10 (the Thom pair in the rank degree, by Mayer–Vietoris over
  trivializing open sets) and §12 (the orientation double cover).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H (local coefficients and the orientation system) and Theorem 4D.10 (the Thom
  isomorphism).
-/

public section

noncomputable section

open Bundle CategoryTheory Module TauCeti Topology AlgebraicTopology

universe w

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type w} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) {K : Type w} [CommRing K]

namespace TauCeti

open VectorBundleOrientationCover LocalCoefficientSystem Set

variable (F E K) in
/-- The orientation local system `o(E)` pulled back to the total space of `E` along the
projection: its fibre at a vector `v` over `b` is the fibre of `o(E)` over `b`. -/
noncomputable abbrev thomPairSignSystem : LocalCoefficientSystem.{w, w, w} K (thomPair F E).fst :=
  (pullback (thomPairProj F E).hom).obj (signLocalSystem F E K hι)

variable (F E K) in
/-- The restriction of the pulled-back orientation local system to the vectors over `W`. -/
noncomputable abbrev thomPairOverSignSystem (W : Set B) :
    LocalCoefficientSystem.{w, w, w} K (thomPairOver F E W).fst :=
  (pullback (ContinuousMap.subtypeVal (π F E ⁻¹' W))).obj (thomPairSignSystem F E hι K)

variable (F E K) in
/-- The homology `Hₙ(E|_W, E₀|_W; o(E))` of the Thom pair over `W` with coefficients in the
orientation local system. -/
noncomputable abbrev thomPairOverSignHomology (W : Set B) (n : ℕ) : ModuleCat.{w} K :=
  (thomPairOver F E W).twistedHomology (thomPairOverSignSystem F E hι K W) n

variable (F E K) in
/-- The restriction `Hₙ(E|_W, E₀|_W; o(E)) ⟶ Hₙ(E|_{W'}, E₀|_{W'}; o(E))` induced by `W ⊆ W'`. -/
noncomputable abbrev thomPairOverSignHomologyMap {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverSignHomology F E hι K W n ⟶ thomPairOverSignHomology F E hι K W' n :=
  HomologicalComplex.homologyMap (subsetPairTwistedChainComplexMap (thomPairSignSystem F E hι K)
    inter_subset_left inter_subset_left (preimage_mono h)
    (inter_subset_inter_left _ (preimage_mono h))) n

variable (K) in
/-- The map of twisted homology induced by an inclusion of pairs of subsets of the total space. -/
private noncomputable abbrev subsetPairSignHomologyMap {A₁ C₁ A₂ C₂ : Set (thomPair F E).fst}
    (hC₁ : C₁ ⊆ A₁) (hC₂ : C₂ ⊆ A₂) (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) (n : ℕ) :=
  HomologicalComplex.homologyMap
    (subsetPairTwistedChainComplexMap (thomPairSignSystem F E hι K) hC₁ hC₂ hA hC) n

/-- The maps induced by inclusions of pairs of subsets compose. -/
private theorem subsetPairSignHomologyMap_comp {A₁ C₁ A₂ C₂ A₃ C₃ : Set (thomPair F E).fst}
    (hC₁ : C₁ ⊆ A₁) (hC₂ : C₂ ⊆ A₂) (hC₃ : C₃ ⊆ A₃) (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂)
    (hA' : A₂ ⊆ A₃) (hC' : C₂ ⊆ C₃) (n : ℕ) :
    subsetPairSignHomologyMap hι K hC₁ hC₂ hA hC n ≫
        subsetPairSignHomologyMap hι K hC₂ hC₃ hA' hC' n =
      subsetPairSignHomologyMap hι K hC₁ hC₃ (hA.trans hA') (hC.trans hC') n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap _ _ _ _ _ _ _ _))

variable (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (ω : Orientation ℝ F ι)

variable (K) in
/-- Over a subset `W` of the base set of a trivialization `e` of the atlas, the orientation local
system on `E|_W` is trivialized by evaluating at the orientations read by `e` as `ω`. -/
noncomputable def thomPairOverSignSystemIso {W : Set B} (hW : W ⊆ e.baseSet) :
    thomPairOverSignSystem F E hι K W ≅ (constantFunctor _).obj (ModuleCat.of K K) :=
  ((pullbackCompIso (X := TopCat.of ↥(π F E ⁻¹' W)) (Y := (thomPair F E).fst)
    (ContinuousMap.subtypeVal (π F E ⁻¹' W)) (thomPairProj F E).hom).app
    (signLocalSystem F E K hι)).symm ≪≫
    signLocalSystemPullbackIsoOfMapsTo hι e ω _ fun v ↦
      (thomPairProj_apply F E v.val).symm ▸ hW v.property

/-- The trivialization over `W` identifies the restriction of the pulled-back orientation local
system with its pullback along the projection of `E|_W`, then evaluates at the orientations read by
`e` as `ω`. -/
theorem thomPairOverSignSystemIso_hom {W : Set B} (hW : W ⊆ e.baseSet) :
    (thomPairOverSignSystemIso hι K e ω hW).hom =
      ((pullbackCompIso (X := TopCat.of ↥(π F E ⁻¹' W)) (Y := (thomPair F E).fst)
        (ContinuousMap.subtypeVal (π F E ⁻¹' W)) (thomPairProj F E).hom).app
        (signLocalSystem F E K hι)).inv ≫
      (signLocalSystemPullbackIsoOfMapsTo hι e ω _ fun v ↦
        (thomPairProj_apply F E v.val).symm ▸ hW v.property).hom :=
  (rfl)

/-- Reading the orientations through `-ω` instead of `ω` negates the trivialization over `W`. -/
@[simp]
theorem thomPairOverSignSystemIso_neg_hom {W : Set B} (hW : W ⊆ e.baseSet) :
    (thomPairOverSignSystemIso hι K e (-ω) hW).hom =
      -(thomPairOverSignSystemIso hι K e ω hW).hom := by
  rw [thomPairOverSignSystemIso_hom, thomPairOverSignSystemIso_hom]
  exact (congrArg (_ ≫ ·) (signLocalSystemPullbackIsoOfMapsTo_neg_hom hι e ω _ _)).trans
    (Preadditive.comp_neg _ _)

variable (K) in
/-- Over a subset `W` of the base set of a trivialization `e` of the atlas, the trivialization of
the orientation local system read through `e` and `ω` identifies `Hₙ(E|_W, E₀|_W; o(E))` with the
untwisted homology `Hₙ(E|_W, E₀|_W; K)`. -/
noncomputable def thomPairOverSignHomologyIso {W : Set B} (hW : W ⊆ e.baseSet) (n : ℕ) :
    thomPairOverSignHomology F E hι K W n ≅
      (thomPairOver F E W).singularHomology (ModuleCat.of K K) n :=
  asIso ((thomPairOver F E W).twistedHomologyCoefficientMap
    (thomPairOverSignSystemIso hι K e ω hW).hom n) ≪≫
    TopPair.twistedHomologyConstantIso _ _ n

/-- The identification with untwisted homology over `W` is the change of coefficients along the
trivialization over `W`, followed by the comparison of twisted homology with constant coefficients
and untwisted homology. -/
theorem thomPairOverSignHomologyIso_hom {W : Set B} (hW : W ⊆ e.baseSet) (n : ℕ) :
    (thomPairOverSignHomologyIso hι K e ω hW n).hom =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          (thomPairOverSignSystemIso hι K e ω hW).hom n ≫
        ((thomPairOver F E W).twistedHomologyConstantIso (ModuleCat.of K K) n).hom :=
  (rfl)

/-- Reading the orientations through `-ω` instead of `ω` negates the identification with untwisted
homology over `W`. -/
@[simp]
theorem thomPairOverSignHomologyIso_neg_hom {W : Set B} (hW : W ⊆ e.baseSet) (n : ℕ) :
    (thomPairOverSignHomologyIso hι K e (-ω) hW n).hom =
      -(thomPairOverSignHomologyIso hι K e ω hW n).hom := by
  rw [thomPairOverSignHomologyIso_hom, thomPairOverSignHomologyIso_hom,
    thomPairOverSignSystemIso_neg_hom, TopPair.twistedHomologyCoefficientMap_neg,
    Preadditive.neg_comp]

/-- The inverse of the identification read through `-ω` is the negative of the one read through
`ω`. -/
@[simp]
theorem thomPairOverSignHomologyIso_neg_inv {W : Set B} (hW : W ⊆ e.baseSet) (n : ℕ) :
    (thomPairOverSignHomologyIso hι K e (-ω) hW n).inv =
      -(thomPairOverSignHomologyIso hι K e ω hW n).inv :=
  Iso.inv_ext (by
    rw [thomPairOverSignHomologyIso_neg_hom, Preadditive.neg_comp_neg, Iso.hom_inv_id])

/-- The restriction from `W` to `W'` is the change of coefficients identifying the two pullbacks of
`o(E)` to `E|_W`, followed by the map induced by the inclusion of Thom pairs. -/
theorem thomPairOverSignHomologyMap_eq {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    thomPairOverSignHomologyMap F E hι K h n =
      (thomPairOver F E W).twistedHomologyCoefficientMap
          ((pullbackCompIso
            (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h))).hom
            (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).hom.app
            (thomPairSignSystem F E hι K)) n ≫
        TopPair.twistedHomologyMap
          (TopPair.ofHom (X := thomPairOver F E W) (Y := thomPairOver F E W')
            (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h)))
            (TopCat.ofHom (ContinuousMap.inclusion
              (inter_subset_inter_left (zeroSectionCompl F E) (preimage_mono (f := π F E) h))))
            rfl)
          (thomPairOverSignSystem F E hι K W') n := by
  rw [thomPairOverSignHomologyMap, subsetPairTwistedChainComplexMap_def]
  exact HomologicalComplex.homologyMap_comp _ _ n

/-- The trivializations of the orientation local system over `W ⊆ W'` commute with the
restriction from `E|_{W'}` to `E|_W`. -/
theorem thomPairOverSignSystemIso_hom_restrict {W W' : Set B} (h : W ⊆ W')
    (hW' : W' ⊆ e.baseSet) :
    (pullbackCompIso
          (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h))).hom
          (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).hom.app
          (thomPairSignSystem F E hι K) ≫
        (pullback (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h))).hom).map
          (thomPairOverSignSystemIso hι K e ω hW').hom ≫
        (pullbackConstantIso _ _).hom =
      (thomPairOverSignSystemIso hι K e ω (h.trans hW')).hom := by
  ext v : 2
  -- The pulled-back systems are only definitionally whiskered functors (as in
  -- `pullbackCompIso_hom_app_app`), so their structural components are reached by `erw`.
  erw [NatTrans.comp_app, NatTrans.comp_app, pullbackCompIso_hom_app_app, Category.id_comp,
    pullback_map_app, pullbackConstantIso_hom_app, Category.comp_id]
  erw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Iso.symm_hom,
    Iso.symm_hom, Iso.app_inv, Iso.app_inv, pullbackCompIso_inv_app_app,
    pullbackCompIso_inv_app_app]
  -- Both components are the trivialization along the projection of `E|_W`, the one over `W'`
  -- written through the inclusion `E|_W ⊆ E|_{W'}`; the identities left over from the
  -- `pullbackCompIso` components are definitionally trivial.
  erw [signLocalSystemPullbackIsoOfMapsTo_hom_app_map]
  rfl

/-- The identifications with untwisted homology over subsets of the base set of `e` commute with
the restrictions. -/
theorem thomPairOverSignHomologyMap_comp_iso_hom {W W' : Set B} (h : W ⊆ W')
    (hW' : W' ⊆ e.baseSet) (n : ℕ) :
    thomPairOverSignHomologyMap F E hι K h n ≫
        (thomPairOverSignHomologyIso hι K e ω hW' n).hom =
      (thomPairOverSignHomologyIso hι K e ω (h.trans hW') n).hom ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) n := by
  rw [thomPairOverSignHomologyMap_eq, thomPairOverSignHomologyIso_hom,
    thomPairOverSignHomologyIso_hom]
  refine (Category.assoc _ _ _).trans ?_
  let f : thomPairOver F E W ⟶ thomPairOver F E W' :=
    TopPair.ofHom (X := thomPairOver F E W) (Y := thomPairOver F E W')
      (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h)))
      (TopCat.ofHom (ContinuousMap.inclusion
        (inter_subset_inter_left (zeroSectionCompl F E) (preimage_mono (f := π F E) h)))) rfl
  have hf : f = thomPairOverMap F E h := TopPair.hom_ext_of_fst _ (thomPairOverMap_fst F E h).symm
  -- From here on the intermediate homology groups are twisted homology with coefficients in
  -- systems on `(thomPair F E).fst`, which is `TotalSpace F E` only up to unfolding; `rw` sees the
  -- goal as ill-typed under reducible transparency, so the remaining rewrites use `erw`.
  -- Move the trivialization over `W'` past the map of pairs, then compare constant coefficients.
  erw [TopPair.twistedHomologyMap_naturality_assoc f (thomPairOverSignSystem F E hι K W')
      (thomPairOverSignSystemIso hι K e ω hW').hom n,
    TopPair.twistedHomologyConstantIso_hom_pair_naturality (ModuleCat.of K K) f n]
  -- Collect the three changes of coefficients into one.
  erw [← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  rw [← hf, Category.assoc]
  erw [(Category.assoc _ _ _).trans (thomPairOverSignSystemIso_hom_restrict hι e ω h hW')]
  -- `f` is a `let` whose body is the map of pairs in the goal.
  rfl

variable [FiniteDimensional ℝ F]

variable (K) in
/-- Below the rank, the homology over a trivializing set vanishes. -/
private theorem isZero_thomPairOverSignHomology_of_subset {W : Set B} (hW : W ⊆ e.baseSet) {n : ℕ}
    (hn : n < finrank ℝ F) (ω : Orientation ℝ F ι) :
    Limits.IsZero (thomPairOverSignHomology F E hι K W n) :=
  (e.isZero_singularHomology_thomPairOver hW (ModuleCat.of K K) hn).of_iso
    (thomPairOverSignHomologyIso hι K e ω hW n)

variable (K) in
/-- The generator of the untwisted homology `Hᵣ(E|_{x}, E₀|_{x}; K)` of the fibre pair over `x`
which the trivialization `e` reads as the generator `TauCeti.complZeroPairGenerator` of
`Hᵣ(F, F ∖ {0}; K)`. -/
noncomputable def thomPairOverFiberGenerator {x : B} (hx : x ∈ e.baseSet) :
    ((thomPairOver F E {x}).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E (mem_singleton x)) (ModuleCat.of K K)
    (finrank ℝ F) (TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
      (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F))

private theorem singularHomologyMap_thomPairOverIso_thomPairOverFiberGenerator {W : Set B}
    (hW : W ⊆ e.baseSet) (x : W) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of K K) (finrank ℝ F)
        (TopPair.singularHomologyMap (thomPairOverMap F E (singleton_subset_iff.2 x.property))
          (ModuleCat.of K K) (finrank ℝ F)
          (thomPairOverFiberGenerator K e (hW x.property))) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  rw [thomPairOverFiberGenerator, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, ← Category.assoc, fiberThomPairOverMap_comp_thomPairOverMap,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ _ hW x.property,
    ← TopPair.singularHomologyMap_comp, Iso.inv_hom_id_assoc, Subtype.coe_eta]
  exact singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator K F x

variable (F E K) in
/-- The class of the fibre pair over `x` with coefficients in the orientation local system: read
by the trivialization at `x`, it is the fibre generator tensored with the orientation read as `ω`.
Every trivialization of the atlas reads it as its own fibre generator
(`TauCeti.thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass`), so it depends only on the
model orientation `ω`, and changes sign with it (`TauCeti.thomPairOverSignFiberClass_neg`). -/
noncomputable def thomPairOverSignFiberClass (x : B) :
    thomPairOverSignHomology F E hι K {x} (finrank ℝ F) :=
  (thomPairOverSignHomologyIso hι K (trivializationAt F E x) ω
    (singleton_subset_iff.2 (FiberBundle.mem_baseSet_trivializationAt' x)) _).inv
    (thomPairOverFiberGenerator K (trivializationAt F E x)
      (FiberBundle.mem_baseSet_trivializationAt' x))

/-- Replacing the model orientation `ω` by `-ω` negates the fibre class. -/
@[simp]
theorem thomPairOverSignFiberClass_neg (x : B) :
    thomPairOverSignFiberClass F E hι K (-ω) x = -thomPairOverSignFiberClass F E hι K ω x := by
  simp only [thomPairOverSignFiberClass, thomPairOverSignHomologyIso_neg_inv, ModuleCat.hom_neg,
    LinearMap.neg_apply]

/-- Two trivializations whose maps `Hᵣ(E_x, E_x ∖ {0}; K) ⟶ Hᵣ(F, F ∖ {0}; K)` agree up to a sign
`s` have fibre generators agreeing up to `s`. -/
private theorem thomPairOverFiberGenerator_eq_units_smul (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e'] {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) (s : ℤˣ)
    (h : TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F) =
      (s : ℤ) • TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.hom
        (ModuleCat.of K K) (finrank ℝ F)) :
    thomPairOverFiberGenerator K e' hx' = (s : ℤ) • thomPairOverFiberGenerator K e hx := by
  rw [thomPairOverFiberGenerator, thomPairOverFiberGenerator,
    TopPair.singularHomologyMap_inv_eq_units_smul _ _ _ _ s h]
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, map_zsmul]

omit [FiniteDimensional ℝ F] in
/-- Over the fibre over `x`, the identification with untwisted homology read through `e` and `ω`
depends only on the orientation of `E_x` which `e` reads as `ω`. -/
private theorem thomPairOverSignHomologyIso_singleton_hom_eq (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e'] (ω' : Orientation ℝ F ι) {x : B} (hx : x ∈ e.baseSet)
    (hx' : x ∈ e'.baseSet)
    (h : (e.mapOrientation ι hx).symm ω = (e'.mapOrientation ι hx').symm ω') (n : ℕ) :
    (thomPairOverSignHomologyIso hι K e ω (singleton_subset_iff.2 hx) n).hom =
      (thomPairOverSignHomologyIso hι K e' ω' (singleton_subset_iff.2 hx') n).hom := by
  -- Every point of the fibre over `x` lies over `x`, where the readings are compared.
  have key : ∀ b, b = x → ∀ (h₁ : b ∈ e.baseSet) (h₂ : b ∈ e'.baseSet),
      (e.mapOrientation ι h₁).symm ω = (e'.mapOrientation ι h₂).symm ω' := by
    rintro b rfl _ _
    exact h
  have hτ : (thomPairOverSignSystemIso hι K e ω (singleton_subset_iff.2 hx)).hom =
      (thomPairOverSignSystemIso hι K e' ω' (singleton_subset_iff.2 hx')).hom :=
    congrArg (_ ≫ ·) (signLocalSystemPullbackIsoOfMapsTo_hom_eq hι e ω e' ω' _ _ _
      fun v ↦ key _ ((thomPairProj_apply F E v.val).trans v.property) _ _)
  rw [thomPairOverSignHomologyIso_hom, thomPairOverSignHomologyIso_hom, hτ]

/-- **The fibre class is canonical**: every trivialization `e` of the atlas whose base set contains
`x` reads it as its fibre generator. If `e` reads the orientations of `E_x` oppositely to the
trivialization at `x`, both the trivialization of the orientation local system and the fibre
generator change sign. -/
theorem thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass {x : B} (hx : x ∈ e.baseSet) :
    (thomPairOverSignHomologyIso hι K e ω (singleton_subset_iff.2 hx) (finrank ℝ F)).hom
        (thomPairOverSignFiberClass F E hι K ω x) =
      thomPairOverFiberGenerator K e hx := by
  set eₓ := trivializationAt F E x
  have hxₓ : x ∈ eₓ.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hκ : (thomPairOverSignHomologyIso hι K eₓ ω (singleton_subset_iff.2 hxₓ)
      (finrank ℝ F)).hom (thomPairOverSignFiberClass F E hι K ω x) =
      thomPairOverFiberGenerator K eₓ hxₓ := Iso.inv_hom_id_apply _ _
  -- The trivialization at `x` reads the orientation `o` of `E_x`, which `e` reads as `ω`, as `ω`
  -- or as `-ω`.
  set o := (e.mapOrientation ι hx).symm ω
  have ho : e.mapOrientation ι hx o = ω := Equiv.apply_symm_apply _ ω
  rcases Orientation.eq_or_eq_neg (eₓ.mapOrientation ι hxₓ o) ω
    (by rw [Nat.card_eq_fintype_card, hι]) with h | h
  · rw [thomPairOverSignHomologyIso_singleton_hom_eq hι e ω eₓ ω hx hxₓ
      ((Equiv.eq_symm_apply _).2 h), hκ,
      thomPairOverFiberGenerator_eq_units_smul eₓ e hxₓ hx 1 (by
        simpa using eₓ.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e hxₓ hx
          hι (ModuleCat.of K K) (ho.trans h.symm) (finrank ℝ F))]
    simp
  · rw [thomPairOverSignHomologyIso_singleton_hom_eq hι e ω eₓ (-ω) hx hxₓ
      ((Equiv.eq_symm_apply _).2 h), thomPairOverSignHomologyIso_neg_hom]
    simp only [ModuleCat.hom_neg, LinearMap.neg_apply]
    rw [hκ,
      thomPairOverFiberGenerator_eq_units_smul eₓ e hxₓ hx (-1) (by
        simpa using eₓ.singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e
          hxₓ hx hι (ModuleCat.of K K)
          (by rw [ho, h]; exact (neg_neg (G := Orientation ℝ F ι) ω).symm) (finrank ℝ F))]
    simp

section Gluing

variable (F E K) in
/-- The fibre class over a point `x` of `W`, in the homology of the Thom pair over `W`. -/
noncomputable def thomPairOverSignFiberClassOver (W : Set B) (x : W) :
    thomPairOverSignHomology F E hι K W (finrank ℝ F) :=
  thomPairOverSignHomologyMap F E hι K (singleton_subset_iff.2 x.property) _
    (thomPairOverSignFiberClass F E hι K ω x)

omit [FiniteDimensional ℝ F] in
/-- The restrictions compose. -/
@[reassoc (attr := simp)]
theorem thomPairOverSignHomologyMap_comp {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W'')
    (n : ℕ) :
    thomPairOverSignHomologyMap F E hι K h n ≫ thomPairOverSignHomologyMap F E hι K h' n =
      thomPairOverSignHomologyMap F E hι K (h.trans h') n :=
  subsetPairSignHomologyMap_comp hι _ _ _ _ _ _ _ n

/-- Restricting from `W` to `W'` carries fibre classes to fibre classes. -/
@[simp]
theorem thomPairOverSignHomologyMap_thomPairOverSignFiberClassOver {W W' : Set B} (h : W ⊆ W')
    (x : W) :
    thomPairOverSignHomologyMap F E hι K h _ (thomPairOverSignFiberClassOver F E hι K ω W x) =
      thomPairOverSignFiberClassOver F E hι K ω W' (inclusion h x) := by
  rw [thomPairOverSignFiberClassOver, thomPairOverSignFiberClassOver,
    ← ConcreteCategory.comp_apply, thomPairOverSignHomologyMap_comp]

/-- Over a subset `W` of the base set of a trivialization `e` of the atlas, reading the fibre class
over `x` through `e` and `ω` gives the class of `x` under
`Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)`. -/
private theorem singularHomologyMap_thomPairOverIso_thomPairOverSignFiberClassOver {W : Set B}
    (hW : W ⊆ e.baseSet) (x : W) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
        (ModuleCat.of K K) (finrank ℝ F)
        ((thomPairOverSignHomologyIso hι K e ω hW (finrank ℝ F)).hom
          (thomPairOverSignFiberClassOver F E hι K ω W x)) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  have hψ : (thomPairOverSignHomologyIso hι K e ω hW (finrank ℝ F)).hom
      (thomPairOverSignFiberClassOver F E hι K ω W x) =
      TopPair.singularHomologyMap (thomPairOverMap F E (singleton_subset_iff.2 x.property))
        (ModuleCat.of K K) (finrank ℝ F) (thomPairOverFiberGenerator K e (hW x.property)) := by
    rw [thomPairOverSignFiberClassOver, ← ConcreteCategory.comp_apply,
      thomPairOverSignHomologyMap_comp_iso_hom, ConcreteCategory.comp_apply,
      thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass hι e ω (hW x.property)]
  rw [hψ]
  exact singularHomologyMap_thomPairOverIso_thomPairOverFiberGenerator e hW x

/-- The fibre classes over two points of `W` joined by a path in `W` inside the base set of a
trivialization `e` of the atlas agree. -/
private theorem thomPairOverSignFiberClassOver_eq_of_joinedIn {W : Set B} {x y : W}
    (h : JoinedIn {z : W | (z : B) ∈ e.baseSet} x y) :
    thomPairOverSignFiberClassOver F E hι K ω W x =
      thomPairOverSignFiberClassOver F E hι K ω W y := by
  set T := e.baseSet
  have hW : W ∩ T ⊆ T := inter_subset_right
  let x' : ↥(W ∩ T) := ⟨x, x.property, h.source_mem⟩
  let y' : ↥(W ∩ T) := ⟨y, y.property, h.target_mem⟩
  have hj : Joined x' y' :=
    h.joined_subtype.map (f := fun z : {z : W | (z : B) ∈ T} ↦
      (⟨z.val.val, z.val.property, z.property⟩ : ↥(W ∩ T))) (by fun_prop)
  have hxy : thomPairOverSignFiberClassOver F E hι K ω (W ∩ T) x' =
      thomPairOverSignFiberClassOver F E hι K ω (W ∩ T) y' := by
    apply (ModuleCat.mono_iff_injective ((thomPairOverSignHomologyIso hι K e ω hW
      (finrank ℝ F)).hom ≫ TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
        (ModuleCat.of K K) (finrank ℝ F))).1 inferInstance
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      singularHomologyMap_thomPairOverIso_thomPairOverSignFiberClassOver,
      singularHomologyMap_thomPairOverIso_thomPairOverSignFiberClassOver,
      singularHomology₀Section_eq_of_joined _ hj]
  have := congrArg (thomPairOverSignHomologyMap F E hι K (inter_subset_left : W ∩ T ⊆ W) _) hxy
  rwa [thomPairOverSignHomologyMap_thomPairOverSignFiberClassOver,
    thomPairOverSignHomologyMap_thomPairOverSignFiberClassOver] at this

/-- **The fibre classes are constant along paths.** -/
theorem thomPairOverSignFiberClassOver_eq_of_path {W : Set B} {x y : W} (γ : Path x y) :
    thomPairOverSignFiberClassOver F E hι K ω W x =
      thomPairOverSignFiberClassOver F E hι K ω W y := by
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  refine γ.eq_of_eventually_eq fun t ↦ ?_
  have hγ : Continuous fun s ↦ ((γ s : W) : B) := continuous_subtypeVal.comp γ.continuous
  have hc : ((γ t : W) : B) ∈ (trivializationAt F E (γ t : B)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' _
  have hO : {s : unitInterval | ((γ s : W) : B) ∈ (trivializationAt F E (γ t : B)).baseSet} ∈
      𝓝 t :=
    (hγ.tendsto t).eventually ((trivializationAt F E (γ t : B)).open_baseSet.mem_nhds hc)
  filter_upwards [pathComponentIn_mem_nhds hO] with s hs
  refine (thomPairOverSignFiberClassOver_eq_of_joinedIn hι (trivializationAt F E (γ t : B)) ω
    ((hs.map γ.continuous.continuousOn).mono ?_)).symm
  rintro _ ⟨u, hu, rfl⟩
  exact hu

variable (F E K) in
/-- The map `H₀(W; K) ⟶ Hᵣ(E|_W, E₀|_W; o(E))` sending the class of a point to the fibre class over
it. -/
noncomputable def thomPairOverSignHomologyFinrankInv (W : Set B) :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W) ⟶
      thomPairOverSignHomology F E hι K W (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of K K) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton K _
      (thomPairOverSignFiberClassOver F E hι K ω W x)))
    fun _ _ γ ↦ by rw [thomPairOverSignFiberClassOver_eq_of_path hι ω γ]

/-- The map sends the class of a point to the fibre class over it. -/
@[reassoc]
theorem singularHomology₀Section_thomPairOverSignHomologyFinrankInv {W : Set B} (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x ≫
        thomPairOverSignHomologyFinrankInv F E hι K ω W =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _
        (thomPairOverSignFiberClassOver F E hι K ω W x)) := by
  rw [thomPairOverSignHomologyFinrankInv]
  exact singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
theorem thomPairOverSignHomologyFinrankInv_naturality {W W' : Set B} (h : W ⊆ W') :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        thomPairOverSignHomologyFinrankInv F E hι K ω W' =
      thomPairOverSignHomologyFinrankInv F E hι K ω W ≫
        thomPairOverSignHomologyMap F E hι K h (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSignHomologyFinrankInv,
    singularHomology₀Section_thomPairOverSignHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp,
    thomPairOverSignHomologyMap_thomPairOverSignFiberClassOver]
  rw [ConcreteCategory.hom_ofHom, show ContinuousMap.inclusion h x = inclusion h x from
    Subtype.ext ((ContinuousMap.inclusion_apply_coe h x).trans (coe_inclusion h x).symm)]

/-- Over a subset of the base set of a trivialization of the atlas, the map is an isomorphism: read
through the trivialization it is the isomorphism `H₀(W) ≅ Hᵣ(W × F, W × (F ∖ {0}))` of the product
bundle. -/
private theorem isIso_thomPairOverSignHomologyFinrankInv_of_subset {W : Set B}
    (hW : W ⊆ e.baseSet) :
    IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω W) := by
  have h : thomPairOverSignHomologyFinrankInv F E hι K ω W ≫
      (thomPairOverSignHomologyIso hι K e ω hW (finrank ℝ F)).hom ≫
        TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom
          (ModuleCat.of K K) (finrank ℝ F) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv := by
    refine singularHomology₀_hom_ext _ fun x ↦ ?_
    rw [singularHomology₀Section_thomPairOverSignHomologyFinrankInv_assoc,
      ModuleCat.ofHom_toSpanSingleton_comp]
    ext
    simp [singularHomologyMap_thomPairOverIso_thomPairOverSignFiberClassOver]
  rw [(IsIso.eq_comp_inv _).2 h]
  infer_instance

omit [FiniteDimensional ℝ F] in
/-- The homology over the empty set vanishes. -/
private theorem isZero_thomPairOverSignHomology_empty (n : ℕ) :
    Limits.IsZero (thomPairOverSignHomology F E hι K ∅ n) := by
  have : IsEmpty (thomPairOver F E ∅).snd := ⟨fun v ↦ v.property.1⟩
  have : IsEmpty (thomPairOver F E ∅).fst := ⟨fun v ↦ v.property⟩
  exact (LocalCoefficientSystem.isZero_twistedHomology_of_isEmpty _ n).of_iso
    (asIso ((thomPairOver F E ∅).twistedHomologyπ _ n)).symm

private theorem isIso_thomPairOverSignHomologyFinrankInv_empty :
    IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω ∅) :=
  have : IsEmpty (TopCat.of (∅ : Set B)) := ⟨fun x ↦ x.property⟩
  Limits.isIso_of_source_target_iso_zero _
    (isZero_singularHomology_of_isEmpty _ _ _).isoZero
    (isZero_thomPairOverSignHomology_empty hι _).isoZero

omit [FiniteDimensional ℝ F] in
/-- Equal pairs of subsets have isomorphic homology. -/
private noncomputable def subsetPairSignHomologyIsoOfEq {A₁ C₁ A₂ C₂ : Set (thomPair F E).fst}
    (hC₁ : C₁ ⊆ A₁) (hC₂ : C₂ ⊆ A₂) (hA : A₁ = A₂) (hC : C₁ = C₂) (n : ℕ) :
    (TopPair.ofInclusion hC₁).twistedHomology
        ((pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj
          (thomPairSignSystem F E hι K)) n ≅
      (TopPair.ofInclusion hC₂).twistedHomology
        ((pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj
          (thomPairSignSystem F E hι K)) n where
  hom := subsetPairSignHomologyMap hι K hC₁ hC₂ hA.le hC.le n
  inv := subsetPairSignHomologyMap hι K hC₂ hC₁ hA.ge hC.ge n
  hom_inv_id := (subsetPairSignHomologyMap_comp hι _ _ _ _ _ _ _ n).trans
    ((congrArg (HomologicalComplex.homologyMap · n)
      (subsetPairTwistedChainComplexMap_self _ hC₁)).trans (HomologicalComplex.homologyMap_id _ n))
  inv_hom_id := (subsetPairSignHomologyMap_comp hι _ _ _ _ _ _ _ n).trans
    ((congrArg (HomologicalComplex.homologyMap · n)
      (subsetPairTwistedChainComplexMap_self _ hC₂)).trans (HomologicalComplex.homologyMap_id _ n))

omit [FiniteDimensional ℝ F] in
/-- The first two maps of the Mayer–Vietoris sequence of the Thom pairs over `U` and `V` with
coefficients in the orientation local system compose to zero. -/
private theorem thomPairOverSignHomologyMap_comp_zero {U V : Set B} (n : ℕ) :
    Limits.biprod.lift (thomPairOverSignHomologyMap F E hι K (inter_subset_left : U ∩ V ⊆ U) n)
        (-thomPairOverSignHomologyMap F E hι K (inter_subset_right : U ∩ V ⊆ V) n) ≫
      Limits.biprod.desc (thomPairOverSignHomologyMap F E hι K (subset_union_left : U ⊆ U ∪ V) n)
        (thomPairOverSignHomologyMap F E hι K (subset_union_right : V ⊆ U ∪ V) n) = 0 := by
  rw [Limits.biprod.lift_desc, thomPairOverSignHomologyMap_comp, Preadditive.neg_comp,
    thomPairOverSignHomologyMap_comp, add_neg_eq_zero]

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [FiniteDimensional ℝ F] in
variable (F E) in
/-- The preimages of an intersection and of a union, and their nonzero vectors. -/
private theorem mayerVietoris_sets (U V : Set B) :
    π F E ⁻¹' (U ∩ V) = π F E ⁻¹' U ∩ π F E ⁻¹' V ∧
    π F E ⁻¹' (U ∩ V) ∩ zeroSectionCompl F E =
      (π F E ⁻¹' U ∩ zeroSectionCompl F E) ∩ (π F E ⁻¹' V ∩ zeroSectionCompl F E) ∧
    π F E ⁻¹' (U ∪ V) = π F E ⁻¹' U ∪ π F E ⁻¹' V ∧
    π F E ⁻¹' (U ∪ V) ∩ zeroSectionCompl F E =
      (π F E ⁻¹' U ∩ zeroSectionCompl F E) ∪ (π F E ⁻¹' V ∩ zeroSectionCompl F E) := by
  refine ⟨preimage_inter, ?_, preimage_union, ?_⟩
  · rw [preimage_inter, inter_inter_distrib_right]
  · rw [preimage_union, union_inter_distrib_right]

omit [FiniteDimensional ℝ F] in
/-- The second map of the Mayer–Vietoris sequence of the Thom pairs over `U` and `V` is the second
map of the Mayer–Vietoris sequence of the two pairs of subsets of the total space. -/
private theorem biprod_desc_thomPairOverSignHomologyMap_comp_hom (U V : Set B) (n : ℕ) :
    Limits.biprod.desc
        (thomPairOverSignHomologyMap F E hι K (subset_union_left : U ⊆ U ∪ V) n)
        (thomPairOverSignHomologyMap F E hι K (subset_union_right : V ⊆ U ∪ V) n) ≫
      (subsetPairSignHomologyIsoOfEq hι _ _ (mayerVietoris_sets F E U V).2.2.1
        (mayerVietoris_sets F E U V).2.2.2 n).hom =
      pairTwistedMayerVietorisFromBiprod (thomPairSignSystem F E hι K) inter_subset_left
        inter_subset_left n := by
  -- `erw`: the summands are `thomPairOverSignHomology` on the left and the homology of the pairs
  -- of subsets on the right, which agree only after unfolding that abbreviation.
  refine Limits.biprod.hom_ext' _ _ ?_ ?_
  · erw [Limits.biprod.inl_desc_assoc, inl_pairTwistedMayerVietorisFromBiprod]
    exact subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n
  · erw [Limits.biprod.inr_desc_assoc, inr_pairTwistedMayerVietorisFromBiprod]
    exact subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n

omit [FiniteDimensional ℝ F] in
/-- **Exactness of the Mayer–Vietoris sequence** of the Thom pairs over open sets `U` and `V` with
coefficients in the orientation local system, at the middle term. -/
private theorem thomPairOverSignHomology_mayerVietoris_exact {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (n : ℕ) :
    (ShortComplex.mk _ _ (thomPairOverSignHomologyMap_comp_zero (F := F) (E := E) hι (K := K)
      (U := U) (V := V) n)).Exact := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  obtain ⟨h₁, h₂, h₃, h₄⟩ := mayerVietoris_sets F E U V
  refine (ShortComplex.exact_iff_of_iso ?_).2 (pairTwistedMayerVietoris_exact₂
    (thomPairSignSystem F E hι K) inter_subset_left inter_subset_left hA hB hC hD n)
  have hf : Limits.biprod.lift
      (thomPairOverSignHomologyMap F E hι K (inter_subset_left : U ∩ V ⊆ U) n)
      (-thomPairOverSignHomologyMap F E hι K (inter_subset_right : U ∩ V ⊆ V) n) =
      (subsetPairSignHomologyIsoOfEq hι _ _ h₁ h₂ n).hom ≫ pairTwistedMayerVietorisToBiprod
        (thomPairSignSystem F E hι K) inter_subset_left inter_subset_left n := by
    -- `erw`, as in `biprod_desc_thomPairOverSignHomologyMap_comp_hom`: the summands agree only
    -- after unfolding `thomPairOverSignHomology`.
    refine Limits.biprod.hom_ext _ _ ?_ ?_
    · rw [Limits.biprod.lift_fst]
      erw [Category.assoc, pairTwistedMayerVietorisToBiprod_fst]
      exact (subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n).symm
    · rw [Limits.biprod.lift_snd]
      erw [Category.assoc, pairTwistedMayerVietorisToBiprod_snd, Preadditive.comp_neg]
      exact congrArg Neg.neg (subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n).symm
  exact ShortComplex.isoMk (subsetPairSignHomologyIsoOfEq hι _ _ h₁ h₂ n) (Iso.refl _)
    (subsetPairSignHomologyIsoOfEq hι _ _ h₃ h₄ n) (hf.symm.trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (biprod_desc_thomPairOverSignHomologyMap_comp_hom hι U V n).symm)

omit [FiniteDimensional ℝ F] in
/-- **The end of the Mayer–Vietoris sequence**: if the homology over `U ∩ V` vanishes in degree
`n - 1` (or `n = 0`), every class over `U ∪ V` is a sum of restrictions of classes over `U` and
over `V`. -/
private theorem epi_thomPairOverSignHomology_union {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    {n : ℕ}
    (hUV : ∀ m, m + 1 = n → Limits.IsZero (thomPairOverSignHomology F E hι K (U ∩ V) m)) :
    Epi (Limits.biprod.desc (thomPairOverSignHomologyMap F E hι K (subset_union_left : U ⊆ U ∪ V) n)
      (thomPairOverSignHomologyMap F E hι K (subset_union_right : V ⊆ U ∪ V) n)) := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  obtain ⟨h₁, h₂, h₃, h₄⟩ := mayerVietoris_sets F E U V
  rw [(Iso.eq_comp_inv _).2 (biprod_desc_thomPairOverSignHomologyMap_comp_hom (E := E) hι (K := K)
    U V n)]
  refine epi_comp' ?_ (IsIso.epi_of_iso (subsetPairSignHomologyIsoOfEq hι _ _ h₃ h₄ n).inv)
  cases n with
  | zero => exact epi_pairTwistedMayerVietorisFromBiprod_zero _ _ _ hA hB hC hD
  | succ m =>
    refine (pairTwistedMayerVietoris_exact₃ _ _ _ hA hB hC hD (m + 1) m rfl).epi_f
      (Limits.IsZero.eq_of_tgt ?_ _ _)
    exact (hUV m rfl).of_iso (subsetPairSignHomologyIsoOfEq hι _ _ h₁ h₂ m).symm

/-- **Finite unions of trivializing open sets**: the map is an isomorphism over a finite union of
open sets each lying in the base set of a trivialization of the atlas. -/
theorem isIso_thomPairOverSignHomologyFinrankInv_biUnion {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ e ∈ trivializationAtlas F E, W i ⊆ e.baseSet) :
    IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω (⋃ i ∈ s, W i)) :=
  isIso_biUnion_of_mayerVietoris (ModuleCat.of K K)
    (fun _ _ h ↦ thomPairOverSignHomologyMap F E hι K h (finrank ℝ F))
    (thomPairOverSignHomologyFinrankInv F E hι K ω)
    (fun _ _ h ↦ thomPairOverSignHomologyFinrankInv_naturality hι ω h)
    (fun W ↦ ∃ e ∈ trivializationAtlas F E, W ⊆ e.baseSet)
    (fun _ _ h ⟨e, he, hW⟩ ↦ ⟨e, he, h.trans hW⟩)
    (fun _ ⟨e, he, hW⟩ ↦ have : MemTrivializationAtlas e := ⟨he⟩
      isIso_thomPairOverSignHomologyFinrankInv_of_subset hι e ω hW)
    (isIso_thomPairOverSignHomologyFinrankInv_empty hι ω)
    (fun _ _ ↦ thomPairOverSignHomologyMap_comp_zero hι _)
    (fun _ _ hU hV ↦ thomPairOverSignHomology_mayerVietoris_exact hι hU hV _)
    -- Over a trivializing set the homology vanishes below the rank, so the sequence ends there.
    (fun _ _ hU hV ⟨e, he, hW⟩ ↦ have : MemTrivializationAtlas e := ⟨he⟩
      epi_thomPairOverSignHomology_union hι hU hV fun m hm ↦
        isZero_thomPairOverSignHomology_of_subset hι K e (inter_subset_left.trans hW) (by omega) ω)
    s hWo hWe

end Gluing

/-! ### The whole base -/

section Global

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] [FiniteDimensional ℝ F] in
variable (F E) in
/-- The ambient map of the identification of the Thom pair over the whole base with the Thom pair
is the inclusion of the preimage of the base. -/
private theorem hom_fst_thomPairOverUnivIso :
    (TopPair.Hom.fst (thomPairOverUnivIso F E).hom).hom =
      ContinuousMap.subtypeVal (π F E ⁻¹' univ) :=
  ContinuousMap.ext fun v ↦ thomPairOverUnivIso_hom_fst_apply F E v

variable (F E K) in
/-- The identification of the homology of the Thom pair over the whole base with the homology of
the Thom pair `(E, E₀)` with coefficients in the orientation local system. -/
noncomputable def thomPairOverUnivSignHomologyIso (n : ℕ) :
    thomPairOverSignHomology F E hι K univ n ≅
      (thomPair F E).twistedHomology (thomPairSignSystem F E hι K) n :=
  have := TopPair.isIso_twistedHomologyCoefficientMap.{w, w, w} (P := thomPairOver F E univ)
    (f := eqToHom (congrArg (fun g ↦ (pullback g).obj (thomPairSignSystem F E hι K))
      (hom_fst_thomPairOverUnivIso F E).symm)) (k := n)
  have := LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_isIso.{w, w, w}
    (L := thomPairSignSystem F E hι K) (f := (thomPairOverUnivIso F E).hom) (n := n)
  asIso ((thomPairOver F E univ).twistedHomologyCoefficientMap
    (eqToHom (congrArg (fun g ↦ (pullback g).obj (thomPairSignSystem F E hι K))
      (hom_fst_thomPairOverUnivIso F E).symm)) n) ≪≫
    asIso (TopPair.twistedHomologyMap (thomPairOverUnivIso F E).hom
      (thomPairSignSystem F E hι K) n)

omit [FiniteDimensional ℝ F] in
/-- The identification over the whole base identifies the two pullbacks of the orientation local
system to the preimage of the base, then maps along the identification of the Thom pairs. -/
theorem thomPairOverUnivSignHomologyIso_hom (n : ℕ) :
    (thomPairOverUnivSignHomologyIso F E hι K n).hom =
      (thomPairOver F E univ).twistedHomologyCoefficientMap
          (eqToHom (congrArg (fun g ↦ (pullback g).obj (thomPairSignSystem F E hι K))
            (ContinuousMap.ext fun v ↦ thomPairOverUnivIso_hom_fst_apply F E v).symm)) n ≫
        TopPair.twistedHomologyMap (thomPairOverUnivIso F E).hom (thomPairSignSystem F E hι K) n :=
  (rfl)

variable (F E K) in
/-- The class of the fibre over `b` in `Hᵣ(E, E₀; o(E))`: the image of the generator of the fibre
pair over `b` tensored with the orientation of the fibre read alike. Given the model orientation
`ω`, it does not depend on the trivialization reading it
(`TauCeti.thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass`); replacing `ω` by `-ω`
negates it (`TauCeti.thomPairSignFiberClass_neg`). -/
noncomputable def thomPairSignFiberClass (b : B) :
    (thomPair F E).twistedHomology (thomPairSignSystem F E hι K) (finrank ℝ F) :=
  (thomPairOverUnivSignHomologyIso F E hι K _).hom
    (thomPairOverSignFiberClassOver F E hι K ω univ ⟨b, trivial⟩)

/-- Replacing the model orientation `ω` by `-ω` negates the fibre class. -/
@[simp]
theorem thomPairSignFiberClass_neg (b : B) :
    thomPairSignFiberClass F E hι K (-ω) b = -thomPairSignFiberClass F E hι K ω b := by
  rw [thomPairSignFiberClass, thomPairSignFiberClass, thomPairOverSignFiberClassOver,
    thomPairOverSignFiberClassOver, thomPairOverSignFiberClass_neg, map_neg, map_neg]

variable (F E K) in
/-- The map `H₀(B; K) ⟶ Hᵣ(E, E₀; o(E))` sending the class of a point to the fibre class over it.
-/
noncomputable def thomPairSignHomologyFinrankInv :
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) ⟶
      (thomPair F E).twistedHomology (thomPairSignSystem F E hι K) (finrank ℝ F) :=
  ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    thomPairOverSignHomologyFinrankInv F E hι K ω univ ≫
      (thomPairOverUnivSignHomologyIso F E hι K _).hom

/-- The map sends the class of a point to the fibre class over it. -/
@[reassoc]
theorem singularHomology₀Section_thomPairSignHomologyFinrankInv (b : B) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b ≫
        thomPairSignHomologyFinrankInv F E hι K ω =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (thomPairSignFiberClass F E hι K ω b)) := by
  rw [thomPairSignHomologyFinrankInv, singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_thomPairOverSignHomologyFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp]
  -- The point `(Homeomorph.Set.univ B).symm b` of `univ` is `⟨b, trivial⟩` by definition, so both
  -- sides are the image of the fibre class over it in `Hᵣ(E, E₀; o(E))`.
  rfl

/-- The map sends the class of `b` to the fibre class over `b`. -/
@[simp]
theorem thomPairSignHomologyFinrankInv_apply_singularHomology₀Section (b : B) :
    thomPairSignHomologyFinrankInv F E hι K ω
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1) =
      thomPairSignFiberClass F E hι K ω b := by
  rw [← ConcreteCategory.comp_apply, singularHomology₀Section_thomPairSignHomologyFinrankInv]
  simp

/-- Over a base covered by finitely many trivializing open sets of the atlas, the map is an
isomorphism. -/
theorem isIso_thomPairSignHomologyFinrankInv_of_biUnion (s : Finset B)
    (hs : ⋃ c ∈ s, (trivializationAt F E c).baseSet = univ) :
    IsIso (thomPairSignHomologyFinrankInv F E hι K ω) := by
  have : IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω univ) := by
    rw [← hs]
    exact isIso_thomPairOverSignHomologyFinrankInv_biUnion hι ω s
      (fun c _ ↦ (trivializationAt F E c).open_baseSet) fun c _ ↦
        ⟨trivializationAt F E c, trivialization_mem_atlas F E c, subset_rfl⟩
  rw [thomPairSignHomologyFinrankInv]
  infer_instance

/-- Over a compact base, the map is an isomorphism. -/
theorem isIso_thomPairSignHomologyFinrankInv [CompactSpace B] :
    IsIso (thomPairSignHomologyFinrankInv F E hι K ω) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun c ↦ (trivializationAt F E c).baseSet)
    (fun c ↦ (trivializationAt F E c).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩
  exact isIso_thomPairSignHomologyFinrankInv_of_biUnion hι ω s (univ_subset_iff.1 hs)

variable (F E K) in
/-- **The Thom pair with coefficients in the orientation local system in the rank degree**: for a
real vector bundle `E → B` of rank `r` over a compact base, `Hᵣ(E, E₀; o(E)) ≅ H₀(B; K)`, where
`o(E)` is the orientation local system pulled back to the total space. No orientation of `E` is
needed: the isomorphism sends the fibre class over `b` to the class of `b`, and depends on the
model orientation `ω` only up to sign. -/
noncomputable def thomPairSignHomologyFinrankIso [CompactSpace B] (ω : Orientation ℝ F ι) :
    (thomPair F E).twistedHomology (thomPairSignSystem F E hι K) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  (@asIso _ _ _ _ (thomPairSignHomologyFinrankInv F E hι K ω)
    (isIso_thomPairSignHomologyFinrankInv hι ω)).symm

/-- The isomorphism `Hᵣ(E, E₀; o(E)) ≅ H₀(B; K)` sends the fibre class over `b` to the class of
`b`. -/
@[simp]
theorem thomPairSignHomologyFinrankIso_hom_apply [CompactSpace B] (b : B) :
    (thomPairSignHomologyFinrankIso F E hι K ω).hom (thomPairSignFiberClass F E hι K ω b) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1 := by
  have := isIso_thomPairSignHomologyFinrankInv (E := E) hι (K := K) ω
  have h := congrArg (fun f ↦ f (1 : K))
    (singularHomology₀Section_thomPairSignHomologyFinrankInv (E := E) hι (K := K) ω b)
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
    ConcreteCategory.comp_apply] at h
  rw [← h, thomPairSignHomologyFinrankIso, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-- The inverse of `Hᵣ(E, E₀; o(E)) ≅ H₀(B; K)` sends the class of a point to the fibre class over
it. -/
@[simp]
theorem thomPairSignHomologyFinrankIso_inv [CompactSpace B] :
    (thomPairSignHomologyFinrankIso F E hι K ω).inv = thomPairSignHomologyFinrankInv F E hι K ω :=
  (rfl)

/-- The inverse of `Hᵣ(E, E₀; o(E)) ≅ H₀(B; K)` sends the class of `b` to the fibre class over `b`.
-/
theorem thomPairSignHomologyFinrankIso_inv_apply [CompactSpace B] (b : B) :
    (thomPairSignHomologyFinrankIso F E hι K ω).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of B) b 1) =
      thomPairSignFiberClass F E hι K ω b := by
  rw [thomPairSignHomologyFinrankIso_inv,
    thomPairSignHomologyFinrankInv_apply_singularHomology₀Section]

end Global

end TauCeti
