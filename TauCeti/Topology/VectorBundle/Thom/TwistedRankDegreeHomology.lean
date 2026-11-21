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

(`TauCeti.thomPairSignHomologyFinrankIso`). No orientation of `E` is needed. The isomorphism sends
the fibre class over `b` to the class of `b` (`TauCeti.thomPairSignHomologyFinrankIso_hom_apply`).
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
`Hᵣ(F, F ∖ {0}; K)`. Every other trivialization `e'` of the atlas reads it the same way
(`TauCeti.thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass`): if `e'` reads the
orientations of `E_x` oppositely, both the trivialization of `o(E)` and the generator of the fibre
pair change sign, and the two signs cancel. This is what makes the fibre classes, unlike the
fibre classes with constant coefficients, independent of all choices but `ω`.

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
(`TauCeti.isIso_thomPairOverSignHomologyFinrankInv_biUnion`). A compact base is such a union.

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

namespace TauCeti.VectorBundleOrientationCover

variable (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (ω : Orientation ℝ F ι)

/-- Over the base set of a trivialization `e` of the atlas, the orientation local system is
trivialized by evaluating at the orientations read by `e` as a fixed orientation `ω` of the model
fibre. -/
noncomputable def signLocalSystemPullbackIsoOfMapsTo {Y : TopCat.{w}} (g : C(Y, B))
    (hg : ∀ y, g y ∈ e.baseSet) :
    (LocalCoefficientSystem.pullback g).obj (signLocalSystem F E K hι) ≅
      (LocalCoefficientSystem.constantFunctor Y).obj (ModuleCat.of K K) :=
  NatIso.ofComponents
    (fun y ↦ (signLocalSystemObjEquiv hι ((FundamentalGroupoid.map g).obj y) ≪≫ₗ
      signFiberEquiv deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h)
        ⟨⟨g y.as, (e.mapOrientation ι (hg y.as)).symm ω⟩, rfl⟩).toModuleIso)
    fun {y y'} γ ↦ by
      have hs : Continuous fun y : Y ↦ (⟨g y, (e.mapOrientation ι (hg y)).symm ω⟩ :
          VectorBundleOrientationCover F E ι) :=
        (continuous_mk_mapOrientation_symm hι e ω).comp
          (g.continuous.subtype_mk hg : Continuous fun y : Y ↦ (⟨g y, hg y⟩ : e.baseSet))
      refine ModuleCat.hom_ext <| LinearMap.ext fun f ↦ ?_
      have h := (isCoveringMap_proj hι).monodromy_map_lift g hs (fun _ ↦ rfl) (inv γ)
      rw [Functor.map_inv] at h
      -- Both sides evaluate a function on the orientations of a fibre; `change` exposes these
      -- evaluations behind the coercions of the module category.
      change signFiberEquiv _ _ _ (signLocalSystemObjEquiv hι _
          (((signLocalSystem F E K hι).map ((FundamentalGroupoid.map g).map γ)).hom f)) =
        signFiberEquiv _ _ _ (signLocalSystemObjEquiv hι _ f)
      rw [signFiberEquiv_apply, signFiberEquiv_apply]
      exact (signLocalSystemObjEquiv_map_apply hι _ f _).trans
        (congrArg (fun q ↦ (signLocalSystemObjEquiv hι _ f : _ → K) q) h)

omit [MemTrivializationAtlas e] in
/-- Two trivializations of the atlas reading the same orientations along `g` as `ω` give the same
trivialization of the orientation local system along `g`. -/
theorem signLocalSystemPullbackIsoOfMapsTo_hom_eq (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {Y : TopCat.{w}} (g : C(Y, B))
    (hg : ∀ y, g y ∈ e.baseSet) (hg' : ∀ y, g y ∈ e'.baseSet)
    (h : ∀ y, (e.mapOrientation ι (hg y)).symm ω = (e'.mapOrientation ι (hg' y)).symm ω) :
    (signLocalSystemPullbackIsoOfMapsTo (K := K) hι e ω g hg).hom =
      (signLocalSystemPullbackIsoOfMapsTo hι e' ω g hg').hom := by
  ext y f
  -- Both components evaluate at the orientations read as `ω`, which agree by `h`.
  change signFiberEquiv _ _ _ (signLocalSystemObjEquiv hι _ f) =
    signFiberEquiv _ _ _ (signLocalSystemObjEquiv hι _ f)
  rw [h y.as]

omit [MemTrivializationAtlas e] in
/-- Two trivializations of the atlas reading opposite orientations along `g` as `ω` give opposite
trivializations of the orientation local system along `g`. -/
theorem signLocalSystemPullbackIsoOfMapsTo_hom_eq_neg (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {Y : TopCat.{w}} (g : C(Y, B))
    (hg : ∀ y, g y ∈ e.baseSet) (hg' : ∀ y, g y ∈ e'.baseSet)
    (h : ∀ y, (e.mapOrientation ι (hg y)).symm ω = -(e'.mapOrientation ι (hg' y)).symm ω) :
    (signLocalSystemPullbackIsoOfMapsTo (K := K) hι e ω g hg).hom =
      -(signLocalSystemPullbackIsoOfMapsTo hι e' ω g hg').hom := by
  ext y f
  -- Both components evaluate at the orientations read as `ω`, which are opposite by `h`, and
  -- the deck involution exchanges them.
  change signFiberEquiv _ _ _ (signLocalSystemObjEquiv hι _ f) =
    -signFiberEquiv _ _ _ (signLocalSystemObjEquiv hι _ f)
  have hd : Function.fiberMap _ proj_comp_deck ((FundamentalGroupoid.map g).obj y).as
      ⟨⟨g y.as, (e'.mapOrientation ι (hg' y.as)).symm ω⟩, rfl⟩ =
      (⟨⟨g y.as, (e.mapOrientation ι (hg y.as)).symm ω⟩, rfl⟩ :
        (proj ⁻¹' {((FundamentalGroupoid.map g).obj y).as} :
          Set (VectorBundleOrientationCover F E ι))) :=
    Subtype.ext (by simp [deck_apply, h y.as])
  have key := signFiberEquiv_fiberMap (R := K) (hσ := proj_comp_deck) deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h)
    (⟨⟨g y.as, (e'.mapOrientation ι (hg' y.as)).symm ω⟩, rfl⟩ :
      (proj ⁻¹' {((FundamentalGroupoid.map g).obj y).as} :
        Set (VectorBundleOrientationCover F E ι))) (signLocalSystemObjEquiv hι _ f)
  rw [hd] at key
  exact key

end TauCeti.VectorBundleOrientationCover

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

/-- The identifications with untwisted homology over subsets of the base set of `e` commute with
the restrictions. -/
theorem thomPairOverSignHomologyMap_comp_iso_hom {W W' : Set B} (h : W ⊆ W')
    (hW' : W' ⊆ e.baseSet) (n : ℕ) :
    thomPairOverSignHomologyMap F E hι K h n ≫
        (thomPairOverSignHomologyIso hι K e ω hW' n).hom =
      (thomPairOverSignHomologyIso hι K e ω (h.trans hW') n).hom ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) n := by
  have hc : (pullbackCompIso
          (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h))).hom
          (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' W'))).hom).hom.app
          (thomPairSignSystem F E hι K) ≫
        (pullback (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h))).hom).map
          (thomPairOverSignSystemIso hι K e ω hW').hom ≫
        (pullbackConstantIso _ _).hom =
      (thomPairOverSignSystemIso hι K e ω (h.trans hW')).hom := by
    ext v : 2
    erw [NatTrans.comp_app, NatTrans.comp_app, pullbackCompIso_hom_app_app, Category.id_comp,
      pullback_map_app, pullbackConstantIso_hom_app, Category.comp_id]
    erw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Iso.symm_hom,
      Iso.symm_hom, Iso.app_inv, Iso.app_inv, pullbackCompIso_inv_app_app,
      pullbackCompIso_inv_app_app]
    rfl
  simp only [thomPairOverSignHomologyMap, thomPairOverSignHomologyIso, Iso.trans_hom, asIso_hom]
  rw [subsetPairTwistedChainComplexMap_def]
  erw [HomologicalComplex.homologyMap_comp]
  refine (Category.assoc _ _ _).trans ?_
  let f : thomPairOver F E W ⟶ thomPairOver F E W' :=
    TopPair.ofHom (X := TopPair.ofInclusion _) (Y := TopPair.ofInclusion _)
      (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (f := π F E) h)))
      (TopCat.ofHom (ContinuousMap.inclusion
        (inter_subset_inter_left (zeroSectionCompl F E) (preimage_mono (f := π F E) h)))) rfl
  have hf : f = thomPairOverMap F E h := TopPair.hom_ext_of_fst _ (thomPairOverMap_fst F E h).symm
  have key := TopPair.twistedHomologyMap_naturality_assoc f
    (thomPairOverSignSystem F E hι K W') (thomPairOverSignSystemIso hι K e ω hW').hom n
    ((thomPairOver F E W').twistedHomologyConstantIso (ModuleCat.of K K) n).hom
  erw [key, TopPair.twistedHomologyConstantIso_hom_pair_naturality (ModuleCat.of K K) f n]
  erw [← TopPair.twistedHomologyCoefficientMap_comp_assoc,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  rw [← hf, Category.assoc]
  have hc' := (Category.assoc _ _ _).trans hc
  erw [hc']
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
which the trivialization at `c` reads as the generator `TauCeti.complZeroPairGenerator` of
`Hᵣ(F, F ∖ {0}; K)`. -/
noncomputable def thomPairOverFiberGenerator (c x : B)
    (hx : x ∈ (trivializationAt F E c).baseSet) :
    ((thomPairOver F E {x}).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E (mem_singleton x)) (ModuleCat.of K K)
    (finrank ℝ F) (TopPair.singularHomologyMap
      ((trivializationAt F E c).continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
      (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F))

private theorem singularHomologyMap_thomPairOverIso_thomPairOverFiberGenerator (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) (x : W) :
    TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
        (ModuleCat.of K K) (finrank ℝ F)
        (TopPair.singularHomologyMap (thomPairOverMap F E (singleton_subset_iff.2 x.property))
          (ModuleCat.of K K) (finrank ℝ F)
          (thomPairOverFiberGenerator K c x (hW x.property))) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  rw [thomPairOverFiberGenerator, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, ← Category.assoc, fiberThomPairOverMap_comp_thomPairOverMap,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ _ hW x.property,
    ← TopPair.singularHomologyMap_comp, Iso.inv_hom_id_assoc, Subtype.coe_eta]
  exact singularHomologyMap_prodThomPairFiberMap_complZeroPairGenerator K F x

variable (F E K) in
/-- The canonical class of the fibre pair over `x` with coefficients in the orientation local
system: read by the trivialization at `x`, it is the fibre generator tensored with the orientation
read as `ω`. -/
noncomputable def thomPairOverSignFiberClass (x : B) :
    thomPairOverSignHomology F E hι K {x} (finrank ℝ F) :=
  (thomPairOverSignHomologyIso hι K (trivializationAt F E x) ω
    (singleton_subset_iff.2 (FiberBundle.mem_baseSet_trivializationAt' x)) _).inv
    (thomPairOverFiberGenerator K x x (FiberBundle.mem_baseSet_trivializationAt' x))

include hι in
/-- Two trivializations reading the orientation of the fibre over `x` alike have the same fibre
generators, and opposite ones if they read it oppositely. -/
private theorem thomPairOverFiberGenerator_eq_or (c d x : B)
    (hc : x ∈ (trivializationAt F E c).baseSet)
    (hd : x ∈ (trivializationAt F E d).baseSet) :
    (((trivializationAt F E c).mapOrientation ι hc).symm ω =
        ((trivializationAt F E d).mapOrientation ι hd).symm ω ∧
      thomPairOverFiberGenerator K c x hc = thomPairOverFiberGenerator K d x hd) ∨
    (((trivializationAt F E c).mapOrientation ι hc).symm ω =
        -((trivializationAt F E d).mapOrientation ι hd).symm ω ∧
      thomPairOverFiberGenerator K c x hc = -thomPairOverFiberGenerator K d x hd) := by
  have hhi {P Q : TopPair.{w}} (φ : P ≅ Q) (n : ℕ)
      (y : (Q.singularHomology (ModuleCat.of K K) n : ModuleCat.{w} K)) :
      TopPair.singularHomologyMap φ.hom (ModuleCat.of K K) n
        (TopPair.singularHomologyMap φ.inv (ModuleCat.of K K) n y) = y := by
    rw [← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp, Iso.inv_hom_id,
      TopPair.singularHomologyMap_id, ConcreteCategory.id_apply]
  set ec := trivializationAt F E c
  set ed := trivializationAt F E d
  set o := (ed.mapOrientation ι hd).symm ω
  have hod : ed.mapOrientation ι hd o = ω := Equiv.apply_symm_apply _ ω
  have hinj := (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
    (ec.continuousLinearEquivAt ℝ x hc).complZeroPairIso.hom (ModuleCat.of K K) (finrank ℝ F))).1
    inferInstance
  rcases Orientation.eq_or_eq_neg (ec.mapOrientation ι hc o) ω
    (by rw [Nat.card_eq_fintype_card, hι]) with h | h
  · refine Or.inl ⟨(Equiv.symm_apply_eq _).2 h.symm, ?_⟩
    have hh := ed.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq ec hd hc hι
      (ModuleCat.of K K) (h.trans hod.symm) (finrank ℝ F)
    have h' : TopPair.singularHomologyMap (ec.continuousLinearEquivAt ℝ x hc).complZeroPairIso.inv
        (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F) =
        TopPair.singularHomologyMap (ed.continuousLinearEquivAt ℝ x hd).complZeroPairIso.inv
          (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F) :=
      hinj (by rw [hhi, hh,
        hhi])
    rw [thomPairOverFiberGenerator, thomPairOverFiberGenerator, h']
  · refine Or.inr ⟨(Equiv.symm_apply_eq _).2 ?_, ?_⟩
    · rw [Trivialization.mapOrientation_neg, h]
      exact (neg_neg (G := Orientation ℝ F ι) ω).symm
    have hh := ed.singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg ec hd hc
      hι (ModuleCat.of K K) (h.trans (congrArg Neg.neg hod.symm)) (finrank ℝ F)
    have h' : TopPair.singularHomologyMap (ec.continuousLinearEquivAt ℝ x hc).complZeroPairIso.inv
        (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F) =
        -TopPair.singularHomologyMap (ed.continuousLinearEquivAt ℝ x hd).complZeroPairIso.inv
          (ModuleCat.of K K) (finrank ℝ F) (complZeroPairGenerator K F) :=
      hinj (by
        have hneg : ∀ {M N : ModuleCat.{w} K} (f : M ⟶ N) (y : M), (-f) y = -f y :=
          fun _ _ ↦ rfl
        rw [hhi, map_neg, hh, hneg,
          hhi, neg_neg])
    rw [thomPairOverFiberGenerator, thomPairOverFiberGenerator, h', map_neg]

omit [FiniteDimensional ℝ F] in
/-- Over the fibre over `x`, the two trivializations of the orientation local system given by
trivializations of the atlas reading the orientation over `x` alike agree, and they are opposite if
the readings are opposite. -/
private theorem thomPairOverSignHomologyIso_singleton_hom_eq_or (c d x : B)
    (hc : x ∈ (trivializationAt F E c).baseSet) (hd : x ∈ (trivializationAt F E d).baseSet)
    (n : ℕ) :
    (((trivializationAt F E c).mapOrientation ι hc).symm ω =
        ((trivializationAt F E d).mapOrientation ι hd).symm ω →
      (thomPairOverSignHomologyIso hι K (trivializationAt F E c) ω (singleton_subset_iff.2 hc)
        n).hom =
        (thomPairOverSignHomologyIso hι K (trivializationAt F E d) ω (singleton_subset_iff.2 hd)
          n).hom) ∧
    (((trivializationAt F E c).mapOrientation ι hc).symm ω =
        -((trivializationAt F E d).mapOrientation ι hd).symm ω →
      (thomPairOverSignHomologyIso hι K (trivializationAt F E c) ω (singleton_subset_iff.2 hc)
        n).hom =
        -(thomPairOverSignHomologyIso hι K (trivializationAt F E d) ω (singleton_subset_iff.2 hd)
          n).hom) := by
  -- Every point of the fibre over `x` lies over `x`, where the readings are compared.
  have hx : ∀ v : ↥(π F E ⁻¹' {x}), thomPairProj F E v.val = x := fun v ↦
    (thomPairProj_apply F E v.val).trans v.property
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have key : ∀ b, b = x → ∀ (h₁ : b ∈ (trivializationAt F E c).baseSet)
        (h₂ : b ∈ (trivializationAt F E d).baseSet),
        ((trivializationAt F E c).mapOrientation ι h₁).symm ω =
          ((trivializationAt F E d).mapOrientation ι h₂).symm ω := by
      rintro b rfl _ _
      exact h
    have hτ : (thomPairOverSignSystemIso hι K (trivializationAt F E c) ω
        (singleton_subset_iff.2 hc)).hom =
        (thomPairOverSignSystemIso hι K (trivializationAt F E d) ω
          (singleton_subset_iff.2 hd)).hom :=
      congrArg (_ ≫ ·) (signLocalSystemPullbackIsoOfMapsTo_hom_eq hι _ ω _ _ _ _
        fun v ↦ key _ (hx v) _ _)
    simp only [thomPairOverSignHomologyIso, Iso.trans_hom, asIso_hom]
    rw [hτ]
  · have key : ∀ b, b = x → ∀ (h₁ : b ∈ (trivializationAt F E c).baseSet)
        (h₂ : b ∈ (trivializationAt F E d).baseSet),
        ((trivializationAt F E c).mapOrientation ι h₁).symm ω =
          -((trivializationAt F E d).mapOrientation ι h₂).symm ω := by
      rintro b rfl _ _
      exact h
    have hτ : (thomPairOverSignSystemIso hι K (trivializationAt F E c) ω
        (singleton_subset_iff.2 hc)).hom =
        -(thomPairOverSignSystemIso hι K (trivializationAt F E d) ω
          (singleton_subset_iff.2 hd)).hom :=
      (congrArg (_ ≫ ·) (signLocalSystemPullbackIsoOfMapsTo_hom_eq_neg hι _ ω _ _ _ _
        fun v ↦ key _ (hx v) _ _)).trans (Preadditive.comp_neg _ _)
    simp only [thomPairOverSignHomologyIso, Iso.trans_hom, asIso_hom]
    rw [hτ, TopPair.twistedHomologyCoefficientMap_neg, Preadditive.neg_comp]

/-- **The fibre class is canonical**: every trivialization of the atlas whose base set contains
`x` reads it as its fibre generator. -/
theorem thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass (c x : B)
    (hc : x ∈ (trivializationAt F E c).baseSet) :
    (thomPairOverSignHomologyIso hι K (trivializationAt F E c) ω (singleton_subset_iff.2 hc)
        (finrank ℝ F)).hom (thomPairOverSignFiberClass F E hι K ω x) =
      thomPairOverFiberGenerator K c x hc := by
  have hd := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) x
  obtain ⟨h₁, h₂⟩ := thomPairOverSignHomologyIso_singleton_hom_eq_or hι (K := K) ω c x x hc hd
    (finrank ℝ F)
  have hκ : (thomPairOverSignHomologyIso hι K (trivializationAt F E x) ω
      (singleton_subset_iff.2 hd) (finrank ℝ F)).hom (thomPairOverSignFiberClass F E hι K ω x) =
      thomPairOverFiberGenerator K x x hd := Iso.inv_hom_id_apply _ _
  rcases thomPairOverFiberGenerator_eq_or hι (K := K) ω c x x hc hd with ⟨ho, hg⟩ | ⟨ho, hg⟩
  · rw [h₁ ho, hκ, hg]
  · have hneg : ∀ {M N : ModuleCat.{w} K} (f : M ⟶ N) (y : M), (-f) y = -f y := fun _ _ ↦ rfl
    rw [h₂ ho, hneg, hκ, hg]

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
      thomPairOverSignHomologyMap F E hι K (h.trans h') n := by
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap _ _ _ _ _ _ _ _))

/-- Restricting from `W` to `W'` carries fibre classes to fibre classes. -/
@[simp]
theorem thomPairOverSignHomologyMap_fiberClassOver {W W' : Set B} (h : W ⊆ W') (x : W) :
    thomPairOverSignHomologyMap F E hι K h _ (thomPairOverSignFiberClassOver F E hι K ω W x) =
      thomPairOverSignFiberClassOver F E hι K ω W' (inclusion h x) := by
  rw [thomPairOverSignFiberClassOver, thomPairOverSignFiberClassOver,
    ← ConcreteCategory.comp_apply, thomPairOverSignHomologyMap_comp]

/-- Over a subset `W` of the base set of the trivialization at `c`, reading the fibre class over
`x` through the trivialization gives the class of `x` under
`Hᵣ(W × F, W × (F ∖ {0}); K) ≅ H₀(W; K)`. -/
private theorem singularHomologyMap_thomPairOverIso_thomPairOverSignFiberClassOver (c : B)
    {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) (x : W) :
    TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
        (ModuleCat.of K K) (finrank ℝ F)
        ((thomPairOverSignHomologyIso hι K (trivializationAt F E c) ω hW (finrank ℝ F)).hom
          (thomPairOverSignFiberClassOver F E hι K ω W x)) =
      (prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)).inv
        (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1) := by
  have hψ : (thomPairOverSignHomologyIso hι K (trivializationAt F E c) ω hW (finrank ℝ F)).hom
      (thomPairOverSignFiberClassOver F E hι K ω W x) =
      TopPair.singularHomologyMap (thomPairOverMap F E (singleton_subset_iff.2 x.property))
        (ModuleCat.of K K) (finrank ℝ F) (thomPairOverFiberGenerator K c x (hW x.property)) := by
    rw [thomPairOverSignFiberClassOver, ← ConcreteCategory.comp_apply,
      thomPairOverSignHomologyMap_comp_iso_hom, ConcreteCategory.comp_apply,
      thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass hι ω c x (hW x.property)]
  rw [hψ]
  exact singularHomologyMap_thomPairOverIso_thomPairOverFiberGenerator c hW x

/-- The fibre classes over two points of `W` joined by a path in `W` inside the base set of the
trivialization at `c` agree. -/
private theorem thomPairOverSignFiberClassOver_eq_of_joinedIn (c : B) {W : Set B} {x y : W}
    (h : JoinedIn {z : W | (z : B) ∈ (trivializationAt F E c).baseSet} x y) :
    thomPairOverSignFiberClassOver F E hι K ω W x =
      thomPairOverSignFiberClassOver F E hι K ω W y := by
  set T := (trivializationAt F E c).baseSet
  have hW : W ∩ T ⊆ T := inter_subset_right
  let x' : ↥(W ∩ T) := ⟨x, x.property, h.source_mem⟩
  let y' : ↥(W ∩ T) := ⟨y, y.property, h.target_mem⟩
  have hj : Joined x' y' :=
    h.joined_subtype.map (f := fun z : {z : W | (z : B) ∈ T} ↦
      (⟨z.val.val, z.val.property, z.property⟩ : ↥(W ∩ T))) (by fun_prop)
  have hxy : thomPairOverSignFiberClassOver F E hι K ω (W ∩ T) x' =
      thomPairOverSignFiberClassOver F E hι K ω (W ∩ T) y' := by
    apply (ModuleCat.mono_iff_injective ((thomPairOverSignHomologyIso hι K
      (trivializationAt F E c) ω hW (finrank ℝ F)).hom ≫ TopPair.singularHomologyMap
        ((trivializationAt F E c).thomPairOverIso ℝ hW).hom (ModuleCat.of K K)
          (finrank ℝ F))).1 inferInstance
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      singularHomologyMap_thomPairOverIso_thomPairOverSignFiberClassOver,
      singularHomologyMap_thomPairOverIso_thomPairOverSignFiberClassOver,
      singularHomology₀Section_eq_of_joined _ hj]
  have := congrArg (thomPairOverSignHomologyMap F E hι K (inter_subset_left : W ∩ T ⊆ W) _) hxy
  rwa [thomPairOverSignHomologyMap_fiberClassOver,
    thomPairOverSignHomologyMap_fiberClassOver] at this

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
  refine (thomPairOverSignFiberClassOver_eq_of_joinedIn hι ω (γ t : B)
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
    ModuleCat.ofHom_toSpanSingleton_comp, thomPairOverSignHomologyMap_fiberClassOver]
  rw [ConcreteCategory.hom_ofHom, show ContinuousMap.inclusion h x = inclusion h x from
    Subtype.ext ((ContinuousMap.inclusion_apply_coe h x).trans (coe_inclusion h x).symm)]

/-- Over a subset of the base set of a chosen trivialization, the map is an isomorphism: read
through the trivialization it is the isomorphism `H₀(W) ≅ Hᵣ(W × F, W × (F ∖ {0}))` of the product
bundle. -/
private theorem isIso_thomPairOverSignHomologyFinrankInv_of_subset (c : B) {W : Set B}
    (hW : W ⊆ (trivializationAt F E c).baseSet) :
    IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω W) := by
  have h : thomPairOverSignHomologyFinrankInv F E hι K ω W ≫
      (thomPairOverSignHomologyIso hι K (trivializationAt F E c) ω hW (finrank ℝ F)).hom ≫
        TopPair.singularHomologyMap ((trivializationAt F E c).thomPairOverIso ℝ hW).hom
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

variable (K) in
/-- The map of twisted homology induced by an inclusion of pairs of subsets of the total space. -/
private noncomputable abbrev subsetPairSignHomologyMap {A₁ C₁ A₂ C₂ : Set (thomPair F E).fst}
    (hC₁ : C₁ ⊆ A₁) (hC₂ : C₂ ⊆ A₂) (hA : A₁ ⊆ A₂) (hC : C₁ ⊆ C₂) (n : ℕ) :=
  HomologicalComplex.homologyMap
    (subsetPairTwistedChainComplexMap (thomPairSignSystem F E hι K) hC₁ hC₂ hA hC) n

omit [FiniteDimensional ℝ F] in
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
    refine Limits.biprod.hom_ext _ _ ?_ ?_
    · rw [Limits.biprod.lift_fst]
      erw [Category.assoc, pairTwistedMayerVietorisToBiprod_fst]
      exact (subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n).symm
    · rw [Limits.biprod.lift_snd]
      erw [Category.assoc, pairTwistedMayerVietorisToBiprod_snd, Preadditive.comp_neg]
      exact congrArg Neg.neg (subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n).symm
  have hg : Limits.biprod.desc
      (thomPairOverSignHomologyMap F E hι K (subset_union_left : U ⊆ U ∪ V) n)
      (thomPairOverSignHomologyMap F E hι K (subset_union_right : V ⊆ U ∪ V) n) ≫
        (subsetPairSignHomologyIsoOfEq hι _ _ h₃ h₄ n).hom =
      pairTwistedMayerVietorisFromBiprod (thomPairSignSystem F E hι K) inter_subset_left
        inter_subset_left n := by
    refine Limits.biprod.hom_ext' _ _ ?_ ?_
    · erw [Limits.biprod.inl_desc_assoc, inl_pairTwistedMayerVietorisFromBiprod]
      exact subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n
    · erw [Limits.biprod.inr_desc_assoc, inr_pairTwistedMayerVietorisFromBiprod]
      exact subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n
  exact ShortComplex.isoMk (subsetPairSignHomologyIsoOfEq hι _ _ h₁ h₂ n) (Iso.refl _)
    (subsetPairSignHomologyIsoOfEq hι _ _ h₃ h₄ n) (hf.symm.trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans hg.symm)

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
  have hg : Limits.biprod.desc
      (thomPairOverSignHomologyMap F E hι K (subset_union_left : U ⊆ U ∪ V) n)
      (thomPairOverSignHomologyMap F E hι K (subset_union_right : V ⊆ U ∪ V) n) =
      pairTwistedMayerVietorisFromBiprod (thomPairSignSystem F E hι K) inter_subset_left
        inter_subset_left n ≫ (subsetPairSignHomologyIsoOfEq hι _ _ h₃ h₄ n).inv := by
    refine Limits.biprod.hom_ext' _ _ ?_ ?_
    · rw [Limits.biprod.inl_desc]
      erw [inl_pairTwistedMayerVietorisFromBiprod_assoc]
      exact (subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n).symm
    · rw [Limits.biprod.inr_desc]
      erw [inr_pairTwistedMayerVietorisFromBiprod_assoc]
      exact (subsetPairSignHomologyMap_comp hι (K := K) _ _ _ _ _ _ _ n).symm
  rw [hg]
  refine epi_comp' ?_ (IsIso.epi_of_iso (subsetPairSignHomologyIsoOfEq hι _ _ h₃ h₄ n).inv)
  cases n with
  | zero => exact epi_pairTwistedMayerVietorisFromBiprod_zero _ _ _ hA hB hC hD
  | succ m =>
    refine (pairTwistedMayerVietoris_exact₃ _ _ _ hA hB hC hD (m + 1) m rfl).epi_f
      (Limits.IsZero.eq_of_tgt ?_ _ _)
    exact (hUV m rfl).of_iso (subsetPairSignHomologyIsoOfEq hι _ _ h₁ h₂ m).symm

/-- Over `W ⊆ W'`, with the map over `W'` an isomorphism, the restriction from `W` to `W'` read
through the maps over `W` and `W'` is the map induced by the inclusion. -/
@[reassoc]
private theorem thomPairOverSignHomologyFinrankInv_comp_map_comp_inv {W W' : Set B} (h : W ⊆ W')
    [IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω W')] :
    thomPairOverSignHomologyFinrankInv F E hι K ω W ≫
        thomPairOverSignHomologyMap F E hι K h (finrank ℝ F) ≫
          inv (thomPairOverSignHomologyFinrankInv F E hι K ω W') =
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← Category.assoc, ← thomPairOverSignHomologyFinrankInv_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- In the Mayer–Vietoris step, a candidate inverse `Φ` of the map over `W'` which on the classes
over a subset `W` is the inverse of the map over `W` followed by the inclusion inverts the map over
`W'` on the classes of points of `W`. -/
private theorem singularHomology₀Section_thomPairOverSignHomologyFinrankInv_comp_of_comp_eq
    {W W' : Set B} (h : W ⊆ W') [IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω W)]
    {Φ : thomPairOverSignHomology F E hι K W' (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : thomPairOverSignHomologyMap F E hι K h (finrank ℝ F) ≫ Φ =
      inv (thomPairOverSignHomologyFinrankInv F E hι K ω W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h)))
    (x : W) :
    singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
          (TopCat.ofHom (ContinuousMap.inclusion h) x) ≫
        thomPairOverSignHomologyFinrankInv F E hι K ω W' ≫ Φ =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W')
        (TopCat.ofHom (ContinuousMap.inclusion h) x) := by
  rw [← singularHomology₀Section_naturality, Category.assoc,
    reassoc_of% (thomPairOverSignHomologyFinrankInv_naturality hι ω h), hΦ,
    IsIso.hom_inv_id_assoc]

/-- Such a `Φ` also inverts the map over `W'` on the classes over `W`. -/
private theorem thomPairOverSignHomologyMap_comp_comp_of_comp_eq {W W' : Set B} (h : W ⊆ W')
    [IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω W)]
    {Φ : thomPairOverSignHomology F E hι K W' (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W')}
    (hΦ : thomPairOverSignHomologyMap F E hι K h (finrank ℝ F) ≫ Φ =
      inv (thomPairOverSignHomologyFinrankInv F E hι K ω W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion h))) :
    thomPairOverSignHomologyMap F E hι K h (finrank ℝ F) ≫ Φ ≫
        thomPairOverSignHomologyFinrankInv F E hι K ω W' =
      thomPairOverSignHomologyMap F E hι K h (finrank ℝ F) := by
  rw [reassoc_of% hΦ, thomPairOverSignHomologyFinrankInv_naturality, IsIso.inv_hom_id_assoc]

/-- **The Mayer–Vietoris step**: if the maps over the open sets `U` and `V` are isomorphisms, the
map over `U ∩ V` is surjective and the homology over `U ∩ V` vanishes in degree `r - 1`, the map
over `U ∪ V` is an isomorphism. -/
private theorem isIso_thomPairOverSignHomologyFinrankInv_union {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) [IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω U)]
    [IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω V)]
    [Epi (thomPairOverSignHomologyFinrankInv F E hι K ω (U ∩ V))]
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      Limits.IsZero (thomPairOverSignHomology F E hι K (U ∩ V) m)) :
    IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω (U ∪ V)) := by
  let ψ := thomPairOverSignHomologyFinrankInv F E hι K ω
  let H₀ := (singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)
  let S := ShortComplex.mk _ _ (thomPairOverSignHomologyMap_comp_zero (F := F) (E := E) hι
    (K := K) (U := U) (V := V) (finrank ℝ F))
  have hS : S.Exact := thomPairOverSignHomology_mayerVietoris_exact hι hU hV _
  have : Epi S.g := epi_thomPairOverSignHomology_union hι hU hV hUV
  -- The inverse map, on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ H₀.obj (TopCat.of ↥(U ∪ V)) :=
    Limits.biprod.desc
      (inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)))
      (inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)))
  -- It vanishes on the image of the first map, since both restrictions of a class over `U ∩ V`
  -- give the same class over `U ∪ V`.
  have hφ : S.f ≫ φ = 0 := by
    rw [← cancel_epi (ψ (U ∩ V)), Limits.comp_zero]
    simp only [S, φ, ψ, H₀, Limits.biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, thomPairOverSignHomologyFinrankInv_comp_map_comp_inv_assoc,
      ← Functor.map_comp, ← TopCat.ofHom_comp, ContinuousMap.inclusion_comp_inclusion,
      add_neg_eq_zero]
  let Φ := (hS.gIsCokernel).desc (Limits.CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ :=
    (hS.gIsCokernel).fac (Limits.CokernelCofork.ofπ φ hφ) Limits.WalkingParallelPair.one
  -- On the classes over `U` and over `V`, `Φ` is the inverse of the map over `U` or `V`.
  have hΦ {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (ψ W)]
      (j : thomPairOverSignHomology F E hι K W (finrank ℝ F) ⟶ S.X₂)
      (hj : j ≫ S.g = thomPairOverSignHomologyMap F E hι K hW (finrank ℝ F))
      (hjφ : j ≫ φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW))) :
      thomPairOverSignHomologyMap F E hι K hW (finrank ℝ F) ≫ Φ =
        inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW)) := by
    rw [← hj, Category.assoc, hgΦ, hjφ]
  have hΦU := hΦ subset_union_left Limits.biprod.inl (Limits.biprod.inl_desc _ _)
    (Limits.biprod.inl_desc _ _)
  have hΦV := hΦ subset_union_right Limits.biprod.inr (Limits.biprod.inr_desc _ _)
    (Limits.biprod.inr_desc _ _)
  refine ⟨Φ, singularHomology₀_hom_ext _ fun x ↦ ?_, (cancel_epi S.g).1
    (Limits.biprod.hom_ext' _ _ ?_ ?_)⟩
  · -- A point of `U ∪ V` lies in `U` or in `V`, where the composite is computed.
    rw [Category.comp_id]
    obtain ⟨x, hx | hx⟩ := x
    · exact singularHomology₀Section_thomPairOverSignHomologyFinrankInv_comp_of_comp_eq hι ω _
        hΦU ⟨x, hx⟩
    · exact singularHomology₀Section_thomPairOverSignHomologyFinrankInv_comp_of_comp_eq hι ω _
        hΦV ⟨x, hx⟩
  · simpa [S] using thomPairOverSignHomologyMap_comp_comp_of_comp_eq hι ω _ hΦU
  · simpa [S] using thomPairOverSignHomologyMap_comp_comp_of_comp_eq hι ω _ hΦV

/-- **Finite unions of trivializing open sets**: the map is an isomorphism over a finite union of
open sets each lying in the base set of a chosen trivialization. -/
theorem isIso_thomPairOverSignHomologyFinrankInv_biUnion {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ c, W i ⊆ (trivializationAt F E c).baseSet) :
    IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset κ), W i) = ∅ by simp]
    exact isIso_thomPairOverSignHomologyFinrankInv_empty hι ω
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨c, hc⟩ := hWe a (Finset.mem_insert_self a s)
    have : IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω (W a)) :=
      isIso_thomPairOverSignHomologyFinrankInv_of_subset hι ω c hc
    have : IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    have : IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
        (hWo i (Finset.mem_insert_of_mem hi))) fun i hi ↦ ?_
      obtain ⟨c', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
      exact ⟨c', inter_subset_right.trans hi'⟩
    exact isIso_thomPairOverSignHomologyFinrankInv_union hι ω
      (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      fun m hm ↦ isZero_thomPairOverSignHomology_of_subset hι K (trivializationAt F E c)
        (inter_subset_left.trans hc) (by omega) ω

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

variable (F E K) in
/-- The canonical class of the fibre over `b` in `Hᵣ(E, E₀; o(E))`: the image of the generator of
the fibre pair over `b` tensored with the orientation of the fibre read alike, which does not
depend on any choice (`TauCeti.thomPairOverSignHomologyIso_hom_thomPairOverSignFiberClass`). -/
noncomputable def thomPairSignFiberClass (b : B) :
    (thomPair F E).twistedHomology (thomPairSignSystem F E hι K) (finrank ℝ F) :=
  (thomPairOverUnivSignHomologyIso F E hι K _).hom
    (thomPairOverSignFiberClassOver F E hι K ω univ ⟨b, trivial⟩)

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
  rfl

/-- Over a base covered by finitely many trivializing open sets of the atlas, the map is an
isomorphism. -/
theorem isIso_thomPairSignHomologyFinrankInv_of_biUnion (s : Finset B)
    (hs : ⋃ c ∈ s, (trivializationAt F E c).baseSet = univ) :
    IsIso (thomPairSignHomologyFinrankInv F E hι K ω) := by
  have : IsIso (thomPairOverSignHomologyFinrankInv F E hι K ω univ) := by
    rw [← hs]
    exact isIso_thomPairOverSignHomologyFinrankInv_biUnion hι ω s
      (fun c _ ↦ (trivializationAt F E c).open_baseSet) fun c _ ↦ ⟨c, subset_rfl⟩
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
`o(E)` is the orientation local system pulled back to the total space. No orientation is needed:
the isomorphism sends the canonical fibre class over `b` to the class of `b`. -/
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

end Global

end TauCeti
