/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Twisted.ConstantNaturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.MayerVietoris.Pair
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Class
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.Topology.Connected.PathConnected

/-!
# The Thom pair in the rank degree with coefficients in the orientation system

Let `E → B` be a real vector bundle of rank `r`, with Thom pair `(E, E₀)`, `E₀` the complement of
the zero section, and let `o(E)` be its orientation local system
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), with coefficients in a commutative ring
`R`, pulled back to the total space along the projection `π`. The relative homology of the Thom
pair with coefficients in `π^*o(E)` vanishes below the rank
(`TauCeti.isZero_twistedHomology_thomPair`). This file computes the first group that does not
vanish: over a compact base,

`Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`

(`TauCeti.thomPairTwistedHomologyFinrankIso`), for every bundle, orientable or not. It sends the
twisted fibre class over `b` (`TauCeti.thomPairTwistedFiberClass`) to the class of `b`
(`TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairTwistedFiberClass`). With constant
coefficients the same group is `H₀(B; R)` only for an oriented bundle, or when `1` is the only unit
of `R` (`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`,
`TauCeti.thomPairSingularHomologyFinrankIso`): the twist by `o(E)` is what makes the fibre classes
independent of a choice of orientation. By the universal coefficient theorem, a morphism
`Hᵣ(E, E₀; π^*o(E)) ⟶ R` is a class of `Hʳ(E, E₀; π^*o(E))`, and the augmentation of `H₀(B; R)`
read through this isomorphism is the candidate for the Thom class of `E` with coefficients in its
orientation system.

## The local trivializations of the orientation system

Over the base set of a linear trivialization `e` of the atlas, the orientations of the fibres which
`e` reads as a fixed orientation `ω` of the model fibre `F` form a continuous section of the
orientation double cover. Evaluating at them trivializes `o(E)` pulled back along any map into the
base set (`TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIso`), and so identifies
homology with coefficients in it with ordinary homology
(`TauCeti.VectorBundleOrientationCover.twistedHomologyPullbackSignLocalSystemIso`), naturally in
maps of pairs. Two trivializations reading the orientations alike give the same identification, and
reversing `ω` negates it.

## The proof

The proof follows the untwisted computation of
`TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology`, after Milnor and Stasheff's proof of the
Thom isomorphism. For each point `b` the trivialization chosen at `b` identifies the coefficients
over the fibre pair `(E_b, E_b ∖ {0})` with `R`; the twisted fibre class over `b` is the class which
it then reads as the class of the fibre pair read as a generator `γ` of `Hᵣ(F, F ∖ {0}; R)`. Any
other trivialization `e` of the atlas reads the same class as the fibre class which `e` reads as
`γ`: if `e` reads the orientations of `E_b` oppositely, both the identification of the coefficients
and the fibre class change sign. So over a subset `W` of the base set of `e`, reading through `e`
carries the twisted fibre classes to the ordinary fibre classes read by `e`, which the product
computation `Hᵣ(W × F, W × (F ∖ {0}); R) ≅ H₀(W; R)` (`TauCeti.prodThomPairSingularHomologyIso`)
identifies with the classes of the points multiplied by a unit. Hence the twisted fibre classes are
constant along paths, they define a map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; π^*o(E))` for every `W`, natural
in `W`, and this map is an isomorphism over every subset of the base set of a trivialization. The
Mayer–Vietoris sequence of two pairs with local coefficients
(`TauCeti.LocalCoefficientSystem.pairTwistedMayerVietoris_exact₂`) ends in degree `r`, since the
twisted homology vanishes below the rank, so the map is an isomorphism over every finite union of
trivializing open sets, by induction on their number. A compact base is such a union.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIso`: the trivialization of the
  orientation system pulled back along a map into the base set of a trivialization.
* `TauCeti.thomPairTwistedFiberClass`: the twisted fibre class over a point.
* `TauCeti.thomPairTwistedHomologyFinrankIso`: `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` over a compact base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over unions of
  trivializing open sets), and §12 (the orientation double cover and twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients) and Section 4.D, Theorem 4D.10
  and its proof (the Thom isomorphism with coefficients twisted by the orientation system).
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

variable {R : Type w} [CommRing R] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)

namespace VectorBundleOrientationCover

variable (R) in
/-- Over a map `g : Y → B` with values in the base set of a trivialization `e` of the atlas, the
pulled-back orientation local system is trivialized by evaluating, over each point `y`, at the
orientation of `E_{g y}` which `e` reads as a fixed orientation `ω` of the model fibre. -/
def pullbackSignLocalSystemIso (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (ω : Orientation ℝ F ι) {Y : TopCat.{w}} (g : C(Y, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet) :
    (LocalCoefficientSystem.pullback g).obj (signLocalSystem F E R hι) ≅
      (LocalCoefficientSystem.constantFunctor Y).obj (ModuleCat.of R R) :=
  NatIso.ofComponents
    (fun y ↦ (signLocalSystemFiberEquiv hι ((e.mapOrientation ι (hg y.as)).symm ω)).toModuleIso)
    fun {y y'} p ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun
        (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y.as))) ↦ ?_)
      -- The constant system transports by the identity, and the pulled-back system by transport
      -- along the image path, which the section of the cover read as `ω` lifts.
      refine (signLocalSystemFiberEquiv_map_of_monodromy hι ((FundamentalGroupoid.map g).map p)
        ?_ f).trans rfl
      induction p using Quotient.ind with | _ δ => ?_
      exact monodromy_mk_mapOrientation_symm hι e ω (δ.map g.continuous) (fun t ↦ hg (δ t)) _ _

/-- Over `y`, the trivialization evaluates at the orientation of `E_{g y}` which `e` reads as
`ω`. -/
@[simp]
theorem pullbackSignLocalSystemIso_hom_app_apply (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {Y : TopCat.{w}} (g : C(Y, TopCat.of B))
    (hg : ∀ y, g y ∈ e.baseSet) (y : Y)
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y))) :
    (ModuleCat.Hom.hom (A := (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y)))
        (B := ModuleCat.of R R)
        ((pullbackSignLocalSystemIso R hι e ω g hg).hom.app (FundamentalGroupoid.mk y))) f =
      signLocalSystemFiberEquiv hι ((e.mapOrientation ι (hg y)).symm ω) f := by
  unfold pullbackSignLocalSystemIso
  exact rfl

/-- Two trivializations and orientations of the model fibre which pull back to the same
orientations of the fibres over `g` give the same trivialization of the pulled-back orientation
local system. -/
theorem pullbackSignLocalSystemIso_congr {e e' : Trivialization F (π F E)}
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {ω ω' : Orientation ℝ F ι}
    {Y : TopCat.{w}} (g : C(Y, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet)
    (hg' : ∀ y, g y ∈ e'.baseSet)
    (h : ∀ y, (e'.mapOrientation ι (hg' y)).symm ω' = (e.mapOrientation ι (hg y)).symm ω) :
    pullbackSignLocalSystemIso R hι e' ω' g hg' = pullbackSignLocalSystemIso R hι e ω g hg := by
  refine Iso.ext (NatTrans.ext (funext fun ⟨y⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y))) ↦ ?_)))
  refine (pullbackSignLocalSystemIso_hom_app_apply hι e' ω' g hg' y f).trans ?_
  rw [h y]
  exact (pullbackSignLocalSystemIso_hom_app_apply hι e ω g hg y f).symm

/-- Reversing the orientation of the model fibre negates the trivialization of the pulled-back
orientation local system. -/
theorem pullbackSignLocalSystemIso_neg_hom (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {Y : TopCat.{w}} (g : C(Y, TopCat.of B))
    (hg : ∀ y, g y ∈ e.baseSet) :
    (pullbackSignLocalSystemIso R hι e (-ω) g hg).hom =
      -(pullbackSignLocalSystemIso R hι e ω g hg).hom := by
  refine NatTrans.ext (funext fun ⟨y⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun
    (f : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk (g y))) ↦ ?_))
  have h : (e.mapOrientation ι (hg y)).symm (-ω) = -(e.mapOrientation ι (hg y)).symm ω :=
    (e.mapOrientation ι (hg y)).symm_apply_eq.2 (by
      rw [Trivialization.mapOrientation_neg, Equiv.apply_symm_apply])
  rw [NatTrans.app_neg, ModuleCat.hom_neg]
  refine (pullbackSignLocalSystemIso_hom_app_apply hι e (-ω) g hg y f).trans ?_
  rw [h, signLocalSystemFiberEquiv_neg]
  exact congrArg Neg.neg (pullbackSignLocalSystemIso_hom_app_apply hι e ω g hg y f).symm

variable (R) in
/-- Over a map `g` from the ambient space of a pair to the base set of a trivialization `e` of the
atlas, the trivialization of the pulled-back orientation local system identifies homology with
coefficients in it with ordinary homology. -/
def twistedHomologyPullbackSignLocalSystemIso (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) (P : TopPair.{w})
    (g : C(P.fst, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet) (n : ℕ) :
    P.twistedHomology ((LocalCoefficientSystem.pullback g).obj (signLocalSystem F E R hι)) n ≅
      P.singularHomology (ModuleCat.of R R) n :=
  asIso (P.twistedHomologyCoefficientMap (pullbackSignLocalSystemIso R hι e ω g hg).hom n) ≪≫
    P.twistedHomologyConstantIso (ModuleCat.of R R) n

/-- The identification of homology with coefficients in the pulled-back orientation local system
with ordinary homology is natural in maps of pairs. -/
theorem twistedHomologyMap_twistedHomologyPullbackSignLocalSystemIso_hom
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (ω : Orientation ℝ F ι)
    {P Q : TopPair.{w}} (f : P ⟶ Q) (g : C(Q.fst, TopCat.of B)) (hg : ∀ y, g y ∈ e.baseSet)
    (n : ℕ) :
    TopPair.twistedHomologyMap f ((LocalCoefficientSystem.pullback g).obj
        (signLocalSystem F E R hι)) n ≫
      (twistedHomologyPullbackSignLocalSystemIso R hι e ω Q g hg n).hom =
    P.twistedHomologyCoefficientMap
        ((LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst f).hom g).inv.app
          (signLocalSystem F E R hι)) n ≫
      (twistedHomologyPullbackSignLocalSystemIso R hι e ω P (g.comp (TopPair.Hom.fst f).hom)
        (fun _ ↦ hg _) n).hom ≫
      P.singularHomologyMap f (ModuleCat.of R R) n := by
  simp only [twistedHomologyPullbackSignLocalSystemIso, Iso.trans_hom, asIso_hom,
    TopPair.twistedHomologyMap_naturality_assoc,
    TopPair.twistedHomologyConstantIso_hom_pair_naturality,
    ← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  -- Both trivializations evaluate over `y` at the orientation that `e` reads as `ω`.
  have h : (LocalCoefficientSystem.pullback (TopPair.Hom.fst f).hom).map
        (pullbackSignLocalSystemIso R hι e ω g hg).hom ≫
      (LocalCoefficientSystem.pullbackConstantIso (TopPair.Hom.fst f).hom (ModuleCat.of R R)).hom =
      (LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst f).hom g).inv.app
          (signLocalSystem F E R hι) ≫
        (pullbackSignLocalSystemIso R hι e ω (g.comp (TopPair.Hom.fst f).hom)
          (fun _ ↦ hg _)).hom := by
    ext _ a
    simp only [NatTrans.comp_app, LocalCoefficientSystem.pullback_map_app,
      LocalCoefficientSystem.pullbackConstantIso_hom_app,
      LocalCoefficientSystem.pullbackCompIso_inv_app_app]
    exact rfl
  simp only [h, TopPair.twistedHomologyCoefficientMap_comp, Category.assoc]

end VectorBundleOrientationCover

open VectorBundleOrientationCover

/-! ### The Thom pairs over subsets of the base -/

section ThomPairOver

variable (F E) in
/-- The projection of the total space, as a map of topological spaces. -/
private abbrev projMap : C(TopCat.of (TotalSpace F E), TopCat.of B) :=
  ⟨π F E, FiberBundle.continuous_proj F E⟩

variable (F E) in
/-- The inclusion of the part of the total space over `W`. -/
private abbrev inclOver (W : Set B) : C((thomPairOver F E W).fst, TopCat.of (TotalSpace F E)) :=
  ContinuousMap.subtypeVal (π F E ⁻¹' W)

variable (R F E) in
/-- The orientation local system of `E`, pulled back to the total space and restricted to the
part over `W`: the coefficients of the Thom pair `(E|_W, E₀|_W)`. -/
private abbrev signSystemOver (W : Set B) :
    LocalCoefficientSystem R (thomPairOver F E W).fst :=
  (LocalCoefficientSystem.pullback (inclOver F E W)).obj
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))

/-- The map `Hₙ(E|_W, E₀|_W; o) ⟶ Hₙ(E|_W', E₀|_W'; o)` for `W ⊆ W'`, as a map of the relative
homology of pairs of subsets of the total space. -/
private abbrev restrictOver {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    (thomPairOver F E W).twistedHomology (signSystemOver R F E hι W) n ⟶
      (thomPairOver F E W').twistedHomology (signSystemOver R F E hι W') n :=
  HomologicalComplex.homologyMap (LocalCoefficientSystem.subsetPairTwistedChainComplexMap
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
    inter_subset_left inter_subset_left (preimage_mono h)
    (inter_subset_inter_left _ (preimage_mono h))) n

/-- The restrictions compose. -/
private theorem restrictOver_comp_restrictOver {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W'')
    (n : ℕ) :
    restrictOver (R := R) (F := F) (E := E) hι h n ≫ restrictOver hι h' n =
      restrictOver hι (h.trans h') n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans (congrArg
    (HomologicalComplex.homologyMap · n)
    (LocalCoefficientSystem.subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap
      _ _ _ _ _ _ _ _))

variable (F E) in
/-- The inclusion of Thom pairs over `W ⊆ W'`, in the form induced by inclusions of subsets of the
total space. -/
private abbrev pairInclOver {W W' : Set B} (h : W ⊆ W') :
    thomPairOver F E W ⟶ thomPairOver F E W' :=
  TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h)))
    (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_inter_left _ (preimage_mono h)))) rfl

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
private theorem pairInclOver_eq {W W' : Set B} (h : W ⊆ W') :
    pairInclOver F E h = thomPairOverMap F E h :=
  TopPair.hom_ext_of_fst _ (thomPairOverMap_fst F E h).symm

/-- The identification of the coefficients over `W` with the pull-back of those over `W' ⊇ W`. -/
private def restrictCoeff {W W' : Set B} (h : W ⊆ W') :
    signSystemOver R F E hι W ⟶ (LocalCoefficientSystem.pullback
      (TopPair.Hom.fst (pairInclOver F E h)).hom).obj (signSystemOver R F E hι W') :=
  (LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst (pairInclOver F E h)).hom
    (inclOver F E W')).hom.app _

/-- The restriction maps are induced by the inclusions of Thom pairs. -/
private theorem restrictOver_eq {W W' : Set B} (h : W ⊆ W') (n : ℕ) :
    restrictOver hι h n =
      (thomPairOver F E W).twistedHomologyCoefficientMap (restrictCoeff hι h) n ≫
      TopPair.twistedHomologyMap (pairInclOver F E h) (signSystemOver R F E hι W') n := by
  refine (congrArg (HomologicalComplex.homologyMap · n) ?_).trans
    (HomologicalComplex.homologyMap_comp _ _ n)
  refine (cancel_epi ((thomPairOver F E W).twistedChainComplexπ
    (signSystemOver R F E hι W))).1 ?_
  refine (LocalCoefficientSystem.twistedChainComplexπ_comp_subsetPairTwistedChainComplexMap
    _ _ _ _ _).trans ?_
  refine (congrArg (· ≫ _) (LocalCoefficientSystem.subsetTwistedChainComplexMap_def
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
    (preimage_mono h))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap
    (pairInclOver F E h) (signSystemOver R F E hι W')).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
    _ _).symm).trans ?_
  exact Category.assoc _ _ _

/-- Over a subset `V` of the base set of a trivialization `e` of the atlas, reading orientations
through `e` identifies `Hₙ(E|_V, E₀|_V; o)` with `Hₙ(E|_V, E₀|_V; R)`. -/
private def readOver (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (ω : Orientation ℝ F ι) {V : Set B} (hV : V ⊆ e.baseSet) (n : ℕ) :
    (thomPairOver F E V).twistedHomology (signSystemOver R F E hι V) n ⟶
      (thomPairOver F E V).singularHomology (ModuleCat.of R R) n :=
  (thomPairOver F E V).twistedHomologyCoefficientMap
      ((LocalCoefficientSystem.pullbackCompIso (inclOver F E V) (projMap F E)).inv.app
        (signLocalSystem F E R hι)) n ≫
    (twistedHomologyPullbackSignLocalSystemIso R hι e ω (thomPairOver F E V)
      ((projMap F E).comp (inclOver F E V)) (fun v ↦ hV v.property) n).hom

private instance isIso_readOver (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (ω : Orientation ℝ F ι) {V : Set B} (hV : V ⊆ e.baseSet) (n : ℕ) :
    IsIso (readOver (R := R) hι e ω hV n) := by
  have : IsIso ((LocalCoefficientSystem.pullbackCompIso (inclOver F E V) (projMap F E)).inv.app
      (signLocalSystem F E R hι)) :=
    inferInstanceAs (IsIso ((LocalCoefficientSystem.pullbackCompIso (inclOver F E V)
      (projMap F E)).app (signLocalSystem F E R hι)).inv)
  unfold readOver
  infer_instance

/-- Two trivializations reading the same orientations of the fibres over `V` read alike. -/
private theorem readOver_congr {e e' : Trivialization F (π F E)} [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] {ω ω' : Orientation ℝ F ι} {V : Set B} (hV : V ⊆ e.baseSet)
    (hV' : V ⊆ e'.baseSet)
    (h : ∀ v (hv : v ∈ V),
      (e'.mapOrientation ι (hV' hv)).symm ω' = (e.mapOrientation ι (hV hv)).symm ω) (n : ℕ) :
    readOver (R := R) hι e' ω' hV' n = readOver hι e ω hV n := by
  unfold readOver twistedHomologyPullbackSignLocalSystemIso
  simp only [Iso.trans_hom, asIso_hom]
  rw [pullbackSignLocalSystemIso_congr hι ((projMap F E).comp (inclOver F E V))
    (fun v ↦ hV v.property) (fun v ↦ hV' v.property) fun v ↦ h _ v.property]

/-- Reading through the opposite orientation of the model fibre is the negative. -/
private theorem readOver_neg (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (ω : Orientation ℝ F ι) {V : Set B} (hV : V ⊆ e.baseSet) (n : ℕ) :
    readOver (R := R) hι e (-ω) hV n = -readOver hι e ω hV n := by
  unfold readOver twistedHomologyPullbackSignLocalSystemIso
  simp only [Iso.trans_hom, asIso_hom, pullbackSignLocalSystemIso_neg_hom,
    TopPair.twistedHomologyCoefficientMap_neg, Preadditive.neg_comp, Preadditive.comp_neg]

/-- Reading through `e` commutes with the restrictions. -/
private theorem restrictOver_readOver (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {V V' : Set B} (h : V ⊆ V')
    (hV' : V' ⊆ e.baseSet) (n : ℕ) :
    restrictOver hι h n ≫ readOver hι e ω hV' n =
      readOver hι e ω (h.trans hV') n ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of R R) n := by
  rw [restrictOver_eq, ← pairInclOver_eq]
  unfold readOver
  simp only [Category.assoc]
  rw [TopPair.twistedHomologyMap_naturality_assoc,
    twistedHomologyMap_twistedHomologyPullbackSignLocalSystemIso_hom]
  simp only [← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  -- All the identifications of coefficients are identities on the fibres.
  have hc : restrictCoeff hι h ≫
      (LocalCoefficientSystem.pullback (TopPair.Hom.fst (pairInclOver F E h)).hom).map
        ((LocalCoefficientSystem.pullbackCompIso (inclOver F E V') (projMap F E)).inv.app
          (signLocalSystem F E R hι)) ≫
      (LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst (pairInclOver F E h)).hom
        ((projMap F E).comp (inclOver F E V'))).inv.app (signLocalSystem F E R hι) =
      (LocalCoefficientSystem.pullbackCompIso (inclOver F E V) (projMap F E)).inv.app
        (signLocalSystem F E R hι) := by
    ext x a
    erw [NatTrans.comp_app, NatTrans.comp_app]
    simp only [restrictCoeff, LocalCoefficientSystem.pullback_map_app,
      LocalCoefficientSystem.pullbackCompIso_hom_app_app,
      LocalCoefficientSystem.pullbackCompIso_inv_app_app]
    exact rfl
  exact congrArg (fun Z ↦ (thomPairOver F E V).twistedHomologyCoefficientMap Z n ≫ _) hc

/-! ### Fibre classes -/

omit [VectorBundle ℝ F E] in
include hι in
/-- Two trivializations reading an orientation of `E_x` alike pull back a class of
`Hₙ(F, F ∖ {0}; R)` to the same class of `Hₙ(E_x, E_x ∖ {0}; R)`. -/
private theorem singularHomologyMap_complZeroPairIso_inv_eq_of_mapOrientation_eq
    [FiniteDimensional ℝ F] {e e' : Trivialization F (π F E)} [e.IsLinear ℝ] [e'.IsLinear ℝ]
    {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) {o : Orientation ℝ (E x) ι}
    (h : e'.mapOrientation ι hx' o = e.mapOrientation ι hx o) {n : ℕ}
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) n : ModuleCat.{w} R)) :
    TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso.inv
        (ModuleCat.of R R) n γ =
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
        (ModuleCat.of R R) n γ := by
  apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
    (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso.hom (ModuleCat.of R R) n)).1
    inferInstance
  refine ((TopPair.singularHomologyMapIso _ (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso
    _).inv_hom_id_apply γ).trans ?_
  rw [Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e e' hx hx'
    hι _ h]
  exact ((TopPair.singularHomologyMapIso _ (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso
    _).inv_hom_id_apply γ).symm

omit [VectorBundle ℝ F E] in
include hι in
/-- Two trivializations reading an orientation of `E_x` oppositely pull back a class of
`Hₙ(F, F ∖ {0}; R)` to opposite classes of `Hₙ(E_x, E_x ∖ {0}; R)`. -/
private theorem singularHomologyMap_complZeroPairIso_inv_eq_neg_of_mapOrientation_eq_neg
    [FiniteDimensional ℝ F] {e e' : Trivialization F (π F E)} [e.IsLinear ℝ] [e'.IsLinear ℝ]
    {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) {o : Orientation ℝ (E x) ι}
    (h : e'.mapOrientation ι hx' o = -e.mapOrientation ι hx o) {n : ℕ}
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) n : ModuleCat.{w} R)) :
    TopPair.singularHomologyMap (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso.inv
        (ModuleCat.of R R) n γ =
      -TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
        (ModuleCat.of R R) n γ := by
  apply (ModuleCat.mono_iff_injective (TopPair.singularHomologyMap
    (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso.hom (ModuleCat.of R R) n)).1
    inferInstance
  refine ((TopPair.singularHomologyMapIso _ (e'.continuousLinearEquivAt ℝ x hx').complZeroPairIso
    _).inv_hom_id_apply γ).trans ?_
  rw [map_neg,
    Trivialization.singularHomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e e'
    hx hx' hι _ h]
  have hneg {M N : ModuleCat.{w} R} (f : M ⟶ N) (y : M) : (-f) y = -(f y) := rfl
  rw [hneg, neg_neg]
  exact ((TopPair.singularHomologyMapIso _ (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso
    _).inv_hom_id_apply γ).symm

variable (F E) in
/-- The class of `Hₙ(E|_W, E₀|_W; R)` of the fibre pair over `x ∈ W` which the linear
trivialization `e` reads as `γ`. -/
private abbrev readFiberClass (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B} {x : B}
    (hxW : x ∈ W) (hx : x ∈ e.baseSet) {n : ℕ}
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) n : ModuleCat.{w} R)) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of R R) n : ModuleCat.{w} R) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E hxW) (ModuleCat.of R R) n
    (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
      (ModuleCat.of R R) n γ)

omit [VectorBundle ℝ F E] in
/-- Restricting a fibre class read by `e` gives the fibre class read by `e`. -/
private theorem singularHomologyMap_thomPairOverMap_readFiberClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W W' : Set B} (h : W ⊆ W') {x : B} (hxW : x ∈ W) (hx : x ∈ e.baseSet)
    {n : ℕ} (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) n : ModuleCat.{w} R)) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of R R) n
        (readFiberClass F E e hxW hx γ) = readFiberClass F E e (h hxW) hx γ := by
  rw [readFiberClass, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    fiberThomPairOverMap_comp_thomPairOverMap]

/-- The twisted class of the fibre pair over `x`, in `Hₙ(E|_{x}, E₀|_{x}; o)`: the class which the
chosen trivialization at `x`, reading orientations as `ω`, reads as the fibre class it reads as
`γ`. -/
private def signFiberClass (ω : Orientation ℝ F ι) {n : ℕ}
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) n : ModuleCat.{w} R)) (x : B) :
    ((thomPairOver F E {x}).twistedHomology (signSystemOver R F E hι {x}) n : ModuleCat.{w} R) :=
  inv (readOver hι (trivializationAt F E x) ω
      (singleton_subset_iff.2 (mem_baseSet_trivializationAt F E x)) n)
    (readFiberClass F E (trivializationAt F E x) (mem_singleton x)
      (mem_baseSet_trivializationAt F E x) γ)

include hι in
/-- Every trivialization of the atlas reads the twisted fibre class as the fibre class it reads as
`γ`. -/
private theorem readOver_signFiberClass [FiniteDimensional ℝ F] (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (ω : Orientation ℝ F ι) {n : ℕ}
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) n : ModuleCat.{w} R)) {x : B} (hx : x ∈ e.baseSet) :
    readOver hι e ω (singleton_subset_iff.2 hx) n (signFiberClass hι ω γ x) =
      readFiberClass F E e (mem_singleton x) hx γ := by
  set e₀ := trivializationAt F E x
  have hx₀ : x ∈ e₀.baseSet := mem_baseSet_trivializationAt F E x
  set o := (e₀.mapOrientation ι hx₀).symm ω
  have ho : e₀.mapOrientation ι hx₀ o = ω := Equiv.apply_symm_apply _ ω
  have hι' : Nat.card ι = finrank ℝ F := Nat.card_eq_fintype_card.trans hι
  have hinv : readOver hι e₀ ω (singleton_subset_iff.2 hx₀) n (signFiberClass hι ω γ x) =
      readFiberClass F E e₀ (mem_singleton x) hx₀ γ :=
    (ConcreteCategory.congr_hom (IsIso.inv_hom_id (readOver hι e₀ ω
      (singleton_subset_iff.2 hx₀) n)) _)
  rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hx o) ω hι' with h | h
  · -- `e` reads the orientations of `E_x` as `e₀` does.
    rw [readOver_congr hι (singleton_subset_iff.2 hx₀) (singleton_subset_iff.2 hx)
      (ω := ω) (fun v hv ↦ by
        obtain rfl := mem_singleton_iff.1 hv
        exact (e.mapOrientation ι _).symm_apply_eq.2 h.symm), hinv]
    exact congrArg (TopPair.singularHomologyMap (fiberThomPairOverMap F E (mem_singleton x))
      (ModuleCat.of R R) n)
      (singularHomologyMap_complZeroPairIso_inv_eq_of_mapOrientation_eq hι hx hx₀
        (ho.trans h.symm) γ)
  · -- `e` reads the orientations of `E_x` oppositely to `e₀`.
    rw [readOver_congr hι (singleton_subset_iff.2 hx₀) (singleton_subset_iff.2 hx)
      (ω := -ω) (fun v hv ↦ by
        obtain rfl := mem_singleton_iff.1 hv
        refine ((e.mapOrientation ι _).symm_apply_eq (y := -o) |>.2 ?_).trans
          ((e₀.mapOrientation ι _).symm_apply_eq (y := -o) |>.2 ?_).symm
        · rw [Trivialization.mapOrientation_neg, h]
          exact (neg_neg ω).symm
        · rw [Trivialization.mapOrientation_neg, ho]), readOver_neg]
    have hneg {M N : ModuleCat.{w} R} (f : M ⟶ N) (y : M) : (-f) y = -(f y) := rfl
    rw [hneg, hinv, readFiberClass, readFiberClass, ← map_neg]
    exact congrArg (TopPair.singularHomologyMap (fiberThomPairOverMap F E (mem_singleton x))
      (ModuleCat.of R R) n)
      (singularHomologyMap_complZeroPairIso_inv_eq_neg_of_mapOrientation_eq_neg hι hx₀ hx
        (h.trans (congrArg Neg.neg ho).symm) γ).symm

/-! ### Fibre classes in the product bundle -/

variable [FiniteDimensional ℝ F]

variable (F) in
/-- The scalar by which a class `γ` of `Hᵣ(F, F ∖ {0}; R)` is the class of the point under
`Hᵣ(F, F ∖ {0}) ≅ Hᵣ(pt × F, pt × (F ∖ {0})) ≅ H₀(pt) ≅ R`. -/
private def fiberScalar
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R)) : R :=
  (TopCat.of PUnit.{w + 1}).singularHomology₀ε (ModuleCat.of R R)
    ((prodThomPairSingularHomologyIso (ModuleCat.of R R) PUnit.{w + 1} F 0 (finrank ℝ F)).hom
      (TopPair.singularHomologyMap (prodThomPairFiberMap F PUnit.unit) (ModuleCat.of R R)
        (finrank ℝ F) γ))

/-- In the product bundle `W × F`, the fibre over `y` of a class `γ` of `Hᵣ(F, F ∖ {0}; R)` is the
class of `y` multiplied by the scalar of `γ`, under `Hᵣ(W × F, W × (F ∖ {0})) ≅ H₀(W)`. -/
private theorem singularHomologyMap_prodThomPairFiberMap_eq {W : Type w} [TopologicalSpace W]
    (y : W) (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R)) :
    TopPair.singularHomologyMap (prodThomPairFiberMap F y) (ModuleCat.of R R) (finrank ℝ F) γ =
      (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).inv
        (fiberScalar F γ • singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) y 1) := by
  -- The fibre over `y` is the fibre over the point, pushed forward along the constant map `y`.
  have hy := prodThomPairFiberMap_comp_prodThomPairMap F PUnit.unit
    (ContinuousMap.const PUnit.{w + 1} y)
  rw [ContinuousMap.const_apply] at hy
  have hz := singularHomology₀_eq_smul_singularHomology₀Section (X := TopCat.of PUnit.{w + 1})
    PUnit.unit ((prodThomPairSingularHomologyIso (ModuleCat.of R R) PUnit.{w + 1} F 0
      (finrank ℝ F)).hom (TopPair.singularHomologyMap (prodThomPairFiberMap F PUnit.unit)
        (ModuleCat.of R R) (finrank ℝ F) γ))
  rw [← hy, TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    ← (prodThomPairSingularHomologyIso (ModuleCat.of R R) PUnit.{w + 1} F 0
      (finrank ℝ F)).hom_inv_id_apply (TopPair.singularHomologyMap
        (prodThomPairFiberMap F PUnit.unit) (ModuleCat.of R R) (finrank ℝ F) γ),
    ← ConcreteCategory.comp_apply,
    prodThomPairSingularHomologyIso_inv_naturality (ModuleCat.of R R) PUnit.{w + 1} F
      (ContinuousMap.const PUnit.{w + 1} y) 0 (finrank ℝ F), ConcreteCategory.comp_apply, hz,
    map_smul]
  exact congrArg _ (congrArg₂ (· • ·) rfl (ConcreteCategory.congr_hom
    (singularHomology₀Section_naturality (ModuleCat.of R R)
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} y)) PUnit.unit) 1))

/-- A generator of `Hᵣ(F, F ∖ {0}; R) ≅ R` has a unit as its scalar. -/
private theorem isUnit_fiberScalar
    {γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R)} (hγ : Submodule.span R {γ} = ⊤) :
    IsUnit (fiberScalar F γ) := by
  -- The class `γ₀` of `Hᵣ(F, F ∖ {0})` corresponding to the class of the point has scalar `1`, and
  -- it is a multiple of `γ`.
  let γ₀ := TopPair.singularHomologyMap (prodThomPairSnd PUnit.{w + 1} F) (ModuleCat.of R R)
    (finrank ℝ F) ((prodThomPairSingularHomologyIso (ModuleCat.of R R) PUnit.{w + 1} F 0
      (finrank ℝ F)).inv (singularHomology₀Section (ModuleCat.of R R)
        (X := TopCat.of PUnit.{w + 1}) PUnit.unit 1))
  have hγ₀ : TopPair.singularHomologyMap (prodThomPairFiberMap F PUnit.unit) (ModuleCat.of R R)
      (finrank ℝ F) γ₀ = (prodThomPairSingularHomologyIso (ModuleCat.of R R) PUnit.{w + 1} F 0
        (finrank ℝ F)).inv (singularHomology₀Section (ModuleCat.of R R)
          (X := TopCat.of PUnit.{w + 1}) PUnit.unit 1) := by
    rw [← ConcreteCategory.comp_apply (TopPair.singularHomologyMap
      (prodThomPairSnd PUnit.{w + 1} F) (ModuleCat.of R R) (finrank ℝ F)),
      ← TopPair.singularHomologyMap_comp, prodThomPairSnd_comp_prodThomPairFiberMap,
      TopPair.singularHomologyMap_id, ConcreteCategory.id_apply]
  have h₀ : fiberScalar F γ₀ = 1 := by
    rw [fiberScalar, hγ₀, Iso.inv_hom_id_apply]
    exact ConcreteCategory.congr_hom (singularHomology₀Section_singularHomology₀ε
      (ModuleCat.of R R) (X := TopCat.of PUnit.{w + 1}) PUnit.unit) (1 : R)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hγ ▸ Submodule.mem_top : γ₀ ∈ _)
  refine IsUnit.of_mul_eq_one_right r ?_
  rw [← h₀, ← hr, fiberScalar, fiberScalar, map_smul, map_smul, map_smul, smul_eq_mul]

omit [VectorBundle ℝ F E] in
/-- Through a trivialization, the fibre class over `x` read by it as `γ` is the class of `x`
multiplied by the scalar of `γ`. -/
private theorem singularHomologyMap_thomPairOverIso_readFiberClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {V : Set B} (hV : V ⊆ e.baseSet) {x : B} (hx : x ∈ V)
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R)) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hV).hom (ModuleCat.of R R) (finrank ℝ F)
        (readFiberClass F E e hx (hV hx) γ) =
      (prodThomPairSingularHomologyIso (ModuleCat.of R R) V F 0 (finrank ℝ F)).inv
        (fiberScalar F γ • singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of V)
          ⟨x, hx⟩ 1) := by
  rw [readFiberClass, ← ConcreteCategory.comp_apply (TopPair.singularHomologyMap
      (fiberThomPairOverMap F E hx) (ModuleCat.of R R) (finrank ℝ F)),
    ← TopPair.singularHomologyMap_comp, e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hV hx,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ x (hV hx)).complZeroPairIso.inv (ModuleCat.of R R)
        (finrank ℝ F)),
    ← TopPair.singularHomologyMap_comp, Iso.inv_hom_id, TopPair.singularHomologyMap_id,
    ConcreteCategory.id_apply]
  exact singularHomologyMap_prodThomPairFiberMap_eq _ γ

variable (ω : Orientation ℝ F ι)
  (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
    (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R))

/-! ### The fibre classes over a subset of the base -/

/-- The twisted class of the fibre pair over `x ∈ W` in `Hᵣ(E|_W, E₀|_W; o)`. -/
private abbrev signFiberClassOver {W : Set B} {x : B} (hx : x ∈ W) :
    ((thomPairOver F E W).twistedHomology (signSystemOver R F E hι W) (finrank ℝ F) :
      ModuleCat.{w} R) :=
  restrictOver hι (singleton_subset_iff.2 hx) (finrank ℝ F) (signFiberClass hι ω γ x)

omit [FiniteDimensional ℝ F] in
/-- Restriction carries twisted fibre classes to twisted fibre classes. -/
private theorem restrictOver_signFiberClassOver {W W' : Set B} (h : W ⊆ W') {x : B}
    (hx : x ∈ W) :
    restrictOver hι h (finrank ℝ F) (signFiberClassOver (E := E) hι ω γ hx) =
      signFiberClassOver (E := E) hι ω γ (h hx) := by
  rw [signFiberClassOver, ← ConcreteCategory.comp_apply, restrictOver_comp_restrictOver]

include hι in
/-- Every trivialization of the atlas reads the twisted fibre class over `x` as the fibre class it
reads as `γ`. -/
private theorem readOver_signFiberClassOver (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {V : Set B} (hV : V ⊆ e.baseSet) {x : B} (hx : x ∈ V) :
    readOver hι e ω hV (finrank ℝ F) (signFiberClassOver (E := E) hι ω γ hx) =
      readFiberClass F E e hx (hV hx) γ := by
  rw [signFiberClassOver, ← ConcreteCategory.comp_apply, restrictOver_readOver,
    ConcreteCategory.comp_apply, readOver_signFiberClass hι e ω γ (hV hx),
    singularHomologyMap_thomPairOverMap_readFiberClass]

include hι in
/-- Twisted fibre classes over points joined inside the base set of a chosen trivialization
agree. -/
private theorem signFiberClassOver_eq_of_joinedIn (c : B) {W : Set B} {x y : B} (hx : x ∈ W)
    (hy : y ∈ W) (h : JoinedIn (W ∩ (trivializationAt F E c).baseSet) x y) :
    signFiberClassOver (E := E) hι ω γ hx = signFiberClassOver (E := E) hι ω γ hy := by
  set e := trivializationAt F E c
  have hV : W ∩ e.baseSet ⊆ e.baseSet := inter_subset_right
  rw [← restrictOver_signFiberClassOver (E := E) hι ω γ inter_subset_left h.source_mem,
    ← restrictOver_signFiberClassOver (E := E) hι ω γ inter_subset_left h.target_mem]
  congr 1
  apply (ModuleCat.mono_iff_injective (readOver hι e ω hV (finrank ℝ F) ≫
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hV).hom (ModuleCat.of R R)
      (finrank ℝ F))).1 inferInstance
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    readOver_signFiberClassOver, readOver_signFiberClassOver,
    singularHomologyMap_thomPairOverIso_readFiberClass,
    singularHomologyMap_thomPairOverIso_readFiberClass,
    singularHomology₀Section_eq_of_joined _ h.joined_subtype]

include hι in
/-- **The twisted fibre classes are constant along paths.** -/
private theorem signFiberClassOver_eq_of_path {W : Set B} {x y : W} (δ : Path x y) :
    signFiberClassOver (E := E) hι ω γ x.property =
      signFiberClassOver (E := E) hι ω γ y.property := by
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  refine δ.eq_of_eventually_eq (f := fun z : W ↦ signFiberClassOver (E := E) hι ω γ z.property)
    fun t ↦ ?_
  have hδ : Continuous fun s ↦ ((δ s : W) : B) := continuous_subtypeVal.comp δ.continuous
  have hc : ((δ t : W) : B) ∈ (trivializationAt F E (δ t : B)).baseSet :=
    mem_baseSet_trivializationAt F E _
  have hO : {s : unitInterval | ((δ s : W) : B) ∈ (trivializationAt F E (δ t : B)).baseSet} ∈
      𝓝 t := (hδ.tendsto t).eventually ((trivializationAt F E (δ t : B)).open_baseSet.mem_nhds hc)
  filter_upwards [pathComponentIn_mem_nhds hO] with s hs
  refine (signFiberClassOver_eq_of_joinedIn hι ω γ (δ t : B) _ _ ?_).symm
  refine (hs.map hδ.continuousOn).mono ?_
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨(δ u).property, hu⟩

/-- The map `H₀(W; R) ⟶ Hᵣ(E|_W, E₀|_W; o)` sending the class of a point to the twisted fibre class
over it. -/
private def signThomPairOverFinrankInv (W : Set B) :
    ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj (TopCat.of W) ⟶
      (thomPairOver F E W).twistedHomology (signSystemOver R F E hι W) (finrank ℝ F) :=
  singularHomology₀Desc (ModuleCat.of R R) (X := TopCat.of W)
    (fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R _
      (signFiberClassOver (E := E) hι ω γ x.property)))
    fun _ _ δ ↦ by rw [signFiberClassOver_eq_of_path hι ω γ δ]

@[reassoc]
private theorem singularHomology₀Section_signThomPairOverFinrankInv {W : Set B} (x : W) :
    singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W) x ≫
        signThomPairOverFinrankInv (E := E) hι ω γ W =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _
        (signFiberClassOver (E := E) hι ω γ x.property)) := by
  rw [signThomPairOverFinrankInv]
  exact singularHomology₀Section_singularHomology₀Desc (X := TopCat.of W) _ _ _ x

/-- The maps over `W ⊆ W'` commute with the restrictions. -/
private theorem signThomPairOverFinrankInv_naturality {W W' : Set B} (h : W ⊆ W') :
    ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) ≫ signThomPairOverFinrankInv (E := E) hι ω γ W' =
      signThomPairOverFinrankInv hι ω γ W ≫ restrictOver hι h (finrank ℝ F) := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_naturality_assoc,
    singularHomology₀Section_signThomPairOverFinrankInv,
    singularHomology₀Section_signThomPairOverFinrankInv_assoc,
    ModuleCat.ofHom_toSpanSingleton_comp, restrictOver_signFiberClassOver]
  rfl

include hι in
/-- Over a subset of the base set of a chosen trivialization, the map is an isomorphism: read
through the trivialization it is the isomorphism `H₀(W) ≅ Hᵣ(W × F, W × (F ∖ {0}))` of the product
bundle after multiplying by the unit scalar of the generator `γ`. -/
private theorem isIso_signThomPairOverFinrankInv_of_subset (hγ : Submodule.span R {γ} = ⊤)
    (c : B) {W : Set B} (hW : W ⊆ (trivializationAt F E c).baseSet) :
    IsIso (signThomPairOverFinrankInv (E := E) hι ω γ W) := by
  set e := trivializationAt F E c
  have hu := isUnit_fiberScalar hγ
  have h : signThomPairOverFinrankInv (E := E) hι ω γ W ≫ readOver hι e ω hW (finrank ℝ F) ≫
      TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of R R) (finrank ℝ F) =
      singularHomology₀UnitsSmul (ModuleCat.of R R) (X := TopCat.of W) (fun _ ↦ hu.unit)
          (fun _ _ _ ↦ rfl) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).inv := by
    refine singularHomology₀_hom_ext _ fun x ↦ ?_
    rw [singularHomology₀Section_signThomPairOverFinrankInv_assoc,
      singularHomology₀Section_singularHomology₀UnitsSmul_assoc, Linear.smul_comp]
    ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_smul, LinearMap.smul_apply,
      IsUnit.unit_spec]
    rw [readOver_signFiberClassOver, singularHomologyMap_thomPairOverIso_readFiberClass, map_smul]
  have : IsIso (signThomPairOverFinrankInv (E := E) hι ω γ W ≫ readOver hι e ω hW (finrank ℝ F) ≫
      TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of R R)
        (finrank ℝ F)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (readOver hι e ω hW (finrank ℝ F) ≫
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of R R) (finrank ℝ F))

/-! ### The Mayer–Vietoris step -/

/-- Pairs of subsets of the total space with the same sets have isomorphic twisted homology. -/
private def subsetPairIso {A₁ C₁ A₂ C₂ : Set (TopCat.of (TotalSpace F E))} (hC₁ : C₁ ⊆ A₁)
    (hC₂ : C₂ ⊆ A₂) (hA : A₁ ⊆ A₂) (hA' : A₂ ⊆ A₁) (hC : C₁ ⊆ C₂) (hC' : C₂ ⊆ C₁) (n : ℕ) :
    (TopPair.ofInclusion hC₁).twistedHomology
        ((LocalCoefficientSystem.pullback (X := TopCat.of ↥A₁) (ContinuousMap.subtypeVal A₁)).obj
          ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))) n ≅
      (TopPair.ofInclusion hC₂).twistedHomology
        ((LocalCoefficientSystem.pullback (X := TopCat.of ↥A₂) (ContinuousMap.subtypeVal A₂)).obj
          ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))) n where
  hom := HomologicalComplex.homologyMap
    (LocalCoefficientSystem.subsetPairTwistedChainComplexMap _ hC₁ hC₂ hA hC) n
  inv := HomologicalComplex.homologyMap
    (LocalCoefficientSystem.subsetPairTwistedChainComplexMap _ hC₂ hC₁ hA' hC') n
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp,
      LocalCoefficientSystem.subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap,
      LocalCoefficientSystem.subsetPairTwistedChainComplexMap_self,
      HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp,
      LocalCoefficientSystem.subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap,
      LocalCoefficientSystem.subsetPairTwistedChainComplexMap_self,
      HomologicalComplex.homologyMap_id]

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [FiniteDimensional ℝ F] [VectorBundle ℝ F E] in
/-- In the union of the nonzero vectors over `V` and over `V'`, those over an open set `U` form an
open subset. -/
private theorem isOpen_coe_preimage_inter_zeroSectionCompl {U : Set B} (hU : IsOpen U)
    (V V' : Set B) :
    IsOpen ((↑) ⁻¹' (π F E ⁻¹' U ∩ zeroSectionCompl F E) :
      Set ↥((π F E ⁻¹' V ∩ zeroSectionCompl F E) ∪ (π F E ⁻¹' V' ∩ zeroSectionCompl F E))) := by
  convert (hU.preimage (FiberBundle.continuous_proj F E)).preimage (continuous_subtypeVal
    (p := (· ∈ (π F E ⁻¹' V ∩ zeroSectionCompl F E) ∪ (π F E ⁻¹' V' ∩ zeroSectionCompl F E))))
    using 1
  ext ⟨p, hp | hp⟩ <;> exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hp.2⟩⟩

variable (R E) in
/-- The Mayer–Vietoris sequence
`Hᵣ(E|_{U ∩ V}, E₀|_{U ∩ V}) ⟶ Hᵣ(E|_U, E₀|_U) ⊞ Hᵣ(E|_V, E₀|_V) ⟶ Hᵣ(E|_{U ∪ V}, E₀|_{U ∪ V})`
with coefficients in the orientation system, in the rank degree. -/
private abbrev signMayerVietoris (U V : Set B) : ShortComplex (ModuleCat.{w} R) :=
  ShortComplex.mk
    (biprod.lift (restrictOver (R := R) (E := E) hι (inter_subset_left : U ∩ V ⊆ U) (finrank ℝ F))
      (-restrictOver (R := R) (E := E) hι (inter_subset_right : U ∩ V ⊆ V) (finrank ℝ F)))
    (biprod.desc (restrictOver (R := R) (E := E) hι (subset_union_left : U ⊆ U ∪ V) (finrank ℝ F))
      (restrictOver (R := R) (E := E) hι (subset_union_right : V ⊆ U ∪ V) (finrank ℝ F)))
    (by simp [restrictOver_comp_restrictOver])

open LocalCoefficientSystem in
/-- The Mayer–Vietoris sequence of the Thom pairs over `U` and `V` is that of the two pairs of
subsets of the total space: the intersection and the union of the pairs are the pairs over `U ∩ V`
and over `U ∪ V`. -/
private def signMayerVietorisIso (U V : Set B) :
    signMayerVietoris R E hι U V ≅ ShortComplex.mk _ _ (pairTwistedMayerVietorisToBiprod_fromBiprod
      ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
      (inter_subset_left : (π F E ⁻¹' U ∩ zeroSectionCompl F E : Set (TopCat.of (TotalSpace F E)))
        ⊆ π F E ⁻¹' U)
      (inter_subset_left : (π F E ⁻¹' V ∩ zeroSectionCompl F E : Set (TopCat.of (TotalSpace F E)))
        ⊆ π F E ⁻¹' V) (finrank ℝ F)) := by
  refine ShortComplex.isoMk (subsetPairIso (R := R) hι
      (inter_subset_left : π F E ⁻¹' (U ∩ V) ∩ zeroSectionCompl F E ⊆ _)
      (inter_subset_inter inter_subset_left inter_subset_left) subset_rfl subset_rfl
      (fun _ hp ↦ ⟨⟨hp.1.1, hp.2⟩, hp.1.2, hp.2⟩) (fun _ hp ↦ ⟨⟨hp.1.1, hp.2.1⟩, hp.1.2⟩) _)
    (Iso.refl _) (subsetPairIso (R := R) hι
      (inter_subset_left : π F E ⁻¹' (U ∪ V) ∩ zeroSectionCompl F E ⊆ _)
      (union_subset_union inter_subset_left inter_subset_left) subset_rfl subset_rfl
      (fun _ hp ↦ hp.1.elim (fun h ↦ .inl ⟨h, hp.2⟩) fun h ↦ .inr ⟨h, hp.2⟩)
      (fun _ hp ↦ hp.elim (fun h ↦ ⟨.inl h.1, h.2⟩) fun h ↦ ⟨.inr h.1, h.2⟩) _) ?_ ?_
  -- Every component is a composite of maps induced by inclusions of pairs of subsets.
  · refine biprod.hom_ext _ _ ?_ ?_
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (pairTwistedMayerVietorisToBiprod_fst _ _ _ _)).trans
        ((HomologicalComplex.homologyMap_comp _ _ _).symm.trans ((congrArg
          (HomologicalComplex.homologyMap · _)
          (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap
            _ _ _ _ _ _ _ _)).trans ?_)))
      exact (congrArg (· ≫ biprod.fst) (Category.comp_id _)).trans (biprod.lift_fst _ _) |>.symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (pairTwistedMayerVietorisToBiprod_snd _ _ _ _)).trans
        ((Preadditive.comp_neg _ _).trans ?_))
      refine Eq.trans ?_ ((congrArg (· ≫ biprod.snd) (Category.comp_id _)).trans
        (biprod.lift_snd _ _)).symm
      exact congrArg Neg.neg ((HomologicalComplex.homologyMap_comp _ _ _).symm.trans (congrArg
        (HomologicalComplex.homologyMap · _)
        (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap
          _ _ _ _ _ _ _ _)))
  · refine biprod.hom_ext' _ _ ?_ ?_
    · refine (congrArg (biprod.inl ≫ ·) (Category.id_comp _)).trans
        ((inl_pairTwistedMayerVietorisFromBiprod _ _ _ _).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ _) (biprod.inl_desc _ _)).symm
      exact (congrArg (HomologicalComplex.homologyMap · _)
        (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap
          _ _ _ _ _ _ _ _)).symm.trans (HomologicalComplex.homologyMap_comp _ _ _)
    · refine (congrArg (biprod.inr ≫ ·) (Category.id_comp _)).trans
        ((inr_pairTwistedMayerVietorisFromBiprod _ _ _ _).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ _) (biprod.inr_desc _ _)).symm
      exact (congrArg (HomologicalComplex.homologyMap · _)
        (subsetPairTwistedChainComplexMap_comp_subsetPairTwistedChainComplexMap
          _ _ _ _ _ _ _ _)).symm.trans (HomologicalComplex.homologyMap_comp _ _ _)

omit [FiniteDimensional ℝ F] in
/-- The Mayer–Vietoris sequence over two open sets is exact. -/
private theorem signMayerVietoris_exact {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) :
    (signMayerVietoris R E hι U V).Exact :=
  (ShortComplex.exact_iff_of_iso (signMayerVietorisIso hι U V)).2
    (LocalCoefficientSystem.pairTwistedMayerVietoris_exact₂ _ _ _
      ((hU.preimage (FiberBundle.continuous_proj F E)).preimage continuous_subtypeVal)
      ((hV.preimage (FiberBundle.continuous_proj F E)).preimage continuous_subtypeVal)
      (isOpen_coe_preimage_inter_zeroSectionCompl (F := F) (E := E) hU U V)
      (isOpen_coe_preimage_inter_zeroSectionCompl (F := F) (E := E) hV U V) _)

omit [FiniteDimensional ℝ F] in
/-- The last map of the Mayer–Vietoris sequence over two open sets is surjective when the twisted
homology over their intersection vanishes in degree `r - 1`. -/
private theorem epi_signMayerVietoris_g {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).twistedHomology (signSystemOver R F E hι (U ∩ V)) m)) :
    Epi (signMayerVietoris R E hι U V).g := by
  have hA := (hU.preimage (FiberBundle.continuous_proj F E)).preimage
    (continuous_subtypeVal (p := (· ∈ π F E ⁻¹' U ∪ π F E ⁻¹' V)))
  have hB := (hV.preimage (FiberBundle.continuous_proj F E)).preimage
    (continuous_subtypeVal (p := (· ∈ π F E ⁻¹' U ∪ π F E ⁻¹' V)))
  have hC := isOpen_coe_preimage_inter_zeroSectionCompl (F := F) (E := E) hU U V
  have hD := isOpen_coe_preimage_inter_zeroSectionCompl (F := F) (E := E) hV U V
  -- The last map of the sequence of pairs of subsets is surjective, by the exactness at the union.
  have h : Epi (ShortComplex.mk _ _
      (LocalCoefficientSystem.pairTwistedMayerVietorisToBiprod_fromBiprod
      ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
      (inter_subset_left : (π F E ⁻¹' U ∩ zeroSectionCompl F E : Set (TopCat.of (TotalSpace F E)))
        ⊆ π F E ⁻¹' U)
      (inter_subset_left : (π F E ⁻¹' V ∩ zeroSectionCompl F E : Set (TopCat.of (TotalSpace F E)))
        ⊆ π F E ⁻¹' V) (finrank ℝ F))).g := by
    obtain h | ⟨m, hm⟩ : finrank ℝ F = 0 ∨ ∃ m, finrank ℝ F = m + 1 := by
      cases finrank ℝ F <;> simp
    · change Epi (LocalCoefficientSystem.pairTwistedMayerVietorisFromBiprod _ _ _ _)
      rw [h]
      exact LocalCoefficientSystem.epi_pairTwistedMayerVietorisFromBiprod_zero _ _ _ hA hB hC hD
    · change Epi (LocalCoefficientSystem.pairTwistedMayerVietorisFromBiprod _ _ _ _)
      rw [hm]
      refine (LocalCoefficientSystem.pairTwistedMayerVietoris_exact₃ _ _ _ hA hB hC hD (m + 1)
        m).epi_f (((hUV m hm.symm).of_iso ?_).eq_of_tgt _ _)
      exact (subsetPairIso (R := R) hι
        (inter_subset_left : π F E ⁻¹' (U ∩ V) ∩ zeroSectionCompl F E ⊆ _)
        (inter_subset_inter inter_subset_left inter_subset_left) subset_rfl subset_rfl
        (fun _ hp ↦ ⟨⟨hp.1.1, hp.2⟩, hp.1.2, hp.2⟩) (fun _ hp ↦ ⟨⟨hp.1.1, hp.2.1⟩, hp.1.2⟩) _).symm
  -- The two sequences are identified.
  have : Epi ((signMayerVietoris R E hι U V).g ≫ (signMayerVietorisIso hι U V).hom.τ₃) := by
    rw [← (signMayerVietorisIso hι U V).hom.comm₂₃]
    infer_instance
  have he : (signMayerVietoris R E hι U V).g =
      ((signMayerVietoris R E hι U V).g ≫ (signMayerVietorisIso hι U V).hom.τ₃) ≫
        inv (signMayerVietorisIso hι U V).hom.τ₃ := by
    simp
  rw [he]
  infer_instance

/-- With the map over `W'` an isomorphism, the restriction from `W ⊆ W'` read through the maps
over `W` and `W'` is the map induced by the inclusion. -/
@[reassoc]
private theorem signThomPairOverFinrankInv_comp_restrictOver_comp_inv {W W' : Set B}
    (h : W ⊆ W') [IsIso (signThomPairOverFinrankInv (E := E) hι ω γ W')] :
    signThomPairOverFinrankInv (E := E) hι ω γ W ≫ restrictOver hι h (finrank ℝ F) ≫
        inv (signThomPairOverFinrankInv (E := E) hι ω γ W') =
      ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← Category.assoc, ← signThomPairOverFinrankInv_naturality, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- On a point of `W ⊆ W'`, a candidate inverse `Φ` of the map over `W'` which on the classes over
`W` is the inverse of the map over `W` followed by the inclusion inverts the map over `W'`. -/
private theorem singularHomology₀Section_signThomPairOverFinrankInv_comp_of_comp_eq
    {W W' : Set B} (h : W ⊆ W') [IsIso (signThomPairOverFinrankInv (E := E) hι ω γ W)]
    {Φ : (thomPairOver F E W').twistedHomology (signSystemOver R F E hι W') (finrank ℝ F) ⟶
      ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj (TopCat.of W')}
    (hΦ : restrictOver hι h (finrank ℝ F) ≫ Φ =
      inv (signThomPairOverFinrankInv (E := E) hι ω γ W) ≫
        ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
          (TopCat.ofHom (ContinuousMap.inclusion h))) (x : W) :
    singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W')
          (TopCat.ofHom (ContinuousMap.inclusion h) x) ≫
        signThomPairOverFinrankInv (E := E) hι ω γ W' ≫ Φ =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of W')
        (TopCat.ofHom (ContinuousMap.inclusion h) x) := by
  rw [← singularHomology₀Section_naturality, Category.assoc,
    reassoc_of% (signThomPairOverFinrankInv_naturality hι ω γ h), hΦ, IsIso.hom_inv_id_assoc]

include hι in
/-- **The Mayer–Vietoris step**: if the maps over the open sets `U` and `V` are isomorphisms, the
map over `U ∩ V` is surjective and the twisted homology of the Thom pair over `U ∩ V` vanishes in
degree `r - 1`, the map over `U ∪ V` is an isomorphism. -/
private theorem isIso_signThomPairOverFinrankInv_union {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) [IsIso (signThomPairOverFinrankInv (E := E) hι ω γ U)]
    [IsIso (signThomPairOverFinrankInv (E := E) hι ω γ V)]
    [Epi (signThomPairOverFinrankInv (E := E) hι ω γ (U ∩ V))]
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).twistedHomology (signSystemOver R F E hι (U ∩ V)) m)) :
    IsIso (signThomPairOverFinrankInv (E := E) hι ω γ (U ∪ V)) := by
  let ψ := signThomPairOverFinrankInv (E := E) hι ω γ
  let H₀ := (singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)
  let S := signMayerVietoris R E hι U V
  have hS : S.Exact := signMayerVietoris_exact hι hU hV
  have : Epi S.g := epi_signMayerVietoris_g hι hU hV hUV
  -- The inverse map, on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ H₀.obj (TopCat.of ↥(U ∪ V)) :=
    biprod.desc (inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)))
      (inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)))
  -- It vanishes on the image of the first map, since both restrictions of a class over `U ∩ V`
  -- give the same class over `U ∪ V`.
  have hφ : S.f ≫ φ = 0 := by
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [S, signMayerVietoris, φ, ψ, H₀, biprod.lift_desc, Preadditive.neg_comp,
      Preadditive.comp_add, Preadditive.comp_neg,
      signThomPairOverFinrankInv_comp_restrictOver_comp_inv_assoc, ← Functor.map_comp,
      ← TopCat.ofHom_comp, ContinuousMap.inclusion_comp_inclusion, add_neg_eq_zero]
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  -- On the classes over `U` and over `V`, `Φ` is the inverse of the map over `U` or `V`.
  have hΦU : restrictOver hι subset_union_left (finrank ℝ F) ≫ Φ =
      inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Φ) (biprod.inl_desc _ _).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (biprod.inl ≫ ·) hgΦ).trans
        (biprod.inl_desc _ _))))
  have hΦV : restrictOver hι subset_union_right (finrank ℝ F) ≫ Φ =
      inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Φ) (biprod.inr_desc _ _).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (biprod.inr ≫ ·) hgΦ).trans
        (biprod.inr_desc _ _))))
  refine ⟨Φ, singularHomology₀_hom_ext _ fun x ↦ ?_,
    (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)⟩
  · -- A point of `U ∪ V` lies in `U` or in `V`, where the composite is computed.
    rw [Category.comp_id]
    obtain ⟨x, hx | hx⟩ := x
    · exact singularHomology₀Section_signThomPairOverFinrankInv_comp_of_comp_eq hι ω γ _ hΦU
        ⟨x, hx⟩
    · exact singularHomology₀Section_signThomPairOverFinrankInv_comp_of_comp_eq hι ω γ _ hΦV
        ⟨x, hx⟩
  -- The second map of the Mayer–Vietoris sequence is an epimorphism.
  · have e₁ : biprod.inl ≫ S.g = restrictOver hι subset_union_left (finrank ℝ F) :=
      biprod.inl_desc _ _
    rw [Category.comp_id, reassoc_of% e₁, reassoc_of% hΦU, signThomPairOverFinrankInv_naturality,
      IsIso.inv_hom_id_assoc, e₁]
  · have e₁ : biprod.inr ≫ S.g = restrictOver hι subset_union_right (finrank ℝ F) :=
      biprod.inr_desc _ _
    rw [Category.comp_id, reassoc_of% e₁, reassoc_of% hΦV, signThomPairOverFinrankInv_naturality,
      IsIso.inv_hom_id_assoc, e₁]

/-- Over the empty set both sides vanish. -/
private theorem isIso_signThomPairOverFinrankInv_empty :
    IsIso (signThomPairOverFinrankInv (E := E) hι ω γ ∅) := by
  have : IsEmpty (thomPairOver F E (∅ : Set B)).fst := ⟨fun x ↦ x.property⟩
  have : IsEmpty (thomPairOver F E (∅ : Set B)).snd := ⟨fun x ↦ x.property.1⟩
  have hz := TopPair.isZero_twistedHomology_of_isIso (thomPairOver F E (∅ : Set B))
    (signSystemOver R F E hι ∅) (fun k ↦ isIso_of_source_target_iso_zero _
      (LocalCoefficientSystem.isZero_twistedHomology_of_isEmpty _ k).isoZero
      (LocalCoefficientSystem.isZero_twistedHomology_of_isEmpty _ k).isoZero) (finrank ℝ F)
  have : IsEmpty (TopCat.of (∅ : Set B)) := ⟨fun x ↦ x.property⟩
  exact isIso_of_source_target_iso_zero _
    (isZero_singularHomology_of_isEmpty _ _ _).isoZero hz.isoZero

include hι in
/-- **Finite unions of trivializing open sets**: the map is an isomorphism over a finite union of
open sets each lying in the base set of a chosen trivialization. -/
private theorem isIso_signThomPairOverFinrankInv_biUnion (hγ : Submodule.span R {γ} = ⊤)
    {κ : Type*} (s : Finset κ) {W : κ → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ c, W i ⊆ (trivializationAt F E c).baseSet) :
    IsIso (signThomPairOverFinrankInv (E := E) hι ω γ (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset κ), W i) = ∅ by simp]
    exact isIso_signThomPairOverFinrankInv_empty hι ω γ
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨c, hc⟩ := hWe a (Finset.mem_insert_self a s)
    have : IsIso (signThomPairOverFinrankInv (E := E) hι ω γ (W a)) :=
      isIso_signThomPairOverFinrankInv_of_subset hι ω γ hγ c hc
    have : IsIso (signThomPairOverFinrankInv (E := E) hι ω γ (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    have : IsIso (signThomPairOverFinrankInv (E := E) hι ω γ (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
        (hWo i (Finset.mem_insert_of_mem hi))) fun i hi ↦ ?_
      obtain ⟨c', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
      exact ⟨c', inter_subset_right.trans hi'⟩
    refine isIso_signThomPairOverFinrankInv_union hι ω γ
      (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      fun m hm ↦ ?_
    -- Below the rank the twisted homology over a trivializing set is the ordinary one, which
    -- vanishes.
    have hV : W a ∩ ⋃ i ∈ s, W i ⊆ (trivializationAt F E c).baseSet := inter_subset_left.trans hc
    exact ((trivializationAt F E c).isZero_singularHomology_thomPairOver hV
      (ModuleCat.of R R) (by omega)).of_iso (asIso (readOver hι (trivializationAt F E c) ω hV m))

/-! ### The whole base -/

variable (F E) in
/-- The inclusion of the Thom pair over the whole base into the Thom pair. -/
private abbrev univPairMap : thomPairOver F E (univ : Set B) ⟶ thomPair F E :=
  TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E)
    univ

/-- The coefficients over the whole base are those pulled back from the Thom pair. -/
private def univCoeffIso : signSystemOver R F E hι (univ : Set B) ≅
    (LocalCoefficientSystem.pullback (TopPair.Hom.fst (univPairMap F E)).hom).obj
      ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι)) :=
  eqToIso (by rw [TopCat.restrictPreimagePairMap_fst]; rfl)

/-- The Thom pair over the whole base has the twisted homology of the Thom pair. -/
private instance isIso_twistedHomologyMap_univPairMap (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap (univPairMap F E)
      ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι)) n) := by
  refine TopPair.isIso_twistedHomologyMap_of_open_cover (univPairMap F E) _ ?_ ?_
    (fun _ : Unit ↦ univ) (fun _ ↦ isOpen_univ) (iUnion_const univ) (fun _ ↦ .inr ?_) n
  · rw [TopCat.restrictPreimagePairMap_fst]
    exact Topology.IsEmbedding.subtypeVal
  · rintro ⟨x, hx⟩ hx'
    rw [TopPair.range_ofSubset_map, TopCat.restrictPreimagePairMap_fst_apply] at hx'
    rw [TopPair.range_ofInclusion_map]
    exact ⟨trivial, hx'⟩
  · rintro x -
    exact ⟨⟨x, trivial⟩, TopCat.restrictPreimagePairMap_fst_apply _ _ _ _⟩

variable [CompactSpace B]

include hι in
/-- Over a compact base, the map over the whole base is an isomorphism. -/
private theorem isIso_signThomPairOverFinrankInv_univ (hγ : Submodule.span R {γ} = ⊤) :
    IsIso (signThomPairOverFinrankInv (E := E) hι ω γ univ) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  have h := isIso_signThomPairOverFinrankInv_biUnion hι ω γ hγ t
    (fun b _ ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦ ⟨b, subset_rfl⟩
  rwa [univ_subset_iff.1 ht] at h

/-- The map `H₀(B; R) ⟶ Hᵣ(E, E₀; π^*o(E))` sending the class of a point to the twisted fibre class
over it. -/
private def signThomPairFinrankInv :
    ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj (TopCat.of B) ⟶
      (thomPair F E).twistedHomology ((LocalCoefficientSystem.pullback
        (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TopCat.of (TotalSpace F E), TopCat.of B))).obj
          (signLocalSystem F E R hι)) (finrank ℝ F) :=
  ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom ≫
    signThomPairOverFinrankInv (E := E) hι ω γ univ ≫
    (thomPairOver F E univ).twistedHomologyCoefficientMap (univCoeffIso (R := R) hι).hom
      (finrank ℝ F) ≫
    TopPair.twistedHomologyMap (univPairMap F E)
      ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι)) (finrank ℝ F)

include hι in
private theorem isIso_signThomPairFinrankInv (hγ : Submodule.span R {γ} = ⊤) :
    IsIso (signThomPairFinrankInv (E := E) hι ω γ) := by
  have := isIso_signThomPairOverFinrankInv_univ (E := E) hι ω γ hγ
  unfold signThomPairFinrankInv
  infer_instance

end ThomPairOver

/-! ### The Thom pair in the rank degree -/

section ThomPair

variable [FiniteDimensional ℝ F] (ω : Orientation ℝ F ι)
  (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
    (ModuleCat.of R R) (finrank ℝ F) : ModuleCat.{w} R))

variable (E) in
/-- The **twisted fibre class** over `b` in `Hᵣ(E, E₀; π^*o(E))`, for `r` the rank: the class of the
fibre pair `(E_b, E_b ∖ {0})` with coefficients in the orientation system. It is normalized by an
orientation `ω` of the model fibre `F` and a class `γ` of `Hᵣ(F, F ∖ {0}; R)`, through the
trivialization chosen at `b`: it identifies the coefficients over the fibre with `R` by evaluation
at the orientation of `E_b` which it reads as `ω`, and the twisted fibre class is the class it then
reads as the fibre class which it reads as `γ`. Every trivialization of the atlas at `b` reads the
class in the same way: one reading the orientations of `E_b` oppositely changes the sign of both
the identification of the coefficients and the fibre class. -/
def thomPairTwistedFiberClass (b : B) :
    ((thomPair F E).twistedHomology ((LocalCoefficientSystem.pullback
      (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TopCat.of (TotalSpace F E), TopCat.of B))).obj
        (signLocalSystem F E R hι)) (finrank ℝ F) : ModuleCat.{w} R) :=
  TopPair.twistedHomologyMap (univPairMap F E)
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι)) (finrank ℝ F)
    ((thomPairOver F E univ).twistedHomologyCoefficientMap (univCoeffIso (R := R) hι).hom
      (finrank ℝ F) (signFiberClassOver (E := E) hι ω γ (mem_univ b)))

variable [CompactSpace B]

/-- **The Thom pair in the rank degree with coefficients in the orientation system**: for a real
vector bundle `E → B` of rank `r` over a compact base, with Thom pair `(E, E₀)` and orientation
local system `o(E)` pulled back to the total space, and any commutative ring `R`,
`Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`. It is normalized by an orientation `ω` of the model fibre and a
generator `γ` of `Hᵣ(F, F ∖ {0}; R) ≅ R`, and sends the twisted fibre class over `b`
(`TauCeti.thomPairTwistedFiberClass`) to the class of `b`
(`TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairTwistedFiberClass`). No orientation of
`E` is needed: the twist by `o(E)` cancels the sign by which a change of trivialization acts on the
fibre classes. -/
def thomPairTwistedHomologyFinrankIso (hγ : Submodule.span R {γ} = ⊤) :
    (thomPair F E).twistedHomology ((LocalCoefficientSystem.pullback
        (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TopCat.of (TotalSpace F E), TopCat.of B))).obj
          (signLocalSystem F E R hι)) (finrank ℝ F) ≅
      ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj (TopCat.of B) :=
  have := isIso_signThomPairFinrankInv (E := E) hι ω γ hγ
  (asIso (signThomPairFinrankInv (E := E) hι ω γ)).symm

/-- The isomorphism `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` sends the twisted fibre class over `b` to the
class of `b`. -/
theorem thomPairTwistedHomologyFinrankIso_hom_thomPairTwistedFiberClass
    (hγ : Submodule.span R {γ} = ⊤) (b : B) :
    (thomPairTwistedHomologyFinrankIso hι ω γ hγ).hom (thomPairTwistedFiberClass E hι ω γ b) =
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1 := by
  have := isIso_signThomPairFinrankInv (E := E) hι ω γ hγ
  have h : signThomPairFinrankInv (E := E) hι ω γ
      (singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of B) b 1) =
      thomPairTwistedFiberClass E hι ω γ b := by
    have hsec := ConcreteCategory.congr_hom (singularHomology₀Section_naturality
      (ModuleCat.of R R) (X := TopCat.of B) (Y := TopCat.of (univ : Set B))
      (TopCat.isoOfHomeo (Homeomorph.Set.univ B).symm).hom b) (1 : R)
    have hΨ := ConcreteCategory.congr_hom (singularHomology₀Section_signThomPairOverFinrankInv
      (E := E) hι ω γ (⟨b, mem_univ b⟩ : (univ : Set B))) (1 : R)
    rw [ConcreteCategory.comp_apply] at hsec hΨ
    rw [signThomPairFinrankInv, ConcreteCategory.comp_apply, hsec]
    simp only [ConcreteCategory.comp_apply]
    erw [hΨ]
    simp [thomPairTwistedFiberClass]
  rw [← h, thomPairTwistedHomologyFinrankIso, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

end ThomPair

end TauCeti
