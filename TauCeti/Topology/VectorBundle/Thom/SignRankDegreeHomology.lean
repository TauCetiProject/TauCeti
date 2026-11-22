/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Twisted.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.MayerVietoris.Pair
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Orientation.TwistedHomology.OverTrivialization
public import TauCeti.Topology.VectorBundle.Thom.Class
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.Twisted.Equivalence
import TauCeti.AlgebraicTopology.Singular.FiniteUnionInduction
import TauCeti.Topology.Category.TopCat.Limits.Basic
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
coefficients the existing identifications of the same group with `H₀(B; R)` need an orientation of
`E`, or that `1` is the only unit of `R`
(`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`,
`TauCeti.thomPairSingularHomologyFinrankIso`): the twist by `o(E)` is what makes the fibre classes
independent of a choice of orientation. With a universal coefficient theorem for local coefficients
and the self-duality of `o(E)`, this computation yields the Thom class of `E` with coefficients in
its orientation system.

## The local trivializations of the orientation system

Over the base set of a linear trivialization `e` of the atlas, the orientations of the fibres which
`e` reads as a fixed orientation `ω` of the model fibre `F` form a continuous section of the
orientation double cover. Evaluating at them trivializes `o(E)` pulled back along any map into the
base set (`TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIso`), and so identifies
homology with coefficients in it with ordinary homology
(`TauCeti.VectorBundleOrientationCover.twistedHomologyPullbackSignLocalSystemIso`), naturally in
maps of pairs. Two trivializations reading the orientations alike give the same identification, and
reversing `ω` negates it. These identifications are in
`TauCeti.Topology.VectorBundle.Orientation.LocalSystem` and
`TauCeti.Topology.VectorBundle.Orientation.TwistedHomology.OverTrivialization`.

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
trivializing open sets, by induction on their number, and so over a compact base
(`TauCeti.isIso_univ_of_subsetMayerVietoris`).

## Main definitions

* `TauCeti.thomPairTwistedFiberClass`: the twisted fibre class over a point.
* `TauCeti.thomPairTwistedHomologyFinrankIso`: `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` over a compact base.

## Main results

* `TauCeti.thomPairTwistedHomologyFinrankIso_hom_thomPairTwistedFiberClass`: the isomorphism sends
  the twisted fibre class over `b` to the class of `b`.
* `TauCeti.thomPairTwistedFiberClass_eq`: every trivialization of the atlas at `b` exhibits the
  twisted fibre class over `b` as the image under the fibre inclusion of the class which it reads
  as the fibre class which it reads as `γ`.
* `TauCeti.thomPairTwistedFiberClass_neg`: reversing the orientation of the model fibre negates the
  twisted fibre classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over unions of
  trivializing open sets), and §12 (the orientation double cover and twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients), and Section 4.D, Theorem 4D.10
  and its proof (the untwisted Thom isomorphism, whose proof this one adapts to coefficients in the
  orientation system).
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
  LocalCoefficientSystem.subsetPairTwistedHomologyMap
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
    inter_subset_left inter_subset_left (preimage_mono h)
    (inter_subset_inter_left _ (preimage_mono h)) n

/-- The restrictions compose. -/
private theorem restrictOver_comp_restrictOver {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W'')
    (n : ℕ) :
    restrictOver (R := R) (F := F) (E := E) hι h n ≫ restrictOver hι h' n =
      restrictOver hι (h.trans h') n :=
  LocalCoefficientSystem.subsetPairTwistedHomologyMap_comp_subsetPairTwistedHomologyMap
    _ _ _ _ _ _ _ _ n

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
  -- The Thom pair over `W` is only definitionally the pair of subsets of the total space on which
  -- the chain-level lemmas are stated, so `rw` cannot match them and each step is applied by
  -- unification.
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
  unfold readOver
  rw [twistedHomologyPullbackSignLocalSystemIso_congr hι _ ((projMap F E).comp (inclOver F E V))
    (fun v ↦ hV v.property) (fun v ↦ hV' v.property) fun v ↦ h _ v.property]

/-- Reading through the opposite orientation of the model fibre is the negative. -/
private theorem readOver_neg (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (ω : Orientation ℝ F ι) {V : Set B} (hV : V ⊆ e.baseSet) (n : ℕ) :
    readOver (R := R) hι e (-ω) hV n = -readOver hι e ω hV n := by
  unfold readOver
  rw [twistedHomologyPullbackSignLocalSystemIso_neg_hom, Preadditive.comp_neg]

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
    -- The objects of the fundamental groupoid of the Thom pair over `V` are only definitionally
    -- points of the subset of the total space over which the coefficients are pulled back, so
    -- `NatTrans.comp_app` matches only up to that unfolding.
    erw [NatTrans.comp_app, NatTrans.comp_app]
    simp only [restrictCoeff, LocalCoefficientSystem.pullback_map_app,
      LocalCoefficientSystem.pullbackCompIso_hom_app_app,
      LocalCoefficientSystem.pullbackCompIso_inv_app_app]
    -- Every component is an identity.
    exact rfl
  exact congrArg (fun Z ↦ (thomPairOver F E V).twistedHomologyCoefficientMap Z n ≫ _) hc

/-! ### Fibre classes -/

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
      (ModuleCat.of R R) n) (ConcreteCategory.congr_hom
        (e.singularHomologyMap_complZeroPairIso_inv_eq_of_mapOrientation_eq e₀ hx hx₀ hι
          (ModuleCat.of R R) (ho.trans h.symm) n) γ)
  · -- `e` reads the orientations of `E_x` oppositely to `e₀`.
    rw [readOver_congr hι (singleton_subset_iff.2 hx₀) (singleton_subset_iff.2 hx)
      (ω := -ω) (fun v hv ↦ by
        obtain rfl := mem_singleton_iff.1 hv
        refine ((e.mapOrientation ι _).symm_apply_eq (y := -o) |>.2 ?_).trans
          ((e₀.mapOrientation ι _).symm_apply_eq (y := -o) |>.2 ?_).symm
        · rw [Trivialization.mapOrientation_neg, h]
          exact (neg_neg ω).symm
        · rw [Trivialization.mapOrientation_neg, ho]), readOver_neg]
    simp only [ModuleCat.hom_neg, LinearMap.neg_apply]
    rw [hinv, readFiberClass, readFiberClass, ← map_neg]
    have h' := congrArg (fun f ↦ ModuleCat.Hom.hom f γ)
      (e₀.singularHomologyMap_complZeroPairIso_inv_eq_neg_of_mapOrientation_eq_neg e hx₀ hx hι
        (ModuleCat.of R R) (h.trans (congrArg Neg.neg ho).symm) n)
    rw [ModuleCat.hom_neg, LinearMap.neg_apply] at h'
    exact congrArg (TopPair.singularHomologyMap (fiberThomPairOverMap F E (mem_singleton x))
      (ModuleCat.of R R) n) h'.symm

include hι in
/-- Reversing the orientation of the model fibre negates the twisted fibre class. -/
private theorem signFiberClass_neg [FiniteDimensional ℝ F] (ω : Orientation ℝ F ι) {n : ℕ}
    (γ : ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularHomology
      (ModuleCat.of R R) n : ModuleCat.{w} R)) (x : B) :
    signFiberClass (E := E) hι (-ω) γ x = -signFiberClass hι ω γ x := by
  have hx := mem_baseSet_trivializationAt F E x
  apply (ModuleCat.mono_iff_injective (readOver hι (trivializationAt F E x) ω
    (singleton_subset_iff.2 hx) n)).1 inferInstance
  have h := readOver_signFiberClass hι (trivializationAt F E x) (-ω) γ hx
  rw [readOver_neg] at h
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply] at h
  rw [map_neg, readOver_signFiberClass hι _ ω γ hx, ← h, neg_neg]

/-! ### Fibre classes in the product bundle -/

variable [FiniteDimensional ℝ F]

omit [VectorBundle ℝ F E] in
/-- Through a trivialization, the fibre class over `x` read by it as a multiple `a • g` of the
point class `g` of `Hᵣ(F, F ∖ {0}; R)` is `a` times the class of `x`. -/
private theorem singularHomologyMap_thomPairOverIso_readFiberClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {V : Set B} (hV : V ⊆ e.baseSet) {x : B} (hx : x ∈ V) (a : R) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hV).hom (ModuleCat.of R R) (finrank ℝ F)
        (readFiberClass F E e hx (hV hx)
          (a • complZeroPairPointHom (ModuleCat.of R R) F (finrank ℝ F) rfl (1 : R))) =
      (prodThomPairSingularHomologyIso (ModuleCat.of R R) V F 0 (finrank ℝ F)).inv
        (a • singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of V) ⟨x, hx⟩ 1) := by
  have hfib := ConcreteCategory.congr_hom
    (complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap (ModuleCat.of R R) V F
      (finrank ℝ F) rfl ⟨x, hx⟩) (1 : R)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hfib
  rw [readFiberClass, ← ConcreteCategory.comp_apply (TopPair.singularHomologyMap
      (fiberThomPairOverMap F E hx) (ModuleCat.of R R) (finrank ℝ F)),
    ← TopPair.singularHomologyMap_comp, e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hV hx,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (TopPair.singularHomologyMap
      (e.continuousLinearEquivAt ℝ x (hV hx)).complZeroPairIso.inv (ModuleCat.of R R)
        (finrank ℝ F)),
    ← TopPair.singularHomologyMap_comp, Iso.inv_hom_id, TopPair.singularHomologyMap_id,
    ConcreteCategory.id_apply, map_smul,
    hfib, map_smul]

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
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    ((span_complZeroPairPointHom_one F R).symm ▸ Submodule.mem_top : γ ∈ _)
  rw [← restrictOver_signFiberClassOver (E := E) hι ω γ inter_subset_left h.source_mem,
    ← restrictOver_signFiberClassOver (E := E) hι ω γ inter_subset_left h.target_mem]
  congr 1
  apply (ModuleCat.mono_iff_injective (readOver hι e ω hV (finrank ℝ F) ≫
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hV).hom (ModuleCat.of R R)
      (finrank ℝ F))).1 inferInstance
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    readOver_signFiberClassOver, readOver_signFiberClassOver, ← ha,
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
  obtain ⟨u, hu⟩ := exists_eq_units_smul_complZeroPairPointHom_one F R hγ
  have h : signThomPairOverFinrankInv (E := E) hι ω γ W ≫ readOver hι e ω hW (finrank ℝ F) ≫
      TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of R R) (finrank ℝ F) =
      singularHomology₀UnitsSmul (ModuleCat.of R R) (X := TopCat.of W) (fun _ ↦ u)
          (fun _ _ _ ↦ rfl) ≫
        (prodThomPairSingularHomologyIso (ModuleCat.of R R) W F 0 (finrank ℝ F)).inv := by
    refine singularHomology₀_hom_ext _ fun x ↦ ?_
    rw [singularHomology₀Section_signThomPairOverFinrankInv_assoc,
      singularHomology₀Section_singularHomology₀UnitsSmul_assoc, Linear.smul_comp]
    ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [readOver_signFiberClassOver, hu, singularHomologyMap_thomPairOverIso_readFiberClass,
      map_smul]
  have : IsIso (signThomPairOverFinrankInv (E := E) hι ω γ W ≫ readOver hι e ω hW (finrank ℝ F) ≫
      TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of R R)
        (finrank ℝ F)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (readOver hι e ω hW (finrank ℝ F) ≫
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of R R) (finrank ℝ F))

/-! ### The Mayer–Vietoris step -/

variable (R E) in
/-- The Mayer–Vietoris sequence
`Hᵣ(E|_{U ∩ V}, E₀|_{U ∩ V}) ⟶ Hᵣ(E|_U, E₀|_U) ⊞ Hᵣ(E|_V, E₀|_V) ⟶ Hᵣ(E|_{U ∪ V}, E₀|_{U ∪ V})`
with coefficients in the orientation system, in the rank degree. -/
private abbrev signMayerVietoris (U V : Set B) : ShortComplex (ModuleCat.{w} R) :=
  subsetMayerVietoris (fun h ↦ restrictOver (R := R) (E := E) hι h (finrank ℝ F))
    (fun h h' ↦ restrictOver_comp_restrictOver hι h h' _) U V

/-- The intersection of the pairs of subsets of the total space over `U` and over `V` is the pair
over `U ∩ V`. -/
private abbrev signInterPairIso (U V : Set B) (n : ℕ) :=
  LocalCoefficientSystem.subsetPairTwistedHomologyIso
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
    (inter_subset_left : π F E ⁻¹' (U ∩ V) ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' (U ∩ V))
    (inter_subset_inter inter_subset_left inter_subset_left :
      (π F E ⁻¹' U ∩ zeroSectionCompl F E) ∩ (π F E ⁻¹' V ∩ zeroSectionCompl F E) ⊆
        π F E ⁻¹' U ∩ π F E ⁻¹' V)
    subset_rfl subset_rfl (fun _ hp ↦ ⟨⟨hp.1.1, hp.2⟩, hp.1.2, hp.2⟩)
    (fun _ hp ↦ ⟨⟨hp.1.1, hp.2.1⟩, hp.1.2⟩) n

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
  refine ShortComplex.isoMk (signInterPairIso hι U V _) (Iso.refl _) (subsetPairTwistedHomologyIso
      ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
      (inter_subset_left : π F E ⁻¹' (U ∪ V) ∩ zeroSectionCompl F E ⊆ _)
      (union_subset_union inter_subset_left inter_subset_left) subset_rfl subset_rfl
      (fun _ hp ↦ hp.1.elim (fun h ↦ .inl ⟨h, hp.2⟩) fun h ↦ .inr ⟨h, hp.2⟩)
      (fun _ hp ↦ hp.elim (fun h ↦ ⟨.inl h.1, h.2⟩) fun h ↦ ⟨.inr h.1, h.2⟩) _) ?_ ?_
  -- Every component is a composite of maps induced by inclusions of pairs of subsets. The middle
  -- terms of the two sequences agree only after unfolding the Thom pairs over `U` and `V` into
  -- pairs of subsets, so the identity between them is cancelled by unification
  -- (`Category.comp_id _`, `Category.id_comp _`) rather than by rewriting.
  · refine biprod.hom_ext _ _ ?_ ?_
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (pairTwistedMayerVietorisToBiprod_fst _ _ _ _)).trans
          ((subsetPairTwistedHomologyMap_comp_subsetPairTwistedHomologyMap
            _ _ _ _ _ _ _ _ _).trans ?_))
      exact ((congrArg (· ≫ biprod.fst) (Category.comp_id _)).trans (biprod.lift_fst _ _)).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (pairTwistedMayerVietorisToBiprod_snd _ _ _ _)).trans ((Preadditive.comp_neg _ _).trans
          ((congrArg Neg.neg (subsetPairTwistedHomologyMap_comp_subsetPairTwistedHomologyMap
            _ _ _ _ _ _ _ _ _)).trans ?_)))
      exact ((congrArg (· ≫ biprod.snd) (Category.comp_id _)).trans (biprod.lift_snd _ _)).symm
  · refine biprod.hom_ext' _ _ ?_ ?_
    · refine (congrArg (biprod.inl ≫ ·) (Category.id_comp _)).trans
        ((inl_pairTwistedMayerVietorisFromBiprod _ _ _ _).trans ?_)
      exact ((subsetPairTwistedHomologyMap_comp_subsetPairTwistedHomologyMap
        _ _ _ _ _ _ _ _ _).symm.trans
        (congrArg (· ≫ _) (biprod.inl_desc _ _)).symm).trans (Category.assoc _ _ _)
    · refine (congrArg (biprod.inr ≫ ·) (Category.id_comp _)).trans
        ((inr_pairTwistedMayerVietorisFromBiprod _ _ _ _).trans ?_)
      exact ((subsetPairTwistedHomologyMap_comp_subsetPairTwistedHomologyMap
        _ _ _ _ _ _ _ _ _).symm.trans
        (congrArg (· ≫ _) (biprod.inr_desc _ _)).symm).trans (Category.assoc _ _ _)

omit [FiniteDimensional ℝ F] in
/-- The Mayer–Vietoris sequence over two open sets is exact. -/
private theorem signMayerVietoris_exact {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) :
    (signMayerVietoris R E hι U V).Exact := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  exact (ShortComplex.exact_iff_of_iso (signMayerVietorisIso hι U V)).2
    (LocalCoefficientSystem.pairTwistedMayerVietoris_exact₂ _ _ _ hA hB hC hD _)

omit [FiniteDimensional ℝ F] in
/-- The last map of the Mayer–Vietoris sequence over two open sets is surjective when the twisted
homology over their intersection vanishes in degree `r - 1`. -/
private theorem epi_signMayerVietoris_g {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ m, m + 1 = finrank ℝ F →
      IsZero ((thomPairOver F E (U ∩ V)).twistedHomology (signSystemOver R F E hι (U ∩ V)) m)) :
    Epi (signMayerVietoris R E hι U V).g := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  -- The last map of the sequence of pairs of subsets is surjective, by the exactness at the union.
  have h : Epi (LocalCoefficientSystem.pairTwistedMayerVietorisFromBiprod
      ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))
      (inter_subset_left : (π F E ⁻¹' U ∩ zeroSectionCompl F E : Set (TopCat.of (TotalSpace F E)))
        ⊆ π F E ⁻¹' U)
      (inter_subset_left : (π F E ⁻¹' V ∩ zeroSectionCompl F E : Set (TopCat.of (TotalSpace F E)))
        ⊆ π F E ⁻¹' V) (finrank ℝ F)) := by
    obtain h | ⟨m, hm⟩ : finrank ℝ F = 0 ∨ ∃ m, finrank ℝ F = m + 1 := by
      cases finrank ℝ F <;> simp
    · rw [h]
      exact LocalCoefficientSystem.epi_pairTwistedMayerVietorisFromBiprod_zero _ _ _ hA hB hC hD
    · rw [hm]
      exact (LocalCoefficientSystem.pairTwistedMayerVietoris_exact₃ _ _ _ hA hB hC hD (m + 1)
        m).epi_f (((hUV m hm.symm).of_iso (signInterPairIso hι U V m).symm).eq_of_tgt _ _)
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
  have := TopCat.isIso_restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
    (zeroSectionCompl F E) (S := univ) fun _ ↦ trivial
  exact LocalCoefficientSystem.isIso_relativeTwistedHomologyMap_of_isIso _ _ n

/-! ### The twisted fibre classes through the fibre inclusions -/

variable (E) in
/-- The fibre pair `(E_x, E_x ∖ {0})`. -/
private abbrev fiberPair (x : B) : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (E x)) ({0}ᶜ : Set (E x))

variable (R F E) in
/-- The identification of the orientation system pulled back to the fibre pair over `x` with the
coefficients of the Thom pair over `{x}` pulled back along the fibre inclusion. -/
private abbrev fiberCoeff (x : B) :=
  (LocalCoefficientSystem.pullbackCompIso
      (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_singleton x))).hom
      ((projMap F E).comp (inclOver F E {x}))).hom.app (signLocalSystem F E R hι) ≫
    (LocalCoefficientSystem.pullback
      (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_singleton x))).hom).map
      ((LocalCoefficientSystem.pullbackCompIso (inclOver F E {x}) (projMap F E)).hom.app
        (signLocalSystem F E R hι))

include hι in
/-- Every trivialization `e` of the atlas at `x` exhibits the twisted fibre class over `x` as the
image under the fibre inclusion of the class which `e` reads as the fibre class it reads as `γ`. -/
private theorem signFiberClass_eq (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    {x : B} (hx : x ∈ e.baseSet) :
    signFiberClass hι ω γ x =
      TopPair.twistedHomologyMap (fiberThomPairOverMap F E (mem_singleton x))
        (signSystemOver R F E hι {x}) (finrank ℝ F)
        ((fiberPair E x).twistedHomologyCoefficientMap (fiberCoeff R F E hι x) (finrank ℝ F)
          ((twistedHomologyPullbackSignLocalSystemIso R hι e ω _
            (((projMap F E).comp (inclOver F E {x})).comp
              (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_singleton x))).hom)
            (fun y ↦ singleton_subset_iff.2 hx
              (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_singleton x)) y).property)
            (finrank ℝ F)).inv
            (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv
              (ModuleCat.of R R) (finrank ℝ F) γ))) := by
  apply (ModuleCat.mono_iff_injective (readOver hι e ω (singleton_subset_iff.2 hx)
    (finrank ℝ F))).1 inferInstance
  rw [readOver_signFiberClass hι e ω γ hx]
  unfold readOver
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  rw [TopPair.twistedHomologyMap_naturality_assoc,
    twistedHomologyMap_twistedHomologyPullbackSignLocalSystemIso_hom]
  simp only [← TopPair.twistedHomologyCoefficientMap_comp_assoc, fiberCoeff, Category.assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, TopPair.twistedHomologyCoefficientMap_id, Iso.inv_hom_id_assoc]

variable [CompactSpace B]

include hι in
/-- Over a compact base, the map over the whole base is an isomorphism, by Mayer–Vietoris induction
over finite unions of trivializing open sets. Below the rank, the twisted homology over a
trivializing set is the ordinary one, which vanishes, so the Mayer–Vietoris sequence ends in degree
`r`. -/
private theorem isIso_signThomPairOverFinrankInv_univ (hγ : Submodule.span R {γ} = ⊤) :
    IsIso (signThomPairOverFinrankInv (E := E) hι ω γ univ) := by
  have hMV {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
      (hUc : ∃ c, U ⊆ (trivializationAt F E c).baseSet) :
      (signMayerVietoris R E hι U V).Exact ∧ Epi (signMayerVietoris R E hι U V).g := by
    obtain ⟨c, hc⟩ := hUc
    refine ⟨signMayerVietoris_exact hι hU hV, epi_signMayerVietoris_g hι hU hV fun m hm ↦ ?_⟩
    exact ((trivializationAt F E c).isZero_singularHomology_thomPairOver
      (inter_subset_left.trans hc) (ModuleCat.of R R) (by omega)).of_iso
      (asIso (readOver hι (trivializationAt F E c) ω (inter_subset_left.trans hc) m))
  exact isIso_univ_of_subsetMayerVietoris
    (H := fun W ↦ (thomPairOver F E W).twistedHomology (signSystemOver R F E hι W) (finrank ℝ F))
    (fun h ↦ restrictOver hι h (finrank ℝ F)) (fun h h' ↦ restrictOver_comp_restrictOver hι h h' _)
    (A := TopCat.subspaceDiagram (A := (id : Set B → Set B)) monotone_id ⋙
      (singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R))
    (ψ := signThomPairOverFinrankInv hι ω γ)
    (fun h ↦ signThomPairOverFinrankInv_naturality hι ω γ h)
    (P := fun W ↦ ∃ c, W ⊆ (trivializationAt F E c).baseSet)
    (fun h ⟨c, hc⟩ ↦ ⟨c, h.trans hc⟩)
    (fun _ ⟨c, hc⟩ ↦ isIso_signThomPairOverFinrankInv_of_subset hι ω γ hγ c hc)
    (isIso_signThomPairOverFinrankInv_empty hι ω γ)
    (fun _ _ ↦ epi_biprod_desc_singularHomologyMap_inclusion _ _ _) hMV
    fun b ↦ ⟨_, (trivializationAt F E b).open_baseSet, mem_baseSet_trivializationAt F E b, b,
      subset_rfl⟩

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
the identification of the coefficients and the fibre class
(`TauCeti.thomPairTwistedFiberClass_eq`). -/
def thomPairTwistedFiberClass (b : B) :
    ((thomPair F E).twistedHomology ((LocalCoefficientSystem.pullback
      (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TopCat.of (TotalSpace F E), TopCat.of B))).obj
        (signLocalSystem F E R hι)) (finrank ℝ F) : ModuleCat.{w} R) :=
  TopPair.twistedHomologyMap (univPairMap F E)
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι)) (finrank ℝ F)
    ((thomPairOver F E univ).twistedHomologyCoefficientMap (univCoeffIso (R := R) hι).hom
      (finrank ℝ F) (signFiberClassOver (E := E) hι ω γ (mem_univ b)))

/-- Reversing the orientation `ω` of the model fibre negates the twisted fibre classes. -/
@[simp]
theorem thomPairTwistedFiberClass_neg (b : B) :
    thomPairTwistedFiberClass E hι (-ω) γ b = -thomPairTwistedFiberClass E hι ω γ b := by
  simp only [thomPairTwistedFiberClass, signFiberClassOver, signFiberClass_neg, map_neg]

/-- **The twisted fibre class through a trivialization.** For every trivialization `e` of the atlas
at `b`, the twisted fibre class over `b` is the image under the fibre inclusion
`(E_b, E_b ∖ {0}) ⟶ (E, E₀)` of the class which `e`, identifying the coefficients over the fibre
with `R` by evaluation at the orientation of `E_b` which it reads as `ω`, reads as the fibre class
which it reads as `γ`. -/
theorem thomPairTwistedFiberClass_eq (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    {b : B} (hb : b ∈ e.baseSet) :
    thomPairTwistedFiberClass E hι ω γ b =
      TopPair.twistedHomologyMap (fiberThomPairMap F E b) ((LocalCoefficientSystem.pullback
        (⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TopCat.of (TotalSpace F E), TopCat.of B))).obj
          (signLocalSystem F E R hι)) (finrank ℝ F)
        ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullbackCompIso (TopPair.Hom.fst (fiberThomPairMap F E b)).hom
            ⟨π F E, FiberBundle.continuous_proj F E⟩).hom.app (signLocalSystem F E R hι))
          (finrank ℝ F)
          ((twistedHomologyPullbackSignLocalSystemIso R hι e ω _
            ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TopCat.of (TotalSpace F E),
              TopCat.of B)).comp (TopPair.Hom.fst (fiberThomPairMap F E b)).hom)
            (fun y ↦ (congrArg (· ∈ e.baseSet)
              (congrArg (π F E) (fiberThomPairMap_fst_apply F E b y))).mpr hb) (finrank ℝ F)).inv
            (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
              (ModuleCat.of R R) (finrank ℝ F) γ))) := by
  have hf : fiberThomPairOverMap F E (mem_singleton b) ≫ pairInclOver F E (subset_univ {b}) ≫
      univPairMap F E = fiberThomPairMap F E b := by
    rw [pairInclOver_eq, fiberThomPairOverMap_comp_thomPairOverMap_assoc,
      fiberThomPairOverMap_comp_restrictPreimagePairMap]
  have hG : (projMap F E).comp (TopPair.Hom.fst (fiberThomPairMap F E b)).hom =
      ((projMap F E).comp (inclOver F E {b})).comp
        (TopPair.Hom.fst (fiberThomPairOverMap F E (mem_singleton b))).hom := by
    ext y
    exact (congrArg (π F E) (fiberThomPairMap_fst_apply F E b y)).trans
      ((TopPair.Hom.fst (fiberThomPairOverMap F E (mem_singleton b)) y).property : _ = b).symm
  rw [thomPairTwistedFiberClass, signFiberClassOver, signFiberClass_eq hι ω γ e hb,
    twistedHomologyPullbackSignLocalSystemIso_inv_of_eq hι e ω _ hG (fun y ↦ (congrArg
      (· ∈ e.baseSet) (congrArg (π F E) (fiberThomPairMap_fst_apply F E b y))).mpr hb)]
  simp only [← ConcreteCategory.comp_apply]
  -- The coefficient comparison on the right lands in a composite of pullback functors, which is
  -- only definitionally the source of the map induced by the fibre inclusion, so the right side is
  -- folded into one morphism by unification.
  refine (ConcreteCategory.congr_hom (C := ModuleCat.{w} R) (?_ : _ = _ ≫ _ ≫
    (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).twistedHomologyCoefficientMap _
      (finrank ℝ F) ≫ TopPair.twistedHomologyMap (fiberThomPairMap F E b) _ (finrank ℝ F)) γ).trans
        rfl
  rw [restrictOver_eq]
  simp only [Category.assoc, TopPair.twistedHomologyMap_naturality_assoc]
  -- The coefficient system lives on the total space, which is only definitionally the ambient
  -- space of the Thom pair, so it is given explicitly.
  rw [TopPair.twistedHomologyMap_comp_comp _ _ _ hf
    ((LocalCoefficientSystem.pullback (projMap F E)).obj (signLocalSystem F E R hι))]
  simp only [← TopPair.twistedHomologyCoefficientMap_comp_assoc]
  congr 4
  ext y : 2
  simp only [fiberCoeff, restrictCoeff, univCoeffIso, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    LocalCoefficientSystem.pullback_map_app, LocalCoefficientSystem.pullbackCompIso_hom_app_app]
  -- The fibres of the various pulled-back systems over `y` agree only definitionally, so the
  -- remaining component lemmas and identity cancellations apply only up to unfolding. What is left
  -- is a composite of `eqToHom`s.
  erw [LocalCoefficientSystem.pullback_map_app, LocalCoefficientSystem.pullbackCompIso_hom_app_app,
    TopPair.fstPullbackCompIso_inv_app, TopPair.fstPullbackCompIso_inv_app, Category.id_comp,
    Category.id_comp, Category.id_comp, Category.id_comp, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl]
  rfl

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
      (E := E) hι ω γ (W := univ) ((TopCat.isoOfHomeo (X := TopCat.of B)
        (Y := TopCat.of (univ : Set B)) (Homeomorph.Set.univ B).symm).hom b)) (1 : R)
    rw [ConcreteCategory.comp_apply] at hsec hΨ
    rw [signThomPairFinrankInv, ConcreteCategory.comp_apply, hsec]
    simp only [ConcreteCategory.comp_apply]
    rw [hΨ]
    simp [thomPairTwistedFiberClass]
  rw [← h, thomPairTwistedHomologyFinrankIso, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

end ThomPair

end TauCeti
