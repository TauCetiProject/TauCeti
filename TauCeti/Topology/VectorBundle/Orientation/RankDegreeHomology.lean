/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic
import TauCeti.Topology.Homotopy.Covering

/-!
# The homology of the Thom pair in the rank degree, with twisted coefficients

Let `E → B` be a real vector bundle of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`,
and let `K` be a ring, such as `ℤ`. An orientation `ω` of the model fibre `F` assigns a generator
of `Hᵣ(E_b, E_b ∖ {0}; K) ≅ K` to each orientation of `E_b`
(`TauCeti.orientedFiberGenerator`), and reversing the orientation negates the generator. The
rank `r` is the lowest degree in which the homology of the Thom pair can be nonzero, and in that
degree it is the zeroth homology of `B` twisted by the orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`):

`Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)`

(`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology`), with no orientability assumption.
The fibre of `o(E)` over `b` consists of the functions `f` on the orientations of `E_b` with
`f (-o) = -f o`, and the class of `f` goes to `f o` times the fibre class of the generator of `o`.
A linear trivialization reading `o` as `ω` carries the generator of `o` to the point class of `1`
(`TauCeti.complZeroPairPointHom`) in `Hᵣ(F, F ∖ {0}; K)`. When `1` is the only unit of `K`, or
when `E` is oriented, the twist disappears and this is `Hᵣ(E, E₀; K) ≅ H₀(B; K)`
(`TauCeti.thomPairSingularHomologyFinrankIso`,
`TauCeti.VectorBundleOrientation.thomPairSingularHomologyFinrankIso`). The homology of the Thom
pair with coefficients in the pulled-back orientation system is a different group, computed in
`TauCeti.Topology.VectorBundle.Thom.TwistedRankDegreeHomology`. When `E` is the negative normal
bundle of a Morse–Bott critical submanifold, `r` is the lowest degree in which the relative
homology across the critical level can be nonzero, and this identifies the group in that degree
with the zeroth homology of the submanifold twisted by the orientations of its negative bundle;
`TauCeti.Geometry.Manifold.Morse.Bott.RankDegreeHomology` reads the orientability of the negative
bundle off that group.

## The proof

Every linear trivialization reading an orientation of `E_b` as `ω` carries its generator to the
point class of `1` (`TauCeti.orientedFiberGenerator_of_mapOrientation_eq`). Over a subset `W` of
the base, the fibre classes in `Hᵣ(E|_W, E₀|_W; K)` of these generators are constant along paths
in the orientation double cover over `W`, since near each point such a path stays in a sheet of a
trivialization. Transport in `o(E)` is lifting of paths to the double cover, so by the colimit
description of twisted zeroth homology
(`TauCeti.LocalCoefficientSystem.isColimitTwistedHomology₀Cocone`) the fibre classes define
`H₀(W; o(E) ⊗ K) ⟶ Hᵣ(E|_W, E₀|_W; K)`, natural in `W`. Over a subset of a trivializing set this
is an isomorphism: followed by `Hᵣ(E|_W, E₀|_W; K) ≅ H₀(W; K)`, it is the map induced by the
trivialization of `o(E)` over `W` by the orientations read as `ω`
(`TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIso`). The
Mayer–Vietoris and compact-support argument `TauCeti.isIso_of_isColimit_biUnion_baseSet` then
makes the map over the whole base an isomorphism.

## Main results

* `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology`: `Hᵣ(E, E₀; K) ≅ H₀(B; o(E) ⊗ K)` for
  any ring `K`.
* `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀_eq_smul`,
  `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply_orientedFiberGenerator`:
  its values on the classes of the fibres and on the fibre classes of the generators.
* `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀`,
  `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply`: the same values, read
  through a linear trivialization.
* `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_neg_hom`,
  `TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_neg_inv`: reversing the model
  orientation `ω` negates the isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation local
  system) and Section 4.D, Theorem 4D.10 and its proof.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261 (the
  relative homology across a critical level with coefficients twisted by the orientations of the
  negative bundle).
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

section Twisted

variable {K : Type w} [Ring K] {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)

open VectorBundleOrientationCover

/-! ### The fibre classes over a subset of the base -/

variable (K) in
/-- The fibre class in `Hᵣ(E|_W, E₀|_W; K)` of an orientation `o` of the fibre over `b ∈ W`: the
image of the generator of `o` under the inclusion of the fibre pair. -/
private def fiberClassOver (W : Set B) {b : B} (hb : b ∈ W) (o : Orientation ℝ (E b) ι) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) : ModuleCat.{w} K) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E hb) (ModuleCat.of K K) (finrank ℝ F)
    (orientedFiberGenerator K ω o)

include hι in
private theorem fiberClassOver_neg (W : Set B) {b : B} (hb : b ∈ W) (o : Orientation ℝ (E b) ι) :
    fiberClassOver K ω W hb (-o) = -fiberClassOver K ω W hb o := by
  rw [fiberClassOver, fiberClassOver, orientedFiberGenerator_neg ω hι, map_neg]

include hι in
/-- Two points on the same sheet of a linear trivialization, over points joined in `W` and in its
base set, have the same fibre class over `W`. -/
private theorem fiberClassOver_eq_of_mem_sheet (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {ω' : Orientation ℝ F ι} {W : Set B} {p q : VectorBundleOrientationCover F E ι}
    (hp : p ∈ sheet e ω') (hq : q ∈ sheet e ω') (h : JoinedIn (W ∩ e.baseSet) p.proj q.proj) :
    fiberClassOver K ω W h.source_mem.1 p.orientation =
      fiberClassOver K ω W h.target_mem.1 q.orientation := by
  obtain ⟨hpe, hp⟩ := mem_sheet_iff.1 hp
  obtain ⟨hqe, hq⟩ := mem_sheet_iff.1 hq
  -- Classes of `Hᵣ(F, F ∖ {0})` read through `e` at `p.proj` and `q.proj` have the same image in
  -- `Hᵣ(E|_W, E₀|_W)`.
  have hj := e.singularHomologyMap_complZeroPairIso_inv_comp_fiberThomPairOverMap_eq_of_joinedIn
    (ModuleCat.of K K) h (finrank ℝ F) rfl
  have hg (g) := congr($hj g)
  simp only [TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply] at hg
  rw [fiberClassOver, fiberClassOver]
  rcases ω'.eq_or_eq_neg ω (Nat.card_eq_fintype_card.trans hι) with hω | hω
  · rw [orientedFiberGenerator_of_mapOrientation_eq ω hι e hpe (hp.trans hω),
      orientedFiberGenerator_of_mapOrientation_eq ω hι e hqe (hq.trans hω), hg]
  · rw [orientedFiberGenerator_of_mapOrientation_eq_neg ω hι e hpe (hp.trans hω),
      orientedFiberGenerator_of_mapOrientation_eq_neg ω hι e hqe (hq.trans hω), map_neg, map_neg,
      hg]

include hι in
/-- **The fibre classes are constant along paths in the orientation double cover** whose base
points stay in `W`: near each point such a path stays on a sheet of a trivialization. -/
private theorem fiberClassOver_eq_of_continuous (W : Set B)
    (Γ : C(unitInterval, VectorBundleOrientationCover F E ι)) (hΓ : ∀ t, (Γ t).proj ∈ W)
    {c₀ c₁ : VectorBundleOrientationCover F E ι} (h₀ : Γ 0 = c₀) (h₁ : Γ 1 = c₁)
    (hc₀ : c₀.proj ∈ W) (hc₁ : c₁.proj ∈ W) :
    fiberClassOver K ω W hc₀ c₀.orientation = fiberClassOver K ω W hc₁ c₁.orientation := by
  subst h₀ h₁
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hlc : IsLocallyConstant fun t ↦ fiberClassOver K ω W (hΓ t) (Γ t).orientation := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    -- Near `t` the path stays on the sheet through `Γ t` of the preferred trivialization.
    let e := trivializationAt F E (Γ t).proj
    let ω' := e.mapOrientation ι (mem_baseSet_trivializationAt F E _) (Γ t).orientation
    have ht : Γ t ∈ sheet e ω' := mem_sheet_iff.2 ⟨mem_baseSet_trivializationAt F E _, rfl⟩
    have hS : Γ ⁻¹' sheet e ω' ∈ 𝓝 t :=
      ((isOpen_sheet hι e ω').preimage Γ.continuous).mem_nhds ht
    filter_upwards [pathComponentIn_mem_nhds hS] with s hs
    refine (fiberClassOver_eq_of_mem_sheet hι ω e ht hs.target_mem ?_).symm
    refine (hs.map (continuous_proj.comp Γ.continuous).continuousOn).mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hΓ u, (mem_sheet_iff.1 hu).1⟩
  exact hlc.apply_eq_of_preconnectedSpace 0 1

/-- The orientation of the fibre over `b` that the preferred trivialization at `b` reads as the
model orientation `ω`. -/
private def modelFiberOrientation (b : B) : Orientation ℝ (E b) ι :=
  ((trivializationAt F E b).mapOrientation ι (mem_baseSet_trivializationAt F E b)).symm ω

variable (K) in
/-- The map from the fibre of the orientation local system over `b ∈ W` to
`Hᵣ(E|_W, E₀|_W; K)`: a function `f` on the orientations of `E_b` goes to `f o` times the fibre
class of `o`, for any orientation `o` (`twistedFiberClass_apply`). -/
private def twistedFiberClass (W : Set B) {b : B} (hb : b ∈ W) :
    (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b) ⟶
      (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton K _
      (fiberClassOver K ω W hb (modelFiberOrientation ω b)) ∘ₗ
    (signLocalSystemFiberEquiv (R := K) hι (modelFiberOrientation ω b)).toLinearMap)

/-- `twistedFiberClass` evaluates `f` at the model orientation of `E_b`. -/
private theorem twistedFiberClass_apply_model (W : Set B) {b : B} (hb : b ∈ W)
    (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    twistedFiberClass K hι ω W hb f =
      signLocalSystemFiberEquiv hι (modelFiberOrientation ω b) f •
        fiberClassOver K ω W hb (modelFiberOrientation ω b) :=
  -- The fibre of the orientation local system is a `ModuleCat` only by unfolding, which `rw` and
  -- `simp` do not see through `ModuleCat.ofHom`, so the apply lemmas are chained as terms.
  (ModuleCat.ofHom_apply _ f).trans
    ((LinearMap.comp_apply _ _ f).trans (LinearMap.toSpanSingleton_apply K _ _ _))

/-- `twistedFiberClass` evaluates `f` at any orientation `o` of `E_b`. -/
private theorem twistedFiberClass_apply (W : Set B) {b : B} (hb : b ∈ W)
    (o : Orientation ℝ (E b) ι) (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    twistedFiberClass K hι ω W hb f =
      signLocalSystemFiberEquiv hι o f • fiberClassOver K ω W hb o := by
  -- As points of the orientation double cover over `b`, `o` and the model orientation are equal
  -- or exchanged by the deck involution.
  rcases eq_or_eq_deck hι (p := ⟨b, modelFiberOrientation ω b⟩) (q := ⟨b, o⟩) rfl with h | h
  · obtain rfl := mk_eq_mk_iff.1 h
    exact twistedFiberClass_apply_model hι ω W hb f
  · obtain rfl := mk_eq_mk_iff.1 (h.trans (deck_apply _))
    rw [signLocalSystemFiberEquiv_neg, fiberClassOver_neg hι, neg_smul_neg]
    exact twistedFiberClass_apply_model hι ω W hb f

/-- The value of `twistedFiberClass` on `f`, computed at any point `q` of the orientation double
cover over `b`. -/
private theorem twistedFiberClass_apply_mem (W : Set B) {b : B} (hb : b ∈ W)
    (q : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)))
    (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    twistedFiberClass K hι ω W hb f =
      (signLocalSystemObjEquiv hι (FundamentalGroupoid.mk b) f :
        (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)) → K) q •
        fiberClassOver K ω W (by rwa [Set.mem_singleton_iff.1 q.property]) q.val.orientation := by
  obtain ⟨⟨b', o⟩, hq⟩ := q
  obtain rfl : b' = b := Set.mem_singleton_iff.1 hq
  rw [twistedFiberClass_apply hι ω W hb o, signLocalSystemFiberEquiv_apply]

/-- **The fibre maps are natural along paths in `W`**: transport in the orientation local system
is monodromy in the orientation double cover, and the fibre classes are constant along the lifted
path. -/
@[reassoc]
private theorem map_mk_comp_twistedFiberClass (W : Set B) {x y : B} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ W) (hx : x ∈ W) (hy : y ∈ W) :
    (signLocalSystem F E K hι).map (Path.Homotopic.Quotient.mk γ) ≫
        twistedFiberClass K hι ω W hy = twistedFiberClass K hι ω W hx := by
  set cov := isCoveringMap_proj (F := F) (E := E) hι
  -- The reversed path, lifted through the model orientation at its start `y`.
  let c₀ : (proj ⁻¹' {y} : Set (VectorBundleOrientationCover F E ι)) :=
    ⟨⟨y, modelFiberOrientation ω y⟩, rfl⟩
  have hc₀ : γ.symm 0 = proj c₀.val := by simp [c₀]
  let Γ := cov.liftPath γ.symm c₀.val hc₀
  have hΓ (t : unitInterval) : (Γ t).proj ∈ W := by
    rw [show (Γ t).proj = γ.symm t from congrFun (cov.liftPath_lifts γ.symm c₀.val hc₀) t]
    exact hγ _
  let q : FundamentalGroupoid.mk (X := TopCat.of B) x ⟶ FundamentalGroupoid.mk y :=
    Path.Homotopic.Quotient.mk γ
  ext f
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, twistedFiberClass_apply_mem hι ω W hy c₀,
    twistedFiberClass_apply_mem hι ω W hx (cov.monodromy (inv q) c₀),
    signLocalSystemObjEquiv_map_apply]
  congr 1
  exact fiberClassOver_eq_of_continuous hι ω W Γ hΓ (cov.liftPath_zero _ _ _)
    (cov.coe_monodromy_inv_mk γ c₀).symm _ _

/-- The fibre maps commute with the restrictions of Thom pairs. -/
@[reassoc]
private theorem twistedFiberClass_comp_singularHomologyMap_thomPairOverMap {W W' : Set B}
    (h : W ⊆ W') {b : B} (hb : b ∈ W) :
    twistedFiberClass K hι ω W hb ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) =
      twistedFiberClass K hι ω W' (h hb) := by
  ext f
  rw [ModuleCat.hom_comp, LinearMap.comp_apply,
    twistedFiberClass_apply hι ω W hb (modelFiberOrientation ω b),
    twistedFiberClass_apply hι ω W' (h hb) (modelFiberOrientation ω b), map_smul, fiberClassOver,
    fiberClassOver, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    fiberThomPairOverMap_comp_thomPairOverMap]

/-! ### The comparison maps over the subsets of the base -/

variable (K E) in
/-- The restriction to `W` of the orientation local system with coefficients `K`. -/
private abbrev signLocalSystemOver (W : Set B) :
    LocalCoefficientSystem.{w, w, w} K (TopCat.of W) :=
  (LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
    (signLocalSystem F E K hι)

variable (K E) in
/-- The zeroth homology of the restrictions of the orientation local system to the subsets of the
base, as a functor of the subset. -/
private abbrev signHomologyFunctor : Set B ⥤ ModuleCat.{w} K :=
  LocalCoefficientSystem.subsetTwistedHomologyFunctor.{w, w, w, w} (signLocalSystem F E K hι)
    (U := (id : Set B → Set B)) monotone_id 0

variable (K) in
/-- The fibre maps over `W`, as a cocone on the restriction to `W` of the orientation local
system. -/
private def twistedFiberCoconeOver (W : Set B) : Cocone (signLocalSystemOver K E hι W) where
  pt := (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F)
  ι :=
    { app x := twistedFiberClass K hι ω W x.as.property
      naturality x y p := by
        induction p using Path.Homotopic.Quotient.ind with
        | mk γ =>
          exact (map_mk_comp_twistedFiberClass hι ω W (γ.map continuous_subtypeVal)
            (fun t ↦ (γ t).property) x.as.property y.as.property).trans (Category.comp_id _).symm }

variable (K E) in
/-- The map `H₀(W; o(E) ⊗ K) ⟶ Hᵣ(E|_W, E₀|_W; K)` sending the class of `f` over `b` to
`twistedFiberClass`. -/
private def thomPairOverTwistedDesc (W : Set B) :
    LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystemOver K E hι W) 0 ⟶
      (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone.{w, w, w} _).desc
    (twistedFiberCoconeOver K hι ω W)

@[reassoc]
private theorem ιTwistedHomology₀_thomPairOverTwistedDesc (W : Set B) (x : W) :
    LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystemOver K E hι W) x ≫
        thomPairOverTwistedDesc K E hι ω W =
      twistedFiberClass K hι ω W x.property :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone.{w, w, w} _).fac
    (twistedFiberCoconeOver K hι ω W) (FundamentalGroupoid.mk x)

private theorem thomPairOverTwistedDesc_ιTwistedHomology₀_apply (W : Set B) (x : W)
    (f : (signLocalSystemOver K E hι W).obj (FundamentalGroupoid.mk x)) :
    thomPairOverTwistedDesc K E hι ω W
        (LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystemOver K E hι W) x f) =
      twistedFiberClass K hι ω W x.property f :=
  ConcreteCategory.congr_hom (ιTwistedHomology₀_thomPairOverTwistedDesc hι ω W x) f

/-- The maps `thomPairOverTwistedDesc` commute with the restrictions. -/
private theorem signHomologyFunctor_map_comp_thomPairOverTwistedDesc {W W' : Set B}
    (h : W ⊆ W') :
    (signHomologyFunctor K E hι).map (homOfLE h) ≫ thomPairOverTwistedDesc K E hι ω W' =
      thomPairOverTwistedDesc K E hι ω W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) := by
  refine LocalCoefficientSystem.twistedHomology₀_hom_ext (signLocalSystemOver K E hι W)
    fun x ↦ ?_
  -- Both sides send the fibre over `x` to `twistedFiberClass` over `W'`. The fibres of the
  -- restricted local systems over `x` are that of `B` only by unfolding, which `rw` does not see
  -- through in the composites, so each side is computed as a term.
  have h₁ : LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystemOver K E hι W) x ≫
      (signHomologyFunctor K E hι).map (homOfLE h) ≫ thomPairOverTwistedDesc K E hι ω W' =
        twistedFiberClass K hι ω W' (h x.property) :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker
      (LocalCoefficientSystem.ιTwistedHomology₀_homologyMap_subsetTwistedChainComplexMap
        (signLocalSystem F E K hι) h x) _).trans
      (ιTwistedHomology₀_thomPairOverTwistedDesc hι ω W' (inclusion h x)))
  have h₂ : LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystemOver K E hι W) x ≫
      thomPairOverTwistedDesc K E hι ω W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of K K) (finrank ℝ F) =
        twistedFiberClass K hι ω W' (h x.property) :=
    (ιTwistedHomology₀_thomPairOverTwistedDesc_assoc hι ω W x _).trans
      (twistedFiberClass_comp_singularHomologyMap_thomPairOverMap hι ω h x.property)
  exact h₁.trans h₂.symm

section Trivial

variable (b₀ : B) {W : Set B} (hW : W ⊆ (trivializationAt F E b₀).baseSet)

variable (K) in
/-- The trivialization at `b₀` and the product computation, `Hᵣ(E|_W, E₀|_W; K) ≅ H₀(W; K)`. -/
private def trivIso : (thomPairOver F E W).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
    ((singularHomologyFunctor (ModuleCat.{w} K) 0).obj (ModuleCat.of K K)).obj (TopCat.of W) :=
  asIso (TopPair.singularHomologyMap ((trivializationAt F E b₀).thomPairOverIso ℝ hW).hom
      (ModuleCat.of K K) (finrank ℝ F)) ≪≫
    prodThomPairSingularHomologyIso (ModuleCat.of K K) W F 0 (finrank ℝ F)

include hι in
/-- Through the trivialization, the fibre class of the orientation read as `ω` is the class of the
point. -/
private theorem trivIso_hom_fiberClassOver (x : W) :
    (trivIso K b₀ hW).hom (fiberClassOver K ω W x.property
        (((trivializationAt F E b₀).mapOrientation ι (hW x.property)).symm ω)) =
      singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x 1 := by
  rw [trivIso, Iso.trans_hom, asIso_hom, ConcreteCategory.comp_apply, fiberClassOver,
    (trivializationAt F E b₀).singularHomologyMap_thomPairOverIso_hom_fiberThomPairOverMap hW x
      (c := 1) ?_, one_smul, Iso.inv_hom_id_apply]
  -- The trivialization at `b₀` reads the generator of the orientation read as `ω` as the point
  -- class of `1`.
  rw [orientedFiberGenerator_of_mapOrientation_eq ω hι _ (hW x.property)
    (Equiv.apply_symm_apply _ _), one_smul]
  exact (TopPair.singularHomologyMapIso _ _ _).inv_hom_id_apply _

/-- Over a subset of a trivializing set, the comparison map read through the trivialization is the
trivialization of the orientation local system by the orientations read as `ω`
(`TauCeti.VectorBundleOrientationCover.pullbackSignLocalSystemIso`) followed by the comparison of
untwisted with ordinary homology. -/
private theorem thomPairOverTwistedDesc_comp_trivIso_hom :
    thomPairOverTwistedDesc K E hι ω W ≫ (trivIso K b₀ hW).hom =
      LocalCoefficientSystem.twistedHomologyCoefficientMap
          (pullbackSignLocalSystemIso K hι (trivializationAt F E b₀) ω
            (ContinuousMap.subtypeVal W) fun x : W ↦ hW x.property).hom 0 ≫
        (LocalCoefficientSystem.twistedHomologyConstantIso (TopCat.of W) (ModuleCat.of K K)
          0).hom := by
  refine LocalCoefficientSystem.twistedHomology₀_hom_ext (signLocalSystemOver K E hι W)
    fun x ↦ ?_
  -- Both sides send `f` to the class of `x` multiplied by the value of `f` at the orientation read
  -- as `ω`.
  have h (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk x.val)) :
      (trivIso K b₀ hW).hom (twistedFiberClass K hι ω W x.property f) =
        singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x
          (signLocalSystemFiberEquiv (R := K) hι
            (((trivializationAt F E b₀).mapOrientation ι (hW x.property)).symm ω) f) := by
    rw [twistedFiberClass_apply hι ω W x.property _ f, map_smul, trivIso_hom_fiberClassOver hι,
      ← map_smul, smul_eq_mul, mul_one]
  rw [LocalCoefficientSystem.ιTwistedHomology₀_coefficientMap_assoc,
    LocalCoefficientSystem.ιTwistedHomology₀_twistedHomologyConstantIso_hom]
  ext f
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [thomPairOverTwistedDesc_ιTwistedHomology₀_apply]
  -- The fibre of the restricted local system over `x` is that of `B` only by unfolding, so `h` and
  -- the evaluation of the trivialization of the local system are applied as terms.
  exact (h f).trans (congrArg (singularHomology₀Section (ModuleCat.of K K) (X := TopCat.of W) x)
    (pullbackSignLocalSystemIso_hom_app_apply (R := K) (Y := TopCat.of W) hι
      (trivializationAt F E b₀) ω (ContinuousMap.subtypeVal W) (fun x : W ↦ hW x.property) x
      f).symm)

include hW in
private theorem isIso_thomPairOverTwistedDesc_of_subset :
    IsIso (thomPairOverTwistedDesc K E hι ω W) := by
  rw [(Iso.eq_comp_inv _).2 (thomPairOverTwistedDesc_comp_trivIso_hom hι ω b₀ hW)]
  infer_instance

end Trivial

/-! ### The passage to the whole base -/

variable (K) in
/-- The fibre classes in `Hᵣ(E, E₀; K)`, as a cocone on the orientation local system. -/
private def twistedFiberCocone : Cocone (signLocalSystem F E K hι) where
  pt := (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F)
  ι :=
    { app x := twistedFiberClass K hι ω univ (mem_univ x.as) ≫
        TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F)
      naturality x y p := by
        induction p using Path.Homotopic.Quotient.ind with
        | mk γ =>
          exact (map_mk_comp_twistedFiberClass_assoc hι ω univ γ (fun _ ↦ mem_univ _) (mem_univ _)
            (mem_univ _) _).trans (Category.comp_id _).symm }

variable (K E) in
/-- The map `H₀(B; o(E) ⊗ K) ⟶ Hᵣ(E, E₀; K)` sending the class of `f` in the fibre over `b` to
`twistedFiberClass`. -/
private def twistedHomologyThomPairDesc :
    LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0 ⟶
      (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone.{w, w, w} _).desc
    (twistedFiberCocone K hι ω)

@[reassoc]
private theorem ιTwistedHomology₀_twistedHomologyThomPairDesc (b : B) :
    LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b ≫
        twistedHomologyThomPairDesc K E hι ω =
      twistedFiberClass K hι ω univ (mem_univ b) ≫ TopPair.singularHomologyMap
        (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F) :=
  (LocalCoefficientSystem.isColimitTwistedHomology₀Cocone.{w, w, w} _).fac
    (twistedFiberCocone K hι ω) (FundamentalGroupoid.mk b)

/-- Over a subset `W`, the map on the whole base restricts to the map over `W`. -/
private theorem twistedHomologyMap_subtypeVal_comp_twistedHomologyThomPairDesc (W : Set B) :
    LocalCoefficientSystem.twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W))
        (signLocalSystem F E K hι) 0 ≫ twistedHomologyThomPairDesc K E hι ω =
      thomPairOverTwistedDesc K E hι ω W ≫ TopPair.singularHomologyMap
        (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom)
        (ModuleCat.of K K) (finrank ℝ F) := by
  refine LocalCoefficientSystem.twistedHomology₀_hom_ext (signLocalSystemOver K E hι W)
    fun x ↦ ?_
  -- Both sides send the fibre over `x` to `twistedFiberClass` over the whole base, followed by the
  -- identification of the pair over it with `(E, E₀)`. The fibres over `x` and over `x` as a point
  -- of `B` agree only by unfolding, which `rw` does not see through in the composites, so each
  -- side is computed as a term.
  have h₁ : LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystemOver K E hι W) x ≫
      LocalCoefficientSystem.twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W))
        (signLocalSystem F E K hι) 0 ≫ twistedHomologyThomPairDesc K E hι ω =
        twistedFiberClass K hι ω univ (mem_univ x.val) ≫ TopPair.singularHomologyMap
          (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F) :=
    (LocalCoefficientSystem.ιTwistedHomology₀_homologyMap_assoc (signLocalSystem F E K hι)
      (TopCat.ofHom (ContinuousMap.subtypeVal W)) x _).trans
      (ιTwistedHomology₀_twistedHomologyThomPairDesc hι ω x.val)
  have h₂ : LocalCoefficientSystem.ιTwistedHomology₀ (signLocalSystemOver K E hι W) x ≫
      thomPairOverTwistedDesc K E hι ω W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E (subset_univ W)) (ModuleCat.of K K)
          (finrank ℝ F) ≫
        TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom (ModuleCat.of K K)
          (finrank ℝ F) =
        twistedFiberClass K hι ω univ (mem_univ x.val) ≫ TopPair.singularHomologyMap
          (thomPairOverUnivIso F E).hom (ModuleCat.of K K) (finrank ℝ F) :=
    (ιTwistedHomology₀_thomPairOverTwistedDesc_assoc hι ω W x _).trans
      (twistedFiberClass_comp_singularHomologyMap_thomPairOverMap_assoc hι ω (subset_univ W)
        x.property _)
  rw [TopPair.singularHomologyMap_comp]
  exact h₁.trans h₂.symm

/-- **The passage to the whole base**: by the Mayer–Vietoris and compact-support argument, the
map is an isomorphism, since it is one over every subset of a trivializing set. -/
private theorem isIso_twistedHomologyThomPairDesc : IsIso (twistedHomologyThomPairDesc K E hι ω) :=
  isIso_of_isColimit_biUnion_baseSet (A := signHomologyFunctor K E hι)
    (ψ := thomPairOverTwistedDesc K E hι ω) le_rfl
    (signHomologyFunctor_map_comp_thomPairOverTwistedDesc hι ω)
    (fun _ _ ↦
      LocalCoefficientSystem.epi_biprod_desc_homologyMap_subsetTwistedChainComplexMap _ _ _)
    (LocalCoefficientSystem.isZero_twistedHomology_zero_of_isEmpty
      (X := TopCat.of (∅ : Set B)) _)
    (fun b _ hW ↦ isIso_thomPairOverTwistedDesc_of_subset hι ω b hW)
    (LocalCoefficientSystem.isColimitSubsetTwistedHomologyCocone (signLocalSystem F E K hι)
      (monotone_biUnion_baseSet_trivializationAt F E) 0 fun _ hL ↦
        hL.elim_finite_subcover _ (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩)
    (twistedHomologyThomPairDesc K E hι ω) fun _ ↦
      twistedHomologyMap_subtypeVal_comp_twistedHomologyThomPairDesc hι ω _

variable (K F E) in
/-- **The homology of the Thom pair in the rank degree, with twisted coefficients.** For a real
vector bundle `E → B` of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`, and any
ring `K`, `Hᵣ(E, E₀; K)` is the zeroth homology of `B` with coefficients in the
orientation local system `o(E)` of `E` (with coefficients `K`). No orientability is assumed; an
orientation of `E` trivializes `o(E)` (`TauCeti.VectorBundleOrientation.signLocalSystemIso`).

The isomorphism depends on the choice of an orientation `ω` of the model fibre `F` (orientations
are defined by alternating forms indexed by the finite type `ι` of cardinality `r`, for instance
`Fin r`), which fixes which orientation of a fibre corresponds to
the point class of `1` (`TauCeti.complZeroPairPointHom`) in `Hᵣ(F, F ∖ {0}; K)`: a linear
trivialization reading an orientation of `E_b` as `ω` carries the class of that orientation to the
fibre class of the point class of `1`
(`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀`,
`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply`). In terms of the generator
`TauCeti.orientedFiberGenerator` of an arbitrary orientation `o` of `E_b`, the class of `f` goes to
`f o` times the fibre class of the generator of `o`
(`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀_eq_smul`,
`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply_orientedFiberGenerator`).
The opposite choice of `ω` negates the isomorphism
(`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_neg_hom`,
`TauCeti.thomPairSingularHomologyFinrankIsoTwistedHomology_neg_inv`). -/
def thomPairSingularHomologyFinrankIsoTwistedHomology :
    (thomPair F E).singularHomology (ModuleCat.of K K) (finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) 0 :=
  have := isIso_twistedHomologyThomPairDesc (K := K) (E := E) hι ω
  (asIso (twistedHomologyThomPairDesc K E hι ω)).symm

private theorem thomPairSingularHomologyFinrankIsoTwistedHomology_inv :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).inv =
      twistedHomologyThomPairDesc K E hι ω :=
  rfl

/-- **The twisted Thom isomorphism on the class of a fibre function.** For any orientation `o` of
`E_b`, the class of `f` in the fibre of the orientation local system over `b` goes to `f o` times
the fibre class of the generator of `o`. -/
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀_eq_smul {b : B}
    (o : Orientation ℝ (E b) ι) (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).inv
        (LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b f) =
      signLocalSystemFiberEquiv hι o f •
        TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (orientedFiberGenerator K ω o) := by
  rw [← ConcreteCategory.comp_apply, thomPairSingularHomologyFinrankIsoTwistedHomology_inv,
    ιTwistedHomology₀_twistedHomologyThomPairDesc, ConcreteCategory.comp_apply,
    twistedFiberClass_apply hι ω univ (mem_univ b) o, map_smul, fiberClassOver,
    ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    fiberThomPairOverMap_comp_thomPairOverUnivIso_hom]

/-- **The twisted Thom isomorphism on the fibre class of a generator.** For any orientation `o` of
`E_b`, the fibre class of the generator of `o` goes to the class of the function on the
orientations of `E_b` equal to `1` at `o`. -/
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply_orientedFiberGenerator {b : B}
    (o : Orientation ℝ (E b) ι) :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (orientedFiberGenerator K ω o)) =
      LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b
        ((signLocalSystemFiberEquiv hι o).symm 1) := by
  have h := thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀_eq_smul hι ω o
    ((signLocalSystemFiberEquiv (R := K) hι o).symm 1)
  rw [LinearEquiv.apply_symm_apply, one_smul] at h
  rw [← h, Iso.inv_hom_id_apply]

/-- **The twisted Thom isomorphism on the class of a fibre function.** Let `e` be a linear
trivialization whose base set contains `b`, and `o` the orientation of `E_b` that `e` reads as the
model orientation `ω`. The class of `f` in the fibre of the orientation local system over `b`
goes to `f o` times the fibre class of the point class of `1` carried to `E_b` by `e`. -/
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (f : (signLocalSystem F E K hι).obj (FundamentalGroupoid.mk b)) :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).inv
        (LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b f) =
      signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ω) f •
        TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F)
            (complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K))) := by
  rw [thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀_eq_smul hι ω
      ((e.mapOrientation ι hb).symm ω),
    orientedFiberGenerator_of_mapOrientation_eq ω hι e hb (Equiv.apply_symm_apply _ _)]

/-- **The twisted Thom isomorphism on a fibre class.** Let `e` be a linear trivialization whose
base set contains `b`, and `o` the orientation of `E_b` that `e` reads as the model orientation
`ω`. The fibre class of the point class of `1` carried to `E_b` by `e` goes to the class of
the function on the orientations of `E_b` equal to `1` at `o`. -/
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of K K) (finrank ℝ F)
          (TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv
            (ModuleCat.of K K) (finrank ℝ F)
            (complZeroPairPointHom (ModuleCat.of K K) F (finrank ℝ F) rfl (1 : K)))) =
      LocalCoefficientSystem.ιTwistedHomology₀.{w, w, w} (signLocalSystem F E K hι) b
        ((signLocalSystemFiberEquiv hι ((e.mapOrientation ι hb).symm ω)).symm 1) := by
  rw [← orientedFiberGenerator_of_mapOrientation_eq ω hι e hb (Equiv.apply_symm_apply _ _),
    thomPairSingularHomologyFinrankIsoTwistedHomology_hom_apply_orientedFiberGenerator]

/-- Reversing the model orientation `ω` negates the inverse of the twisted Thom isomorphism. -/
@[simp]
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_neg_inv :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι (-ω)).inv =
      -(thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).inv := by
  refine LocalCoefficientSystem.twistedHomology₀_hom_ext (signLocalSystem F E K hι) fun b ↦ ?_
  ext f
  simp only [Preadditive.comp_neg, ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀_eq_smul hι (-ω)
      (modelFiberOrientation ω b) f,
    thomPairSingularHomologyFinrankIsoTwistedHomology_inv_ιTwistedHomology₀_eq_smul hι ω
      (modelFiberOrientation ω b) f,
    orientedFiberGenerator_neg_left ω hι, map_neg, smul_neg]

/-- Reversing the model orientation `ω` negates the twisted Thom isomorphism. -/
@[simp]
theorem thomPairSingularHomologyFinrankIsoTwistedHomology_neg_hom :
    (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι (-ω)).hom =
      -(thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι ω).hom := by
  rw [← cancel_mono (thomPairSingularHomologyFinrankIsoTwistedHomology K F E hι (-ω)).inv,
    Iso.hom_inv_id, thomPairSingularHomologyFinrankIsoTwistedHomology_neg_inv,
    Preadditive.neg_comp_neg, Iso.hom_inv_id]

end Twisted

end TauCeti
