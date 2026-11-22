/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Geometry.Manifold.Morse.CWModel
import Mathlib.Order.SuccPred.IntervalSucc
import TauCeti.Geometry.Manifold.Morse.Deformation.Cofibration
import TauCeti.Geometry.Manifold.Morse.Exhaustion
import TauCeti.Geometry.Manifold.Morse.Generic.Strong
import TauCeti.Logic.Equiv.Sum
import TauCeti.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.CWComplex.Classical.SequentialColimit
import TauCeti.Topology.Maps.Proper.Basic

/-!
# The CW model of a proper Morse function

Let `f` be a Morse function on a boundaryless manifold `M`, proper and bounded below. Then `M` is
homotopy equivalent to a Hausdorff CW complex with one `λ`-cell for each critical point of `f` of
index `λ` (`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`). When `f` has infinitely many
critical points of some index, the model has infinitely many cells of that dimension; for compact
`M` it is the finite model `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`.

The model is the union of the CW models of an exhaustion of `M` by regular sublevels. Choose
regular values `a 0 < a 1 < ⋯` tending to infinity, with `a 0` below every value of `f`
(`TauCeti.IsMorse.exists_regular_sublevel_exhaustion`). The sublevel `M_{a 0}` is empty, the empty
CW complex. Each band `f⁻¹[a k, a (k + 1)]` is compact, so a CW model `W k ≃ₕ M_{a k}` extends to a
CW model `W (k + 1) ≃ₕ M_{a (k + 1)}` containing `W k` as a subcomplex, with one new `λ`-cell for
each critical point of index `λ` with value in `(a k, a (k + 1)]`
(`TauCeti.IsMorse.exists_cwComplex_extension_homotopyEquiv_sublevel`). Every stage is a finite CW
complex, since a compact band holds finitely many critical points
(`TauCeti.IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel`).

The colimit `X` of the stages `W k` is a CW complex whose cells are the new cells of all the stages
(`TauCeti.cwComplexOfIsColimit`), so its `λ`-cells correspond to the critical points of index `λ`:
each lies in exactly one band `(a k, a (k + 1)]`. It is Hausdorff because every stage is Hausdorff
(`TauCeti.t2Space_of_isColimit_cwComplex`). Inside `X` the stages are linked by
closed cofibrations, since each is a subcomplex of the next, and so are the regular sublevels of
`M`, by collars of the regular levels
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`). The models of
the stages commute strictly with the inclusions, so they glue to a homotopy equivalence `X ≃ₕ M`
compatible with the stage subcomplexes
(`TauCeti.exists_homotopyEquiv_cwComplexOfIsColimitSubcomplex`).

The model keeps track of the sublevels
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_subcomplex_sublevel`). Each stage `W k` is a
subcomplex of `X` (`TauCeti.cwComplexOfIsColimitSubcomplex`), whose cells are those labelled by the
critical points in `M_{a k}`; the homotopy equivalence `X ≃ₕ M` restricts on it to a homotopy
equivalence `W k ≃ₕ M_{a k}`; and every compact subset of `X`, for instance the image of a sphere
or of a homotopy, lies in a single stage.

## Main results

* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_subcomplex_sublevel`: the CW model of a proper
  Morse function bounded below, with subcomplexes modelling an exhaustion of `M` by regular
  sublevels, compatibly with the homotopy equivalence.
* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv`: **the sublevel-compatible CW
  exhaustion of a proper Morse function.** A manifold carrying a proper Morse function bounded below
  admits a regular exhaustion `a 0 < a 1 < ⋯` and a Hausdorff CW homotopy model `X ≃ₕ M` exhausted
  by an increasing sequence of finite CW subcomplexes `W k` restricting `X ≃ₕ M` to stage homotopy
  equivalences `W k ≃ₕ {f ≤ a k}` (with homotopy inverse mapping `{f ≤ a k}` into `W k`), whose
  `λ`-cells globally and at each stage correspond to the critical points of index `λ`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`: **the CW model of a proper Morse function.** A
  manifold carrying a proper Morse function bounded below is homotopy equivalent to a Hausdorff
  CW complex whose `λ`-cells correspond to the critical points of index `λ`.
* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`: when every critical
  point of `f` has Morse index at most `d`, the CW homotopy model (and its sublevel-compatible
  subcomplex exhaustion) is finite-dimensional and has no cells in dimensions strictly above `d`.
* `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv_of_isProperMap` and
  `TauCeti.IsMorse.finiteCWType_of_isProperMap`: when `f` has finitely many critical points, the
  CW model is finite and the manifold has finite CW type.
* `TauCeti.IsMorse.cwType`, `TauCeti.CWType.of_isManifold`, and
  `TauCeti.CWType.of_isManifold_of_isProperMap`: a manifold carrying a proper bounded-below Morse
  function, any sigma-compact finite-dimensional smooth boundaryless Hausdorff manifold, or any
  smooth boundaryless Hausdorff manifold admitting a proper map to a weakly locally compact
  sigma-compact space has CW type.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5, its proof, and §6, Corollary 6.7.
* J. Milnor, *On spaces having the homotopy type of a CW-complex*, Transactions of the American
  Mathematical Society 90 (1959), 272–280, Corollary 1.
-/

public section

noncomputable section

open Set Filter Topology Topology.RelCWComplex CategoryTheory Limits
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

/-- A finite CW model of the sublevel `{f ≤ a}`, keeping track of its cell bijection with the
critical points in `{f ≤ a}`. -/
private structure SublevelCWModel {E H : Type*} {M : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M]
    [ChartedSpace H M] (f : M → ℝ) (a : ℝ) where
  /-- The model. -/
  W : Type u
  [topologicalSpace : TopologicalSpace W]
  [t2Space : T2Space W]
  [cwComplex : CWComplex (univ : Set W)]
  [finite : RelCWComplex.Finite (univ : Set W)]
  /-- The homotopy equivalence of the model with the sublevel. -/
  h : W ≃ₕ {x | f x ≤ a}
  /-- The `m`-cells of the model correspond to the critical points of index `m` in `{f ≤ a}`. -/
  cellEquiv : ∀ m, cell (univ : Set W) m ≃
    ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m}

attribute [instance] SublevelCWModel.topologicalSpace SublevelCWModel.t2Space
  SublevelCWModel.cwComplex SublevelCWModel.finite

/-- The sequence of models defined recursively from a first model and a rule extending each model
to the next sublevel. -/
private def sublevelCWModelSeq {E H : Type*} {M : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {f : M → ℝ} {a : ℕ → ℝ}
    (S₀ : SublevelCWModel I f (a 0))
    (S' : ∀ k, SublevelCWModel I f (a k) → SublevelCWModel I f (a (k + 1))) :
    ∀ k, SublevelCWModel I f (a k)
  | 0 => S₀
  | k + 1 => S' k (sublevelCWModelSeq S₀ S' k)

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

open Classical in
/-- Splitting the critical points of index `m` in `{f ≤ b}` into those in `{f ≤ a}` and those in
`(a, b]`, when `a ≤ b`. -/
private def criticalPointsIicUnionEquiv {a b : ℝ} (hab : a ≤ b) (m : ℕ) :
    ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m} ⊕
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m} ≃
    ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic b | manifoldMorseIndex I f x = m} :=
  (Equiv.Set.union
    (s := {x ∈ criticalPoints I f ∩ f ⁻¹' Iic a | manifoldMorseIndex I f x = m})
    (t := {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m})
    (disjoint_left.2 fun _ hx hx' ↦ (not_lt.2 hx.1.2) hx'.1.2.1)).symm.trans
    (Set.equivOfEq <| by
      ext x
      simp only [mem_union, mem_ofPred_eq, mem_inter_iff, mem_preimage, ← Iic_union_Ioc_eq_Iic hab]
      tauto)

/-- The critical points of index `m` are the disjoint union, over `k`, of those with value in
`(a k, a (k + 1)]`, when `a` increases to infinity from below all values of `f`. -/
private def sigmaCriticalPointsIocEquiv {a : ℕ → ℝ} (hmono : StrictMono a)
    (htop : Tendsto a atTop atTop) (ha0 : ∀ x, a 0 < f x) (m : ℕ) :
    (Σ k, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m})
      ≃ ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
  Equiv.ofBijective (fun p ↦ ⟨p.2.val, p.2.property.1.1, p.2.property.2⟩) <| by
    refine ⟨fun ⟨k, x, hx⟩ ⟨l, y, hy⟩ hxy ↦ ?_, fun ⟨x, hx, hxm⟩ ↦ ?_⟩
    · obtain rfl : x = y := congrArg Subtype.val hxy
      -- The intervals `(a k, a (k + 1)]` are pairwise disjoint.
      obtain rfl : k = l := by
        by_contra hkl
        exact hmono.monotone.pairwise_disjoint_on_Ioc_succ hkl |>.ne_of_mem hx.1.2 hy.1.2 rfl
      rfl
    · -- The intervals `(a k, a (k + 1)]` cover `(a 0, ∞)`.
      have hcover := iUnion_Ioc_map_succ_eq_Ioi (f := a) (fun k ↦ hmono.monotone (Nat.zero_le k))
        (not_bddAbove_iff.2 fun r ↦
          let ⟨k, hk⟩ := (htop.eventually_gt_atTop r).exists
          ⟨a k, mem_range_self k, hk⟩)
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hcover.symm ▸ ha0 x : f x ∈ ⋃ k, Ioc (a k) (a (k + 1)))
      exact ⟨⟨k, x, ⟨hx, hk⟩, hxm⟩, rfl⟩

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] in
/-- Across a compact band between regular values, a finite CW model of the lower sublevel extends
to one of the upper sublevel, containing it as a subcomplex, with one new `m`-cell for each
critical point of index `m` in the band. -/
private theorem IsMorse.exists_sublevelCWModel_extension (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (S : SublevelCWModel I f a) :
    ∃ (S' : SublevelCWModel I f b) (ι : C(S.W, S'.W)), IsClosedEmbedding ι ∧
      (∀ w, (S'.h (ι w) : M) = S.h w) ∧
      ∃ e : ∀ m, cell (univ : Set S'.W) m ≃ cell (univ : Set S.W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', _, hι, -, hh, e, he⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb S.W S.h
  exact ⟨⟨W', h', fun m ↦ (e m).trans ((Equiv.sumCongr (S.cellEquiv m) (.refl _)).trans
    (criticalPointsIicUnionEquiv hab m))⟩, ι, hι, hh, e, he⟩

/-- The tower of finite CW models of the regular sublevels of a proper Morse function bounded
below: regular values `a 0 < a 1 < ⋯` tending to infinity, with `a 0` below every value of `f`, and
finite CW models `S k` of the sublevels `M_{a k}`, each a subcomplex of the next along a closed
embedding commuting with the models, with one new `m`-cell for each critical point of index `m`
with value in `(a k, a (k + 1)]`. The inclusions of the sublevels are closed cofibrations. -/
private theorem IsMorse.exists_sublevelCWModel_tower (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (a : ℕ → ℝ) (S : ∀ k, SublevelCWModel I f (a k)) (ι : ∀ k, C((S k).W, (S (k + 1)).W))
      (e : ∀ k m, cell (univ : Set (S (k + 1)).W) m ≃ cell (univ : Set (S k).W) m ⊕
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
        (∀ x, a 0 < f x) ∧
        (∀ k, HasHomotopyExtensionProperty ((↑) ⁻¹' {x | f x ≤ a k} : Set {x | f x ≤ a (k + 1)})) ∧
        (∀ k, IsClosedEmbedding (ι k)) ∧
        (∀ k w, ((S (k + 1)).h (ι k w) : M) = (S k).h w) ∧
        ∀ k m j x, map m ((e k m).symm (.inl j)) x = ι k (map m j x) := by
  obtain ⟨a, K, hmono, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x := by
    by_contra hx
    have hxK : x ∈ K 0 := by rw [hK]; exact not_lt.1 hx
    rw [hK0] at hxK
    exact hxK
  choose S' ι hι hh e he using fun k (S : SublevelCWModel I f (a k)) ↦
    hf.exists_sublevelCWModel_extension (hmono k.lt_succ_self).le
      (hp.isCompact_preimage isCompact_Icc) (hreg k) (hreg (k + 1)) S
  -- The models start from the empty one, since the sublevel `M_{a 0}` is empty.
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (not_le.2 (ha0 x)) x.property⟩
  have hcell0 (m : ℕ) : cell (univ : Set PEmpty.{u + 1}) m ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a 0) | manifoldMorseIndex I f x = m} :=
    have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    have : IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a 0) | manifoldMorseIndex I f x = m} :=
      ⟨fun x ↦ (not_le.2 (ha0 x.val)) x.property.1.2⟩
    Equiv.equivOfIsEmpty _ _
  let S := sublevelCWModelSeq ⟨PEmpty.{u + 1}, Homeomorph.empty.toHomotopyEquiv, hcell0⟩ S'
  -- The inclusions of the regular sublevels are closed cofibrations, by collars of the levels.
  refine ⟨a, S, fun k ↦ ι k (S k), fun k ↦ e k (S k), hmono, htop, hreg, ha0, fun k ↦ ?_,
    fun k ↦ hι k (S k), fun k ↦ hh k (S k), fun k ↦ he k (S k)⟩
  rw [← range_sublevelInclusion f (hmono k.lt_succ_self).le]
  exact hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
    hf.contMDiff (hmono k.lt_succ_self) (hp.isCompact_preimage isCompact_Icc) (hreg k)
    (hmono k.lt_succ_self).le

/-- Finite-dimensional core of the sublevel-compatible CW exhaustion of a proper Morse function,
carrying the global cell labeling, compact-subset containment, and stage-compatible homotopy
equivalences. -/
private theorem IsMorse.exists_cwComplex_subcomplex_witness_of_finiteDimensional (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (W : ℕ → Subcomplex (univ : Set X))
      (h : X ≃ₕ M) (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k})
      (e : ∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ x, a 0 < f x) ∧
      (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : (W k : Set X)), (hW k w : M) = h w) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ k m j, j ∈ (W k).I m ↔ f (e m j) ≤ a k) ∧
      ∀ K : Set X, IsCompact K → ∃ k, K ⊆ W k := by
  -- Outline: take finite CW models `S k` of the regular sublevels `M_{a k}`, each a subcomplex of
  -- the next; take their colimit `X` with its CW structure, whose stages are subcomplexes, and
  -- label its cells; then glue the models to a map `X → M` and compare the two towers of closed
  -- cofibrations.
  obtain ⟨a, S, ι, e, hmono, htop, hreg, ha0, hBH, hι, hh, he⟩ :=
    hf.exists_sublevelCWModel_tower hp hbdd
  -- The tower of models, its colimit `X`, and the cells of each stage among those of the next.
  let F : ℕ ⥤ TopCat.{u} :=
    Functor.ofSequence (X := fun k : ℕ ↦ TopCat.of (S k).W) fun k : ℕ ↦
      (TopCat.ofHom (ι k) : TopCat.of (S k).W ⟶ TopCat.of (S (k + 1)).W)
  have hF (k : ℕ) : IsClosedEmbedding (F.map (homOfLE k.le_succ)) := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hι k
  let (k : ℕ) : CWComplex (univ : Set (F.obj k)) := (S k).cwComplex
  let (k : ℕ) : RelCWComplex.Finite (univ : Set (F.obj k)) := (S k).finite
  have (k : ℕ) : T2Space (F.obj k) := (S k).t2Space
  let ιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) : cell (univ : Set (S (k + 1)).W) m :=
    (e k m).symm (.inl j)
  have hιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) :
      ⇑(map m (ιc k m j)) = F.map (homOfLE k.le_succ) ∘ map m j := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact funext (he k m j)
  -- Glue the stage equivalences on the CW colimit `c.pt` and its stage subcomplexes.
  let c := colimit.cocone F
  have hc : IsColimit c := colimit.isColimit F
  let := cwComplexOfIsColimit hF hιc hc
  have := t2Space_of_isColimit_cwComplex hF hιc hc
  obtain ⟨h, hW, hhW, hsymm⟩ := exists_homotopyEquiv_cwComplexOfIsColimitSubcomplex hF hιc hc
    (A := fun k ↦ {x | f x ≤ a k}) ((sublevel_mono f).comp hmono.monotone)
    (iUnion_sublevel_eq_univ_of_tendsto f htop)
    (isCoherentWith_range_sublevel_of_tendsto hf.contMDiff.continuous htop) hBH (fun k ↦ (S k).h)
    fun k w ↦ by rw [Functor.ofSequence_map_homOfLE_succ]; exact hh k w
  -- The cells of `X` are the new cells of all stages, which are the critical points in the bands
  -- `(a k, a (k + 1)]`.
  have : IsEmpty (F.obj 0) := ⟨fun w ↦ (not_le.2 (ha0 _)) ((S 0).h w).property⟩
  have hempty (m : ℕ) : IsEmpty (cell (univ : Set (F.obj 0)) m) :=
    ⟨fun j ↦ isEmptyElim (map m j 0)⟩
  let eX (m : ℕ) := (cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <|
    (Equiv.emptySum _ _).trans <|
      (Equiv.sigmaCongrRight fun k ↦ (e k m).complRangeSymmInl).trans
        (sigmaCriticalPointsIocEquiv hmono htop ha0 m)
  refine ⟨a, c.pt, c.pt.str, inferInstance, ‹_›, cwComplexOfIsColimitSubcomplex hF hιc hc,
    h, hW, eX, hmono, htop, ha0, hreg, monotone_cwComplexOfIsColimitSubcomplex hF hιc hc,
    (coe_cwComplexOfIsColimitSubcomplex hF hιc hc 0).trans (range_eq_empty _),
    iUnion_coe_cwComplexOfIsColimitSubcomplex hF hιc hc,
    fun k ↦ finite_cwComplexOfIsColimitSubcomplex hF hιc hc k, hhW, hsymm, fun k m j ↦ ?_,
    fun L hL ↦ exists_subset_cwComplexOfIsColimitSubcomplex_of_isCompact hF hιc hc hL⟩
  -- A new cell of the stage `k' + 1` belongs to the stage `k` exactly when `k' < k`, and its
  -- critical point has value in `(a k', a (k' + 1)]`.
  obtain ⟨s | ⟨k', x⟩, rfl⟩ := (cwComplexOfIsColimitCellEquiv hF hιc hc m).symm.surjective j
  · exact (hempty m).elim s
  have hx := ((e k' m).complRangeSymmInl x).property.1.2
  refine (cwComplexOfIsColimitCellEquiv_symm_inr_mem_I_iff hF hιc hc _).trans ?_
  simp only [eX, Equiv.trans_apply, Equiv.apply_symm_apply]
  refine ⟨fun hk ↦ hx.2.trans (hmono.monotone hk), fun hk ↦ ?_⟩
  exact hmono.lt_iff_lt.1 (hx.1.trans_le hk)

omit [FiniteDimensional ℝ E] in
/-- Shared witness for `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_subcomplex_sublevel` and
`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv`, handling the empty-manifold and
finite-dimensionality reduction once. -/
private theorem IsMorse.exists_cwComplex_subcomplex_witness (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (W : ℕ → Subcomplex (univ : Set X))
      (h : X ≃ₕ M) (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k})
      (e : ∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ x, a 0 < f x) ∧
      (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : (W k : Set X)), (hW k w : M) = h w) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ k m j, j ∈ (W k).I m ↔ f (e m j) ≤ a k) ∧
      ∀ K : Set X, IsCompact K → ∃ k, K ⊆ W k := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · let W : ℕ → Subcomplex (univ : Set PEmpty.{u + 1}) :=
      fun _ ↦ ⟨∅, fun _ ↦ ∅, isClosed_empty, by simp⟩
    have hcellEmpty (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) :=
      ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    have hWempty (k m : ℕ) : IsEmpty (cell (W k : Set PEmpty.{u + 1}) m) :=
      ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    have (k : ℕ) : IsEmpty {x : M | f x ≤ (k : ℝ)} := ⟨fun x ↦ hM.elim x.val⟩
    let e (m : ℕ) : cell (univ : Set PEmpty.{u + 1}) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
      have : IsEmpty ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
        ⟨fun x ↦ hM.elim x.val⟩
      Equiv.equivOfIsEmpty _ _
    exact ⟨Nat.cast, PEmpty.{u + 1}, inferInstance, inferInstance, inferInstance, W,
      Homeomorph.empty.toHomotopyEquiv, fun _ ↦ Homeomorph.empty.toHomotopyEquiv, e,
      Nat.strictMono_cast, tendsto_natCast_atTop_atTop, isEmptyElim,
      fun _ ↦ isRegularValue_of_notMem_range fun ⟨x, _⟩ ↦ hM.elim x,
      monotone_const, rfl, eq_univ_of_forall isEmptyElim,
      fun k ↦ RelCWComplex.finite_of_finite_cells
        (have : IsEmpty (Σ n, cell (W k : Set PEmpty.{u + 1}) n) :=
          ⟨fun ⟨n, j⟩ ↦ (hWempty k n).elim j⟩
        inferInstance),
      fun _ x ↦ PEmpty.elim x.val, fun _ x ↦ hM.elim x,
      fun _ m j ↦ (hcellEmpty m).elim j, fun _ _ ↦ ⟨0, fun x _ ↦ PEmpty.elim x⟩⟩
  · obtain ⟨a, K, -, htop, hreg, hK, -, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
    obtain ⟨n, hn⟩ := (htop.eventually_ge_atTop (f x₀)).exists
    have : Nonempty {x | f x ≤ a n} := ⟨⟨x₀, hn⟩⟩
    have hcomp : IsCompact (f ⁻¹' Iic (a n)) := hK n ▸ K.isCompact n
    have : FiniteDimensional ℝ E := finiteDimensional_of_isCompact_sublevel (I := I)
      hf.contMDiff.continuous hcomp (hreg n)
    exact hf.exists_cwComplex_subcomplex_witness_of_finiteDimensional hp hbdd

omit [FiniteDimensional ℝ E] in
/-- **The CW model of a proper Morse function, with its sublevels** (Milnor, *Morse Theory*,
Theorem 3.5 and its proof). Let `f` be a Morse function on a boundaryless manifold `M`, proper and
bounded below. There are regular values `a 0 < a 1 < ⋯` of `f` tending to infinity, a Hausdorff CW
complex `X` whose `m`-cells are labelled by the critical points of `f` of index `m`, a homotopy
equivalence `H : X ≃ₕ M`, and subcomplexes `W k` of `X` such that:

* the cells of `W k` are those labelled by the critical points in the sublevel `{f ≤ a k}`;
* every compact subset of `X` lies in some `W k`;
* `H` restricts on `W k` to a homotopy equivalence `W k ≃ₕ {f ≤ a k}`.

So the model is the increasing union of CW models of the regular sublevels, with the comparison
maps commuting strictly with the inclusions. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_subcomplex_sublevel (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    ∃ a : ℕ → ℝ, StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
        (H : X ≃ₕ M)
        (e : ∀ m, cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})
        (W : ℕ → Subcomplex (univ : Set X)),
        (∀ k m j, j ∈ (W k).I m ↔ f (e m j) ≤ a k) ∧
        (∀ K : Set X, IsCompact K → ∃ k, K ⊆ W k) ∧
        ∀ k, ∃ h : ↥(W k : Set X) ≃ₕ {x | f x ≤ a k}, ∀ w, (h w : M) = H w := by
  obtain ⟨a, X, instTop, instT2, instCW, W, h, hW, e, hmono, htop, -, hreg, -, -, -, -, hhW, -,
      hI, hK⟩ := hf.exists_cwComplex_subcomplex_witness hp hbdd
  exact ⟨a, hmono, htop, hreg, X, instTop, instT2, instCW, h, e, W, hI, hK,
    fun k ↦ ⟨hW k, hhW k⟩⟩

omit [FiniteDimensional ℝ E] in
/-- **The sublevel-compatible CW exhaustion of a proper Morse function** (Milnor, *Morse Theory*,
Theorem 3.5 and its proof). Let `f` be a proper, bounded-below Morse function on a boundaryless
manifold `M`. Then there exist a strictly increasing sequence of regular values `a : ℕ → ℝ` tending
to `+∞` with `a 0 < f x` everywhere, a Hausdorff CW complex `X`, an increasing sequence of finite
CW subcomplexes `W : ℕ → Subcomplex (univ : Set X)` exhausting `X` from `W 0 = ∅`, a homotopy
equivalence `h : X ≃ₕ M`, and stage homotopy equivalences `hW k : W k ≃ₕ {f ≤ a k}` restricted from
`h` whose global homotopy inverse `h.symm` carries `{f ≤ a k}` into `W k`. Moreover, the `m`-cells
of `X` (and of each `W k`) correspond to the critical points of `f` of index `m` (in `{f ≤ a k}`).
-/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (W : ℕ → Subcomplex (univ : Set X))
      (h : X ≃ₕ M) (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ x, a 0 < f x) ∧
      (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : (W k : Set X)), (hW k w : M) = h w) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})) ∧
      ∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a k) | manifoldMorseIndex I f x = m}) := by
  obtain ⟨a, X, instTop, instT2, instCW, W, h, hW, e, hmono, htop, ha0, hreg, hWmono, hW0, hWuniv,
      hWfin, hhW, hsymm, hI, -⟩ := hf.exists_cwComplex_subcomplex_witness hp hbdd
  refine ⟨a, X, instTop, instT2, instCW, W, h, hW, hmono, htop, ha0, hreg, hWmono, hW0, hWuniv,
    hWfin, hhW, hsymm, fun m ↦ ⟨e m⟩, fun k m ↦ ?_⟩
  rw [CWComplex.Subcomplex.cell_def]
  let e' : ↥((W k).I m) ≃
      {y : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} // f y.val ≤ a k} :=
    Equiv.subtypeEquiv (e m) fun j ↦ hI k m j
  exact ⟨e'.trans
    { toFun := fun ⟨⟨x, hx, hxm⟩, hfx⟩ ↦ ⟨x, ⟨hx, hfx⟩, hxm⟩
      invFun := fun ⟨x, ⟨hx, hfx⟩, hxm⟩ ↦ ⟨⟨x, hx, hxm⟩, hfx⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }⟩

omit [FiniteDimensional ℝ E] in
/-- **Index-bounded sublevel-compatible CW exhaustion of a proper Morse function.** If `f` is a
proper, bounded-below Morse function on a boundaryless manifold `M` whose critical points all have
Morse index at most `d`, then the sublevel-compatible CW exhaustion of
`IsMorse.exists_cwComplex_subcomplex_homotopyEquiv` is finite-dimensional and has no cells in
dimensions strictly above `d`, globally or in any stage subcomplex `W k`. -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hidx : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (W : ℕ → Subcomplex (univ : Set X))
      (h : X ≃ₕ M) (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ x, a 0 < f x) ∧
      (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (W 0 : Set X) = ∅ ∧ (⋃ k, (W k : Set X)) = univ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      RelCWComplex.FiniteDimensional (univ : Set X) ∧
      (∀ k (w : (W k : Set X)), (hW k w : M) = h w) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})) ∧
      (∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a k) | manifoldMorseIndex I f x = m})) ∧
      (∀ m, d < m → IsEmpty (cell (univ : Set X) m)) ∧
      ∀ k m, d < m → IsEmpty (cell (W k : Set X) m) := by
  obtain ⟨a, X, instTop, instT2, instCW, W, h, hW, hmono, htop, ha0, hreg, hWmono, hW0, hWuniv,
      hWfin, hhW, hsymm, hcell, hWcell⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  have hempty (m : ℕ) (hm : d < m) : IsEmpty (cell (univ : Set X) m) :=
    (hcell m).some.isEmpty_congr.2 ⟨fun x ↦ ((x.property.2 ▸ hidx x.val x.property.1).trans_lt
        hm).false⟩
  have hWempty (k m : ℕ) (hm : d < m) : IsEmpty (cell (W k : Set X) m) :=
    (hWcell k m).some.isEmpty_congr.2 ⟨fun x ↦ ((x.property.2 ▸ hidx x.val x.property.1.1).trans_lt
        hm).false⟩
  exact ⟨a, X, instTop, instT2, instCW, W, h, hW, hmono, htop, ha0, hreg, hWmono, hW0, hWuniv,
    hWfin, RelCWComplex.finiteDimensional_of_isEmpty_cell_gt (univ : Set X) hempty, hhW, hsymm,
    hcell, hWcell, hempty, hWempty⟩

omit [FiniteDimensional ℝ E] in
/-- **Index-bounded CW model of a proper Morse function.** If `f` is a proper, bounded-below Morse
function on a boundaryless manifold `M` whose critical points all have Morse index at most `d`,
then `M` is homotopy equivalent to a finite-dimensional Hausdorff CW complex `X` whose `m`-cells
correspond to the critical points of `f` of index `m`, with no cells in dimensions strictly above
`d`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hidx : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.FiniteDimensional (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})) ∧
      ∀ m, d < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨_, X, instTop, instT2, instCW, _, h, _, -, -, -, -, -, -, -, -, hfd, -, -, hcell, -,
      hempty, -⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv_of_manifoldMorseIndex_le hp hbdd hidx
  exact ⟨X, instTop, instT2, instCW, hfd, ⟨h.symm⟩, hcell, hempty⟩

omit [FiniteDimensional ℝ E] in
/-- **The CW model of a proper Morse function** (Milnor, *Morse Theory*, Theorem 3.5). Let `f` be
a Morse function on a boundaryless manifold `M`, proper and bounded below. Then `M` is homotopy
equivalent to a Hausdorff CW complex `X` whose `m`-cells correspond to the critical points of `f`
of index `m`, for every `m`. When there are infinitely many critical points of index `m`, `X` has
infinitely many `m`-cells. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨_, X, instTop, instT2, instCW, _, h, _, -, -, -, -, -, -, -, -, -, -, hcell, -⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  exact ⟨X, instTop, instT2, instCW, ⟨h.symm⟩, hcell⟩

omit [FiniteDimensional ℝ E] in
/-- **The finite CW model of a proper Morse function with finitely many critical points.** Let `f`
be a Morse function on a boundaryless manifold `M`, proper, bounded below, and with finitely many
critical points. Then `M` is homotopy equivalent to a finite Hausdorff CW complex `X` whose
`m`-cells correspond to the critical points of `f` of index `m`, for every `m`. -/
theorem IsMorse.exists_finite_cwComplex_homotopyEquiv_of_isProperMap (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) (hfin : (criticalPoints I f).Finite) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      RelCWComplex.Finite (univ : Set X) ∧ Nonempty (M ≃ₕ X) ∧
      ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨X, _, _, _, ⟨h⟩, hcell⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  have := finite_sigma_criticalPoints (I := I) hfin
  exact ⟨X, _, ‹_›, ‹_›, RelCWComplex.finite_of_finite_cells (.of_equiv _
    (Equiv.sigmaCongrRight fun m ↦ (hcell m).some.symm)), ⟨h⟩, hcell⟩

omit [FiniteDimensional ℝ E] in
/-- A boundaryless manifold carrying a proper Morse function bounded below with finitely many
critical points has finite CW type. -/
theorem IsMorse.finiteCWType_of_isProperMap (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (hfin : (criticalPoints I f).Finite) : FiniteCWType M := by
  obtain ⟨X, _, _, _, _, ⟨e⟩, -⟩ :=
    hf.exists_finite_cwComplex_homotopyEquiv_of_isProperMap hp hbdd hfin
  exact (e.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv).finiteCWType

omit [FiniteDimensional ℝ E] in
/-- A boundaryless Hausdorff manifold carrying a proper Morse function bounded below has CW type. -/
theorem IsMorse.cwType (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    CWType M := by
  obtain ⟨X, _, _, _, ⟨h⟩, -⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  exact h.cwType

variable (M I) in
include I in
/-- **Sigma-compact manifolds have CW type** (Milnor, *Morse Theory*, Theorem 3.5, the remark
following it, and §6, Corollary 6.7; Milnor 1959, Corollary 1). Every sigma-compact boundaryless
Hausdorff smooth manifold with a finite-dimensional model carries a proper bounded-below Morse
function (`TauCeti.exists_isMorse_isProperMap_bddBelow`) and is therefore homotopy equivalent to a
CW complex. -/
theorem CWType.of_isManifold [SigmaCompactSpace M] : CWType M :=
  let ⟨_, hgm, hgp, hgbdd⟩ := exists_isMorse_isProperMap_bddBelow (I := I) (M := M)
  hgm.cwType hgp hgbdd

omit [FiniteDimensional ℝ E] in
variable (I) in
include I in
/-- A boundaryless Hausdorff smooth manifold admitting a proper map to a weakly locally compact
sigma-compact space has CW type, without a separate finite-dimensionality assumption on the model
space. -/
theorem CWType.of_isManifold_of_isProperMap {Y : Type*} [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace Y] [SigmaCompactSpace Y] {g : M → Y} (hg : IsProperMap g) :
    CWType M := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact (Homeomorph.empty : M ≃ₜ PEmpty.{u + 1}).cwType
  have := hg.weaklyLocallyCompactSpace
  have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
  have := hg.sigmaCompactSpace
  exact CWType.of_isManifold M I

end TauCeti
