/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel
import Mathlib.Order.SuccPred.IntervalSucc
import TauCeti.Geometry.Manifold.Morse.Deformation.Cofibration
import TauCeti.Geometry.Manifold.Morse.Exhaustion
import TauCeti.Logic.Equiv.Sum
import TauCeti.Topology.Category.TopCat.Normal
import TauCeti.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.CWComplex.Classical.SequentialColimit
import TauCeti.Topology.Homotopy.Extension.Tower

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
each lies in exactly one band `(a k, a (k + 1)]`. It is Hausdorff, indeed normal, because each
stage is compact (`TauCeti.TopCat.normalSpace_of_isColimit`). Inside `X` the stages are linked by
closed cofibrations, since each is a subcomplex of the next, and so are the regular sublevels of
`M`, by collars of the regular levels
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`). The models of
the stages commute strictly with the inclusions, so they glue to a map `X → M` which is a homotopy
equivalence on every stage, hence a homotopy equivalence
(`TauCeti.exists_homotopyEquiv_of_isCoherentWith`).

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
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`: **the CW model of a proper Morse function.** A
  manifold carrying a proper Morse function bounded below is homotopy equivalent to a Hausdorff
  CW complex whose `λ`-cells correspond to the critical points of index `λ`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof.
-/

public section

noncomputable section

open Set Filter Topology Topology.RelCWComplex CategoryTheory Limits
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

/-- A finite CW model of the sublevel `{f ≤ a}`. -/
private structure SublevelCWModel {M : Type u} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) where
  /-- The model. -/
  W : Type u
  [topologicalSpace : TopologicalSpace W]
  [t2Space : T2Space W]
  [cwComplex : CWComplex (univ : Set W)]
  [finite : RelCWComplex.Finite (univ : Set W)]
  /-- The homotopy equivalence of the model with the sublevel. -/
  h : W ≃ₕ {x | f x ≤ a}

attribute [instance] SublevelCWModel.topologicalSpace SublevelCWModel.t2Space
  SublevelCWModel.cwComplex SublevelCWModel.finite

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- The sequence of models defined recursively from a first model and a rule extending each model
to the next sublevel. -/
private def sublevelCWModelSeq {M : Type u} [TopologicalSpace M] {f : M → ℝ} {a : ℕ → ℝ}
    (S₀ : SublevelCWModel f (a 0))
    (S' : ∀ k, SublevelCWModel f (a k) → SublevelCWModel f (a (k + 1))) :
    ∀ k, SublevelCWModel f (a k)
  | 0 => S₀
  | k + 1 => S' k (sublevelCWModelSeq S₀ S' k)

/-- Across a compact band between regular values, a finite CW model of the lower sublevel extends
to one of the upper sublevel, containing it as a subcomplex, with one new `m`-cell for each
critical point of index `m` in the band. -/
private theorem IsMorse.exists_sublevelCWModel_extension (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) (S : SublevelCWModel f a) :
    ∃ (S' : SublevelCWModel f b) (ι : C(S.W, S'.W)), IsClosedEmbedding ι ∧
      (∀ w, (S'.h (ι w) : M) = S.h w) ∧
      ∃ e : ∀ m, cell (univ : Set S'.W) m ≃ cell (univ : Set S.W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', _, hι, -, hh, e, he⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb S.W S.h
  exact ⟨⟨W', h'⟩, ι, hι, hh, e, he⟩

/-- The critical points of index `m` are the disjoint union, over `k`, of those with value in
`(a k, a (k + 1)]`, when `a` increases to infinity from below all values of `f`. -/
private def sigmaCriticalPointsIocEquiv {a : ℕ → ℝ} (hmono : StrictMono a)
    (htop : Tendsto a atTop atTop) (ha0 : ∀ x, a 0 < f x) (m : ℕ) :
    (Σ k, ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m})
      ≃ ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
  Equiv.ofBijective (fun p ↦ ⟨p.2.1, p.2.2.1.1, p.2.2.2⟩) <| by
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

/-- The tower of finite CW models of the regular sublevels of a proper Morse function bounded
below: regular values `a 0 < a 1 < ⋯` tending to infinity, with `a 0` below every value of `f`, and
finite CW models `S k` of the sublevels `M_{a k}`, each a subcomplex of the next along a closed
embedding commuting with the models, with one new `m`-cell for each critical point of index `m`
with value in `(a k, a (k + 1)]`. The inclusions of the sublevels are closed cofibrations. -/
private theorem IsMorse.exists_sublevelCWModel_tower (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (a : ℕ → ℝ) (S : ∀ k, SublevelCWModel f (a k)) (ι : ∀ k, C((S k).W, (S (k + 1)).W))
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
  choose S' ι hι hh e he using fun k (S : SublevelCWModel f (a k)) ↦
    hf.exists_sublevelCWModel_extension (hmono k.lt_succ_self).le
      (hp.isCompact_preimage isCompact_Icc) (hreg k) (hreg (k + 1)) S
  -- The models start from the empty one, since the sublevel `M_{a 0}` is empty.
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (not_le.2 (ha0 x)) x.2⟩
  let S := sublevelCWModelSeq { W := PEmpty.{u + 1}, h := Homeomorph.empty.toHomotopyEquiv } S'
  -- The inclusions of the regular sublevels are closed cofibrations, by collars of the levels.
  refine ⟨a, S, fun k ↦ ι k (S k), fun k ↦ e k (S k), hmono, htop, hreg, ha0, fun k ↦ ?_,
    fun k ↦ hι k (S k), fun k ↦ hh k (S k), fun k ↦ he k (S k)⟩
  rw [← range_sublevelInclusion f (hmono k.lt_succ_self).le]
  exact hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
    hf.contMDiff (hmono k.lt_succ_self) (hp.isCompact_preimage isCompact_Icc) (hreg k)
    (hmono k.lt_succ_self).le

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
  have (k : ℕ) : T2Space (F.obj k) := (S k).t2Space
  let ιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) : cell (univ : Set (S (k + 1)).W) m :=
    (e k m).symm (.inl j)
  have hιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) :
      ⇑(map m (ιc k m j)) = F.map (homOfLE k.le_succ) ∘ map m j := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact funext (he k m j)
  let c := colimit.cocone F
  have hc : IsColimit c := colimit.isColimit F
  let := cwComplexOfIsColimit hF hιc hc
  -- `X` is `T4`, as a sequential colimit of compact Hausdorff spaces along closed embeddings.
  have : ∀ k, CompactSpace (F.obj k) := fun k ↦
    isCompact_univ_iff.1 (CWComplex.isCompact_of_finite (C := (univ : Set (S k).W)))
  have := TopCat.t4Space_of_isColimit hF hc
  -- The sublevels of `M` are a tower of closed cofibrations exhausting `M` with the coherent
  -- topology, and the models commute with their inclusions.
  obtain ⟨H, hH⟩ := exists_homotopyEquiv_of_isColimit_cwComplex hF hιc hc
    ((sublevel_mono f).comp hmono.monotone) (iUnion_sublevel_eq_univ_of_tendsto f htop)
    (isCoherentWith_range_sublevel_of_tendsto hf.contMDiff.continuous htop) hBH
    (fun k ↦ (S k).h) fun k w ↦ by
      rw [Functor.ofSequence_map_homOfLE_succ]
      exact hh k w
  -- The cells of `X` are the cells of the first, empty, stage, and the new cells of the later
  -- stages, which are the critical points in the bands `(a k, a (k + 1)]`.
  have hempty (m : ℕ) : IsEmpty (cell (univ : Set (F.obj 0)) m) :=
    ⟨fun j ↦ (not_le.2 (ha0 _)) ((S 0).h (map m j 0)).2⟩
  let eX (m : ℕ) := (cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <|
    (Equiv.emptySum _ _).trans <|
      (Equiv.sigmaCongrRight fun k ↦ (e k m).complRangeSymmInl).trans
        (sigmaCriticalPointsIocEquiv hmono htop ha0 m)
  refine ⟨a, hmono, htop, hreg, c.pt, _, inferInstance, ‹_›, H, eX,
    cwComplexOfIsColimitSubcomplex hF hιc hc, fun k m j ↦ ?_,
    fun L hL ↦ exists_subset_cwComplexOfIsColimitSubcomplex_of_isCompact hF hιc hc hL, fun k ↦ ?_⟩
  · -- A new cell of the stage `k' + 1` belongs to the stage `k` exactly when `k' < k`, and its
    -- critical point has value in `(a k', a (k' + 1)]`.
    obtain ⟨s | ⟨k', x⟩, rfl⟩ := (cwComplexOfIsColimitCellEquiv hF hιc hc m).symm.surjective j
    · exact (hempty m).elim s
    have hx := ((e k' m).complRangeSymmInl x).2.1.2
    refine (cwComplexOfIsColimitCellEquiv_symm_inr_mem_I_iff hF hιc hc _).trans ?_
    simp only [eX, Equiv.trans_apply, Equiv.apply_symm_apply]
    refine ⟨fun hk ↦ hx.2.trans (hmono.monotone hk), fun hk ↦ ?_⟩
    exact hmono.lt_iff_lt.1 (hx.1.trans_le hk)
  · -- On the stage `k`, `H` is the model `S k` of `M_{a k}`, read through the closed embedding of
    -- the stage into `X`.
    have hemb := (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc k).isEmbedding
    refine ⟨(Homeomorph.setCongr (coe_cwComplexOfIsColimitSubcomplex hF hιc hc k)).trans
      hemb.toHomeomorph.symm |>.toHomotopyEquiv.trans (S k).h, fun w ↦ ?_⟩
    obtain ⟨w, hw⟩ := w
    obtain ⟨z, rfl⟩ := (coe_cwComplexOfIsColimitSubcomplex hF hιc hc k).subset hw
    rw [hH]
    exact congrArg (fun y ↦ ((S k).h y : M)) (hemb.toHomeomorph_symm_apply z)

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
  obtain ⟨-, -, -, -, X, _, _, _, H, e, -⟩ :=
    hf.exists_cwComplex_homotopyEquiv_subcomplex_sublevel hp hbdd
  exact ⟨X, _, ‹_›, ‹_›, ⟨H.symm⟩, fun m ↦ ⟨e m⟩⟩

end TauCeti
