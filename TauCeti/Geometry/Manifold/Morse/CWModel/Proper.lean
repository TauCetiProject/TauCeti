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

## Main results

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
  -- Outline: build finite CW models `S k` of the regular sublevels `M_{a k}`, each a subcomplex of
  -- the next; take their colimit `X` with its CW structure and count its cells; then glue the
  -- models to a map `X → M` and compare the two towers of closed cofibrations.
  obtain ⟨a, K, hmono, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x := by
    by_contra hx
    have hxK : x ∈ K 0 := by rw [hK]; exact not_lt.1 hx
    rw [hK0] at hxK
    exact hxK
  have hcompact (k : ℕ) : IsCompact (f ⁻¹' Icc (a k) (a (k + 1))) :=
    hp.isCompact_preimage isCompact_Icc
  choose S' ι hι hh e he using fun k (S : SublevelCWModel f (a k)) ↦
    hf.exists_sublevelCWModel_extension (hmono k.lt_succ_self).le (hcompact k) (hreg k)
      (hreg (k + 1)) S
  -- The finite CW models of the sublevels `M_{a k}`, starting from the empty one.
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (not_le.2 (ha0 x)) x.2⟩
  let S := sublevelCWModelSeq { W := PEmpty.{u + 1}, h := Homeomorph.empty.toHomotopyEquiv } S'
  -- The tower of models, its colimit `X`, and the cells of each stage among those of the next.
  let F : ℕ ⥤ TopCat.{u} :=
    Functor.ofSequence (X := fun k : ℕ ↦ TopCat.of (S k).W) fun k : ℕ ↦
      (TopCat.ofHom (ι k (S k)) : TopCat.of (S k).W ⟶ TopCat.of (S (k + 1)).W)
  have hF (k : ℕ) : IsClosedEmbedding (F.map (homOfLE k.le_succ)) := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hι k (S k)
  let (k : ℕ) : CWComplex (univ : Set (F.obj k)) := (S k).cwComplex
  have (k : ℕ) : T2Space (F.obj k) := (S k).t2Space
  let ιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) : cell (univ : Set (S (k + 1)).W) m :=
    (e k (S k) m).symm (.inl j)
  have hιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) :
      ⇑(map m (ιc k m j)) = F.map (homOfLE k.le_succ) ∘ map m j := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact funext (he k (S k) m j)
  let c := colimit.cocone F
  have hc : IsColimit c := colimit.isColimit F
  let := cwComplexOfIsColimit hF hιc hc
  -- `X` is `T4`, as a sequential colimit of compact Hausdorff spaces along closed embeddings.
  have : ∀ k, CompactSpace (F.obj k) := fun k ↦
    isCompact_univ_iff.1 (CWComplex.isCompact_of_finite (C := (univ : Set (S k).W)))
  have := TopCat.t4Space_of_isColimit hF hc
  refine ⟨c.pt, _, inferInstance, ‹_›, ?_, fun m ↦ ⟨?_⟩⟩
  swap
  · -- The cells of `X` are the cells of the first, empty, stage, and the new cells of the later
    -- stages, which are the critical points in the bands `(a k, a (k + 1)]`.
    have : IsEmpty (cell (univ : Set (F.obj 0)) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    exact (cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <| (Equiv.emptySum _ _).trans <|
      (Equiv.sigmaCongrRight fun k ↦ (e k (S k) m).complRangeSymmInl).trans
        (sigmaCriticalPointsIocEquiv hmono htop ha0 m)
  -- The models glue to a map `X → M`, a homotopy equivalence on every stage.
  let φ : Cocone F :=
    { pt := TopCat.of M
      ι := NatTrans.ofSequence
        (fun k ↦ TopCat.ofHom ((ContinuousMap.subtypeVal _).comp (S k).h.toFun)) fun k ↦ by
          ext w
          rw [Functor.ofSequence_map_homOfLE_succ]
          exact hh k (S k) w }
  let g : C(c.pt, M) := (hc.desc φ).hom
  have hg (k : ℕ) (w : F.obj k) : g (c.ι.app k w) = (S k).h w :=
    ConcreteCategory.congr_hom (hc.fac φ k) w
  have hemb := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc
  let eA (k : ℕ) : (range (c.ι.app k) : Set c.pt) ≃ₕ {x | f x ≤ a k} :=
    (hemb k).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.trans (S k).h
  have heA (k : ℕ) (x : (range (c.ι.app k) : Set c.pt)) : (eA k x : M) = g x := by
    obtain ⟨_, w, rfl⟩ := x
    -- `eA k` inverts `c.ι.app k` on its range and then applies the model `(S k).h`.
    exact (congrArg (fun y ↦ ((S k).h y : M))
      ((hemb k).isEmbedding.toHomeomorph_symm_apply w)).trans (hg k w).symm
  -- The stages of `X` and the sublevels of `M` are towers of closed cofibrations, exhausting
  -- `X` and `M` with the coherent topology.
  have hBH (k : ℕ) : HasHomotopyExtensionProperty
      ((↑) ⁻¹' {x | f x ≤ a k} : Set {x | f x ≤ a (k + 1)}) := by
    rw [← range_sublevelInclusion f (hmono k.lt_succ_self).le]
    exact hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
      hf.contMDiff (hmono k.lt_succ_self) (hcompact k) (hreg k) (hmono k.lt_succ_self).le
  obtain ⟨h, -, -⟩ := exists_homotopyEquiv_of_isCoherentWith (TopCat.monotone_range_ι c)
    ((sublevel_mono f).comp hmono.monotone) (TopCat.iUnion_range_ι_of_isColimit hc)
    (iUnion_sublevel_eq_univ_of_tendsto f htop) (TopCat.isCoherentWith_range_ι_of_isColimit hc)
    (isCoherentWith_range_sublevel_of_tendsto hf.contMDiff.continuous htop)
    (hasHomotopyExtensionProperty_preimage_range_ι hF hιc hc) hBH g eA heA
  exact ⟨h.symm⟩

end TauCeti
