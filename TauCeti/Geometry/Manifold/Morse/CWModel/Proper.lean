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

* `IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel_of_manifoldMorseIndex_le`:
  extending a dimension-bounded finite CW model across a compact regular band whose critical points
  have index at most `d` preserves the cell-dimension bound `d`.
* `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isCompact`,
  `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv_sublevel_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.finiteCWType_sublevel`: every compact regular sublevel of a Morse function on a
  possibly noncompact manifold has a finite CW model (of dimension at most `d` when its critical
  indices are at most `d`), hence finite CW type.
* `TauCeti.IsMorse.exists_cwComplex_sublevel_homotopyEquiv`: **the CW model of a proper Morse
  function with compatible sublevel models.** A manifold carrying a proper Morse function bounded
  below is homotopy equivalent to a Hausdorff CW complex `X` whose `λ`-cells correspond to the
  critical points of `f` of index `λ`, realized as the union of closed embeddings of finite CW
  models of an increasing sequence of regular sublevels commuting with the global homotopy
  equivalence.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv` and
  `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`: the global CW homotopy
  model of a proper bounded-below Morse function, and its dimension bound `d` when all critical
  indices are at most `d`.
* `TauCeti.IsMorse.cwType`: a manifold carrying a proper bounded-below Morse function has CW type.

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

/-- **Extending dimension-bounded finite CW models of sublevels.** Let `f` be a Morse function and
`a ≤ b` regular values with compact band `f⁻¹[a, b]` in which every critical point with value in
`(a, b]` has Morse index at most `d`. Any finite CW model `h : W ≃ₕ {f ≤ a}` with no cells above
dimension `d` extends along a closed cofibration `ι : C(W, W')` to a finite CW model
`h' : W' ≃ₕ {f ≤ b}` whose new `m`-cells correspond to the critical points of index `m` in `(a, b]`
and which likewise has no cells above dimension `d`. -/
theorem IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b, manifoldMorseIndex I f x ≤ d)
    (W : Type u) [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)]
    [RelCWComplex.Finite (univ : Set W)] (h : W ≃ₕ {x | f x ≤ a})
    (hW : ∀ k, d < k → IsEmpty (cell (univ : Set W) k)) :
    ∃ (W' : Type u) (_ : TopologicalSpace W') (_ : T2Space W') (_ : CWComplex (univ : Set W'))
      (ι : C(W, W')) (h' : W' ≃ₕ {x | f x ≤ b}),
      RelCWComplex.Finite (univ : Set W') ∧ IsClosedEmbedding ι ∧
      HasHomotopyExtensionProperty (range ι) ∧ (∀ w, (h' (ι w) : M) = h w) ∧
      (∀ k, d < k → IsEmpty (cell (univ : Set W') k)) ∧
      ∃ e : ∀ m, cell (univ : Set W') m ≃ cell (univ : Set W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', hfin, hι, hA, hh, e, he⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb W h
  refine ⟨W', _, ‹_›, ‹_›, ι, h', hfin, hι, hA, hh, fun k hk ↦ ?_, e, he⟩
  have : IsEmpty (cell (univ : Set W) k) := hW k hk
  have : IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = k} :=
    ⟨fun ⟨x, hx, hxk⟩ ↦ ((hd x hx).trans_lt (hxk ▸ hk)).false⟩
  exact (e k).isEmpty

omit [FiniteDimensional ℝ E] in
/-- **The finite CW model of a compact regular sublevel.** Let `f` be a Morse function on a
possibly noncompact boundaryless manifold `M` and `b` a regular value with compact sublevel
`{f ≤ b}`. Then `{f ≤ b}` is homotopy equivalent to a finite Hausdorff CW complex whose `m`-cells
correspond to the critical points of `f` in `{f ≤ b}` of index `m`. -/
theorem IsMorse.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isCompact (hf : IsMorse I f)
    {b : ℝ} (hcompact : IsCompact {x | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ {x | f x ≤ b} | manifoldMorseIndex I f x = m}) := by
  rcases isEmpty_or_nonempty {x | f x ≤ b} with hEmpty | _
  · refine ⟨PEmpty.{u + 1}, _, inferInstance, inferInstance, inferInstance,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun m ↦ ⟨?_⟩⟩
    have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    have : IsEmpty ↥{x ∈ criticalPoints I f ∩ {x | f x ≤ b} | manifoldMorseIndex I f x = m} :=
      ⟨fun ⟨x, hx, _⟩ ↦ hEmpty.false ⟨x, hx.2⟩⟩
    exact Equiv.equivOfIsEmpty _ _
  have := finiteDimensional_of_isCompact_sublevel hf.contMDiff.continuous hcompact hb
  obtain ⟨a, hab, ha⟩ := exists_le_forall_lt_of_isCompact_sublevel hcompact
    hf.contMDiff.continuous.continuousOn
  have : IsEmpty {x | f x ≤ a} := ⟨fun x ↦ (ha x.1).not_ge x.2⟩
  have hband : IsCompact (f ⁻¹' Icc a b) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous) fun _ hx ↦ hx.2
  have hareg : IsRegularValue I 𝓘(ℝ) f a :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨p, _, hp⟩ ↦ (ha p).ne' hp
  obtain ⟨W, _, _, _, -, h', hfin, -, -, -, e, -⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hband hareg hb PEmpty.{u + 1}
      Homeomorph.empty.toHomotopyEquiv
  refine ⟨W, _, ‹_›, ‹_›, hfin, ⟨h'⟩, fun m ↦ ⟨?_⟩⟩
  have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
  refine (e m).trans ((Equiv.emptySum _ _).trans (Set.equivOfEq ?_))
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioc]
  exact ⟨fun ⟨⟨hx, _, hxb⟩, hm⟩ ↦ ⟨⟨hx, hxb⟩, hm⟩,
    fun ⟨⟨hx, hxb⟩, hm⟩ ↦ ⟨⟨hx, ha x, hxb⟩, hm⟩⟩

omit [FiniteDimensional ℝ E] in
/-- **Dimension-bounded finite CW model of a compact regular sublevel.** If `b` is a regular value
of a Morse function `f` with compact sublevel `{f ≤ b}` in which every critical point has index at
most `d`, then `{f ≤ b}` is homotopy equivalent to a finite Hausdorff CW complex whose `m`-cells
correspond to the critical points of `f` in `{f ≤ b}` of index `m` and which has no cells above
dimension `d`. -/
theorem IsMorse.exists_finite_cwComplex_homotopyEquiv_sublevel_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {b : ℝ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ≤ b → manifoldMorseIndex I f x ≤ d) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      (∀ k, d < k → IsEmpty (cell (univ : Set W) k)) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ {x | f x ≤ b} | manifoldMorseIndex I f x = m}) := by
  obtain ⟨W, _, _, _, hfin, ⟨h⟩, hcell⟩ :=
    hf.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isCompact hcompact hb
  refine ⟨W, _, ‹_›, ‹_›, hfin, ⟨h⟩, fun k hk ↦ ?_, hcell⟩
  refine (hcell k).some.isEmpty_congr.2 ⟨fun ⟨x, ⟨hx, hxb⟩, hxk⟩ ↦ ?_⟩
  exact ((hd x hx hxb).trans_lt (hxk ▸ hk)).false

omit [FiniteDimensional ℝ E] in
/-- Every compact regular sublevel of a Morse function on a boundaryless manifold has finite CW
type. -/
theorem IsMorse.finiteCWType_sublevel (hf : IsMorse I f) {b : ℝ}
    (hcompact : IsCompact {x | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    FiniteCWType {x | f x ≤ b} := by
  obtain ⟨W, _, _, _, _, ⟨e⟩, -⟩ :=
    hf.exists_finite_cwComplex_homotopyEquiv_sublevel_of_isCompact hcompact hb
  exact (e.symm.trans (Homeomorph.Set.univ W).symm.toHomotopyEquiv).finiteCWType

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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- At stage `k` of `sublevelCWModelSeq` starting from an empty sublevel, the `m`-cells correspond
to the critical points of `f` in `{f ≤ a k}` of index `m`. -/
private theorem sublevelCWModelSeq_cell_equiv {a : ℕ → ℝ} (hmono : StrictMono a)
    (ha0 : ∀ x, a 0 < f x) (S₀ : SublevelCWModel f (a 0))
    (hS₀ : ∀ m, IsEmpty (cell (univ : Set S₀.W) m))
    (S' : ∀ k, SublevelCWModel f (a k) → SublevelCWModel f (a (k + 1)))
    (e : ∀ k (S : SublevelCWModel f (a k)) (m : ℕ),
      cell (univ : Set (S' k S).W) m ≃ cell (univ : Set S.W) m ⊕
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m})
    (k m : ℕ) :
    Nonempty (cell (univ : Set (sublevelCWModelSeq S₀ S' k).W) m ≃
      ↥{x ∈ criticalPoints I f ∩ {x | f x ≤ a k} | manifoldMorseIndex I f x = m}) := by
  classical
  induction k with
  | zero =>
    have : IsEmpty (cell (univ : Set (sublevelCWModelSeq S₀ S' 0).W) m) := hS₀ m
    have : IsEmpty ↥{x ∈ criticalPoints I f ∩ {x | f x ≤ a 0} | manifoldMorseIndex I f x = m} :=
      ⟨fun ⟨x, hx, _⟩ ↦ (ha0 x).not_ge hx.2⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩
  | succ k ih =>
    obtain ⟨ek⟩ := ih
    have hdisj : Disjoint
        {x ∈ criticalPoints I f ∩ {x | f x ≤ a k} | manifoldMorseIndex I f x = m}
        {x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m} :=
      disjoint_left.2 fun x hx hx' ↦ hx'.1.2.1.not_ge hx.1.2
    refine ⟨(e k (sublevelCWModelSeq S₀ S' k) m).trans ((Equiv.sumCongr ek (.refl _)).trans
      ((Equiv.Set.union hdisj).symm.trans (Set.equivOfEq ?_)))⟩
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioc]
    refine ⟨?_, fun ⟨⟨hx, hxk⟩, hm⟩ ↦ ?_⟩
    · rintro (⟨⟨hx, hxk⟩, hm⟩ | ⟨⟨hx, _, hxk⟩, hm⟩)
      · exact ⟨⟨hx, hxk.trans (hmono k.lt_succ_self).le⟩, hm⟩
      · exact ⟨⟨hx, hxk⟩, hm⟩
    · rcases le_or_gt (f x) (a k) with hle | hgt
      · exact .inl ⟨⟨hx, hle⟩, hm⟩
      · exact .inr ⟨⟨hx, hgt, hxk⟩, hm⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
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

omit [FiniteDimensional ℝ E] in
/-- **The CW model of a proper Morse function, with compatible finite sublevel models.** Let `f` be
a proper Morse function, bounded below, on a boundaryless Hausdorff manifold `M`. There exist
strictly increasing regular values `a : ℕ → ℝ` tending to infinity from below all values of `f`, a
Hausdorff CW complex `X` with a homotopy equivalence `h : X ≃ₕ M` whose `m`-cells correspond to the
critical points of `f` of index `m`, and finite Hausdorff CW complexes `W k` with closed embeddings
`j k : C(W k, X)` exhausting `X` and homotopy equivalences `hSub k : W k ≃ₕ {f ≤ a k}` such that
`h ∘ j k` is `hSub k` followed by the sublevel inclusion, `h.symm` carries `{f ≤ a k}` into the
image of `j k`, and the `m`-cells of `W k` correspond to the critical points of `f` in `{f ≤ a k}`
of index `m`. -/
theorem IsMorse.exists_cwComplex_sublevel_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (a : ℕ → ℝ) (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
      (_ : CWComplex (univ : Set X)) (h : X ≃ₕ M)
      (W : ℕ → Type u) (_ : ∀ k, TopologicalSpace (W k)) (_ : ∀ k, T2Space (W k))
      (_ : ∀ k, CWComplex (univ : Set (W k))) (_ : ∀ k, RelCWComplex.Finite (univ : Set (W k)))
      (j : ∀ k, C(W k, X)) (hSub : ∀ k, W k ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      (∀ x, a 0 < f x) ∧ (∀ k, IsClosedEmbedding (j k)) ∧ ⋃ k, range (j k) = univ ∧
      (∀ k w, h (j k w) = (hSub k w : M)) ∧
      (∀ k, MapsTo h.symm {x | f x ≤ a k} (range (j k))) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})) ∧
      ∀ k m, Nonempty (cell (univ : Set (W k)) m ≃
        ↥{x ∈ criticalPoints I f ∩ {x | f x ≤ a k} | manifoldMorseIndex I f x = m}) := by
  rcases isEmpty_or_nonempty M with hEmpty | _
  · have hEmptySub (k : ℕ) : IsEmpty {x | f x ≤ (k : ℝ)} := ⟨fun x ↦ hEmpty.false x.1⟩
    have hEmptyCell (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) :=
      ⟨fun c ↦ PEmpty.elim (map m c 0)⟩
    have hEmptyCrit (m : ℕ) : IsEmpty ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m} :=
      ⟨fun x ↦ hEmpty.false x.1⟩
    refine ⟨fun k : ℕ ↦ (k : ℝ), PEmpty.{u + 1}, _, inferInstance, inferInstance,
      Homeomorph.empty.toHomotopyEquiv, fun _ ↦ PEmpty.{u + 1}, fun _ ↦ _, fun _ ↦ inferInstance,
      fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ .id _,
      fun _ ↦ Homeomorph.empty.toHomotopyEquiv, Nat.strictMono_cast, tendsto_natCast_atTop_atTop,
      fun _ ↦ isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, _⟩ ↦ hEmpty.false x,
      fun x ↦ hEmpty.elim x, fun _ ↦ .id, eq_univ_of_forall fun x ↦ PEmpty.elim x,
      fun _ w ↦ PEmpty.elim w, fun _ x ↦ hEmpty.elim x,
      fun m ↦ ⟨Equiv.equivOfIsEmpty _ _⟩, fun k m ↦ ⟨?_⟩⟩
    have : IsEmpty ↥{x ∈ criticalPoints I f ∩ {x | f x ≤ (k : ℝ)} |
        manifoldMorseIndex I f x = m} := ⟨fun x ↦ hEmpty.false x.1⟩
    exact Equiv.equivOfIsEmpty _ _
  have : WeaklyLocallyCompactSpace M :=
    ⟨fun x ↦ ⟨f ⁻¹' Icc (f x - 1) (f x + 1), hp.isCompact_preimage isCompact_Icc,
      hp.continuous.continuousAt (Icc_mem_nhds (by linarith) (by linarith))⟩⟩
  have : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
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
  let S₀ : SublevelCWModel f (a 0) :=
    { W := PEmpty.{u + 1}, h := Homeomorph.empty.toHomotopyEquiv }
  let S := sublevelCWModelSeq S₀ S'
  have hScell := sublevelCWModelSeq_cell_equiv hmono ha0 S₀
    (fun m ↦ ⟨fun c ↦ PEmpty.elim (map m c 0)⟩) S' e
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
  obtain ⟨h, h_eq, hMaps⟩ := exists_homotopyEquiv_of_isCoherentWith (TopCat.monotone_range_ι c)
    ((sublevel_mono f).comp hmono.monotone) (TopCat.iUnion_range_ι_of_isColimit hc)
    (iUnion_sublevel_eq_univ_of_tendsto f htop) (TopCat.isCoherentWith_range_ι_of_isColimit hc)
    (isCoherentWith_range_sublevel_of_tendsto hf.contMDiff.continuous htop)
    (hasHomotopyExtensionProperty_preimage_range_ι hF hιc hc) hBH g eA heA
  refine ⟨a, c.pt, _, inferInstance, ‹_›, h, fun k ↦ (S k).W, fun k ↦ (S k).topologicalSpace,
    fun k ↦ (S k).t2Space, fun k ↦ (S k).cwComplex, fun k ↦ (S k).finite,
    fun k ↦ (c.ι.app k).hom, fun k ↦ (S k).h, hmono, htop, hreg, ha0, hemb,
    TopCat.iUnion_range_ι_of_isColimit hc,
    fun k w ↦ (congrFun h_eq _).trans (hg k w), hMaps, fun m ↦ ⟨?_⟩, hScell⟩
  -- The cells of `X` are the cells of the first, empty, stage, and the new cells of the later
  -- stages, which are the critical points in the bands `(a k, a (k + 1)]`.
  have : IsEmpty (cell (univ : Set (F.obj 0)) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
  exact (cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <| (Equiv.emptySum _ _).trans <|
    (Equiv.sigmaCongrRight fun k ↦ (e k (S k) m).complRangeSymmInl).trans
      (sigmaCriticalPointsIocEquiv hmono htop ha0 m)

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
  obtain ⟨_, X, _, _, _, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcell, -⟩ :=
    hf.exists_cwComplex_sublevel_homotopyEquiv hp hbdd
  exact ⟨X, _, ‹_›, ‹_›, ⟨h.symm⟩, hcell⟩

omit [FiniteDimensional ℝ E] in
/-- **The dimension-bounded CW model of a proper Morse function.** Let `f` be a proper Morse
function, bounded below, on a boundaryless Hausdorff manifold `M`, all of whose critical points
have Morse index at most `d`. Then `M` is homotopy equivalent to a Hausdorff CW complex `X` whose
`m`-cells correspond to the critical points of `f` of index `m` and which has no cells in
dimensions strictly greater than `d`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ (∀ k, d < k → IsEmpty (cell (univ : Set X) k)) ∧
      ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨X, _, _, _, ⟨h⟩, hcell⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  refine ⟨X, _, ‹_›, ‹_›, ⟨h⟩, fun k hk ↦ ?_, hcell⟩
  exact (hcell k).some.isEmpty_congr.2 ⟨fun ⟨x, hx, hxk⟩ ↦ ((hd x hx).trans_lt (hxk ▸ hk)).false⟩

omit [FiniteDimensional ℝ E] in
/-- A boundaryless Hausdorff manifold carrying a proper Morse function bounded below has CW type. -/
theorem IsMorse.cwType (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    CWType M := by
  obtain ⟨X, _, _, _, ⟨h⟩, -⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  exact (h.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv).cwType

end TauCeti
