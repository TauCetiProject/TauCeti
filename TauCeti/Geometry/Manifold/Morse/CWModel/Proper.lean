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
import TauCeti.Topology.Maps.Proper.Basic

/-!
# The CW model of a proper Morse function

Let `f` be a Morse function on a Hausdorff boundaryless manifold `M`, proper and bounded below.
Then `M` is homotopy equivalent to a Hausdorff CW complex `X` with one `λ`-cell for each critical
point of `f` of index `λ` (`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`), refined by an
increasing exhausting filtration by finite CW subcomplexes `W k` modelling the regular sublevels
`{f ≤ a k}` (`TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv`). No finite-dimensionality
assumption on the model space is needed: when `M` is nonempty, `f : M → ℝ` makes `M` locally
compact (`IsProperMap.weaklyLocallyCompactSpace`), so Riesz's theorem
(`FiniteDimensional.of_locallyCompact_manifold`) forces the model space to be finite-dimensional.
When every critical point of `f` has index at most `d`, `X` has no cells in dimensions strictly
above `d` (`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`).

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
stage is compact (`TauCeti.TopCat.normalSpace_of_isColimit`). Inside `X` the stages sit as finite
subcomplexes (`TauCeti.cwComplexOfIsColimitSubcomplex`) linked by closed cofibrations, and so are
the regular sublevels of `M`, by collars of the regular levels
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`). The models of
the stages commute strictly with the inclusions, so they glue to a map `X → M` which is a homotopy
equivalence on every stage, hence a homotopy equivalence
(`TauCeti.exists_homotopyEquiv_of_isCoherentWith`).

## Main results

* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv`: **sublevel-filtered CW model of a
  proper Morse function.** Produces `X ≃ₕ M` together with regular values `a k → ∞` and an
  exhausting sequence of finite CW subcomplexes `W k ≃ₕ {f ≤ a k}` counting the critical points by
  index on `M` and on each sublevel `{f ≤ a k}`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`: **the CW model of a proper Morse function.**
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`: when all critical
  indices of `f` are at most `d`, `M` is homotopy equivalent to a Hausdorff CW complex with no cells
  above dimension `d`.

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
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
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
private theorem IsMorse.exists_sublevelCWModel_extension [FiniteDimensional ℝ E] (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (S : SublevelCWModel f a) :
    ∃ (S' : SublevelCWModel f b) (ι : C(S.W, S'.W)), IsClosedEmbedding ι ∧
      (∀ w, (S'.h (ι w) : M) = S.h w) ∧
      ∃ e : ∀ m, cell (univ : Set S'.W) m ≃ cell (univ : Set S.W) m ⊕
          ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m},
        ∀ m j x, map m ((e m).symm (.inl j)) x = ι (map m j x) := by
  obtain ⟨W', _, _, _, ι, h', _, hι, -, hh, e, he⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hcompact ha hb S.W S.h
  exact ⟨⟨W', h'⟩, ι, hι, hh, e, he⟩

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- Splitting the critical points of index `m` in `{f ≤ t}` into `{f ≤ s}` and `f⁻¹(s, t]`. -/
private def criticalPointsIicSumIocEquiv {s t : ℝ} (hst : s ≤ t) (m : ℕ) :
    ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic s | manifoldMorseIndex I f x = m} ⊕
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc s t | manifoldMorseIndex I f x = m} ≃
    ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic t | manifoldMorseIndex I f x = m} :=
  Equiv.ofBijective
    (Sum.elim (fun x ↦ ⟨x.1, ⟨x.2.1.1, x.2.1.2.trans hst⟩, x.2.2⟩)
      fun x ↦ ⟨x.1, ⟨x.2.1.1, x.2.1.2.2⟩, x.2.2⟩)
    ⟨by
      rintro (x | x) (y | y) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact absurd (h ▸ y.2.1.2.1) (not_lt.2 x.2.1.2)
      · exact absurd (h ▸ x.2.1.2.1) (not_lt.2 y.2.1.2)
      · exact congrArg Sum.inr (Subtype.ext h),
     fun ⟨x, ⟨hx, hxt⟩, hxm⟩ ↦
      (le_or_gt (f x) s).elim (fun hxs ↦ ⟨.inl ⟨x, ⟨hx, hxs⟩, hxm⟩, rfl⟩)
        fun hxs ↦ ⟨.inr ⟨x, ⟨hx, hxs, hxt⟩, hxm⟩, rfl⟩⟩

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- At stage `k`, the `m`-cells of `(sublevelCWModelSeq S₀ S' k).W` correspond to the critical
points of `f` of index `m` in `{f ≤ a k}`. -/
private def stageCriticalPointsIicEquiv {a : ℕ → ℝ} (hmono : StrictMono a) (ha0 : ∀ x, a 0 < f x)
    (S₀ : SublevelCWModel f (a 0)) [IsEmpty S₀.W]
    (S' : ∀ k, SublevelCWModel f (a k) → SublevelCWModel f (a (k + 1)))
    (e : ∀ k (S : SublevelCWModel f (a k)) m, cell (univ : Set (S' k S).W) m ≃
      cell (univ : Set S.W) m ⊕
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc (a k) (a (k + 1)) | manifoldMorseIndex I f x = m}) :
    ∀ k m, cell (univ : Set (sublevelCWModelSeq S₀ S' k).W) m ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a k) | manifoldMorseIndex I f x = m}
  | 0, m =>
    @Equiv.equivOfIsEmpty _ _ ⟨fun j ↦ @IsEmpty.false S₀.W ‹_› (map m j 0)⟩
      ⟨fun x ↦ (not_le.2 (ha0 x.1)) x.2.1.2⟩
  | k + 1, m =>
    (e k (sublevelCWModelSeq S₀ S' k) m).trans <|
      (Equiv.sumCongr (stageCriticalPointsIicEquiv hmono ha0 S₀ S' e k m) (Equiv.refl _)).trans
        (criticalPointsIicSumIocEquiv (hmono k.lt_succ_self).le m)

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
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

/-- The sequential `TopCat` diagram of a family of sublevel CW models connected by maps `ι k`. -/
private abbrev sublevelCWModelDiagram {M : Type u} [TopologicalSpace M] {f : M → ℝ} {a : ℕ → ℝ}
    (S : ∀ k, SublevelCWModel f (a k)) (ι : ∀ k, C((S k).W, (S (k + 1)).W)) : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence (X := fun k : ℕ ↦ TopCat.of (S k).W) fun k : ℕ ↦
    (TopCat.ofHom (ι k) : TopCat.of (S k).W ⟶ TopCat.of (S (k + 1)).W)

/-- Given an exhausting sequence of regular values and compatible sublevel CW models, the maps to
`M` glue on the sequential colimit `c.pt` to a homotopy equivalence restricting to the stage models
on `range (c.ι.app k)`. -/
private theorem exists_homotopyEquiv_sublevelCWModelDiagram [FiniteDimensional ℝ E]
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a : ℕ → ℝ} (hmono : StrictMono a) (htop : Tendsto a atTop atTop)
    (hreg : ∀ k, IsRegularValue I 𝓘(ℝ) f (a k))
    (hcompact : ∀ k, IsCompact (f ⁻¹' Icc (a k) (a (k + 1))))
    (S : ∀ k, SublevelCWModel f (a k)) (ι : ∀ k, C((S k).W, (S (k + 1)).W))
    (hh : ∀ k w, ((S (k + 1)).h (ι k w) : M) = (S k).h w)
    {c : Cocone (sublevelCWModelDiagram S ι)} (hc : IsColimit c)
    (hF : ∀ k : ℕ, IsClosedEmbedding ((sublevelCWModelDiagram S ι).map (homOfLE k.le_succ)))
    (hAH : ∀ k, HasHomotopyExtensionProperty
      ((↑) ⁻¹' (range (c.ι.app k) : Set c.pt) : Set (range (c.ι.app (k + 1)) : Set c.pt))) :
    ∃ (h : c.pt ≃ₕ M) (eA : ∀ k, (range (c.ι.app k) : Set c.pt) ≃ₕ {x | f x ≤ a k}),
      (∀ k (x : (range (c.ι.app k) : Set c.pt)), (eA k x : M) = h x.1) ∧
      ∀ k, MapsTo h.symm {x | f x ≤ a k} (range (c.ι.app k) : Set c.pt) := by
  let φ : Cocone (sublevelCWModelDiagram S ι) :=
    { pt := TopCat.of M
      ι := NatTrans.ofSequence
        (fun k ↦ TopCat.ofHom ((ContinuousMap.subtypeVal _).comp (S k).h.toFun)) fun k ↦ by
          ext w; rw [Functor.ofSequence_map_homOfLE_succ]; exact hh k w }
  let g : C(c.pt, M) := (hc.desc φ).hom
  have hemb := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc
  let eA (k : ℕ) : (range (c.ι.app k) : Set c.pt) ≃ₕ {x | f x ≤ a k} :=
    (hemb k).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.trans (S k).h
  have heA (k : ℕ) (x : (range (c.ι.app k) : Set c.pt)) : (eA k x : M) = g x.1 := by
    obtain ⟨_, w, rfl⟩ := x
    exact (congrArg (fun y ↦ ((S k).h y : M))
      ((hemb k).isEmbedding.toHomeomorph_symm_apply w)).trans
      (ConcreteCategory.congr_hom (hc.fac φ k) w).symm
  have hBH (k : ℕ) : HasHomotopyExtensionProperty
      ((↑) ⁻¹' {x | f x ≤ a k} : Set {x | f x ≤ a (k + 1)}) := by
    rw [← range_sublevelInclusion f (hmono k.lt_succ_self).le]
    exact hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
      hf (hmono k.lt_succ_self) (hcompact k) (hreg k) (hmono k.lt_succ_self).le
  obtain ⟨h, hhg, hmaps⟩ := exists_homotopyEquiv_of_isCoherentWith (TopCat.monotone_range_ι c)
    ((sublevel_mono f).comp hmono.monotone) (TopCat.iUnion_range_ι_of_isColimit hc)
    (iUnion_sublevel_eq_univ_of_tendsto f htop) (TopCat.isCoherentWith_range_ι_of_isColimit hc)
    (isCoherentWith_range_sublevel_of_tendsto hf.continuous htop) hAH hBH g eA heA
  exact ⟨h, eA, fun k x ↦ (heA k x).trans (congrFun hhg x.1).symm, hmaps⟩

/-- Finite-dimensional core of `IsMorse.exists_cwComplex_subcomplex_homotopyEquiv`: glue the
sublevel CW models into a sequential colimit, read each stage as a finite subcomplex, and compare
the two towers of closed cofibrations. -/
private theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv_of_finiteDimensional
    [FiniteDimensional ℝ E] (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (a : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)) (h : X ≃ₕ M)
      (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (⋃ k, (W k : Set X)) = univ ∧ (W 0 : Set X) = ∅ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : W k), (hW k w : M) = h w) ∧ (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})) ∧
      ∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a k) | manifoldMorseIndex I f x = m}) := by
  obtain ⟨a, K, hmono, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x := by
    by_contra! hx; exact (hK0 ▸ (hK 0).symm ▸ hx : x ∈ (∅ : Set M))
  have hcompact (k : ℕ) : IsCompact (f ⁻¹' Icc (a k) (a (k + 1))) :=
    hp.isCompact_preimage isCompact_Icc
  choose S' ι hι hh e he using fun k (S : SublevelCWModel f (a k)) ↦
    hf.exists_sublevelCWModel_extension (hmono k.lt_succ_self).le (hcompact k) (hreg k)
      (hreg (k + 1)) S
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (not_le.2 (ha0 x)) x.2⟩
  let S₀ : SublevelCWModel f (a 0) := { W := PEmpty.{u + 1}, h := Homeomorph.empty.toHomotopyEquiv }
  let S := sublevelCWModelSeq S₀ S'
  let F := sublevelCWModelDiagram S fun k ↦ ι k (S k)
  have hF (k : ℕ) : IsClosedEmbedding (F.map (homOfLE k.le_succ)) := by
    rw [Functor.ofSequence_map_homOfLE_succ]; exact hι k (S k)
  let (k : ℕ) : CWComplex (univ : Set (F.obj k)) := (S k).cwComplex
  let (k : ℕ) : RelCWComplex.Finite (univ : Set (F.obj k)) := (S k).finite
  have (k : ℕ) : T2Space (F.obj k) := (S k).t2Space
  let ιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) : cell (univ : Set (S (k + 1)).W) m :=
    (e k (S k) m).symm (.inl j)
  have hιc (k m : ℕ) (j : cell (univ : Set (S k).W) m) :
      ⇑(map m (ιc k m j)) = F.map (homOfLE k.le_succ) ∘ map m j := by
    rw [Functor.ofSequence_map_homOfLE_succ]; exact funext (he k (S k) m j)
  let c := colimit.cocone F
  have hc : IsColimit c := colimit.isColimit F
  let instCW := cwComplexOfIsColimit hF hιc hc
  have : ∀ k, CompactSpace (F.obj k) := fun k ↦
    isCompact_univ_iff.1 (CWComplex.isCompact_of_finite (C := (univ : Set (S k).W)))
  have := TopCat.t4Space_of_isColimit hF hc
  let W := cwComplexOfIsColimitSubcomplex hF hιc hc
  have hWeq := coe_cwComplexOfIsColimitSubcomplex hF hιc hc
  obtain ⟨h, eA, heA, hmaps⟩ := exists_homotopyEquiv_sublevelCWModelDiagram hf.contMDiff hmono htop
    hreg hcompact S (fun k ↦ ι k (S k)) (fun k ↦ hh k (S k)) hc hF
    (hasHomotopyExtensionProperty_preimage_range_ι hF hιc hc)
  refine ⟨c.pt, inferInstance, inferInstance, instCW, a, W, h,
    fun k ↦ (Homeomorph.setCongr (hWeq k)).toHomotopyEquiv.trans (eA k), hmono, htop, hreg,
    monotone_cwComplexOfIsColimitSubcomplex hF hιc hc,
    iUnion_coe_cwComplexOfIsColimitSubcomplex hF hιc hc,
    (hWeq 0).trans (eq_empty_iff_forall_notMem.2 fun _ hx ↦ PEmpty.elim hx.choose),
    fun k ↦ finite_cwComplexOfIsColimitSubcomplex hF hιc hc k,
    fun k (w : W k) ↦ heA k ⟨w.1, (hWeq k).subset w.2⟩, fun k ↦ (hWeq k).symm ▸ hmaps k,
    fun m ↦ ⟨?_⟩, fun k m ↦ ⟨(cwComplexOfIsColimitSubcomplexCellEquiv hF hιc hc k m).trans
      (stageCriticalPointsIicEquiv hmono ha0 S₀ S' e k m)⟩⟩
  have : IsEmpty (cell (univ : Set (F.obj 0)) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
  exact (cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <| (Equiv.emptySum _ _).trans <|
    (Equiv.sigmaCongrRight fun k ↦ (e k (S k) m).complRangeSymmInl).trans
      (sigmaCriticalPointsIocEquiv hmono htop ha0 m)

/-- **Sublevel-filtered CW model of a proper Morse function** (Milnor, *Morse Theory*, Theorem 3.5
and its proof). Let `f` be a Morse function on a Hausdorff boundaryless manifold `M`, proper and
bounded below. Then there are a Hausdorff CW complex `X`, a strictly increasing unbounded sequence
`a` of regular values of `f`, an exhausting sequence `W` of finite CW subcomplexes of `X` starting
at `W 0 = ∅`, and a homotopy equivalence `h : X ≃ₕ M` restricting on each `W k` to a homotopy
equivalence `W k ≃ₕ {f ≤ a k}` (with `h.symm` mapping `{f ≤ a k}` into `W k`), such that the
`m`-cells of `X` (and of each `W k`) correspond to the critical points of `f` of index `m` (in
`{f ≤ a k}`). -/
theorem IsMorse.exists_cwComplex_subcomplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X))
      (a : ℕ → ℝ) (W : ℕ → Subcomplex (univ : Set X)) (h : X ≃ₕ M)
      (hW : ∀ k, (W k : Set X) ≃ₕ {x | f x ≤ a k}),
      StrictMono a ∧ Tendsto a atTop atTop ∧ (∀ k, IsRegularValue I 𝓘(ℝ) f (a k)) ∧
      Monotone W ∧ (⋃ k, (W k : Set X)) = univ ∧ (W 0 : Set X) = ∅ ∧
      (∀ k, RelCWComplex.Finite (W k : Set X)) ∧
      (∀ k (w : W k), (hW k w : M) = h w) ∧ (∀ k, MapsTo h.symm {x | f x ≤ a k} (W k)) ∧
      (∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})) ∧
      ∀ k m, Nonempty (cell (W k : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a k) | manifoldMorseIndex I f x = m}) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨PEmpty.{u + 1}, inferInstance, inferInstance, inferInstance, fun k : ℕ ↦ (k : ℝ),
      fun _ ↦ ⊥, Homeomorph.empty.toHomotopyEquiv, fun _ ↦ Homeomorph.empty.toHomotopyEquiv,
      Nat.strictMono_cast, tendsto_natCast_atTop_atTop,
      fun _ ↦ isRegularValue_iff.2 fun x ↦ isEmptyElim x, monotone_const,
      by simp [eq_empty_of_isEmpty (univ : Set PEmpty.{u + 1})], rfl, fun _ ↦ inferInstance,
      fun _ w ↦ isEmptyElim w.1, fun _ x ↦ isEmptyElim x, fun m ↦ ⟨?_⟩, fun _ m ↦ ⟨?_⟩⟩
    · have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
      exact Equiv.equivOfIsEmpty _ _
    · have : IsEmpty (cell ((⊥ : Subcomplex (univ : Set PEmpty.{u + 1})) : Set PEmpty.{u + 1}) m) :=
        ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
      exact Equiv.equivOfIsEmpty _ _
  have : WeaklyLocallyCompactSpace M := hp.weaklyLocallyCompactSpace
  have : FiniteDimensional ℝ E := .of_locallyCompact_manifold M I
  exact hf.exists_cwComplex_subcomplex_homotopyEquiv_of_finiteDimensional hp hbdd

/-- **The CW model of a proper Morse function** (Milnor, *Morse Theory*, Theorem 3.5). Let `f` be
a Morse function on a Hausdorff boundaryless manifold `M`, proper and bounded below. Then `M` is
homotopy equivalent to a Hausdorff CW complex `X` whose `m`-cells correspond to the critical points
of `f` of index `m`, for every `m`. When there are infinitely many critical points of index `m`, `X`
has infinitely many `m`-cells. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, Nonempty (cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m}) := by
  obtain ⟨X, _, _, _, -, -, h, -, -, -, -, -, -, -, -, -, -, hcell, -⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  exact ⟨X, _, inferInstance, ‹_›, ⟨h.symm⟩, hcell⟩

/-- **Index-bounded CW model of a proper Morse function.** If a Hausdorff boundaryless manifold `M`
carries a proper bounded-below Morse function `f` whose critical points all have Morse index at most
`d`, then `M` is homotopy equivalent to a Hausdorff CW complex with no cells in dimensions strictly
above `d`. -/
theorem IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (M ≃ₕ X) ∧ ∀ m, d < m → IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨X, _, _, _, ⟨h⟩, hcell⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  refine ⟨X, _, inferInstance, ‹_›, ⟨h⟩, fun m hm ↦ ?_⟩
  refine (hcell m).some.isEmpty_congr.2 ⟨fun ⟨x, hx, hxm⟩ ↦ ?_⟩
  exact not_lt_of_ge (hd x hx) (hxm ▸ hm)

end TauCeti
