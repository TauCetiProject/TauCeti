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

* `TauCeti.IsMorse.exists_cwComplex_subcomplex_homotopyEquiv`: **the sublevel-compatible CW
  exhaustion of a proper Morse function.** A manifold carrying a proper Morse function bounded below
  admits a regular exhaustion `a 0 < a 1 < ⋯` and a Hausdorff CW homotopy model `X ≃ₕ M` exhausted
  by an increasing sequence of finite CW subcomplexes `W k` restricting `X ≃ₕ M` to stage homotopy
  equivalences `W k ≃ₕ {f ≤ a k}` (with homotopy inverse mapping `{f ≤ a k}` into `W k`), whose
  `λ`-cells globally and at each stage correspond to the critical points of index `λ`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`: **the CW model of a proper Morse function.** A
  manifold carrying a proper Morse function bounded below is homotopy equivalent to a Hausdorff
  CW complex whose `λ`-cells correspond to the critical points of index `λ`.
* `TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`: when every critical
  point of `f` has Morse index at most `d`, the CW homotopy model is finite-dimensional and has no
  cells in dimensions strictly above `d`.

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

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
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

open Classical in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
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

/-- Glue compatible stage homotopy equivalences `S k ≃ₕ {f ≤ a k}` into a homotopy equivalence
`c.pt ≃ₕ M` from the colimit of the CW tower, restricting to `eW k` on each stage subcomplex and
with homotopy inverse mapping `{f ≤ a k}` into the `k`-th stage subcomplex. -/
private theorem IsMorse.exists_homotopyEquiv_colimit_sublevel (hf : IsMorse I f) {a : ℕ → ℝ}
    (hmono : StrictMono a) (htop : Tendsto a atTop atTop)
    (hreg : ∀ k, IsRegularValue I 𝓘(ℝ) f (a k))
    (hcompact : ∀ k, IsCompact (f ⁻¹' Icc (a k) (a (k + 1))))
    (S : ∀ k, SublevelCWModel I f (a k)) (ι : ∀ k, C((S k).W, (S (k + 1)).W))
    {F : ℕ ⥤ TopCat.{u}} (hF_eq : F = Functor.ofSequence (X := fun k ↦ TopCat.of (S k).W)
      fun k ↦ (TopCat.ofHom (ι k) : TopCat.of (S k).W ⟶ TopCat.of (S (k + 1)).W))
    [∀ k, CWComplex (univ : Set (F.obj k))] [∀ k, T2Space (F.obj k)]
    (hF : ∀ k : ℕ, IsClosedEmbedding (F.map (homOfLE k.le_succ)))
    {ιc : ∀ k m, cell (univ : Set (F.obj k)) m → cell (univ : Set (F.obj (k + 1))) m}
    (hιc : ∀ (k m : ℕ) j, ⇑(map m (ιc k m j)) = F.map (homOfLE k.le_succ) ∘ map m j)
    (hh : ∀ k w, ((S (k + 1)).h (ι k w) : M) = (S k).h w) {c : Cocone F} (hc : IsColimit c) :
    letI := cwComplexOfIsColimit hF hιc hc
    let W := cwComplexOfIsColimitSubcomplex hF hιc hc
    ∃ (h : c.pt ≃ₕ M) (eW : ∀ k, (W k : Set c.pt) ≃ₕ {x | f x ≤ a k}),
      (∀ k (x : (W k : Set c.pt)), (eW k x : M) = h x) ∧
      ∀ k, MapsTo h.symm {x | f x ≤ a k} (W k) := by
  subst hF_eq
  let := cwComplexOfIsColimit hF hιc hc
  let φ : Cocone (Functor.ofSequence (X := fun k ↦ TopCat.of (S k).W)
      fun k ↦ (TopCat.ofHom (ι k) : TopCat.of (S k).W ⟶ TopCat.of (S (k + 1)).W)) :=
    { pt := TopCat.of M
      ι := NatTrans.ofSequence
        (fun k ↦ TopCat.ofHom ((ContinuousMap.subtypeVal _).comp (S k).h.toFun)) fun k ↦ by
          ext w
          rw [Functor.ofSequence_map_homOfLE_succ]
          exact hh k w }
  let g : C(c.pt, M) := (hc.desc φ).hom
  have hg (k : ℕ) (w : (S k).W) : g (c.ι.app k w) = (S k).h w :=
    ConcreteCategory.congr_hom (hc.fac φ k) w
  have hemb := TopCat.isClosedEmbedding_ι_of_isColimit_of_succ hF hc
  let eA (k : ℕ) : (range (c.ι.app k) : Set c.pt) ≃ₕ {x | f x ≤ a k} :=
    (hemb k).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.trans (S k).h
  have heA (k : ℕ) (x : (range (c.ι.app k) : Set c.pt)) : (eA k x : M) = g x := by
    obtain ⟨_, w, rfl⟩ := x
    exact (congrArg (fun y ↦ ((S k).h y : M))
      ((hemb k).isEmbedding.toHomeomorph_symm_apply w)).trans (hg k w).symm
  have hBH (k : ℕ) : HasHomotopyExtensionProperty
      ((↑) ⁻¹' {x | f x ≤ a k} : Set {x | f x ≤ a (k + 1)}) := by
    rw [← range_sublevelInclusion f (hmono k.lt_succ_self).le]
    exact hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
      hf.contMDiff (hmono k.lt_succ_self) (hcompact k) (hreg k) (hmono k.lt_succ_self).le
  obtain ⟨h, hcoe, hsymm⟩ := exists_homotopyEquiv_of_isCoherentWith (TopCat.monotone_range_ι c)
    ((sublevel_mono f).comp hmono.monotone) (TopCat.iUnion_range_ι_of_isColimit hc)
    (iUnion_sublevel_eq_univ_of_tendsto f htop) (TopCat.isCoherentWith_range_ι_of_isColimit hc)
    (isCoherentWith_range_sublevel_of_tendsto hf.contMDiff.continuous htop)
    (hasHomotopyExtensionProperty_preimage_range_ι hF hιc hc) hBH g eA heA
  have hW_coe := coe_cwComplexOfIsColimitSubcomplex hF hιc hc
  exact ⟨h, fun k ↦ (Homeomorph.setCongr (hW_coe k)).toHomotopyEquiv.trans (eA k),
    fun k x ↦ (heA k ⟨x.1, hW_coe k ▸ x.2⟩).trans (congrFun hcoe.symm x.1),
    fun k ↦ (hW_coe k).symm ▸ hsymm k⟩

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
  obtain ⟨a, K, hmono, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have ha0 (x : M) : a 0 < f x := not_le.1 fun hx ↦ notMem_empty x (hK0 ▸ (hK 0).symm ▸ hx)
  have hcompact (k : ℕ) : IsCompact (f ⁻¹' Icc (a k) (a (k + 1))) :=
    hp.isCompact_preimage isCompact_Icc
  choose S' ι hι hh e he using fun k (S : SublevelCWModel I f (a k)) ↦
    hf.exists_sublevelCWModel_extension (hmono k.lt_succ_self).le (hcompact k) (hreg k)
      (hreg (k + 1)) S
  have : IsEmpty {x | f x ≤ a 0} := ⟨fun x ↦ (not_le.2 (ha0 x)) x.2⟩
  have hcell0 (m : ℕ) : cell (univ : Set PEmpty.{u + 1}) m ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a 0) | manifoldMorseIndex I f x = m} :=
    have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    have : IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic (a 0) | manifoldMorseIndex I f x = m} :=
      ⟨fun x ↦ (not_le.2 (ha0 x.1)) x.2.1.2⟩
    Equiv.equivOfIsEmpty _ _
  let S := sublevelCWModelSeq ⟨PEmpty.{u + 1}, Homeomorph.empty.toHomotopyEquiv, hcell0⟩ S'
  let F : ℕ ⥤ TopCat.{u} :=
    Functor.ofSequence (X := fun k : ℕ ↦ TopCat.of (S k).W) fun k : ℕ ↦
      (TopCat.ofHom (ι k (S k)) : TopCat.of (S k).W ⟶ TopCat.of (S (k + 1)).W)
  have hF (k : ℕ) : IsClosedEmbedding (F.map (homOfLE k.le_succ)) := by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact hι k (S k)
  let (k : ℕ) : CWComplex (univ : Set (F.obj k)) := (S k).cwComplex
  let (k : ℕ) : RelCWComplex.Finite (univ : Set (F.obj k)) := (S k).finite
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
  have : ∀ k, CompactSpace (F.obj k) := fun k ↦
    isCompact_univ_iff.1 (CWComplex.isCompact_of_finite (C := (univ : Set (S k).W)))
  have := TopCat.t4Space_of_isColimit hF hc
  obtain ⟨h, hW, hhW, hsymm⟩ := hf.exists_homotopyEquiv_colimit_sublevel hmono htop hreg hcompact
    S (fun k ↦ ι k (S k)) rfl hF hιc (fun k ↦ hh k (S k)) hc
  have hW_coe := coe_cwComplexOfIsColimitSubcomplex hF hιc hc
  refine ⟨a, c.pt, c.pt.str, inferInstance, ‹_›, cwComplexOfIsColimitSubcomplex hF hιc hc,
    h, hW, hmono, htop, ha0, hreg,
    fun k l hkl ↦ SetLike.coe_subset_coe.1 ((hW_coe k).trans_subset
      ((TopCat.monotone_range_ι c hkl).trans_eq (hW_coe l).symm)),
    (hW_coe 0).trans (by
      have : IsEmpty (F.obj 0) := inferInstanceAs (IsEmpty PEmpty.{u + 1})
      exact range_eq_empty _),
    (iUnion_congr hW_coe).trans (TopCat.iUnion_range_ι_of_isColimit hc),
    fun k ↦ finite_cwComplexOfIsColimitSubcomplex hF hιc hc k, hhW, hsymm, fun m ↦ ⟨?_⟩,
    fun k m ↦ ?_⟩
  · have : IsEmpty (cell (univ : Set (F.obj 0)) m) := ⟨fun j ↦ PEmpty.elim (map m j 0)⟩
    exact (cwComplexOfIsColimitCellEquiv hF hιc hc m).trans <| (Equiv.emptySum _ _).trans <|
      (Equiv.sigmaCongrRight fun k ↦ (e k (S k) m).complRangeSymmInl).trans
        (sigmaCriticalPointsIocEquiv hmono htop ha0 m)
  · rw [CWComplex.Subcomplex.cell_def]
    exact ⟨(cwComplexOfIsColimitSubcomplexCellEquiv hF hιc hc k m).trans ((S k).cellEquiv m)⟩

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
  obtain ⟨_, X, _, _, _, _, h, _, -, -, -, -, -, -, -, -, -, -, hcell, -⟩ :=
    hf.exists_cwComplex_subcomplex_homotopyEquiv hp hbdd
  exact ⟨X, _, ‹_›, ‹_›, ⟨h.symm⟩, hcell⟩

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
  obtain ⟨X, _, _, _, ⟨h⟩, hcell⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  have hempty (m : ℕ) (hm : d < m) : IsEmpty (cell (univ : Set X) m) :=
    (hcell m).some.isEmpty_congr.2 ⟨fun x ↦ ((x.2.2 ▸ hidx x.1 x.2.1).trans_lt hm).false⟩
  exact ⟨X, _, ‹_›, ‹_›, RelCWComplex.finiteDimensional_of_isEmpty_cell_gt (univ : Set X) hempty,
    ⟨h⟩, hcell, hempty⟩

end TauCeti
