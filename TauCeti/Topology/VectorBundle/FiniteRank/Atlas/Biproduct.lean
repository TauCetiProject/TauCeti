/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Core.Congr
public import TauCeti.Topology.VectorBundle.Core.LocallyConstant
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Whitney sums and binary biproducts of variable-rank bundle atlases

For two variable-rank bundle atlases `A D : FiniteRankAtlas 𝕜 X`, the rank of their Whitney sum is
`A.rank + D.rank : LocallyConstant X ℕ`. Unlike constant-rank bundle cores, a single clopen stratum
`{x : X // (A.rank + D.rank) x = n}` of the total rank need not have constant summand ranks across
disconnected components (for instance `(1, 0)` and `(0, 1)` both have sum `1`). However, the pair
`(A.rank x, D.rank x)` refines `{x : X // (A.rank + D.rank) x = n}` as a locally constant map into
`{p : ℕ × ℕ // p.1 + p.2 = n}`. On each clopen piece of this refinement, the stratum cores of `A`
and `D` pull back to constant-rank cores whose `FiniteRankBundleCore.whitneySum` has model
`Fin (p.1 + p.2) → 𝕜`, transported to `Fin n → 𝕜` via `VectorBundleCore.congrModel` and glued
across all summand-rank pairs via `VectorBundleCore.ofLocallyConstant`.

`continuous_mk_whitneySum_iff` characterizes continuity of maps into the reconstructed total space
`TotalSpace Unit (whitneySum A D).Fiber` by continuity of their two coordinate-block projections
into `TotalSpace Unit A.Fiber` and `TotalSpace Unit D.Fiber`. Neither compactness, separation,
paracompactness, nor boundedness of the ranks on `X` is needed, and `𝕜` need not be complete.

From this total-space universal property we obtain the four bicone morphisms (`whitneyFst`,
`whitneySnd`, `whitneyInl`, `whitneyInr`), the bilimit witness `whitneyBiconeIsBilimit`, the
`HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)` instance, concrete pairing (`whitneyLift`), copairing
(`whitneyDesc`), functorial action on morphisms and isomorphisms (`whitneyMap`, `whitneyMapIso`),
symmetry and associativity isomorphisms (`whitneyCommIso`, `whitneyAssocIso`), and the natural
homeomorphism `whitneySumTotalSpaceHomeomorph` between `TotalSpace Unit (whitneySum A D).Fiber`
and the fibered product `{pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
pq.1.proj = pq.2.proj}` over `X`.

## References

* M. F. Atiyah, *K-Theory*, §1.1–1.2.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Topology

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section Construction

/-- On the rank-`n` stratum of `A.rank + D.rank`, the pair of summand ranks `(A.rank x, D.rank x)`
is locally constant with values in `{p : ℕ × ℕ // p.1 + p.2 = n}`. -/
def rankSplit (A D : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    LocallyConstant {x : X // (A.rank + D.rank) x = n} {p : ℕ × ℕ // p.1 + p.2 = n} :=
  LocallyConstant.desc
    (fun x : {x : X // (A.rank + D.rank) x = n} => (⟨(A.rank x.1, D.rank x.1), x.2⟩ :
      {p : ℕ × ℕ // p.1 + p.2 = n}))
    ⟨fun x => (A.rank x.1, D.rank x.1),
      (A.rank.isLocallyConstant.prodMk D.rank.isLocallyConstant).comp_continuous
        continuous_subtype_val⟩
    rfl Subtype.val_injective

@[simp] theorem rankSplit_apply (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // (A.rank + D.rank) x = n}) :
    rankSplit A D n x = ⟨(A.rank x.1, D.rank x.1), x.2⟩ := (rfl)

/-- The Whitney sum of two variable-rank bundle atlases, glued on each total-rank stratum across
the locally constant refinement by summand-rank pairs. -/
-- Expose the rank projection so `(whitneySum A D).Fiber x` reduces to concatenated coordinates.
@[expose]
noncomputable def whitneySum (A D : FiniteRankAtlas 𝕜 X) : FiniteRankAtlas 𝕜 X where
  rank := A.rank + D.rank
  charts n :=
    VectorBundleCore.ofLocallyConstant (rankSplit A D n)
      (fun s =>
        ((FiniteRankBundleCore.whitneySum
          ((⟨s.1.1, A.charts s.1.1, A.indexAt_eq s.1.1⟩ :
              FiniteRankBundleCore 𝕜 {y : X // A.rank y = s.1.1}).pullback
            ⟨fun x => ⟨x.1.1,
              congrArg (fun q => q.1.1) ((rankSplit_apply A D n x.1).symm.trans x.2)⟩,
              (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩)
          ((⟨s.1.2, D.charts s.1.2, D.indexAt_eq s.1.2⟩ :
              FiniteRankBundleCore 𝕜 {y : X // D.rank y = s.1.2}).pullback
            ⟨fun x => ⟨x.1.1,
              congrArg (fun q => q.1.2) ((rankSplit_apply A D n x.1).symm.trans x.2)⟩,
              (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩)).core).congrModel
          (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr s.2)))
      (fun _ x => VectorBundleCore.indexAt_congrModel _ _ x)
  indexAt_eq _ := VectorBundleCore.indexAt_ofLocallyConstant _ _ _

@[simp] theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank := (rfl)

theorem rank_whitneySum_apply (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySum A D).rank x = A.rank x + D.rank x := (rfl)

/-- Split a coordinate vector in the Whitney-sum fibre over `x` into its pair of vectors in
`A.Fiber x` and `D.Fiber x`. -/
def whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySum A D).Fiber x ≃L[𝕜] A.Fiber x × D.Fiber x :=
  splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)

theorem whitneySumFiberEquiv_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A D x v = splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x) v := (rfl)

theorem whitneySumFiberEquiv_symm_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (w : A.Fiber x × D.Fiber x) :
    (whitneySumFiberEquiv A D x).symm w =
      (splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)).symm w := (rfl)

private theorem continuous_pullback_mk_iff {W Z Y : Type*} [TopologicalSpace W]
    [TopologicalSpace Z] [TopologicalSpace Y] (C : FiniteRankBundleCore 𝕜 Z) (f : C(W, Z))
    {g : Y → W} (hg : Continuous g) (v : Y → Fin C.rank → 𝕜) :
    Continuous (fun y => (⟨g y, v y⟩ : (C.pullback f).core.TotalSpace)) ↔
      Continuous (fun y => (⟨f (g y), v y⟩ : C.core.TotalSpace)) := by
  refine (C.pullbackHomeomorph f).comp_continuous_iff.symm.trans
    ((inducing_pullbackTotalSpaceEmbedding (Fin C.rank → 𝕜) C.core.Fiber f).continuous_iff.trans ?_)
  refine (continuous_congr fun y => ?_).trans ⟨fun h => h.snd, fun h => hg.prodMk h⟩
  dsimp only [Function.comp_apply]
  rw [C.pullbackHomeomorph_apply]
  rfl

private theorem continuous_core_whitneySum_mk_iff {W Y : Type*} [TopologicalSpace W]
    [TopologicalSpace Y] (C₁ C₂ : FiniteRankBundleCore 𝕜 W) {g : Y → W}
    (v : Y → Fin (C₁.rank + C₂.rank) → 𝕜) :
    Continuous (fun y =>
        (⟨g y, v y⟩ : (FiniteRankBundleCore.whitneySum C₁ C₂).core.TotalSpace)) ↔
      Continuous (fun y =>
        (⟨g y, (splitCoords (𝕜 := 𝕜) C₁.rank C₂.rank (v y)).1⟩ : C₁.core.TotalSpace)) ∧
      Continuous (fun y =>
        (⟨g y, (splitCoords (𝕜 := 𝕜) C₁.rank C₂.rank (v y)).2⟩ : C₂.core.TotalSpace)) := by
  refine (FiniteRankBundleCore.whitneySumTotalSpaceHomeomorph C₁ C₂).comp_continuous_iff.symm.trans
    ((FiberBundle.Prod.isInducing_diag (Fin C₁.rank → 𝕜) C₁.core.Fiber
      (Fin C₂.rank → 𝕜) C₂.core.Fiber).continuous_iff.trans ?_)
  refine (continuous_congr fun y => ?_).trans continuous_prodMk
  dsimp only [Function.comp_apply]
  rw [FiniteRankBundleCore.whitneySumTotalSpaceHomeomorph_apply,
    FiniteRankBundleCore.whitneySumFiberEquiv_apply]

private theorem continuous_mk_iff_rankPairStrata (C : FiniteRankAtlas 𝕜 X)
    (q : LocallyConstant X ℕ) {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (hb : Continuous b) (t : ∀ y, C.Fiber (b y)) :
    Continuous (fun y => (⟨b y, t y⟩ : TotalSpace Unit C.Fiber)) ↔
      ∀ c k : ℕ, Continuous (fun y : {y : Y // C.rank (b y) = c ∧ q (b y) = k} =>
        (⟨⟨b y.1, y.2.1⟩, fun i => t y.1 (Fin.cast y.2.1.symm i)⟩ :
          (C.charts c).TotalSpace)) := by
  rw [C.continuous_mk_iff_rankStrata hb t]
  refine forall_congr' fun c => ⟨fun hc k => ?_, fun hc => ?_⟩
  · exact hc.comp ((continuous_subtype_val :
      Continuous (Subtype.val : {y : Y // C.rank (b y) = c ∧ q (b y) = k} → Y)).subtype_mk
        fun y => y.2.1)
  · apply continuous_of_cover_nhds
      (s := fun k : ℕ => {y : {y : Y // C.rank (b y) = c} | q (b y.1) = k})
    · intro y
      exact ⟨q (b y.1),
        ((q.isLocallyConstant.isOpen_fiber _).preimage
          (hb.comp continuous_subtype_val)).mem_nhds rfl⟩
    · intro k
      rw [continuousOn_iff_continuous_domRestrict]
      exact (hc k).comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        fun y => ⟨y.1.2, y.2⟩)

private theorem splitCoords_cast_fst {a d n : ℕ} {m₁ m₂ : ℕ}
    (ha : m₁ = a) (hd : m₂ = d) (hr : a + d = n) (hn : m₁ + m₂ = n)
    (v : Fin (m₁ + m₂) → 𝕜) :
    (splitCoords (𝕜 := 𝕜) a d
      ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr hr)).symm
        (fun i => v (Fin.cast hn.symm i)))).1 =
      fun i => (splitCoords (𝕜 := 𝕜) m₁ m₂ v).1 (Fin.cast ha.symm i) := by
  subst ha
  subst hd
  subst hr
  rfl

private theorem splitCoords_cast_snd {a d n : ℕ} {m₁ m₂ : ℕ}
    (ha : m₁ = a) (hd : m₂ = d) (hr : a + d = n) (hn : m₁ + m₂ = n)
    (v : Fin (m₁ + m₂) → 𝕜) :
    (splitCoords (𝕜 := 𝕜) a d
      ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr hr)).symm
        (fun i => v (Fin.cast hn.symm i)))).2 =
      fun i => (splitCoords (𝕜 := 𝕜) m₁ m₂ v).2 (Fin.cast hd.symm i) := by
  subst ha
  subst hd
  subst hr
  rfl

private def rankSplitFst (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (s : {p : ℕ × ℕ // p.1 + p.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = s},
      {y : X // A.rank y = s.1.1}) :=
  ⟨fun x => ⟨x.1.1,
    congrArg (fun q => q.1.1) ((rankSplit_apply A D n x.1).symm.trans x.2)⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x =>
      congrArg (fun q => q.1.1) ((rankSplit_apply A D n x.1).symm.trans x.2)⟩

private def rankSplitSnd (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (s : {p : ℕ × ℕ // p.1 + p.2 = n}) :
    C({x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = s},
      {y : X // D.rank y = s.1.2}) :=
  ⟨fun x => ⟨x.1.1,
    congrArg (fun q => q.1.2) ((rankSplit_apply A D n x.1).symm.trans x.2)⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x =>
      congrArg (fun q => q.1.2) ((rankSplit_apply A D n x.1).symm.trans x.2)⟩

private theorem continuous_mk_whitneySum_stratum_iff (A D : FiniteRankAtlas 𝕜 X) (n : ℕ)
    {Y : Type*} [TopologicalSpace Y] {b : Y → {x : X // (A.rank + D.rank) x = n}}
    (hb : Continuous b) (v : Y → Fin n → 𝕜) :
    Continuous (fun y => (⟨b y, v y⟩ : ((whitneySum A D).charts n).TotalSpace)) ↔
      ∀ s : {p : ℕ × ℕ // p.1 + p.2 = n},
        Continuous (fun y : {y : Y // rankSplit A D n (b y) = s} =>
          (⟨⟨(b y.1).1,
              congrArg (fun q => q.1.1) ((rankSplit_apply A D n (b y.1)).symm.trans y.2)⟩,
            (splitCoords (𝕜 := 𝕜) s.1.1 s.1.2
              ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr s.2)).symm
                (v y.1))).1⟩ : (A.charts s.1.1).TotalSpace)) ∧
        Continuous (fun y : {y : Y // rankSplit A D n (b y) = s} =>
          (⟨⟨(b y.1).1,
              congrArg (fun q => q.1.2) ((rankSplit_apply A D n (b y.1)).symm.trans y.2)⟩,
            (splitCoords (𝕜 := 𝕜) s.1.1 s.1.2
              ((ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr s.2)).symm
                (v y.1))).2⟩ : (D.charts s.1.2).TotalSpace)) := by
  let coreA : ∀ a : ℕ, FiniteRankBundleCore 𝕜 {y : X // A.rank y = a} :=
    fun a => ⟨a, A.charts a, A.indexAt_eq a⟩
  let coreD : ∀ d : ℕ, FiniteRankBundleCore 𝕜 {y : X // D.rank y = d} :=
    fun d => ⟨d, D.charts d, D.indexAt_eq d⟩
  let e : ∀ s : {p : ℕ × ℕ // p.1 + p.2 = n},
      (Fin (s.1.1 + s.1.2) → 𝕜) ≃L[𝕜] (Fin n → 𝕜) :=
    fun s => ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n => 𝕜) (finCongr s.2)
  let W : ∀ s : {p : ℕ × ℕ // p.1 + p.2 = n},
      FiniteRankBundleCore 𝕜
        {x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = s} :=
    fun s => FiniteRankBundleCore.whitneySum
      ((coreA s.1.1).pullback (rankSplitFst A D n s))
      ((coreD s.1.2).pullback (rankSplitSnd A D n s))
  refine (VectorBundleCore.continuous_mk_ofLocallyConstant_iff (rankSplit A D n)
    (fun s => (W s).core.congrModel (e s))
    (fun s x => VectorBundleCore.indexAt_congrModel (W s).core (e s) x) hb v).trans
      (forall_congr' fun s => ?_)
  have hbase : Continuous (fun y : {y : Y // rankSplit A D n (b y) = s} =>
      (⟨b y.1, y.2⟩ : {x : {x : X // (A.rank + D.rank) x = n} // rankSplit A D n x = s})) :=
    (hb.comp continuous_subtype_val).subtype_mk fun y => y.2
  exact (VectorBundleCore.continuous_mk_congrModel_iff
    (b := fun y : {y : Y // rankSplit A D n (b y) = s} => ⟨b y.1, y.2⟩)
    (s := fun y => v y.1) (W s).core (e s)).trans
    ((continuous_core_whitneySum_mk_iff
      ((coreA s.1.1).pullback (rankSplitFst A D n s))
      ((coreD s.1.2).pullback (rankSplitSnd A D n s))
      (g := fun y : {y : Y // rankSplit A D n (b y) = s} => ⟨b y.1, y.2⟩)
      (fun y => (e s).symm (v y.1))).trans
      (and_congr
        (continuous_pullback_mk_iff (coreA s.1.1) (rankSplitFst A D n s) hbase
          (fun y => (splitCoords (𝕜 := 𝕜) s.1.1 s.1.2 ((e s).symm (v y.1))).1))
        (continuous_pullback_mk_iff (coreD s.1.2) (rankSplitSnd A D n s) hbase
          (fun y => (splitCoords (𝕜 := 𝕜) s.1.1 s.1.2 ((e s).symm (v y.1))).2))))

private theorem continuous_blocks_of_continuous_mk_whitneySum {A D : FiniteRankAtlas 𝕜 X}
    {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (s : ∀ y, (whitneySum A D).Fiber (b y))
    (hs : Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit (whitneySum A D).Fiber))) :
    Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).1⟩ : TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).2⟩ : TotalSpace Unit D.Fiber)) := by
  have hb : Continuous b := (whitneySum A D).continuous_proj.comp hs
  have hstrata := ((whitneySum A D).continuous_mk_iff_rankStrata hb s).mp hs
  rw [continuous_mk_iff_rankPairStrata A D.rank hb,
    continuous_mk_iff_rankPairStrata D A.rank hb]
  refine ⟨fun a d => ?_, fun d a => ?_⟩
  · have hn : ∀ y : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d},
        (A.rank + D.rank) (b y.1) = a + d :=
      fun y => by simp only [LocallyConstant.coe_add, Pi.add_apply, y.2.1, y.2.2]
    have hr := ((continuous_mk_whitneySum_stratum_iff A D (a + d)
      ((hb.comp continuous_subtype_val).subtype_mk fun y => y.2)
      (fun y i => s y.1 (Fin.cast y.2.symm i))).mp (hstrata (a + d)) ⟨(a, d), rfl⟩).1
    let emb : {y : Y // A.rank (b y) = a ∧ D.rank (b y) = d} →
        {z : {y : Y // (A.rank + D.rank) (b y) = a + d} //
          rankSplit A D (a + d) ⟨b z.1, z.2⟩ = ⟨(a, d), rfl⟩} :=
      fun y => ⟨⟨y.1, hn y⟩, Subtype.ext (Prod.ext y.2.1 y.2.2)⟩
    refine (hr.comp ((continuous_subtype_val.subtype_mk hn).subtype_mk _ : Continuous emb)).congr
      fun y => congrArg
        (TotalSpace.mk' (Fin a → 𝕜) (⟨b y.1, y.2.1⟩ : {x : X // A.rank x = a}))
        (splitCoords_cast_fst y.2.1 y.2.2 rfl (hn y) (s y.1))
  · have hn : ∀ y : {y : Y // D.rank (b y) = d ∧ A.rank (b y) = a},
        (A.rank + D.rank) (b y.1) = a + d :=
      fun y => by simp only [LocallyConstant.coe_add, Pi.add_apply, y.2.2, y.2.1]
    have hr := ((continuous_mk_whitneySum_stratum_iff A D (a + d)
      ((hb.comp continuous_subtype_val).subtype_mk fun y => y.2)
      (fun y i => s y.1 (Fin.cast y.2.symm i))).mp (hstrata (a + d)) ⟨(a, d), rfl⟩).2
    let emb : {y : Y // D.rank (b y) = d ∧ A.rank (b y) = a} →
        {z : {y : Y // (A.rank + D.rank) (b y) = a + d} //
          rankSplit A D (a + d) ⟨b z.1, z.2⟩ = ⟨(a, d), rfl⟩} :=
      fun y => ⟨⟨y.1, hn y⟩, Subtype.ext (Prod.ext y.2.2 y.2.1)⟩
    refine (hr.comp ((continuous_subtype_val.subtype_mk hn).subtype_mk _ : Continuous emb)).congr
      fun y => congrArg
        (TotalSpace.mk' (Fin d → 𝕜) (⟨b y.1, y.2.1⟩ : {x : X // D.rank x = d}))
        (splitCoords_cast_snd y.2.2 y.2.1 rfl (hn y) (s y.1))

private theorem continuous_mk_whitneySum_of_continuous_blocks {A D : FiniteRankAtlas 𝕜 X}
    {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (s : ∀ y, (whitneySum A D).Fiber (b y))
    (hs : Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).1⟩ : TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).2⟩ : TotalSpace Unit D.Fiber))) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit (whitneySum A D).Fiber)) := by
  rcases hs with ⟨hsA, hsD⟩
  have hb : Continuous b := A.continuous_proj.comp hsA
  have hA := (continuous_mk_iff_rankPairStrata A D.rank hb _).mp hsA
  have hD := (continuous_mk_iff_rankPairStrata D A.rank hb _).mp hsD
  refine ((whitneySum A D).continuous_mk_iff_rankStrata hb s).mpr fun n => ?_
  refine (continuous_mk_whitneySum_stratum_iff A D n
    ((hb.comp continuous_subtype_val).subtype_mk fun y => y.2)
    (fun y i => s y.1 (Fin.cast y.2.symm i))).mpr fun r => ⟨?_, ?_⟩
  · let projA : {z : {y : Y // (A.rank + D.rank) (b y) = n} //
        rankSplit A D n ⟨b z.1, z.2⟩ = r} →
        {y : Y // A.rank (b y) = r.1.1 ∧ D.rank (b y) = r.1.2} :=
      fun z => ⟨z.1.1, congrArg (fun q => q.1.1) z.2, congrArg (fun q => q.1.2) z.2⟩
    refine ((hA r.1.1 r.1.2).comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ :
        Continuous projA)).congr fun z =>
      congrArg (TotalSpace.mk' (Fin r.1.1 → 𝕜)
        (⟨b z.1.1, congrArg (fun q => q.1.1) z.2⟩ : {x : X // A.rank x = r.1.1}))
        (splitCoords_cast_fst (congrArg (fun q => q.1.1) z.2)
          (congrArg (fun q => q.1.2) z.2) r.2 z.1.2 (s z.1.1)).symm
  · let projD : {z : {y : Y // (A.rank + D.rank) (b y) = n} //
        rankSplit A D n ⟨b z.1, z.2⟩ = r} →
        {y : Y // D.rank (b y) = r.1.2 ∧ A.rank (b y) = r.1.1} :=
      fun z => ⟨z.1.1, congrArg (fun q => q.1.2) z.2, congrArg (fun q => q.1.1) z.2⟩
    refine ((hD r.1.2 r.1.1).comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ :
        Continuous projD)).congr fun z =>
      congrArg (TotalSpace.mk' (Fin r.1.2 → 𝕜)
        (⟨b z.1.1, congrArg (fun q => q.1.2) z.2⟩ : {x : X // D.rank x = r.1.2}))
        (splitCoords_cast_snd (congrArg (fun q => q.1.1) z.2)
          (congrArg (fun q => q.1.2) z.2) r.2 z.1.2 (s z.1.1)).symm

/-- A map into the reconstructed total space of `whitneySum A D` is continuous if and only if
both coordinate-block projections into the total spaces of `A` and `D` are continuous. -/
theorem continuous_mk_whitneySum_iff {A D : FiniteRankAtlas 𝕜 X}
    {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (s : ∀ y, (whitneySum A D).Fiber (b y)) :
    Continuous (fun y => (⟨b y, s y⟩ : TotalSpace Unit (whitneySum A D).Fiber)) ↔
      Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).1⟩ : TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y =>
        (⟨b y, (whitneySumFiberEquiv A D (b y) (s y)).2⟩ : TotalSpace Unit D.Fiber)) :=
  ⟨continuous_blocks_of_continuous_mk_whitneySum s,
    continuous_mk_whitneySum_of_continuous_blocks s⟩

end Construction

section Bicone

/-- Projection of the Whitney sum onto its first variable-rank bundle atlas. -/
noncomputable def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A where
  fiberMap x :=
    (LinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp (whitneySumFiberEquiv A D x).toLinearMap
  continuous_totalSpaceMap :=
    ((continuous_mk_whitneySum_iff (b := TotalSpace.proj) (fun p => p.2)).mp continuous_id).1

/-- Projection of the Whitney sum onto its second variable-rank bundle atlas. -/
noncomputable def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D where
  fiberMap x :=
    (LinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp (whitneySumFiberEquiv A D x).toLinearMap
  continuous_totalSpaceMap :=
    ((continuous_mk_whitneySum_iff (b := TotalSpace.proj) (fun p => p.2)).mp continuous_id).2

/-- Inclusion of the first variable-rank bundle atlas into the Whitney sum. -/
noncomputable def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D where
  fiberMap x :=
    (whitneySumFiberEquiv A D x).symm.toLinearMap.comp (LinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))
  continuous_totalSpaceMap := by
    apply (continuous_mk_whitneySum_iff (b := TotalSpace.proj) _).mpr
    refine ⟨continuous_id.congr fun p => ?_,
      (D.continuous_zeroSection.comp A.continuous_proj).congr fun p => ?_⟩
    · rcases p with ⟨x, u⟩
      exact congrArg (fun w : A.Fiber x × D.Fiber x => (⟨x, w.1⟩ : TotalSpace Unit A.Fiber))
        ((whitneySumFiberEquiv A D x).apply_symm_apply (u, 0)).symm
    · rcases p with ⟨x, u⟩
      exact congrArg (fun w : A.Fiber x × D.Fiber x => (⟨x, w.2⟩ : TotalSpace Unit D.Fiber))
        ((whitneySumFiberEquiv A D x).apply_symm_apply (u, 0)).symm

/-- Inclusion of the second variable-rank bundle atlas into the Whitney sum. -/
noncomputable def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D where
  fiberMap x :=
    (whitneySumFiberEquiv A D x).symm.toLinearMap.comp (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))
  continuous_totalSpaceMap := by
    apply (continuous_mk_whitneySum_iff (b := TotalSpace.proj) _).mpr
    refine ⟨(A.continuous_zeroSection.comp D.continuous_proj).congr fun p => ?_,
      continuous_id.congr fun p => ?_⟩
    · rcases p with ⟨x, w⟩
      exact congrArg (fun q : A.Fiber x × D.Fiber x => (⟨x, q.1⟩ : TotalSpace Unit A.Fiber))
        ((whitneySumFiberEquiv A D x).apply_symm_apply (0, w)).symm
    · rcases p with ⟨x, w⟩
      exact congrArg (fun q : A.Fiber x × D.Fiber x => (⟨x, q.2⟩ : TotalSpace Unit D.Fiber))
        ((whitneySumFiberEquiv A D x).apply_symm_apply (0, w)).symm

/-- The first projection extracts the first coordinate block in every fibre. -/
@[simp] theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyFst A D).fiberMap x =
      (LinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp (whitneySumFiberEquiv A D x).toLinearMap :=
  (rfl)

/-- The second projection extracts the second coordinate block in every fibre. -/
@[simp] theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySnd A D).fiberMap x =
      (LinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp (whitneySumFiberEquiv A D x).toLinearMap :=
  (rfl)

/-- The first inclusion appends a zero block in every fibre. -/
@[simp] theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInl A D).fiberMap x =
      (whitneySumFiberEquiv A D x).symm.toLinearMap.comp
        (LinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x)) :=
  (rfl)

/-- The second inclusion prepends a zero block in every fibre. -/
@[simp] theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInr A D).fiberMap x =
      (whitneySumFiberEquiv A D x).symm.toLinearMap.comp
        (LinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x)) :=
  (rfl)

@[reassoc (attr := simp)] theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro u
  simp only [fiberMap_comp, fiberMap_whitneyFst, fiberMap_whitneyInl, fiberMap_id,
    LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply,
    LinearMap.fst_apply, LinearMap.id_apply]

@[reassoc (attr := simp)] theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro u
  simp only [fiberMap_comp, fiberMap_whitneySnd, fiberMap_whitneyInl, fiberMap_zero,
    LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply,
    LinearMap.snd_apply, LinearMap.zero_apply]

@[reassoc (attr := simp)] theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro w
  simp only [fiberMap_comp, fiberMap_whitneyFst, fiberMap_whitneyInr, fiberMap_zero,
    LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply,
    LinearMap.fst_apply, LinearMap.zero_apply]

@[reassoc (attr := simp)] theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro w
  simp only [fiberMap_comp, fiberMap_whitneySnd, fiberMap_whitneyInr, fiberMap_id,
    LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply,
    LinearMap.snd_apply, LinearMap.id_apply]

/-- The Whitney sum of variable-rank bundle atlases together with its four canonical maps. -/
-- Expose the apex projection so the types of the four legs reduce to `whitneySum A D`.
@[expose]
noncomputable def whitneyBicone (A D : FiniteRankAtlas 𝕜 X) : BinaryBicone A D where
  pt := whitneySum A D
  fst := whitneyFst A D
  snd := whitneySnd A D
  inl := whitneyInl A D
  inr := whitneyInr A D
  inl_fst := whitneyInl_fst A D
  inl_snd := whitneyInl_snd A D
  inr_fst := whitneyInr_fst A D
  inr_snd := whitneyInr_snd A D

@[simp] theorem whitneyBicone_pt (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).pt = whitneySum A D := (rfl)

@[simp] theorem whitneyBicone_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).fst = whitneyFst A D := (rfl)

@[simp] theorem whitneyBicone_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).snd = whitneySnd A D := (rfl)

@[simp] theorem whitneyBicone_inl (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inl = whitneyInl A D := (rfl)

@[simp] theorem whitneyBicone_inr (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inr = whitneyInr A D := (rfl)

/-- The two coordinate-block projections and inclusions resolve the identity on `whitneySum A D`. -/
@[simp] theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  simp only [fiberMap_add, fiberMap_comp, fiberMap_id, fiberMap_whitneyFst, fiberMap_whitneySnd,
    fiberMap_whitneyInl, fiberMap_whitneyInr, LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.id_apply]
  rw [← map_add, Prod.fst_add_snd]
  exact (whitneySumFiberEquiv A D x).symm_apply_apply v

/-- The geometric Whitney sum of variable-rank bundle atlases is a binary biproduct bilimit. -/
noncomputable def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

/-- Variable-rank bundle atlases have binary biproducts given by Whitney sums. -/
instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

end Bicone

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two morphisms of variable-rank bundle atlases with common source into `whitneySum A D`. -/
noncomputable def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

theorem whitneyLift_def (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g = f ≫ whitneyInl A D + g ≫ whitneyInr A D := (rfl)

@[reassoc (attr := simp)]
theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

@[reassoc (attr := simp)]
theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneySnd A D = g := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Every morphism into a Whitney sum is the pairing of its two projections. -/
theorem eq_whitneyLift (h : E ⟶ whitneySum A D) :
    h = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
  calc
    h = h ≫ 𝟙 (whitneySum A D) := (Category.comp_id h).symm
    _ = h ≫ (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) := by
      rw [whitney_total]
    _ = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
      simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

/-- Morphisms into a Whitney sum are determined by their two projections. -/
theorem whitneySum_hom_ext {h₁ h₂ : E ⟶ whitneySum A D}
    (hfst : h₁ ≫ whitneyFst A D = h₂ ≫ whitneyFst A D)
    (hsnd : h₁ ≫ whitneySnd A D = h₂ ≫ whitneySnd A D) : h₁ = h₂ := by
  rw [eq_whitneyLift h₁, eq_whitneyLift h₂, hfst, hsnd]

@[reassoc]
theorem comp_whitneyLift (h : C ⟶ E) (f : E ⟶ A) (g : E ⟶ D) :
    h ≫ whitneyLift f g = whitneyLift (h ≫ f) (h ≫ g) := by
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

@[simp]
theorem whitneyLift_fst_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (whitneyFst A D) (whitneySnd A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem whitneyLift_zero (E A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (0 : E ⟶ A) (0 : E ⟶ D) = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyLift_add (f₁ f₂ : E ⟶ A) (g₁ g₂ : E ⟶ D) :
    whitneyLift (f₁ + f₂) (g₁ + g₂) = whitneyLift f₁ g₁ + whitneyLift f₂ g₂ :=
  whitneySum_hom_ext (by simp [Preadditive.add_comp]) (by simp [Preadditive.add_comp])

@[simp]
theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) :
    (whitneyLift f g).fiberMap x =
      (whitneySumFiberEquiv A D x).symm.toLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  apply LinearMap.ext
  intro v
  simp only [whitneyLift, fiberMap_add, fiberMap_comp, fiberMap_whitneyInl, fiberMap_whitneyInr,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.coe_prod, Function.prod_apply, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]

theorem whitneySumFiberEquiv_fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X)
    (v : E.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyLift f g).fiberMap x v) =
      (f.fiberMap x v, g.fiberMap x v) := by
  rw [LinearMap.congr_fun (fiberMap_whitneyLift f g x) v]
  exact (whitneySumFiberEquiv A D x).apply_symm_apply (f.fiberMap x v, g.fiberMap x v)

/-- Copair two morphisms of variable-rank bundle atlases with common target out of
`whitneySum A D`. -/
noncomputable def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

theorem whitneyDesc_def (f : A ⟶ E) (g : D ⟶ E) :
    whitneyDesc f g = whitneyFst A D ≫ f + whitneySnd A D ≫ g := (rfl)

@[reassoc (attr := simp)]
theorem whitneyInl_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInl A D ≫ whitneyDesc f g = f := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyInr_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInr A D ≫ whitneyDesc f g = g := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyLift_desc (f : E ⟶ A) (g : E ⟶ D) (h : A ⟶ C) (k : D ⟶ C) :
    whitneyLift f g ≫ whitneyDesc h k = f ≫ h + g ≫ k := by
  simp [whitneyLift, whitneyDesc, Preadditive.add_comp, Preadditive.comp_add]

/-- Every morphism out of a Whitney sum is the copairing of its two summand restrictions. -/
theorem eq_whitneyDesc (h : whitneySum A D ⟶ E) :
    h = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
  calc
    h = 𝟙 (whitneySum A D) ≫ h := (Category.id_comp h).symm
    _ = (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) ≫ h := by
      rw [whitney_total]
    _ = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
      simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

/-- Morphisms out of a Whitney sum are determined by their restrictions to the two summands. -/
theorem whitneySum_hom_ext' {h₁ h₂ : whitneySum A D ⟶ E}
    (hinl : whitneyInl A D ≫ h₁ = whitneyInl A D ≫ h₂)
    (hinr : whitneyInr A D ≫ h₁ = whitneyInr A D ≫ h₂) : h₁ = h₂ := by
  rw [eq_whitneyDesc h₁, eq_whitneyDesc h₂, hinl, hinr]

@[reassoc]
theorem whitneyDesc_comp (f : A ⟶ E) (g : D ⟶ E) (h : E ⟶ C) :
    whitneyDesc f g ≫ h = whitneyDesc (f ≫ h) (g ≫ h) := by
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

@[simp]
theorem whitneyDesc_inl_inr (A D : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (whitneyInl A D) (whitneyInr A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem whitneyDesc_zero (A D E : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (0 : A ⟶ E) (0 : D ⟶ E) = 0 :=
  whitneySum_hom_ext' (by simp) (by simp)

@[simp]
theorem whitneyDesc_add (f₁ f₂ : A ⟶ E) (g₁ g₂ : D ⟶ E) :
    whitneyDesc (f₁ + f₂) (g₁ + g₂) = whitneyDesc f₁ g₁ + whitneyDesc f₂ g₂ :=
  whitneySum_hom_ext' (by simp [Preadditive.comp_add]) (by simp [Preadditive.comp_add])

@[simp]
theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : X) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (whitneySumFiberEquiv A D x).toLinearMap := by
  apply LinearMap.ext
  intro v
  rfl

theorem fiberMap_whitneyDesc_apply (f : A ⟶ E) (g : D ⟶ E) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyDesc f g).fiberMap x v =
      f.fiberMap x (whitneySumFiberEquiv A D x v).1 +
        g.fiberMap x (whitneySumFiberEquiv A D x v).2 :=
  (rfl)

/-- Direct sum of two morphisms of variable-rank bundle atlases on Whitney sums. -/
noncomputable def whitneyMap (f : A ⟶ A') (g : D ⟶ D') : whitneySum A D ⟶ whitneySum A' D' :=
  whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g)

theorem whitneyMap_def (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g = whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g) := (rfl)

@[reassoc (attr := simp)]
theorem whitneyMap_fst (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneyFst A' D' = whitneyFst A D ≫ f :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem whitneyMap_snd (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneySnd A' D' = whitneySnd A D ≫ g :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem whitneyInl_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInl A D ≫ whitneyMap f g = f ≫ whitneyInl A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[reassoc (attr := simp)]
theorem whitneyInr_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInr A D ≫ whitneyMap f g = g ≫ whitneyInr A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_id (A D : FiniteRankAtlas 𝕜 X) :
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) := by
  simp [whitneyMap_def]

@[simp]
theorem whitneyMap_zero (A A' D D' : FiniteRankAtlas 𝕜 X) :
    whitneyMap (0 : A ⟶ A') (0 : D ⟶ D') = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_add (f₁ f₂ : A ⟶ A') (g₁ g₂ : D ⟶ D') :
    whitneyMap (f₁ + f₂) (g₁ + g₂) = whitneyMap f₁ g₁ + whitneyMap f₂ g₂ :=
  whitneySum_hom_ext
    (by simp [Preadditive.add_comp, Preadditive.comp_add])
    (by simp [Preadditive.add_comp, Preadditive.comp_add])

@[simp]
theorem whitneyMap_comp (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) = whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X) :
    (whitneyMap f g).fiberMap x =
      (whitneySumFiberEquiv A' D' x).symm.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (whitneySumFiberEquiv A D x).toLinearMap) := by
  apply LinearMap.ext
  intro v
  simp only [whitneyMap, fiberMap_whitneyLift, fiberMap_comp, fiberMap_whitneyFst,
    fiberMap_whitneySnd, LinearMap.comp_apply, LinearMap.coe_prod, Function.prod_apply,
    LinearMap.prodMap_apply, LinearMap.fst_apply, LinearMap.snd_apply]

theorem whitneySumFiberEquiv_fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A' D' x ((whitneyMap f g).fiberMap x v) =
      (f.fiberMap x (whitneySumFiberEquiv A D x v).1,
        g.fiberMap x (whitneySumFiberEquiv A D x v).2) := by
  rw [LinearMap.congr_fun (fiberMap_whitneyMap f g x) v]
  exact (whitneySumFiberEquiv A' D' x).apply_symm_apply _

/-- Direct sum of two variable-rank bundle atlas isomorphisms. -/
noncomputable def whitneyMapIso (e₁ : A ≅ A') (e₂ : D ≅ D') :
    whitneySum A D ≅ whitneySum A' D' where
  hom := whitneyMap e₁.hom e₂.hom
  inv := whitneyMap e₁.inv e₂.inv
  hom_inv_id := by rw [← whitneyMap_comp, e₁.hom_inv_id, e₂.hom_inv_id, whitneyMap_id]
  inv_hom_id := by rw [← whitneyMap_comp, e₁.inv_hom_id, e₂.inv_hom_id, whitneyMap_id]

@[simp]
theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom := (rfl)

@[simp]
theorem whitneyMapIso_inv (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).inv = whitneyMap e₁.inv e₂.inv := (rfl)

@[simp]
theorem whitneyMapIso_refl (A D : FiniteRankAtlas 𝕜 X) :
    whitneyMapIso (Iso.refl A) (Iso.refl D) = Iso.refl (whitneySum A D) := by
  ext
  simp

@[simp]
theorem whitneyMapIso_symm (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).symm = whitneyMapIso e₁.symm e₂.symm := (rfl)

@[simp]
theorem whitneyMapIso_trans (e₁ : A ≅ A') (e₁' : A' ≅ A'') (e₂ : D ≅ D') (e₂' : D' ≅ D'') :
    (whitneyMapIso e₁ e₂).trans (whitneyMapIso e₁' e₂') =
      whitneyMapIso (e₁.trans e₁') (e₂.trans e₂') := by
  ext
  simp

end UniversalProperty

section Coherence

/-- Symmetry isomorphism exchanging the two summands of a variable-rank Whitney sum. -/
noncomputable def whitneyCommIso (A D : FiniteRankAtlas 𝕜 X) :
    whitneySum A D ≅ whitneySum D A where
  hom := whitneyLift (whitneySnd A D) (whitneyFst A D)
  inv := whitneyLift (whitneySnd D A) (whitneyFst D A)
  hom_inv_id := whitneySum_hom_ext (by simp) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyCommIso_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).hom = whitneyLift (whitneySnd A D) (whitneyFst A D) := (rfl)

@[simp]
theorem whitneyCommIso_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).inv = whitneyLift (whitneySnd D A) (whitneyFst D A) := (rfl)

@[simp]
theorem whitneyCommIso_symm (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).symm = whitneyCommIso D A := (rfl)

@[reassoc]
theorem whitneyMap_commIso_hom {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ (whitneyCommIso A' D').hom =
      (whitneyCommIso A D).hom ≫ whitneyMap g f :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Associativity isomorphism regrouping a threefold variable-rank Whitney sum. -/
noncomputable def whitneyAssocIso (A D C : FiniteRankAtlas 𝕜 X) :
    whitneySum (whitneySum A D) C ≅ whitneySum A (whitneySum D C) where
  hom := whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
    (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _))
  inv := whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
    (whitneySnd _ _ ≫ whitneySnd D C)
  hom_inv_id := whitneySum_hom_ext (whitneySum_hom_ext (by simp) (by simp)) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

@[simp]
theorem whitneyAssocIso_hom (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).hom =
      whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _)) := (rfl)

@[simp]
theorem whitneyAssocIso_inv (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).inv =
      whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C) := (rfl)

@[reassoc]
theorem whitneyMap_assocIso_hom {A A' D D' C C' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (h : C ⟶ C') :
    whitneyMap (whitneyMap f g) h ≫ (whitneyAssocIso A' D' C').hom =
      (whitneyAssocIso A D C).hom ≫ whitneyMap f (whitneyMap g h) :=
  whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

end Coherence

section FiberedProduct

/-- Under `whitneySumFiberEquiv`, the two components of a Whitney-sum vector are the images under
`whitneyFst` and `whitneySnd`. -/
theorem fst_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).1 = (whitneyFst A D).fiberMap x v := (rfl)

theorem snd_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).2 = (whitneySnd A D).fiberMap x v := (rfl)

theorem whitneySumFiberEquiv_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) (u : A.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInl A D).fiberMap x u) = (u, 0) :=
  (whitneySumFiberEquiv A D x).apply_symm_apply (u, 0)

theorem whitneySumFiberEquiv_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) (w : D.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInr A D).fiberMap x w) = (0, w) :=
  (whitneySumFiberEquiv A D x).apply_symm_apply (0, w)

private theorem whitneySumTotalSpace_inv_mk {A D : FiniteRankAtlas 𝕜 X}
    {q : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}}
    {x : X} {u : A.Fiber x} {w : D.Fiber x}
    (hq₁ : q.1.1 = ⟨x, u⟩) (hq₂ : q.1.2 = ⟨x, w⟩) :
    (⟨q.1.1.proj,
      (whitneySumFiberEquiv A D q.1.1.proj).symm (q.1.1.2, q.2 ▸ q.1.2.2)⟩ :
        TotalSpace Unit (whitneySum A D).Fiber) =
      ⟨x, (whitneySumFiberEquiv A D x).symm (u, w)⟩ := by
  rcases q with ⟨⟨p₁, p₂⟩, h⟩
  dsimp only at hq₁ hq₂ ⊢
  subst hq₁
  subst hq₂
  cases h
  rfl

/-- The reconstructed total space of `whitneySum A D` is homeomorphic to the fibered product of
`TotalSpace Unit A.Fiber` and `TotalSpace Unit D.Fiber` over `X`, via `(whitneyFst, whitneySnd)`
in the forward direction and `whitneySumFiberEquiv.symm` on each fibre in the inverse direction. -/
noncomputable def whitneySumTotalSpaceHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} where
  toFun p := ⟨((whitneyFst A D).totalSpaceMap p, (whitneySnd A D).totalSpaceMap p),
    ((whitneyFst A D).proj_totalSpaceMap p).trans ((whitneySnd A D).proj_totalSpaceMap p).symm⟩
  invFun q :=
    ⟨q.1.1.proj, (whitneySumFiberEquiv A D q.1.1.proj).symm (q.1.1.2, q.2 ▸ q.1.2.2)⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    exact (whitneySumTotalSpace_inv_mk
      (Hom.totalSpaceMap_mk (whitneyFst A D) x v)
      (Hom.totalSpaceMap_mk (whitneySnd A D) x v)).trans
      (congrArg (TotalSpace.mk' Unit x) ((whitneySumFiberEquiv A D x).symm_apply_apply v))
  right_inv := by
    rintro ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
    cases h
    apply Subtype.ext
    dsimp only
    rw [Hom.totalSpaceMap_mk, Hom.totalSpaceMap_mk]
    have heq := (whitneySumFiberEquiv A D x₁).apply_symm_apply (u, w)
    exact Prod.ext
      (congrArg (TotalSpace.mk' Unit x₁) (congrArg Prod.fst heq))
      (congrArg (TotalSpace.mk' Unit x₁) (congrArg Prod.snd heq))
  continuous_toFun :=
    ((whitneyFst A D).totalSpaceMap.continuous.prodMk
      (whitneySnd A D).totalSpaceMap.continuous).subtype_mk _
  continuous_invFun := by
    refine (continuous_mk_whitneySum_iff
      (b := fun q : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
        pq.1.proj = pq.2.proj} => q.1.1.proj)
      (fun q => (whitneySumFiberEquiv A D q.1.1.proj).symm (q.1.1.2, q.2 ▸ q.1.2.2))).mpr ?_
    refine ⟨(continuous_fst.comp continuous_subtype_val).congr ?_,
      (continuous_snd.comp continuous_subtype_val).congr ?_⟩
    · rintro ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
      cases h
      exact congrArg (fun p : A.Fiber x₁ × D.Fiber x₁ => (⟨x₁, p.1⟩ : TotalSpace Unit A.Fiber))
        ((whitneySumFiberEquiv A D x₁).apply_symm_apply (u, w)).symm
    · rintro ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, h⟩
      cases h
      exact congrArg (fun p : A.Fiber x₁ × D.Fiber x₁ => (⟨x₁, p.2⟩ : TotalSpace Unit D.Fiber))
        ((whitneySumFiberEquiv A D x₁).apply_symm_apply (u, w)).symm

@[simp]
theorem whitneySumTotalSpaceHomeomorph_apply_fst (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    (whitneySumTotalSpaceHomeomorph A D p).1.1 = (whitneyFst A D).totalSpaceMap p := (rfl)

@[simp]
theorem whitneySumTotalSpaceHomeomorph_apply_snd (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    (whitneySumTotalSpaceHomeomorph A D p).1.2 = (whitneySnd A D).totalSpaceMap p := (rfl)

@[simp]
theorem proj_whitneySumTotalSpaceHomeomorph_symm (A D : FiniteRankAtlas 𝕜 X)
    (q : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) :
    ((whitneySumTotalSpaceHomeomorph A D).symm q).proj = q.1.1.proj := (rfl)

@[simp]
theorem totalSpaceMap_whitneyFst_symm (A D : FiniteRankAtlas 𝕜 X)
    (q : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) :
    (whitneyFst A D).totalSpaceMap ((whitneySumTotalSpaceHomeomorph A D).symm q) = q.1.1 :=
  congrArg (fun r => r.1.1) ((whitneySumTotalSpaceHomeomorph A D).apply_symm_apply q)

@[simp]
theorem totalSpaceMap_whitneySnd_symm (A D : FiniteRankAtlas 𝕜 X)
    (q : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) :
    (whitneySnd A D).totalSpaceMap ((whitneySumTotalSpaceHomeomorph A D).symm q) = q.1.2 :=
  congrArg (fun r => r.1.2) ((whitneySumTotalSpaceHomeomorph A D).apply_symm_apply q)

/-- `whitneySumTotalSpaceHomeomorph` intertwines `whitneyMap f g` with the componentwise action of
`f.totalSpaceMap` and `g.totalSpaceMap` on the fibered product over `X`. -/
theorem whitneySumTotalSpaceHomeomorph_naturality {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨(f.totalSpaceMap (whitneySumTotalSpaceHomeomorph A D p).1.1,
        g.totalSpaceMap (whitneySumTotalSpaceHomeomorph A D p).1.2), by simp⟩ := by
  apply Subtype.ext
  simp only [whitneySumTotalSpaceHomeomorph_apply_fst, whitneySumTotalSpaceHomeomorph_apply_snd]
  refine Prod.ext ?_ ?_
  · exact (DFunLike.congr_fun (totalSpaceMap_comp _ _) p).symm.trans
      ((congrArg (fun h => h.totalSpaceMap p) (whitneyMap_fst f g)).trans
        (DFunLike.congr_fun (totalSpaceMap_comp _ _) p))
  · exact (DFunLike.congr_fun (totalSpaceMap_comp _ _) p).symm.trans
      ((congrArg (fun h => h.totalSpaceMap p) (whitneyMap_snd f g)).trans
        (DFunLike.congr_fun (totalSpaceMap_comp _ _) p))

end FiberedProduct

end TauCeti.FiniteRankAtlas
