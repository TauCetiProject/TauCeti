/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.RootSum
public import TauCeti.Geometry.Manifold.SymmetricPower
public import TauCeti.Topology.PiCurry.Analytic

/-!
# Holomorphic transitions between elementary-symmetric charts

An elementary-symmetric chart on `Sym^n X` separates a tuple into finitely many blocks lying in
disjoint coordinate patches of `X`, and records each block by the elementary symmetric functions of
its points read in the patch coordinate. Two such charts may separate a tuple into blocks in
different ways. Where both are defined, a change from one to the other regroups the points: a block
of the target chart collects, from every block of the source chart, the points that lie in its
patch, applies the change of surface coordinate to them, and takes their elementary symmetric
functions.

This file proves that this transition is holomorphic. The analytic input is
`TauCeti.Sym.analyticAt_sum_map_filter_coeffEquiv_symm`: sums of a holomorphic function over the
roots of a monic polynomial lying in a region depend analytically on the coefficients, colliding
roots included. Applied to the power sums of the points of one target block, and combined with
Newton's identities, it shows that each target block of coordinates is analytic in the source
coordinates. Repeated points are included throughout. The regularity claims assume that, for every
point `z` of a tuple lying in both chart sources, and for every source patch `V i` and target
patch `W j` containing `z`, the change of surface coordinate `fun w : ℂ => ψ j ((φ i).symm w)` is
analytic at `φ i z`; on a complex curve this holds for any two charts of the atlas.

For background on the symmetric-power setting, see Ozsváth–Szabó, *Holomorphic disks and
topological invariants for closed three-manifolds*
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206)), §2.2. The chart construction and
transition calculation in this file are developed here, rather than attributed to that section.

## Main declarations

* `TauCeti.symOpenPartialHomeomorph_transition_apply`: for two charts using the same block
  partition, the transition is the blockwise change of surface coordinate on elementary symmetric
  coordinates.
* `TauCeti.analyticAt_symOpenPartialHomeomorph_transition`: the transition between two
  elementary-symmetric charts, with arbitrary block partitions, is analytic at the coordinates of
  every tuple lying in both sources.
* `TauCeti.contDiffOn_symOpenPartialHomeomorph_trans`: the transition partial homeomorphism is
  analytic on its source, in the form used by Mathlib's manifold atlas API.
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}

/-- **The coefficient expression is the same-partition chart transition on the source target.** -/
theorem symOpenPartialHomeomorph_transition_apply
    (φ ψ : ι → OpenPartialHomeomorph α ℂ)
    (V : ι → Set α) (m : ι → ℕ) (hm : ∑ i, m i = n)
    (hVo : ∀ i, IsOpen (V i))
    (hVsubφ : ∀ i, V i ⊆ (φ i).source)
    (hVsubψ : ∀ i, V i ⊆ (ψ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e e' : (Σ i, Fin (m i)) ≃ Fin n)
    (hp : Nonempty (∀ i, Sym ↥(V i) (m i)))
    (c : Fin n → ℂ)
    (hc : c ∈ (symOpenPartialHomeomorph
      φ V m hm hVo hVsubφ hVdisj e hp).target) :
    piSigmaConstHomeomorph ℂ e' (fun i =>
      Sym.coeffEquiv ℂ (m i)
        (Sym.map (fun w : ℂ => ψ i ((φ i).symm w))
          ((Sym.coeffEquiv ℂ (m i)).symm
            ((piSigmaConstHomeomorph ℂ e).symm c i)))) =
      symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp
        ((symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp).symm c) := by
  classical
  let C : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph φ V m hm hVo hVsubφ hVdisj e hp
  let D : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ) :=
    symOpenPartialHomeomorph ψ V m hm hVo hVsubψ hVdisj e' hp
  have hrepr : ∃ q : ∀ i, Sym ↥(V i) (m i),
      C.symm c = Sym.sumSubtype V m hm q := by
    have hs : C.symm c ∈ C.source := C.map_target hc
    rw [symOpenPartialHomeomorph_source φ V m hm hVo hVsubφ hVdisj e hp] at hs
    rcases Set.mem_range.mp hs with ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  obtain ⟨q, hq⟩ := hrepr
  have hsq : Sym.sumSubtype V m hm q ∈ C.source := by
    rw [← hq]
    exact C.map_target hc
  have hc' : C (Sym.sumSubtype V m hm q) = c := by
    rw [← hq, C.right_inv hc]
  rw [← hc', C.left_inv hsq]
  have hCcoords : C (Sym.sumSubtype V m hm q) =
      piSigmaConstHomeomorph ℂ e (fun j =>
        Sym.coeffEquiv ℂ (m j)
          (Sym.map (fun z : ↥(V j) => φ j (z : α)) (q j))) := by
    exact symOpenPartialHomeomorph_apply φ V m hm hVo hVsubφ hVdisj e hp q
  rw [hCcoords]
  rw [symOpenPartialHomeomorph_apply ψ V m hm hVo hVsubψ hVdisj e' hp]
  apply congrArg (piSigmaConstHomeomorph ℂ e')
  funext i
  have hroot : (Sym.coeffEquiv ℂ (m i)).symm
        (((piSigmaConstHomeomorph ℂ e).symm
          (piSigmaConstHomeomorph ℂ e (fun j =>
            Sym.coeffEquiv ℂ (m j)
              (Sym.map (fun z : ↥(V j) => φ j (z : α)) (q j))))) i) =
      Sym.map (fun z : ↥(V i) => φ i (z : α)) (q i) := by
    simp
  rw [hroot]
  congr 1
  rw [Sym.map_map]
  congr 1
  funext z
  simp only [Function.comp_apply]
  have hzφ : (φ i).symm (φ i z) = z :=
    (φ i).left_inv (hVsubφ i z.2)
  rw [hzφ]

open scoped Classical in
/-- The points of a concatenated tuple lying in the target patch `W j`, in the coordinate `ψ j`,
collected block by block from the source patches: from the `i`-th block, read in the coordinate
`φ i`, keep the points whose image lies in `φ i '' (V i ∩ W j)` and change coordinate. -/
private theorem sum_map_filter_map_eq_map (φ : ι → OpenPartialHomeomorph α ℂ)
    (ψ : κ → OpenPartialHomeomorph α ℂ) {V : ι → Set α} {m : ι → ℕ} {hm : ∑ i, m i = n}
    {W : κ → Set α} {p : κ → ℕ} {hp : ∑ j, p j = n}
    (hVsub : ∀ i, V i ⊆ (φ i).source) (hWdisj : Pairwise (Function.onFun Disjoint W))
    {q : ∀ i, Sym ↥(V i) (m i)} {r : ∀ j, Sym ↥(W j) (p j)}
    (hqr : Sym.sumSubtype V m hm q = Sym.sumSubtype W p hp r) (j : κ) :
    ∑ i, (((q i : Multiset ↥(V i)).map fun x : ↥(V i) => φ i (x : α)).filter
        (· ∈ φ i '' (V i ∩ W j))).map (fun w => ψ j ((φ i).symm w)) =
      (r j : Multiset ↥(W j)).map fun y : ↥(W j) => ψ j (y : α) := by
  classical
  -- in each source block, the points whose coordinate lies in `φ i '' (V i ∩ W j)` are exactly
  -- those lying in `W j`, and the change of coordinate recovers the point
  have hblock : ∀ i, (((q i : Multiset ↥(V i)).map fun x : ↥(V i) => φ i (x : α)).filter
      (· ∈ φ i '' (V i ∩ W j))).map (fun w => ψ j ((φ i).symm w)) =
      (((q i : Multiset ↥(V i)).map Subtype.val).filter (· ∈ W j)).map (ψ j) := by
    intro i
    rw [Multiset.filter_map, Multiset.map_map, Multiset.filter_map, Multiset.map_map]
    refine Multiset.map_congr (Multiset.filter_congr fun x _ => ?_) fun x _ => ?_
    · simp only [Function.comp_apply, Set.mem_image, Set.mem_inter_iff]
      refine ⟨?_, fun hx => ⟨x, ⟨x.2, hx⟩, rfl⟩⟩
      rintro ⟨y, ⟨hyV, hyW⟩, hyx⟩
      rwa [(φ i).injOn (hVsub i hyV) (hVsub i x.2) hyx] at hyW
    · simp only [Function.comp_apply, (φ i).left_inv (hVsub i x.2)]
  rw [Finset.sum_congr rfl fun i _ => hblock i, ← Multiset.coe_mapAddMonoidHom (ψ j), ← map_sum,
    Multiset.coe_mapAddMonoidHom, ← Multiset.filter_sum, ← Sym.coe_sumSubtype hm q, hqr,
    Sym.filter_mem_sumSubtype hWdisj]
  exact Multiset.map_map _ _ _

/-- **The transition between two elementary-symmetric charts is analytic at every tuple lying in
both sources.** The charts are built from disjoint patch families `V`, `W` with multiplicities
`m`, `p`, surface coordinates `φ`, `ψ` and regrouping bijections `e`, `e'`, which may all differ.
Repeated points in the tuple `t` are allowed. The hypothesis `hφψ` requires the change of surface
coordinate `ψ j ∘ (φ i).symm` to be analytic at `φ i z` for every point `z` of `t` lying in
`V i ∩ W j`. -/
theorem analyticAt_symOpenPartialHomeomorph_transition
    (φ : ι → OpenPartialHomeomorph α ℂ) (ψ : κ → OpenPartialHomeomorph α ℂ)
    (V : ι → Set α) (m : ι → ℕ) (hm : ∑ i, m i = n)
    (W : κ → Set α) (p : κ → ℕ) (hp : ∑ j, p j = n)
    (hVo : ∀ i, IsOpen (V i)) (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (hWo : ∀ j, IsOpen (W j)) (hWsub : ∀ j, W j ⊆ (ψ j).source)
    (hWdisj : Pairwise (Function.onFun Disjoint W))
    (e : (Σ i, Fin (m i)) ≃ Fin n) (e' : (Σ j, Fin (p j)) ≃ Fin n)
    (hq : Nonempty (∀ i, Sym ↥(V i) (m i))) (hr : Nonempty (∀ j, Sym ↥(W j) (p j)))
    {t : Sym α n}
    (ht : t ∈ (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq).source)
    (ht' : t ∈ (symOpenPartialHomeomorph ψ W p hp hWo hWsub hWdisj e' hr).source)
    (hφψ : ∀ i j, ∀ z ∈ V i ∩ W j, z ∈ t →
      AnalyticAt ℂ (fun w : ℂ => ψ j ((φ i).symm w)) (φ i z)) :
    AnalyticAt ℂ
      (fun c : Fin n → ℂ => symOpenPartialHomeomorph ψ W p hp hWo hWsub hWdisj e' hr
        ((symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq).symm c))
      (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq t) := by
  classical
  set C := symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq with hC
  set D := symOpenPartialHomeomorph ψ W p hp hWo hWsub hWdisj e' hr with hD
  -- the points of the `i`-th block of a coefficient tuple, in the coordinate `φ i`
  let R : (Fin n → ℂ) → ι → Multiset ℂ := fun c i =>
    ((Sym.coeffEquiv ℂ (m i)).symm ((piSigmaConstHomeomorph ℂ e).symm c i) : Multiset ℂ)
  -- the points lying in `W j`, in the coordinate `ψ j`, collected over the source blocks
  let M : (Fin n → ℂ) → κ → Multiset ℂ := fun c j =>
    ∑ i, ((R c i).filter (· ∈ φ i '' (V i ∩ W j))).map fun w => ψ j ((φ i).symm w)
  -- the candidate coordinate expression for the transition
  let F : (Fin n → ℂ) → Fin n → ℂ := fun c =>
    piSigmaConstHomeomorph ℂ e' fun j k =>
      (-1) ^ (p j - (k : ℕ)) * (M c j).esymm (p j - (k : ℕ))
  -- the block decompositions of `t`
  obtain ⟨q, hqt⟩ : t ∈ Set.range (Sym.sumSubtype V m hm) := by
    rwa [hC, symOpenPartialHomeomorph_source] at ht
  obtain ⟨r, hrt⟩ : t ∈ Set.range (Sym.sumSubtype W p hp) := by
    rwa [hD, symOpenPartialHomeomorph_source] at ht'
  -- `F` agrees with the transition wherever the latter is defined
  have hF : ∀ c ∈ (C.symm.trans D).source, F c = D (C.symm c) := by
    intro c hc
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] at hc
    obtain ⟨hcC, hcD⟩ := hc
    obtain ⟨q', hq'⟩ : C.symm c ∈ Set.range (Sym.sumSubtype V m hm) := by
      rw [← symOpenPartialHomeomorph_source φ V m hm hVo hVsub hVdisj e hq]
      exact C.map_target hcC
    obtain ⟨r', hr'⟩ : C.symm c ∈ Set.range (Sym.sumSubtype W p hp) := by
      rwa [← symOpenPartialHomeomorph_source ψ W p hp hWo hWsub hWdisj e' hr]
    have hqr : Sym.sumSubtype V m hm q' = Sym.sumSubtype W p hp r' := hq'.trans hr'.symm
    have hcq : c = C (Sym.sumSubtype V m hm q') := by rw [hq', C.right_inv hcC]
    have hR : ∀ i, R c i = (q' i : Multiset ↥(V i)).map fun x : ↥(V i) => φ i (x : α) := by
      intro i
      simp only [R, hcq, hC, symOpenPartialHomeomorph_apply, Homeomorph.symm_apply_apply,
        Equiv.symm_apply_apply, _root_.Sym.coe_map]
    rw [← hq', hqr, hD, symOpenPartialHomeomorph_apply]
    simp only [F, M, hR]
    congr 1
    funext j
    ext k
    rw [Sym.coeffEquiv_apply, _root_.Sym.coe_map, sum_map_filter_map_eq_map φ ψ hVsub hWdisj hqr]
  -- the points of the `i`-th block of `C t`
  have hRt : ∀ i, R (C t) i = (q i : Multiset ↥(V i)).map fun x : ↥(V i) => φ i (x : α) := by
    intro i
    simp only [R, ← hqt, hC, symOpenPartialHomeomorph_apply, Homeomorph.symm_apply_apply,
      Equiv.symm_apply_apply, _root_.Sym.coe_map]
  -- a point of the `i`-th block of `t` lies in `V i`, in `t`, and in some `W j'`
  have hmem_t : ∀ i (x : ↥(V i)), x ∈ q i → (x : α) ∈ t := fun i x hx => by
    rw [← hqt]
    exact (Sym.mem_sumSubtype_iff (fun i' hi' ha => Set.disjoint_left.1 (hVdisj hi') ha x.2)
      x.2).2 (by simpa using hx)
  have hmem_W : ∀ a ∈ t, ∃ j, a ∈ W j := fun a ha => by
    rw [← hrt] at ha
    exact Sym.exists_mem_of_mem_sumSubtype ha
  have hUo : ∀ i j, IsOpen (φ i '' (V i ∩ W j)) := fun i j =>
    ((φ i).isOpen_image_iff_of_subset_source (Set.inter_subset_left.trans (hVsub i))).2
      ((hVo i).inter (hWo j))
  -- the images of the pieces `V i ∩ W j` under `φ i` are pairwise disjoint in `j`
  have hUdisj : ∀ i j j', j ≠ j' → Disjoint (φ i '' (V i ∩ W j)) (φ i '' (V i ∩ W j')) := by
    intro i j j' hjj'
    rw [Set.disjoint_left]
    rintro w ⟨a, ⟨haV, haW⟩, rfl⟩ ⟨a', ⟨ha'V, ha'W⟩, ha'⟩
    rw [(φ i).injOn (hVsub i ha'V) (hVsub i haV) ha'] at ha'W
    exact Set.disjoint_left.1 (hWdisj hjj') haW ha'W
  -- `F` is analytic at `C t`
  have hFa : AnalyticAt ℂ F (C t) := by
    refine (analyticAt_piSigmaConstHomeomorph e' _).comp (AnalyticAt.pi fun j =>
      AnalyticAt.pi fun k => analyticAt_const.mul
        (analyticAt_esymm_of_forall_analyticAt_sum_map_pow _ fun l _ _ => ?_))
    -- the power sums of the `j`-th target block are sums over the source blocks
    have hMl : ∀ c, ((M c j).map (· ^ l)).sum = ∑ i,
        (((R c i).filter (· ∈ φ i '' (V i ∩ W j))).map fun w => ψ j ((φ i).symm w) ^ l).sum := by
      intro c
      simp only [M]
      rw [← Multiset.coe_mapAddMonoidHom, map_sum, ← Multiset.coe_sumAddMonoidHom, map_sum]
      simp only [Multiset.coe_mapAddMonoidHom, Multiset.coe_sumAddMonoidHom, Multiset.map_map,
        Function.comp_def]
    simp only [hMl]
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have hproj : AnalyticAt ℂ (fun c : Fin n → ℂ => (piSigmaConstHomeomorph ℂ e).symm c i) (C t) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun i => Fin (m i) → ℂ) i).analyticAt _).comp
        (analyticAt_piSigmaConstHomeomorph_symm e (C t))
    refine (Sym.analyticAt_sum_map_filter_coeffEquiv_symm (g := fun w => ψ j ((φ i).symm w) ^ l)
      (U := φ i '' (V i ∩ W j)) ?_ ?_).comp hproj
    · -- no point of the block lies on the frontier of `φ i '' (V i ∩ W j)`
      intro z hz
      have hz' : z ∈ R (C t) i := _root_.Sym.mem_coe.2 hz
      rw [hRt, Multiset.mem_map] at hz'
      obtain ⟨x, hx, rfl⟩ := hz'
      obtain ⟨j', hj'⟩ := hmem_W x (hmem_t i x hx)
      have hzU' : φ i x ∈ φ i '' (V i ∩ W j') := ⟨x, ⟨x.2, hj'⟩, rfl⟩
      rcases eq_or_ne j' j with rfl | hjj'
      · rw [(hUo i j').frontier_eq]
        exact fun h => h.2 hzU'
      · exact fun h => Set.disjoint_left.1 ((hUdisj i j j' hjj'.symm).closure_left (hUo i j'))
          (frontier_subset_closure h) hzU'
    · -- at the points of the block lying in `φ i '' (V i ∩ W j)`, the change of coordinate is
      -- analytic
      intro z hz hzU
      have hz' : z ∈ R (C t) i := _root_.Sym.mem_coe.2 hz
      rw [hRt, Multiset.mem_map] at hz'
      obtain ⟨x, hx, rfl⟩ := hz'
      obtain ⟨y, ⟨hyV, hyW⟩, hyx⟩ := hzU
      rw [(φ i).injOn (hVsub i hyV) (hVsub i x.2) hyx] at hyW
      exact (hφψ i j x ⟨x.2, hyW⟩ (hmem_t i x hx)).fun_pow l
  -- the transition is defined near `C t`
  have hmem : C t ∈ (C.symm.trans D).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage, C.left_inv ht]
    exact ⟨C.map_source ht, ht'⟩
  refine hFa.congr ?_
  filter_upwards [(C.symm.trans D).open_source.mem_nhds hmem] with c hc
  exact hF c hc

/-- **The transition partial homeomorphism between two elementary-symmetric charts is analytic on
its source.** This is the source-and-target form consumed by `isManifold_of_contDiffOn`. Here
`hφψ` requires the change of surface coordinate `ψ j ∘ (φ i).symm` to be analytic at `φ i z` for
every point `z` of `V i ∩ W j` belonging to some tuple `t` in both chart sources; no condition is
imposed at points of `V i ∩ W j` outside every such tuple. -/
theorem contDiffOn_symOpenPartialHomeomorph_trans
    (φ : ι → OpenPartialHomeomorph α ℂ) (ψ : κ → OpenPartialHomeomorph α ℂ)
    (V : ι → Set α) (m : ι → ℕ) (hm : ∑ i, m i = n)
    (W : κ → Set α) (p : κ → ℕ) (hp : ∑ j, p j = n)
    (hVo : ∀ i, IsOpen (V i)) (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (hWo : ∀ j, IsOpen (W j)) (hWsub : ∀ j, W j ⊆ (ψ j).source)
    (hWdisj : Pairwise (Function.onFun Disjoint W))
    (e : (Σ i, Fin (m i)) ≃ Fin n) (e' : (Σ j, Fin (p j)) ≃ Fin n)
    (hq : Nonempty (∀ i, Sym ↥(V i) (m i))) (hr : Nonempty (∀ j, Sym ↥(W j) (p j)))
    (hφψ : ∀ t ∈ (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq).source ∩
        (symOpenPartialHomeomorph ψ W p hp hWo hWsub hWdisj e' hr).source,
      ∀ i j, ∀ z ∈ V i ∩ W j, z ∈ t →
        AnalyticAt ℂ (fun w : ℂ => ψ j ((φ i).symm w)) (φ i z)) :
    ContDiffOn ℂ ω
      ((symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq).symm.trans
        (symOpenPartialHomeomorph ψ W p hp hWo hWsub hWdisj e' hr))
      ((symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq).symm.trans
        (symOpenPartialHomeomorph ψ W p hp hWo hWsub hWdisj e' hr)).source := by
  set C := symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq
  set D := symOpenPartialHomeomorph ψ W p hp hWo hWsub hWdisj e' hr
  intro c hc
  have hc' := hc
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage] at hc'
  obtain ⟨hcC, hcD⟩ := hc'
  have hA := analyticAt_symOpenPartialHomeomorph_transition φ ψ V m hm W p hp hVo hVsub hVdisj
    hWo hWsub hWdisj e e' hq hr (C.map_target hcC) hcD (hφψ _ ⟨C.map_target hcC, hcD⟩)
  rw [C.right_inv hcC] at hA
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_def]
  exact hA.contDiffAt.contDiffWithinAt

end TauCeti

end
