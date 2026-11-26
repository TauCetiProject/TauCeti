/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.ConjExtend
public import TauCeti.Topology.VectorBundle.FiniteRank.Conjugate

/-!
# Doubling a complex bundle core along a subset

Let `C` be a complex point-indexed finite-rank core over `X` and `A ⊆ X` a subset. Suppose
that the transitions of `C` are *real at the points of `A`*: each transition at a point of `A`
commutes with coordinatewise complex conjugation (`FiniteRankBundleCore.IsRealAlong`, characterized
by `FiniteRankBundleCore.isRealAlong_iff_coordChange_star`). Then the real subspaces `ℝⁿ ⊆ ℂⁿ` of
the charts at the points of `A` agree, so they form a subbundle `F` of `C` over `A`. It is a
maximal totally real subbundle, and conversely a core real along `A` is the way such a pair
`(C, F)` is encoded here.

`FiniteRankBundleCore.doubleAlong` glues `C` on the first sheet of `TauCeti.DoubleAlong A` to the
conjugate core on the second sheet. Its transition between charts at `z` and `w` is the transition
of `C` at the folded points on the first sheet and its intrinsic conjugate on the second sheet
(`TauCeti.DoubleAlong.conjExtend`, the extension of an operator-valued function by conjugation);
the two agree on the common image of `A` because `C` is real there. In terms of the bundles, the
fibre of `C` at a point of `A` is identified with the fibre of the conjugate bundle by the
antilinear involution of `C` over `A` with fixed set `F`, which in the coordinates of the conjugate
core is the identity.

The restrictions of the double to the two sheets are `C` (`doubleAlongInlIso`) and its conjugate
(`doubleAlongInrIso`), by the identity in coordinates. Coordinatewise conjugation covering the
sheet swap `TauCeti.DoubleAlong.swap` is a homeomorphism of the total space of the double
(`doubleAlongSwap`). It is a conjugate-linear involution on fibres, and its fixed points are
exactly the vectors with real coordinates over the image of `A` (`doubleAlongSwap_mk_eq_self_iff`,
`doubleAlongSwap_mk_inl_eq_self_iff`). The trivial core is real along every subset, and its
double is again trivial (`doubleAlongTrivialIso`); there the involution is
`(z, v) ↦ (swap z, conj v)`.

Doubling is functorial for bundle maps whose fibre maps over `A` commute with coordinatewise
conjugation, that is, which carry the real subbundle of the source into that of the target:
`doubleAlongMap` is the bundle map on the first sheet and its intrinsic conjugate on the second
sheet. It preserves identities and composites (`doubleAlongMap_id`, `doubleAlongMap_comp`),
commutes with the lifted swaps (`doubleAlongMap_totalSpaceMap_doubleAlongSwap`), restricts to the
given map and its conjugate on the two sheets, and doubles isomorphisms to isomorphisms
(`doubleAlongIso`).

No closedness of `A` is needed. For the boundary of a Riemann surface with boundary this is the
topological doubled bundle over the Schottky double. Smoothness of the double via collars is not
treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.3, the doubled bundle.
-/

public section

open Bundle CategoryTheory Set Topology WithConv Filter

namespace TauCeti.FiniteRankBundleCore

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The transitions of a complex core are *real along* `A` when every transition at a point of
`A`, between charts containing that point, commutes with coordinatewise conjugation. The real
coordinate subspaces of the charts over `A` then form a maximal totally real subbundle.
The native `IsSelfAdjoint` condition uses the intrinsic star on `WithConv` operators. -/
def IsRealAlong (C : FiniteRankBundleCore ℂ X) (A : Set X) : Prop :=
  ∀ i j x, x ∈ A → x ∈ C.core.baseSet i → x ∈ C.core.baseSet j →
    IsSelfAdjoint (toConv (C.core.coordChange i j x))

variable {A : Set X}

/-- A complex core is real along `A` if and only if each transition at a point of `A` commutes
with coordinatewise conjugation. -/
theorem isRealAlong_iff_coordChange_star {C : FiniteRankBundleCore ℂ X} :
    C.IsRealAlong A ↔ ∀ i j x, x ∈ A → x ∈ C.core.baseSet i → x ∈ C.core.baseSet j →
      ∀ v, C.core.coordChange i j x (star v) = star (C.core.coordChange i j x v) := by
  simp only [IsRealAlong, ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]

/-- A transition of a core real along `A`, at a point of `A`, commutes with coordinatewise
conjugation. -/
theorem IsRealAlong.coordChange_star {C : FiniteRankBundleCore ℂ X} (hC : C.IsRealAlong A)
    {i j x : X} (hx : x ∈ A) (hi : x ∈ C.core.baseSet i) (hj : x ∈ C.core.baseSet j)
    (v : Fin C.rank → ℂ) :
    C.core.coordChange i j x (star v) = star (C.core.coordChange i j x v) :=
  isRealAlong_iff_coordChange_star.1 hC i j x hx hi hj v

/-- The trivial core is real along every subset. -/
theorem isRealAlong_trivial (n : ℕ) (A : Set X) : (trivial ℂ X n).IsRealAlong A :=
  isRealAlong_iff_coordChange_star.2 fun _ _ _ _ _ _ _ => rfl

/-- The transitions of the doubled core: those of `C` at the folded points on the first sheet, and
their intrinsic conjugates elsewhere (`DoubleAlong.conjExtend`). -/
noncomputable def doubleAlongCoordChange (C : FiniteRankBundleCore ℂ X) (A : Set X)
    (i j : DoubleAlong A) : DoubleAlong A → (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ) :=
  DoubleAlong.conjExtend A (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j))

@[simp] theorem doubleAlongCoordChange_inl (C : FiniteRankBundleCore ℂ X) (i j : DoubleAlong A)
    (x : X) :
    doubleAlongCoordChange C A i j (DoubleAlong.inl A x) =
      C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j) x :=
  DoubleAlong.conjExtend_inl A _ x

/-- On the second sheet, away from the glued set, the doubled transition is the conjugate
transition of `C`; no realness of `C` is needed there. -/
theorem doubleAlongCoordChange_inr_of_notMem (C : FiniteRankBundleCore ℂ X) (i j : DoubleAlong A)
    {x : X} (hx : x ∉ A) :
    doubleAlongCoordChange C A i j (DoubleAlong.inr A x) =
      (star (toConv
        (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j) x))).ofConv :=
  DoubleAlong.conjExtend_inr_of_notMem A _ hx

/-- On the second sheet the doubled transition is the conjugate transition of `C`, at points of the
two charts. -/
theorem doubleAlongCoordChange_inr {C : FiniteRankBundleCore ℂ X} (hC : C.IsRealAlong A)
    {i j : DoubleAlong A} {x : X} (hi : x ∈ C.core.baseSet (DoubleAlong.fold A i))
    (hj : x ∈ C.core.baseSet (DoubleAlong.fold A j)) :
    doubleAlongCoordChange C A i j (DoubleAlong.inr A x) =
      (star (toConv
        (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j) x))).ofConv :=
  DoubleAlong.conjExtend_inr A _ fun hx => hC _ _ x hx hi hj

/-- The doubled transition from a chart to itself is the identity on the chart. -/
theorem doubleAlongCoordChange_self {C : FiniteRankBundleCore ℂ X} (hC : C.IsRealAlong A)
    (i y : DoubleAlong A) (hy : DoubleAlong.fold A y ∈ C.core.baseSet (DoubleAlong.fold A i))
    (v : Fin C.rank → ℂ) : doubleAlongCoordChange C A i i y v = v := by
  induction y using DoubleAlong.induction_on with
  | hl x =>
    rw [doubleAlongCoordChange_inl]
    exact C.core.coordChange_self _ x (by simpa using hy) v
  | hr x =>
    have hx : x ∈ C.core.baseSet (DoubleAlong.fold A i) := by simpa using hy
    rw [doubleAlongCoordChange_inr hC hx hx, ContinuousLinearMap.intrinsicStar_apply,
      C.core.coordChange_self _ x hx, star_star]

/-- The doubled transitions satisfy the cocycle condition. -/
theorem doubleAlongCoordChange_comp {C : FiniteRankBundleCore ℂ X} (hC : C.IsRealAlong A)
    (i j k y : DoubleAlong A)
    (hi : DoubleAlong.fold A y ∈ C.core.baseSet (DoubleAlong.fold A i))
    (hj : DoubleAlong.fold A y ∈ C.core.baseSet (DoubleAlong.fold A j))
    (hk : DoubleAlong.fold A y ∈ C.core.baseSet (DoubleAlong.fold A k)) (v : Fin C.rank → ℂ) :
    doubleAlongCoordChange C A j k y (doubleAlongCoordChange C A i j y v) =
      doubleAlongCoordChange C A i k y v := by
  induction y using DoubleAlong.induction_on with
  | hl x =>
    simp only [DoubleAlong.fold_inl] at hi hj hk
    simp only [doubleAlongCoordChange_inl]
    exact C.core.coordChange_comp _ _ _ x ⟨⟨hi, hj⟩, hk⟩ v
  | hr x =>
    simp only [DoubleAlong.fold_inr] at hi hj hk
    rw [doubleAlongCoordChange_inr hC hi hj, doubleAlongCoordChange_inr hC hj hk,
      doubleAlongCoordChange_inr hC hi hk]
    simp only [ContinuousLinearMap.intrinsicStar_apply, star_star,
      C.core.coordChange_comp _ _ _ x ⟨⟨hi, hj⟩, hk⟩]

/-- The doubled transitions are continuous on the overlap of the folded charts. -/
theorem continuousOn_doubleAlongCoordChange {C : FiniteRankBundleCore ℂ X}
    (hC : C.IsRealAlong A) (i j : DoubleAlong A) :
    ContinuousOn (doubleAlongCoordChange C A i j)
      (DoubleAlong.fold A ⁻¹' C.core.baseSet (DoubleAlong.fold A i) ∩
        DoubleAlong.fold A ⁻¹' C.core.baseSet (DoubleAlong.fold A j)) := by
  rw [← preimage_inter]
  exact DoubleAlong.continuousOn_conjExtend A
    ((C.core.isOpen_baseSet _).inter (C.core.isOpen_baseSet _))
    (C.core.continuousOn_coordChange _ _) fun x hx => hC _ _ x hx.1 hx.2.1 hx.2.2

/-- The double of a complex core along a subset `A` on which its transitions are real:
`C` on the first sheet and its conjugate on the second sheet, glued along `A` by the identity in
coordinates. The chart at `z` lies over the chart of `C` at the folded point. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin C.rank → ℂ`.
@[expose]
noncomputable def doubleAlong (C : FiniteRankBundleCore ℂ X) (hC : C.IsRealAlong A) :
    FiniteRankBundleCore ℂ (DoubleAlong A) where
  rank := C.rank
  core :=
    { baseSet := fun z => DoubleAlong.fold A ⁻¹' C.core.baseSet (DoubleAlong.fold A z)
      isOpen_baseSet := fun z =>
        (C.core.isOpen_baseSet (DoubleAlong.fold A z)).preimage (DoubleAlong.fold A).continuous
      indexAt := id
      mem_baseSet_at := fun z => C.mem_baseSet_self (DoubleAlong.fold A z)
      coordChange := doubleAlongCoordChange C A
      coordChange_self := fun i y hy v => doubleAlongCoordChange_self hC i y hy v
      continuousOn_coordChange := continuousOn_doubleAlongCoordChange hC
      coordChange_comp := fun i j k y hy v =>
        doubleAlongCoordChange_comp hC i j k y hy.1.1 hy.1.2 hy.2 v }
  indexAt_eq := fun _ => rfl

section Double

variable (C : FiniteRankBundleCore ℂ X) (hC : C.IsRealAlong A)

@[simp] theorem rank_doubleAlong : (C.doubleAlong hC).rank = C.rank := (rfl)

@[simp] theorem localTriv_baseSet_doubleAlong (z : DoubleAlong A) :
    ((C.doubleAlong hC).core.localTriv z).baseSet =
      DoubleAlong.fold A ⁻¹' C.core.baseSet (DoubleAlong.fold A z) := (rfl)

theorem mem_baseSet_doubleAlong {y z : DoubleAlong A} :
    y ∈ (C.doubleAlong hC).core.baseSet z ↔
      DoubleAlong.fold A y ∈ C.core.baseSet (DoubleAlong.fold A z) := Iff.rfl

@[simp] theorem coordChange_doubleAlong (i j y : DoubleAlong A) :
    (C.doubleAlong hC).core.coordChange i j y = doubleAlongCoordChange C A i j y := (rfl)

/-- The double restricted to the first sheet is the original core, by the identity in
coordinates. -/
noncomputable def doubleAlongInlIso : (C.doubleAlong hC).pullback (DoubleAlong.inl A) ≅ C :=
  constIso (fun i => Eq.subset <| by
      ext x
      simp only [VectorBundleCore.baseSet_at, localTriv_baseSet_pullback,
        localTriv_baseSet_doubleAlong, mem_preimage, DoubleAlong.fold_inl])
    (ContinuousLinearEquiv.refl ℂ (Fin C.rank → ℂ)) fun i j x _ _ => by
    -- State the identity on standard coordinates to fix the inherited fibre instances.
    have h : (ContinuousLinearMap.id ℂ (Fin C.rank → ℂ)).comp
        (doubleAlongCoordChange C A (DoubleAlong.inl A i) (DoubleAlong.inl A j)
          (DoubleAlong.inl A x)) =
        (C.core.coordChange i j x).comp (ContinuousLinearMap.id ℂ (Fin C.rank → ℂ)) := by
      simp
    exact h

/-- The double restricted to the second sheet is the conjugate core, by the identity in
coordinates. -/
noncomputable def doubleAlongInrIso :
    (C.doubleAlong hC).pullback (DoubleAlong.inr A) ≅ (conjugate X).obj C :=
  constIso (fun i => Eq.subset <| by
      ext x
      simp only [VectorBundleCore.baseSet_at, localTriv_baseSet_pullback,
        localTriv_baseSet_doubleAlong, localTriv_baseSet_conjugate_obj, mem_preimage,
        DoubleAlong.fold_inr])
    (ContinuousLinearEquiv.refl ℂ (Fin C.rank → ℂ)) fun i j x hi hj => by
    simp only [VectorBundleCore.baseSet_at, localTriv_baseSet_pullback,
      localTriv_baseSet_doubleAlong, mem_preimage, DoubleAlong.fold_inr] at hi hj
    rw [← VectorBundleCore.baseSet_at] at hi hj
    -- State the identity on standard coordinates to fix the inherited fibre instances.
    have h : (ContinuousLinearMap.id ℂ (Fin C.rank → ℂ)).comp
        (doubleAlongCoordChange C A (DoubleAlong.inr A i) (DoubleAlong.inr A j)
          (DoubleAlong.inr A x)) =
        (star (toConv (C.core.coordChange i j x))).ofConv.comp
          (ContinuousLinearMap.id ℂ (Fin C.rank → ℂ)) := by
      rw [doubleAlongCoordChange_inr hC (by rwa [DoubleAlong.fold_inr])
        (by rwa [DoubleAlong.fold_inr])]
      simp
    exact h

@[simp] theorem fiberMap_doubleAlongInlIso_hom (x : X) :
    (C.doubleAlongInlIso hC).hom.fiberMap x = ContinuousLinearMap.id ℂ (Fin C.rank → ℂ) := by
  rw [doubleAlongInlIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_doubleAlongInlIso_inv (x : X) :
    (C.doubleAlongInlIso hC).inv.fiberMap x = ContinuousLinearMap.id ℂ (Fin C.rank → ℂ) := by
  rw [doubleAlongInlIso]
  exact fiberMap_constIso_inv _ _ _ x

@[simp] theorem fiberMap_doubleAlongInrIso_hom (x : X) :
    (C.doubleAlongInrIso hC).hom.fiberMap x = ContinuousLinearMap.id ℂ (Fin C.rank → ℂ) := by
  rw [doubleAlongInrIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_doubleAlongInrIso_inv (x : X) :
    (C.doubleAlongInrIso hC).inv.fiberMap x = ContinuousLinearMap.id ℂ (Fin C.rank → ℂ) := by
  rw [doubleAlongInrIso]
  exact fiberMap_constIso_inv _ _ _ x

/-- The doubled transitions between swapped charts at a swapped point are the conjugates of the
original ones. -/
theorem doubleAlongCoordChange_swap {i j y : DoubleAlong A}
    (hi : y ∈ (C.doubleAlong hC).core.baseSet i)
    (hj : y ∈ (C.doubleAlong hC).core.baseSet j) (v : Fin C.rank → ℂ) :
    doubleAlongCoordChange C A (DoubleAlong.swap A i) (DoubleAlong.swap A j)
        (DoubleAlong.swap A y) (star v) =
      star (doubleAlongCoordChange C A i j y v) := by
  rw [mem_baseSet_doubleAlong] at hi hj
  induction y using DoubleAlong.induction_on with
  | hl x =>
    simp only [DoubleAlong.fold_inl] at hi hj
    rw [DoubleAlong.swap_inl, doubleAlongCoordChange_inr hC (by simpa using hi) (by simpa using hj),
      doubleAlongCoordChange_inl, ContinuousLinearMap.intrinsicStar_apply, star_star]
    simp
  | hr x =>
    simp only [DoubleAlong.fold_inr] at hi hj
    rw [DoubleAlong.swap_inr, doubleAlongCoordChange_inl, doubleAlongCoordChange_inr hC hi hj,
      ContinuousLinearMap.intrinsicStar_apply, star_star]
    simp

/-- Coordinatewise conjugation covering the sheet swap, as a map of total spaces. -/
private noncomputable def doubleAlongSwapFun (p : (C.doubleAlong hC).core.TotalSpace) :
    (C.doubleAlong hC).core.TotalSpace :=
  ⟨DoubleAlong.swap A p.proj, (star : (Fin C.rank → ℂ) → Fin C.rank → ℂ) p.snd⟩

private theorem doubleAlongSwapFun_involutive :
    Function.Involutive (doubleAlongSwapFun C hC) := fun ⟨z, v⟩ =>
  (C.doubleAlong hC).core.mk_eq_mk_iff.2
    ⟨DoubleAlong.swap_swap A z, star_star (R := Fin C.rank → ℂ) v⟩

private theorem continuous_doubleAlongSwapFun : Continuous (doubleAlongSwapFun C hC) := by
  set D := C.doubleAlong hC
  refine continuous_iff_continuousAt.2 fun p => ?_
  refine (FiberBundle.continuousAt_totalSpace _ _).2 ⟨((DoubleAlong.swap A).continuous.comp
    D.core.continuous_proj).continuousAt, ?_⟩
  rw [trivializationAt_core]
  have hsrc : (D.core.localTriv p.proj).source ∈ 𝓝 p :=
    (D.core.localTriv p.proj).open_source.mem_nhds (D.mem_baseSet_self p.proj)
  have hcont : ContinuousAt (fun q => (star : (Fin C.rank → ℂ) → Fin C.rank → ℂ)
      (D.core.localTriv p.proj q).2) p :=
    continuous_star.continuousAt.comp
      (continuous_snd.continuousAt.comp ((D.core.localTriv p.proj).continuousAt
        (D.mem_baseSet_self p.proj)))
  refine hcont.congr (mem_of_superset hsrc fun q hq => ?_)
  rw [VectorBundleCore.mem_localTriv_source] at hq
  simp only [mem_ofPred_eq, VectorBundleCore.localTriv_apply, D.indexAt_eq]
  exact (doubleAlongCoordChange_swap C hC (D.mem_baseSet_self q.proj) hq q.snd).symm

/-- The lift of the sheet swap to the double: coordinatewise conjugation on fibres, covering
`DoubleAlong.swap`. It is a homeomorphism of total spaces and an involution. -/
noncomputable def doubleAlongSwap :
    (C.doubleAlong hC).core.TotalSpace ≃ₜ (C.doubleAlong hC).core.TotalSpace where
  toFun := doubleAlongSwapFun C hC
  invFun := doubleAlongSwapFun C hC
  left_inv := doubleAlongSwapFun_involutive C hC
  right_inv := doubleAlongSwapFun_involutive C hC
  continuous_toFun := continuous_doubleAlongSwapFun C hC
  continuous_invFun := continuous_doubleAlongSwapFun C hC

/-- The lifted swap conjugates coordinates and swaps the sheets. Coordinatewise conjugation is the
conjugate-linear equivalence `starL ℂ`, so the lift is conjugate-linear on fibres. -/
@[simp] theorem doubleAlongSwap_mk (z : DoubleAlong A) (v : Fin C.rank → ℂ) :
    C.doubleAlongSwap hC ⟨z, v⟩ = ⟨DoubleAlong.swap A z, (star v : Fin C.rank → ℂ)⟩ := (rfl)

/-- The lifted swap conjugates the coordinates of every point. -/
@[simp] theorem snd_doubleAlongSwap (p : (C.doubleAlong hC).core.TotalSpace) :
    ((C.doubleAlongSwap hC p).snd : Fin C.rank → ℂ) =
      (star : (Fin C.rank → ℂ) → Fin C.rank → ℂ) p.snd := (rfl)

/-- The lifted swap covers the sheet swap. -/
@[simp] theorem proj_doubleAlongSwap (p : (C.doubleAlong hC).core.TotalSpace) :
    (C.doubleAlongSwap hC p).proj = DoubleAlong.swap A p.proj := (rfl)

@[simp] theorem doubleAlongSwap_doubleAlongSwap (p : (C.doubleAlong hC).core.TotalSpace) :
    C.doubleAlongSwap hC (C.doubleAlongSwap hC p) = p :=
  doubleAlongSwapFun_involutive C hC p

@[simp] theorem symm_doubleAlongSwap :
    (C.doubleAlongSwap hC).symm = C.doubleAlongSwap hC := (rfl)

/-- A point of the double's total space is fixed by the lifted swap exactly when it lies over the
image of `A` and its coordinates are real. -/
theorem doubleAlongSwap_mk_eq_self_iff (z : DoubleAlong A) (v : Fin C.rank → ℂ) :
    C.doubleAlongSwap hC ⟨z, v⟩ = ⟨z, v⟩ ↔ DoubleAlong.fold A z ∈ A ∧ star v = v := by
  rw [doubleAlongSwap_mk]
  exact (C.doubleAlong hC).core.mk_eq_mk_iff.trans
    (and_congr (DoubleAlong.swap_eq_self_iff A z) .rfl)

/-- Over a point of `A`, the fixed vectors of the lifted swap are exactly the real coordinate
vectors: the fixed set is the totally real subbundle `ℝⁿ` encoded by `C`. -/
theorem doubleAlongSwap_mk_inl_eq_self_iff {a : X} (ha : a ∈ A) (v : Fin C.rank → ℂ) :
    C.doubleAlongSwap hC ⟨DoubleAlong.inl A a, v⟩ = ⟨DoubleAlong.inl A a, v⟩ ↔
      ∃ r : Fin C.rank → ℝ, v = fun k => (r k : ℂ) := by
  rw [doubleAlongSwap_mk_eq_self_iff, DoubleAlong.fold_inl]
  simp only [ha, true_and, funext_iff, Pi.star_apply, Complex.star_def, Complex.conj_eq_iff_real]
  exact Classical.skolem

end Double

/-- The common chart domain of the doubles of two cores at `i` and `j` is the preimage under the
fold of the common chart domain of the cores at the folded points. -/
theorem baseSet_inter_baseSet_doubleAlong {C C' : FiniteRankBundleCore ℂ X}
    (hC : C.IsRealAlong A) (hC' : C'.IsRealAlong A) (i j : DoubleAlong A) :
    (C.doubleAlong hC).core.baseSet i ∩ (C'.doubleAlong hC').core.baseSet j =
      DoubleAlong.fold A ⁻¹' (C.core.baseSet (DoubleAlong.fold A i) ∩
        C'.core.baseSet (DoubleAlong.fold A j)) := by
  ext y
  rw [Set.mem_inter_iff, mem_baseSet_doubleAlong, mem_baseSet_doubleAlong, Set.mem_preimage,
    Set.mem_inter_iff]

/-- The double of a trivial core is trivial, by the identity in coordinates. Under this
identification the lifted swap `doubleAlongSwap` is `(z, v) ↦ (swap z, conj v)`
(`doubleAlongSwap_mk`). -/
noncomputable def doubleAlongTrivialIso (n : ℕ) :
    (trivial ℂ X n).doubleAlong (isRealAlong_trivial n A) ≅ trivial ℂ (DoubleAlong A) n :=
  constIso (fun _ => Set.preimage_univ.le) (ContinuousLinearEquiv.refl ℂ (Fin n → ℂ))
    fun i j y _ _ => by
    -- State the identity on standard coordinates to fix the inherited fibre instances.
    have h : (ContinuousLinearMap.id ℂ (Fin n → ℂ)).comp
        (doubleAlongCoordChange (trivial ℂ X n) A i j y) =
        (ContinuousLinearMap.id ℂ (Fin n → ℂ)).comp (ContinuousLinearMap.id ℂ (Fin n → ℂ)) := by
      ext v : 1
      -- Here v is typed over Fin (trivial ℂ X n).rank, while the identities use Fin n.
      -- Rewriting comp_apply does not match those inherited fibre instances. Identify
      -- the definitional rank equality and evaluate the two identity composites first.
      change doubleAlongCoordChange (trivial ℂ X n) A i j y v = v
      induction y using DoubleAlong.induction_on with
      | hl x =>
        rw [doubleAlongCoordChange_inl, coordChange_trivial]
        exact ContinuousLinearMap.id_apply v
      | hr x =>
        rw [doubleAlongCoordChange_inr (isRealAlong_trivial n A) (mem_univ x) (mem_univ x),
          ContinuousLinearMap.intrinsicStar_apply]
        exact star_star v
    exact h

@[simp] theorem fiberMap_doubleAlongTrivialIso_hom (n : ℕ) (z : DoubleAlong A) :
    (doubleAlongTrivialIso n).hom.fiberMap z = ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
  rw [doubleAlongTrivialIso]
  exact fiberMap_constIso_hom _ _ _ z

@[simp] theorem fiberMap_doubleAlongTrivialIso_inv (n : ℕ) (z : DoubleAlong A) :
    (doubleAlongTrivialIso n).inv.fiberMap z = ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
  rw [doubleAlongTrivialIso]
  exact fiberMap_constIso_inv _ _ _ z


/-! ### Functoriality -/

/-- The inverse of an isomorphism whose fibre map at a point commutes with coordinatewise
conjugation commutes with it as well. -/
theorem _root_.CategoryTheory.Iso.fiberMap_inv_star {C C' : FiniteRankBundleCore ℂ X} (e : C ≅ C')
    {a : X}
    (he : ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) (v : Fin C'.rank → ℂ) :
    e.inv.fiberMap a (star v) = star (e.inv.fiberMap a v) := by
  conv_lhs => rw [← e.fiberMap_inv_hom_id_apply a v, ← he, e.fiberMap_hom_inv_id_apply]

/-- For cores `C` and `C'` real along `A`, the chart expression of a bundle map `C ⟶ C'` whose fibre
maps over `A` commute with conjugation is real at the points of `A`. -/
theorem isSelfAdjoint_inChartCoordinates {C C' : FiniteRankBundleCore ℂ X} (hC : C.IsRealAlong A)
    (hC' : C'.IsRealAlong A) (φ : C ⟶ C')
    (hφ : ∀ a ∈ A, ∀ v, φ.fiberMap a (star v) = star (φ.fiberMap a v)) {i j a : X} (ha : a ∈ A)
    (hi : a ∈ C.core.baseSet i) (hj : a ∈ C'.core.baseSet j) :
    IsSelfAdjoint (toConv (C.core.inChartCoordinates C'.core i j a (φ.fiberMap a))) := by
  refine (ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _).2 fun v => ?_
  simp only [inChartCoordinates_core_apply, hC.coordChange_star ha hi (C.mem_baseSet_self a),
    hφ a ha, hC'.coordChange_star ha (C'.mem_baseSet_self a) hj]

section Map

variable {C C' C'' : FiniteRankBundleCore ℂ X} (hC : C.IsRealAlong A) (hC' : C'.IsRealAlong A)
  (hC'' : C''.IsRealAlong A)

/-- In charts of the doubles, the conjugation extension of the fibre maps of a bundle map is the
conjugation extension of its chart expression in the folded charts. -/
theorem inChartCoordinates_doubleAlong_conjExtend (φ : C ⟶ C') (i j y : DoubleAlong A) :
    (C.doubleAlong hC).core.inChartCoordinates (C'.doubleAlong hC').core i j y
        (DoubleAlong.conjExtend A φ.fiberMap y) =
      DoubleAlong.conjExtend A (fun x => C.core.inChartCoordinates C'.core (DoubleAlong.fold A i)
        (DoubleAlong.fold A j) x (φ.fiberMap x)) y := by
  rw [inChartCoordinates_core, coordChange_doubleAlong, coordChange_doubleAlong]
  -- State the identity on standard coordinates to fix the inherited fibre instances.
  have h : (doubleAlongCoordChange C' A y j y).comp ((DoubleAlong.conjExtend A φ.fiberMap y).comp
      (doubleAlongCoordChange C A i y y)) = DoubleAlong.conjExtend A (fun x =>
        C.core.inChartCoordinates C'.core (DoubleAlong.fold A i) (DoubleAlong.fold A j) x
          (φ.fiberMap x)) y := by
    rw [doubleAlongCoordChange, doubleAlongCoordChange, ← DoubleAlong.conjExtend_comp,
      ← DoubleAlong.conjExtend_comp]
    exact DoubleAlong.conjExtend_congr A (inChartCoordinates_core C C' _ _ _ _).symm
  exact h

/-- The conjugation extension of the fibre maps of a bundle map real over `A` is a continuous
section of the Hom bundle of the doubles. -/
private theorem continuous_conjExtend_fiberMap (φ : C ⟶ C')
    (hφ : ∀ a ∈ A, ∀ v, φ.fiberMap a (star v) = star (φ.fiberMap a v)) :
    Continuous fun y ↦ TotalSpace.mk'
      ((Fin (C.doubleAlong hC).rank → ℂ) →L[ℂ] (Fin (C'.doubleAlong hC').rank → ℂ))
      (E := fun y ↦ (C.doubleAlong hC).core.Fiber y →L[ℂ] (C'.doubleAlong hC').core.Fiber y) y
      (DoubleAlong.conjExtend A φ.fiberMap y) := by
  refine VectorBundleCore.continuous_hom_bundle_iff_forall_continuousOn.2 fun i j ↦ ?_
  have hS : IsOpen
      (C.core.baseSet (DoubleAlong.fold A i) ∩ C'.core.baseSet (DoubleAlong.fold A j)) :=
    (C.core.isOpen_baseSet _).inter (C'.core.isOpen_baseSet _)
  refine (DoubleAlong.continuousOn_conjExtend A hS
    (VectorBundleCore.continuousOn_inChartCoordinates φ.continuous_fiberMap.continuousOn)
    fun a ha => isSelfAdjoint_inChartCoordinates hC hC' φ hφ ha.1 ha.2.1 ha.2.2).congr fun y _ => ?_
  exact inChartCoordinates_doubleAlong_conjExtend hC hC' φ i j y

/-- The double of a bundle map `φ : C ⟶ C'` whose fibre maps over `A` commute with coordinatewise
conjugation: `φ` on the first sheet and its intrinsic conjugate on the second sheet. These agree
over `A`, where `φ` preserves the real subbundles. -/
noncomputable def doubleAlongMap (φ : C ⟶ C')
    (hφ : ∀ a ∈ A, ∀ v, φ.fiberMap a (star v) = star (φ.fiberMap a v)) :
    C.doubleAlong hC ⟶ C'.doubleAlong hC' :=
  VectorBundleCore.CoordinateHom.ofContinuous (DoubleAlong.conjExtend A φ.fiberMap)
    (continuous_conjExtend_fiberMap hC hC' φ hφ)

variable (φ : C ⟶ C') (hφ : ∀ a ∈ A, ∀ v, φ.fiberMap a (star v) = star (φ.fiberMap a v))

/-- The fibre maps of the doubled bundle map are the conjugation extension of those of `φ`. -/
theorem fiberMap_doubleAlongMap (y : DoubleAlong A) :
    (doubleAlongMap hC hC' φ hφ).fiberMap y = DoubleAlong.conjExtend A φ.fiberMap y := by
  rw [doubleAlongMap]
  exact congrFun (VectorBundleCore.CoordinateHom.fiberMap_ofContinuous _ _) y

@[simp] theorem fiberMap_doubleAlongMap_inl (x : X) :
    (doubleAlongMap hC hC' φ hφ).fiberMap (DoubleAlong.inl A x) = φ.fiberMap x := by
  rw [fiberMap_doubleAlongMap, DoubleAlong.conjExtend_inl]

/-- On the second sheet the doubled bundle map is the intrinsic conjugate of `φ`. -/
@[simp] theorem fiberMap_doubleAlongMap_inr (x : X) :
    (doubleAlongMap hC hC' φ hφ).fiberMap (DoubleAlong.inr A x) =
      (star (toConv (φ.fiberMap x))).ofConv := by
  rw [fiberMap_doubleAlongMap, DoubleAlong.conjExtend_inr]
  exact fun hx => (ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _).2 (hφ x hx)

/-- Doubling preserves identities. -/
@[simp] theorem doubleAlongMap_id (h : ∀ a ∈ A, ∀ v, (𝟙 C : C ⟶ C).fiberMap a (star v) =
    star ((𝟙 C : C ⟶ C).fiberMap a v)) :
    doubleAlongMap hC hC (𝟙 C) h = 𝟙 (C.doubleAlong hC) :=
  hom_ext fun y => by
    rw [fiberMap_doubleAlongMap, fiberMap_id, ← DoubleAlong.conjExtend_id A y]
    exact DoubleAlong.conjExtend_congr A (fiberMap_id C _)

/-- Doubling preserves composition. -/
theorem doubleAlongMap_comp (ψ : C' ⟶ C'')
    (hψ : ∀ a ∈ A, ∀ v, ψ.fiberMap a (star v) = star (ψ.fiberMap a v))
    (h : ∀ a ∈ A, ∀ v, (φ ≫ ψ).fiberMap a (star v) = star ((φ ≫ ψ).fiberMap a v)) :
    doubleAlongMap hC hC'' (φ ≫ ψ) h = doubleAlongMap hC hC' φ hφ ≫ doubleAlongMap hC' hC'' ψ hψ :=
  hom_ext fun y => by
    rw [fiberMap_comp, fiberMap_doubleAlongMap, fiberMap_doubleAlongMap, fiberMap_doubleAlongMap]
    -- State the identity on standard coordinates to fix the inherited fibre instances.
    have h : DoubleAlong.conjExtend A (φ ≫ ψ).fiberMap y =
        (DoubleAlong.conjExtend A ψ.fiberMap y).comp (DoubleAlong.conjExtend A φ.fiberMap y) := by
      rw [← DoubleAlong.conjExtend_comp]
      exact DoubleAlong.conjExtend_congr A (fiberMap_comp φ ψ _)
    exact h

/-- The doubled bundle map commutes with the lifted sheet swaps `doubleAlongSwap`. -/
theorem doubleAlongMap_totalSpaceMap_doubleAlongSwap (p : (C.doubleAlong hC).core.TotalSpace) :
    (doubleAlongMap hC hC' φ hφ).totalSpaceMap (C.doubleAlongSwap hC p) =
      C'.doubleAlongSwap hC' ((doubleAlongMap hC hC' φ hφ).totalSpaceMap p) := by
  obtain ⟨z, v⟩ := p
  simp only [VectorBundleCore.CoordinateHom.totalSpaceMap_def]
  refine TotalSpace.ext (by simp) (heq_of_eq ?_)
  simp only [proj_doubleAlongSwap, snd_doubleAlongSwap]
  -- In coordinates: the conjugation extension at the swapped point is the conjugate extension.
  have h (w : Fin C.rank → ℂ) : DoubleAlong.conjExtend A φ.fiberMap (DoubleAlong.swap A z)
      (star w) = star (DoubleAlong.conjExtend A φ.fiberMap z w) := by
    rw [DoubleAlong.conjExtend_swap A fun x hx =>
      (ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _).2 (hφ x hx),
      ContinuousLinearMap.intrinsicStar_apply, star_star]
  rw [fiberMap_doubleAlongMap, fiberMap_doubleAlongMap]
  -- The fibres of the doubles are the coordinate spaces `Fin C.rank → ℂ` and `Fin C'.rank → ℂ`
  -- by definition (`rank_doubleAlong`), where `h` is stated.
  exact h v

/-- On the first sheet the doubled bundle map is `φ`, under the identifications
`doubleAlongInlIso`. -/
@[reassoc] theorem pullbackMap_doubleAlongMap_inl_comp_doubleAlongInlIso_hom :
    pullbackMap (doubleAlongMap hC hC' φ hφ) (DoubleAlong.inl A) ≫ (C'.doubleAlongInlIso hC').hom =
      (C.doubleAlongInlIso hC).hom ≫ φ :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_pullbackMap, fiberMap_doubleAlongMap_inl,
      fiberMap_doubleAlongInlIso_hom]
    -- Both sides are `φ` at `x` composed with identities. The pulled-back double has rank
    -- `C.rank` by definition (`rank_pullback`, `rank_doubleAlong`), so its coordinate fibres are
    -- those of `C`; state the identity on these standard coordinates and close by it.
    have h : (ContinuousLinearMap.id ℂ (Fin C'.rank → ℂ)).comp (φ.fiberMap x) =
        (φ.fiberMap x).comp (ContinuousLinearMap.id ℂ (Fin C.rank → ℂ)) := by
      rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    exact h

/-- On the second sheet the doubled bundle map is the conjugate of `φ`, under the identifications
`doubleAlongInrIso`. -/
@[reassoc] theorem pullbackMap_doubleAlongMap_inr_comp_doubleAlongInrIso_hom :
    pullbackMap (doubleAlongMap hC hC' φ hφ) (DoubleAlong.inr A) ≫ (C'.doubleAlongInrIso hC').hom =
      (C.doubleAlongInrIso hC).hom ≫ (conjugate X).map φ :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_pullbackMap, fiberMap_doubleAlongMap_inr,
      fiberMap_doubleAlongInrIso_hom, fiberMap_conjugate_map]
    -- Both sides are the conjugate of `φ` at `x` composed with identities. The pulled-back double
    -- and `(conjugate X).obj C` have rank `C.rank` by definition (`rank_pullback`,
    -- `rank_doubleAlong`, `rank_conjugate_obj`), so their coordinate fibres are those of `C`;
    -- state the identity on these standard coordinates and close by it.
    have h : (ContinuousLinearMap.id ℂ (Fin C'.rank → ℂ)).comp
        (star (toConv (φ.fiberMap x))).ofConv =
        (star (toConv (φ.fiberMap x))).ofConv.comp (ContinuousLinearMap.id ℂ (Fin C.rank → ℂ)) := by
      rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    exact h

/-- The double of an isomorphism `e : C ≅ C'` whose fibre maps over `A` commute with
coordinatewise conjugation: an isomorphism of the doubles, `e` on the first sheet and its conjugate
on the second sheet. -/
noncomputable def doubleAlongIso (e : C ≅ C')
    (he : ∀ a ∈ A, ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) :
    C.doubleAlong hC ≅ C'.doubleAlong hC' where
  hom := doubleAlongMap hC hC' e.hom he
  inv := doubleAlongMap hC' hC e.inv fun a ha => e.fiberMap_inv_star (he a ha)
  hom_inv_id := by
    rw [← doubleAlongMap_comp _ _ _ _ _ _ _ (by simp)]
    simp only [Iso.hom_inv_id, doubleAlongMap_id]
  inv_hom_id := by
    rw [← doubleAlongMap_comp _ _ _ _ _ _ _ (by simp)]
    simp only [Iso.inv_hom_id, doubleAlongMap_id]

@[simp] theorem doubleAlongIso_hom (e : C ≅ C')
    (he : ∀ a ∈ A, ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) :
    (doubleAlongIso hC hC' e he).hom = doubleAlongMap hC hC' e.hom he :=
  -- The `hom` field of `doubleAlongIso`, as defined above.
  (rfl)

@[simp] theorem doubleAlongIso_inv (e : C ≅ C')
    (he : ∀ a ∈ A, ∀ v, e.hom.fiberMap a (star v) = star (e.hom.fiberMap a v)) :
    (doubleAlongIso hC hC' e he).inv =
      doubleAlongMap hC' hC e.inv fun a ha => e.fiberMap_inv_star (he a ha) :=
  -- The `inv` field of `doubleAlongIso`, as defined above.
  (rfl)

end Map

end TauCeti.FiniteRankBundleCore
