/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic
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
of `C` at the folded points on the first sheet and its intrinsic conjugate on the second sheet;
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

No closedness of `A` is needed. For the boundary of a Riemann surface with boundary this is the
topological doubled bundle over the Schottky double. Smoothness of the double via collars, and
independence of the choices up to isomorphism, are not treated here.

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

open Classical in
/-- The transitions of the doubled core: those of `C` at the folded points on the first sheet, and
their intrinsic conjugates elsewhere. -/
noncomputable def doubleAlongCoordChange (C : FiniteRankBundleCore ℂ X) (A : Set X)
    (i j : DoubleAlong A) : DoubleAlong A → (Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ) :=
  (range (DoubleAlong.inl A)).piecewise
    (fun y => C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j)
      (DoubleAlong.fold A y))
    fun y => (star (toConv (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j)
      (DoubleAlong.fold A y)))).ofConv

@[simp] theorem doubleAlongCoordChange_inl (C : FiniteRankBundleCore ℂ X) (i j : DoubleAlong A)
    (x : X) :
    doubleAlongCoordChange C A i j (DoubleAlong.inl A x) =
      C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j) x := by
  simp [doubleAlongCoordChange]

/-- On the second sheet, away from the glued set, the doubled transition is the conjugate
transition of `C`; no realness of `C` is needed there. -/
theorem doubleAlongCoordChange_inr_of_notMem (C : FiniteRankBundleCore ℂ X) (i j : DoubleAlong A)
    {x : X} (hx : x ∉ A) :
    doubleAlongCoordChange C A i j (DoubleAlong.inr A x) =
      (star (toConv
        (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j) x))).ofConv := by
  have : DoubleAlong.inr A x ∉ range (DoubleAlong.inl A) := by
    rintro ⟨y, hy⟩
    obtain ⟨rfl, hyA⟩ := (DoubleAlong.inl_eq_inr_iff A).1 hy
    exact hx hyA
  simp [doubleAlongCoordChange, this]

/-- On the second sheet the doubled transition is the conjugate transition of `C`, at points of the
two charts. -/
theorem doubleAlongCoordChange_inr {C : FiniteRankBundleCore ℂ X} (hC : C.IsRealAlong A)
    {i j : DoubleAlong A} {x : X} (hi : x ∈ C.core.baseSet (DoubleAlong.fold A i))
    (hj : x ∈ C.core.baseSet (DoubleAlong.fold A j)) :
    doubleAlongCoordChange C A i j (DoubleAlong.inr A x) =
      (star (toConv
        (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j) x))).ofConv := by
  by_cases hx : x ∈ A
  · rw [← DoubleAlong.inl_coe_eq_inr A ⟨x, hx⟩, doubleAlongCoordChange_inl]
    exact (congrArg (fun f : WithConv ((Fin C.rank → ℂ) →L[ℂ] (Fin C.rank → ℂ)) ↦ f.ofConv)
      (hC _ _ x hx hi hj).star_eq).symm
  · exact doubleAlongCoordChange_inr_of_notMem C i j hx

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
  set U := C.core.baseSet (DoubleAlong.fold A i) ∩ C.core.baseSet (DoubleAlong.fold A j)
  have hU : IsOpen U := (C.core.isOpen_baseSet _).inter (C.core.isOpen_baseSet _)
  have hc : ContinuousOn (C.core.coordChange (DoubleAlong.fold A i) (DoubleAlong.fold A j)) U :=
    C.core.continuousOn_coordChange _ _
  have hs : IsOpen (DoubleAlong.fold A ⁻¹' U) := hU.preimage (DoubleAlong.fold A).continuous
  -- Check continuity on each sheet of `X ⊕ X`, through the quotient map onto the double.
  rw [← preimage_inter, (DoubleAlong.isQuotientMap_quotientMap A).continuousOn_isOpen_iff hs,
    (hs.preimage (DoubleAlong.quotientMap A).continuous).continuousOn_iff]
  rintro (x | x) hx
  · rw [mem_preimage, DoubleAlong.quotientMap_inl, mem_preimage, DoubleAlong.fold_inl] at hx
    rw [← IsOpenEmbedding.inl.continuousAt_iff]
    refine (hc.continuousAt (hU.mem_nhds hx)).congr (Eventually.of_forall fun y => ?_)
    simp [DoubleAlong.quotientMap_inl]
  · rw [mem_preimage, DoubleAlong.quotientMap_inr, mem_preimage, DoubleAlong.fold_inr] at hx
    rw [← IsOpenEmbedding.inr.continuousAt_iff]
    refine (ContinuousLinearMap.continuous_intrinsicStar.continuousAt.comp
      (hc.continuousAt (hU.mem_nhds hx))).congr (mem_of_superset (hU.mem_nhds hx) fun y hy => ?_)
    simp only [Function.comp_apply, DoubleAlong.quotientMap_inr]
    exact (doubleAlongCoordChange_inr hC hy.1 hy.2).symm

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

end TauCeti.FiniteRankBundleCore
