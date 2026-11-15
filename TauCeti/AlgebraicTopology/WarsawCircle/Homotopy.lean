/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.WarsawCircle.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.AlgebraicTopology.Homotopy.Whitehead

/-!
# Homotopy groups and non-contractibility of the Warsaw circle

The Warsaw circle `TauCeti.WarsawCircle` is the standard counterexample showing that Whitehead's
theorem (`ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`,
`TauCeti.contractibleSpace_of_subsingleton_homotopyGroup`) and the uniqueness of `K(G, 1)` spaces
(`TauCeti.IsAspherical.exists_homotopyEquiv`) genuinely require CW type.

On the one hand, every continuous map from a compact locally path-connected space `K` into
`WarsawCircle` lifts uniquely along `WarsawCircle.ofHalfLine` to the convex half-line `[0, ∞)`
(`WarsawCircle.existsUnique_lift_ofHalfLine`). Straight-line interpolation in `[0, ∞)` therefore
makes any two maps `f₀, f₁ : C(K, WarsawCircle)` agreeing on a subset `S ⊆ K` homotopic relative to
`S` (`WarsawCircle.homotopicRel_of_eqOn`). Taking `K = I` and `K = I^N` shows that `WarsawCircle`
is simply connected and that `HomotopyGroup N WarsawCircle w` is a subsingleton for every indexing
type `N` and base point `w`. Hence `WarsawCircle` is aspherical (`WarsawCircle.isAspherical`), is
an Eilenberg--Mac Lane space of type `K(G, 1)` for every trivial group `G`
(`WarsawCircle.isEilenbergMacLaneSpaceOne`), and every map in either direction between
`WarsawCircle` and a contractible space is a weak homotopy equivalence.

On the other hand, collapsing the vertical limit segment `{0} × [-1, 1]` to `0` defines a
surjective quotient map `WarsawCircle.collapse : C(WarsawCircle, AddCircle (1 : ℝ))` that is **not**
nullhomotopic (`WarsawCircle.not_nullhomotopic_collapse`). Indeed, by homotopy lifting along the
universal cover `ℝ → AddCircle (1 : ℝ)`, a nullhomotopy of `collapse` would yield a continuous lift
`g : C(WarsawCircle, ℝ)`. Connectedness forces `g ∘ ofHalfLine` to be a constant `c` on `[0, 2]`,
to reach `c + 1/2` at the junction `t = 5`, and to equal `c + 1 - (2 * (t - 4))⁻¹` on `[5, ∞)`.
Along `t_n = 4 + 2π(n + 1) → ∞`, the points `ofHalfLine t_n` converge in `WarsawCircle` to
`WarsawCircle.origin = ofHalfLine 1`, forcing `c = c + 1`. Consequently `WarsawCircle` is neither
contractible (`WarsawCircle.not_contractibleSpace`) nor of CW type (`WarsawCircle.not_cwType`).

## Main definitions

* `TauCeti.WarsawCircle.homotopyRelOfEqOn`: relative homotopy between maps from a compact locally
  path-connected space into `WarsawCircle` agreeing on `S`.
* `TauCeti.WarsawCircle.collapse`: the quotient map `C(WarsawCircle, AddCircle (1 : ℝ))` collapsing
  `warsawCircleLimitSegment` to `0`.

## Main results

* `SimplyConnectedSpace TauCeti.WarsawCircle` and
  `Subsingleton (HomotopyGroup N TauCeti.WarsawCircle w)`: simple connectedness and vanishing of
  all cubical homotopy groups.
* `TauCeti.WarsawCircle.isAspherical` and `TauCeti.WarsawCircle.isEilenbergMacLaneSpaceOne`:
  `WarsawCircle` is aspherical and a `K(1, 1)` space.
* `TauCeti.WarsawCircle.isQuotientMap_collapse` and
  `TauCeti.WarsawCircle.collapse_eq_collapse_iff`: `collapse` identifies `AddCircle (1 : ℝ)` with
  the quotient of `WarsawCircle` collapsing the vertical limit segment.
* `TauCeti.WarsawCircle.not_nullhomotopic_collapse`,
  `TauCeti.WarsawCircle.not_contractibleSpace`, and `TauCeti.WarsawCircle.not_cwType`:
  `collapse` is essential, so `WarsawCircle` is neither contractible nor of CW type.

## References

* R. Schwamberger and R. M. Vogt, *Dold spaces in homotopy theory*, Algebr. Geom. Topol. **9**
  (2009), 1585--1622.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3 and Section 4.1.
-/

public section

noncomputable section

open Filter Function Set Topology
open scoped ContinuousMap Topology.Homotopy unitInterval

namespace TauCeti.WarsawCircle

/-! ### Weak contractibility via lifting to `[0, ∞)` -/

/-- **Relative homotopy via `[0, ∞)`.** Any two continuous maps from a compact locally
path-connected space `K` into `WarsawCircle` that agree on `S : Set K` are joined by a canonical
homotopy relative to `S`, obtained by pushing forward straight-line interpolation between their
lifts in `[0, ∞)`. -/
def homotopyRelOfEqOn {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] {f₀ f₁ : C(K, WarsawCircle)} {S : Set K}
    (hS : S.EqOn f₀ f₁) : f₀.HomotopyRel f₁ S where
  toContinuousMap := ofHalfLine.comp
    { toFun := fun sk : I × K ↦
        ⟨(1 - (sk.1 : ℝ)) * (liftOfHalfLine f₀ sk.2 : ℝ) +
          (sk.1 : ℝ) * (liftOfHalfLine f₁ sk.2 : ℝ),
          mem_Ici.mpr (add_nonneg
            (mul_nonneg (sub_nonneg.mpr sk.1.2.2) (liftOfHalfLine f₀ sk.2).2)
            (mul_nonneg sk.1.2.1 (liftOfHalfLine f₁ sk.2).2))⟩
      continuous_toFun := by fun_prop }
  map_zero_left k := by
    simp
  map_one_left k := by
    simp
  prop' s k hk := by
    have hlift : liftOfHalfLine f₀ k = liftOfHalfLine f₁ k :=
      ofHalfLine_injective (by simp [hS hk])
    have hline :
        (⟨(1 - (s : ℝ)) * (liftOfHalfLine f₀ k : ℝ) + (s : ℝ) * (liftOfHalfLine f₁ k : ℝ),
          mem_Ici.mpr (add_nonneg
            (mul_nonneg (sub_nonneg.mpr s.2.2) (liftOfHalfLine f₀ k).2)
            (mul_nonneg s.2.1 (liftOfHalfLine f₁ k).2))⟩ : Ici (0 : ℝ)) =
        liftOfHalfLine f₀ k := by
      ext; dsimp; rw [hlift]; ring
    simp [hline]

/-- Two continuous maps from a compact locally path-connected space into `WarsawCircle` agreeing on
`S` are homotopic relative to `S`. -/
theorem homotopicRel_of_eqOn {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] {f₀ f₁ : C(K, WarsawCircle)} {S : Set K}
    (hS : S.EqOn f₀ f₁) : f₀.HomotopicRel f₁ S :=
  ⟨homotopyRelOfEqOn hS⟩

/-- Any two continuous maps from a compact locally path-connected space into `WarsawCircle` are
homotopic. -/
theorem homotopic_of_compactSpace {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] (f₀ f₁ : C(K, WarsawCircle)) : f₀.Homotopic f₁ :=
  ⟨(homotopyRelOfEqOn (S := ∅) (eqOn_empty f₀ f₁)).toHomotopy⟩

/-- Every continuous map from a compact locally path-connected space into `WarsawCircle` is
nullhomotopic. -/
theorem nullhomotopic_of_compactSpace {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [LocallyPathConnectedSpace K] (f : C(K, WarsawCircle)) : f.Nullhomotopic :=
  ⟨basepoint, homotopic_of_compactSpace f (ContinuousMap.const K basepoint)⟩

/-- **The Warsaw circle is simply connected.** -/
instance instSimplyConnectedSpace : SimplyConnectedSpace WarsawCircle := by
  have : LocallyPathConnectedSpace I := Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  refine simply_connected_iff_paths_homotopic'.mpr ⟨inferInstance, fun {x y} p₁ p₂ ↦ ?_⟩
  refine homotopicRel_of_eqOn (f₀ := p₁.toContinuousMap) (f₁ := p₂.toContinuousMap) ?_
  rintro s (rfl | rfl) <;> simp

/-- **All cubical homotopy groups of the Warsaw circle are trivial**, for any indexing type `N` of
cube directions and any base point `w`. -/
instance instSubsingletonHomotopyGroup (N : Type*) (w : WarsawCircle) :
    Subsingleton (HomotopyGroup N WarsawCircle w) := by
  have : LocallyPathConnectedSpace I := Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, left_mem_Icc.mpr zero_le_one⟩)
  refine ⟨Quotient.ind₂ fun p q ↦ Quotient.sound ?_⟩
  exact homotopicRel_of_eqOn fun y hy ↦
    (GenLoop.boundary p y hy).trans (GenLoop.boundary q y hy).symm

/-- **The Warsaw circle is aspherical** at every base point. -/
theorem isAspherical (w : WarsawCircle) : IsAspherical WarsawCircle w :=
  IsAspherical.mk inferInstance fun _ ↦ inferInstance

/-- **The Warsaw circle is an Eilenberg--Mac Lane space of type `K(G, 1)`** for every trivial group
`G`. -/
theorem isEilenbergMacLaneSpaceOne (G : Type*) [Group G] [Subsingleton G] (w : WarsawCircle) :
    IsEilenbergMacLaneSpaceOne G WarsawCircle w :=
  IsEilenbergMacLaneSpaceOne.mk (isAspherical w)
    ⟨MulEquiv.ofBijective (1 : FundamentalGroup WarsawCircle w →* G) (bijective_of_subsingleton' _)⟩

/-- **Every continuous map from a contractible space to the Warsaw circle is a weak homotopy
equivalence.** -/
theorem isWeakHomotopyEquivalence_of_contractibleSpace {X : Type*} [TopologicalSpace X]
    [ContractibleSpace X] (f : C(X, WarsawCircle)) : f.IsWeakHomotopyEquivalence :=
  (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective (Classical.arbitrary X)).2
    fun _ ↦ bijective_of_subsingleton' _

/-- **Every continuous map from the Warsaw circle to a contractible space is a weak homotopy
equivalence.** -/
theorem isWeakHomotopyEquivalence_to_contractibleSpace {X : Type*} [TopologicalSpace X]
    [ContractibleSpace X] (f : C(WarsawCircle, X)) : f.IsWeakHomotopyEquivalence :=
  (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective basepoint).2
    fun _ ↦ bijective_of_subsingleton' _

/-! ### The quotient map `WarsawCircle.collapse` onto `AddCircle (1 : ℝ)` -/

/-- Phase function on `warsawCircleSineCurve`: maps `x ∈ [0, 1]` to `1 - x / 2 ∈ [1/2, 1]`, sending
the vertical limit segment `x = 0` to `1 ≡ 0 (mod 1)` and `(1, sin 1)` to `1/2`. -/
private def sinePhase (p : ℝ × ℝ) : ℝ :=
  1 - p.1 / 2

/-- Polynomial phase function on `warsawCircleClosingArc`: maps `(0, -1)` to `0` and increases
strictly along the three segments of the closing arc to `1/2` at `(1, sin 1)`. -/
private def arcPhase (p : ℝ × ℝ) : ℝ :=
  (p.1 + 1 + (1 - 2 * p.1) * (-2 - p.2)) / (2 * (4 + Real.sin 1))

/-- `sinePhase` evaluates to `1` along the vertical axis `x = 0`. -/
private theorem sinePhase_zero_fst (y : ℝ) : sinePhase (0, y) = 1 := by
  simp [sinePhase]

/-- `sinePhase` evaluates to `1 / 2` along the vertical line `x = 1`. -/
private theorem sinePhase_one_fst (y : ℝ) : sinePhase (1, y) = 1 / 2 := by
  simp [sinePhase]; norm_num

/-- `arcPhase` vanishes at `(0, -1)`. -/
private theorem arcPhase_zero_neg_one : arcPhase (0, -1) = 0 := by
  unfold arcPhase; dsimp; norm_num

/-- `arcPhase` evaluates to `1 / 2` at `(1, sin 1)`. -/
private theorem arcPhase_one_sin_one : arcPhase (1, Real.sin 1) = 1 / 2 := by
  have hL : 4 + Real.sin 1 ≠ 0 := by linarith [Real.neg_one_le_sin 1]
  unfold arcPhase
  dsimp
  have hnum : 1 + 1 + (1 - 2 * 1) * (-2 - Real.sin 1) = 4 + Real.sin 1 := by ring
  rw [hnum, mul_comm 2 (4 + Real.sin 1), div_mul_eq_div_div, div_self hL]

/-- At both junction points `(0, -1)` and `(1, sin 1)` where `warsawCircleSineCurve` meets
`warsawCircleClosingArc`, `sinePhase` and `arcPhase` agree in `AddCircle (1 : ℝ)`. -/
private theorem coe_sinePhase_eq_coe_arcPhase_of_mem_inter {p : ℝ × ℝ}
    (hp : p ∈ warsawCircleSineCurve ∩ warsawCircleClosingArc) :
    (sinePhase p : AddCircle (1 : ℝ)) = (arcPhase p : AddCircle (1 : ℝ)) := by
  rw [warsawCircleSineCurve_inter_warsawCircleClosingArc] at hp
  rcases hp with rfl | rfl
  · rw [sinePhase_zero_fst, arcPhase_zero_neg_one, AddCircle.coe_period, QuotientAddGroup.mk_zero]
  · rw [sinePhase_one_fst, arcPhase_one_sin_one]

/-- Glued raw phase map `ℝ × ℝ → AddCircle (1 : ℝ)`. -/
private def rawCollapse (p : ℝ × ℝ) : AddCircle (1 : ℝ) := by
  classical
  exact if p ∈ warsawCircleSineCurve then (sinePhase p : AddCircle (1 : ℝ))
    else (arcPhase p : AddCircle (1 : ℝ))

/-- Formula for `rawCollapse` on `warsawCircleSineCurve`. -/
private theorem rawCollapse_eq_of_mem_warsawCircleSineCurve {p : ℝ × ℝ}
    (hp : p ∈ warsawCircleSineCurve) :
    rawCollapse p = (sinePhase p : AddCircle (1 : ℝ)) := by
  simp [rawCollapse, hp]

/-- Formula for `rawCollapse` on `warsawCircleClosingArc`. -/
private theorem rawCollapse_eq_of_mem_warsawCircleClosingArc {p : ℝ × ℝ}
    (hp : p ∈ warsawCircleClosingArc) :
    rawCollapse p = (arcPhase p : AddCircle (1 : ℝ)) := by
  unfold rawCollapse
  split_ifs with hs
  · exact coe_sinePhase_eq_coe_arcPhase_of_mem_inter ⟨hs, hp⟩
  · rfl

/-- Continuity of `rawCollapse` on `warsawCircleSet` via the pasting lemma for closed subsets. -/
private theorem continuousOn_rawCollapse : ContinuousOn rawCollapse warsawCircleSet := by
  have hs : ContinuousOn rawCollapse warsawCircleSineCurve :=
    ((continuous_quotient_mk'.comp (by unfold sinePhase; fun_prop)).continuousOn).congr
      fun _ hp ↦ rawCollapse_eq_of_mem_warsawCircleSineCurve hp
  have hc : ContinuousOn rawCollapse warsawCircleClosingArc :=
    ((continuous_quotient_mk'.comp (by unfold arcPhase; fun_prop)).continuousOn).congr
      fun _ hp ↦ rawCollapse_eq_of_mem_warsawCircleClosingArc hp
  rw [warsawCircleSet_eq_union]
  exact hs.union_of_isClosed hc isClosed_warsawCircleSineCurve isClosed_warsawCircleClosingArc

/-- **The canonical collapse map `C(WarsawCircle, AddCircle (1 : ℝ))`**, sending the vertical limit
segment `{0} × [-1, 1]` to `0` and wrapping the rest of the Warsaw circle homeomorphically around
the punctured circle. -/
def collapse : C(WarsawCircle, AddCircle (1 : ℝ)) where
  toFun := warsawCircleSet.domRestrict rawCollapse
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp continuousOn_rawCollapse

/-- On `warsawCircleSineCurve`, `collapse` is `(1 - x / 2 : AddCircle (1 : ℝ))`. -/
theorem collapse_eq_of_mem_warsawCircleSineCurve {w : WarsawCircle}
    (hw : (w : ℝ × ℝ) ∈ warsawCircleSineCurve) :
    collapse w = ((1 - (w : ℝ × ℝ).1 / 2 : ℝ) : AddCircle (1 : ℝ)) :=
  rawCollapse_eq_of_mem_warsawCircleSineCurve hw

/-- On `warsawCircleClosingArc`, `collapse` is given by the rational phase formula from `0` at
`(0, -1)` to `1 / 2` at `(1, sin 1)`. -/
theorem collapse_eq_of_mem_warsawCircleClosingArc {w : WarsawCircle}
    (hw : (w : ℝ × ℝ) ∈ warsawCircleClosingArc) :
    collapse w =
      ((((w : ℝ × ℝ).1 + 1 + (1 - 2 * (w : ℝ × ℝ).1) * (-2 - (w : ℝ × ℝ).2)) /
        (2 * (4 + Real.sin 1)) : ℝ) : AddCircle (1 : ℝ)) :=
  rawCollapse_eq_of_mem_warsawCircleClosingArc hw

/-- On `warsawCircleLimitSegment`, `collapse` vanishes. -/
theorem collapse_eq_zero_of_mem_warsawCircleLimitSegment {w : WarsawCircle}
    (hw : (w : ℝ × ℝ) ∈ warsawCircleLimitSegment) : collapse w = 0 := by
  rw [collapse_eq_of_mem_warsawCircleSineCurve (mem_warsawCircleSineCurve_iff.mpr (Or.inl hw)),
    (mem_warsawCircleLimitSegment_iff.mp hw).1]
  simp

/-- At `basepoint = (0, -1)`, `collapse` vanishes. -/
@[simp]
theorem collapse_basepoint : collapse basepoint = 0 :=
  collapse_eq_zero_of_mem_warsawCircleLimitSegment <| by
    rw [mem_warsawCircleLimitSegment_iff, coe_basepoint]; norm_num

/-- At `origin = (0, 0)`, `collapse` vanishes. -/
@[simp]
theorem collapse_origin : collapse origin = 0 :=
  collapse_eq_zero_of_mem_warsawCircleLimitSegment <| by
    rw [mem_warsawCircleLimitSegment_iff, coe_origin]; norm_num

/-- At `rightEndpoint = (1, sin 1)`, `collapse` equals `1 / 2`. -/
@[simp]
theorem collapse_rightEndpoint : collapse rightEndpoint = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  have hmem : (rightEndpoint : ℝ × ℝ) ∈ warsawCircleSineCurve :=
    mem_warsawCircleSineCurve_iff.mpr (Or.inr (mem_warsawCircleSineGraph_iff.mpr
      ⟨by rw [coe_rightEndpoint]; exact ⟨zero_lt_one, le_rfl⟩, by rw [coe_rightEndpoint]; simp⟩))
  rw [collapse_eq_of_mem_warsawCircleSineCurve hmem, coe_rightEndpoint]
  exact congrArg (QuotientAddGroup.mk' _) (by norm_num)

/-- Explicit real lift of `collapse (ofHalfLine t)` mapping `[0, 2]` to `0` and `(2, ∞)` strictly
monotonically onto `(0, 1)`. -/
private def halfLinePhase (t : Ici (0 : ℝ)) : ℝ :=
  if (t : ℝ) ≤ 2 then 0
  else if (t : ℝ) ≤ 5 then arcPhase (ofHalfLine t : ℝ × ℝ)
  else sinePhase (ofHalfLine t : ℝ × ℝ)

/-- `halfLinePhase t` lifts `collapse (ofHalfLine t)` to `ℝ`. -/
private theorem coe_halfLinePhase (t : Ici (0 : ℝ)) :
    (halfLinePhase t : AddCircle (1 : ℝ)) = collapse (ofHalfLine t) := by
  unfold halfLinePhase
  split_ifs with h2 h5
  · rw [QuotientAddGroup.mk_zero, collapse_eq_zero_of_mem_warsawCircleLimitSegment
      (coe_ofHalfLine_mem_warsawCircleLimitSegment_of_le_two h2)]
  · symm
    exact rawCollapse_eq_of_mem_warsawCircleClosingArc
      (coe_ofHalfLine_mem_warsawCircleClosingArc_of_mem_Icc ⟨le_of_not_ge h2, h5⟩)
  · symm
    exact rawCollapse_eq_of_mem_warsawCircleSineCurve (mem_warsawCircleSineCurve_iff.mpr
      (Or.inr (coe_ofHalfLine_mem_warsawCircleSineGraph_of_five_le (le_of_not_ge h5))))

/-- Algebraic formula for `arcPhase (ofHalfLine t)` on `[0, 4]` and `(4, 5]`. -/
private theorem arcPhase_ofHalfLine_formula {t : Ici (0 : ℝ)} (ht5 : (t : ℝ) ≤ 5) :
    arcPhase (ofHalfLine t : ℝ × ℝ) =
      if (t : ℝ) ≤ 4 then ((t : ℝ) - 2) / (2 * (4 + Real.sin 1))
      else (2 + ((t : ℝ) - 4) * (Real.sin 1 + 2)) / (2 * (4 + Real.sin 1)) := by
  split_ifs with h4
  · rcases le_or_gt (t : ℝ) 3 with h3 | h3
    · rw [coe_ofHalfLine_of_le_three h3]; unfold arcPhase; dsimp; ring
    · rw [coe_ofHalfLine_of_mem_Icc_three_four ⟨h3.le, h4⟩]; unfold arcPhase; dsimp; ring
  · rw [coe_ofHalfLine_of_mem_Icc_four_five ⟨le_of_not_ge h4, ht5⟩]; unfold arcPhase; dsimp; ring

/-- For `t > 2`, `halfLinePhase t` lies strictly between `0` and `1`. -/
private theorem halfLinePhase_mem_Ioo_of_two_lt {t : Ici (0 : ℝ)} (ht2 : 2 < (t : ℝ)) :
    halfLinePhase t ∈ Ioo (0 : ℝ) 1 := by
  have hL : 0 < 4 + Real.sin 1 := by linarith [Real.neg_one_le_sin 1]
  have hsin : 0 < Real.sin 1 + 2 := by linarith [Real.neg_one_le_sin 1]
  unfold halfLinePhase
  rw [ite_eq_right (not_le.mpr ht2)]
  split_ifs with h5
  · rw [arcPhase_ofHalfLine_formula h5]
    split_ifs with h4
    · exact ⟨div_pos (by linarith) (by positivity),
        (div_lt_one (by positivity)).mpr (by linarith)⟩
    · refine ⟨div_pos (by nlinarith) (by positivity), (div_lt_one (by positivity)).mpr ?_⟩
      nlinarith
  · rw [coe_ofHalfLine_of_five_le (le_of_not_ge h5)]
    unfold sinePhase; dsimp
    have hinv_le : ((t : ℝ) - 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hinv_pos : 0 < ((t : ℝ) - 4)⁻¹ := inv_pos.mpr (by linarith)
    exact ⟨by linarith, by linarith⟩

/-- Every value `halfLinePhase t` lies in the fundamental domain `[0, 1)`. -/
private theorem halfLinePhase_mem_Ico (t : Ici (0 : ℝ)) : halfLinePhase t ∈ Ico (0 : ℝ) 1 := by
  rcases le_or_gt (t : ℝ) 2 with h2 | h2
  · simp [halfLinePhase, h2]
  · exact Ioo_subset_Ico_self (halfLinePhase_mem_Ioo_of_two_lt h2)

/-- `halfLinePhase` is strictly monotone on `(2, ∞)`. -/
private theorem strictMonoOn_halfLinePhase :
    StrictMonoOn halfLinePhase {t : Ici (0 : ℝ) | 2 < (t : ℝ)} := by
  intro s hs t ht hst
  have hs2 : 2 < (s : ℝ) := hs
  have ht2 : 2 < (t : ℝ) := ht
  have hst' : (s : ℝ) < (t : ℝ) := Subtype.coe_lt_coe.mpr hst
  have hL : 0 < 2 * (4 + Real.sin 1) := by linarith [Real.neg_one_le_sin 1]
  have hsin : 0 < Real.sin 1 + 2 := by linarith [Real.neg_one_le_sin 1]
  unfold halfLinePhase
  rw [ite_eq_right (not_le.mpr hs2), ite_eq_right (not_le.mpr ht2)]
  rcases le_or_gt (s : ℝ) 5 with hs5 | hs5 <;> rcases le_or_gt (t : ℝ) 5 with ht5 | ht5
  · simp only [hs5, ht5, ↓reduceIte]
    rw [arcPhase_ofHalfLine_formula hs5, arcPhase_ofHalfLine_formula ht5]
    split_ifs with hs4 ht4
    · exact div_lt_div_of_pos_right (by linarith) hL
    · exact div_lt_div_of_pos_right (by nlinarith) hL
    · linarith
    · exact div_lt_div_of_pos_right (by nlinarith) hL
  · simp only [hs5, not_le.mpr ht5, ↓reduceIte]
    rw [arcPhase_ofHalfLine_formula hs5, coe_ofHalfLine_of_five_le ht5.le]
    unfold sinePhase; dsimp
    have hle_half : (if (s : ℝ) ≤ 4 then ((s : ℝ) - 2) / (2 * (4 + Real.sin 1))
        else (2 + ((s : ℝ) - 4) * (Real.sin 1 + 2)) / (2 * (4 + Real.sin 1))) ≤ 1 / 2 := by
      split_ifs with hs4 <;> rw [div_le_iff₀ hL] <;> nlinarith
    have hgt_half : 1 / 2 < 1 - ((t : ℝ) - 4)⁻¹ / 2 := by
      have : ((t : ℝ) - 4)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      linarith
    exact lt_of_le_of_lt hle_half hgt_half
  · linarith
  · simp only [not_le.mpr hs5, not_le.mpr ht5, ↓reduceIte]
    rw [coe_ofHalfLine_of_five_le hs5.le, coe_ofHalfLine_of_five_le ht5.le]
    unfold sinePhase; dsimp
    have : ((t : ℝ) - 4)⁻¹ < ((s : ℝ) - 4)⁻¹ := inv_strictAnti₀ (by linarith) (by linarith)
    linarith

/-- **`collapse w = 0` if and only if `w` lies on the vertical limit segment `{0} × [-1, 1]`.** -/
@[simp]
theorem collapse_eq_zero_iff {w : WarsawCircle} :
    collapse w = 0 ↔ (w : ℝ × ℝ) ∈ warsawCircleLimitSegment := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  obtain ⟨t, rfl⟩ := ofHalfLine_surjective w
  rw [← coe_halfLinePhase, AddCircle.coe_eq_zero_iff_of_mem_Ico (halfLinePhase_mem_Ico t),
    coe_ofHalfLine_mem_warsawCircleLimitSegment_iff]
  rcases le_or_gt (t : ℝ) 2 with h2 | h2
  · simp [halfLinePhase, h2]
  · exact iff_of_false (halfLinePhase_mem_Ioo_of_two_lt h2).1.ne' (not_le.mpr h2)

/-- **Fibers of `WarsawCircle.collapse`**: two points have the same image under `collapse` if and
only if they are equal or both belong to `warsawCircleLimitSegment`. -/
theorem collapse_eq_collapse_iff {w₁ w₂ : WarsawCircle} :
    collapse w₁ = collapse w₂ ↔
      w₁ = w₂ ∨
        ((w₁ : ℝ × ℝ) ∈ warsawCircleLimitSegment ∧ (w₂ : ℝ × ℝ) ∈ warsawCircleLimitSegment) := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  obtain ⟨t₁, rfl⟩ := ofHalfLine_surjective w₁
  obtain ⟨t₂, rfl⟩ := ofHalfLine_surjective w₂
  have hm₁ : halfLinePhase t₁ ∈ Ico (0 : ℝ) (0 + 1) := by simpa using halfLinePhase_mem_Ico t₁
  have hm₂ : halfLinePhase t₂ ∈ Ico (0 : ℝ) (0 + 1) := by simpa using halfLinePhase_mem_Ico t₂
  rw [← coe_halfLinePhase, ← coe_halfLinePhase,
    AddCircle.coe_eq_coe_iff_of_mem_Ico hm₁ hm₂,
    coe_ofHalfLine_mem_warsawCircleLimitSegment_iff,
    coe_ofHalfLine_mem_warsawCircleLimitSegment_iff]
  rcases le_or_gt (t₁ : ℝ) 2 with h₁ | h₁ <;> rcases le_or_gt (t₂ : ℝ) 2 with h₂ | h₂
  · simp [halfLinePhase, h₁, h₂]
  · have h0 : halfLinePhase t₁ = 0 := by simp [halfLinePhase, h₁]
    have hpos := (halfLinePhase_mem_Ioo_of_two_lt h₂).1
    refine iff_of_false (by linarith) ?_
    rintro (heq | ⟨-, hle⟩)
    · have := congrArg (Subtype.val : Ici (0 : ℝ) → ℝ) (ofHalfLine_injective heq); linarith
    · linarith
  · have h0 : halfLinePhase t₂ = 0 := by simp [halfLinePhase, h₂]
    have hpos := (halfLinePhase_mem_Ioo_of_two_lt h₁).1
    refine iff_of_false (by linarith) ?_
    rintro (heq | ⟨hle, -⟩)
    · have := congrArg (Subtype.val : Ici (0 : ℝ) → ℝ) (ofHalfLine_injective heq); linarith
    · linarith
  · simp only [not_le.mpr h₁, not_le.mpr h₂, and_false, or_false, ofHalfLine_injective.eq_iff]
    exact strictMonoOn_halfLinePhase.injOn.eq_iff h₁ h₂

/-- **`WarsawCircle.collapse` is surjective.** -/
theorem collapse_surjective : Surjective collapse := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  intro z
  obtain ⟨r, hr, rfl⟩ := AddCircle.eq_coe_Ico z
  rcases le_or_gt r (1 / 2) with hr_half | hr_half
  · let φ : ℝ → ℝ := fun u ↦ arcPhase (ofHalfLine ⟨max u 0, le_max_right u 0⟩ : ℝ × ℝ)
    have hφ_cont : Continuous φ := by unfold φ arcPhase; fun_prop
    have hφ2 : φ 2 = 0 := by
      dsimp [φ]
      have hmax : (⟨max (2 : ℝ) 0, le_max_right 2 0⟩ : Ici (0 : ℝ)) = ⟨2, by norm_num⟩ := by
        ext; norm_num
      rw [hmax, ofHalfLine_two, coe_basepoint, arcPhase_zero_neg_one]
    have hφ5 : φ 5 = 1 / 2 := by
      dsimp [φ]
      have hmax : (⟨max (5 : ℝ) 0, le_max_right 5 0⟩ : Ici (0 : ℝ)) = ⟨5, by norm_num⟩ := by
        ext; norm_num
      rw [hmax, ofHalfLine_five, coe_rightEndpoint, arcPhase_one_sin_one]
    have hivt : Icc (0 : ℝ) (1 / 2) ⊆ φ '' Icc 2 5 := by
      simpa [hφ2, hφ5] using intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 5) hφ_cont.continuousOn
    obtain ⟨u, hu, rfl⟩ := hivt ⟨hr.1, hr_half⟩
    let t : Ici (0 : ℝ) := ⟨max u 0, le_max_right u 0⟩
    have ht : (t : ℝ) ∈ Icc 2 5 := by
      dsimp [t]; rw [max_eq_left (by linarith [hu.1])]; exact hu
    exact ⟨ofHalfLine t, rawCollapse_eq_of_mem_warsawCircleClosingArc
      (coe_ofHalfLine_mem_warsawCircleClosingArc_of_mem_Icc ht)⟩
  · let x : ℝ := 2 * (1 - r)
    have hx0 : 0 < x := by linarith [hr.2]
    have hx1 : x ≤ 1 := by linarith
    have hxinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
    let t : Ici (0 : ℝ) := ⟨4 + x⁻¹, mem_Ici.mpr (by positivity)⟩
    have ht5 : 5 ≤ (t : ℝ) := by dsimp [t]; linarith
    refine ⟨ofHalfLine t, ?_⟩
    rw [collapse_eq_of_mem_warsawCircleSineCurve (mem_warsawCircleSineCurve_iff.mpr
      (Or.inr (coe_ofHalfLine_mem_warsawCircleSineGraph_of_five_le ht5))),
      coe_ofHalfLine_of_five_le ht5]
    congr 1
    dsimp [t, x]
    rw [add_sub_cancel_left, inv_inv]
    ring

/-- **`WarsawCircle.collapse` is a quotient map**, exhibiting `AddCircle (1 : ℝ)` as the quotient
of `WarsawCircle` obtained by collapsing the vertical limit segment `{0} × [-1, 1]` to `0`. -/
theorem isQuotientMap_collapse : IsQuotientMap collapse :=
  collapse.continuous.isClosedMap.isQuotientMap collapse.continuous collapse_surjective

/-! ### Non-nullhomotopy of `collapse`, non-contractibility, and failure of CW type -/

/-- Any hypothetical continuous lift `g : C(WarsawCircle, ℝ)` of `collapse` satisfies
`g rightEndpoint = g origin + 1 / 2`. -/
private theorem lift_collapse_rightEndpoint_eq (g : C(WarsawCircle, ℝ))
    (hg : ∀ w, (g w : AddCircle (1 : ℝ)) = collapse w) :
    g rightEndpoint = g origin + 1 / 2 := by
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let ψ : C(Ici (0 : ℝ), ℝ) := g.comp ofHalfLine
  have hco : (g origin : AddCircle (1 : ℝ)) = 0 := by rw [hg, collapse_origin]
  have h12 : ψ ⟨2, by norm_num⟩ = g origin := by
    have : PreconnectedSpace (Icc (0 : ℝ) 2) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    let ι₀₂ : C(Icc (0 : ℝ) 2, Ici (0 : ℝ)) :=
      ⟨fun u ↦ ⟨u.1, u.2.1⟩, continuous_subtype_val.subtype_mk _⟩
    have hconst := cov.const_of_comp (ψ.comp ι₀₂).continuous
      (fun u v ↦ by
        dsimp [ψ]
        rw [hg, hg, collapse_eq_zero_of_mem_warsawCircleLimitSegment
            (coe_ofHalfLine_mem_warsawCircleLimitSegment_of_le_two u.2.2),
          collapse_eq_zero_of_mem_warsawCircleLimitSegment
            (coe_ofHalfLine_mem_warsawCircleLimitSegment_of_le_two v.2.2)])
      ⟨2, by norm_num, le_rfl⟩ ⟨1, zero_le_one, by norm_num⟩
    simpa [ψ, ι₀₂] using hconst
  let ι₂₅ : C(Icc (2 : ℝ) 5, Ici (0 : ℝ)) :=
    ⟨fun u ↦ ⟨u.1, mem_Ici.mpr (by linarith [u.2.1])⟩, continuous_subtype_val.subtype_mk _⟩
  have : PreconnectedSpace (Icc (2 : ℝ) 5) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let φ₂₅ : Icc (2 : ℝ) 5 → ℝ := fun u ↦ g origin + arcPhase (ofHalfLine (ι₂₅ u) : ℝ × ℝ)
  have hφ_cont : Continuous φ₂₅ := by unfold φ₂₅ arcPhase; fun_prop
  have hcomp_eq :
      ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ (ψ ∘ ι₂₅) = ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ φ₂₅ := by
    ext u
    dsimp [ψ, φ₂₅]
    rw [hco, zero_add, hg]
    exact rawCollapse_eq_of_mem_warsawCircleClosingArc
      (coe_ofHalfLine_mem_warsawCircleClosingArc_of_mem_Icc u.2)
  have h2_eq : (ψ ∘ ι₂₅) ⟨2, le_rfl, by norm_num⟩ = φ₂₅ ⟨2, le_rfl, by norm_num⟩ := by
    dsimp [φ₂₅, ι₂₅]
    rw [h12, ofHalfLine_two, coe_basepoint, arcPhase_zero_neg_one, add_zero]
  have heq := congrFun (cov.eq_of_comp_eq (ψ.comp ι₂₅).continuous hφ_cont hcomp_eq
    ⟨2, le_rfl, by norm_num⟩ h2_eq) ⟨5, by norm_num, le_rfl⟩
  simpa [ψ, φ₂₅, ι₂₅, arcPhase_one_sin_one] using heq

/-- Any hypothetical continuous lift `g : C(WarsawCircle, ℝ)` of `collapse` along
`ℝ → AddCircle (1 : ℝ)` must equal `g origin + 1 - (ofHalfLine t).1 / 2` for all `t ≥ 5`. -/
private theorem lift_collapse_ofHalfLine_eq_of_five_le (g : C(WarsawCircle, ℝ))
    (hg : ∀ w, (g w : AddCircle (1 : ℝ)) = collapse w) {t : Ici (0 : ℝ)} (ht : 5 ≤ (t : ℝ)) :
    g (ofHalfLine t) = g origin + 1 - (ofHalfLine t : ℝ × ℝ).1 / 2 := by
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let ψ : C(Ici (0 : ℝ), ℝ) := g.comp ofHalfLine
  have hco : (g origin : AddCircle (1 : ℝ)) = 0 := by rw [hg, collapse_origin]
  let ι₅ : C(Ici (5 : ℝ), Ici (0 : ℝ)) :=
    ⟨fun u ↦ ⟨u.1, mem_Ici.mpr (by linarith [mem_Ici.mp u.2])⟩,
      continuous_subtype_val.subtype_mk _⟩
  have : PreconnectedSpace (Ici (5 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp (convex_Ici 5).isPreconnected
  let φ₅ : Ici (5 : ℝ) → ℝ := fun u ↦ g origin + sinePhase (ofHalfLine (ι₅ u) : ℝ × ℝ)
  have hφ₅_cont : Continuous φ₅ := by unfold φ₅ sinePhase; fun_prop
  have hcomp₅ :
      ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ (ψ ∘ ι₅) = ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ φ₅ := by
    ext u
    dsimp [ψ, φ₅]
    have hu5 : 5 ≤ (ι₅ u : ℝ) := mem_Ici.mp u.2
    rw [hco, zero_add, hg,
      collapse_eq_of_mem_warsawCircleSineCurve (mem_warsawCircleSineCurve_iff.mpr
        (Or.inr (coe_ofHalfLine_mem_warsawCircleSineGraph_of_five_le hu5)))]
    rfl
  have h5_eq : (ψ ∘ ι₅) ⟨5, le_rfl⟩ = φ₅ ⟨5, le_rfl⟩ := by
    dsimp [ψ, φ₅, ι₅]
    rw [ofHalfLine_five, lift_collapse_rightEndpoint_eq g hg, coe_rightEndpoint, sinePhase_one_fst]
  have heq := congrFun (cov.eq_of_comp_eq (ψ.comp ι₅).continuous hφ₅_cont hcomp₅
    ⟨5, le_rfl⟩ h5_eq) ⟨t.1, ht⟩
  simpa [ψ, φ₅, ι₅, sinePhase, add_sub_assoc] using heq

/-- **`WarsawCircle.collapse` admits no continuous lift to `ℝ`** along the universal cover
`ℝ → AddCircle (1 : ℝ)`. -/
theorem not_exists_lift_collapse :
    ¬ ∃ g : C(WarsawCircle, ℝ), ∀ w, (g w : AddCircle (1 : ℝ)) = collapse w := by
  rintro ⟨g, hg⟩
  let u : ℕ → Ici (0 : ℝ) := fun n ↦ ⟨4 + (n + 1 : ℕ) * (2 * Real.pi), mem_Ici.mpr (by positivity)⟩
  have hu5 (n : ℕ) : 5 ≤ (u n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    dsimp [u]; nlinarith [Real.two_le_pi]
  have hu_coe (n : ℕ) : (ofHalfLine (u n) : ℝ × ℝ) = (((n + 1 : ℕ) * (2 * Real.pi))⁻¹, 0) := by
    rw [coe_ofHalfLine_of_five_le (hu5 n)]
    dsimp [u]
    rw [add_sub_cancel_left]
    have hsin : Real.sin ((n + 1 : ℕ) * (2 * Real.pi)) = 0 := by
      simpa using Real.sin_add_nat_mul_two_pi 0 (n + 1)
    rw [hsin]
  have hinv_zero : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) * (2 * Real.pi))⁻¹ : ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const (by positivity))
  have hlim_w : Tendsto (fun n ↦ ofHalfLine (u n)) atTop (𝓝 origin) := by
    rw [tendsto_subtype_rng, coe_origin]
    exact (hinv_zero.prodMk_nhds tendsto_const_nhds).congr fun n ↦ (hu_coe n).symm
  have hlim₁ : Tendsto (fun n ↦ g (ofHalfLine (u n))) atTop (𝓝 (g origin)) :=
    (g.continuous.tendsto origin).comp hlim_w
  have hlim₂ : Tendsto (fun n ↦ g (ofHalfLine (u n))) atTop (𝓝 (g origin + 1)) := by
    have hbase :
        Tendsto (fun n : ℕ ↦ g origin + 1 - (((n + 1 : ℕ) * (2 * Real.pi))⁻¹ : ℝ) / 2)
          atTop (𝓝 (g origin + 1 - 0 / 2)) :=
      tendsto_const_nhds.sub (hinv_zero.div_const 2)
    rw [zero_div, sub_zero] at hbase
    refine hbase.congr fun n ↦ ?_
    rw [lift_collapse_ofHalfLine_eq_of_five_le g hg (hu5 n), hu_coe n]
  linarith [tendsto_nhds_unique hlim₁ hlim₂]

/-- **`WarsawCircle.collapse` is not nullhomotopic.** -/
theorem not_nullhomotopic_collapse : ¬ collapse.Nullhomotopic := by
  rintro ⟨z₀, ⟨H⟩⟩
  obtain ⟨r₀, hr₀⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) z₀
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let F := H.symm
  have hF0 (w : WarsawCircle) : F (0, w) = ((ContinuousMap.const WarsawCircle r₀ w : ℝ) :
      AddCircle (1 : ℝ)) := by
    simpa [F] using hr₀.symm
  let G := cov.liftHomotopy F.toContinuousMap (ContinuousMap.const WarsawCircle r₀) hF0
  refine not_exists_lift_collapse ⟨G.curry 1, fun w ↦ ?_⟩
  have hlifts := congrFun (cov.liftHomotopy_lifts F.toContinuousMap
    (ContinuousMap.const WarsawCircle r₀) hF0) (1, w)
  simpa [G, F] using hlifts

/-- **The Warsaw circle is not contractible**, despite having trivial homotopy groups in all
dimensions. -/
theorem not_contractibleSpace : ¬ ContractibleSpace WarsawCircle := fun _ ↦
  not_nullhomotopic_collapse ((id_nullhomotopic WarsawCircle).comp_right collapse)

/-- **The Warsaw circle is not homotopy equivalent to any contractible space.** -/
theorem isEmpty_homotopyEquiv_of_contractibleSpace {X : Type*} [TopologicalSpace X]
    [ContractibleSpace X] : IsEmpty (WarsawCircle ≃ₕ X) :=
  ⟨fun e ↦ not_contractibleSpace e.contractibleSpace⟩

/-- Symmetric form of `WarsawCircle.isEmpty_homotopyEquiv_of_contractibleSpace`. -/
theorem isEmpty_homotopyEquiv_of_contractibleSpace' {X : Type*} [TopologicalSpace X]
    [ContractibleSpace X] : IsEmpty (X ≃ₕ WarsawCircle) :=
  ⟨fun e ↦ not_contractibleSpace e.symm.contractibleSpace⟩

/-- **The Warsaw circle does not have CW type**: a weakly contractible space of CW type is
contractible by Whitehead's theorem (`TauCeti.contractibleSpace_of_subsingleton_homotopyGroup`),
whereas `WarsawCircle` is not contractible. -/
theorem not_cwType : ¬ CWType WarsawCircle := fun _ ↦
  not_contractibleSpace
    (contractibleSpace_of_subsingleton_homotopyGroup basepoint fun _ ↦ inferInstance)

end TauCeti.WarsawCircle
