/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.TopBranchedCover

/-!
# The branch points of a filled cover

Let `p : E → ℂ ∖ {0, 1}` be a covering map whose fibre over `1/2` is numbered by
`ν : p ⁻¹' {1/2} ≃ Fin n`, with monodromy triple `(σ0, σ1, σinf)`, and let
`TauCeti.FilledCover.fillMap p : FilledCover p → OnePoint ℂ` be its extension to the filled cover.
This file reads the ramification of `fillMap p` off the monodromy, point by point.

* **The fibres over the punctures are the cycles.** The fibre of `fillMap p` over `0` is in
  bijection with the cycles of `σ0` (`TauCeti.FilledCover.fiberZeroEquivSameCycleQuotient`), and
  likewise over `1` and `∞` with the cycles of `σ1` and `σinf`.
* **The local degree is the cycle length.** At the point over `0` of the cycle of a sheet `i`, the
  map `fillMap p` is `w ↦ w ^ e` in charts, where `e` is the length of the cycle of `i` under `σ0`
  (`TauCeti.FilledCover.isLocalPowerAt_fillMap_fiberZeroEquivSameCycleQuotient_symm_mk`).
* **The branch points are the nontrivial cycles.** Call `y` a branch point of `fillMap p` when
  `fillMap p` is injective on no neighbourhood of `y`. Off the three fibres over the punctures
  `fillMap p` is a covering map, so it has no branch points there; the added point of a component
  is a branch point exactly when its local degree is not `1`
  (`TauCeti.FilledCover.setOf_forall_not_injOn_fillMap`). In terms of the monodromy, the point
  over `0` of the cycle of `i` is a branch point exactly when `σ0` moves `i`
  (`TauCeti.FilledCover.exists_injOn_fillMap_fiberZeroEquivSameCycleQuotient_symm_mk_iff`), and
  likewise over `1` and `∞`.

So a puncture over which every cycle is trivial, such as `0` for the map `4 z (1 - z)` whose
`σ0` is the identity, carries no branch point, although it is one of the three marked values.

## Main definitions

* `TauCeti.FilledCover.fiberZeroEquivSameCycleQuotient`,
  `TauCeti.FilledCover.fiberOneEquivSameCycleQuotient`,
  `TauCeti.FilledCover.fiberInfEquivSameCycleQuotient`: the fibres over `0`, `1` and `∞` as the
  sets of cycles of `σ0`, `σ1` and `σinf`.

## Main results

* `TauCeti.FilledCover.isLocalPowerAt_fillMap_fiberZeroEquivSameCycleQuotient_symm_mk` and its
  companions over `1` and `∞`: the local degree at a point of a marked fibre is the length of its
  cycle.
* `TauCeti.FilledCover.exists_injOn_fillMap_incl`: `fillMap p` is locally injective at every point
  of the original cover.
* `TauCeti.FilledCover.exists_injOn_fillMap_center_iff`: it is locally injective at an added point
  exactly when the local degree there is `1`.
* `TauCeti.FilledCover.setOf_forall_not_injOn_fillMap`: the branch points of `fillMap p` are the
  added points of local degree `≠ 1`.
* `TauCeti.FilledCover.exists_injOn_fillMap_fiberZeroEquivSameCycleQuotient_symm_mk_iff` and its
  companions over `1` and `∞`: the point of a cycle is a branch point exactly when the cycle is
  nontrivial.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §4 (branch points as the points near which a map is not injective).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 and §4.2 (the points over a branch value are the cycles of the monodromy, with the cycle
  lengths as ramification indices).
-/

public noncomputable section

namespace TauCeti

open Function Set Topology Equiv.Perm ThricePuncturedSphere PunctureFilling FilledPoint
open scoped OnePoint

namespace FilledCover

variable {E : Type*} [TopologicalSpace E] (p : E → ThricePuncturedSphere)

/-- The fibre of the extended projection over `0` consists of the points added over `0`, one
for each connected component of `p ⁻¹' D₀*`. -/
private theorem fillMap_preimage_zero :
    fillMap p ⁻¹' {((0 : ℂ) : OnePoint ℂ)} = range fun c ↦ center (chart p) (overZero p c) := by
  rw [← Puncture.toOnePoint_zero, fillMap_preimage_puncture]
  -- The components over `zero.neighborhood` are those over `puncturedNeighborhoodZero` by
  -- definition, so `sigmaEquiv_symm_zero` applies to them.
  exact congrArg range (funext fun c ↦ congrArg (center (chart p)) (sigmaEquiv_symm_zero p c))

/-- The fibre of the extended projection over `1` consists of the points added over `1`, one
for each connected component of `p ⁻¹' D₁*`. -/
private theorem fillMap_preimage_one :
    fillMap p ⁻¹' {((1 : ℂ) : OnePoint ℂ)} = range fun c ↦ center (chart p) (overOne p c) := by
  rw [← Puncture.toOnePoint_one, fillMap_preimage_puncture]
  -- The components over `one.neighborhood` are those over `puncturedNeighborhoodOne` by
  -- definition, so `sigmaEquiv_symm_one` applies to them.
  exact congrArg range (funext fun c ↦ congrArg (center (chart p)) (sigmaEquiv_symm_one p c))

/-- The fibre of the extended projection over `∞` consists of the points added over `∞`, one
for each connected component of `p ⁻¹' D∞*`. -/
private theorem fillMap_preimage_inf :
    fillMap p ⁻¹' {(∞ : OnePoint ℂ)} = range fun c ↦ center (chart p) (overInf p c) := by
  rw [← Puncture.toOnePoint_inf, fillMap_preimage_puncture]
  -- The components over `inf.neighborhood` are those over `puncturedNeighborhoodInf` by
  -- definition, so `sigmaEquiv_symm_inf` applies to them.
  exact congrArg range (funext fun c ↦ congrArg (center (chart p)) (sigmaEquiv_symm_inf p c))

variable {p} (hp : IsCoveringMap p) {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n)

/-! ### The fibres over the punctures are the cycles of the monodromy -/

/-- **The fibre over `0` is the set of cycles of `σ0`.** The point over `0` of the cycle of a
sheet `i` is the point added for the component of `p ⁻¹' D₀*` containing the end of the lift of
`αZero` from the sheet numbered `i`
(`IsCoveringMap.sameCycleQuotientσ0EquivConnectedComponents`). -/
def fiberZeroEquivSameCycleQuotient :
    fillMap p ⁻¹' {((0 : ℂ) : OnePoint ℂ)} ≃
      Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ0) :=
  ((Equiv.ofInjective
    (fun c ↦ center (chart p) (overZero p (hp.sameCycleQuotientσ0EquivConnectedComponents ν c)))
    (center_injective.comp ((overZero_injective p).comp (Equiv.injective _)))).trans
      (Set.equivOfEq ((Equiv.surjective _).range_comp _ |>.trans
        (fillMap_preimage_zero p).symm))).symm

/-- **The fibre over `1` is the set of cycles of `σ1`.** The point over `1` of the cycle of a
sheet `i` is the point added for the component of `p ⁻¹' D₁*` containing the end of the lift of
`αOne` from the sheet numbered `i`
(`IsCoveringMap.sameCycleQuotientσ1EquivConnectedComponents`). -/
def fiberOneEquivSameCycleQuotient :
    fillMap p ⁻¹' {((1 : ℂ) : OnePoint ℂ)} ≃
      Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ1) :=
  ((Equiv.ofInjective
    (fun c ↦
      center (chart p) (overOne p (hp.sameCycleQuotientσ1EquivConnectedComponents ν c)))
    (center_injective.comp ((overOne_injective p).comp (Equiv.injective _)))).trans
      (Set.equivOfEq ((Equiv.surjective _).range_comp _ |>.trans
        (fillMap_preimage_one p).symm))).symm

/-- **The fibre over `∞` is the set of cycles of `σinf`.** The point over `∞` of the cycle of a
sheet `i` is the point added for the component of `p ⁻¹' D∞*` containing the end of the lift of
`αPlus` from the sheet numbered `i`
(`IsCoveringMap.sameCycleQuotientσinfEquivConnectedComponents`). -/
def fiberInfEquivSameCycleQuotient :
    fillMap p ⁻¹' {(∞ : OnePoint ℂ)} ≃
      Quotient (SameCycle.setoid (hp.monodromyTriple ν).σinf) :=
  ((Equiv.ofInjective
    (fun c ↦
      center (chart p) (overInf p (hp.sameCycleQuotientσinfEquivConnectedComponents ν c)))
    (center_injective.comp ((overInf_injective p).comp (Equiv.injective _)))).trans
      (Set.equivOfEq ((Equiv.surjective _).range_comp _ |>.trans
        (fillMap_preimage_inf p).symm))).symm

/-- The point over `0` of a cycle `c` of `σ0` is the point added for the component of
`p ⁻¹' D₀*` corresponding to `c`. -/
@[simp]
theorem coe_fiberZeroEquivSameCycleQuotient_symm_apply
    (c : Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ0)) :
    ((fiberZeroEquivSameCycleQuotient hp ν).symm c : FilledCover p) =
      center (chart p) (overZero p (hp.sameCycleQuotientσ0EquivConnectedComponents ν c)) :=
  (rfl)

/-- The point over `1` of a cycle `c` of `σ1` is the point added for the component of
`p ⁻¹' D₁*` corresponding to `c`. -/
@[simp]
theorem coe_fiberOneEquivSameCycleQuotient_symm_apply
    (c : Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ1)) :
    ((fiberOneEquivSameCycleQuotient hp ν).symm c : FilledCover p) =
      center (chart p) (overOne p (hp.sameCycleQuotientσ1EquivConnectedComponents ν c)) :=
  (rfl)

/-- The point over `∞` of a cycle `c` of `σinf` is the point added for the component of
`p ⁻¹' D∞*` corresponding to `c`. -/
@[simp]
theorem coe_fiberInfEquivSameCycleQuotient_symm_apply
    (c : Quotient (SameCycle.setoid (hp.monodromyTriple ν).σinf)) :
    ((fiberInfEquivSameCycleQuotient hp ν).symm c : FilledCover p) =
      center (chart p) (overInf p (hp.sameCycleQuotientσinfEquivConnectedComponents ν c)) :=
  (rfl)

/-! ### The local degree at a point over a puncture is the length of its cycle -/

/-- **The local degree over `0` is the cycle length.** At the point over `0` of the cycle of the
sheet `i`, the extended projection is `w ↦ w ^ e` in charts, where `e` is the length of the cycle
of `i` under `σ0`. -/
theorem isLocalPowerAt_fillMap_fiberZeroEquivSameCycleQuotient_symm_mk (i : Fin n) :
    IsLocalPowerAt (fillMap p) ((fiberZeroEquivSameCycleQuotient hp ν).symm (Quotient.mk _ i))
      (minimalPeriod (hp.monodromyTriple ν).σ0 i) := by
  rw [coe_fiberZeroEquivSameCycleQuotient_symm_apply,
    hp.sameCycleQuotientσ0EquivConnectedComponents_mk,
    ← degree_overZero_mk_monodromy hp ν i]
  exact isLocalPowerAt_fillMap_center hp (.of_equiv _ ν.symm) _

/-- **The local degree over `1` is the cycle length.** At the point over `1` of the cycle of the
sheet `i`, the extended projection is `w ↦ w ^ e` in charts, where `e` is the length of the cycle
of `i` under `σ1`. -/
theorem isLocalPowerAt_fillMap_fiberOneEquivSameCycleQuotient_symm_mk (i : Fin n) :
    IsLocalPowerAt (fillMap p) ((fiberOneEquivSameCycleQuotient hp ν).symm (Quotient.mk _ i))
      (minimalPeriod (hp.monodromyTriple ν).σ1 i) := by
  rw [coe_fiberOneEquivSameCycleQuotient_symm_apply,
    hp.sameCycleQuotientσ1EquivConnectedComponents_mk,
    ← degree_overOne_mk_monodromy hp ν i]
  exact isLocalPowerAt_fillMap_center hp (.of_equiv _ ν.symm) _

/-- **The local degree over `∞` is the cycle length.** At the point over `∞` of the cycle of the
sheet `i`, the extended projection is `w ↦ w ^ e` in charts, where `e` is the length of the cycle
of `i` under `σinf`. -/
theorem isLocalPowerAt_fillMap_fiberInfEquivSameCycleQuotient_symm_mk (i : Fin n) :
    IsLocalPowerAt (fillMap p) ((fiberInfEquivSameCycleQuotient hp ν).symm (Quotient.mk _ i))
      (minimalPeriod (hp.monodromyTriple ν).σinf i) := by
  rw [coe_fiberInfEquivSameCycleQuotient_symm_apply,
    hp.sameCycleQuotientσinfEquivConnectedComponents_mk,
    ← degree_overInf_mk_monodromy hp ν i]
  exact isLocalPowerAt_fillMap_center hp (.of_equiv _ ν.symm) _

/-! ### The branch points -/

section BranchLocus

variable {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- **The original cover is unbranched.** At a point of the original cover, the extended
projection is injective on a neighbourhood, since it is a covering map off the three punctures. -/
theorem exists_injOn_fillMap_incl (x : E) :
    ∃ U ∈ 𝓝 (incl (chart p) x), InjOn (fillMap p) U := by
  have hx : fillMap p (incl (chart p) x) ∈ markedᶜ := by
    rw [fillMap_incl, ← range_toOnePoint]
    exact mem_range_self _
  exact ((isCoveringMapOn_fillMap hp hfin).isLocalHomeomorphOn.isLocalPowerAt_one hx
    (mem_chart_source ℂ _)).eq_one_iff_exists_injOn.1 rfl

/-- At an added point, the extended projection is injective on a neighbourhood exactly when the
local degree there is `1`. -/
theorem exists_injOn_fillMap_center_iff (i : FilledPoint p) :
    (∃ U ∈ 𝓝 (center (chart p) i), InjOn (fillMap p) U) ↔ degree p i = 1 :=
  (isLocalPowerAt_fillMap_center hp hfin i).eq_one_iff_exists_injOn.symm

/-- **The branch locus of a filled cover.** The points of the filled cover near which the
extended projection is injective on no neighbourhood are exactly the added points of local degree
other than `1`. In particular every branch point lies over one of the three punctures. -/
theorem setOf_forall_not_injOn_fillMap :
    {y | ∀ U ∈ 𝓝 y, ¬InjOn (fillMap p) U} = center (chart p) '' {i | degree p i ≠ 1} := by
  ext y
  induction y using PunctureFilling.induction with
  | incl x =>
    obtain ⟨U, hU, hinj⟩ := exists_injOn_fillMap_incl hp hfin x
    simpa using ⟨U, hU, hinj⟩
  | center i =>
    simpa [center_injective.mem_set_image, not_exists, not_and] using
      (exists_injOn_fillMap_center_iff hp hfin i).not

end BranchLocus

/-- **The branch points over `0` are the nontrivial cycles of `σ0`.** The extended projection is
injective on a neighbourhood of the point over `0` of the cycle of the sheet `i` exactly when
`σ0` fixes `i`. -/
theorem exists_injOn_fillMap_fiberZeroEquivSameCycleQuotient_symm_mk_iff (i : Fin n) :
    (∃ U ∈ 𝓝 ((fiberZeroEquivSameCycleQuotient hp ν).symm (Quotient.mk _ i) : FilledCover p),
      InjOn (fillMap p) U) ↔ (hp.monodromyTriple ν).σ0 i = i :=
  (isLocalPowerAt_fillMap_fiberZeroEquivSameCycleQuotient_symm_mk hp ν i
    |>.eq_one_iff_exists_injOn).symm.trans minimalPeriod_eq_one_iff_isFixedPt

/-- **The branch points over `1` are the nontrivial cycles of `σ1`.** The extended projection is
injective on a neighbourhood of the point over `1` of the cycle of the sheet `i` exactly when
`σ1` fixes `i`. -/
theorem exists_injOn_fillMap_fiberOneEquivSameCycleQuotient_symm_mk_iff (i : Fin n) :
    (∃ U ∈ 𝓝 ((fiberOneEquivSameCycleQuotient hp ν).symm (Quotient.mk _ i) : FilledCover p),
      InjOn (fillMap p) U) ↔ (hp.monodromyTriple ν).σ1 i = i :=
  (isLocalPowerAt_fillMap_fiberOneEquivSameCycleQuotient_symm_mk hp ν i
    |>.eq_one_iff_exists_injOn).symm.trans minimalPeriod_eq_one_iff_isFixedPt

/-- **The branch points over `∞` are the nontrivial cycles of `σinf`.** The extended projection is
injective on a neighbourhood of the point over `∞` of the cycle of the sheet `i` exactly when
`σinf` fixes `i`. -/
theorem exists_injOn_fillMap_fiberInfEquivSameCycleQuotient_symm_mk_iff (i : Fin n) :
    (∃ U ∈ 𝓝 ((fiberInfEquivSameCycleQuotient hp ν).symm (Quotient.mk _ i) : FilledCover p),
      InjOn (fillMap p) U) ↔ (hp.monodromyTriple ν).σinf i = i :=
  (isLocalPowerAt_fillMap_fiberInfEquivSameCycleQuotient_symm_mk hp ν i
    |>.eq_one_iff_exists_injOn).symm.trans minimalPeriod_eq_one_iff_isFixedPt

end FilledCover

end TauCeti
