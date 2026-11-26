/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.OrientedLine
public import TauCeti.Dynamics.Billiard.ConvexTable.Exit
public import TauCeti.Dynamics.Billiard.OrientedLine
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.LocalAtTarget
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Oriented lines and the phase cylinder of a convex table

An oriented line of the plane `ℂ` is represented by a pair `(e, c) ∈ Circle × ℝ`: the line
`{z | e × z = c}` (`TauCeti.orientedLineSet`), oriented by its direction `e`, where
`a × b = Im (conj a * b)`; reversing the orientation, `(e, c) ↦ (−e, −c)`, keeps the point set
(`TauCeti.orientedLineSet_neg`), so it preserves the lines meeting any set
(`TauCeti.neg_mem_setOf_orientedLineSet_inter_nonempty_iff`).

For a convex table `γ` with unit tangent `τ`, the oriented line of the state `(s, δ)` is
`Λ(s, δ) = (exp(iδ) τ(s), exp(iδ) τ(s) × γ(s))` (`TauCeti.ConvexTable.orientedLine`), the line
along which the ball leaves `γ(s)` at the angle `δ`. It contains the exit point `γ(s₁)`
(`TauCeti.ConvexTable.exitParam`, `TauCeti.ConvexTable.apply_exitParam_mem_orientedLineSet`).
The main result is that `Λ` is a homeomorphism from the phase cylinder `AddCircle ℓ × (0, π)`
onto the set of oriented lines meeting the interior of the region `Ω` bounded by `γ`
(`TauCeti.ConvexTable.orientedLineHomeomorph`), which is open
(`TauCeti.ConvexTable.isOpen_setOf_orientedLineSet_inter_interior_nonempty`), with inverse the
entry state (`TauCeti.ConvexTable.orientedLineHomeomorph_symm_apply_mk`):

* for `δ ∈ (0, π)` the line meets the interior of `Ω`, and the tangent lines (`sin δ = 0`) do not
  (`TauCeti.ConvexTable.orientedLineSet_orientedLine_inter_interior_nonempty`,
  `TauCeti.ConvexTable.orientedLineSet_orientedLine_inter_interior_eq_empty`);
* `Λ` is injective on the phase cylinder
  (`TauCeti.ConvexTable.orientedLine_eq_orientedLine_iff`), by the injectivity of the oriented
  lines of `TauCeti.StrictConvexBilliardTable`, which agree with `Λ`
  (`TauCeti.ConvexTable.toStrictConvexBilliardTable_orientedLine_cos`);
* every line meeting the interior of `Ω` is `Λ` of its entry state
  (`TauCeti.ConvexTable.exists_orientedLine_eq`): the point where the line enters `Ω` is the last
  point of `Ω` before an interior point, in the reverse direction, and lies on the curve;
* the inverse is continuous because `Λ` extends continuously to the compact closed cylinder
  `AddCircle ℓ × [0, π]`, so it is a closed map there, and the phase cylinder is exactly the
  preimage of the lines meeting the interior of `Ω`.

## References

* M. Bialy and A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric billiard
  tables*, Ann. of Math. 196 (2022), Section 2.
-/

public section

noncomputable section

open Function Set Filter Topology Complex
open scoped ComplexConjugate

namespace TauCeti

/-! ### The oriented lines of a convex table -/

namespace ConvexTable

attribute [local instance] Complex.finrank_real_complex_fact

variable {k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (T : ConvexTable k ℓ)

/-- The **oriented line** `Λ(s, δ) = (exp(iδ) τ(s), exp(iδ) τ(s) × γ(s))` of the state `(s, δ)`:
the line through `γ(s)` with direction `exp(iδ) τ(s)`. -/
def orientedLine (s δ : ℝ) : Circle × ℝ :=
  orientedLineThrough (Circle.exp δ * T.tangent s) (T s)

theorem orientedLine_def (s δ : ℝ) :
    T.orientedLine s δ = orientedLineThrough (Circle.exp δ * T.tangent s) (T s) :=
  (rfl)

@[simp]
theorem coe_orientedLine_fst (s δ : ℝ) :
    ((T.orientedLine s δ).1 : ℂ) = exp (δ * I) * deriv T s := by
  simp [orientedLine_def, orientedLineThrough_def, Circle.coe_exp]

theorem orientedLine_snd (s δ : ℝ) :
    (T.orientedLine s δ).2 = (conj (exp (δ * I) * deriv T s) * T s).im := by
  simp [orientedLine_def, orientedLineThrough_def, Circle.coe_exp]

theorem continuous_orientedLine : Continuous fun x : ℝ × ℝ => T.orientedLine x.1 x.2 := by
  have hdir : Continuous fun x : ℝ × ℝ => Circle.exp x.2 * T.tangent x.1 :=
    (Circle.exp.continuous.comp continuous_snd).mul (T.continuous_tangent.comp continuous_fst)
  simp only [orientedLine_def, orientedLineThrough_def]
  refine hdir.prodMk (continuous_im.comp ?_)
  exact (continuous_conj.comp (continuous_subtypeVal.comp hdir)).mul
    (T.continuous.comp continuous_fst)

theorem periodic_orientedLine (δ : ℝ) : Periodic (fun s => T.orientedLine s δ) ℓ := fun s => by
  simp only [orientedLine_def, T.periodic_tangent s, T.periodic s]

/-- The table point `γ(s)` lies on the line `Λ(s, δ)`. -/
theorem apply_mem_orientedLineSet (s δ : ℝ) : T s ∈ orientedLineSet (T.orientedLine s δ) :=
  mem_orientedLineSet_orientedLineThrough _ _

/-- The points `γ(s) + r exp(iδ) τ(s)` lie on the line `Λ(s, δ)`. -/
theorem add_smul_mem_orientedLineSet (s δ r : ℝ) :
    T s + r • (exp (δ * I) * deriv T s) ∈ orientedLineSet (T.orientedLine s δ) := by
  rw [← coe_orientedLine_fst, mem_orientedLineSet, Circle.im_conj_mul_add_smul]
  exact mem_orientedLineSet.1 (T.apply_mem_orientedLineSet s δ)

/-- **The line leaves at the exit point.** For `0 < δ < π`, the exit point `γ(s₁)`
(`TauCeti.ConvexTable.exitParam`) lies on the line `Λ(s, δ)`. -/
theorem apply_exitParam_mem_orientedLineSet {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    T (T.exitParam s δ) ∈ orientedLineSet (T.orientedLine s δ) := by
  rw [eq_add_of_sub_eq' (T.apply_exitParam_sub_eq_norm_smul hδ)]
  exact T.add_smul_mem_orientedLineSet s δ _

/-- For `0 < δ < π`, the line `Λ(s, δ)` meets the interior of the region `Ω`. -/
theorem orientedLineSet_orientedLine_inter_interior_nonempty {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    (orientedLineSet (T.orientedLine s δ) ∩ interior T.region).Nonempty := by
  obtain ⟨r, hr⟩ := (T.eventually_add_smul_mem_interior_region (s := s) hδ).exists
  exact ⟨_, T.add_smul_mem_orientedLineSet s δ r, hr⟩

/-- **Tangent lines miss the interior.** If `sin δ = 0`, the line `Λ(s, δ)` is the tangent line at
`γ(s)` and does not meet the interior of `Ω`. -/
theorem orientedLineSet_orientedLine_inter_interior_eq_empty {s δ : ℝ} (hδ : Real.sin δ = 0) :
    orientedLineSet (T.orientedLine s δ) ∩ interior T.region = ∅ := by
  refine eq_empty_of_forall_notMem fun z ⟨hz, hint⟩ => ?_
  have hpos := (T.mem_interior_region_iff.1 hint) s
  -- For `sin δ = 0` the direction `exp(iδ) τ(s)` is `±τ(s)`.
  have hexp : Circle.exp δ = 1 ∨ Circle.exp δ = -1 :=
    (Circle.im_coe_eq_zero_iff _).1 (by rw [Circle.coe_exp, exp_ofReal_mul_I_im, hδ])
  rw [orientedLine_def, mem_orientedLineSet, orientedLineThrough_def, ← sub_eq_zero, ← sub_im,
    ← mul_sub] at hz
  rcases hexp with h | h <;>
    simp only [h, one_mul, neg_mul, Circle.coe_neg, map_neg, neg_im, neg_eq_zero,
      coe_tangent] at hz <;>
    exact hpos.ne' hz

/-- **The two oriented-line APIs agree.** For `δ ∈ [0, π]`, the oriented line of the state
`(s, cos δ)` of the strict convex billiard table underlying `T` is `Λ(s, δ)`, with its direction
viewed in `ℂ`. -/
theorem toStrictConvexBilliardTable_orientedLine_cos {s δ : ℝ} (hδ : δ ∈ Icc 0 Real.pi) :
    T.toStrictConvexBilliardTable.orientedLine s (Real.cos δ) =
      (((T.orientedLine s δ).1 : ℂ), (T.orientedLine s δ).2) := by
  rw [StrictConvexBilliardTable.orientedLine_def,
    T.toStrictConvexBilliardTable_outgoingDir_cos hδ, Complex.areaForm,
    coe_toStrictConvexBilliardTable]
  exact Prod.ext (T.coe_orientedLine_fst s δ).symm (T.orientedLine_snd s δ).symm

/-- **Injectivity on the phase cylinder.** For `δ ∈ (0, π)` and `δ' ∈ [0, π]`, the states `(s, δ)`
and `(s', δ')` have the same oriented line exactly when `s ≡ s'` modulo `ℓ` and `δ = δ'`. -/
theorem orientedLine_eq_orientedLine_iff {s s' δ δ' : ℝ} (hδ : δ ∈ Ioo 0 Real.pi)
    (hδ' : δ' ∈ Icc 0 Real.pi) :
    T.orientedLine s δ = T.orientedLine s' δ' ↔ (s : AddCircle ℓ) = s' ∧ δ = δ' := by
  have hinj : Injective fun p : Circle × ℝ => ((p.1 : ℂ), p.2) := fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Circle.ext h.1) h.2
  rw [← hinj.eq_iff, ← T.toStrictConvexBilliardTable_orientedLine_cos (Ioo_subset_Icc_self hδ),
    ← T.toStrictConvexBilliardTable_orientedLine_cos hδ',
    StrictConvexBilliardTable.orientedLine_eq_orientedLine_iff _ (Real.mapsTo_cos_Ioo hδ),
    coe_toStrictConvexBilliardTable, T.apply_eq_apply_iff,
    Real.injOn_cos.eq_iff (Ioo_subset_Icc_self hδ) hδ']

/-- The ray from an interior point `z₀` of `Ω` in the direction `−e` meets the curve: the last
point of `Ω` on it is not interior, so it is a point `γ(s)`. -/
private theorem exists_apply_eq_sub_smul {z₀ : ℂ} (hint : z₀ ∈ interior T.region) (e : Circle) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ s, T s = z₀ - r • (e : ℂ) := by
  -- The parameters `r ≥ 0` with `z₀ − r e ∈ Ω` form a compact set; take the largest.
  set S : Set ℝ := {r | 0 ≤ r ∧ z₀ - r • (e : ℂ) ∈ T.region}
  obtain ⟨M, hM⟩ := T.isCompact_region.isBounded.subset_closedBall 0
  have hSb : S ⊆ Icc 0 (‖z₀‖ + M) := fun r ⟨hr, hrΩ⟩ => by
    refine ⟨hr, ?_⟩
    have h1 : ‖z₀ - r • (e : ℂ)‖ ≤ M := by simpa using hM hrΩ
    have h2 : r = ‖z₀ - (z₀ - r • (e : ℂ))‖ := by simp [abs_of_nonneg hr]
    rw [h2]
    exact (norm_sub_le _ _).trans (by linarith)
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ((Metric.isBounded_Icc _ _).subset hSb)
    exact isClosed_Ici.inter (T.isClosed_region.preimage (by fun_prop))
  have hS0 : (0 : ℝ) ∈ S := ⟨le_rfl, by simpa using interior_subset hint⟩
  set r₀ := sSup S
  have hr₀ : r₀ ∈ S := hSc.sSup_mem ⟨0, hS0⟩
  set w := z₀ - r₀ • (e : ℂ)
  -- The last point `w` of `Ω` is not interior, so it lies on the curve.
  have hw : w ∉ interior T.region := by
    intro hw
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
    have hmem : r₀ + ε / 2 ∈ S := by
      refine ⟨by linarith [hr₀.1], interior_subset (hball ?_)⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have : z₀ - (r₀ + ε / 2) • (e : ℂ) - w = -((ε / 2) • (e : ℂ)) := by simp only [w]; module
      rw [this, norm_neg, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by positivity)]
      linarith
    have := le_csSup hSc.bddAbove hmem
    linarith
  obtain ⟨s, hs⟩ : w ∈ range T := by
    by_contra h
    exact hw (by rw [T.interior_region]; exact ⟨hr₀.2, h⟩)
  exact ⟨r₀, hr₀.1, s, hs⟩

/-- **Surjectivity onto the lines meeting the interior.** Every oriented line meeting the interior
of `Ω` is `Λ(s, δ)` for some `s` and `δ ∈ (0, π)`: its entry state. -/
theorem exists_orientedLine_eq {p : Circle × ℝ}
    (hp : (orientedLineSet p ∩ interior T.region).Nonempty) :
    ∃ s, ∃ δ ∈ Ioo 0 Real.pi, T.orientedLine s δ = p := by
  obtain ⟨z₀, hz₀, hint⟩ := hp
  set e : ℂ := (p.1 : ℂ)
  -- The entry point `w = γ(s)` is the last point of `Ω` before `z₀`, in the reverse direction.
  obtain ⟨r₀, hr₀, s, hs⟩ := T.exists_apply_eq_sub_smul hint p.1
  set w := z₀ - r₀ • e
  -- The direction points to the left of `τ(s)`, so it is `exp(iδ) τ(s)` with `δ ∈ (0, π)`.
  have hleft : 0 < (conj (deriv T s) * e).im := by
    have h := (T.mem_interior_region_iff.1 hint) s
    have hz : z₀ - T s = r₀ • e := by rw [hs]; simp only [w]; abel
    rw [hz, real_smul, mul_left_comm, im_ofReal_mul] at h
    exact pos_of_mul_pos_right h hr₀
  set u : Circle := (T.tangent s)⁻¹ * p.1
  have hu : (u : ℂ) = conj (deriv T s) * e := by
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj, coe_tangent]
  have harg : arg (u : ℂ) ∈ Ioo 0 Real.pi := by
    rw [hu]
    refine ⟨lt_of_le_of_ne (arg_nonneg_iff.2 hleft.le) fun h => ?_,
      arg_lt_pi_iff.2 (Or.inr hleft.ne')⟩
    exact hleft.ne' (arg_eq_zero_iff.1 h.symm).2
  refine ⟨s, arg (u : ℂ), harg, ?_⟩
  have hdir : Circle.exp (arg (u : ℂ)) * T.tangent s = p.1 := by
    rw [Circle.exp_arg, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hw' : w = z₀ + (-r₀) • e := by simp only [w]; module
  rw [orientedLine_def, hdir, orientedLineThrough_def, hs, hw', Circle.im_conj_mul_add_smul,
    mem_orientedLineSet.1 hz₀]

/-- The oriented lines meeting the interior of `Ω` form an open set. -/
theorem isOpen_setOf_orientedLineSet_inter_interior_nonempty :
    IsOpen {p : Circle × ℝ | (orientedLineSet p ∩ interior T.region).Nonempty} :=
  isOpen_setOf_orientedLineSet_inter_nonempty isOpen_interior

/-- `Λ` on `AddCircle ℓ × ℝ`. -/
def addCircleOrientedLine (x : AddCircle ℓ × ℝ) : Circle × ℝ :=
  (T.periodic_orientedLine x.2).lift x.1

@[simp]
theorem addCircleOrientedLine_mk (s δ : ℝ) :
    T.addCircleOrientedLine ((s : AddCircle ℓ), δ) = T.orientedLine s δ :=
  (T.periodic_orientedLine δ).lift_coe s

theorem continuous_addCircleOrientedLine : Continuous T.addCircleOrientedLine :=
  ((QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap
    (X := ℝ × ℝ)).continuous_iff.2 T.continuous_orientedLine

/-- `Λ` on the compact closed cylinder `AddCircle ℓ × [0, π]`. -/
private def closedLine (x : AddCircle ℓ × Icc 0 Real.pi) : Circle × ℝ :=
  T.addCircleOrientedLine (x.1, x.2)

private theorem continuous_closedLine : Continuous T.closedLine :=
  T.continuous_addCircleOrientedLine.comp (continuous_fst.prodMk
    (continuous_subtypeVal.comp continuous_snd))

/-- The set of oriented lines meeting the interior of `Ω`. -/
private abbrev interiorLines : Set (Circle × ℝ) :=
  {p | (orientedLineSet p ∩ interior T.region).Nonempty}

private theorem mem_preimage_closedLine_iff (x : AddCircle ℓ × Icc 0 Real.pi) :
    x ∈ T.closedLine ⁻¹' T.interiorLines ↔ (x.2 : ℝ) ∈ Ioo 0 Real.pi := by
  obtain ⟨a, δ, hδ⟩ := x
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [mem_preimage, closedLine, addCircleOrientedLine_mk]
  refine ⟨fun h => ?_, T.orientedLineSet_orientedLine_inter_interior_nonempty⟩
  by_contra hIoo
  -- The endpoints `δ = 0` and `δ = π` give tangent lines, which miss the interior.
  have hsin : Real.sin δ = 0 := by
    rcases hδ.1.eq_or_lt with rfl | h0
    · exact Real.sin_zero
    · rw [hδ.2.eq_of_not_lt fun hπ => hIoo ⟨h0, hπ⟩, Real.sin_pi]
  exact h.ne_empty (T.orientedLineSet_orientedLine_inter_interior_eq_empty hsin)

/-- The restriction of `Λ` to the phase cylinder, onto the lines meeting the interior. -/
private def restrictedLine :
    T.closedLine ⁻¹' T.interiorLines → T.interiorLines :=
  T.interiorLines.restrictPreimage T.closedLine

private theorem continuous_restrictedLine : Continuous T.restrictedLine :=
  T.continuous_closedLine.restrictPreimage

private theorem isClosedMap_restrictedLine : IsClosedMap T.restrictedLine :=
  T.continuous_closedLine.isClosedMap.restrictPreimage _

private theorem coe_restrictedLine_mk (s δ : ℝ) (hδ : δ ∈ Icc 0 Real.pi)
    (h : ((s : AddCircle ℓ), (⟨δ, hδ⟩ : Icc 0 Real.pi)) ∈ T.closedLine ⁻¹' T.interiorLines) :
    (T.restrictedLine ⟨((s : AddCircle ℓ), ⟨δ, hδ⟩), h⟩ : Circle × ℝ) = T.orientedLine s δ := by
  simp only [restrictedLine, restrictPreimage_mk, closedLine, addCircleOrientedLine_mk]

private theorem bijective_restrictedLine : Bijective T.restrictedLine := by
  constructor
  · rintro ⟨⟨a, ⟨δ, hδ⟩⟩, hx⟩ ⟨⟨a', ⟨δ', hδ'⟩⟩, hx'⟩ h
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨s', rfl⟩ := QuotientAddGroup.mk_surjective a'
    have hIoo := (T.mem_preimage_closedLine_iff _).1 hx
    have h' : T.orientedLine s δ = T.orientedLine s' δ' := by
      rw [← T.coe_restrictedLine_mk s δ hδ hx, ← T.coe_restrictedLine_mk s' δ' hδ' hx', h]
    obtain ⟨hss, hδδ⟩ := (T.orientedLine_eq_orientedLine_iff hIoo hδ').1 h'
    subst hδδ
    exact Subtype.ext (Prod.ext hss rfl)
  · rintro ⟨p, hp⟩
    obtain ⟨s, δ, hδ, rfl⟩ := T.exists_orientedLine_eq hp
    have hx := (T.mem_preimage_closedLine_iff ((s : AddCircle ℓ), ⟨δ, Ioo_subset_Icc_self hδ⟩)).2 hδ
    exact ⟨⟨_, hx⟩, Subtype.ext (T.coe_restrictedLine_mk s δ _ hx)⟩

/-- The phase cylinder as the preimage of the lines meeting the interior. -/
private def phaseCylinderEquiv :
    AddCircle ℓ × Ioo 0 Real.pi ≃ₜ T.closedLine ⁻¹' T.interiorLines where
  toFun x := ⟨(x.1, ⟨x.2, Ioo_subset_Icc_self x.2.property⟩),
    (T.mem_preimage_closedLine_iff _).2 x.2.property⟩
  invFun x := (x.val.1, ⟨x.val.2, (T.mem_preimage_closedLine_iff _).1 x.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem coe_phaseCylinderEquiv_apply (x : AddCircle ℓ × Ioo 0 Real.pi) :
    (T.phaseCylinderEquiv x : AddCircle ℓ × Icc 0 Real.pi) =
      (x.1, ⟨x.2, Ioo_subset_Icc_self x.2.property⟩) :=
  (rfl)

/-- **The phase cylinder is the space of oriented lines meeting the interior.** The map
`Λ(s, δ) = (exp(iδ) τ(s), exp(iδ) τ(s) × γ(s))` is a homeomorphism from `AddCircle ℓ × (0, π)`
onto the set of oriented lines meeting the interior of the region `Ω`. Its inverse sends such a
line to its entry state. -/
def orientedLineHomeomorph :
    AddCircle ℓ × Ioo 0 Real.pi ≃ₜ
      {p : Circle × ℝ // (orientedLineSet p ∩ interior T.region).Nonempty} :=
  T.phaseCylinderEquiv.trans
    ((Equiv.ofBijective _ T.bijective_restrictedLine).toHomeomorphOfContinuousClosed
      T.continuous_restrictedLine T.isClosedMap_restrictedLine)

/-- The homeomorphism is `Λ` on the phase cylinder. -/
@[simp]
theorem coe_orientedLineHomeomorph_apply (x : AddCircle ℓ × Ioo 0 Real.pi) :
    (T.orientedLineHomeomorph x : Circle × ℝ) = T.addCircleOrientedLine (x.1, x.2) := by
  -- Keep the preimage subtype unnormalised, so that the coercions still match.
  simp [orientedLineHomeomorph, restrictedLine, closedLine, coe_phaseCylinderEquiv_apply,
    -preimage_ofPred_eq]

/-- The homeomorphism sends the state `(s, δ)` to the line `Λ(s, δ)`. -/
theorem coe_orientedLineHomeomorph_apply_mk (s : ℝ) (δ : Ioo 0 Real.pi) :
    (T.orientedLineHomeomorph ((s : AddCircle ℓ), δ) : Circle × ℝ) = T.orientedLine s δ := by
  simp

/-- The inverse of `Λ` sends the line `Λ(s, δ)` to its entry state `(s, δ)`. -/
@[simp]
theorem orientedLineHomeomorph_symm_apply_mk (s : ℝ) (δ : Ioo 0 Real.pi)
    (h : (orientedLineSet (T.orientedLine s δ) ∩ interior T.region).Nonempty) :
    T.orientedLineHomeomorph.symm ⟨T.orientedLine s δ, h⟩ = ((s : AddCircle ℓ), δ) :=
  T.orientedLineHomeomorph.symm_apply_eq.2
    (Subtype.ext (T.coe_orientedLineHomeomorph_apply_mk s δ).symm)

end ConvexTable

end TauCeti
