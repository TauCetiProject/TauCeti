/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Inverse
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

/-!
# The billiard map of a `C¹` table is a homeomorphism

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)`. This file proves that when the unit tangent `χ'` is
continuous, `B` is continuous on the strip
(`TauCeti.StrictConvexBilliardTable.continuousOn_nextCollision`). Its inverse is `τ⁻¹ ∘ ι ∘ B ∘ ι`,
with `ι(s, v) = (s, -v)` and `τ(s, v) = (s + L, v)`, so `B` is a homeomorphism of the strip
(`TauCeti.StrictConvexBilliardTable.nextCollisionHomeomorph`), and the billiard map `β` it induces
on the space of collision states `AddCircle L × (-1, 1)` is a homeomorphism
(`TauCeti.StrictConvexBilliardTable.billiardHomeomorph`).

The proof of continuity uses only the transversality of the chord at its far end. For the state
`x = (s, v)` with outgoing velocity `u(x)`, the next collision parameter `t₀` is the unique zero in
`(s, s + L)` of `f_x(t) = ω(u(x), χ(t) - χ(s))`, where `ω` is the area form. Its derivative there
is `ω(u(x), χ'(t₀)) = √(1 - w ^ 2) > 0`, since the chord is not tangent to the boundary at
`χ(t₀)`. So `f_x` changes sign from negative to positive on any small interval `[a, b]` around
`t₀`. Since `f_y(a)` and `f_y(b)` depend continuously on the state `y`, the same sign change holds
for every nearby state, and the intermediate value theorem and the uniqueness of the next collision
put the next collision parameter of `y` in `(a, b)`. No second derivative of `χ` is used.

## Main results

* `TauCeti.StrictConvexBilliardTable.continuous_outgoingDir`: the outgoing velocity depends
  continuously on the state.
* `TauCeti.StrictConvexBilliardTable.continuousAt_nextParam`,
  `TauCeti.StrictConvexBilliardTable.continuousAt_nextTangential`,
  `TauCeti.StrictConvexBilliardTable.continuousOn_nextCollision`: the next-collision map is
  continuous on the strip.
* `TauCeti.StrictConvexBilliardTable.continuous_nextCollisionEquiv`,
  `TauCeti.StrictConvexBilliardTable.continuous_nextCollisionEquiv_symm`,
  `TauCeti.StrictConvexBilliardTable.nextCollisionHomeomorph`: the next-collision map is a
  homeomorphism of the strip.
* `TauCeti.StrictConvexBilliardTable.billiardHomeomorph`: the billiard map is a homeomorphism of
  `AddCircle L × (-1, 1)`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3 (the billiard ball map).
-/

public section

noncomputable section

open Function Set Filter Topology
open scoped RealInnerProductSpace

namespace TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-! ### Continuity of the next-collision map on the strip -/

/-- For a table with continuous unit tangent, the outgoing velocity `u(s, v)` depends continuously
on the state `(s, v)`. -/
theorem continuous_outgoingDir (hχ : Continuous (deriv χ)) :
    Continuous fun x : ℝ × ℝ ↦ χ.outgoingDir x.1 x.2 := by
  simp only [outgoingDir_def]
  exact (continuous_snd.smul (hχ.comp continuous_fst)).add
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_snd.pow 2))).smul
      (o.rightAngleRotation.continuous.comp (hχ.comp continuous_fst)))

/-- The chord of a state `(s, v)` crosses the boundary transversally at its next collision
parameter `t₀`: arbitrarily close to `t₀` there are parameters `a < t₀ < b` in `(s, s + L)` with
`ω(u, χ(a) - χ(s)) < 0 < ω(u, χ(b) - χ(s))`. -/
private theorem exists_areaForm_neg_pos_near_nextParam {s v ε : ℝ} (hv : v ∈ Ioo (-1) 1)
    (hε : 0 < ε) : ∃ a b, s < a ∧ χ.nextParam s v - ε < a ∧ a < χ.nextParam s v ∧
      χ.nextParam s v < b ∧ b < χ.nextParam s v + ε ∧ b < s + χ.period ∧
      o.areaForm (χ.outgoingDir s v) (χ a - χ s) < 0 ∧
      0 < o.areaForm (χ.outgoingDir s v) (χ b - χ s) := by
  set t₀ := χ.nextParam s v
  have ht₀ : t₀ ∈ Ioo s (s + χ.period) := χ.nextParam_mem_Ioo hv
  set f : ℝ → ℝ := fun t ↦ o.areaForm (χ.outgoingDir s v) (χ t - χ s)
  -- At `t₀`, the function `f` crosses zero with positive slope `ω(u, χ'(t₀))`.
  have hderiv : HasDerivAt f (o.areaForm (χ.outgoingDir s v) (deriv χ t₀)) t₀ :=
    (o.areaForm (χ.outgoingDir s v)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t₀
      ((χ.differentiableAt t₀).hasDerivAt.sub_const (χ s))
  have hpos : 0 < o.areaForm (χ.outgoingDir s v) (deriv χ t₀) := by
    rw [o.areaForm_swap, neg_pos]
    exact χ.areaForm_deriv_nextParam_outgoingDir_neg hv
  have hzero : f t₀ = 0 := χ.areaForm_outgoingDir_sub_nextParam hv
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hderiv).eventually (lt_mem_nhds hpos)
  obtain ⟨a, ha, ha'⟩ := ((hslope.filter_mono (nhdsLT_le_nhdsNE t₀)).and
    (Ioo_mem_nhdsLT (max_lt (by linarith) ht₀.1 : max (t₀ - ε) s < t₀))).exists
  obtain ⟨b, hb, hb'⟩ := ((hslope.filter_mono (nhdsGT_le_nhdsNE t₀)).and
    (Ioo_mem_nhdsGT (lt_min (by linarith) ht₀.2 : t₀ < min (t₀ + ε) (s + χ.period)))).exists
  rw [slope_def_field, hzero, sub_zero] at ha hb
  refine ⟨a, b, (le_max_right _ _).trans_lt ha'.1, (le_max_left _ _).trans_lt ha'.1, ha'.2,
    hb'.1, hb'.2.trans_le (min_le_left _ _), hb'.2.trans_le (min_le_right _ _), ?_, ?_⟩
  · by_contra hc
    exact ha.not_ge (div_nonpos_of_nonneg_of_nonpos (not_lt.1 hc) (by linarith [ha'.2]))
  · by_contra hc
    exact hb.not_ge (div_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (by linarith [hb'.1]))

/-- For a table with continuous unit tangent, the next collision parameter `t(s, v)` is continuous
on the strip. -/
theorem continuousAt_nextParam (hχ : Continuous (deriv χ)) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ χ.nextParam x.1 x.2) (s, v) := by
  -- `f x t = ω(u(x), χ(t) - χ(x.1))` vanishes at the next collision parameter of `x`.
  let f : ℝ × ℝ → ℝ → ℝ := fun x t ↦ o.areaForm (χ.outgoingDir x.1 x.2) (χ t - χ x.1)
  have hf : ∀ t, Continuous fun x : ℝ × ℝ ↦ f x t := fun t ↦
    (o.areaForm'.continuous₂.comp₂ (χ.continuous_outgoingDir hχ)
      (continuous_const.sub (χ.continuous.comp continuous_fst)))
  have hf' : ∀ x : ℝ × ℝ, Continuous (f x) := fun x ↦
    (LinearMap.continuous_of_finiteDimensional (o.areaForm (χ.outgoingDir x.1 x.2))).comp
      (χ.continuous.sub continuous_const)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, b, hsa, ha₁, ha₂, hb₁, hb₂, hbs, hfa, hfb⟩ :=
    χ.exists_areaForm_neg_pos_near_nextParam hv hε
  -- The sign change of `f · a` and `f · b` persists at every nearby state `x`, which locates the
  -- next collision parameter of `x` in `(a, b)`.
  filter_upwards [(hf a).continuousAt.eventually_lt continuousAt_const hfa,
    continuousAt_const.eventually_lt (hf b).continuousAt hfb,
    continuous_fst.continuousAt.eventually_lt continuousAt_const hsa,
    continuousAt_const.eventually_lt (continuous_fst.add continuous_const).continuousAt hbs,
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hv] with x h₁ h₂ h₃ h₄ h₅
  obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo (by linarith : a ≤ b) (hf' x).continuousOn ⟨h₁, h₂⟩
  have heq : t = χ.nextParam x.1 x.2 :=
    χ.eq_nextParam_of_areaForm_eq_zero h₅ ⟨h₃.trans ht.1, ht.2.trans h₄⟩ hft
  rw [← heq, Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [ht.1, ht.2]

/-- For a table with continuous unit tangent, the next tangential component `w(s, v)` is continuous
on the strip. -/
theorem continuousAt_nextTangential (hχ : Continuous (deriv χ)) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ χ.nextTangential x.1 x.2) (s, v) := by
  simp only [nextTangential_def]
  exact (χ.continuous_outgoingDir hχ).continuousAt.inner
    (hχ.continuousAt.comp (χ.continuousAt_nextParam hχ hv))

/-- For a table with continuous unit tangent, the next-collision map is continuous on the strip
`ℝ × (-1, 1)`. -/
theorem continuousOn_nextCollision (hχ : Continuous (deriv χ)) :
    ContinuousOn χ.nextCollision (univ ×ˢ Ioo (-1) 1) := by
  rintro ⟨s, v⟩ ⟨-, hv⟩
  rw [show χ.nextCollision = fun x ↦ (χ.nextParam x.1 x.2, χ.nextTangential x.1 x.2) from
    funext χ.nextCollision_apply]
  exact ((χ.continuousAt_nextParam hχ hv).prodMk
    (χ.continuousAt_nextTangential hχ hv)).continuousWithinAt

/-! ### The next-collision map and the billiard map are homeomorphisms -/

/-- A map `ℝ × ℝ → ℝ × ℝ` that is continuous on the strip `ℝ × (-1, 1)` and sends it into itself
is continuous as a map of the subtype `ℝ × (-1, 1)`. -/
private theorem continuous_restrict_strip {f : ℝ × ℝ → ℝ × ℝ}
    (hf : ContinuousOn f (univ ×ˢ Ioo (-1) 1))
    (hmaps : ∀ x : ℝ × Ioo (-1 : ℝ) 1, (f (x.1, x.2)).2 ∈ Ioo (-1) 1) :
    Continuous fun x : ℝ × Ioo (-1 : ℝ) 1 ↦
      ((f (x.1, x.2)).1, (⟨(f (x.1, x.2)).2, hmaps x⟩ : Ioo (-1 : ℝ) 1)) := by
  have hc : Continuous fun x : ℝ × Ioo (-1 : ℝ) 1 ↦ f (x.1, x.2) :=
    hf.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      fun x ↦ ⟨trivial, x.2.2⟩
  exact (continuous_fst.comp hc).prodMk ((continuous_snd.comp hc).subtype_mk _)

/-- For a table with continuous unit tangent, the next-collision map is continuous as a bijection
of the strip. -/
theorem continuous_nextCollisionEquiv (hχ : Continuous (deriv χ)) :
    Continuous χ.nextCollisionEquiv := by
  convert continuous_restrict_strip (χ.continuousOn_nextCollision hχ)
    fun x ↦ by simpa using χ.nextTangential_mem_Ioo x.2.2 using 1
  funext x
  ext <;> simp

/-- For a table with continuous unit tangent, the inverse `τ⁻¹ ∘ ι ∘ B ∘ ι` of the next-collision
map is continuous. -/
theorem continuous_nextCollisionEquiv_symm (hχ : Continuous (deriv χ)) :
    Continuous χ.nextCollisionEquiv.symm := by
  have hmaps : MapsTo (fun x : ℝ × ℝ ↦ (x.1, -x.2)) (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) :=
    fun x hx ↦ ⟨trivial, by linarith [hx.2.2], by linarith [hx.2.1]⟩
  have hc : ContinuousOn
      (fun x : ℝ × ℝ ↦ (χ.nextParam x.1 (-x.2) - χ.period, -χ.nextTangential x.1 (-x.2)))
      (univ ×ˢ Ioo (-1) 1) := by
    have := ((continuous_fst.sub (continuous_const (y := χ.period))).prodMk
      continuous_snd.neg).comp_continuousOn ((χ.continuousOn_nextCollision hχ).comp
        (continuous_fst.prodMk continuous_snd.neg).continuousOn hmaps)
    convert this using 1
    ext x <;> simp
  convert continuous_restrict_strip hc fun x ↦ χ.neg_nextTangential_neg_mem_Ioo x.1 x.2 using 1
  funext x
  ext <;> simp

/-- For a table with continuous unit tangent, the next-collision map is a homeomorphism of the
strip `ℝ × (-1, 1)`. -/
def nextCollisionHomeomorph (hχ : Continuous (deriv χ)) :
    ℝ × Ioo (-1 : ℝ) 1 ≃ₜ ℝ × Ioo (-1 : ℝ) 1 where
  toEquiv := χ.nextCollisionEquiv
  continuous_toFun := χ.continuous_nextCollisionEquiv hχ
  continuous_invFun := χ.continuous_nextCollisionEquiv_symm hχ

@[simp]
theorem coe_nextCollisionHomeomorph (hχ : Continuous (deriv χ)) :
    ⇑(χ.nextCollisionHomeomorph hχ) = χ.nextCollisionEquiv := by
  rfl

@[simp]
theorem coe_nextCollisionHomeomorph_symm (hχ : Continuous (deriv χ)) :
    ⇑(χ.nextCollisionHomeomorph hχ).symm = χ.nextCollisionEquiv.symm := by
  rfl

/-- For a table with continuous unit tangent, the billiard map of `AddCircle L × (-1, 1)` is
continuous. -/
theorem continuous_billiardMap (hχ : Continuous (deriv χ)) : Continuous χ.billiardMap := by
  have hq : IsOpenQuotientMap
      (Prod.map ((↑) : ℝ → AddCircle χ.period) (id : Ioo (-1 : ℝ) 1 → _)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  convert hq.continuous.comp (χ.continuous_nextCollisionEquiv hχ) using 1
  ext ⟨s, v⟩ <;> simp

/-- For a table with continuous unit tangent, the inverse of the billiard map is continuous. -/
theorem continuous_billiardMap_symm (hχ : Continuous (deriv χ)) :
    Continuous χ.billiardMap.symm := by
  have hq : IsOpenQuotientMap
      (Prod.map ((↑) : ℝ → AddCircle χ.period) (id : Ioo (-1 : ℝ) 1 → _)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  convert hq.continuous.comp (χ.continuous_nextCollisionEquiv_symm hχ) using 1
  ext ⟨s, v⟩
  · simp only [comp_apply, Prod.map_apply, id, billiardMap_symm_coe, nextCollisionEquiv_symm_apply]
    conv_rhs => rw [← AddCircle.coe_add_period, sub_add_cancel]
  · simp

/-- For a table with continuous unit tangent, the billiard map is a homeomorphism of the space of
collision states `AddCircle L × (-1, 1)`. -/
def billiardHomeomorph (hχ : Continuous (deriv χ)) :
    AddCircle χ.period × Ioo (-1 : ℝ) 1 ≃ₜ AddCircle χ.period × Ioo (-1 : ℝ) 1 where
  toEquiv := χ.billiardMap
  continuous_toFun := χ.continuous_billiardMap hχ
  continuous_invFun := χ.continuous_billiardMap_symm hχ

@[simp]
theorem coe_billiardHomeomorph (hχ : Continuous (deriv χ)) :
    ⇑(χ.billiardHomeomorph hχ) = χ.billiardMap := by
  rfl

@[simp]
theorem coe_billiardHomeomorph_symm (hχ : Continuous (deriv χ)) :
    ⇑(χ.billiardHomeomorph hχ).symm = χ.billiardMap.symm := by
  rfl

end StrictConvexBilliardTable

end TauCeti
