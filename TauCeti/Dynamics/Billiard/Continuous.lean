/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Inverse
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.Deriv.Slope

/-!
# The billiard map is a homeomorphism

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)`. This file proves that the unit tangent `χ'` is
continuous (`TauCeti.StrictConvexBilliardTable.continuous_deriv`) and that `B` is continuous on the
strip (`TauCeti.StrictConvexBilliardTable.continuousOn_nextCollision`). Its inverse is
`τ⁻¹ ∘ ι ∘ B ∘ ι`, with `ι(s, v) = (s, -v)` and `τ(s, v) = (s + L, v)`, so `B` is a homeomorphism
of the strip (`TauCeti.StrictConvexBilliardTable.nextCollisionHomeomorph`), and the billiard map `β`
it induces on the space of collision states `AddCircle L × (-1, 1)` is a homeomorphism
(`TauCeti.StrictConvexBilliardTable.billiardHomeomorph`).

The unit tangent is continuous because strict convexity determines it: a cluster value `u` of `χ'`
at `s` keeps the whole table weakly to its left, so `t ↦ ω(u, χ(t) - χ(s))` has a minimum at `s`,
where `ω` is the area form. Its derivative `ω(u, χ'(s))` there vanishes, so `u = ±χ'(s)`, and the
table cannot lie to the left of `-χ'(s)`.

The proof of continuity of `B` uses only the transversality of the chord at its far end. For the
state `x = (s, v)` with outgoing velocity `u(x)`, the next collision parameter `t₀` is the unique
zero in `(s, s + L)` of `f_x(t) = ω(u(x), χ(t) - χ(s))`. Its derivative there is
`ω(u(x), χ'(t₀)) = √(1 - w ^ 2) > 0`, since the chord is not tangent to the boundary at
`χ(t₀)`. So `f_x` changes sign from negative to positive on any small interval `[a, b]` around
`t₀`. Since `f_y(a)` and `f_y(b)` depend continuously on the state `y`, the same sign change holds
for every nearby state, and the intermediate value theorem and the uniqueness of the next collision
put the next collision parameter of `y` in `(a, b)`. No second derivative of `χ` is used.

## Main results

* `TauCeti.StrictConvexBilliardTable.continuous_deriv`: the unit tangent is continuous.
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

/-! ### Continuity of the unit tangent -/

/-- The unit tangent `χ'` of a strictly convex table is continuous: a cluster value `u` of `χ'` at
`s` keeps the whole table weakly to its left, `0 ≤ ω(u, χ(t) - χ(s))`, which forces `u = χ'(s)`. -/
theorem continuous_deriv : Continuous (deriv χ) := by
  have hnonneg : ∀ r t, 0 ≤ o.areaForm (deriv χ r) (χ t - χ r) := fun r t ↦ by
    by_cases h : χ t = χ r
    · simp [h]
    · exact (χ.areaForm_pos r t h).le
  refine continuous_iff_continuousAt.2 fun s ↦ continuousAt_iff_ultrafilter.2 fun g hg ↦ ?_
  obtain ⟨u, hu, hgu⟩ := (isCompact_sphere (0 : E) 1).ultrafilter_le_nhds (g.map (deriv χ))
    (le_principal_iff.2 (Ultrafilter.mem_map.2 (Eventually.of_forall fun r ↦ by
      simp [χ.norm_deriv r])))
  have hgu : Tendsto (deriv χ) g (𝓝 u) := hgu
  rw [mem_sphere_zero_iff_norm] at hu
  -- The limit `u` of the tangents keeps the whole table weakly to its left.
  have hleft : ∀ t, 0 ≤ o.areaForm u (χ t - χ s) := fun t ↦
    ge_of_tendsto ((o.areaForm'.continuous₂.tendsto (u, χ t - χ s)).comp
      (hgu.prodMk_nhds ((tendsto_const_nhds.sub (χ.continuous.tendsto s)).mono_left hg)))
      (Eventually.of_forall fun r ↦ hnonneg r t)
  -- So `t ↦ ω(u, χ(t) - χ(s))` has a minimum at `s`, where its derivative `ω(u, χ'(s))` vanishes.
  have hzero : o.areaForm u (deriv χ s) = 0 :=
    IsLocalMin.hasDerivAt_eq_zero (f := fun t ↦ o.areaForm u (χ t - χ s))
      (Eventually.of_forall fun t ↦ by simpa using hleft t)
      ((o.areaForm u).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s
        ((χ.differentiableAt s).hasDerivAt.sub_const (χ s)))
  have hinner : ⟪u, deriv χ s⟫ = 1 ∨ ⟪u, deriv χ s⟫ = -1 := by
    simpa [hzero, hu, χ.norm_deriv s] using o.inner_sq_add_areaForm_sq u (deriv χ s)
  rcases hinner with h | h
  · rwa [← (inner_eq_one_iff_of_norm_eq_one hu (χ.norm_deriv s)).1 h]
  · -- The opposite tangent `-χ'(s)` would put the rest of the table on its right.
    rw [(inner_eq_neg_one_iff_of_norm_eq_one hu (χ.norm_deriv s)).1 h] at hleft
    have ht : s + χ.period / 2 ∈ Ioo s (s + χ.period) :=
      ⟨by linarith [χ.period_pos], by linarith [χ.period_pos]⟩
    have h₁ := hleft (s + χ.period / 2)
    simp only [map_neg, LinearMap.neg_apply, neg_nonneg] at h₁
    exact absurd h₁ (χ.areaForm_pos s _ (χ.apply_ne_of_mem_Ioo ht)).not_ge

/-! ### Continuity of the next-collision map on the strip -/

/-- The outgoing velocity `u(s, v)` depends continuously on the state `(s, v)`. -/
theorem continuous_outgoingDir : Continuous fun x : ℝ × ℝ ↦ χ.outgoingDir x.1 x.2 := by
  simp only [outgoingDir_def]
  exact (continuous_snd.smul (χ.continuous_deriv.comp continuous_fst)).add
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_snd.pow 2))).smul
      (o.rightAngleRotation.continuous.comp (χ.continuous_deriv.comp continuous_fst)))

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
  obtain ⟨a, ha, ha'⟩ := ((hderiv.hasDerivWithinAt.eventually_nhdsLT_lt_of_pos hpos).and
    (Ioo_mem_nhdsLT (max_lt (by linarith) ht₀.1 : max (t₀ - ε) s < t₀))).exists
  obtain ⟨b, hb, hb'⟩ := ((hderiv.hasDerivWithinAt.eventually_nhdsGT_lt_of_pos hpos).and
    (Ioo_mem_nhdsGT (lt_min (by linarith) ht₀.2 : t₀ < min (t₀ + ε) (s + χ.period)))).exists
  exact ⟨a, b, (le_max_right _ _).trans_lt ha'.1, (le_max_left _ _).trans_lt ha'.1, ha'.2,
    hb'.1, hb'.2.trans_le (min_le_left _ _), hb'.2.trans_le (min_le_right _ _),
    ha.trans_eq hzero, hzero.symm.trans_lt hb⟩

/-- The next collision parameter `t(s, v)` is continuous on the strip. -/
theorem continuousAt_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ χ.nextParam x.1 x.2) (s, v) := by
  -- `f x t = ω(u(x), χ(t) - χ(x.1))` vanishes at the next collision parameter of `x`.
  let f : ℝ × ℝ → ℝ → ℝ := fun x t ↦ o.areaForm (χ.outgoingDir x.1 x.2) (χ t - χ x.1)
  have hf : ∀ t, Continuous fun x : ℝ × ℝ ↦ f x t := fun t ↦
    (o.areaForm'.continuous₂.comp₂ χ.continuous_outgoingDir
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

/-- The next tangential component `w(s, v)` is continuous on the strip. -/
theorem continuousAt_nextTangential {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ χ.nextTangential x.1 x.2) (s, v) := by
  simp only [nextTangential_def]
  exact χ.continuous_outgoingDir.continuousAt.inner
    (χ.continuous_deriv.continuousAt.comp (χ.continuousAt_nextParam hv))

/-- The next-collision map is continuous on the strip `ℝ × (-1, 1)`. -/
theorem continuousOn_nextCollision : ContinuousOn χ.nextCollision (univ ×ˢ Ioo (-1) 1) := by
  rintro ⟨s, v⟩ ⟨-, hv⟩
  rw [show χ.nextCollision = fun x ↦ (χ.nextParam x.1 x.2, χ.nextTangential x.1 x.2) from
    funext χ.nextCollision_apply]
  exact ((χ.continuousAt_nextParam hv).prodMk
    (χ.continuousAt_nextTangential hv)).continuousWithinAt

/-! ### The next-collision map and the billiard map are homeomorphisms -/

/-- The next-collision map is continuous as a bijection of the strip. -/
theorem continuous_nextCollisionEquiv : Continuous χ.nextCollisionEquiv := by
  have hc : Continuous fun x : ℝ × Ioo (-1 : ℝ) 1 ↦ χ.nextCollision (x.1, x.2) :=
    χ.continuousOn_nextCollision.comp_continuous
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))
      fun x ↦ ⟨trivial, x.2.property⟩
  convert (continuous_fst.comp hc).prodMk ((continuous_snd.comp hc).subtype_mk
    fun x ↦ χ.nextCollision_snd_mem_Ioo x.2.property) using 1
  funext x
  ext <;> simp

/-- The time reversal `v ↦ -v` of tangential components is continuous on `(-1, 1)`. -/
private theorem continuous_neg_Ioo :
    Continuous fun v : Ioo (-1 : ℝ) 1 ↦
      (⟨-v, by linarith [v.property.2], by linarith [v.property.1]⟩ : Ioo (-1 : ℝ) 1) :=
  continuous_subtypeVal.neg.subtype_mk _

/-- The inverse `τ⁻¹ ∘ ι ∘ B ∘ ι` of the next-collision map is continuous. -/
theorem continuous_nextCollisionEquiv_symm : Continuous χ.nextCollisionEquiv.symm := by
  convert ((continuous_fst.sub (continuous_const (y := χ.period))).prodMk
    (continuous_neg_Ioo.comp continuous_snd)).comp
      (χ.continuous_nextCollisionEquiv.comp
        (continuous_fst.prodMk (continuous_neg_Ioo.comp continuous_snd))) using 1
  funext x
  ext <;> simp

/-- The next-collision map is a homeomorphism of the strip `ℝ × (-1, 1)`. -/
def nextCollisionHomeomorph : ℝ × Ioo (-1 : ℝ) 1 ≃ₜ ℝ × Ioo (-1 : ℝ) 1 where
  toEquiv := χ.nextCollisionEquiv
  continuous_toFun := χ.continuous_nextCollisionEquiv
  continuous_invFun := χ.continuous_nextCollisionEquiv_symm

@[simp]
theorem nextCollisionHomeomorph_toEquiv :
    χ.nextCollisionHomeomorph.toEquiv = χ.nextCollisionEquiv := by
  rfl

@[simp]
theorem coe_nextCollisionHomeomorph : ⇑χ.nextCollisionHomeomorph = χ.nextCollisionEquiv := by
  rfl

@[simp]
theorem coe_nextCollisionHomeomorph_symm :
    ⇑χ.nextCollisionHomeomorph.symm = χ.nextCollisionEquiv.symm := by
  rfl

/-- The billiard map of `AddCircle L × (-1, 1)` is continuous. -/
theorem continuous_billiardMap : Continuous χ.billiardMap := by
  have hq : IsOpenQuotientMap
      (Prod.map ((↑) : ℝ → AddCircle χ.period) (id : Ioo (-1 : ℝ) 1 → _)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  convert hq.continuous.comp χ.continuous_nextCollisionEquiv using 1
  ext ⟨s, v⟩ <;> simp

/-- The inverse `ι ∘ β ∘ ι` of the billiard map is continuous. -/
theorem continuous_billiardMap_symm : Continuous χ.billiardMap.symm := by
  convert (continuous_id.prodMap continuous_neg_Ioo).comp
    (χ.continuous_billiardMap.comp (continuous_id.prodMap continuous_neg_Ioo)) using 1
  funext ⟨θ, v⟩
  induction θ using QuotientAddGroup.induction_on with | H s => ?_
  ext <;> simp

/-- The billiard map is a homeomorphism of the space of collision states
`AddCircle L × (-1, 1)`. -/
def billiardHomeomorph :
    AddCircle χ.period × Ioo (-1 : ℝ) 1 ≃ₜ AddCircle χ.period × Ioo (-1 : ℝ) 1 where
  toEquiv := χ.billiardMap
  continuous_toFun := χ.continuous_billiardMap
  continuous_invFun := χ.continuous_billiardMap_symm

@[simp]
theorem billiardHomeomorph_toEquiv : χ.billiardHomeomorph.toEquiv = χ.billiardMap := by
  rfl

@[simp]
theorem coe_billiardHomeomorph : ⇑χ.billiardHomeomorph = χ.billiardMap := by
  rfl

@[simp]
theorem coe_billiardHomeomorph_symm : ⇑χ.billiardHomeomorph.symm = χ.billiardMap.symm := by
  rfl

end StrictConvexBilliardTable

end TauCeti
