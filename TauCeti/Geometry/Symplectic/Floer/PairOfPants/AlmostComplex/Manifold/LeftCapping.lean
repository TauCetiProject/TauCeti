/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.LeftCapping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Capping

/-!
# The input-exchange family capped at `0` in a manifold

The left unit homotopy of the pair-of-pants product counts the members of the input-exchange
family capped at `0`, whose Hamiltonian perturbations are
`TauCeti.Floer.cappedExchangePerturbation H L c`, `0 ≤ c ≤ 1`, on the capped domain `ℂ ∖ {1}`.
`TauCeti.Floer.cappedExchangeAlmostComplex` constructs the matching domain-dependent almost complex
structures on a fixed symplectic vector space. This file constructs them on the tangent bundle of a
manifold `M` with a nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible smooth almost complex structure `J₀` and smooth `σ`-tame end families
`J q t`. For a neck length `L` and `c ∈ ℝ`, the smooth almost complex structure
`TauCeti.SmoothTwoForm.Compatible.cappedExchangeAlmostComplex h₀ J hJ L c w` is, on the disc
`‖w - c‖ ≤ 2 exp (2π)`, the capping structure at `0`
(`TauCeti.SmoothTwoForm.Compatible.cappingAlmostComplex`) of the pair of pants whose output family
is replaced by `J₀`, and off that disc the negative plane structure of `J_∞` translated by `c`.

* On every tangent fiber of the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the plumbing
  map at `0`, it is the linear structure `TauCeti.Floer.cappedExchangeAlmostComplex`
  (`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_cappedExchangeAlmostComplex`), and
  for `L ≥ 1` and `0 ≤ c ≤ 1` it is `J₀` at the three missing points.
* It is tame, and compatible when the end structures are.
* At `c = 0` it is the capping structure at `0` of the pair of pants with end families `J`, and at
  `c = 1`, if `J_∞` has period one, it is the capping structure at `1` of the pair of pants with
  exchanged end families (`TauCeti.Floer.exchangeEndData`) composed with `w ↦ 1 - w`.
* For `L ≥ 1` and `0 ≤ c ≤ 1` it is `J_1(t)` far out on the remaining input end, and for every
  `c` it is
  `J_∞(t)` far out on the output end recentred at `c`, for period-one end families.
* For `L > 2` and `0 ≤ c ≤ 1` it is `J₀` on the disc of radius `exp (-2π(L - 1)) / 2` about the
  capped puncture `0`.
* For `L > 4` and period-one end families which are jointly `C^n` on `ℝ × M`, it is jointly `C^n`
  along `C^n` families of parameters `-1 < c < 2`, points of the capped domain `ℂ ∖ {1}` and points
  of `M` (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappedExchangeAlmostComplex`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants and on the input exchange.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
-/

public noncomputable section

open Bundle Set Real Manifold Topology Function
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀)
  (J : Puncture → ℝ → SmoothAlmostComplexStructure I M) (hJ : ∀ q t, σ.Tames (J q t))
  {L c : ℝ}

/-- The radius `2 exp (2π)` of the disc on which the negative plane data are trivial exceeds `3`. -/
private theorem three_lt_two_mul_exp_two_pi : 3 < 2 * Real.exp (2 * π) := by
  nlinarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]

omit [FiniteDimensional ℝ E] in
/-- On a tangent fiber, the end families of the input part are the linear end families of the
input part. -/
private theorem almostComplexStructureAt_update_inf_base (x : M) :
    (fun q t (_ : Unit) => (update J inf (fun _ => J₀) q t).almostComplexStructureAt x) =
      update (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x) inf
        (fun _ _ => J₀.almostComplexStructureAt x) := by
  funext q t u
  rcases eq_or_ne q inf with rfl | hq
  · simp
  · simp [update_of_ne hq]

/-- The almost complex structure on `M` of the member `c` of the input-exchange family capped at
`0`, with neck length `L`, at the point `w ∈ ℂ`. On the disc `‖w - c‖ ≤ 2 exp (2π)` it is the
capping structure at `0` of the pair of pants with the input families of `J` and output family
`J₀`, and off that disc it is the negative plane structure of `J_∞` translated by `c`. -/
def cappedExchangeAlmostComplex (L c : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  if ‖w - c‖ ≤ 2 * Real.exp (2 * π) then
    h₀.cappingAlmostComplex (update J inf fun _ => J₀) (tames_update_inf_base h₀.tames hJ) zero L w
  else h₀.negativePlaneAlmostComplex (J inf) (hJ inf) (w - c)

/-- On the disc `‖w - c‖ ≤ 2 exp (2π)` the member `c` is the capping structure at `0` of the input
part. -/
theorem cappedExchangeAlmostComplex_of_norm_le {w : ℂ} (hw : ‖w - c‖ ≤ 2 * Real.exp (2 * π)) :
    h₀.cappedExchangeAlmostComplex J hJ L c w =
      h₀.cappingAlmostComplex (update J inf fun _ => J₀) (tames_update_inf_base h₀.tames hJ) zero L
        w := by
  simp only [cappedExchangeAlmostComplex, hw, ↓reduceIte]

/-- Off the disc `‖w - c‖ ≤ 2 exp (2π)` the member `c` is the negative plane structure of the
output family, translated by `c`. -/
theorem cappedExchangeAlmostComplex_of_lt_norm {w : ℂ} (hw : 2 * Real.exp (2 * π) < ‖w - c‖) :
    h₀.cappedExchangeAlmostComplex J hJ L c w =
      h₀.negativePlaneAlmostComplex (J inf) (hJ inf) (w - c) := by
  simp only [cappedExchangeAlmostComplex, hw.not_ge, ↓reduceIte]

/-- Every member of the family is tamed by the two-form. -/
theorem tames_cappedExchangeAlmostComplex (L c : ℝ) (w : ℂ) :
    σ.Tames (h₀.cappedExchangeAlmostComplex J hJ L c w) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  exacts [tames_cappingAlmostComplex h₀ _ _ w, tames_negativePlaneAlmostComplex h₀ _ _ _]

/-- Every member of the family is compatible with the two-form when the end structures are. -/
theorem compatible_cappedExchangeAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t)) (L c : ℝ)
    (w : ℂ) : σ.Compatible (h₀.cappedExchangeAlmostComplex J hJ L c w) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  · exact compatible_cappingAlmostComplex h₀ _ _
      ((forall_update_iff J fun _ f => ∀ t, σ.Compatible (f t)).2 ⟨fun _ => h₀, fun q _ => hJc q⟩)
      w
  · exact compatible_negativePlaneAlmostComplex h₀ _ _ (hJc inf) _

/-- On every tangent fiber of the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, the member `c` of the
family is the linear input-exchange family capped at `0` of the fiberwise end families. -/
theorem almostComplexStructureAt_cappedExchangeAlmostComplex {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) (x : M) :
    (h₀.cappedExchangeAlmostComplex J hJ L c w).almostComplexStructureAt x =
      Floer.cappedExchangeAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun q t _ => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) L c w () := by
  rcases le_or_gt ‖w - c‖ (2 * Real.exp (2 * π)) with hn | hn
  · rw [cappedExchangeAlmostComplex_of_norm_le h₀ J hJ hn,
      Floer.cappedExchangeAlmostComplex_of_norm_le _ hn,
      almostComplexStructureAt_cappingAlmostComplex h₀ _ _ hw]
    simp only [update_of_ne (show zero ≠ inf by decide),
      almostComplexStructureAt_update_inf_base J x]
  · rw [cappedExchangeAlmostComplex_of_lt_norm h₀ J hJ hn,
      Floer.cappedExchangeAlmostComplex_of_lt_norm _ hn,
      almostComplexStructureAt_negativePlaneAlmostComplex]

/-- The three points `0`, `1` and `ψ(1)` missing from the four-punctured sphere lie in the closed
unit disc, since `ψ(1)` lies within distance `exp (-2π(L - 1)) / 2` of `0`. -/
private theorem norm_le_one_of_not {w : ℂ} (hL : 1 ≤ L)
    (hw : ¬((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1)) : ‖w‖ ≤ 1 := by
  have hψ : ‖zero.plumbingMap L 1‖ ≤ 1 := by
    have h := norm_plumbingMap_one_sub_endCenter_lt zero L
    rw [endCenter_zero, sub_zero] at h
    have : Real.exp (-(2 * π * (L - 1))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    linarith
  simp only [not_and_or, not_not] at hw
  rcases hw with (rfl | rfl) | rfl <;> simp [hψ]

/-- **The missing points.** For `L ≥ 1` and `0 ≤ c ≤ 1`, at the points `0`, `1` and `ψ(1)` missing
from the four-punctured sphere, every member of the family is `J₀`. -/
theorem cappedExchangeAlmostComplex_of_not (hL : 1 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {w : ℂ}
    (hw : ¬((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1)) :
    h₀.cappedExchangeAlmostComplex J hJ L c w = J₀ := by
  have hn : ‖w - c‖ ≤ 2 * Real.exp (2 * π) := by
    have h := norm_sub_le w (c : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at h
    linarith [norm_le_one_of_not hL hw, three_lt_two_mul_exp_two_pi]
  rw [cappedExchangeAlmostComplex_of_norm_le h₀ J hJ hn, cappingAlmostComplex_of_not h₀ _ _ hw]

/-- **The start of the family is the capping structure at `0`.** For `L ≥ 2`, the member `c = 0`
of the family is the capping structure at `0` of the pair of pants with end families `J`. -/
theorem cappedExchangeAlmostComplex_zero (hL : 2 ≤ L) :
    h₀.cappedExchangeAlmostComplex J hJ L 0 = h₀.cappingAlmostComplex J hJ zero L := by
  funext w
  by_cases hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1
  · refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex h₀ J hJ hw,
      Floer.cappedExchangeAlmostComplex_zero _ hL,
      almostComplexStructureAt_cappingAlmostComplex h₀ J hJ hw]
  · rw [cappedExchangeAlmostComplex_of_not h₀ J hJ (by linarith) le_rfl zero_le_one hw,
      cappingAlmostComplex_of_not h₀ J hJ hw]

omit [FiniteDimensional ℝ E] in
/-- On a tangent fiber, the exchanged end families are the exchanged linear end families. -/
private theorem almostComplexStructureAt_exchangeEndData (x : M) :
    (fun q t (_ : Unit) => (Floer.exchangeEndData J q t).almostComplexStructureAt x) =
      Floer.exchangeEndData (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x) := by
  funext q
  cases q <;> simp only [Floer.exchangeEndData_zero, Floer.exchangeEndData_one,
    Floer.exchangeEndData_inf]

/-- The second input of the sphere plumbed into the end at `1` is the image under the exchange
`w ↦ 1 - w` of the second input of the sphere plumbed into the end at `0`. -/
private theorem one_plumbingMap_one (L : ℝ) : one.plumbingMap L 1 = 1 - zero.plumbingMap L 1 := by
  rw [plumbingMap_apply, plumbingMap_apply, plumbingFactor_one, endCenter_one, endCenter_zero]
  ring

/-- **The end of the family is the exchanged capping structure at `1`.** If the output family
`J_∞` has period one in `t` and `L ≥ 2`, the member `c = 1` of the family at `w` is the capping
structure at `1` of the pair of pants with exchanged end families (`TauCeti.Floer.exchangeEndData`)
at `1 - w`. -/
theorem cappedExchangeAlmostComplex_one (hJp : Periodic (J inf) 1)
    (hJ' : ∀ q t, σ.Tames (Floer.exchangeEndData J q t)) (hL : 2 ≤ L) (w : ℂ) :
    h₀.cappedExchangeAlmostComplex J hJ L 1 w =
      h₀.cappingAlmostComplex (Floer.exchangeEndData J) hJ' one L (1 - w) := by
  have hiff : ((1 - w ≠ 0 ∧ 1 - w ≠ 1) ∧ 1 - w ≠ one.plumbingMap L 1) ↔
      ((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) := by
    simp only [one_plumbingMap_one, ne_eq, sub_eq_zero, sub_eq_self, sub_right_inj]
    exact ⟨fun ⟨⟨h₁, h₀⟩, hψ⟩ => ⟨⟨h₀, fun h => h₁ h.symm⟩, hψ⟩,
      fun ⟨⟨h₀, h₁⟩, hψ⟩ => ⟨⟨fun h => h₁ h.symm, h₀⟩, hψ⟩⟩
  by_cases hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1
  · refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex h₀ J hJ hw,
      Floer.cappedExchangeAlmostComplex_one _ (fun t => by simp only [hJp t])
        (fun q t _ => by
          rw [← congrFun (congrFun (almostComplexStructureAt_exchangeEndData J x) q) t]
          exact h₀.isNondegenerate.tames_iff.mp (hJ' q t) x) hL,
      almostComplexStructureAt_cappingAlmostComplex h₀ _ hJ' (hiff.2 hw)]
    simp only [almostComplexStructureAt_exchangeEndData, Floer.exchangeEndData_one]
  · rw [cappedExchangeAlmostComplex_of_not h₀ J hJ (by linarith) zero_le_one le_rfl hw,
      cappingAlmostComplex_of_not h₀ _ hJ' (mt hiff.1 hw)]

/-- **The family is `J_1(t)` far out on the remaining input end.** For `0 ≤ c ≤ 1` and `L ≥ 1`, if
`J_1` has period one in `t`, then on the part `s ≥ 2` of the input end at `1` the member `c` of the
family at the point with end coordinates `z = s + i t` is `J_1 t`. -/
theorem cappedExchangeAlmostComplex_cylindricalEndLift (hJp : Periodic (J one) 1) (hL : 1 ≤ L)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 2 ≤ z.re) :
    h₀.cappedExchangeAlmostComplex J hJ L c (one.cylindricalEndLift z) = J one z.im := by
  -- The point lies at distance at least `1/2` from `0`, so it is not `ψ(1)`.
  have hS := one.cylindricalEndLift_ne_zero_and_ne_one (z := z)
    (by rw [endSign_eq_one (by decide), one_mul]; linarith)
  have hw : ((one.cylindricalEndLift z ≠ 0 ∧ one.cylindricalEndLift z ≠ 1) ∧
      one.cylindricalEndLift z ≠ zero.plumbingMap L 1) := by
    refine mem_plumbedSphere_of_le_norm_sub_endCenter (Or.inr hS) ?_
    have h := norm_cylindricalEndLift_sub_endCenter one z
    rw [norm_endScale (by decide), endCenter_one] at h
    have h₁ : Real.exp (-(2 * π * z.re)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have h₂ : Real.exp (-(2 * π * (L - 1))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have h₃ := norm_sub_norm_le (1 : ℂ) (one.cylindricalEndLift z)
    rw [norm_one, norm_sub_rev] at h₃
    rw [endCenter_zero, sub_zero]
    linarith
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  rw [almostComplexStructureAt_cappedExchangeAlmostComplex h₀ J hJ hw,
    Floer.cappedExchangeAlmostComplex_cylindricalEndLift _ (fun t => by simp only [hJp t])
      (by linarith) hc₀ hc₁ hz]

/-- **The family is `J_∞(t)` far out on the output end.** If `J_∞` has period one in `t`, then on
the part `s ≤ -2` of the output end recentred at `c`, the member `c` of the family at the point
`c + φ_∞(z)` with end coordinates `z = s + i t` is `J_∞ t`. -/
theorem cappedExchangeAlmostComplex_add_cylindricalEndLift_inf (hJp : Periodic (J inf) 1)
    (L c : ℝ) {z : ℂ} (hz : z.re ≤ -2) :
    h₀.cappedExchangeAlmostComplex J hJ L c (c + inf.cylindricalEndLift z) = J inf z.im := by
  have hφ : 2 * Real.exp (2 * π) < ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    rw [h]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])) two_pos
  rw [cappedExchangeAlmostComplex_of_lt_norm h₀ J hJ (by rwa [add_sub_cancel_left]),
    add_sub_cancel_left, negativePlaneAlmostComplex_cylindricalEndLift h₀ _ _ hJp hz]

/-- **The capped disc.** For `L > 2` and `0 ≤ c ≤ 1`, every member of the family is `J₀` on the
disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture `0`, the image under the plumbing
map of the pole disc of the plane. -/
theorem cappedExchangeAlmostComplex_eq_of_norm_le (hL : 2 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) :
    h₀.cappedExchangeAlmostComplex J hJ L c w = J₀ := by
  have hρ : Real.exp (-(2 * π * (L - 1))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hn : ‖w - c‖ ≤ 2 * Real.exp (2 * π) := by
    have h := norm_sub_le w (c : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at h
    linarith [three_lt_two_mul_exp_two_pi]
  rw [cappedExchangeAlmostComplex_of_norm_le h₀ J hJ hn]
  exact cappingAlmostComplex_eq_of_norm_sub_endCenter_le h₀ _ _ (by decide) hL
    (by rwa [endCenter_zero, sub_zero])

/-- Away from the two inputs, the capping structure at `0` of the input part is `J₀`. -/
private theorem cappingAlmostComplex_update_inf_base_eq (hL : 2 ≤ L) {w : ℂ} (hw₀ : 1 / 2 ≤ ‖w‖)
    (hw₁ : 1 / 2 ≤ ‖w - 1‖) :
    h₀.cappingAlmostComplex (update J inf fun _ => J₀) (tames_update_inf_base h₀.tames hJ) zero L
      w = J₀ := by
  have hρ : Real.exp (-(2 * π * (L - 1))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1 :=
    mem_plumbedSphere_of_le_norm_sub_endCenter
      (Or.inr ⟨fun h => by norm_num [h] at hw₀, fun h => by norm_num [h] at hw₁⟩)
      (by rw [endCenter_zero, sub_zero]; linarith)
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  rw [almostComplexStructureAt_cappingAlmostComplex h₀ _ _ hw, Floer.plumbedAlmostComplex_def,
    ite_eq_right (not_lt.2 (Floer.re_endCoord_zero_le_div_two hL hw₀))]
  simp only [almostComplexStructureAt_update_inf_base J x]
  exact Floer.pairOfPantsAlmostComplex_update_inf_base_eq
    (hJb := fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) (h₀.compatibleAt x) hw₀ hw₁ ()

/-- **The family is smooth.** For end families which have period one in `t` and are `C^n` on
`ℝ × M`, and a neck length `L > 4`, the input-exchange family capped at `0` is `C^n` jointly in the
parameter, the domain point and the target point, along any `C^n` family of these whose parameters
lie in `(-1, 2)` and whose domain points lie in the capped domain `ℂ ∖ {1}`. The family may depend
on further manifold parameters. -/
theorem contMDiff_cappedExchangeAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hL : 4 < L) {γ : N → ℝ} {f : N → ℂ} {b : N → M} (hγ : ContMDiff I' 𝓘(ℝ) n γ)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) (hγI : ∀ p, γ p ∈ Ioo (-1) 2)
    (hf₁ : ∀ p, f p ≠ 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) (b p)
        ((h₀.cappedExchangeAlmostComplex J hJ L (γ p) (f p)).toEndomorphism (b p))) := by
  -- The capping structure of the input part is smooth along the whole family.
  have hcap := contMDiff_cappingAlmostComplex h₀ (update J inf fun _ => J₀)
    (tames_update_inf_base h₀.tames hJ)
    ((forall_update_iff J fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hJp q⟩)
    ((forall_update_iff J fun _ f => ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((f p.1).toEndomorphism p.2))).2
      ⟨(J₀.toEndomorphism.contMDiff.of_le ENat.LEInfty.out).comp contMDiff_snd,
        fun q _ => hJs q⟩)
    (q := zero) (by decide) (ℓ := fun _ => L) contMDiff_const hf hb (fun _ => hL)
    (fun p => by
      rcases eq_or_ne (f p) 0 with h | h
      · exact Or.inl (h.trans endCenter_zero.symm)
      · exact Or.inr ⟨h, hf₁ p⟩)
  -- So is the translated plane structure.
  have hsub : ContMDiff I' 𝓘(ℝ, ℂ) n fun p => f p - (γ p : ℂ) :=
    hf.sub (Complex.ofRealCLM.contDiff.contMDiff.comp hγ)
  have hpl := contMDiff_negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (hJp inf) (hJs inf) hsub hb
  have hdist : Continuous fun p => ‖f p - (γ p : ℂ)‖ := hsub.continuous.norm
  intro p
  rcases lt_or_ge ‖f p - (γ p : ℂ)‖ (2 * Real.exp (2 * π)) with hlt | hge
  · -- Near the disc `‖w - c‖ < 2 exp (2π)` the family is the capping structure of the input part.
    refine (hcap p).congr_of_eventuallyEq ?_
    filter_upwards [hdist.continuousAt.eventually (gt_mem_nhds hlt)] with p' hp'
    rw [cappedExchangeAlmostComplex_of_norm_le h₀ J hJ hp'.le]
  · -- Away from the disc `‖w - c‖ ≤ 3` the family is the translated plane structure.
    refine (hpl p).congr_of_eventuallyEq ?_
    have h3 : 3 < ‖f p - (γ p : ℂ)‖ := three_lt_two_mul_exp_two_pi.trans_le hge
    filter_upwards [hdist.continuousAt.eventually (lt_mem_nhds h3)] with p' hp'
    rcases le_or_gt ‖f p' - (γ p' : ℂ)‖ (2 * Real.exp (2 * π)) with hle | hgt
    · -- In the annulus `3 < ‖w - c‖ ≤ 2 exp (2π)` both structures are the base structure.
      obtain ⟨hw₀, hw₁⟩ := half_le_norm_of_le_norm_sub (r := 2) (w := f p')
        (abs_le.2 ⟨by linarith [(hγI p').1], (hγI p').2.le⟩)
        (abs_le.2 ⟨by linarith [(hγI p').1], by linarith [(hγI p').2]⟩) (by linarith)
      rw [cappedExchangeAlmostComplex_of_norm_le h₀ J hJ hle,
        cappingAlmostComplex_update_inf_base_eq h₀ J hJ (by linarith) hw₀ hw₁,
        negativePlaneAlmostComplex_eq_of_norm_le h₀ _ _ hle]
    · rw [cappedExchangeAlmostComplex_of_lt_norm h₀ J hJ hgt]

end TauCeti.SmoothTwoForm.Compatible
