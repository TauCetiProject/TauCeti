/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Almost complex structures along the input-exchange family capped at `0`

The unit of the pair-of-pants product is a unit on both sides. On the left it is proved with the
family of Floer data that caps the input at `0` of the pair of pants `S = ℂ ∖ {0, 1}` by a
negative PSS plane and moves the output end from `0` to `1`. Its Hamiltonian perturbations are
`TauCeti.Floer.cappedExchangePerturbation H L c`, `0 ≤ c ≤ 1`: the input-exchange datum
`TauCeti.Floer.exchangePerturbation H c` with the negative plane of `H_0` plumbed into the end at
`0` along a neck of length `L`. This file constructs the matching family of domain-dependent
almost complex structures.

Fix an `ω`-compatible base structure `J₀` and families `J_q(t, x)` of `ω`-tame structures on the
three ends. The member `TauCeti.Floer.cappedExchangeAlmostComplex h₀ J hJ L c` is, on the half-neck
`Re z > L/2` of the end at `0`, the negative plane structure of `J_0`
(`TauCeti.Floer.negativePlaneAlmostComplex`) in the plumbing coordinate `w / ψ'` of
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap`, and elsewhere the member `c` of the
input-exchange family `TauCeti.Floer.exchangeAlmostComplex`. It is the same plumbing as for the
capping family at `0`, `TauCeti.Floer.plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf
(J zero)) J _ _ zero L`, with the receiving pair-of-pants structure replaced by the member `c` of
the input-exchange family. The main results are:

* `TauCeti.Floer.tames_cappedExchangeAlmostComplex`,
  `TauCeti.Floer.compatible_cappedExchangeAlmostComplex`: every member is `ω`-tame, and
  `ω`-compatible when the end structures are.
* `TauCeti.Floer.cappedExchangeAlmostComplex_zero`: at `c = 0` the family is the capping structure
  at `0`.
* `TauCeti.Floer.cappedExchangeAlmostComplex_one`: at `c = 1`, if `J_∞` has period one, its value at
  `w` is the capping structure at `1` of the exchanged end structures
  (`TauCeti.Floer.exchangeEndData`) at `1 - w`. The exchange `σ(w) = 1 - w` carries the plumbing at
  `0` to the plumbing at `1`, and the input-exchange family at `c = 1` to the exchanged
  pair-of-pants structure.
* `TauCeti.Floer.cappedExchangeAlmostComplex_of_norm_le`: for `-1 ≤ c ≤ 2`, on the disc `‖w‖ ≤ 1`
  every member is the capping structure at `0`. So it is `J₀` on the image
  `‖w‖ ≤ exp (-2π(L - 1)) / 2` of the pole disc of the plane, for `L > 2`
  (`TauCeti.Floer.cappedExchangeAlmostComplex_eq_of_norm_le`), and it is `J₀` at the puncture `1`,
  for `L ≥ 2` (`TauCeti.Floer.cappedExchangeAlmostComplex_endCenter_one`).
* `TauCeti.Floer.cappedExchangeAlmostComplex_cylindricalEndLift` and
  `TauCeti.Floer.cappedExchangeAlmostComplex_add_cylindricalEndLift_inf`: for `0 ≤ c ≤ 1` every
  member is `J_1(t, x)` far out on the input end at `1`, in the end lift `φ_1`, and `J_∞(t, x)` far
  out on the output end, in the end lift `c + φ_∞`, when these have period one. These are the end
  coordinates in which the members of `TauCeti.Floer.cappedExchangePerturbation` are `H_q(t) dt`.
* `TauCeti.Floer.contMDiffAt_cappedExchangeAlmostComplex`: for period-one `C^n` end families and
  `L > 4`, the family is `C^n` jointly in the parameter `-1 < c < 2`, the point of the capped
  domain `ℂ ∖ {1}` and the point `x`.

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

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M V : Type*}

section Algebraic

variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {L c : ℝ} {w : ℂ}

open Classical in
/-- **The input-exchange family of almost complex structures capped at `0`.** For a neck length
`L` and `c ∈ ℝ`, relative to an `ω`-compatible base structure `J₀`, this is the negative plane
structure of the input structure `J_0` in the plumbing coordinate `(w - c_0) / ψ'` on the half-neck
`Re z > L/2` of the end at `0`, and the member `c` of the input-exchange family
`TauCeti.Floer.exchangeAlmostComplex` elsewhere. At `c = 0` it is the capping structure at `0`
(`TauCeti.Floer.cappedExchangeAlmostComplex_zero`), and at `c = 1` the capping structure at `1` of
the exchanged end structures, composed with `w ↦ 1 - w`
(`TauCeti.Floer.cappedExchangeAlmostComplex_one`). -/
def cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀)
    (J : Puncture → ℝ → M → AlmostComplexStructure V) (hJ : ∀ q t x, ω.Tames (J q t x))
    (L c : ℝ) (w : ℂ) (x : M) : AlmostComplexStructure V :=
  if L / 2 < (zero.endCoord w).re then
    negativePlaneAlmostComplex h₀ (J zero) (hJ zero)
      ((w - zero.endCenter) / zero.plumbingFactor L) x
  else exchangeAlmostComplex h₀ J hJ c w x

/-- On the half-neck `Re z > L/2` of the end at `0`, every member of the family is the negative
plane structure of `J_0` in the plumbing coordinate. -/
theorem cappedExchangeAlmostComplex_of_lt_re_endCoord (h₀ : ω.Compatible J₀)
    (hw : L / 2 < (zero.endCoord w).re) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x =
      negativePlaneAlmostComplex h₀ (J zero) (hJ zero)
        ((w - zero.endCenter) / zero.plumbingFactor L) x :=
  ite_eq_left hw

/-- Off the half-neck `Re z > L/2` of the end at `0`, the member `c` of the family is the member `c`
of the input-exchange family. -/
theorem cappedExchangeAlmostComplex_of_re_endCoord_le (h₀ : ω.Compatible J₀)
    (hw : (zero.endCoord w).re ≤ L / 2) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x = exchangeAlmostComplex h₀ J hJ c w x :=
  ite_eq_right hw.not_gt

/-- Every member of the family is tamed by `ω`. -/
theorem tames_cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀) (L c : ℝ) (w : ℂ) (x : M) :
    ω.Tames (cappedExchangeAlmostComplex h₀ J hJ L c w x) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  exacts [tames_negativePlaneAlmostComplex h₀ _ x, tames_exchangeAlmostComplex h₀ c w x]

/-- Every member of the family is `ω`-compatible when the end structures are. -/
theorem compatible_cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (L c : ℝ) (w : ℂ) (x : M) :
    ω.Compatible (cappedExchangeAlmostComplex h₀ J hJ L c w x) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  exacts [compatible_negativePlaneAlmostComplex h₀ (hJc zero) _ x,
    compatible_exchangeAlmostComplex h₀ hJc c w x]

/-- **The start of the family is the capping structure at `0`.** At `c = 0` the family is the
structure obtained by plumbing the negative plane with end structure `J_0` into the end at `0` of
the pair of pants with end structures `J`, over the same base structure `J₀`. -/
@[simp]
theorem cappedExchangeAlmostComplex_zero (h₀ : ω.Compatible J₀) :
    cappedExchangeAlmostComplex h₀ J hJ L 0 =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero)) J
        (tames_update_inf h₀.tames (hJ zero)) hJ zero L := by
  funext w x
  rcases lt_or_ge (L / 2) (zero.endCoord w).re with hw | hw
  · rw [cappedExchangeAlmostComplex_of_lt_re_endCoord h₀ hw, plumbedAlmostComplex_def,
      ite_eq_left hw, pairOfPantsAlmostComplex_update_inf]
  · rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ hw, exchangeAlmostComplex_zero,
      plumbedAlmostComplex_def, ite_eq_right hw.not_gt]

/-- **The end of the family is the exchanged capping structure at `1`.** If the output structure
`J_∞` has period one in `t`, the member `c = 1` of the family at `w` is, at `1 - w`, the structure
obtained by plumbing the negative plane with end structure `J_0` into the end at `1` of the pair of
pants with exchanged end structures (`TauCeti.Floer.exchangeEndData`: `J_1` at `0`, `J_0` at `1`
and `t ↦ J_∞(t + 1/2)` at `∞`). -/
theorem cappedExchangeAlmostComplex_one (h₀ : ω.Compatible J₀) (hJp : Periodic (J inf) 1)
    (hJ' : ∀ q t x, ω.Tames (exchangeEndData J q t x)) (w : ℂ) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L 1 w x =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero)) (exchangeEndData J)
        (tames_update_inf h₀.tames (hJ zero)) hJ' one L (1 - w) x := by
  have hre : (one.endCoord (1 - w)).re = (zero.endCoord w).re := by rw [endCoord_one_one_sub]
  rcases lt_or_ge (L / 2) (zero.endCoord w).re with hw | hw
  · -- In plumbing coordinates the exchange is the identity.
    have hpt : (1 - w - one.endCenter) / one.plumbingFactor L =
        (w - zero.endCenter) / zero.plumbingFactor L := by
      rw [plumbingFactor_one, endCenter_one, endCenter_zero, div_neg, ← neg_div]
      ring_nf
    rw [cappedExchangeAlmostComplex_of_lt_re_endCoord h₀ hw, plumbedAlmostComplex_def,
      ite_eq_left (by rwa [hre]), hpt, pairOfPantsAlmostComplex_update_inf]
  · rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ hw, exchangeAlmostComplex_one h₀ hJp hJ',
      plumbedAlmostComplex_def, ite_eq_right (by rw [hre]; exact hw.not_gt)]

/-- **Near the capped puncture the family is the capping structure at `0`.** For `-1 ≤ c ≤ 2`, on
the disc `‖w‖ ≤ 1` the member `c` of the family is the capping structure at `0`, whatever the neck
length. -/
theorem cappedExchangeAlmostComplex_of_norm_le (h₀ : ω.Compatible J₀) (hc : c ∈ Icc (-1) 2)
    (hw : ‖w‖ ≤ 1) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero)) J
        (tames_update_inf h₀.tames (hJ zero)) hJ zero L w x := by
  rcases lt_or_ge (L / 2) (zero.endCoord w).re with hw' | hw'
  · rw [cappedExchangeAlmostComplex_of_lt_re_endCoord h₀ hw', plumbedAlmostComplex_def,
      ite_eq_left hw', pairOfPantsAlmostComplex_update_inf]
  · rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ hw',
      exchangeAlmostComplex_eq_pairOfPantsAlmostComplex h₀ hc (hw.trans (by norm_num)),
      plumbedAlmostComplex_def,
      ite_eq_right hw'.not_gt]

/-- **The capped disc.** For `L > 2` and `-1 ≤ c ≤ 2`, every member of the family is `J₀` on the
disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture `0`, the image under the plumbing
map of the pole disc of the plane. -/
theorem cappedExchangeAlmostComplex_eq_of_norm_le (h₀ : ω.Compatible J₀) (hL : 2 < L)
    (hc : c ∈ Icc (-1) 2) (hw : ‖w‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x = J₀ := by
  have hw₁ : ‖w‖ ≤ 1 := hw.trans <| by
    have : Real.exp (-(2 * π * (L - 1))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    linarith
  rw [cappedExchangeAlmostComplex_of_norm_le h₀ hc hw₁]
  exact plumbedAlmostComplex_update_inf_eq h₀ (by decide) hL (by simpa using hw) x

/-- **The uncapped input.** For `L ≥ 2` and `-1 ≤ c ≤ 2`, every member of the family is `J₀` at
the puncture `1`. -/
theorem cappedExchangeAlmostComplex_endCenter_one (h₀ : ω.Compatible J₀) (hL : 2 ≤ L)
    (hc : c ∈ Icc (-1) 2) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c one.endCenter x = J₀ := by
  have hn : ‖one.endCenter - (c : ℂ)‖ ≤ 2 * Real.exp (2 * π) := by
    rw [endCenter_one, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith [fourteen_le_two_mul_exp_two_pi, hc.1, hc.2]
  rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀
      (re_endCoord_zero_le_half hL (by norm_num [endCenter_one])),
    exchangeAlmostComplex_of_norm_le h₀ hn, pairOfPantsAlmostComplex_endCenter]

/-- **The family is `J_1(t)` far out on the remaining input end.** For `L ≥ 0` and `0 ≤ c ≤ 1`, if
`J_1` has period one in `t`, then on the part `s ≥ 2` of the input end at `1` the member `c` of the
family at the point with end coordinates `z = s + i t` is `J_1 t x`. -/
theorem cappedExchangeAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀)
    (hJp : Periodic (J one) 1) (hL : 0 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 2 ≤ z.re)
    (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c (one.cylindricalEndLift z) x = J one z.im x := by
  have hw : (zero.endCoord (one.cylindricalEndLift z)).re ≤ L / 2 := by
    have h := endSign_mul_re_endCoord_nonpos (q := one) (r := zero) (by decide)
      (w := one.cylindricalEndLift z)
      (by rw [endSign_eq_one (by decide), one_mul, re_endCoord_cylindricalEndLift]; linarith)
    rw [endSign_eq_one (by decide), one_mul] at h
    linarith
  rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ hw,
    exchangeAlmostComplex_cylindricalEndLift h₀ (by decide) hJp hc₀ hc₁ hz]

/-- **The family is `J_∞(t)` far out on the output end.** For `L ≥ 2` and `0 ≤ c ≤ 1`, if `J_∞` has
period one in `t`, then on the part `s ≤ -2` of the output end recentred at `c`, the member `c` of
the family at the point `c + φ_∞(z)` with end coordinates `z = s + i t` is `J_∞ t x`. -/
theorem cappedExchangeAlmostComplex_add_cylindricalEndLift_inf (h₀ : ω.Compatible J₀)
    (hJp : Periodic (J inf) 1) (hL : 2 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : z.re ≤ -2)
    (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c (c + inf.cylindricalEndLift z) x = J inf z.im x := by
  -- The end lift at `∞` stays at distance at least `2` from `0` on the part `s ≤ 0`.
  have hφ : 2 ≤ ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    rw [h]
    nlinarith [Real.one_le_exp (by nlinarith [Real.pi_pos] : 0 ≤ -(2 * π * z.re))]
  have hn : 1 / 2 ≤ ‖(c : ℂ) + inf.cylindricalEndLift z‖ := by
    have h := norm_sub_norm_le (inf.cylindricalEndLift z) (-(c : ℂ))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc₀, add_comm] at h
    linarith
  rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ (re_endCoord_zero_le_half hL hn),
    exchangeAlmostComplex_add_cylindricalEndLift_inf h₀ hJp c hz]

end Algebraic

section Smooth

/-! ### Smoothness -/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The family is smooth.** For families `J q t x` of `ω`-tame structures which have period one
in `t` and are `C^n` on `ℝ × M`, and a neck length `L > 4`, the input-exchange family capped at `0`
is `C^n` jointly in the parameter `c`, the point of the capped domain `ℂ ∖ {1}` and the point `x`,
at every parameter `-1 < c < 2`. On the disc `‖w‖ < 1` it is the capping structure at `0`, and off
the disc `‖w‖ ≤ 1/2` it is the input-exchange family. -/
theorem contMDiffAt_cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap))
    {L : ℝ} (hL : 4 < L) {c : ℝ} (hc : c ∈ Ioo (-1) 2) {w : ℂ} (hw : w ≠ 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × (ℂ × M) =>
        (cappedExchangeAlmostComplex h₀ J hJ L p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap)
      (c, (w, x)) := by
  have hnorm : Continuous fun p : ℝ × (ℂ × M) => ‖p.2.1‖ :=
    (continuous_fst.comp continuous_snd).norm
  have hpar : ∀ᶠ p : ℝ × (ℂ × M) in 𝓝 (c, (w, x)), p.1 ∈ Ioo (-1) 2 :=
    continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hc)
  rcases lt_or_ge ‖w‖ 1 with hlt | hge
  · -- On the disc `‖w‖ < 1` the family is the capping structure at `0`, which does not depend on
    -- the parameter.
    have hw' : w = zero.endCenter ∨ w ≠ 0 ∧ w ≠ 1 := by
      rcases eq_or_ne w 0 with rfl | hw₀
      · exact Or.inl endCenter_zero.symm
      · exact Or.inr ⟨hw₀, hw⟩
    have hcap := contMDiffAt_plumbedAlmostComplex_update_inf h₀
      (hJa := tames_update_inf h₀.tames (hJ zero)) (hJb := hJ) (by decide) hJp hJs hL hw' x
    refine (hcap.comp (c, (w, x)) (contMDiffAt_const.prodMk contMDiffAt_snd)).congr_of_eventuallyEq
      ?_
    filter_upwards [hnorm.continuousAt.eventually (gt_mem_nhds hlt), hpar] with p hp hpc
    simp only [comp_apply, cappedExchangeAlmostComplex_of_norm_le h₀ (Ioo_subset_Icc_self hpc)
      hp.le]
  · -- Off the disc `‖w‖ ≤ 1/2` the family is the input-exchange family.
    have hw₀ : w ≠ 0 := by
      rintro rfl
      norm_num at hge
    have hex := contMDiffAt_exchangeAlmostComplex h₀ (hJ := hJ) hJp hJs hc ⟨w, hw₀, hw⟩ x
    refine hex.congr_of_eventuallyEq ?_
    filter_upwards [hnorm.continuousAt.eventually (lt_mem_nhds (by linarith : 1 / 2 < ‖w‖))]
      with p hp
    rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ (re_endCoord_zero_le_half (by linarith)
      hp.le)]

end Smooth

end TauCeti.Floer
