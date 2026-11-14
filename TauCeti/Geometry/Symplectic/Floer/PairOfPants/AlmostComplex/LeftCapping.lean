/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping

/-!
# Almost complex structures along the input-exchange family capped at `0`

The unit of the pair-of-pants product is a unit on either side. Gluing a negative PSS plane into
the input at `1` of the pair of pants `ℂ ∖ {0, 1}` gives a cylinder in the end coordinates of the
remaining input, but gluing it into the input at `0` leaves `ℂ ∖ {1}`, whose remaining input end is
centred at `1` while the output end is centred at `0`. The Hamiltonian perturbations
`TauCeti.Floer.cappedExchangePerturbation H L c`, `0 ≤ c ≤ 1`, join this capping family at `0` to
the capping family at `1` of the pair of pants with exchanged inputs, by moving the output end:
they plumb the negative plane with Hamiltonian `H_0` into the end at `0` of the input-exchange
family. This file constructs the matching family of domain-dependent almost complex structures.

Fix an `ω`-compatible base structure `J₀` and families `J_q(t, x)` of `ω`-tame structures on the
three ends. The *capped input part* is the structure of the pair of pants whose output structure is
replaced by `J₀`, with the negative plane of end structure `J_0` plumbed into its end at `0` along
a neck of length `L`, as in `TauCeti.Floer.plumbedAlmostComplex_update_inf_eq`. The *plane part* is
the negative plane structure of `J_∞` (`TauCeti.Floer.negativePlaneAlmostComplex`). The family
`TauCeti.Floer.cappedExchangeAlmostComplex h₀ J hJ L c` is the capped input part on the disc
`‖w - c‖ ≤ 2 exp (2π)` and the plane part translated by `c` off it, just as the perturbation is the
capped input datum plus the translated plane datum. Every member is `ω`-tame, and `ω`-compatible
when the end structures are.

Away from the capped disc the family is the input-exchange family of almost complex structures
(`TauCeti.Floer.cappedExchangeAlmostComplex_of_re_endCoord_le`), and near the capped puncture it is
the capping structure at `0` (`TauCeti.Floer.cappedExchangeAlmostComplex_of_lt_re_endCoord`). The
main results are:

* `TauCeti.Floer.cappedExchangeAlmostComplex_zero`: at `c = 0` the family is the capping structure
  at `0` of the pair of pants with end structures `J`.
* `TauCeti.Floer.cappedExchangeAlmostComplex_one`: at `c = 1`, if `J_∞` has period one, the member
  at `w` is the capping structure at `1` of the pair of pants with exchanged end structures
  (`TauCeti.Floer.exchangeEndData`) at `1 - w`. The exchange `w ↦ 1 - w` carries the plumbing at
  `0` to the plumbing at `1`.
* `TauCeti.Floer.cappedExchangeAlmostComplex_cylindricalEndLift` and
  `TauCeti.Floer.cappedExchangeAlmostComplex_add_cylindricalEndLift_inf`: every member with
  `0 ≤ c ≤ 1` is `J_1(t, x)` far out on the remaining input end, in the end lift `φ_1`, if `J_1`
  has period one, and every member is `J_∞(t, x)` far out on the output end recentred at `c`, in
  the end lift `c + φ_∞`, if `J_∞` has period one. These are the end coordinates in which the
  members of `TauCeti.Floer.cappedExchangePerturbation` are `H_q(t) dt`.
* `TauCeti.Floer.cappedExchangeAlmostComplex_eq_of_norm_le`: for `L > 2` and `0 ≤ c ≤ 1` every
  member is `J₀` on the disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture `0`, where
  the perturbation vanishes as well (`TauCeti.Floer.cappedExchangePerturbation_eq_zero`).
* `TauCeti.Floer.contMDiffAt_cappedExchangeAlmostComplex`: for period-one `C^n` end families, the
  family is `C^n` jointly in the neck length `L > 4`, the parameter `-1 < c < 2`, the point of the
  capped domain `ℂ ∖ {1}` and the point `x`.
* `TauCeti.Floer.isComplexLinearMap_perturbedFDeriv_cappedExchange_one`: for a symplectic vector
  space target, if `u` solves the Floer equation at `σ(z)` for the exchanged data capped at `1`,
  then `u ∘ σ` solves it at `z` for the member `c = 1` of the family, perturbation and almost
  complex structure together, where `σ(w) = 1 - w`.

Together with `TauCeti.Floer.cappedExchangePerturbation_zero` and
`TauCeti.Floer.cappedExchangePerturbation_one`, the members `c = 0` and `c = 1` of the family of
Floer data `(K_c, J_c)` are therefore the problem capped at `0` and the exchanged problem capped at
`1`.

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
  {L c : ℝ}

/-- **The input-exchange family of almost complex structures capped at `0`.** For a neck length
`L` and `c ∈ ℝ`, relative to an `ω`-compatible base structure `J₀`, this is, on the disc
`‖w - c‖ ≤ 2 exp (2π)`, the structure obtained by plumbing the negative plane with end structure
`J_0` into the end at `0` of the pair of pants with the input structures of `J` and output
structure `J₀`, and off that disc the negative plane structure of the output structure `J_∞`
translated by `c`. Its output end is the end at `∞` recentred at `c`, as for the perturbations
`TauCeti.Floer.cappedExchangePerturbation`. -/
def cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀)
    (J : Puncture → ℝ → M → AlmostComplexStructure V) (hJ : ∀ q t x, ω.Tames (J q t x))
    (L c : ℝ) (w : ℂ) (x : M) : AlmostComplexStructure V :=
  if ‖w - c‖ ≤ 2 * Real.exp (2 * π) then
    plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero))
      (update J inf fun _ _ => J₀) (tames_update_inf h₀.tames (hJ zero))
      (tames_update_inf_base h₀.tames hJ) zero L w x
  else negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (w - c) x

/-- On the disc `‖w - c‖ ≤ 2 exp (2π)` the member `c` of the family is the capped input part. -/
theorem cappedExchangeAlmostComplex_of_norm_le (h₀ : ω.Compatible J₀) {w : ℂ}
    (hw : ‖w - c‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero))
        (update J inf fun _ _ => J₀) (tames_update_inf h₀.tames (hJ zero))
        (tames_update_inf_base h₀.tames hJ) zero L w x := by
  simp only [cappedExchangeAlmostComplex, hw, ↓reduceIte]

/-- Off the disc `‖w - c‖ ≤ 2 exp (2π)` the member `c` of the family is the negative plane
structure of the output structure, translated by `c`. -/
theorem cappedExchangeAlmostComplex_of_lt_norm (h₀ : ω.Compatible J₀) {w : ℂ}
    (hw : 2 * Real.exp (2 * π) < ‖w - c‖) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x =
      negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (w - c) x := by
  simp only [cappedExchangeAlmostComplex, hw.not_ge, ↓reduceIte]

/-- Every member of the family is tamed by `ω`. -/
theorem tames_cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀) (L c : ℝ) (w : ℂ) (x : M) :
    ω.Tames (cappedExchangeAlmostComplex h₀ J hJ L c w x) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  exacts [tames_plumbedAlmostComplex h₀ h₀ w x, tames_negativePlaneAlmostComplex h₀ _ x]

/-- Every member of the family is `ω`-compatible when the end structures are. -/
theorem compatible_cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (L c : ℝ) (w : ℂ) (x : M) :
    ω.Compatible (cappedExchangeAlmostComplex h₀ J hJ L c w x) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  · refine compatible_plumbedAlmostComplex h₀ h₀ ?_ ?_ w x
    · intro r t y
      rcases eq_or_ne r inf with rfl | hr
      · simpa using hJc zero t y
      · simpa [update_of_ne hr] using h₀
    · intro r t y
      rcases eq_or_ne r inf with rfl | hr
      · simpa using h₀
      · simpa [update_of_ne hr] using hJc r t y
  · exact compatible_negativePlaneAlmostComplex h₀ (hJc inf) _ x

/-- **Away from the capped disc the family is the input-exchange family.** Where the longitudinal
coordinate of the end at `0` is at most `L / 2`, the member `c` of the capped family is the member
`c` of the input-exchange family of almost complex structures. -/
theorem cappedExchangeAlmostComplex_of_re_endCoord_le (h₀ : ω.Compatible J₀) {w : ℂ}
    (hw : (zero.endCoord w).re ≤ L / 2) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x = exchangeAlmostComplex h₀ J hJ c w x := by
  rcases le_or_gt ‖w - c‖ (2 * Real.exp (2 * π)) with hn | hn
  · rw [cappedExchangeAlmostComplex_of_norm_le h₀ hn, exchangeAlmostComplex_of_norm_le h₀ hn,
      plumbedAlmostComplex_def, ite_eq_right (not_lt.2 hw)]
  · rw [cappedExchangeAlmostComplex_of_lt_norm h₀ hn, exchangeAlmostComplex_of_lt_norm h₀ hn]

/-- **Near the capped puncture the family is the capping structure at `0`.** For `L ≥ 2` and
`0 ≤ c ≤ 1`, where the longitudinal coordinate of the end at `0` exceeds `L / 2`, the member `c` of
the family is the structure obtained by plumbing the negative plane with end structure `J_0` into
the end at `0` of the pair of pants with end structures `J`. -/
theorem cappedExchangeAlmostComplex_of_lt_re_endCoord (h₀ : ω.Compatible J₀) (hL : 2 ≤ L)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {w : ℂ} (hw : L / 2 < (zero.endCoord w).re) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c w x =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero)) J
        (tames_update_inf h₀.tames (hJ zero)) hJ zero L w x := by
  have hw' : ‖w‖ ≤ 1 / 2 := by
    by_contra! h
    linarith [re_endCoord_zero_le_div_two hL h.le]
  have hn : ‖w - c‖ ≤ 2 * Real.exp (2 * π) := by
    have h := norm_sub_le w (c : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at h
    linarith [three_lt_two_mul_exp_two_pi]
  rw [cappedExchangeAlmostComplex_of_norm_le h₀ hn, plumbedAlmostComplex_def,
    plumbedAlmostComplex_def, ite_eq_left hw, ite_eq_left hw]

/-- **The start of the family is the capping structure at `0`.** For `L ≥ 2`, the member `c = 0` of
the family is the structure obtained by plumbing the negative plane with end structure `J_0` into
the end at `0` of the pair of pants with end structures `J`. -/
@[simp]
theorem cappedExchangeAlmostComplex_zero (h₀ : ω.Compatible J₀) (hL : 2 ≤ L) :
    cappedExchangeAlmostComplex h₀ J hJ L 0 =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero)) J
        (tames_update_inf h₀.tames (hJ zero)) hJ zero L := by
  funext w x
  rcases le_or_gt (zero.endCoord w).re (L / 2) with hw | hw
  · rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ hw, exchangeAlmostComplex_zero,
      plumbedAlmostComplex_def, ite_eq_right (not_lt.2 hw)]
  · exact cappedExchangeAlmostComplex_of_lt_re_endCoord h₀ hL le_rfl zero_le_one hw x

/-- **The end of the family is the exchanged capping structure at `1`.** If the output structure
`J_∞` has period one in `t` and `L ≥ 2`, the member `c = 1` of the family at `w` is the structure
obtained by plumbing the negative plane with end structure `J_0` into the end at `1` of the pair of
pants with exchanged end structures (`TauCeti.Floer.exchangeEndData`), at `1 - w`. -/
theorem cappedExchangeAlmostComplex_one (h₀ : ω.Compatible J₀) (hJp : Periodic (J inf) 1)
    (hJ' : ∀ q t x, ω.Tames (exchangeEndData J q t x)) (hL : 2 ≤ L) (w : ℂ) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L 1 w x =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero)) (exchangeEndData J)
        (tames_update_inf h₀.tames (hJ zero)) hJ' one L (1 - w) x := by
  have hre : (one.endCoord (1 - w)).re = (zero.endCoord w).re := by rw [endCoord_one_one_sub]
  rcases le_or_gt (zero.endCoord w).re (L / 2) with hw | hw
  · rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ hw, exchangeAlmostComplex_one h₀ hJp hJ',
      plumbedAlmostComplex_def, ite_eq_right (by rw [hre]; exact not_lt.2 hw)]
  · -- In plumbing coordinates the exchange is the identity.
    have hpt : (1 - w - one.endCenter) / one.plumbingFactor L =
        (w - zero.endCenter) / zero.plumbingFactor L := by
      rw [plumbingFactor_one, endCenter_one, endCenter_zero, div_neg, ← neg_div]
      ring_nf
    rw [cappedExchangeAlmostComplex_of_lt_re_endCoord h₀ hL zero_le_one le_rfl hw,
      plumbedAlmostComplex_def, plumbedAlmostComplex_def, ite_eq_left hw,
      ite_eq_left (by rwa [hre]), hpt]

/-- **The family is `J_1(t)` far out on the remaining input end.** For `0 ≤ c ≤ 1` and `L ≥ 0`, if
`J_1` has period one in `t`, then on the part `s ≥ 2` of the input end at `1` the member `c` of the
family at the point with end coordinates `z = s + i t` is `J_1(t, x)`. -/
theorem cappedExchangeAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀)
    (hJp : Periodic (J one) 1) (hL : 0 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ}
    (hz : 2 ≤ z.re) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c (one.cylindricalEndLift z) x = J one z.im x := by
  have hw : (zero.endCoord (one.cylindricalEndLift z)).re ≤ L / 2 := by
    have h := endSign_mul_re_endCoord_nonpos (q := one) (r := zero) (by decide)
      (w := one.cylindricalEndLift z)
      (by rw [endSign_eq_one (by decide), one_mul, re_endCoord_cylindricalEndLift]; linarith)
    rw [endSign_eq_one (by decide), one_mul] at h
    linarith
  rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ hw,
    exchangeAlmostComplex_cylindricalEndLift h₀ (by decide) hJp hc₀ hc₁ hz]

/-- **The family is `J_∞(t)` far out on the output end.** If `J_∞` has period one in `t`, then on
the part `s ≤ -2` of the output end recentred at `c`, the member `c` of the family at the point
`c + φ_∞(z)` with end coordinates `z = s + i t` is `J_∞(t, x)`. -/
theorem cappedExchangeAlmostComplex_add_cylindricalEndLift_inf (h₀ : ω.Compatible J₀)
    (hJp : Periodic (J inf) 1) (L c : ℝ) {z : ℂ} (hz : z.re ≤ -2) (x : M) :
    cappedExchangeAlmostComplex h₀ J hJ L c (c + inf.cylindricalEndLift z) x = J inf z.im x := by
  have hφ : 2 * Real.exp (2 * π) < ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    rw [h]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])) two_pos
  rw [cappedExchangeAlmostComplex_of_lt_norm h₀ (by rwa [add_sub_cancel_left]),
    add_sub_cancel_left, negativePlaneAlmostComplex_cylindricalEndLift h₀ hJp hz]

/-- **The capped disc.** For `L > 2` and `0 ≤ c ≤ 1`, every member of the family is `J₀` on the
disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture `0`, the image under the plumbing
map of the pole disc of the plane. -/
theorem cappedExchangeAlmostComplex_eq_of_norm_le (h₀ : ω.Compatible J₀) (hL : 2 < L)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {w : ℂ} (hw : ‖w‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2)
    (x : M) : cappedExchangeAlmostComplex h₀ J hJ L c w x = J₀ := by
  have hw' : ‖w - zero.endCenter‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2 := by
    rwa [endCenter_zero, sub_zero]
  rcases eq_or_ne w zero.endCenter with rfl | hc
  · -- At the capped puncture itself the structure is that of the receiving pair of pants.
    rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ (by rw [re_endCoord_endCenter]; linarith),
      exchangeAlmostComplex_of_norm_le h₀ (by
        rw [endCenter_zero, zero_sub, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc₀]
        linarith [three_lt_two_mul_exp_two_pi]),
      pairOfPantsAlmostComplex_endCenter]
  · rw [cappedExchangeAlmostComplex_of_lt_re_endCoord h₀ hL.le hc₀ hc₁
      (by linarith [le_re_endCoord_of_norm_sub_endCenter_le (by decide) hc hw'])]
    exact plumbedAlmostComplex_update_inf_eq h₀ (by decide) hL hw' x

/-- The capped input part inserts the negative plane with end structure `J_0`, which is also the
structure at `0` of the receiving family `update J ∞ J₀`. -/
private theorem plumbedAlmostComplex_update_inf_update_zero (h₀ : ω.Compatible J₀)
    (hA : ∀ r t x, ω.Tames
      (update (fun _ _ _ => J₀) inf ((update J inf fun _ _ => J₀) zero) r t x))
    (w : ℂ) (x : M) :
    plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf ((update J inf fun _ _ => J₀) zero))
        (update J inf fun _ _ => J₀) hA (tames_update_inf_base h₀.tames hJ) zero L w x =
      plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero))
        (update J inf fun _ _ => J₀) (tames_update_inf h₀.tames (hJ zero))
        (tames_update_inf_base h₀.tames hJ) zero L w x := by
  simp only [update_of_ne (show zero ≠ inf by decide)]

end Algebraic

section Smooth

/-! ### Smoothness -/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] {L : ℝ}

/-- **The family is smooth.** For families `J q t x` of `ω`-tame structures which have period one
in `t` and are `C^n` on `ℝ × M`, the input-exchange family capped at `0` is `C^n` jointly in the
neck length `L`, the parameter `c`, the point of the capped domain `ℂ ∖ {1}` and the point `x`, at
every neck length `L > 4` and parameter `-1 < c < 2`. Near the disc `‖w‖ ≤ 1/2` it is the capping
structure at `0`, which does not depend on `c`, and off the disc `‖w‖ ≤ exp (-2π) / 2` it is the
input-exchange family, which does not depend on `L`. -/
theorem contMDiffAt_cappedExchangeAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hL : 4 < L) {c : ℝ} (hc : c ∈ Ioo (-1) 2) {w : ℂ} (hw : w ≠ 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I))) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × (ℝ × (ℂ × M)) => (cappedExchangeAlmostComplex h₀ J hJ p.1 p.2.1 p.2.2.1
        p.2.2.2).toLinearMap.toContinuousLinearMap)
      (L, (c, (w, x))) := by
  have hnorm : Continuous fun p : ℝ × (ℝ × (ℂ × M)) => ‖p.2.2.1‖ :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).norm
  rcases lt_or_ge ‖w‖ (1 / 2) with hlt | hge
  · -- Near the disc `‖w‖ < 1/2` the family is the capped input part, which does not depend on the
    -- parameter.
    have hin := contMDiffAt_plumbedAlmostComplex_update_inf (Jb := update J inf fun _ _ => J₀)
      (hJa := tames_update_inf h₀.tames (tames_update_inf_base h₀.tames hJ zero))
      (hJb := tames_update_inf_base h₀.tames hJ) h₀
      (by decide)
      ((forall_update_iff J fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hJp q⟩)
      ((forall_update_iff J fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
        (fun p : ℝ × M => (f p.1 p.2).toLinearMap.toContinuousLinearMap)).2
        ⟨contMDiff_const, fun q _ => hJs q⟩)
      hL (w := w) (by
        rcases eq_or_ne w 0 with rfl | h₀'
        · exact Or.inl endCenter_zero.symm
        · exact Or.inr ⟨h₀', hw⟩) x
    refine (hin.comp (L, (c, (w, x)))
      (contMDiffAt_fst.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))).congr_of_eventuallyEq ?_
    filter_upwards [hnorm.continuousAt.eventually (gt_mem_nhds hlt),
      continuous_snd.fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hc)] with p hp hpc
    have hn : ‖p.2.2.1 - p.2.1‖ ≤ 2 * Real.exp (2 * π) := by
      have h := norm_sub_le p.2.2.1 (p.2.1 : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      have : |p.2.1| ≤ 2 := abs_le.2 ⟨by linarith [hpc.1], hpc.2.le⟩
      linarith [three_lt_two_mul_exp_two_pi]
    simp only [Function.comp_apply, cappedExchangeAlmostComplex_of_norm_le h₀ hn]
    rw [plumbedAlmostComplex_update_inf_update_zero (hJ := hJ)]
  · -- Off the disc `‖w‖ ≤ exp (-2π) / 2` the family is the input-exchange family.
    have hw₀ : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hge
      linarith
    have hex := contMDiffAt_exchangeAlmostComplex h₀ (hJ := hJ) hJp hJs hc ⟨w, hw₀, hw⟩ x
    refine (hex.comp (L, (c, (w, x))) contMDiffAt_snd).congr_of_eventuallyEq ?_
    have hsmall : Real.exp (-(2 * π)) / 2 < 1 / 2 := by
      have : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
      linarith
    filter_upwards [hnorm.continuousAt.eventually (lt_mem_nhds (hsmall.trans_le hge)),
      continuous_fst.continuousAt.eventually (lt_mem_nhds (show 2 < L by linarith))] with p hp hpL
    rw [Function.comp_apply, cappedExchangeAlmostComplex_of_re_endCoord_le h₀
      ((re_endCoord_zero_le_one hp.le).trans (by linarith))]

end Smooth

section Solutions

/-! ### Solutions at the end of the family -/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {H : Puncture → ℝ → V → ℝ}
  {J : Puncture → ℝ → V → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)} {L : ℝ}

/-- **Solutions at the end of the family.** Let `σ(z) = (1, 0) - z` be the exchange `w ↦ 1 - w` in
the real coordinates `ℝ × ℝ ≃ ℂ`, let the Hamiltonians `H_q` have period one and be `C¹`, let the
output structure `J_∞` have period one, and let `L > 4`. If `u` is differentiable at `σ(z)`, where
`σ(z)` lies in the domain `ℂ ∖ {0}` of the exchanged problem capped at `1`, and solves the Floer
equation there for the data obtained by plumbing the negative plane with Hamiltonian `H_0` and end
structure `J_0` into the end at `1` of the pair of pants with exchanged data, then `u ∘ σ` solves
the Floer equation at `z` for the member `c = 1` of the input-exchange family capped at `0`, the
perturbation `TauCeti.Floer.cappedExchangePerturbation H L 1` with the almost complex structure
`TauCeti.Floer.cappedExchangeAlmostComplex h₀ J hJ L 1` at `u(σ(z))`. -/
theorem isComplexLinearMap_perturbedFDeriv_cappedExchange_one (h₀ : ω.Compatible J₀)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hJp : Periodic (J inf) 1) (hJ' : ∀ q t x, ω.Tames (exchangeEndData J q t x)) (hL : 4 < L)
    {u : ℝ × ℝ → V} {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ 1)
    (hu : DifferentiableAt ℝ u ((1, 0) - z))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (J zero)) (exchangeEndData J)
        (tames_update_inf h₀.tames (hJ zero)) hJ' one L
        (Complex.equivRealProdCLM.symm ((1, 0) - z)) (u ((1, 0) - z)))
      (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation (Pi.single inf (H zero)) (exchangeEndData H) one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (H zero)) (exchangeEndData H) one L
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        u ((1, 0) - z) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (cappedExchangeAlmostComplex h₀ J hJ L 1 (Complex.equivRealProdCLM.symm z)
        (u ((1, 0) - z)))
      (ω.perturbedFDeriv
        (fun z x ↦ cappedExchangePerturbation H L 1 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L 1 (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        (u ∘ fun z ↦ (1, 0) - z) z : ℝ × ℝ →ₗ[ℝ] V) := by
  set e := Complex.equivRealProdCLM.symm
  have hσ : e ((1, 0) - z) = 1 - e z := by
    apply Complex.ext <;> simp [e]
  -- The structure at `z` is the exchanged capping structure at `σ(z)`.
  rw [cappedExchangeAlmostComplex_one h₀ hJp hJ' (by linarith), ← hσ]
  -- The perturbation is the pullback along `σ` of the exchanged capping perturbation.
  have hpull (v : ℝ × ℝ) : (fun z x ↦ cappedExchangePerturbation H L 1 (e z) x (e v)) =
      perturbationPullback (fun z ↦ (1, 0) - z)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (H zero)) (exchangeEndData H) one L
          (e z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (H zero)) (exchangeEndData H) one L
          (e z) x Complex.I) v := by
    funext z' x
    rw [perturbationPullback_plumbedPerturbation_exchangeEndData (hH inf) (by linarith)]
  rw [← equivRealProdCLM_symm_stdComplexLineReal, ← equivRealProdCLM_symm_stdComplexLineImag,
    hpull, hpull]
  -- The exchanged capping perturbation is differentiable in the target point at `σ(z)`, which is
  -- the capped puncture `1` or a point of `ℂ ∖ {0, 1}`.
  have hS : e ((1, 0) - z) = one.endCenter ∨ e ((1, 0) - z) ≠ 0 ∧ e ((1, 0) - z) ≠ 1 := by
    rw [hσ, endCenter_one]
    by_cases h1 : 1 - e z = 1
    · exact Or.inl h1
    · exact Or.inr ⟨fun h0 => hz (by linear_combination -h0), h1⟩
  have hK (v : ℂ) : DifferentiableAt ℝ
      (fun x ↦ plumbedPerturbation (Pi.single inf (H zero)) (exchangeEndData H) one L
        (e ((1, 0) - z)) x v) (u ((1, 0) - z)) := by
    have hd := (contDiffAt_uncurry_plumbedPerturbation_single_inf (q := one) (by decide)
      (periodic_exchangeEndData hH) (contDiff_uncurry_exchangeEndData hHs) hL hS
      (u ((1, 0) - z)) v).differentiableAt one_ne_zero
    rw [exchangeEndData_one] at hd
    exact hd.comp _ ((differentiableAt_const _).prodMk differentiableAt_id)
  -- The exchange is holomorphic: its derivative is `-1`.
  have hφ : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ (1, 0) - z) z :=
    (differentiableAt_const _).sub differentiableAt_id
  have hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (fun z : ℝ × ℝ ↦ (1, 0) - z) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
    rw [fderiv_const_sub, fderiv_fun_id]
    simp
  exact ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback hφ hu (hK 1) (hK Complex.I)
    hφJ h

end Solutions

end TauCeti.Floer
