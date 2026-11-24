/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.LeftCapping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping

/-!
# Almost complex structures along the input-exchange family capped at `0` in a manifold

The left unit property of the pair-of-pants product is proved with the family of Floer data that
caps the input at `0` of the pair of pants `S = ℂ ∖ {0, 1}` by a negative PSS plane and moves the
output end from `0` to `1`. Its perturbations `TauCeti.Floer.cappedExchangePerturbation H L c` are
defined for any target, and `TauCeti.Floer.cappedExchangeAlmostComplex` constructs its almost
complex structures on a fixed symplectic vector space. This file constructs them on the tangent
bundle of a manifold `M` with a nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible smooth almost complex structure `J₀` and smooth `σ`-tame structures `J q t`
for the ends `q` and times `t`. For a neck length `L`, `c ∈ ℝ` and `w ∈ ℂ`, the smooth almost
complex structure `TauCeti.SmoothTwoForm.Compatible.cappedExchangeAlmostComplex h₀ J hJ L c w` is
the negative plane structure `TauCeti.SmoothTwoForm.Compatible.negativePlaneAlmostComplex` of `J 0`
in the plumbing coordinate on the half-neck `Re z > L/2` of the end at `0`, and the member `c` of
the input-exchange family `TauCeti.SmoothTwoForm.Compatible.exchangeAlmostComplex` elsewhere. On the
tangent space at every point `x` it is the linear structure of `J₀ x` and the end structures
`J q t x`
(`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_cappedExchangeAlmostComplex`), so its
properties follow fiberwise from the linear construction:

* it is tame, and compatible when the end structures are;
* for `L > 2`, at `c = 0` it is the capping structure at `0`,
  `TauCeti.SmoothTwoForm.Compatible.cappingAlmostComplex J hJ zero L`
  (`TauCeti.SmoothTwoForm.Compatible.cappedExchangeAlmostComplex_zero`), and at `c = 1`, if `J ∞`
  has period one, its value at `w` is the capping structure at `1` of the exchanged end structures
  `TauCeti.Floer.exchangeEndData J` at `1 - w`
  (`TauCeti.SmoothTwoForm.Compatible.cappedExchangeAlmostComplex_one`);
* for `L > 2` and `-1 ≤ c ≤ 2`, on the disc `‖w‖ ≤ 1` it is the capping structure at `0`
  (`TauCeti.SmoothTwoForm.Compatible.cappedExchangeAlmostComplex_of_norm_le`), so it is `J₀` on
  the image `‖w‖ ≤ exp (-2π(L - 1)) / 2` of the pole disc of the plane, and it is `J₀` at the three
  punctures of the plumbed sphere `ℂ ∖ {0, 1, ψ_0(1)}`
  (`TauCeti.SmoothTwoForm.Compatible.cappedExchangeAlmostComplex_of_not`);
* for `0 ≤ c ≤ 1`, `L ≥ 2` and period-one end structures, it is `J 1 t` far out on the input end
  at `1` in the end lift `φ_1`, and `J ∞ t` far out on the output end in the end lift `c + φ_∞`,
  the end coordinates in which the perturbations of the family are `H_q(t) dt`;
* for `L > 4` and period-one end structures which are jointly `C^n` on `ℝ × M`, it is jointly
  `C^n` along `C^n` families of parameters `-1 < c < 2`, points of the capped domain `ℂ ∖ {1}` and
  points of `M` (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappedExchangeAlmostComplex`).

Finally, for `L > 4` the member `c = 1` of the family of Floer data is the pullback along
`w ↦ 1 - w` of the data of the capping family at `1` with exchanged Hamiltonians and end
structures: if `u` solves the Floer equation for the latter at `1 - w`, then `u (1 - ·)` solves it
at `w` for the member `c = 1`
(`TauCeti.SmoothTwoForm.Compatible.isComplexLinearMap_perturbedMFDeriv_cappedExchange_one`).
This is the naturality of the Floer equation under the exchange,
`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_one_sub`, applied to
`TauCeti.Floer.cappedExchangePerturbation_one`.

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

open Classical in
/-- **The input-exchange family capped at `0` on a manifold.** For a neck length `L` and `c ∈ ℝ`,
relative to a `σ`-compatible base structure `J₀`, this is the negative plane structure of the
input structures `J 0` in the plumbing coordinate `(w - c_0) / ψ'` on the half-neck `Re z > L/2`
of the end at `0`, and the member `c` of the input-exchange family elsewhere. -/
def cappedExchangeAlmostComplex (L c : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  if L / 2 < (zero.endCoord w).re then
    h₀.negativePlaneAlmostComplex (J zero) (hJ zero)
      ((w - zero.endCenter) / zero.plumbingFactor L)
  else h₀.exchangeAlmostComplex J hJ c w

variable {L c : ℝ} {w : ℂ}

/-- On the half-neck `Re z > L/2` of the end at `0`, every member of the family is the negative
plane structure of `J 0` in the plumbing coordinate. -/
theorem cappedExchangeAlmostComplex_of_lt_re_endCoord (hw : L / 2 < (zero.endCoord w).re) :
    h₀.cappedExchangeAlmostComplex J hJ L c w =
      h₀.negativePlaneAlmostComplex (J zero) (hJ zero)
        ((w - zero.endCenter) / zero.plumbingFactor L) :=
  ite_eq_left hw

/-- Off the half-neck `Re z > L/2` of the end at `0`, the member `c` of the family is the member
`c` of the input-exchange family. -/
theorem cappedExchangeAlmostComplex_of_re_endCoord_le (hw : (zero.endCoord w).re ≤ L / 2) :
    h₀.cappedExchangeAlmostComplex J hJ L c w = h₀.exchangeAlmostComplex J hJ c w :=
  ite_eq_right hw.not_gt

/-- **The fiberwise description.** On the tangent space at `x`, the member `c` of the family at
`w` is the linear structure `TauCeti.Floer.cappedExchangeAlmostComplex` of `J₀ x` and the end
structures `J q t x`. -/
theorem almostComplexStructureAt_cappedExchangeAlmostComplex (L c : ℝ) (w : ℂ) (x : M) :
    (h₀.cappedExchangeAlmostComplex J hJ L c w).almostComplexStructureAt x =
      Floer.cappedExchangeAlmostComplex (h₀.compatibleAt x)
        (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) L c w () := by
  rcases lt_or_ge (L / 2) (zero.endCoord w).re with hw | hw
  · rw [cappedExchangeAlmostComplex_of_lt_re_endCoord h₀ J hJ hw,
      Floer.cappedExchangeAlmostComplex_of_lt_re_endCoord _ hw,
      almostComplexStructureAt_negativePlaneAlmostComplex]
  · rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ J hJ hw,
      Floer.cappedExchangeAlmostComplex_of_re_endCoord_le _ hw,
      almostComplexStructureAt_exchangeAlmostComplex]

/-- Every member of the family is tamed by `σ`. -/
theorem tames_cappedExchangeAlmostComplex (L c : ℝ) (w : ℂ) :
    σ.Tames (h₀.cappedExchangeAlmostComplex J hJ L c w) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  exacts [tames_negativePlaneAlmostComplex h₀ _ _ _, tames_exchangeAlmostComplex h₀ J hJ c w]

/-- Every member of the family is `σ`-compatible when the end structures are. -/
theorem compatible_cappedExchangeAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t)) (L c : ℝ)
    (w : ℂ) : σ.Compatible (h₀.cappedExchangeAlmostComplex J hJ L c w) := by
  unfold cappedExchangeAlmostComplex
  split_ifs
  exacts [compatible_negativePlaneAlmostComplex h₀ _ _ (hJc zero) _,
    compatible_exchangeAlmostComplex h₀ J hJ hJc c w]

/-- **The capped disc.** For `L > 2` and `-1 ≤ c ≤ 2`, every member of the family is `J₀` on the
disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture `0`, the image under the plumbing
map of the pole disc of the plane. -/
theorem cappedExchangeAlmostComplex_eq_of_norm_le (hL : 2 < L) (hc : c ∈ Icc (-1) 2)
    (hw : ‖w‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) :
    h₀.cappedExchangeAlmostComplex J hJ L c w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex]
    exact Floer.cappedExchangeAlmostComplex_eq_of_norm_le _ hL hc hw ()

/-- **The uncapped input.** For `L ≥ 2` and `-1 ≤ c ≤ 2`, every member of the family is `J₀` at
the puncture `1`. -/
theorem cappedExchangeAlmostComplex_endCenter_one (hL : 2 ≤ L) (hc : c ∈ Icc (-1) 2) :
    h₀.cappedExchangeAlmostComplex J hJ L c one.endCenter = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex]
    exact Floer.cappedExchangeAlmostComplex_endCenter_one _ hL hc ()

/-- **The punctures of the capped sphere.** For `L > 2` and `-1 ≤ c ≤ 2`, every member of the
family is `J₀` at the three points `0`, `1` and `ψ_0(1)` missing from the plumbed four-punctured
sphere `ℂ ∖ {0, 1, ψ_0(1)}`, where the capping structure at `0` is `J₀` too: `0` and `ψ_0(1)` lie in
the image of the pole disc of the plane. -/
theorem cappedExchangeAlmostComplex_of_not (hL : 2 < L) (hc : c ∈ Icc (-1) 2)
    (hw : ¬((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1)) :
    h₀.cappedExchangeAlmostComplex J hJ L c w = J₀ := by
  simp only [not_and_or, not_not] at hw
  rcases hw with (rfl | rfl) | rfl
  · exact cappedExchangeAlmostComplex_eq_of_norm_le h₀ J hJ hL hc (by rw [norm_zero]; positivity)
  · simpa using cappedExchangeAlmostComplex_endCenter_one h₀ J hJ hL.le hc
  · exact cappedExchangeAlmostComplex_eq_of_norm_le h₀ J hJ hL hc
      (by simpa [endCenter_zero] using (norm_plumbingMap_one_sub_endCenter_lt zero L).le)

/-- **Near the capped puncture the family is the capping structure at `0`.** For `L > 2` and
`-1 ≤ c ≤ 2`, on the disc `‖w‖ ≤ 1` the member `c` of the family is the capping structure at `0`
of the pair of pants with end structures `J`. -/
theorem cappedExchangeAlmostComplex_of_norm_le (hL : 2 < L) (hc : c ∈ Icc (-1) 2)
    (hw : ‖w‖ ≤ 1) :
    h₀.cappedExchangeAlmostComplex J hJ L c w = h₀.cappingAlmostComplex J hJ zero L w := by
  by_cases hw' : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1
  · refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex,
      almostComplexStructureAt_cappingAlmostComplex h₀ J hJ hw',
      Floer.cappedExchangeAlmostComplex_of_norm_le _ hc hw]
  · rw [cappingAlmostComplex_of_not h₀ J hJ hw',
      cappedExchangeAlmostComplex_of_not h₀ J hJ hL hc hw']

/-- **The start of the family is the capping structure at `0`.** For `L > 2`, at `c = 0` the family
is the structure obtained by plumbing the negative plane with end structures `J 0` into the end at
`0` of the pair of pants with end structures `J`. -/
theorem cappedExchangeAlmostComplex_zero (hL : 2 < L) :
    h₀.cappedExchangeAlmostComplex J hJ L 0 = h₀.cappingAlmostComplex J hJ zero L := by
  funext w
  by_cases hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1
  · refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex,
      almostComplexStructureAt_cappingAlmostComplex h₀ J hJ hw,
      Floer.cappedExchangeAlmostComplex_zero]
  · rw [cappingAlmostComplex_of_not h₀ J hJ hw,
      cappedExchangeAlmostComplex_of_not h₀ J hJ hL ⟨by norm_num, by norm_num⟩ hw]

/-- **The end of the family is the exchanged capping structure at `1`.** For `L > 2`, if the
output structures `J ∞` have period one in `t`, the member `c = 1` of the family at `w` is, at
`1 - w`, the structure obtained by plumbing the negative plane with end structures `J 0` into the
end at `1` of the pair of pants with exchanged end structures (`TauCeti.Floer.exchangeEndData`:
`J 1` at `0`, `J 0` at `1` and `t ↦ J ∞ (t + 1/2)` at `∞`). -/
theorem cappedExchangeAlmostComplex_one (hL : 2 < L) (hJp : Periodic (J inf) 1)
    (hJ' : ∀ q t, σ.Tames (Floer.exchangeEndData J q t)) (w : ℂ) :
    h₀.cappedExchangeAlmostComplex J hJ L 1 w =
      h₀.cappingAlmostComplex (Floer.exchangeEndData J) hJ' one L (1 - w) := by
  by_cases hw : (1 - w ≠ 0 ∧ 1 - w ≠ 1) ∧ 1 - w ≠ one.plumbingMap L 1
  · refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex,
      Floer.cappedExchangeAlmostComplex_one _ (fun t => by simp only [hJp t])
        (h₀.tames_exchangeEndData_almostComplexStructureAt J hJ' x),
      almostComplexStructureAt_cappingAlmostComplex h₀ _ hJ' hw]
    -- The fiberwise exchanged end structures are the exchanged fiberwise end structures.
    have hex : (fun r t (_ : Unit) => (Floer.exchangeEndData J r t).almostComplexStructureAt x) =
        Floer.exchangeEndData (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x) := by
      funext r t u
      cases r <;> simp
    simp only [hex, Floer.exchangeEndData_one]
  · -- The punctures `0`, `1` and `ψ_1(1)` of the exchanged capped sphere are `1 - w` for the
    -- punctures `1`, `0` and `ψ_0(1)` of the capped sphere.
    have hw' : ¬((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) := by
      have hψ : 1 - one.plumbingMap L 1 = zero.plumbingMap L 1 := by
        simp only [plumbingMap_apply, plumbingFactor_one, endCenter_one, endCenter_zero]
        ring
      rintro ⟨⟨h₀, h₁⟩, h₂⟩
      refine hw ⟨⟨fun h => h₁ (by linear_combination -h), fun h => h₀ (by linear_combination -h)⟩,
        fun h => h₂ ?_⟩
      rw [← hψ, ← h, sub_sub_cancel]
    rw [cappingAlmostComplex_of_not h₀ _ hJ' hw,
      cappedExchangeAlmostComplex_of_not h₀ J hJ hL ⟨by norm_num, by norm_num⟩ hw']

/-- **The family is `J 1 t` far out on the remaining input end.** For `L ≥ 0` and `0 ≤ c ≤ 1`, if
`J 1` has period one in `t`, then on the part `s ≥ 2` of the input end at `1` the member `c` of the
family at the point with end coordinates `z = s + i t` is `J 1 t`. -/
theorem cappedExchangeAlmostComplex_cylindricalEndLift (hJp : Periodic (J one) 1) (hL : 0 ≤ L)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 2 ≤ z.re) :
    h₀.cappedExchangeAlmostComplex J hJ L c (one.cylindricalEndLift z) = J one z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex]
    exact Floer.cappedExchangeAlmostComplex_cylindricalEndLift _ (fun t => by simp only [hJp t])
      hL hc₀ hc₁ hz ()

/-- **The family is `J ∞ t` far out on the output end.** For `L ≥ 2` and `0 ≤ c ≤ 1`, if `J ∞` has
period one in `t`, then on the part `s ≤ -2` of the output end recentred at `c`, the member `c` of
the family at the point `c + φ_∞(z)` with end coordinates `z = s + i t` is `J ∞ t`. -/
theorem cappedExchangeAlmostComplex_add_cylindricalEndLift_inf (hJp : Periodic (J inf) 1)
    (hL : 2 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : z.re ≤ -2) :
    h₀.cappedExchangeAlmostComplex J hJ L c (c + inf.cylindricalEndLift z) = J inf z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedExchangeAlmostComplex]
    exact Floer.cappedExchangeAlmostComplex_add_cylindricalEndLift_inf _
      (fun t => by simp only [hJp t]) hL hc₀ hc₁ hz ()

/-! ### Smoothness -/

/-- **The family is smooth.** For end structures which have period one in `t` and are `C^n` on
`ℝ × M`, and a neck length `L > 4`, the input-exchange family capped at `0` is `C^n` as a section of
the tangent endomorphism bundle along `b`, read along `C^n` families of parameters `c`, domain
points `f` and target points `b`, provided `-1 < c < 2` and every domain point lies in the capped
domain `ℂ ∖ {1}`. The family may depend on further manifold parameters. On the disc `‖w‖ < 1` it is
the capping structure at `0`, and off the disc `‖w‖ ≤ 1/2` it is the input-exchange family. -/
theorem contMDiff_cappedExchangeAlmostComplex {F G N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {I' : ModelWithCorners ℝ F G} [TopologicalSpace N]
    [ChartedSpace G N] {n : ℕ∞ω} [ENat.LEInfty n] (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hL : 4 < L) {c : N → ℝ} {f : N → ℂ} {b : N → M} (hc : ContMDiff I' 𝓘(ℝ) n c)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) (hcy : ∀ y, c y ∈ Ioo (-1) 2)
    (hf₁ : ∀ y, f y ≠ 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.cappedExchangeAlmostComplex J hJ L (c y) (f y)).toEndomorphism (b y))) := by
  intro y₀
  rcases lt_or_ge ‖f y₀‖ 1 with hlt | hge
  · -- On the disc `‖w‖ < 1` the family is the capping structure at `0`. Restrict the family to
    -- the open set of parameters whose domain point lies there.
    let U : TopologicalSpace.Opens N :=
      ⟨{y | ‖f y‖ < 1}, isOpen_lt hf.continuous.norm continuous_const⟩
    have hU := contMDiff_cappingAlmostComplex h₀ J hJ hJp hJs (q := zero) (by decide)
      (ℓ := fun _ : U => L) contMDiff_const (hf.comp contMDiff_subtypeVal)
      (hb.comp contMDiff_subtypeVal) (fun _ => hL) fun y => by
        rcases eq_or_ne (f y) 0 with h | h
        · exact Or.inl (by rw [comp_apply, h, endCenter_zero])
        · exact Or.inr ⟨h, hf₁ y⟩
    refine contMDiffAt_subtype_iff (U := U) (x := ⟨y₀, hlt⟩) |>.mp ?_
    refine (hU _).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    have hy : ‖f y‖ < 1 := y.property
    simp only [comp_apply, cappedExchangeAlmostComplex_of_norm_le h₀ J hJ
      (by linarith : (2 : ℝ) < L) (Ioo_subset_Icc_self (hcy y)) hy.le]
  · -- Off the disc `‖w‖ ≤ 1/2` the family is the input-exchange family.
    have hw₀ : f y₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hge
      norm_num at hge
    refine (contMDiffAt_exchangeAlmostComplex h₀ J hJ hJp hJs (hc y₀) (hf y₀) (hb y₀) (hcy y₀)
      ⟨hw₀, hf₁ y₀⟩).congr_of_eventuallyEq ?_
    filter_upwards [hf.continuous.norm.continuousAt.eventually
      (lt_mem_nhds (by linarith : 1 / 2 < ‖f y₀‖))] with y hy
    rw [cappedExchangeAlmostComplex_of_re_endCoord_le h₀ J hJ
      (re_endCoord_zero_le_half (by linarith) hy.le)]

/-! ### Solutions at the end of the family -/

/-- **Solutions at the end of the family.** Let `σ'(z) = (1, 0) - z` be the exchange `w ↦ 1 - w`
in the real coordinates `ℝ × ℝ ≃ ℂ`, let the Hamiltonians `H_q` on `M` have period one and be
`C¹`, let the output structures `J ∞` have period one, and let `L > 4`. If `u` is differentiable at
a point `σ'(z)` of the capped domain `ℂ ∖ {0}` and solves the Floer equation there for the data of
the capping family at `1` with exchanged Hamiltonians and end structures, then `u ∘ σ'` solves the
Floer equation at `z` for the member `c = 1` of the family capped at `0`: the perturbation
`TauCeti.Floer.cappedExchangePerturbation H L 1` with the almost complex structure
`cappedExchangeAlmostComplex h₀ J hJ L 1`. -/
theorem isComplexLinearMap_perturbedMFDeriv_cappedExchange_one {H : Puncture → ℝ → M → ℝ}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (hL : 4 < L)
    (hJp : Periodic (J inf) 1) (hJ' : ∀ q t, σ.Tames (Floer.exchangeEndData J q t))
    {u : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm ((1, 0) - z) = one.endCenter ∨
      Complex.equivRealProdCLM.symm ((1, 0) - z) ≠ 0 ∧
        Complex.equivRealProdCLM.symm ((1, 0) - z) ≠ 1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u ((1, 0) - z))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.cappingAlmostComplex (Floer.exchangeEndData J) hJ' one L
        (Complex.equivRealProdCLM.symm ((1, 0) - z))).almostComplexStructureAt (u ((1, 0) - z)))
      (σ.perturbedMFDeriv
        (fun z x ↦ Floer.plumbedPerturbation (Pi.single inf (H zero)) (Floer.exchangeEndData H)
          one L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ Floer.plumbedPerturbation (Pi.single inf (H zero)) (Floer.exchangeEndData H)
          one L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u ((1, 0) - z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.cappedExchangeAlmostComplex J hJ L 1
        (Complex.equivRealProdCLM.symm z)).almostComplexStructureAt (u ((1, 0) - z)))
      (σ.perturbedMFDeriv
        (fun z x ↦ Floer.cappedExchangePerturbation H L 1 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ Floer.cappedExchangePerturbation H L 1 (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        (u ∘ fun z ↦ (1, 0) - z) z).toLinearMap := by
  set e := Complex.equivRealProdCLM.symm
  have hσ : 1 - e z = e ((1, 0) - z) := by
    apply Complex.ext <;> simp [e]
  -- The structure at `z` is the exchanged capping structure at `σ'(z)`.
  rw [cappedExchangeAlmostComplex_one h₀ J hJ (by linarith) hJp hJ', hσ]
  -- The perturbation is the pullback along `σ'` of the exchanged capping perturbation, which is
  -- differentiable in the target point at `σ'(z)`.
  have hK (v : ℂ) : MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ Floer.plumbedPerturbation (Pi.single inf (H zero)) (Floer.exchangeEndData H) one L
        (e ((1, 0) - z)) x v) (u ((1, 0) - z)) := by
    have hd := Floer.contMDiffAt_plumbedPerturbation_single_inf (q := one) (by decide)
      (Floer.periodic_exchangeEndData hH) (Floer.contMDiff_uncurry_exchangeEndData hHs) hL hz
      (u ((1, 0) - z))
    rw [Floer.exchangeEndData_one] at hd
    exact ((hd.comp _ (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply
      contMDiffAt_const).mdifferentiableAt one_ne_zero
  exact σ.isComplexLinearMap_perturbedMFDeriv_comp_one_sub
    (Floer.cappedExchangePerturbation_one (hH inf) (by linarith)) hu hK h

end TauCeti.SmoothTwoForm.Compatible
