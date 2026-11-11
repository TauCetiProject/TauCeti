/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange

/-!
# Almost complex structures along the input-exchange family

Graded commutativity of the pair-of-pants product compares the pair of pants with its inputs
exchanged by the holomorphic involution `σ(w) = 1 - w` of `S = ℂ ∖ {0, 1}`. The Hamiltonian
perturbations of the comparison are the input-exchange family
`TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`: the input part of the pair-of-pants datum
plus the negative plane datum of the output Hamiltonian, translated by `c`. It is the pair-of-pants
datum at `c = 0` and the pullback along `σ` of the pair-of-pants datum with exchanged inputs at
`c = 1`. This file constructs the matching family of domain-dependent almost complex structures.

Fix an `ω`-compatible base structure `J₀` and families `J_q(t, x)` of `ω`-tame structures on the
three ends. The *input part* is the pair-of-pants structure whose output structure is replaced by
`J₀`, and the *plane part* is the negative plane structure of `J_∞`
(`TauCeti.Floer.negativePlaneAlmostComplex`). The input part is `J₀` at distance at least `1/2`
from both inputs (`TauCeti.Floer.pairOfPantsAlmostComplex_update_inf_base_eq`), and the plane part
is `J₀` on the disc `‖w‖ ≤ 2 exp (2π)`. Relative to `J₀`, the Cayley transform of the pair-of-pants
structure is the sum of the Cayley transforms of its two parts
(`TauCeti.Floer.cayley_pairOfPantsAlmostComplex_eq_add`), just as the pair-of-pants datum is the sum
of its input part and its plane datum.

The family `TauCeti.Floer.exchangeAlmostComplex h₀ J hJ c` is the input part on the disc
`‖w - c‖ ≤ 2 exp (2π)` and the plane part translated by `c` off it. Every member is `ω`-tame, and
`ω`-compatible when the end structures are. For `-1 ≤ c ≤ 2` the two parts are `J₀` where the other
one is used, so the Cayley transform of the member `c` is the sum of the Cayley transforms of the
input part and of the translated plane part (`TauCeti.Floer.cayley_exchangeAlmostComplex`). The
main results are:

* `TauCeti.Floer.exchangeAlmostComplex_zero`: at `c = 0` the family is the pair-of-pants structure.
* `TauCeti.Floer.exchangeAlmostComplex_one`: at `c = 1` it is the pair-of-pants structure with
  exchanged end structures (`TauCeti.Floer.exchangeEndData`) composed with `σ`, if `J_∞` has
  period one. The output structure of the exchanged data is rotated by half a period,
  `t ↦ J_∞(t + 1/2)`, which matches the half turn of the end at `∞`
  (`TauCeti.Floer.negativePlaneAlmostComplex_neg`).
* `TauCeti.Floer.exchangeAlmostComplex_cylindricalEndLift` and
  `TauCeti.Floer.exchangeAlmostComplex_add_cylindricalEndLift_inf`: if `J_q` has period one,
  every member with `0 ≤ c ≤ 1` is `J_q(t, x)` far out on the input end `q`, in the end lift
  `φ_q`, and if `J_∞` has period one, every member is `J_∞(t, x)` far out on the output end, in
  the end lift `c + φ_∞`. These are the end coordinates in which the members of
  `TauCeti.Floer.exchangePerturbation` are `H_q(t) dt`.
* `TauCeti.Floer.contMDiffAt_exchangeAlmostComplex`: for period-one `C^n` end families, the family
  is `C^n` jointly in the parameter `-1 < c < 2`, the domain point of `S` and the point `x`.
* `TauCeti.Floer.isComplexLinearMap_perturbedFDeriv_exchange_one`: for a symplectic vector space
  target, if `u` solves the Floer equation at `σ(z)` for the pair-of-pants data with exchanged
  inputs, then `u ∘ σ` solves it at `z` for the member `c = 1` of the family, perturbation and
  almost complex structure together.

Together with `TauCeti.Floer.exchangePerturbation_zero`, the members `c = 0` and `c = 1` of the
family of Floer data `(K_c, J_c)` are therefore the pair-of-pants problem and the problem with
exchanged inputs.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on
  perturbation data on punctured surfaces whose ends are related by automorphisms.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M V : Type*}

/-- The radius `2 exp (2π)` of the disc on which the negative plane data are trivial exceeds `3`. -/
private theorem three_lt_two_mul_exp_two_pi : 3 < 2 * Real.exp (2 * π) := by
  nlinarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]

section Algebraic

variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}

/-- **The input-exchange family of almost complex structures.** For `c ∈ ℝ`, relative to an
`ω`-compatible base structure `J₀`, this is the pair-of-pants structure of the input structures
of `J` (with output structure `J₀`) on the disc `‖w - c‖ ≤ 2 exp (2π)`, and the negative plane
structure of the output structure `J_∞` translated by `c` off that disc. Its output end is the end
at `∞` recentred at `c`, as for the perturbations `TauCeti.Floer.exchangePerturbation`. At `c = 0`
it is the pair-of-pants structure (`TauCeti.Floer.exchangeAlmostComplex_zero`), and at `c = 1`,
if `J_∞` has period one, it is the pair-of-pants structure with exchanged end structures composed
with `w ↦ 1 - w` (`TauCeti.Floer.exchangeAlmostComplex_one`). -/
def exchangeAlmostComplex (h₀ : ω.Compatible J₀)
    (J : Puncture → ℝ → M → AlmostComplexStructure V) (hJ : ∀ q t x, ω.Tames (J q t x))
    (c : ℝ) (w : ℂ) (x : M) : AlmostComplexStructure V :=
  if ‖w - c‖ ≤ 2 * Real.exp (2 * π) then
    pairOfPantsAlmostComplex h₀ (update J inf fun _ _ => J₀) (tames_update_inf_base h₀.tames hJ)
      w x
  else negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (w - c) x

/-- On the disc `‖w - c‖ ≤ 2 exp (2π)` the member `c` of the family is the pair-of-pants structure
of the input structures. -/
theorem exchangeAlmostComplex_of_norm_le (h₀ : ω.Compatible J₀) {c : ℝ} {w : ℂ}
    (hw : ‖w - c‖ ≤ 2 * Real.exp (2 * π)) (x : M) :
    exchangeAlmostComplex h₀ J hJ c w x =
      pairOfPantsAlmostComplex h₀ (update J inf fun _ _ => J₀)
        (tames_update_inf_base h₀.tames hJ) w x := by
  simp only [exchangeAlmostComplex, hw, ↓reduceIte]

/-- Off the disc `‖w - c‖ ≤ 2 exp (2π)` the member `c` of the family is the negative plane
structure of the output structure, translated by `c`. -/
theorem exchangeAlmostComplex_of_lt_norm (h₀ : ω.Compatible J₀) {c : ℝ} {w : ℂ}
    (hw : 2 * Real.exp (2 * π) < ‖w - c‖) (x : M) :
    exchangeAlmostComplex h₀ J hJ c w x =
      negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (w - c) x := by
  simp only [exchangeAlmostComplex, hw.not_ge, ↓reduceIte]

/-- Every member of the family is tamed by `ω`. -/
theorem tames_exchangeAlmostComplex (h₀ : ω.Compatible J₀) (c : ℝ) (w : ℂ) (x : M) :
    ω.Tames (exchangeAlmostComplex h₀ J hJ c w x) := by
  unfold exchangeAlmostComplex
  split_ifs
  exacts [tames_pairOfPantsAlmostComplex h₀ w x, tames_negativePlaneAlmostComplex h₀ _ x]

/-- Every member of the family is `ω`-compatible when the end structures are. -/
theorem compatible_exchangeAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ q t x, ω.Compatible (J q t x)) (c : ℝ) (w : ℂ) (x : M) :
    ω.Compatible (exchangeAlmostComplex h₀ J hJ c w x) := by
  unfold exchangeAlmostComplex
  split_ifs
  · exact compatible_pairOfPantsAlmostComplex h₀
      ((forall_update_iff J fun _ f => ∀ t x, ω.Compatible (f t x)).2
        ⟨fun _ _ => h₀, fun q _ => hJc q⟩) w x
  · exact compatible_negativePlaneAlmostComplex h₀ (hJc inf) _ x

/-- **The Cayley transform of the family.** For `-1 ≤ c ≤ 2`, relative to `J₀`, the Cayley
transform of the member `c` of the family is the sum of the Cayley transforms of the pair-of-pants
structure of the input structures and of the negative plane structure of the output structure
translated by `c`: each part is `J₀` where the other one is used. -/
theorem cayley_exchangeAlmostComplex (h₀ : ω.Compatible J₀) {c : ℝ} (hc : c ∈ Icc (-1) 2)
    (w : ℂ) (x : M) :
    J₀.cayley (exchangeAlmostComplex h₀ J hJ c w x) =
      J₀.cayley (pairOfPantsAlmostComplex h₀ (update J inf fun _ _ => J₀)
          (tames_update_inf_base h₀.tames hJ) w x) +
        J₀.cayley (negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (w - c) x) := by
  rcases le_or_gt ‖w - c‖ (2 * Real.exp (2 * π)) with hw | hw
  · rw [exchangeAlmostComplex_of_norm_le h₀ hw, negativePlaneAlmostComplex_eq_of_norm_le h₀ hw,
      AlmostComplexStructure.cayley_self, add_zero]
  · obtain ⟨hw₀, hw₁⟩ := half_le_norm_of_le_norm_sub (r := 2) (w := w)
      (abs_le.2 ⟨by linarith [hc.1], hc.2⟩) (abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩)
      (by linarith [three_lt_two_mul_exp_two_pi])
    rw [exchangeAlmostComplex_of_lt_norm h₀ hw,
      pairOfPantsAlmostComplex_update_inf_base_eq (hJb := hJ) h₀ hw₀ hw₁,
      AlmostComplexStructure.cayley_self, zero_add]

/-- **The start of the family is the pair-of-pants structure.** -/
@[simp]
theorem exchangeAlmostComplex_zero (h₀ : ω.Compatible J₀) :
    exchangeAlmostComplex h₀ J hJ 0 = pairOfPantsAlmostComplex h₀ J hJ := by
  funext w x
  refine h₀.eq_of_cayley_eq (tames_exchangeAlmostComplex h₀ 0 w x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  rw [cayley_exchangeAlmostComplex h₀ ⟨by norm_num, by norm_num⟩, Complex.ofReal_zero, sub_zero]
  exact (cayley_pairOfPantsAlmostComplex_eq_add h₀ w x).symm

/-- The input part of the pair-of-pants structure is exchanged by `w ↦ 1 - w`: the input part with
exchanged end structures at `1 - w` is the input part at `w`. -/
private theorem pairOfPantsAlmostComplex_update_exchangeEndData_one_sub
    (h₀ : ω.Compatible J₀)
    (hA : ∀ q t x, ω.Tames (update (exchangeEndData J) inf (fun _ _ => J₀) q t x))
    (w : ℂ) (x : M) :
    pairOfPantsAlmostComplex h₀ (update (exchangeEndData J) inf fun _ _ => J₀) hA (1 - w) x =
      pairOfPantsAlmostComplex h₀ (update J inf fun _ _ => J₀)
        (tames_update_inf_base h₀.tames hJ) w x := by
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsAlmostComplex h₀ _ x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  simp [cayley_pairOfPantsAlmostComplex, Puncture.sum_univ, endCoord_zero_one_sub,
    endCoord_one_one_sub, AlmostComplexStructure.cayley_self, add_comm]

/-- **The end of the family is the exchanged pair-of-pants structure.** If the output structure
`J_∞` has period one in `t`, the member `c = 1` of the family at `w` is the pair-of-pants structure
with exchanged end structures (`TauCeti.Floer.exchangeEndData`: `J one` at `0`, `J zero` at `1` and
`t ↦ J_∞(t + 1/2)` at `∞`) at `1 - w`. -/
theorem exchangeAlmostComplex_one (h₀ : ω.Compatible J₀) (hJp : Periodic (J inf) 1)
    (hJ' : ∀ q t x, ω.Tames (exchangeEndData J q t x)) (w : ℂ) (x : M) :
    exchangeAlmostComplex h₀ J hJ 1 w x =
      pairOfPantsAlmostComplex h₀ (exchangeEndData J) hJ' (1 - w) x := by
  refine h₀.eq_of_cayley_eq (tames_exchangeAlmostComplex h₀ 1 w x)
    (tames_pairOfPantsAlmostComplex h₀ _ x) ?_
  -- The output part: the exchanged output structure is `J_∞` rotated by half a period.
  have hplane (K : ℝ → M → AlmostComplexStructure V) (hK : ∀ t x, ω.Tames (K t x))
      (hKJ : K = fun t => J inf (t + 1 / 2)) :
      negativePlaneAlmostComplex h₀ K hK (1 - w) x =
        negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (w - 1) x := by
    subst hKJ
    rw [← negativePlaneAlmostComplex_neg h₀ hJp hK (w - 1) x, neg_sub]
  rw [cayley_exchangeAlmostComplex h₀ ⟨by norm_num, by norm_num⟩, Complex.ofReal_one,
    cayley_pairOfPantsAlmostComplex_eq_add (Jb := exchangeEndData J) (hJb := hJ'),
    pairOfPantsAlmostComplex_update_exchangeEndData_one_sub (hJ := hJ),
    hplane _ (hJ' inf) (exchangeEndData_inf J)]

/-- **The family is `J_q(t)` far out on an input end.** For `0 ≤ c ≤ 1`, if `J q` has period one
in `t`, then on the part `s ≥ 2` of the input end `q` the member `c` of the family at the point
with end coordinates `z = s + i t` is `J q t x`. -/
theorem exchangeAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀) {q : Puncture}
    (hq : q ≠ inf) (hJp : Periodic (J q) 1) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ}
    (hz : 2 ≤ z.re) (x : M) :
    exchangeAlmostComplex h₀ J hJ c (q.cylindricalEndLift z) x = J q z.im x := by
  have hw : ‖q.cylindricalEndLift z - c‖ ≤ 2 * Real.exp (2 * π) :=
    (norm_cylindricalEndLift_sub_le hq hc₀ hc₁ (by linarith)).trans
      (by linarith [three_lt_two_mul_exp_two_pi])
  rw [exchangeAlmostComplex_of_norm_le h₀ hw,
    pairOfPantsAlmostComplex_cylindricalEndLift h₀ (by simpa [update_of_ne hq] using hJp)
      (by rwa [endSign_eq_one hq, one_mul]) x, update_of_ne hq]

/-- **The family is `J_∞(t)` far out on the output end.** If `J_∞` has period one in `t`, then on
the part `s ≤ -2` of the output end recentred at `c`, the member `c` of the family at the point
`c + φ_∞(z)` with end coordinates `z = s + i t` is `J_∞ t x`. -/
theorem exchangeAlmostComplex_add_cylindricalEndLift_inf (h₀ : ω.Compatible J₀)
    (hJp : Periodic (J inf) 1) (c : ℝ) {z : ℂ} (hz : z.re ≤ -2) (x : M) :
    exchangeAlmostComplex h₀ J hJ c (c + inf.cylindricalEndLift z) x = J inf z.im x := by
  have hφ : 2 * Real.exp (2 * π) < ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    rw [h]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])) two_pos
  rw [exchangeAlmostComplex_of_lt_norm h₀ (by rwa [add_sub_cancel_left]), add_sub_cancel_left,
    negativePlaneAlmostComplex_cylindricalEndLift h₀ hJp hz]

end Algebraic

section Smooth

/-! ### Smoothness -/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → M → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The family is smooth.** For families `J q t x` of `ω`-tame structures which have period one
in `t` and are `C^n` on `ℝ × M`, the input-exchange family is `C^n` jointly in the parameter `c`,
the domain point of `S = ℂ ∖ {0, 1}` and the point `x`, at every parameter `-1 < c < 2`. Near the
disc `‖w - c‖ < 2 exp (2π)` it is the pair-of-pants structure of the input structures, and near
the complement of the disc `‖w - c‖ ≤ 3` it is the translated negative plane structure. -/
theorem contMDiffAt_exchangeAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap))
    {c : ℝ} (hc : c ∈ Ioo (-1) 2) (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × (ℂ × M) =>
        (exchangeAlmostComplex h₀ J hJ p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap)
      (c, ((w : ℂ), x)) := by
  have hdist : Continuous fun p : ℝ × (ℂ × M) => ‖p.2.1 - (p.1 : ℂ)‖ :=
    ((continuous_fst.comp continuous_snd).sub
      (Complex.continuous_ofReal.comp continuous_fst)).norm
  rcases lt_or_ge ‖(w : ℂ) - c‖ (2 * Real.exp (2 * π)) with hlt | hge
  · -- Near the disc the family is the pair-of-pants structure of the input structures.
    have hin := contMDiffAt_pairOfPantsAlmostComplex h₀ (hJ := tames_update_inf_base h₀.tames hJ)
      ((forall_update_iff J fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hJp q⟩)
      ((forall_update_iff J fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
        (fun p : ℝ × M => (f p.1 p.2).toLinearMap.toContinuousLinearMap)).2
        ⟨contMDiff_const, fun q _ => hJs q⟩)
      w x
    refine (hin.comp (c, ((w : ℂ), x)) contMDiffAt_snd).congr_of_eventuallyEq ?_
    filter_upwards [hdist.continuousAt.eventually (gt_mem_nhds hlt)] with p hp
    simp only [Function.comp_apply, exchangeAlmostComplex_of_norm_le h₀ hp.le]
  · -- Away from the disc `‖w - c‖ ≤ 3` the family is the translated plane structure.
    have hpl : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
        (fun p : ℝ × (ℂ × M) => (negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (p.2.1 - p.1)
          p.2.2).toLinearMap.toContinuousLinearMap) (c, ((w : ℂ), x)) := by
      have hsub : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
          (fun p : ℝ × (ℂ × M) => p.2.1 - (p.1 : ℂ)) (c, ((w : ℂ), x)) :=
        (contMDiffAt_fst.comp _ contMDiffAt_snd).sub
          (Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst)
      exact (contMDiff_negativePlaneAlmostComplex h₀ (hJp inf) (hJs inf)).contMDiffAt.comp
        (f := fun p : ℝ × (ℂ × M) => (p.2.1 - (p.1 : ℂ), p.2.2)) _
        (hsub.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))
    refine hpl.congr_of_eventuallyEq ?_
    have h3 : 3 < ‖(w : ℂ) - c‖ := three_lt_two_mul_exp_two_pi.trans_le hge
    filter_upwards [hdist.continuousAt.eventually (lt_mem_nhds h3),
      continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hc)] with p hp hpc
    rcases le_or_gt ‖p.2.1 - p.1‖ (2 * Real.exp (2 * π)) with hle | hgt
    · -- In the annulus `3 < ‖w - c‖ ≤ 2 exp (2π)` both parts are the base structure.
      obtain ⟨hw₀, hw₁⟩ := half_le_norm_of_le_norm_sub (r := 2) (w := p.2.1)
        (abs_le.2 ⟨by linarith [hpc.1], hpc.2.le⟩)
        (abs_le.2 ⟨by linarith [hpc.1], by linarith [hpc.2]⟩) (by linarith)
      rw [exchangeAlmostComplex_of_norm_le h₀ hle,
        pairOfPantsAlmostComplex_update_inf_base_eq (hJb := hJ) h₀ hw₀ hw₁,
        negativePlaneAlmostComplex_eq_of_norm_le h₀ hle]
    · rw [exchangeAlmostComplex_of_lt_norm h₀ hgt]

end Smooth

section Solutions

/-! ### Solutions at the end of the family -/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {H : Puncture → ℝ → V → ℝ}
  {J : Puncture → ℝ → V → AlmostComplexStructure V} {hJ : ∀ q t x, ω.Tames (J q t x)}

/-- **Solutions at the end of the family.** Let `σ(z) = (1, 0) - z` be the exchange `w ↦ 1 - w` in
the real coordinates `ℝ × ℝ ≃ ℂ`, let the Hamiltonians `H_q` have period one and be `C¹`, and let
the output structure `J_∞` have period one. If `u` is differentiable at `σ(z) ∈ S` and solves the
Floer equation there for the pair-of-pants data with exchanged inputs, then `u ∘ σ` solves the
Floer equation at `z` for the member `c = 1` of the input-exchange family: the perturbation
`TauCeti.Floer.exchangePerturbation H 1` with the almost complex structure
`TauCeti.Floer.exchangeAlmostComplex h₀ J hJ 1` at `u(σ(z))`. -/
theorem isComplexLinearMap_perturbedFDeriv_exchange_one (h₀ : ω.Compatible J₀)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hJp : Periodic (J inf) 1) (hJ' : ∀ q t x, ω.Tames (exchangeEndData J q t x))
    {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    (hu : DifferentiableAt ℝ u ((1, 0) - z))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (pairOfPantsAlmostComplex h₀ (exchangeEndData J) hJ'
        (Complex.equivRealProdCLM.symm ((1, 0) - z)) (u ((1, 0) - z)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation (exchangeEndData H)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (exchangeEndData H)
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        u ((1, 0) - z) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (exchangeAlmostComplex h₀ J hJ 1 (Complex.equivRealProdCLM.symm z) (u ((1, 0) - z)))
      (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H 1 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H 1 (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ fun z ↦ (1, 0) - z) z : ℝ × ℝ →ₗ[ℝ] V) := by
  set e := Complex.equivRealProdCLM.symm
  have hσ : e ((1, 0) - z) = 1 - e z := by
    apply Complex.ext <;> simp [e]
  -- The structure at `z` is the exchanged pair-of-pants structure at `σ(z)`.
  rw [exchangeAlmostComplex_one h₀ hJp hJ', ← hσ]
  -- The perturbation is the pullback along `σ` of the exchanged pair-of-pants perturbation.
  have hpull (v : ℝ × ℝ) : (fun z x ↦ exchangePerturbation H 1 (e z) x (e v)) =
      perturbationPullback (fun z ↦ (1, 0) - z)
        (fun z x ↦ pairOfPantsPerturbation (exchangeEndData H) (e z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (exchangeEndData H) (e z) x Complex.I) v := by
    funext z' x
    rw [perturbationPullback_pairOfPantsPerturbation_exchangeEndData (hH inf)]
  rw [← equivRealProdCLM_symm_stdComplexLineReal, ← equivRealProdCLM_symm_stdComplexLineImag,
    hpull, hpull]
  -- The exchanged pair-of-pants perturbation is differentiable in the target point at `σ(z)`.
  have hS : e ((1, 0) - z) ≠ 0 ∧ e ((1, 0) - z) ≠ 1 := by
    rw [hσ]
    exact ⟨fun h0 => hz.2 (by linear_combination -h0), fun h1 => hz.1 (by linear_combination -h1)⟩
  have hK (v : ℂ) : DifferentiableAt ℝ
      (fun x ↦ pairOfPantsPerturbation (exchangeEndData H) (e ((1, 0) - z)) x v)
      (u ((1, 0) - z)) := by
    have hd := (contDiffAt_pairOfPantsPerturbation_prod (periodic_exchangeEndData hH)
      (contDiff_uncurry_exchangeEndData hHs) hS (u ((1, 0) - z))).differentiableAt
      one_ne_zero
    exact (hd.comp _ ((differentiableAt_const _).prodMk differentiableAt_id)).clm_apply
      (differentiableAt_const v)
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
