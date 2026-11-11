/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# The pair of pants capped at `1` as a Floer cylinder

Plumbing the negative PSS plane with Hamiltonian `H_1` into the input end at `1` of the pair of
pants `ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞`, along a neck of length `L`, gives the
perturbation one-form `K = TauCeti.Floer.plumbedPerturbation (Pi.single ∞ H_1) H 1 L` of the
capping family (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping`). It is smooth on the
capped domain `ℂ ∖ {0}`, a cylinder whose two ends are the remaining input at `0` and the output
at `∞`. This file puts it on the standard cylinder `ℝ × ℝ/ℤ`, where, like a continuation datum
from `H_0` to `H_∞`, it is `H_0(t) dt` and `H_∞(t) dt` on the two ends; the unit property of the
pair-of-pants product compares the capping family with continuation maps in these coordinates.

The end lift `φ_0(z) = exp (-2πz) / 2` of the end at `0` maps the cylinder `ℂ / iℤ` onto
`ℂ ∖ {0}`. The end lift at `∞` is centred at `0` too, so in the cylinder coordinate `z = s + i t`
of `φ_0` the end at `∞` is the translate `z ↦ z + log 4 / (2π)` of its own end coordinate
(`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift_zero_eq_inf_add`). The pullback of `K`
along `φ_0` has components `TauCeti.Floer.cappedCylinderComponent H L v` along a tangent vector `v`
of the cylinder, and:

* it is `H_0(t) dt` for `s ≥ 2` (`TauCeti.Floer.cappedCylinderComponent_of_two_le`) and `H_∞(t) dt`
  for `s ≤ -3` (`TauCeti.Floer.cappedCylinderComponent_of_le_neg_three`), whatever the neck length
  `L ≥ 2`; the capping Hamiltonian `H_1` only enters on the preimage of the end at `1`, a disc in
  the cylinder about the point that `φ_0` sends to the capped puncture `1`;
* it has period one in `t` (`TauCeti.Floer.periodic_cappedCylinderComponent`);
* for `L > 4` and period-one `C^n` Hamiltonians it is `C^n` jointly in the cylinder point and the
  target point (`TauCeti.Floer.contMDiff_cappedCylinderComponent`, for a manifold target, and
  `TauCeti.Floer.contDiff_uncurry_cappedCylinderComponent`, for a vector space target).

For a symplectic vector space target `(V, ω)` and bounds `|H_r| ≤ B_r`, the integrated curvature
`∫ |R_K(u)|` over one period `ℝ × [t₀, t₀ + 1)` of the cylinder is at most
`B_1 + (B_0 + B_1 + B_∞)` along every map `u`, uniformly in `L`
(`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le`), since
the curvature allowance does not depend on the chart. For a `C²` map `u` with
`u(s, 1) = u(s, 0)`, and `a ≤ -3`, `2 ≤ b`, the Floer energy over `[a, b] × [0, 1]` is

`∫ E = A_{H_0}(u(b, ·)) - A_{H_∞}(u(a, ·)) - ∫ R_K(u)`

(`TauCeti.SymplecticForm.integral_floerEnergyDensity_cappedCylinderComponent`), within
`B_1 + (B_0 + B_1 + B_∞)` of the change of action
(`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le`). For a
Floer solution with tame almost complex structures the energy is nonnegative, so the action of the
output loop is at most the action of the input loop plus this constant
(`TauCeti.SymplecticForm.hamiltonianAction_le_add_add_sum_of_cappedCylinderComponent`), and the
same holds for the limiting actions at the two ends
(`TauCeti.SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_cappedCylinderComponent`).
This is the action filtration shift of the capping family, the same at every neck length.

Capping the input at `0` instead leaves the cylinder `ℂ ∖ {1}`, whose remaining end at `1` is
centred at `1` while the output end is centred at `0`; the two end coordinates then differ by more
than a translation, and that family is not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity of Hamiltonian perturbations.
-/

public noncomputable section

open Set Real Manifold Topology Function MeasureTheory Filter
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {Hb : Puncture → ℝ → M → ℝ} {L : ℝ}

/-- **The pair of pants capped at `1`, on the cylinder.** The component along a tangent vector
`v` of the cylinder, at the point `z = (s, t)` and the target point `x`, of the pullback along the
end lift `φ_0` of the end at `0` of the perturbation obtained by plumbing the negative plane with
Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with Hamiltonians `Hb`, along a
neck of length `L`. Its `ds` and `dt` components are `cappedCylinderComponent Hb L 1` and
`cappedCylinderComponent Hb L Complex.I`. -/
def cappedCylinderComponent (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) (v : ℂ) (z : ℝ × ℝ) (x : M) :
    ℝ :=
  plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
    (zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) x
    (deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) * v)

theorem cappedCylinderComponent_def (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) (v : ℂ) (z : ℝ × ℝ)
    (x : M) :
    cappedCylinderComponent Hb L v z x =
      plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) x
        (deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) * v) :=
  (rfl)

/-- Where the signed longitudinal coordinate of the end at `1` is not positive, the capped datum is
the datum of the receiving pair of pants. -/
private theorem plumbedPerturbation_single_inf_one_of_re_endCoord_nonpos (hL : 2 ≤ L) {w : ℂ}
    (hw : (one.endCoord w).re ≤ 0) (x : M) :
    plumbedPerturbation (Pi.single inf (Hb one)) Hb one L w x = pairOfPantsPerturbation Hb w x :=
  plumbedPerturbation_of_re_endCoord_le (by simp) (by simp) (by linarith) x

/-- On the part `±s ≥ 1` of an end other than `1`, the longitudinal coordinate of the end at `1` is
not positive. -/
private theorem re_endCoord_one_cylindricalEndLift_nonpos {q : Puncture} (hq : q ≠ one) {w : ℂ}
    (hw : 1 ≤ q.endSign * w.re) : (one.endCoord (q.cylindricalEndLift w)).re ≤ 0 := by
  simpa using endSign_mul_re_endCoord_nonpos hq (w := q.cylindricalEndLift w)
    (by rw [re_endCoord_cylindricalEndLift]; linarith)

/-- The end lift of the end at `0` maps the cylinder into `ℂ ∖ {0}`: every image point is the
capped puncture `1` or a point of the pair of pants. -/
private theorem cylindricalEndLift_zero_eq_endCenter_one_or (w : ℂ) :
    zero.cylindricalEndLift w = one.endCenter ∨
      zero.cylindricalEndLift w ≠ 0 ∧ zero.cylindricalEndLift w ≠ 1 := by
  have h₀ := zero.cylindricalEndLift_sub_endCenter_ne_zero w
  rw [endCenter_zero, sub_zero] at h₀
  rcases eq_or_ne (zero.cylindricalEndLift w) 1 with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr ⟨h₀, h⟩

/-- **The input end.** For `s ≥ 2`, the capped datum on the cylinder is `Hb 0 (t) dt`. -/
theorem cappedCylinderComponent_of_two_le (hHb : Periodic (Hb zero) 1) (hL : 2 ≤ L)
    {z : ℝ × ℝ} (hz : 2 ≤ z.1) (v : ℂ) (x : M) :
    cappedCylinderComponent Hb L v z x = v.im * Hb zero z.2 x := by
  set w := Complex.equivRealProdCLM.symm z
  have hw : w.re = z.1 := by simp [w, Complex.equivRealProdCLM_symm_apply]
  have hone : (one.endCoord (zero.cylindricalEndLift w)).re ≤ 0 :=
    re_endCoord_one_cylindricalEndLift_nonpos (by simp)
      (by rw [endSign_zero, one_mul, hw]; linarith)
  rw [cappedCylinderComponent_def, plumbedPerturbation_single_inf_one_of_re_endCoord_nonpos hL hone,
    pairOfPantsPerturbation_cylindricalEndLift hHb (by simpa [hw] using hz)]
  simp [w, Complex.equivRealProdCLM_symm_apply]

/-- **The output end.** For `s ≤ -3`, the capped datum on the cylinder is `Hb ∞ (t) dt`. -/
theorem cappedCylinderComponent_of_le_neg_three (hHb : Periodic (Hb inf) 1) (hL : 2 ≤ L)
    {z : ℝ × ℝ} (hz : z.1 ≤ -3) (v : ℂ) (x : M) :
    cappedCylinderComponent Hb L v z x = v.im * Hb inf z.2 x := by
  -- In the end coordinate of `∞`, the point `z` of the cylinder is `z + c`, and `c < 1`.
  set c : ℝ := Real.log 4 / (2 * π)
  set w := Complex.equivRealProdCLM.symm z + (c : ℂ)
  have hc : c < 1 := by
    rw [div_lt_one (by positivity)]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith [Real.two_le_pi]
  have hw : w.re = z.1 + c := by simp [w, Complex.equivRealProdCLM_symm_apply]
  have hlift : zero.cylindricalEndLift = fun z ↦ inf.cylindricalEndLift (z + (c : ℂ)) :=
    funext cylindricalEndLift_zero_eq_inf_add
  have hderiv : deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) =
      deriv inf.cylindricalEndLift w := by
    rw [hlift, deriv_comp_add_const]
  have hone : (one.endCoord (inf.cylindricalEndLift w)).re ≤ 0 :=
    re_endCoord_one_cylindricalEndLift_nonpos (by simp) (by rw [endSign_inf, hw]; linarith)
  rw [cappedCylinderComponent_def, hderiv, congrFun hlift,
    plumbedPerturbation_single_inf_one_of_re_endCoord_nonpos hL hone,
    pairOfPantsPerturbation_cylindricalEndLift hHb (by rw [endSign_inf, hw]; linarith)]
  simp [w, Complex.equivRealProdCLM_symm_apply]

/-- **Periodicity.** The capped datum on the cylinder has period one in the angular coordinate
`t`. -/
theorem periodic_cappedCylinderComponent (Hb : Puncture → ℝ → M → ℝ) (L : ℝ) (v : ℂ) (s : ℝ) :
    Periodic (fun t ↦ cappedCylinderComponent Hb L v (s, t)) 1 := by
  intro t
  have h : zero.cylindricalEndLift (Complex.equivRealProdCLM.symm (s, t + 1)) =
      zero.cylindricalEndLift (Complex.equivRealProdCLM.symm (s, t)) := by
    simpa [Complex.equivRealProdCLM_symm_apply] using zero.periodic_cylindricalEndLift s t
  funext x
  beta_reduce
  rw [cappedCylinderComponent_def, cappedCylinderComponent_def, deriv_cylindricalEndLift,
    deriv_cylindricalEndLift, h]

/-- The capped datum on the cylinder is the pullback along the end chart of `0` of the capped
datum on `ℂ ∖ {0}`, in real coordinates. -/
theorem perturbationPullback_endChart_zero_plumbedPerturbation (Hb : Puncture → ℝ → M → ℝ)
    (L : ℝ) (v : ℝ × ℝ) :
    perturbationPullback (endChart zero)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
          (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      cappedCylinderComponent Hb L (Complex.equivRealProdCLM.symm v) := by
  rw [perturbationPullback_endChart_eq_cylindricalEndLift]
  funext z x
  rw [cappedCylinderComponent_def]

section Smooth

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The capped datum on the cylinder is smooth.** For period-one Hamiltonians `Hb` of class
`C^n` on `ℝ × M` and neck length `L > 4`, every component of the capped datum on the cylinder is
`C^n` jointly in the cylinder point and the target point. -/
theorem contMDiff_cappedCylinderComponent {n : ℕ∞} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r))) (hL : 4 < L) (v : ℂ) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (cappedCylinderComponent Hb L v)) := by
  rintro ⟨z, x⟩
  have hlift : ContDiff ℝ n
      (fun z : ℝ × ℝ ↦ zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
    ((zero.contDiff_cylindricalEndLift n).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff
  have hderiv : ContDiff ℝ n
      (fun z : ℝ × ℝ ↦ deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm z) * v) := by
    simp only [deriv_cylindricalEndLift]
    exact ((contDiff_const.mul (hlift.sub contDiff_const)).neg).mul contDiff_const
  -- The end lift maps the cylinder into `ℂ ∖ {0}`, where the capped datum is smooth.
  have hK := contMDiffAt_plumbedPerturbation_single_inf (q := one) (by simp) hHb hHbs hL
    (cylindricalEndLift_zero_eq_endCenter_one_or (Complex.equivRealProdCLM.symm z)) x
  have hg : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) n
      (fun p : (ℝ × ℝ) × M ↦ (zero.cylindricalEndLift (Complex.equivRealProdCLM.symm p.1), p.2))
      (z, x) :=
    ((hlift.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt
  exact (hK.comp (z, x) hg).clm_apply (hderiv.contMDiff.comp contMDiff_fst).contMDiffAt

end Smooth

section VectorSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Hb : Puncture → ℝ → V → ℝ}

/-- **The capped datum on the cylinder is smooth**, for a vector space target. For period-one
Hamiltonians `Hb` of class `C^n` on `ℝ × V` and neck length `L > 4`, every component of the capped
datum on the cylinder is `C^n` jointly in the cylinder point and the target point. -/
theorem contDiff_uncurry_cappedCylinderComponent {n : ℕ∞} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ n (uncurry (Hb r))) (hL : 4 < L) (v : ℂ) :
    ContDiff ℝ n (uncurry (cappedCylinderComponent Hb L v)) :=
  (contMDiff_prod_modelWithCornersSelf_iff.1 (contMDiff_cappedCylinderComponent hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hL v)).contDiff

end VectorSpace

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Hb : Puncture → ℝ → V → ℝ} {L : ℝ} {Bb : Puncture → ℝ}

/-- **The integrated curvature of the capped cylinder is bounded uniformly in the neck length.**
For period-one `C¹` Hamiltonians with `|Hb r| ≤ Bb r` and neck length `L > 4`, along every map `u`
the integral of `|R_K(z, u(z))|` over one period `ℝ × [t₀, t₀ + 1)` of the cylinder is at most
`Bb 1 + ∑ r, Bb r`. -/
theorem lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (t₀ : ℝ) (u : ℝ × ℝ → V) :
    ∫⁻ z in univ ×ˢ Ico t₀ (t₀ + 1), ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) z (u z)‖ₑ ≤
      ENNReal.ofReal (Bb one) + ∑ r, ENNReal.ofReal (Bb r) := by
  set s : Set (ℝ × ℝ) := univ ×ˢ Ico t₀ (t₀ + 1)
  have hinj := injOn_endChart_univ_prod_Ico zero t₀
  -- A map on the capped domain which restricts to `u` along the end chart.
  set u' : ℝ × ℝ → V := u ∘ invFunOn (endChart zero) s
  have hu' {w : ℝ × ℝ} (hw : w ∈ s) : u' (endChart zero w) = u w := by
    simp only [u', comp_apply]
    rw [hinj.leftInvOn_invFunOn hw]
  -- The end chart lands in `ℂ ∖ {0}`, where the capped datum is `C¹`.
  have hdiff (v : ℂ) (w : ℝ × ℝ) := (contDiffAt_uncurry_plumbedPerturbation_single_inf
    (q := one) (y := endChart zero w) (by simp) hHb hHbs hL
    (by rw [equivRealProdCLM_symm_endChart]; exact cylindricalEndLift_zero_eq_endCenter_one_or _)
    (u' (endChart zero w)) v).differentiableAt one_ne_zero
  -- Differentiability in the domain point.
  have hdom (v : ℂ) (w : ℝ × ℝ) : DifferentiableAt ℝ
      (fun z ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (Complex.equivRealProdCLM.symm z) (u' (endChart zero w)) v) (endChart zero w) := by
    have hg : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ (z, u' (endChart zero w))) (endChart zero w) := by
      fun_prop
    exact (hdiff v w).comp (endChart zero w) hg
  have h := ω.lintegral_enorm_hamiltonianCurvature_image (u := u')
    (Ks := fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (Complex.equivRealProdCLM.symm z) x Complex.I)
    (MeasurableSet.univ.prod measurableSet_Ico) hinj
    (fun w _ ↦ (contDiff_endChart zero 2).contDiffAt) (fun w _ ↦ hdom 1 w)
    (fun w _ ↦ hdom Complex.I w)
  rw [perturbationPullback_endChart_zero_plumbedPerturbation,
    perturbationPullback_endChart_zero_plumbedPerturbation] at h
  have h₁ : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    simp [stdComplexLineReal_eq, Complex.equivRealProdCLM_symm_apply]
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    simp [stdComplexLineImag_eq, Complex.equivRealProdCLM_symm_apply]
  rw [h₁, hI] at h
  calc ∫⁻ z in s, ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z)‖ₑ
      = ∫⁻ z in s, ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u' (endChart zero z))‖ₑ :=
        setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ico) fun w hw ↦ by
          rw [hu' hw]
    _ = _ := h.symm
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_inf_le ω
        (q := one) (by simp)
        hHb hHbs hL hBb u'

/-- **The energy identity of the capped cylinder.** Let `Hb` be period-one `C¹` Hamiltonians and
`L > 4`, and let `u` be `C²` on an open neighbourhood `U` of `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. If `a ≤ -3` and `2 ≤ b`, then the Floer energy of `u` over
the rectangle for the capped datum on the cylinder is the action of the input loop at `s = b` for
`Hb 0`, minus the action of the output loop at `s = a` for `Hb ∞`, minus the integrated
curvature:

`∫ E = A_{H_0}(u(b, ·)) - A_{H_∞}(u(a, ·)) - ∫ R_K(u)`. -/
theorem integral_floerEnergyDensity_cappedCylinderComponent (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u U) {a b : ℝ}
    (ha : a ≤ -3) (hb : 2 ≤ b) (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z =
      ω.hamiltonianAction (Hb zero) (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (Hb inf) (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z) :=
  ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub_sub_integral_hamiltonianCurvature hU hu
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1).contDiffOn
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I).contDiffOn (by linarith) hRU
    hper (fun s _ ↦ by simpa using periodic_cappedCylinderComponent Hb L 1 s 0)
    (fun t _ ↦ funext fun x ↦ by
      rw [cappedCylinderComponent_of_le_neg_three (hHb inf) (by linarith) ha]
      simp)
    (fun t _ ↦ funext fun x ↦ by
      rw [cappedCylinderComponent_of_two_le (hHb zero) (by linarith) hb]
      simp)

/-- **The energy bound of the capped cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_cappedCylinderComponent`, if `|Hb r| ≤ Bb r`,
then the Floer energy over `[a, b] × [0, 1]` differs from the change of action
`A_{H_0}(u(b, ·)) - A_{H_∞}(u(a, ·))` by at most `Bb 1 + ∑ r, Bb r`, uniformly in the neck length
and in `a` and `b`. -/
theorem abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u U) {a b : ℝ} (ha : a ≤ -3) (hb : 2 ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    |(∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z) -
      (ω.hamiltonianAction (Hb zero) (fun t ↦ u (b, t)) -
        ω.hamiltonianAction (Hb inf) (fun t ↦ u (a, t)))| ≤ Bb one + ∑ r, Bb r := by
  have hsub (x y : ℝ) : x - y - x = -y := by ring
  rw [integral_floerEnergyDensity_cappedCylinderComponent ω hHb hHbs hL hU hu ha hb hRU hper,
    hsub, abs_neg]
  have hB0 (r : Puncture) : 0 ≤ Bb r := (abs_nonneg _).trans (hBb r 0 0)
  have hsum : 0 ≤ ∑ r, Bb r := Finset.sum_nonneg fun r _ ↦ hB0 r
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (hB0 one) hsum), ← Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_add (hB0 one) hsum, ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hB0 r]
  have hcurv := lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le ω hHb hHbs hL hBb
    0 u
  -- The rectangle lies in `ℝ × [0, 1]`, which is `ℝ × [0, 1)` up to a null set.
  have hsets : ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] univ ×ˢ Icc 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq EventuallyEq.rfl Ico_ae_eq_Icc
  rw [zero_add, setLIntegral_congr hsets] at hcurv
  exact (enorm_integral_le_lintegral_enorm _).trans
    ((lintegral_mono_set (prod_mono (subset_univ _) le_rfl)).trans hcurv)

/-- **The action bound of the capped cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le`, if `u`
solves the Floer equation on the rectangle for almost complex structures tamed by `ω`, then the
action of the output loop at `s = a` is at most the action of the input loop at `s = b` plus
`Bb 1 + ∑ r, Bb r`. -/
theorem hamiltonianAction_le_add_add_sum_of_cappedCylinderComponent (ω : SymplecticForm V)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u U) {a b : ℝ} (ha : a ≤ -3) (hb : 2 ≤ b)
    (hRU : Icc a b ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (Hb inf) (fun t ↦ u (a, t)) ≤
      ω.hamiltonianAction (Hb zero) (fun t ↦ u (b, t)) + Bb one + ∑ r, Bb r := by
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le ω hHb hHbs
    hL hBb hU hu ha hb hRU hper)).2
  linarith

/-- **The action bound of the capped cylinder at its ends.** Let `u` be `C²` on an open
neighbourhood `U` of `ℝ × [0, 1]`, with `u(s, 1) = u(s, 0)`, solving the Floer equation there for
the capped datum on the cylinder and almost complex structures tamed by `ω`. If the actions of the
loops `t ↦ u(s, t)` for `Hb ∞` tend to `a_∞` as `s → -∞` and those for `Hb 0` tend to `a_0` as
`s → ∞`, then `a_∞ ≤ a_0 + Bb 1 + ∑ r, Bb r`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_cappedCylinderComponent
    (ω : SymplecticForm V) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hL : 4 < L) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u U)
    (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U) (hper : ∀ s, u (s, 1) = u (s, 0))
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    {a₀ a_inf : ℝ}
    (hinf : Tendsto (fun s ↦ ω.hamiltonianAction (Hb inf) (fun t ↦ u (s, t))) atBot (𝓝 a_inf))
    (h₀ : Tendsto (fun s ↦ ω.hamiltonianAction (Hb zero) (fun t ↦ u (s, t))) atTop (𝓝 a₀)) :
    a_inf ≤ a₀ + Bb one + ∑ r, Bb r := by
  have hsub {a b : ℝ} : Icc a b ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  -- Compare the output loop at `s = -R` with the input loop at `s = R`, for `R ≥ 3`.
  have hbound : ∀ᶠ R in atTop, ω.hamiltonianAction (Hb inf) (fun t ↦ u (-R, t)) ≤
      ω.hamiltonianAction (Hb zero) (fun t ↦ u (R, t)) + Bb one + ∑ r, Bb r :=
    eventually_atTop.2 ⟨3, fun R hR ↦ hamiltonianAction_le_add_add_sum_of_cappedCylinderComponent
      ω hHb hHbs hL hBb hU hu (by linarith) (by linarith) (hsub.trans hRU) (fun s _ ↦ hper s)
      (fun z hz ↦ hJ z (hsub hz)) fun z hz ↦ hfloer z (hsub hz)⟩
  exact le_of_tendsto_of_tendsto (hinf.comp tendsto_neg_atTop_atBot)
    ((h₀.add_const _).add_const _) hbound

end TauCeti.SymplecticForm
