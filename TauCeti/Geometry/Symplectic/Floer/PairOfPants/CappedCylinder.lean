/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped
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

For a manifold target `M` with a nondegenerate two-form `ω`, such as a closed symplectic
manifold, the curvature bound, the energy identity and the action bound between loops at finite
ends hold, with actions depending on discs bounding the loops; the bound on limiting actions at
the two ends is not proved for a manifold target here. The curvature bound
holds along every map into `M`
(`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le`; the
vector space bound is its case `TauCeti.SymplecticForm.constSmooth`). For a `C¹` map `u` with
`u(s, 1) = u(s, 0)`, the energy over `[a, b] × [0, 1]` is
`∫ u^*ω + ∫₀¹ H_0(t, u(b, t)) dt - ∫₀¹ H_∞(t, u(a, t)) dt - ∫ R_K(u)`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent`). For a `C²`
map, `1`-periodic in `t`, and a disc `D` bounding the output loop `γ_a = u(a, ·)`, the disc `D ⋆ u`
transported along the cylinder bounds the input loop `γ_b = u(b, ·)`, and

`∫ E = A_{H_0}(γ_b, D ⋆ u) - A_{H_∞}(γ_a, D) - ∫ R_K(u)`

for the capped action `A_H(γ, D) = ∫ D^*ω + ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cappedLoopAction`)
(`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub`).
Hence for a Floer solution with tamed almost complex structures,
`A_{H_∞}(γ_a, D) ≤ A_{H_0}(γ_b, D ⋆ u) + B_1 + (B_0 + B_1 + B_∞)`
(`IsNondegenerate.cappedLoopAction_le_add_add_sum_of_cappedCylinderComponent`). These
identities assume that the energy density and the curvature along `u` are integrable over the
rectangle.

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
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the energy of Floer cylinders between capped
  orbits.
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

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] {Hb : Puncture → ℝ → M → ℝ} {L : ℝ} {Bb : Puncture → ℝ}
  {ω : SmoothTwoForm I M} {u : ℝ × ℝ → M} {a b : ℝ}

/-- **The integrated curvature of the capped cylinder is bounded uniformly in the neck length**,
for a manifold target. For period-one `C¹` Hamiltonians on a manifold `M` with a two-form `ω`,
with `|Hb r| ≤ Bb r`, and neck length `L > 4`, along every map `u` into `M` the integral of
`|R_K(z, u(z))|` over one period `ℝ × [t₀, t₀ + 1)` of the cylinder is at most
`Bb 1 + ∑ r, Bb r`. -/
theorem lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (t₀ : ℝ) (u : ℝ × ℝ → M) :
    ∫⁻ z in univ ×ˢ Ico t₀ (t₀ + 1), ‖ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) z (u z)‖ₑ ≤
      ENNReal.ofReal (Bb one) + ∑ r, ENNReal.ofReal (Bb r) := by
  set s : Set (ℝ × ℝ) := univ ×ˢ Ico t₀ (t₀ + 1)
  have hinj := injOn_endChart_univ_prod_Ico zero t₀
  -- A map on the capped domain which restricts to `u` along the end chart.
  set u' : ℝ × ℝ → M := u ∘ invFunOn (endChart zero) s
  have hu' {w : ℝ × ℝ} (hw : w ∈ s) : u' (endChart zero w) = u w := by
    simp only [u', comp_apply]
    rw [hinj.leftInvOn_invFunOn hw]
  -- The end chart lands in `ℂ ∖ {0}`, where the capped datum is `C¹`.
  have hK (w : ℝ × ℝ) (x : M) := contMDiffAt_plumbedPerturbation_single_inf (n := 1)
    (q := one) (w := Complex.equivRealProdCLM.symm (endChart zero w)) (by simp) hHb hHbs hL
    (by rw [equivRealProdCLM_symm_endChart]; exact cylindricalEndLift_zero_eq_endCenter_one_or _)
    x
  -- Differentiability in the domain point.
  have hdom (v : ℂ) (w : ℝ × ℝ) (x : M) : DifferentiableAt ℝ
      (fun z ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (Complex.equivRealProdCLM.symm z) x v) (endChart zero w) := by
    have hg : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℂ).prod I) 1
        (fun z : ℝ × ℝ ↦ (Complex.equivRealProdCLM.symm z, x)) (endChart zero w) :=
      (Complex.equivRealProdCLM.symm.contDiff.contMDiff.prodMk contMDiff_const).contMDiffAt
    exact (contMDiffAt_iff_contDiffAt.1 (((hK w x).comp (endChart zero w) hg).clm_apply
      contMDiffAt_const)).differentiableAt one_ne_zero
  -- Differentiability in the target point.
  have htgt (v : ℂ) (w : ℝ × ℝ) (x : M) : MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (Complex.equivRealProdCLM.symm (endChart zero w)) x v) x := by
    have hg : ContMDiffAt I (𝓘(ℝ, ℂ).prod I) 1
        (fun x : M ↦ (Complex.equivRealProdCLM.symm (endChart zero w), x)) x :=
      contMDiffAt_const.prodMk contMDiffAt_id
    exact (((hK w x).comp x hg).clm_apply contMDiffAt_const).mdifferentiableAt one_ne_zero
  have h := ω.lintegral_enorm_hamiltonianCurvature_image (u := u')
    (Ks := fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
      (Complex.equivRealProdCLM.symm z) x Complex.I)
    (MeasurableSet.univ.prod measurableSet_Ico) hinj
    (fun w _ ↦ (contDiff_endChart zero 2).contDiffAt) (fun w _ ↦ hdom 1 w _)
    (fun w _ ↦ hdom Complex.I w _) (fun w _ ↦ htgt 1 w _) (fun w _ ↦ htgt Complex.I w _)
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
    _ ≤ _ := ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_inf_le
        (q := one) (by simp) hHb hHbs hL hBb u'

/-- The integrated curvature of the capped cylinder over the rectangle `[a, b] × [0, 1]` is at
most `Bb 1 + ∑ r, Bb r`, whatever `a`, `b` and the neck length `L > 4`. -/
theorem abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → M) (a b : ℝ) :
    |∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) z (u z)| ≤ Bb one + ∑ r, Bb r := by
  have hB0 (r : Puncture) : 0 ≤ Bb r := (abs_nonneg _).trans (hBb r 0 (u 0))
  have hsum : 0 ≤ ∑ r, Bb r := Finset.sum_nonneg fun r _ ↦ hB0 r
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (hB0 one) hsum), ← Real.eNorm_eq_ofReal_abs,
    ENNReal.ofReal_add (hB0 one) hsum, ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hB0 r]
  have hcurv := ω.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le hHb hHbs hL hBb
    0 u
  -- The rectangle lies in `ℝ × [0, 1]`, which is `ℝ × [0, 1)` up to a null set.
  have hsets : ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] univ ×ˢ Icc 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc
  rw [zero_add, setLIntegral_congr hsets] at hcurv
  exact (eNorm_integral_le_lintegral_eNorm _).trans
    ((lintegral_mono_set (prod_mono (subset_univ _) le_rfl)).trans hcurv)

variable [FiniteDimensional ℝ E]

/-- **The energy identity of the capped cylinder**, for a manifold target. Let `ω` be a
nondegenerate two-form on a finite-dimensional manifold `M`, `Hb` period-one `C¹` Hamiltonians
on `M` and `L > 4`, and let `u` be `C¹` with `u(s, 1) = u(s, 0)` for `s ∈ [a, b]`. If `a ≤ -3`
and `2 ≤ b`, and the energy density and the curvature along `u` are integrable over the rectangle,
then the Floer energy of `u` over `[a, b] × [0, 1]` for the capped datum on the cylinder is the
symplectic area of `u` over the rectangle, plus the Hamiltonian term of the input loop at `s = b`
for `Hb 0`, minus that of the output loop at `s = a` for `Hb ∞`, minus the integrated curvature:

`∫ E = ∫ u^*ω + ∫₀¹ Hb 0 (t, u(b, t)) dt - ∫₀¹ Hb ∞ (t, u(a, t)) dt - ∫ R_K(u)`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (ha : a ≤ -3) (hb : 2 ≤ b)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z =
      rectangleIntegral ω.1 u (a, 0) (b, 1) + (∫ t in 0..1, Hb zero t (u (b, t))) -
        (∫ t in 0..1, Hb inf t (u (a, t))) -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z) := by
  have hab : a ≤ b := by linarith
  have hL₂ : 2 ≤ L := by linarith
  have hR' : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := Icc_prod_Icc _ _ _ _
  have hab' : ((a, 0) : ℝ × ℝ) ≤ (b, 1) := Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  rw [hR'] at hE hR ⊢
  rw [hω.integral_floerEnergyDensity isOpen_univ hu.contMDiffOn
    (contMDiff_cappedCylinderComponent hHb hHbs hL 1).contMDiffOn
    (contMDiff_cappedCylinderComponent hHb hHbs hL Complex.I).contMDiffOn hab' (subset_univ _)
    hE hR, ← hω₀.setIntegral_eq_rectangleIntegral hu hab']
  -- The `ds` terms along the circles `t = 0` and `t = 1` cancel by periodicity.
  have hs : ∫ s in a..b, cappedCylinderComponent Hb L 1 (s, 1) (u (s, 1)) =
      ∫ s in a..b, cappedCylinderComponent Hb L 1 (s, 0) (u (s, 0)) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le hab] at hs
    rw [hper s hs]
    simpa using congrFun (periodic_cappedCylinderComponent Hb L 1 s 0) (u (s, 0))
  -- The `dt` terms along the circles `s = b` and `s = a` are those of `Hb 0` and `Hb ∞`.
  have hb' : ∫ t in (0 : ℝ)..1, cappedCylinderComponent Hb L Complex.I (b, t) (u (b, t)) =
      ∫ t in (0 : ℝ)..1, Hb zero t (u (b, t)) :=
    intervalIntegral.integral_congr fun t _ ↦ by
      simp [cappedCylinderComponent_of_two_le (hHb zero) hL₂ (z := (b, t)) hb]
  have ha' : ∫ t in (0 : ℝ)..1, cappedCylinderComponent Hb L Complex.I (a, t) (u (a, t)) =
      ∫ t in (0 : ℝ)..1, Hb inf t (u (a, t)) :=
    intervalIntegral.integral_congr fun t _ ↦ by
      simp [cappedCylinderComponent_of_le_neg_three (hHb inf) hL₂ (z := (a, t)) ha]
  rw [hs, hb', ha']
  simp only [SmoothBundleForm.eval₂_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  ring

/-- **The energy of the capped cylinder in terms of capped actions**, for a manifold target.
Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent`, let
`u` be `C²` and `1`-periodic in `t`, and let `D` be a disc bounding the output loop
`γ_a = u(a, ·)`. Gluing to `D` the cylinder swept by `u` from `γ_a` to the input loop
`γ_b = u(b, ·)` gives a disc `D ⋆ u` bounding `γ_b`, and the Floer energy of `u` over
`[a, b] × [0, 1]` is the capped action of the input for `Hb 0` minus that of the output for `Hb ∞`,
minus the integrated curvature:

`∫ E = A_{Hb 0}(γ_b, D ⋆ u) - A_{Hb ∞}(γ_a, D) - ∫ R_K(u)`,

for the capped action `A_H(γ, D) = ∫ D^*ω + ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cappedLoopAction`). -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    (ha : a ≤ -3) (hb : 2 ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z =
      cappedLoopAction ω.1 (Hb zero) (fun t ↦ u (b, t))
          (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) -
        cappedLoopAction ω.1 (Hb inf) (fun t ↦ u (a, t)) D -
        ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z) := by
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  have h := cappedLoopAction_rectangleTrans_sub_cappedLoopAction hω₀ (Hb zero) hD
    (isLoopCylinder_comp_prodMap hu hper a b)
  rw [hω.integral_floerEnergyDensity_cappedCylinderComponent hHb hHbs hL (hu.of_le one_le_two) ha
    hb (fun s _ ↦ by simpa using hper (s, 0)) hE hR,
    ← rectangleIntegral_comp_prodMap_affine hω₀ (hu.of_le one_le_two) a b 0 1]
  rw [cappedLoopAction_def, cappedLoopAction_def] at h ⊢
  linarith

/-- **The energy bound of the capped cylinder**, for a manifold target. Under the hypotheses of
`IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub`, if
`|Hb r| ≤ Bb r`, then the Floer energy over `[a, b] × [0, 1]` differs from the change of capped
action `A_{Hb 0}(γ_b, D ⋆ u) - A_{Hb ∞}(γ_a, D)` by at most `Bb 1 + ∑ r, Bb r`, uniformly in the
neck length and in `a` and `b`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    (ha : a ≤ -3) (hb : 2 ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t))
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    |(∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z) -
      (cappedLoopAction ω.1 (Hb zero) (fun t ↦ u (b, t))
          (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) -
        cappedLoopAction ω.1 (Hb inf) (fun t ↦ u (a, t)) D)| ≤ Bb one + ∑ r, Bb r := by
  have hsub (x y z : ℝ) : x - y - z - (x - y) = -z := by ring
  rw [hω.integral_floerEnergyDensity_cappedCylinderComponent_eq_cappedLoopAction_sub hHb hHbs hL
    hu hper ha hb hD hE hR, hsub, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le hHb hHbs hL hBb u a b

/-- **The action bound of the capped cylinder**, for a manifold target. Under the hypotheses of
`IsNondegenerate.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le`, if `u` solves
the Floer equation on the rectangle for almost complex structures `J z` on `T_{u z} M` tamed by
`ω`, then the capped action of the output loop `γ_a = u(a, ·)` with its disc `D` is at most that
of the input loop `γ_b = u(b, ·)` with the transported disc `D ⋆ u`, plus `Bb 1 + ∑ r, Bb r`:

`A_{Hb ∞}(γ_a, D) ≤ A_{Hb 0}(γ_b, D ⋆ u) + Bb 1 + ∑ r, Bb r`.

This is the action filtration shift of the capping family on a manifold target, the same at
every neck length. -/
theorem IsNondegenerate.cappedLoopAction_le_add_add_sum_of_cappedCylinderComponent
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L)
    (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    (ha : a ≤ -3) (hb : 2 ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t))
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedMFDeriv (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u z).toLinearMap)
    (hE : IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) u) (Icc a b ×ˢ Icc 0 1))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    cappedLoopAction ω.1 (Hb inf) (fun t ↦ u (a, t)) D ≤
      cappedLoopAction ω.1 (Hb zero) (fun t ↦ u (b, t))
          (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) +
        Bb one + ∑ r, Bb r := by
  have hE₀ := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_cappedCylinderComponent_sub_le hHb hHbs
    hL hBb hu hper ha hb hD hE hR)).2
  linarith

end TauCeti.SmoothTwoForm

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
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hL hBb t₀ u

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
  simpa using ω.constSmooth.abs_setIntegral_hamiltonianCurvature_cappedCylinderComponent_le hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hL hBb u a b

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
