/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart.Output

/-!
# The linearized operator along the input-exchange family on `W^{1,2}`

Graded commutativity of the pair-of-pants product counts the members of the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, on the pair of pants
`S = ℂ ∖ {0, 1}`, on a finite-dimensional symplectic vector space `(V, ω)`. Each member is the
pair-of-pants datum far out on the two input ends, and on the output end it is the pair-of-pants
datum translated by `c`: it is `H_∞(t) dt` in the end chart `c + φ'_∞` recentred at `c`. This file
realizes the linearized operator `D_u` of such data on the Sobolev space `W^{1,2}_0(S, V)` of the
cylindrical metric, `TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical
weight `ρ = TauCeti.Floer.cylindricalWeight`, and proves that it has finite-dimensional kernel and
closed range, as `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm` does for data
that are the pair-of-pants datum far out on every end.

* **The coefficients on the recentred output end.** The coefficient field of `D_u` on the conformal
  jets of `ρ` is `(a, b, c') ↦ b + J c' + ρ^(-1/2) C a`, where `C` is the zeroth-order part of
  `D_u`. At a point `z = φ'_∞(ζ) + c` of the recentred output end, the zeroth-order part of the
  data is that of their translate by `c` at `φ'_∞(ζ)`, where the translated data are the
  pair-of-pants data. So the chart identity of the pair of pants bounds
  `2π |φ'_∞(ζ)| ‖C(z)‖` by the coefficients of the end datum `H'_∞(t) dt` along `u` read in the
  recentred chart. Since `ρ(z)^(-1/2) ≤ |z| ≤ 2 |φ'_∞(ζ)|` for `|c| ≤ 1`, the coefficient field on
  conformal jets is bounded there
  (`TauCeti.SymplecticForm.norm_floerConformalJetCoeff_positiveEndChart_inf_add_le`).
* **Boundedness.** Far out on the output end the standard end chart and the recentred one cover
  the same points: a point beyond the height `T + 1` of `φ'_∞` lies beyond the height `T` of
  `c + φ'_∞`. With the bounds on the input ends and continuity on a compact truncation, the
  coefficient field is essentially bounded on `S`
  (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_of_recentered`), so the realization is the
  linearized operator on the jets of test sections.
* **Peetre's estimate.** With the semi-Fredholm estimate for data with a recentred output end
  (`exists_forall_le_mul_integral_floerLinearization_add_of_recentered` in
  `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange.SemiFredholm`), this gives Peetre's
  estimate `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x` of test sections, for a compact
  `K ⊆ S`
  (`exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_recentered`), and Peetre's
  argument gives finite-dimensional kernel
  (`finiteDimensional_ker_floerConformalSobolevOperator_of_recentered`) and closed range
  (`isClosed_range_floerConformalSobolevOperator_of_recentered`).
* **The input-exchange family.** Every member `K_c` of the family is such a datum, so its
  linearized operator has finite-dimensional kernel
  (`finiteDimensional_ker_floerConformalSobolevOperator_exchangePerturbation`) and closed range
  (`isClosed_range_floerConformalSobolevOperator_exchangePerturbation`).

The finiteness of the cokernel and the Fredholm index are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and its graded
  commutativity.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate and Sobolev spaces on punctured Riemann surfaces
  with cylindrical ends.
-/

public section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Far out on the output end, at a point `w` with `|w| > 8`, the inverse square root of the
cylindrical weight at `w + c`, for `|c| ≤ 1`, is at most `2 |w|`, written as
`π⁻¹ (2π |w - c_∞|)` with the center `c_∞ = 0` of the output end. -/
private theorem inv_sqrt_cylindricalWeight_add_le {c : ℝ} (hc : |c| ≤ 1) {w : ℝ × ℝ}
    (hw : 8 < ‖Complex.equivRealProdCLM.symm w‖) :
    (√(cylindricalWeight (w + (c, 0))))⁻¹ ≤
      π⁻¹ * (2 * π * ‖Complex.equivRealProdCLM.symm w - inf.endCenter‖) := by
  have hcn : ‖(c : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hadd : Complex.equivRealProdCLM.symm (w + (c, 0)) = Complex.equivRealProdCLM.symm w + c :=
    TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero w c
  have hne : Complex.equivRealProdCLM.symm (w + (c, 0)) ≠ inf.endCenter := by
    rw [hadd, endCenter_inf]
    intro h
    have := norm_sub_norm_le (Complex.equivRealProdCLM.symm w) (-(c : ℂ))
    rw [norm_neg, sub_neg_eq_add, h, norm_zero] at this
    linarith
  -- The weight at `w + c` is at least `|w + c|⁻²`, and `|w + c| ≤ |w| + 1 ≤ 2 |w|`.
  refine (inv_sqrt_cylindricalWeight_le_norm_sub_endCenter inf hne).trans ?_
  rw [hadd, endCenter_inf, sub_zero, sub_zero,
    show π⁻¹ * (2 * π * ‖Complex.equivRealProdCLM.symm w‖) =
      2 * ‖Complex.equivRealProdCLM.symm w‖ by field_simp]
  linarith [norm_add_le (Complex.equivRealProdCLM.symm w) (c : ℂ)]

/-- **The coefficient field on conformal jets on a recentred output end.** Let `|c| ≤ 1`, and let
`z = φ'_∞(ζ) + c`, with `ζ = (s, t)` and `s ≥ 2`, be a point of the output end of
`S = ℂ ∖ {0, 1}` read in the end chart `c + φ'_∞` recentred at `c`. Suppose that at `z` the
structures are `J(z, ·) = J_∞(t)`, the perturbation `(K_s, K_t)` is the pair-of-pants perturbation
of period-one Hamiltonians `H_q` translated by `c`, with `H_∞(t)` `C²`, and `u` solves the Floer
equation. If `B` bounds the coefficient field on jets of the end datum `H'_∞(t) dt`, with the
structures `J_∞(t)`, along `u` read in the recentred chart at `ζ`, then the coefficient field on
the conformal jets of the cylindrical weight is at most `1 + B + (1 + B) B / π` at `z`. -/
theorem norm_floerConformalJetCoeff_positiveEndChart_inf_add_le (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ t, ContDiff ℝ 2 (H inf t))
    {c : ℝ} (hc : |c| ≤ 1) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Jq : ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) (hJz : J (positiveEndChart inf ζ + (c, 0)) = Jq ζ.2)
    (hKs : Ks (positiveEndChart inf ζ + (c, 0)) = fun x ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)) x 1)
    (hKt : Kt (positiveEndChart inf ζ + (c, 0)) = fun x ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)) x
        Complex.I)
    (hu : DifferentiableAt ℝ u (positiveEndChart inf ζ + (c, 0)))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ + (c, 0)) (u (positiveEndChart inf ζ + (c, 0))))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart inf ζ + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H inf w.2)
      (fun ζ' ↦ u (positiveEndChart inf ζ' + (c, 0))) ζ‖ ≤ B) :
    ‖ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
      (positiveEndChart inf ζ + (c, 0))‖ ≤ 1 + B + (1 + B) * B / π := by
  set a : ℝ × ℝ := (c, 0)
  set w := positiveEndChart inf ζ
  -- The data and `u` translated by `c` are the pair-of-pants data and a solution of their Floer
  -- equation at `w`.
  have hfl' : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (w + a) (u (w + a)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (fun v ↦ u (v + a)) w : ℝ × ℝ →ₗ[ℝ] V) := by
    rw [← ω.perturbedFDeriv_congr _ (Ks := fun v ↦ Ks (v + a)) (Kt := fun v ↦ Kt (v + a)) hKs hKt,
      ω.perturbedFDeriv_comp_add_right]
    exact hfl
  have hu' : DifferentiableAt ℝ (fun v ↦ u (v + a)) w :=
    hu.comp w (differentiableAt_id.add_const a)
  have hC := ω.mul_norm_floerLinearizationCoeff_positiveEndChart_le hH (q := inf) hHs
    (J := fun v ↦ J (v + a)) hζ hu' hfl'
  -- The zeroth-order part at `w` of the translated data is that of the data at `w + c`.
  have hCt : ω.floerLinearizationCoeff (fun z y ↦ (J (z + a) y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (fun v ↦ u (v + a)) w =
        ω.floerLinearizationCoeff (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (w + a) := by
    rw [ω.floerLinearizationCoeff_congr_data (Ks' := fun v ↦ Ks (v + a))
      (Kt' := fun v ↦ Kt (v + a)) _ rfl hKs.symm hKt.symm]
    ext v
    simp only [floerLinearizationCoeff_apply, fderiv_comp_add_right]
  rw [hCt] at hC
  have h8 : 8 < ‖Complex.equivRealProdCLM.symm w‖ :=
    eight_lt_norm_of_one_lt_fst_positiveEndCoord_inf (by
      rw [fst_positiveEndCoord_positiveEndChart]
      linarith)
  refine (ω.norm_floerConformalJetCoeff_le_of_norm_floerJetCoeff_comp_le (ρ := cylindricalWeight)
    (φ := fun ζ' ↦ positiveEndChart inf ζ' + a)
    (Je := fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap)
    (congrArg (fun j y ↦ (j y).toLinearMap.toContinuousLinearMap) hJz) hB hC
    (inv_sqrt_cylindricalWeight_add_le hc h8) (inv_nonneg.2 pi_pos.le)).trans_eq (by ring)

/-- **The coefficient field on the recentred output end.** Let `|c| ≤ 1`, and far out on the output
end, beyond the height `T` of the end chart `c + φ'_∞` recentred at `c`, let the data be
cylindrical, `J(φ'_∞(s, t) + c) = J_∞(t)`, with the pair-of-pants perturbation of jointly `C²`
period-one Hamiltonians `H_q` translated by `c`, and let `u` be `C¹` there and solve the Floer
equation. If `B` bounds the coefficient field on jets of the end datum along `u` read in the
recentred chart over the band `t ∈ [0, 1]` beyond `T`, then the coefficient field on conformal jets
is at most `1 + B + (1 + B) B / π` beyond the height `T + 1` of the standard end chart `φ'_∞`. -/
theorem norm_floerConformalJetCoeff_positiveEndChart_inf_le_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ContDiff ℝ 2 (uncurry (H inf))) {c : ℝ} (hc : |c| ≤ 1)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V} (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    {T B : ℝ} (hT : max 2 R₁ ≤ T)
    (hB : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → ζ.2 ∈ Icc (0 : ℝ) 1 →
      ‖ω.floerJetCoeff (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H inf w.2)
        (fun ζ' ↦ u (positiveEndChart inf ζ' + (c, 0))) ζ‖ ≤ B)
    {ζ : ℝ × ℝ} (hζ : T + 1 < ζ.1) :
    ‖ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (positiveEndChart inf ζ)‖ ≤
      1 + B + (1 + B) * B / π := by
  have h2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hz : positiveEndChart inf ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (by linarith)
  -- Read the point in the recentred end chart, beyond its height `T`.
  obtain ⟨ζ', hζ'1, hζ'2, hζ'⟩ := exists_positiveEndChart_inf_eq_add hc (by linarith) hζ
  have hR₁ : R₁ ≤ ζ'.1 := by linarith [le_max_right 2 R₁]
  have hR : R₁ ≤ (positiveEndCoord inf (positiveEndChart inf ζ')).1 := by
    rwa [fst_positiveEndCoord_positiveEndChart]
  rw [hζ'] at hz ⊢
  exact ω.norm_floerConformalJetCoeff_positiveEndChart_inf_add_le hH
    (fun t ↦ hHs.comp (contDiff_const.prodMk contDiff_id)) hc (by linarith) (hJeq ζ' hR₁)
    (hK _ hR).1 (hK _ hR).2
    ((hu _ hz).differentiableAt one_ne_zero) (hF _ hR) (hB ζ' hζ'1.le (Ico_subset_Icc_self hζ'2))

/-- **The coefficients of the linearized operator with a recentred output end are bounded on the
jets of `W^{1,2}`.** Let `H_q` be jointly `C²` period-one Hamiltonians on the three ends of
`S = ℂ ∖ {0, 1}`, let `|c| ≤ 1`, and let `(J, K_s, K_t)` be Floer data on `S`, with `J` `C¹` and
`K_s`, `K_t` `C²` along `u`, which far out on each end, beyond a height `R₁`, are cylindrical: on
the input ends `q = 0, 1` they are `C¹` families `J_q(t)` and the pair-of-pants perturbation of `H`
in the positive end charts `φ'_q`, and on the output end they are a `C¹` family `J_∞(t)` and the
pair-of-pants perturbation translated by `c`, in the recentred end chart `c + φ'_∞`. Let `u` be
`C¹` on `S`, solve the Floer equation beyond `R₁` on each end, and have loops, read in these end
charts, converging uniformly on `[0, 1]` to loops `x_q` continuous on `[0, 1]`, while the slice
defects tend uniformly to zero. Then the coefficient field of the linearized Floer operator on the
jets of the cylindrical weight is essentially bounded on `S`, so that
`TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from `W^{1,2}_0(S, V)` to
`L²(S, V)`. The members of the input-exchange family `TauCeti.Floer.exchangePerturbation` are such
data. -/
theorem memLp_floerConformalJetCoeff_of_recentered (ω : SymplecticForm V)
    {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc : |c| ≤ 1) {x : Puncture → ℝ → V}
    (hx : ∀ q, ContinuousOn (x q) (Icc 0 1)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
      (volume.restrict thricePuncturedSphereReal) := by
  have hcont : ContinuousOn (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) thricePuncturedSphereReal :=
    ω.continuousOn_floerConformalJetCoeff isWeight_cylindricalWeight hJ hKs hKt
      fun z hz ↦ (hu z hz).contDiffWithinAt
  -- Far out on each end, the coefficient field of the end datum along `u` read in its end chart
  -- is bounded over the band `t ∈ [0, 1]`.
  have hin (q : Puncture) : ∃ B, ∀ᶠ s in atTop, q ≠ inf → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖ω.floerJetCoeff (fun w y ↦ (Je q w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) (s, t)‖ ≤ B := by
    by_cases hq : q = inf
    · exact ⟨0, .of_forall fun _ h ↦ (h hq).elim⟩
    obtain ⟨B, h⟩ := ω.exists_eventually_norm_floerJetCoeff_le
      (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (hJe q) (hx q) (hux q hq) (hδ q hq)
    exact ⟨B, h.mono fun _ h _ ↦ h⟩
  choose Bq hBq using hin
  obtain ⟨B₀, hB₀⟩ := ω.exists_eventually_norm_floerJetCoeff_le
    (contDiff_uncurry_positiveEndHamiltonian (hHs inf)) (hJe inf) (hx inf) hux_inf hδ_inf
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((eventually_all.2 hBq).and
    (hB₀.and (eventually_ge_atTop (max 2 R₁))))
  have hTR : max 2 R₁ ≤ T := (hT T le_rfl).2.2
  set B := ∑ q, |Bq q| + |B₀|
  have hBqB (q : Puncture) : Bq q ≤ B := (le_abs_self _).trans ((Finset.single_le_sum
    (f := fun q' ↦ |Bq q'|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ q)).trans
      (le_add_of_nonneg_right (abs_nonneg _)))
  have hB₀B : B₀ ≤ B :=
    (le_abs_self _).trans (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
  -- Beyond the height `T + 1` the point lies far out on an input end, where the data are the
  -- pair-of-pants data, or far out on the recentred output end.
  refine memLp_top_of_continuousOn_of_norm_positiveEndChart_le hcont (T := T + 1)
    (M := 1 + B + (1 + B) * B / π) fun q ζ hζ1 hζ2 ↦ ?_
  by_cases hq : q = inf
  · subst hq
    exact ω.norm_floerConformalJetCoeff_positiveEndChart_inf_le_of_recentered hH (hHs inf) hc
      hJeq_inf hK_inf hu hF_inf hTR (fun ζ hζ ht ↦ ((hT ζ.1 hζ).2.1 ζ.2 ht).trans hB₀B) hζ1
  have h2 : 2 ≤ ζ.1 := by linarith [le_max_left 2 R₁]
  have hR₁ : R₁ ≤ ζ.1 := by linarith [le_max_right 2 R₁]
  have hR : R₁ ≤ (positiveEndCoord q (positiveEndChart q ζ)).1 := by
    rwa [fst_positiveEndCoord_positiveEndChart]
  have hz : positiveEndChart q ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (by linarith)
  refine (ω.norm_floerConformalJetCoeff_positiveEndChart_le hH
    (fun t ↦ (hHs q).comp (contDiff_const.prodMk contDiff_id)) h2 (hJeq q hq ζ hR₁)
    (hK q hq _ hz hR).1 (hK q hq _ hz hR).2 ((hu _ hz).differentiableAt one_ne_zero)
    (hF q hq _ hz hR)
    (((hT ζ.1 (by linarith)).1 q hq ζ.2 (Ico_subset_Icc_self hζ2)).trans (hBqB q))).trans ?_
  gcongr
  linarith [pi_pos]

/-- **Peetre's estimate for data with a recentred output end.** Under the hypotheses of the
semi-Fredholm estimate `exists_forall_le_mul_integral_floerLinearization_add_of_recentered`
(Floer data `(J, K_s, K_t)` that are cylindrical far out on the ends and equal there to the
pair-of-pants data on the input ends and to their translate by `c ∈ [0, 1]` on the output end, and
a map `u` that solves the Floer equation there and whose ends converge to nondegenerate one-periodic
orbits of the end Hamiltonians), there are a compact set `K ⊆ S` and `C` such that the jet
`x ∈ W^{1,2}_0(S, V)` of every test section `ξ` satisfies `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` for
the realization `D_u = TauCeti.SymplecticForm.floerConformalSobolevOperator` of the linearized
Floer operator. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ K, IsCompact K ∧ K ⊆ thricePuncturedSphereReal ∧ ∃ C,
      ∀ y : H1 V thricePuncturedSphereReal cylindricalWeight,
        (y : Lp (V × V × V) 2 (volume.restrict thricePuncturedSphereReal)) ∈
          jetSubmodule V thricePuncturedSphereReal cylindricalWeight →
        ‖y‖ ≤ C * (‖ω.floerConformalSobolevOperator thricePuncturedSphereReal cylindricalWeight
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u y‖ +
          ‖restrictWeightedValue V thricePuncturedSphereReal K y‖) := by
  obtain ⟨C, -, T, hT, hest⟩ := ω.exists_forall_le_mul_integral_floerLinearization_add_of_recentered
    hH hHs hc₀ hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hK hK_inf hJ hKs hKt hu hc hF hF_inf hux hux_inf
    hδ hδ_inf
  have hM := ω.memLp_floerConformalJetCoeff_of_recentered hH hHs
    (abs_le.2 ⟨by linarith, hc₁⟩)
    (fun q ↦ (continuous_iff_continuousAt.2 fun t ↦ (hx q t).continuousAt).continuousOn) hJe hJeq
    hJeq_inf hK hK_inf hJ hKs hKt hu hF hF_inf hux hux_inf hδ hδ_inf
  obtain ⟨C', hC'⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_estimate hM hT hest
  exact ⟨_, isCompact_preimage_truncation _, preimage_truncation_subset_thricePuncturedSphereReal _,
    C', hC'⟩

/-- **The linearized operator with a recentred output end has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_add_of_recentered`, the realization
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator for the cylindrical metric has
finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).ker := by
  obtain ⟨K, hK, hKS, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_recentered
      hH hHs hc₀ hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hK hK_inf hJ hKs hKt hu hc hF hF_inf hux
      hux_inf hδ hδ_inf
  exact finiteDimensional_ker_of_estimate isWeight_cylindricalWeight hK hKS _ hest

/-- **The linearized operator with a recentred output end has closed range on `W^{1,2}`.** Under
the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_add_of_recentered`, the realization
`D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator for the cylindrical metric has
closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_of_recentered
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {Ks Kt : ℝ × ℝ → V → ℝ}
    (hK : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      Ks z = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt z = fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (hK_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      Ks (z + (c, 0)) = (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1) ∧
        Kt (z + (c, 0)) =
          fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv Ks Kt u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).range :
        Set (Lp V 2 (volume.restrict thricePuncturedSphereReal))) := by
  obtain ⟨K, hK, hKS, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_recentered
      hH hHs hc₀ hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hK hK_inf hJ hKs hKt hu hc hF hF_inf hux
      hux_inf hδ hδ_inf
  exact isClosed_range_of_estimate isWeight_cylindricalWeight hK hKS _ hest

/-- **Peetre's estimate along the input-exchange family.** Let `K_c` be the member `c ∈ [0, 1]` of
the input-exchange family `TauCeti.Floer.exchangePerturbation H c`, under the hypotheses of its
semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_exchangePerturbation_add`. Then there are a
compact set `K ⊆ S` and `C` such that the jet `x ∈ W^{1,2}_0(S, V)` of every test section `ξ`
satisfies `‖x‖ ≤ C (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` for the realization of the linearized Floer operator
of `(J, K_c)`. -/
theorem exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_exchangePerturbation_add
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    ∃ K, IsCompact K ∧ K ⊆ thricePuncturedSphereReal ∧ ∃ C,
      ∀ y : H1 V thricePuncturedSphereReal cylindricalWeight,
        (y : Lp (V × V × V) 2 (volume.restrict thricePuncturedSphereReal)) ∈
          jetSubmodule V thricePuncturedSphereReal cylindricalWeight →
        ‖y‖ ≤ C * (‖(ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u) y‖ +
          ‖restrictWeightedValue V thricePuncturedSphereReal K y‖) := by
  -- Beyond the height `max R₁ 2`, `K_c` is the pair-of-pants datum on the input ends and its
  -- translate by `c` on the output end.
  have hR₁ : R₁ ≤ max R₁ 2 := le_max_left _ _
  have h1 {r : ℝ} (hr : max R₁ 2 ≤ r) : 1 < r := by linarith [le_max_right R₁ 2]
  exact ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_recentered hH hHs
    hc₀ hc₁ hX hx hnd hJe hJex (fun q hq ζ hζ ↦ hJeq q hq ζ (hR₁.trans hζ))
    (fun ζ hζ ↦ hJeq_inf ζ (hR₁.trans hζ))
    (fun _ hq _ _ hz ↦
      exchangePerturbation_components_eq_of_pos_fst_positiveEndCoord hc₀ hc₁ hq
        (zero_lt_one.trans (h1 hz)))
    (fun _ hz ↦ exchangePerturbation_add_components_eq_of_one_lt_fst_positiveEndCoord hc₀ hc₁
      (h1 hz)) hJ
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs c hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_exchangePerturbation hH hHs c hz (u z) Complex.I) hu hc
    (fun q hq z hz hzR ↦ hF q hq z hz (hR₁.trans hzR)) (fun z hz ↦ hF_inf z (hR₁.trans hz)) hux
    hux_inf hδ hδ_inf

/-- **The linearized operator along the input-exchange family has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_exchangePerturbation_add` along the member
`c ∈ [0, 1]` of the input-exchange family, the realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of
the linearized Floer operator of `(J, K_c)` for the cylindrical metric has finite-dimensional
kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_exchangePerturbation
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).ker := by
  obtain ⟨K, hK, hKS, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_exchangePerturbation_add hH hHs
      hc₀ hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hJ hu hc hF hF_inf hux hux_inf hδ hδ_inf
  exact finiteDimensional_ker_of_estimate isWeight_cylindricalWeight hK hKS _ hest

/-- **The linearized operator along the input-exchange family has closed range on `W^{1,2}`.**
Under the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_exchangePerturbation_add` along the member
`c ∈ [0, 1]` of the input-exchange family, the realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of
the linearized Floer operator of `(J, K_c)` for the cylindrical metric has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_exchangePerturbation
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {L : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (L q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q, q ≠ inf → ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    (hJeq_inf : ∀ ζ : ℝ × ℝ, R₁ ≤ ζ.1 → J (positiveEndChart inf ζ + (c, 0)) = Je inf ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, q ≠ inf → ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hF_inf : ∀ z : ℝ × ℝ, R₁ ≤ (positiveEndCoord inf z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (z + (c, 0)) (u (z + (c, 0))))
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (z + (c, 0)) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, q ≠ inf →
      TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop (Icc 0 1))
    (hux_inf : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t) + (c, 0))) (x inf)
      atTop (Icc 0 1))
    (hδ : ∀ q, q ≠ inf → TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hδ_inf : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H inf t))
        (fun ζ ↦ u (positiveEndChart inf ζ + (c, 0))) (s, t)) 0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u).range :
        Set (Lp V 2 (volume.restrict thricePuncturedSphereReal))) := by
  obtain ⟨K, hK, hKS, C, hest⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_exchangePerturbation_add hH hHs
      hc₀ hc₁ hX hx hnd hJe hJex hJeq hJeq_inf hJ hu hc hF hF_inf hux hux_inf hδ hδ_inf
  exact isClosed_range_of_estimate isWeight_cylindricalWeight hK hKS _ hest

end TauCeti.SymplecticForm
