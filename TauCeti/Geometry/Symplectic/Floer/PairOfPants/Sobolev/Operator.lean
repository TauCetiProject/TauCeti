/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.PeriodicOrbitLimit
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Linearization
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization

/-!
# The linearized Floer operator on the Sobolev space of the pair of pants

Let `u` be a Floer pair of pants: a solution of the Floer equation on `S = ℂ ∖ {0, 1}` for the
pair-of-pants perturbation `K = TauCeti.Floer.pairOfPantsPerturbation H` of period-one
Hamiltonians `H_q` on the three ends, with values in a symplectic vector space `(V, ω)`. Its
linearized operator `D_u ξ = ∂s ξ + J(z, u z) ∂t ξ + C(z) ξ`
(`TauCeti.SymplecticForm.floerLinearization`) is written in the coordinate `z` of `ℂ`. This file
shows that it is a bounded operator from the Sobolev space `W^{1,2}_0(S, V)` of the cylindrical
metric (`TauCeti.ConformalSobolev.H1 V S ρ` for the weight `ρ = TauCeti.Floer.cylindricalWeight`
of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev`) to `L²(S, V)`: its realization
`TauCeti.SymplecticForm.floerConformalSobolevOperator` has an essentially bounded coefficient
field on conformal jets, so that it agrees with `D_u` on the jets of test sections
(`TauCeti.SymplecticForm.floerConformalSobolevOperator_toLp_jet_ae_eq`).

The zeroth-order part `C(z)` is not bounded on `S`: near a puncture `c` the perturbation is
`H_q(t) dt`, and `dt` has size `|z - c|⁻¹ / 2π` in the coordinate `z`. What the coefficient field on
conformal jets needs is `‖C(z)‖ ≤ B √ρ(z)`
(`TauCeti.SymplecticForm.norm_floerConformalJetCoeff_le`), and this holds because `C` is bounded in
the end coordinates.

* **The coefficient in end coordinates.** Read in the positive end chart `φ'_q`, the linearized
  operator at `φ'_q(ζ)` is `a D_u - b J D_u` for `(a, b) = dφ'_q (1, 0)`
  (`TauCeti.SymplecticForm.floerLinearization_comp_positiveEndChart`). Applied to constant
  sections, this gives `C_end(ζ) = (a - b J) C(φ'_q ζ)` for the zeroth-order part `C_end` of the
  linearized operator of the end datum `H'_q(t) dt` along `u ∘ φ'_q`
  (`TauCeti.SymplecticForm.floerLinearizationCoeff_comp_positiveEndChart_apply`). Since
  `J² = -1`, `a - b J` is inverted by `(a + b J) / (a² + b²)`, and `a² + b²` is the Jacobian
  `4π² |φ'_q(ζ) - c_q|²` of the chart, so
  `2π |φ'_q(ζ) - c_q| ‖C(φ'_q ζ)‖ ≤ (1 + ‖J‖) ‖C_end(ζ)‖`
  (`TauCeti.SymplecticForm.mul_norm_floerLinearizationCoeff_positiveEndChart_le`).
* **The weight.** The cylindrical weight is at least `|z - c_q|⁻²` for each center `c_q`
  (`TauCeti.Floer.inv_norm_sub_endCenter_sq_le_cylindricalWeight`, in
  `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev`), so `ρ(z)^(-1/2) ‖C(z)‖` is at
  most `(1 + ‖J‖) ‖C_end‖ / 2π` on the ends.
* **Boundedness.** On the ends beyond a height `T ≥ 2`, where `J` is a `C¹` family `J_q(t)` in the
  end coordinates, `u` is bounded and the slice defect `∂t (u ∘ φ'_q) - X_{H'_q}` of the end
  datum is bounded over a band of angular width one, `C_end` is bounded on that band by the
  corresponding estimate on cylinders
  (`TauCeti.SymplecticForm.exists_forall_norm_floerJetCoeff_le`). Since the end chart has period one
  in `t`, the coefficient field on conformal jets is then bounded on the whole end
  (`TauCeti.SymplecticForm.norm_floerConformalJetCoeff_positiveEndChart_le`). On the truncation
  `S_T`, which is compact, the coefficient field is continuous. Hence it is essentially bounded on
  `S` (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_pairOfPants`).

Only the ends use the pair-of-pants perturbation: the coefficient field at a point depends on the
Floer data only through their values at that point
(`TauCeti.SymplecticForm.floerConformalJetCoeff_congr_data`), and on `S_T` continuity suffices. So
`memLp_floerConformalJetCoeff_pairOfPants` is stated for Floer data `(J, K_s, K_t)` on `S` that
equal the pair-of-pants data beyond the height `T`, as do the data of the families that modify the
pair of pants away from its ends, such as the pair of pants with continuation necks.

The bounds on `u` and on the slice defects on the ends are of the kind provided by the convergence
of the ends of a Floer pair of pants to its asymptotic orbits. They are derived from that
convergence, and the semi-Fredholm estimate of `D_u` in this norm with finite-dimensional kernel and
closed range is proved, in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the Sobolev realization of real Cauchy–Riemann operators on surfaces with
  cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal

namespace TauCeti

namespace SymplecticForm

open Floer ConformalSobolev ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **The zeroth-order part of the linearized operator in an end chart.** Let `u` solve the Floer
equation for the pair-of-pants perturbation of period-one Hamiltonians `H_q` at the point
`w = φ'_q(ζ)` of the end `q`, with `ζ = (s, t)` and `s ≥ 2`, where `φ'_q` is the positive end chart,
and let each `H_q(t)` be `C²`. Then the zeroth-order part `C_end(ζ)` of the linearized operator of
the end datum `H'_q(t) dt` along `u ∘ φ'_q` is `(a - b J) C(w)`, where `C(w)` is the zeroth-order
part of the linearized operator in the coordinate of `ℂ`, `J = J(w, u w)` and
`(a, b) = dφ'_q (1, 0)`. -/
theorem floerLinearizationCoeff_comp_positiveEndChart_apply (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ ζ.1) (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) (v : V) :
    ω.floerLinearizationCoeff
        (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q) ζ v =
      (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ω.floerLinearizationCoeff
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (positiveEndChart q ζ) v -
        (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 • J (positiveEndChart q ζ)
          (u (positiveEndChart q ζ)) (ω.floerLinearizationCoeff
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            u (positiveEndChart q ζ) v) := by
  -- On constant sections the two linearized operators are their zeroth-order parts, so the
  -- chart identity `D_end = a D - b J D` becomes `C_end = (a - b J) C`.
  have h := ω.floerLinearization_comp_positiveEndChart hH hHs (ξ := fun _ ↦ v) hζ hu
    (differentiableAt_const v) hfl
  have hc : (fun _ : ℝ × ℝ ↦ v) ∘ positiveEndChart q = fun _ ↦ v := rfl
  rw [hc, floerLinearization_eq_add, floerLinearization_eq_add, stdComplexLineReal_eq] at h
  simpa only [fderiv_const_apply, FunLike.coe_zero, Pi.zero_apply, map_zero, zero_add,
    Function.comp_apply] using h

/-- **The zeroth-order part of the linearized operator on an end.** Let `u` solve the Floer
equation for the pair-of-pants perturbation of period-one Hamiltonians `H_q` at the point
`w = φ'_q(ζ)` of the end `q`, with `ζ = (s, t)` and `s ≥ 2`, where `φ'_q` is the positive end chart,
and let each `H_q(t)` be `C²`. Then the zeroth-order part `C(w)` of the linearized operator in the
coordinate of `ℂ` is controlled by the zeroth-order part `C_end(ζ)` of the linearized operator of
the end datum `H'_q(t) dt` along `u ∘ φ'_q`, with the factor `2π |w - c_q|` of the chart:
`2π |w - c_q| ‖C(w)‖ ≤ (1 + ‖J(w, u w)‖) ‖C_end(ζ)‖`. -/
theorem mul_norm_floerLinearizationCoeff_positiveEndChart_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ ζ.1) (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    2 * π * ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ *
        ‖ω.floerLinearizationCoeff (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (positiveEndChart q ζ)‖ ≤
      (1 + ‖(J (positiveEndChart q ζ)
          (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap‖) *
        ‖ω.floerLinearizationCoeff
          (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q) ζ‖ := by
  rw [← positiveEndChartScale_apply]
  set w := positiveEndChart q ζ
  set C := ω.floerLinearizationCoeff (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u w
  set Ce := ω.floerLinearizationCoeff
    (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q) ζ
  set Jw := J w (u w)
  set a := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1
  set b := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2
  set r := positiveEndChartScale q ζ
  have hid (v : V) : Ce v = a • C v - b • Jw (C v) :=
    ω.floerLinearizationCoeff_comp_positiveEndChart_apply hH hHs hζ hu hfl v
  -- The Jacobian of the positive end chart is `a² + b² = (2π |w - c_q|)²`.
  have hdet : a ^ 2 + b ^ 2 = r ^ 2 := (sq_positiveEndChartScale_eq_sq_add_sq q ζ).symm
  have hr : 0 < r := positiveEndChartScale_pos q ζ
  exact Jw.mul_opNorm_le_of_eq_smul_sub_smul hid hdet hr

/-- **The coefficient field on conformal jets on an end.** Let the perturbation `(K_s, K_t)` be the
pair-of-pants perturbation of period-one `C²` Hamiltonians `H_q` at the point `w = φ'_q(ζ)` of the
end `q`, with `ζ = (s, t)` and `s ≥ 2`, let `u` solve the Floer equation at `w`, and let the
structures at `w` be `J(w, ·) = J_q(t)`. If `B` bounds the coefficient field on jets of the end
datum `H'_q(t) dt`, with the structures `J_q(t)`, along `u ∘ φ'_q` at `ζ`, then the coefficient
field on the conformal jets of the cylindrical weight is at most `1 + B + (1 + B) B / 2π` at `w`.
The pair-of-pants perturbation itself is the case `K_s`, `K_t` equal to its components. -/
theorem norm_floerConformalJetCoeff_positiveEndChart_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1)
    (hJz : J (positiveEndChart q ζ) = Jq ζ.2)
    (hKs : Ks (positiveEndChart q ζ) = fun x ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x 1)
    (hKt : Kt (positiveEndChart q ζ) = fun x ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x
        Complex.I)
    (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ‖ ≤ B) :
    ‖ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
      (positiveEndChart q ζ)‖ ≤ 1 + B + (1 + B) * B / (2 * π) := by
  rw [ω.floerConformalJetCoeff_congr_data _ u rfl
    (Ks' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    hKs hKt]
  rw [ω.perturbedFDeriv_congr u hKs hKt
    (Ks' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)]
    at hfl
  -- The zeroth-order part `C(w)` is at most `(1 + B) B / (2π d)` with `d = |w - c_q|`, and the
  -- weight is at least `d⁻²`.
  have hne := equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ
  refine (ω.norm_floerConformalJetCoeff_le_of_norm_floerJetCoeff_comp_le
    (ρ := cylindricalWeight) (by simp only [hJz]) hB
    (ω.mul_norm_floerLinearizationCoeff_positiveEndChart_le hH hHs hζ hu hfl) ?_
    (inv_nonneg.2 (mul_pos two_pos pi_pos).le)).trans_eq (by ring)
  rw [← mul_assoc, inv_mul_cancel₀ (mul_pos two_pos pi_pos).ne', one_mul]
  exact inv_sqrt_cylindricalWeight_le_norm_sub_endCenter q hne

/-- **The linearized operator along a pair of pants is bounded on `W^{1,2}`.** Let `H_q` be jointly
`C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, let `(J, K_s, K_t)` be Floer
data on `S` with `J` `C¹` and `K_s`, `K_t` `C²` along the graph of `u`, and let `u` be `C¹` on `S`.
Suppose that beyond a height `T ≥ 2` of every end `q`, read in the positive end chart `φ'_q`, the
structures are a `C¹` family `J_q(t)` of the end coordinate `t`, the perturbation is the
pair-of-pants perturbation of `H`, and `u` solves the Floer equation, while over the band
`t ∈ [0, 1]` of angular width one `u` is bounded and so is the slice defect
`∂t (u ∘ φ'_q) - X_{H'_q(t)}(u ∘ φ'_q)` of the end datum. Then the coefficient field of the
linearized Floer operator on the jets of the cylindrical weight of `S` is essentially bounded on
`S`, so that `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from
`W^{1,2}_0(S, V)` to `L²(S, V)`. The pair-of-pants perturbation itself is the case `K_s`, `K_t`
equal to its components on all of `S`. -/
theorem memLp_floerConformalJetCoeff_pairOfPants (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q)))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (uncurry fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {Jq : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJq : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Jq q p.1 p.2).toLinearMap.toContinuousLinearMap)
    {T : ℝ} (hT : 2 ≤ T) (hJend : ∀ q ζ, T ≤ ζ.1 → J (positiveEndChart q ζ) = Jq q ζ.2)
    (hKend : ∀ q ζ, T ≤ ζ.1 →
      Ks (positiveEndChart q ζ) = (fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x 1) ∧
      Kt (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x Complex.I)
    (hfl : ∀ q ζ, T ≤ ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    {Cu Cδ : ℝ} (hub : ∀ q ζ, T ≤ ζ.1 → ζ.2 ∈ Icc 0 1 → ‖u (positiveEndChart q ζ)‖ ≤ Cu)
    (hδ : ∀ q ζ, T ≤ ζ.1 → ζ.2 ∈ Icc 0 1 → ‖sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
      (u ∘ positiveEndChart q) ζ‖ ≤ Cδ) :
    MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
      (volume.restrict thricePuncturedSphereReal) := by
  have hcont : ContinuousOn (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) thricePuncturedSphereReal :=
    ω.continuousOn_floerConformalJetCoeff isWeight_cylindricalWeight hJ hKs hKt hu
  -- On each end the coefficient field of the end datum is bounded, by the estimate on cylinders.
  choose Bq hBq using fun q ↦ ω.exists_forall_norm_floerJetCoeff_le
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (hJq q) (u ∘ positiveEndChart q) Cu Cδ
  set B := ∑ q, |Bq q|
  have hBqB (q : Puncture) : Bq q ≤ B := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun q' ↦ |Bq q'|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ q))
  -- Beyond the height `T` of the end `q`, the data are the pair-of-pants data.
  refine memLp_top_of_continuousOn_of_norm_positiveEndChart_le hcont (T := T)
    (M := 1 + B + (1 + B) * B / (2 * π)) fun q ζ hζ1 hζ2 ↦ ?_
  have hζT : T ≤ ζ.1 := le_of_lt hζ1
  have hζI : ζ.2 ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hζ2
  have hz : positiveEndChart q ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (by linarith)
  exact ω.norm_floerConformalJetCoeff_positiveEndChart_le hH
    (fun t ↦ (hHs q).comp (contDiff_const.prodMk contDiff_id)) (hT.trans hζT) (hJend q ζ hζT)
    (hKend q ζ hζT).1 (hKend q ζ hζT).2
    ((hu.differentiableOn one_ne_zero).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds hz)) (hfl q ζ hζT)
    ((hBq q ζ hζI (hub q ζ hζT hζI) (hδ q ζ hζT hζI)).trans (hBqB q))

end SymplecticForm

end TauCeti
