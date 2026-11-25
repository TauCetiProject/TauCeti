/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Operator
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Transfer
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Asymptotic
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The linearized operator of a pair of pants along an end chart and its end model

Let `u` be a map of the pair of pants `S = ℂ ∖ {0, 1}` into a finite-dimensional symplectic vector
space `(V, ω)` which, far out on the end `q`, solves the Floer equation for the pair-of-pants
perturbation of period-one Hamiltonians `H_q` and structures `J(φ'_q(s, t), ·) = J_q(t)`, where
`φ'_q` is the positive end chart. Its linearized operator `D_u` acts on `W^{1,2}_0(S, V)` through
the coefficient field `M` on the conformal jets `(√ρ ξ, ∂s ξ, ∂t ξ)` of the cylindrical weight `ρ`
(`TauCeti.SymplecticForm.floerConformalJetCoeff`). Transferring sections of the cylinder to `S`
along `φ'_q` with a cutoff `β` (`TauCeti.Floer.endTransfer`) turns `D_u` into the first-order
operator on the strip whose coefficient field at `ζ` is `M(φ'_q(ζ))` composed with the jet
coefficient of the transfer `TauCeti.Floer.endTransferCoeff q β ζ`
(`TauCeti.Floer.jetOperator_endTransfer`). This file identifies that coefficient field on the end
and shows that it converges to that of a model operator: the stationary cylinder operator at the
asymptotic orbit followed by a pointwise rotation. This is what the ends contribute to a parametrix
of `D_u` spliced from inverses of its end models.

* **The operator along the end chart.** Where `β = 1` and `dβ = 0`, at a point `ζ = (s, t)` with
  `s ≥ 2`, the coefficient field on the strip is
  `r⁻¹ (a + b J(φ'_q(ζ), u(φ'_q(ζ)))) ∘ M_end(ζ)`
  (`TauCeti.SymplecticForm.floerConformalJetCoeff_positiveEndChart_comp_endTransferCoeff`). Here
  `M_end` is the coefficient field on jets of the linearized operator along `u ∘ φ'_q` of the end
  datum `H'_q(t) dt` with the structures `J(φ'_q(·), ·)`, `(a, b) = dφ'_q (1, 0)` and
  `r = 2π |φ'_q(ζ) - c_q|` is the conformal scale of the chart. Since `φ'_q` is holomorphic,
  `D_end (ξ ∘ φ'_q) = (a - b J) (D_u ξ) ∘ φ'_q`, and `(a - b J)⁻¹ = (a + b J) / r²`; the factor `r`
  of the `L²` isometry `TauCeti.Floer.positiveEndChartLp` leaves `(a + b J) / r`, a rotation by the
  structure `J`.
* **The end model.** If the loops of `u ∘ φ'_q` converge uniformly to a one-periodic orbit `x_q` of
  `H'_q` and the slice defect `∂t (u ∘ φ'_q) - X_{H'_q}(u ∘ φ'_q)` tends uniformly to zero, then
  far out on the end this coefficient field is uniformly close to
  `r⁻¹ (a + b J_q(t, x_q(t))) ∘ M_q(t)`, where `M_q` is the coefficient field of the stationary
  cylinder operator `∂s + J_q(t, x_q(t)) (∂t - dX_{H'_q(t)}(x_q(t)))` at the orbit
  (`eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt`, in the namespace
  `TauCeti.SymplecticForm`).
  The end Floer data enter only through the end model of the cylinder,
  `TauCeti.SymplecticForm.eventually_forall_norm_floerJetCoeff_sub_stationaryJetCoeff_lt`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on real Cauchy–Riemann operators on surfaces with cylindrical ends.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the asymptotic operators at the ends.
-/

public section

noncomputable section

open Set Function Filter Real TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **The linearized operator of a pair of pants along an end chart.** Let `u` solve the Floer
equation for the pair-of-pants perturbation of period-one `C²` Hamiltonians `H_q` at the point
`w = φ'_q(ζ)` of the end `q`, with `ζ = (s, t)` and `s ≥ 2`, and let the cutoff `β` be `1` with
vanishing derivative at `w`. Then the coefficient field on conformal jets at `w`, composed with the
jet coefficient of the transfer along `φ'_q`, is `r⁻¹ (a + b J)` composed with the coefficient field
on jets at `ζ` of the linearized operator along `u ∘ φ'_q` of the end datum `H'_q(t) dt`, where
`J = J(w, u w)`, `(a, b) = dφ'_q (1, 0)` and `r` is the conformal scale of the chart. -/
theorem floerConformalJetCoeff_positiveEndChart_comp_endTransferCoeff (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ ζ.1) (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hβ : β (positiveEndChart q ζ) = 1) (hdβ : fderiv ℝ β (positiveEndChart q ζ) = 0) :
    (ω.floerConformalJetCoeff cylindricalWeight
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) =
      ((positiveEndChartScale q ζ)⁻¹ •
          ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ContinuousLinearMap.id ℝ V +
            (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 • (J (positiveEndChart q ζ)
              (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap)).comp
        (ω.floerJetCoeff
          (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q) ζ) := by
  have hr := positiveEndChartScale_pos q ζ
  -- The weight is positive at `φ'_q(ζ)`, which is not the center of the end.
  have hρ : 0 < √(cylindricalWeight (positiveEndChart q ζ)) := by
    have hd := norm_pos_iff.2
      (sub_ne_zero.2 (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ))
    exact Real.sqrt_pos.2 ((inv_pos.2 (pow_pos hd 2)).trans_le
      (inv_norm_sub_endCenter_sq_le_cylindricalWeight q _))
  -- The Jacobian of the chart is `a² + b² = r²`.
  have hdet := sq_positiveEndChartScale_eq_sq_add_sq q ζ
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, floerConformalJetCoeff_apply, endTransferCoeff_apply,
    floerJetCoeff_apply, Function.comp_apply, smul_apply, add_apply,
    ContinuousLinearMap.id_apply, hβ, hdβ, zero_apply, mul_zero, zero_smul, zero_add, one_mul,
    ω.floerLinearizationCoeff_comp_positiveEndChart_apply hH hHs hζ hu hfl v.1, map_smul,
    LinearMap.coe_toContinuousLinearMap', smul_smul]
  have hJJ (x : V) : (J (positiveEndChart q ζ) (u (positiveEndChart q ζ))).toLinearMap
      ((J (positiveEndChart q ζ) (u (positiveEndChart q ζ))).toLinearMap x) = -x :=
    (J (positiveEndChart q ζ) (u (positiveEndChart q ζ))).apply_apply x
  generalize (J (positiveEndChart q ζ) (u (positiveEndChart q ζ))).toLinearMap = L at hJJ ⊢
  generalize ω.floerLinearizationCoeff (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
    (positiveEndChart q ζ) v.1 = c
  generalize (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 = a at hdet ⊢
  generalize (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 = b at hdet ⊢
  generalize positiveEndChartScale q ζ = r at hr hdet ⊢
  generalize √(cylindricalWeight (positiveEndChart q ζ)) = ρ at hρ ⊢
  simp only [map_add, map_sub, map_smul, hJJ, smul_add, smul_sub, smul_neg, smul_smul]
  have h₁ : ρ⁻¹ * (r * (ρ * 1)) = r := by field_simp
  have h₂ : r⁻¹ * (a * a) + r⁻¹ * (b * b) = r := by
    field_simp
    linear_combination -hdet
  linear_combination (norm := module) h₁ • c - h₂ • c

/-- **Pointwise comparison with an end model.** Let the Floer data at the point `w = φ'_q(ζ)` of the
end `q`, with `ζ = (s, t)` and `s ≥ 2`, be the structures `J_q(t)` and the pair-of-pants
perturbation of period-one `C²` Hamiltonians `H_q`, let `u` be differentiable and solve the Floer
equation at `w`, and let the cutoff `β` be `1` with vanishing derivative at `w`. For a loop `x` and
a loop `S_t` of endomorphisms, the coefficient field on conformal jets at `w`, composed with the jet
coefficient of the transfer along `φ'_q`, differs from `r⁻¹ (a + b J_q(t, x(t)))` composed with the
coefficient field `M` of the stationary cylinder operator `∂s + J_q(t, x(t)) (∂t - S_t)` by at most
`(1 + ‖J_q(t, u w)‖) ‖F - M‖ + ‖J_q(t, u w) - J_q(t, x(t))‖ ‖M‖`, where `F` is the coefficient field
on jets at `ζ` of the linearized operator along `u ∘ φ'_q` of the end datum `H'_q(t) dt`,
`(a, b) = dφ'_q (1, 0)` and `r` is the conformal scale of the chart. -/
theorem norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1)
    (hJz : J (positiveEndChart q ζ) = Jq ζ.2)
    (hKs : Ks (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
      (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x 1)
    (hKt : Kt (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
      (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x Complex.I)
    (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hβ : β (positiveEndChart q ζ) = 1) (hdβ : fderiv ℝ β (positiveEndChart q ζ) = 0)
    (x : ℝ → V) (S : ℝ → V →L[ℝ] V) :
    ‖(ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) -
        ((positiveEndChartScale q ζ)⁻¹ •
          ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ContinuousLinearMap.id ℝ V +
            (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 •
              (Jq ζ.2 (x ζ.2)).toLinearMap.toContinuousLinearMap)).comp
          (Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S ζ)‖ ≤
      (1 + ‖(Jq ζ.2 (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap‖) *
          ‖ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ -
            Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S ζ‖ +
        ‖(Jq ζ.2 (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap -
            (Jq ζ.2 (x ζ.2)).toLinearMap.toContinuousLinearMap‖ *
          ‖Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S ζ‖ := by
  rw [ω.perturbedFDeriv_congr u
    (Ks' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    hKs hKt] at hfl
  rw [ω.floerConformalJetCoeff_congr_data _ u rfl
    (Ks' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    hKs hKt,
    ω.floerConformalJetCoeff_positiveEndChart_comp_endTransferCoeff hH hHs hζ hu hfl hβ hdβ,
    ω.floerJetCoeff_congr_data (u ∘ positiveEndChart q)
      (J' := fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap) (Ks' := fun _ _ ↦ 0)
      (Kt' := fun w ↦ positiveEndHamiltonian H q w.2) (by simp only [hJz]) rfl rfl, hJz]
  -- Split the difference into the change of operator and the change of rotation.
  set F := ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2) (u ∘ positiveEndChart q) ζ
  set M := Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S ζ
  set a := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1
  set b := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2
  set r := positiveEndChartScale q ζ
  set Lu := (Jq ζ.2 (u (positiveEndChart q ζ))).toLinearMap.toContinuousLinearMap
  set Lx := (Jq ζ.2 (x ζ.2)).toLinearMap.toContinuousLinearMap
  have hr : 0 < r := positiveEndChartScale_pos q ζ
  have ha : |a| ≤ r := abs_fst_fderiv_positiveEndChart_le q ζ
  have hb : |b| ≤ r := abs_snd_fderiv_positiveEndChart_le q ζ
  have hsplit : (r⁻¹ • (a • ContinuousLinearMap.id ℝ V + b • Lu)).comp F -
      (r⁻¹ • (a • ContinuousLinearMap.id ℝ V + b • Lx)).comp M =
        (r⁻¹ • (a • ContinuousLinearMap.id ℝ V + b • Lu)).comp (F - M) +
          ((r⁻¹ * b) • (Lu - Lx)).comp M := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp]
    module
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)) <;>
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  · -- The rotation `r⁻¹ (a + b L)` has norm at most `1 + ‖L‖`, since `|a|, |b| ≤ r`.
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr]
    calc ‖a • ContinuousLinearMap.id ℝ V + b • Lu‖
        ≤ |a| * ‖ContinuousLinearMap.id ℝ V‖ + |b| * ‖Lu‖ :=
          (norm_add_le _ _).trans (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])
      _ ≤ r * 1 + r * ‖Lu‖ := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = r * (1 + ‖Lu‖) := by ring
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hr]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rwa [inv_mul_le_iff₀ hr, mul_one]

/-- **The end model of the linearized operator of a pair of pants.** Let `(J, K_s, K_t)` be Floer
data on the pair of pants which beyond a height `T` of the end `q`, read in the positive end chart
`φ'_q`, are the structures `J_q(t)` of a `C¹` family and the pair-of-pants perturbation of
period-one Hamiltonians `H_q` with `H_q` jointly `C²`, and let `u` be differentiable and solve the
Floer equation there. Let the loops of `u ∘ φ'_q` converge uniformly to a one-periodic orbit `x` of
the end Hamiltonian `H'_q`, with slice defect `∂t (u ∘ φ'_q) - X_{H'_q}(u ∘ φ'_q)` tending
uniformly to zero, and let the cutoff `β` be `1` with vanishing derivative beyond the height `T`.
Then for every `ε > 0` and every sufficiently large `s`, at every `t ∈ [0, 1]`, the coefficient
field on conformal jets at `φ'_q(s, t)`, composed with the jet coefficient of the transfer along
`φ'_q`, is within `ε` of `r⁻¹ (a + b J_q(t, x(t)))` composed with the coefficient field of the
stationary cylinder operator `∂s + J_q(t, x(t)) (∂t - dX_{H'_q(t)}(x(t)))`, where
`(a, b) = dφ'_q (1, 0)` and `r` is the conformal scale of the chart at `(s, t)`. -/
theorem eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) {q : Puncture}
    (hHs : ContDiff ℝ 2 (uncurry (H q)))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {β : ℝ × ℝ → ℝ} {T : ℝ}
    (hJend : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → J (positiveEndChart q ζ) = Jq ζ.2)
    (hKend : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 →
      Ks (positiveEndChart q ζ) = (fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x 1) ∧
      Kt (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x Complex.I)
    (hu : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hβ : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 →
      β (positiveEndChart q ζ) = 1 ∧ fderiv ℝ β (positiveEndChart q ζ) = 0)
    {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (positiveEndChart q (s, t))).comp (endTransferCoeff q β (s, t)) -
        ((positiveEndChartScale q (s, t))⁻¹ •
          ((fderiv ℝ (positiveEndChart q) (s, t) (1, 0)).1 • ContinuousLinearMap.id ℝ V +
            (fderiv ℝ (positiveEndChart q) (s, t) (1, 0)).2 •
              (Jq t (x t)).toLinearMap.toContinuousLinearMap)).comp
          (Floer.stationaryJetCoeff (fun t ↦ Jq t (x t))
            (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (x t))
            (s, t))‖ < ε := by
  set Jc : ℝ × V → V →L[ℝ] V := fun p ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap
  set S : ℝ → V →L[ℝ] V :=
    fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (x t)
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hJx : Continuous fun t ↦ Jc (t, x t) := hJq.continuous.comp (continuous_id.prodMk hxc)
  have hS : Continuous S := (continuous_fderiv_slice_right
    (f := fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1)
      (contDiff_uncurry_positiveEndHamiltonian hHs))).comp (continuous_id.prodMk hxc)
  -- The model and the structure along the orbit are bounded over a period.
  obtain ⟨BM, hBM⟩ := (isCompact_singleton.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := {(0 : ℝ)} ×ˢ Icc (0 : ℝ) 1)
    (Floer.continuous_stationaryJetCoeff hJx hS).continuousOn
  obtain ⟨BJ, hBJ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hJx.continuousOn
  set B := |BJ| + |BM| + 2
  have hB : 0 < B := by positivity
  -- Far out, the structures along `u ∘ φ'_q` are uniformly close to those along the orbit, and
  -- the operator of the end datum is uniformly close to the stationary model.
  have hJu := Metric.tendstoUniformlyOn_iff.1 ((isCompact_Icc.image
    (continuous_id.prodMk hxc)).comp_tendstoUniformlyOn (g := Jc)
    (fun _ _ ↦ hJq.continuous.continuousAt) hux.graph) (min 1 (ε / (2 * B))) (by positivity)
  have hFM := ω.eventually_forall_norm_floerJetCoeff_sub_stationaryJetCoeff_lt hJq
    (contDiff_uncurry_positiveEndHamiltonian hHs) isCompact_Icc hx hux hδ
    (by positivity : 0 < ε / (2 * B))
  filter_upwards [eventually_ge_atTop (max T 2), hJu, hFM] with s hs hsJ hsF t ht
  have hsT : T ≤ (s, t).1 := (le_max_left _ _).trans hs
  obtain ⟨hKsq, hKtq⟩ := hKend (s, t) hsT
  obtain ⟨hβ₁, hβ₂⟩ := hβ (s, t) hsT
  refine (ω.norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_le hH
    (fun t ↦ hHs.comp (contDiff_const.prodMk contDiff_id)) ((le_max_right _ _).trans hs)
    (hJend (s, t) hsT) hKsq hKtq (hu (s, t) hsT) (hfl (s, t) hsT) hβ₁ hβ₂ x S).trans_lt ?_
  have hJ' : ‖Jc (t, u (positiveEndChart q (s, t))) - Jc (t, x t)‖ < min 1 (ε / (2 * B)) := by
    simpa only [dist_eq_norm, norm_sub_rev, id_eq] using hsJ t ht
  -- The model at `(s, t)` is the model at `(0, t)`.
  have hM : ‖Floer.stationaryJetCoeff (fun t ↦ Jq t (x t)) S (s, t)‖ ≤ B := by
    rw [Floer.stationaryJetCoeff_eq_of_snd_eq (z := (s, t)) (z' := (0, t)) rfl]
    linarith [hBM (0, t) ⟨rfl, ht⟩, le_abs_self BM, abs_nonneg BJ]
  have hJu : 1 + ‖Jc (t, u (positiveEndChart q (s, t)))‖ ≤ B := by
    linarith [norm_le_norm_add_norm_sub' (Jc (t, u (positiveEndChart q (s, t)))) (Jc (t, x t)),
      hBJ t ht, (lt_min_iff.1 hJ').1, le_abs_self BJ, abs_nonneg BM]
  calc _ ≤ B * ‖_ - _‖ + ε / (2 * B) * B := by
        gcongr
        exact (lt_min_iff.1 hJ').2.le
    _ < B * (ε / (2 * B)) + ε / (2 * B) * B := by
        gcongr
        exact hsF t ht
    _ = ε := by field_simp; ring

end TauCeti.SymplecticForm
