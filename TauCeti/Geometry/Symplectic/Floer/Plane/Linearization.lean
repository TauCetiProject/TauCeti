/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
public import TauCeti.Geometry.Symplectic.Floer.Plane.Basic
public import TauCeti.Geometry.Symplectic.Floer.Energy
import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Geometry.Symplectic.Floer.Plane.ExponentialDecay
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Topology.MetricSpace.Pseudo.Basic
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# The linearized Floer operator on the end of a PSS plane

Let `p` be a PSS plane, with the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a
period-one Hamiltonian `H` on a symplectic vector space `(V, ω)`, and let `u` solve the Floer
equation `(du - X_K)^{0,1} = 0` on the plane for structures `J(z, x)`. The linearized operator
`D_u` along `u` (`TauCeti.SymplecticForm.floerLinearization`) is written in the coordinate
`z = s + i t` of `ℂ`. The Fredholm theory of `D_u` is governed by the end at `∞`, where `u`
converges to its asymptotic orbit and the natural coordinates are those of the end lift
`φ(z) = exp (2π ε z)` (`TauCeti.Floer.PSSPlane.cylindricalEndLift`), in which the end is a
half-cylinder `ε s > a` and the datum is `H(t) dt` from `ε s = 2` on.

* **The operator in end coordinates.** On the part `ε s ≥ 2` of the end, the linearized operator
  along `u ∘ φ` in the direction `ξ ∘ φ`, for the cylindrical datum `K_s = 0`, `K_t = H(t)` and the
  structures `J(φ(·), ·)`, is `a D_u ξ - b J D_u ξ` at `φ(s, t)`, where `a + i b` is the complex
  derivative of `φ` (`TauCeti.SymplecticForm.floerLinearization_comp_realChart_cylindricalEndLift`).
  Its square norm is at most `(1 + B²) det (dφ) ‖D_u ξ‖²` where `‖J‖ ≤ B`
  (`TauCeti.SymplecticForm.norm_floerLinearization_comp_realChart_cylindricalEndLift_sq_le`).
* **The end estimate.** Suppose that the loops of `u` along the end converge uniformly to an orbit
  `x` of `H` starting at a nondegenerate fixed point of the time-one map, while the slice defect
  `∂t (u ∘ φ) - X_{H_t}` tends uniformly to zero, and that far out on the end `J` is a `C¹` family
  `J_e(t)` compatible along `x`. Then the `W^{1,2}` energy of `ξ ∘ φ` over the cylinder is
  controlled by `∫ ‖D_u ξ‖²` over the plane, for every `C²` section `ξ` with compact support far out
  on the end
  (`exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization`, in the namespace
  `TauCeti.SymplecticForm`).
  This is the estimate of the linearized operator of a half-cylinder at a nondegenerate orbit
  (`exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq`)
  carried to the plane: the factor `det (dφ)` is the Jacobian of the end lift, which is injective
  on a strip of angular width one, so changing variables bounds the integral over the cylinder by
  the integral over the plane.

* **Finite-energy planes.** The convergence hypotheses hold for a finite-energy solution with
  image in a compact set, structures cylindrical on the end and nondegenerate orbits, by the
  exponential decay at the end of a PSS plane
  (`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`),
  so the end estimate holds for such planes
  (`exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_finite_energy`).

The end estimate is the end ingredient of the semi-Fredholm estimate of `D_u` on the plane, on
which the counts of PSS planes rest. The target is a symplectic vector space throughout.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Fredholm theory of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1,
  on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)
open scoped Topology NNReal Manifold Real

namespace TauCeti.SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A component of the perturbation of a PSS plane is the Hamiltonian at the angular coordinate,
scaled by a factor depending only on the domain point. -/
private theorem perturbation_apply_eq_mul (p : PSSPlane) (H : ℝ → V → ℝ) (w v : ℂ) :
    (fun x ↦ p.perturbation H w x v) = fun x ↦
      (Real.smoothTransition (p.endSign * (p.endCoord w).re - 1) * p.endAngularForm w v) *
        H (p.endCoord w).im x := by
  funext x
  rw [perturbation_def, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- For a Hamiltonian `H(t)` which is `C²` on `V`, the Hamiltonian vector field of every component
of the perturbation of a PSS plane is differentiable. -/
theorem differentiableAt_hamiltonianVectorField_pssPlanePerturbation (ω : SymplecticForm V)
    {p : PSSPlane} {H : ℝ → V → ℝ} (hHs : ∀ t, ContDiff ℝ 2 (H t)) (w v : ℂ) (y : V) :
    DifferentiableAt ℝ (ω.hamiltonianVectorField (fun x ↦ p.perturbation H w x v)) y := by
  rw [perturbation_apply_eq_mul, funext (ω.hamiltonianVectorField_const_mul _ _)]
  exact ((ω.contDiff_hamiltonianVectorField (n := 1) (hHs _)).differentiable
    (by norm_num) _).const_smul _

/-- **The linearized operator of a PSS plane on its end.** Let `u` solve the Floer equation for
the perturbation of the PSS plane `p` at the point `φ(ζ)` of the end, with `ζ = (s, t)` and
`ε s ≥ 2`, where `φ` is the end lift and `ε = p.endSign`, and let each `H(t)` be `C²` on `V`.
Read in the end coordinates, the linearized operator along `u ∘ φ` in the direction `ξ ∘ φ`, for
the cylindrical datum `H(t) dt` and the structures `J(φ(·), ·)`, is `a D_u ξ - b J D_u ξ`, where
`D_u ξ` is the linearized operator in the coordinate of `ℂ` at `φ(ζ)` and `(a, b) = dφ (1, 0)`. -/
theorem floerLinearization_comp_realChart_cylindricalEndLift (ω : SymplecticForm V)
    {p : PSSPlane} {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ∀ t, ContDiff ℝ 2 (H t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u ξ : ℝ × ℝ → V} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ p.endSign * ζ.1) (hu : DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ))
    (hξ : DifferentiableAt ℝ ξ (realChart p.cylindricalEndLift ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart p.cylindricalEndLift ζ) (u (realChart p.cylindricalEndLift ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (realChart p.cylindricalEndLift ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerLinearization
        (fun ζ' y ↦ (J (realChart p.cylindricalEndLift ζ') y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun ζ' ↦ H ζ'.2) (u ∘ realChart p.cylindricalEndLift)
        (ξ ∘ realChart p.cylindricalEndLift) ζ =
      (fderiv ℝ (realChart p.cylindricalEndLift) ζ stdComplexLineReal).1 • ω.floerLinearization
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ (realChart p.cylindricalEndLift ζ) -
        (fderiv ℝ (realChart p.cylindricalEndLift) ζ stdComplexLineReal).2 •
          J (realChart p.cylindricalEndLift ζ) (u (realChart p.cylindricalEndLift ζ))
            (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
              (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
              (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
              u ξ (realChart p.cylindricalEndLift ζ)) := by
  set w := Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ)
  have hK (v : ℂ) : ∀ᶠ y in 𝓝 (u (realChart p.cylindricalEndLift ζ)),
      DifferentiableAt ℝ (fun x ↦ p.perturbation H w x v) y := .of_forall fun y ↦ by
    rw [perturbation_apply_eq_mul]
    exact ((hHs _).differentiable two_ne_zero y).const_mul _
  have hX (v : ℂ) := ω.differentiableAt_hamiltonianVectorField_pssPlanePerturbation (p := p) hHs
    w v (u (realChart p.cylindricalEndLift ζ))
  -- The linearized operator at `ζ` sees the pulled-back datum only at `ζ`, where it is the
  -- cylindrical datum `H(t) dt`.
  refine Eq.trans ?_ (ω.floerLinearization_perturbationPullback
    ((contDiff_realChart p.contDiff_cylindricalEndLift).differentiable one_ne_zero ζ)
    (isComplexLinearMap_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)) hu hξ (hK 1)
    (hK Complex.I) (hX 1) (hX Complex.I) ((floerOperator_eq_zero_iff ω J _ _ u _).2 hfl))
  refine ω.floerLinearization_congr_data _ _ rfl ?_ ?_
  · rw [perturbationPullback_realChart_cylindricalEndLift_stdComplexLineReal]
  · rw [perturbationPullback_realChart_cylindricalEndLift_stdComplexLineImag p hH]
    funext y
    beta_reduce
    rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The operator in end coordinates, pointwise.** Under the hypotheses of
`floerLinearization_comp_realChart_cylindricalEndLift`, if moreover `‖J‖ ≤ B` at `φ(ζ)`, then the
linearized operator read in end coordinates satisfies
`‖D' (ξ ∘ φ)‖² ≤ (1 + B²) det (dφ) ‖D_u ξ‖²` at `ζ`. -/
theorem norm_floerLinearization_comp_realChart_cylindricalEndLift_sq_le (ω : SymplecticForm V)
    {p : PSSPlane} {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ∀ t, ContDiff ℝ 2 (H t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u ξ : ℝ × ℝ → V} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ p.endSign * ζ.1) (hu : DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ))
    (hξ : DifferentiableAt ℝ ξ (realChart p.cylindricalEndLift ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart p.cylindricalEndLift ζ) (u (realChart p.cylindricalEndLift ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (realChart p.cylindricalEndLift ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖(J (realChart p.cylindricalEndLift ζ)
      (u (realChart p.cylindricalEndLift ζ))).toLinearMap.toContinuousLinearMap‖ ≤ B) :
    ‖ω.floerLinearization
        (fun ζ' y ↦ (J (realChart p.cylindricalEndLift ζ') y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun ζ' ↦ H ζ'.2) (u ∘ realChart p.cylindricalEndLift)
        (ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2 ≤
      (1 + B ^ 2) * ((fderiv ℝ (realChart p.cylindricalEndLift) ζ).det *
        ‖ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ (realChart p.cylindricalEndLift ζ)‖ ^ 2) := by
  rw [ω.floerLinearization_comp_realChart_cylindricalEndLift hH hHs hζ hu hξ hfl,
    ContinuousLinearMap.det,
    (isComplexLinearMap_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)).det_eq_sq_add_sq,
    ContinuousLinearMap.coe_coe]
  set a := (fderiv ℝ (realChart p.cylindricalEndLift) ζ stdComplexLineReal).1
  set b := (fderiv ℝ (realChart p.cylindricalEndLift) ζ stdComplexLineReal).2
  set Jx := J (realChart p.cylindricalEndLift ζ) (u (realChart p.cylindricalEndLift ζ))
  set D := ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    u ξ (realChart p.cylindricalEndLift ζ)
  have h := ContinuousLinearMap.norm_smul_add_smul_apply_sq_le _ hB a (-b) D
  rwa [neg_sq, neg_smul, ← sub_eq_add_neg, mul_assoc] at h

/-- The linearized operator of a PSS plane applied to a `C¹` section `ξ` with compact support in a
set `Ω`, along a map `u` which is `C¹` on `Ω` with `J` also `C¹` along `u` there, is continuous
on the plane and has compact support. -/
private theorem continuous_floerLinearization_perturbation (ω : SymplecticForm V)
    {p : PSSPlane} {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u ξ : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ Ω, ContDiffAt ℝ 1 u z) (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (hξΩ : tsupport ξ ⊆ Ω) :
    Continuous (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ) ∧
    HasCompactSupport (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ) := by
  set D := ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ
  -- The support of `D ξ` lies in that of `ξ`.
  have hsupp : tsupport D ⊆ tsupport ξ := ω.tsupport_floerLinearization_subset _ _ _ u ξ
  have hD : Continuous D := continuous_iff_continuousAt.2 fun z ↦ by
    by_cases hz : z ∈ tsupport ξ
    · exact ω.continuousAt_floerLinearization (hJ z (hξΩ hz))
        ((contDiff_uncurry_perturbation (p := p) hH hHs 1).contDiffAt)
        ((contDiff_uncurry_perturbation (p := p) hH hHs Complex.I).contDiffAt) (hu z (hξΩ hz))
        hξ.contDiffAt
    · exact continuousAt_const.congr
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz (hsupp h)).symm
  exact ⟨hD, hξc.mono' ((subset_tsupport _).trans hsupp)⟩

/-- **The half-cylinder estimate at the end of a PSS plane.** Under the convergence hypotheses of
`exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization`, there are `C₁`,
`B` and `R₀` such that on every band `[a, b]` with `ε s ≥ R₀`, the structure `J_e` is bounded by
`B` along `u ∘ φ`, and the linearized operator of the cylindrical end data along `u ∘ φ` controls
the `W^{1,2}` energy of sections of period one in `t` vanishing on the two boundary slices. -/
private theorem exists_setIntegral_le_mul_setIntegral_floerLinearization_comp_realChart
    (ω : SymplecticForm V) (p : PSSPlane) {H : ℝ → V → ℝ} (hHs : ContDiff ℝ 2 (uncurry H))
    {L : ℝ≥0} (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun q : ℝ × V ↦ (Je q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {r : ℝ} {u : ℝ × ℝ → V}
    (hu : ∀ ζ : ℝ × ℝ, r < p.endSign * ζ.1 → ContDiffAt ℝ 1 (u ∘ realChart p.cylindricalEndLift) ζ)
    (hux : TendstoUniformlyOn
      (fun s t ↦ u (realChart p.cylindricalEndLift (p.endSign * s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
      (u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t)) 0 atTop (Icc 0 1)) :
    ∃ C₁ B R₀ : ℝ, ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s ∈ Icc a b, R₀ ≤ p.endSign * s) →
      (∀ s ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, ‖(Je t (u (realChart p.cylindricalEndLift
        (s, t)))).toLinearMap.toContinuousLinearMap‖ ≤ B) ∧
      ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
        (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ ζ stdComplexLineImag‖ ^ 2 + ‖ξ ζ‖ ^ 2) ≤
          C₁ * ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) ξ ζ‖ ^ 2 := by
  set φ := realChart p.cylindricalEndLift
  -- Far out on the end, in the longitudinal coordinate `s`, means along `l`.
  set l : Filter ℝ := map (p.endSign * ·) atTop
  have hl {P : ℝ → Prop} (h : ∀ᶠ s in l, P s) : ∃ R, ∀ s, R ≤ p.endSign * s → P s := by
    obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_map.1 h)
    exact ⟨R, fun s hs ↦ by simpa [← mul_assoc] using hR _ hs⟩
  have hlr : ∀ᶠ s in l, r < p.endSign * s :=
    eventually_map.2 ((eventually_gt_atTop r).mono fun s hs ↦ by
      rwa [← mul_assoc, endSign_mul_endSign, one_mul])
  have hux' : TendstoUniformlyOn (fun s t ↦ (u ∘ φ) (s, t)) x l (Icc 0 1) :=
    tendstoUniformlyOn_map_iff.2 hux
  obtain ⟨C₁, -, U, hU, hest⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_norm_floerLinearization_sq hX hHs hx hnd
      hJe hJex (u := u ∘ φ) (hlr.mono fun s hs t _ ↦ hu (s, t) hs) hux'
      (tendstoUniformlyOn_map_iff.2 hδ)
  -- A bound for `J_e` along `u ∘ φ` far out on the end, where `u ∘ φ` is close to `x`.
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod ((isCompact_Icc.image hxc).cthickening (r := 1))
    ).exists_bound_of_continuousOn hJe.continuous.continuousOn
  have hBl : ∀ᶠ s in l, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(Je t ((u ∘ φ) (s, t))).toLinearMap.toContinuousLinearMap‖ ≤ B := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hux' 1 one_pos] with s hs t ht
    exact hB (t, _) ⟨ht, Metric.mem_cthickening_of_dist_le _ (x t) 1 _ (mem_image_of_mem x ht)
      (by rw [dist_comm]; exact (hs t ht).le)⟩
  obtain ⟨R₀, hR₀⟩ := hl ((eventually_mem_set.2 hU).and hBl)
  exact ⟨C₁, B, R₀, fun a b hab hR ↦ ⟨fun s hs ↦ (hR₀ s (hR s hs)).2,
    fun ξ hξ hper ha hb ↦ hest hξ hper hab (fun s hs ↦ (hR₀ s (hR s hs)).1) ha hb⟩⟩

/-- **Comparing the two operators on a band.** On a band `[a, b]` of the end where `ε s > r`,
`ε s ≥ 2` and `‖J_e‖ ≤ B` along `u ∘ φ`, the `L²` norm of the linearized operator of the
cylindrical end data along `u ∘ φ` on `ξ ∘ φ` is at most `1 + B²` times the `L²` norm over the
plane of the linearized operator `D_u ξ` of the perturbation of the plane. -/
private theorem setIntegral_norm_floerLinearization_comp_realChart_sq_le (ω : SymplecticForm V)
    {p : PSSPlane} {H : ℝ → V → ℝ} (hH : Periodic H 1) (hHs : ContDiff ℝ 2 (uncurry H))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun q : ℝ × V ↦ (Je q.1 q.2).toLinearMap.toContinuousLinearMap) {r : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, r < p.endSign * ζ.1 → J (realChart p.cylindricalEndLift ζ) = Je ζ.2)
    {u ξ : ℝ × ℝ → V}
    (hu : ∀ z, Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖ → ContDiffAt ℝ 1 u z)
    (hF : ∀ z, Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hξ : ContDiff ℝ 2 ξ)
    (hD : Continuous (ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ))
    (hDs : HasCompactSupport (ω.floerLinearization
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ))
    {a b B : ℝ} (hab : ∀ s ∈ Icc a b, r < p.endSign * s ∧ 2 ≤ p.endSign * s)
    (hB : ∀ s ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, ‖(Je t (u (realChart p.cylindricalEndLift
        (s, t)))).toLinearMap.toContinuousLinearMap‖ ≤ B) :
    ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
        (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift)
        (ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2 ≤
      (1 + B ^ 2) * ∫ z, ‖ω.floerLinearization
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ z‖ ^ 2 := by
  set φ := realChart p.cylindricalEndLift
  set D := ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ
  have hφ : ContDiff ℝ 2 φ := contDiff_realChart p.contDiff_cylindricalEndLift
  have hDi : Integrable fun z ↦ ‖D z‖ ^ 2 := Continuous.integrable_of_hasCompactSupport
    (f := fun z ↦ ‖D z‖ ^ 2) (hD.norm.pow 2) (hDs.comp_left (g := fun v : V ↦ ‖v‖ ^ 2) (by simp))
  have hmem {ζ : ℝ × ℝ} (hζ : ζ ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) :
      Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm (φ ζ)‖ :=
    p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2 (hab _ hζ.1).1
  have hrect : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  -- The operator of the end data along `u ∘ φ` on `ξ ∘ φ` is continuous on the band.
  have hD' : ContinuousOn (fun ζ ↦ ‖ω.floerLinearization
      (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
      (u ∘ φ) (ξ ∘ φ) ζ‖ ^ 2) (Icc a b ×ˢ Icc (0 : ℝ) 1) := fun ζ hζ ↦
    ((ω.continuousAt_floerLinearization
      (J := fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
      (Kt := fun w ↦ H w.2) (hJe.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
      contDiffAt_const (hHs.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt
      ((hu _ (hmem hζ)).comp _ (hφ.contDiffAt.of_le one_le_two))
      ((hξ.comp hφ).contDiffAt.of_le one_le_two)).norm.pow 2).continuousWithinAt
  have hJac : Continuous fun ζ ↦ (fderiv ℝ φ ζ).det :=
    ContinuousLinearMap.continuous_det.comp (hφ.continuous_fderiv two_ne_zero)
  calc _ ≤ ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, (1 + B ^ 2) * ((fderiv ℝ φ ζ).det * ‖D (φ ζ)‖ ^ 2) :=
        setIntegral_mono_on (hD'.integrableOn_compact hrect)
          ((continuous_const.mul (hJac.mul ((hD.norm.pow 2).comp hφ.continuous))).continuousOn
            |>.integrableOn_compact hrect) (measurableSet_Icc.prod measurableSet_Icc)
          fun ζ hζ ↦ by
            -- Beyond `r` the structure on the end is `J_e`, so the two operators agree at `ζ`.
            have hJζ := hJeq ζ (hab _ hζ.1).1
            rw [ω.floerLinearization_congr_data (J' := fun ζ' y ↦
              (J (φ ζ') y).toLinearMap.toContinuousLinearMap) _ _ (by simp [hJζ]) rfl rfl]
            refine ω.norm_floerLinearization_comp_realChart_cylindricalEndLift_sq_le hH
              (fun t ↦ hHs.comp (contDiff_const.prodMk contDiff_id))
              (hab _ hζ.1).2 ((hu _ (hmem hζ)).differentiableAt one_ne_zero)
              (hξ.differentiable two_ne_zero _) (hF _ (hmem hζ)) ?_
            rw [hJζ]
            exact hB ζ.1 hζ.1 ζ.2 hζ.2
    _ = (1 + B ^ 2) * ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ φ ζ).det * ‖D (φ ζ)‖ ^ 2 :=
        integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (p.setIntegral_det_mul_comp_realChart_cylindricalEndLift_le_integral
          (fun _ ↦ sq_nonneg _) hDi a b) (by positivity)

/-- **Structures cylindrical on the end are smooth there.** If from `ε s > r` on the structures
of a PSS plane read in end coordinates are a `Cⁿ` family `J_e(t)`, then `J` is `Cⁿ` jointly in the
domain point and the target point on the part `‖w‖ > exp (2π r)` of the plane. -/
private theorem contDiffAt_of_comp_realChart_cylindricalEndLift_eq (p : PSSPlane)
    {n : WithTop ℕ∞} {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ n fun q : ℝ × V ↦ (Je q.1 q.2).toLinearMap.toContinuousLinearMap) {r : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, r < p.endSign * ζ.1 → J (realChart p.cylindricalEndLift ζ) = Je ζ.2)
    {z : ℝ × ℝ} (hz : Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖) (y : V) :
    ContDiffAt ℝ n (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap)
      (z, y) := by
  -- `J_e` has period one, as the end lift has.
  have hper : Periodic (fun t y ↦ (Je t y).toLinearMap.toContinuousLinearMap) 1 := fun t ↦ by
    have h₁ := hJeq (p.endSign * (r + 1), t + 1) (by simp [← mul_assoc])
    have h₂ := hJeq (p.endSign * (r + 1), t) (by simp [← mul_assoc])
    rw [realChart_cylindricalEndLift_add_one] at h₁
    have h : Je (t + 1) = Je t := h₁.symm.trans h₂
    simp only [h]
  have h := p.contMDiffAt_comp_im_endCoord hper
    (contMDiff_prod_modelWithCornersSelf_iff.2 hJe.contMDiff)
    (norm_pos_iff.1 ((Real.exp_pos _).trans hz)) y
  refine ((contMDiffAt_prod_modelWithCornersSelf_iff.1 h).contDiffAt.comp (z, y)
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).congr_of_eventuallyEq ?_
  -- On the part `‖w‖ > exp (2π r)`, `J w` is `J_e` at the angular coordinate of `w`.
  have hΩ : IsOpen {w : ℝ × ℝ | Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm w‖} :=
    isOpen_lt continuous_const (by fun_prop)
  filter_upwards [(hΩ.preimage continuous_fst).mem_nhds hz] with q hq
  rw [mem_preimage, mem_ofPred_eq] at hq
  have hφ : realChart p.cylindricalEndLift
      (Complex.equivRealProdCLM (p.endCoord (Complex.equivRealProdCLM.symm q.1))) = q.1 := by
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
      p.cylindricalEndLift_endCoord (norm_pos_iff.1 ((Real.exp_pos _).trans hq)),
      ContinuousLinearEquiv.apply_symm_apply]
  have hJq := hJeq _ (p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.1 (by rwa [hφ]))
  rw [hφ] at hJq
  simp [hJq]

/-- **The end estimate on a PSS plane.** Let `u` be `C¹` on a part `‖w‖ > exp (2π r)` of the end
of the PSS plane `p`, solving there the Floer equation for the perturbation of a jointly `C²`
period-one Hamiltonian `H`. Suppose that, with `φ` the end lift and
`ε = p.endSign`, the loops `t ↦ u(φ(ε s, t))` converge uniformly as `s → ∞` to an orbit `x` of
`H` starting at a nondegenerate fixed point of the time-one map, while the slice defect
`∂t (u ∘ φ) - X_{H_t}(u ∘ φ)` at `(ε s, t)` tends uniformly to zero, and that from `ε s > r` on,
`J(φ(s, t)) = J_e(t)` for a `C¹` family `J_e` compatible along `x`. Then there are `C` and `R`
such that every `C²` section `ξ` with compact support in the part `‖w‖ > exp (2π R)` of the end
satisfies

`∫_{ℝ × [0, 1]} (‖∂s (ξ ∘ φ)‖² + ‖∂t (ξ ∘ φ)‖² + ‖ξ ∘ φ‖²) ≤ C ∫ ‖D_u ξ‖²`

for the linearized Floer operator `D_u` of the perturbation of the plane, the integral on the
right being over the plane. -/
theorem exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization
    (ω : SymplecticForm V) (p : PSSPlane) {H : ℝ → V → ℝ} (hH : Periodic H 1)
    (hHs : ContDiff ℝ 2 (uncurry H)) {L : ℝ≥0}
    (hX : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Je : ℝ → V → AlmostComplexStructure V}
    (hJe : ContDiff ℝ 1 fun q : ℝ × V ↦ (Je q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ t, ω.Compatible (Je t (x t))) {r : ℝ}
    (hJeq : ∀ ζ : ℝ × ℝ, r < p.endSign * ζ.1 → J (realChart p.cylindricalEndLift ζ) = Je ζ.2)
    {u : ℝ × ℝ → V}
    (hu : ∀ z, Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖ → ContDiffAt ℝ 1 u z)
    (hF : ∀ z, Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : TendstoUniformlyOn
      (fun s t ↦ u (realChart p.cylindricalEndLift (p.endSign * s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
      (u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t)) 0 atTop (Icc 0 1)) :
    ∃ C R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | Real.exp (2 * π * R) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ z‖ ^ 2 := by
  set φ := realChart p.cylindricalEndLift
  have hφ : ContDiff ℝ 2 φ := contDiff_realChart p.contDiff_cylindricalEndLift
  have huφ (ζ : ℝ × ℝ) (hζ : r < p.endSign * ζ.1) : ContDiffAt ℝ 1 (u ∘ φ) ζ :=
    (hu _ (p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2 hζ)).comp _
      (hφ.contDiffAt.of_le one_le_two)
  obtain ⟨C₁, B, R₀, hfar⟩ :=
    ω.exists_setIntegral_le_mul_setIntegral_floerLinearization_comp_realChart p hHs hX hx hnd hJe
      hJex huφ hux hδ
  set R := max R₀ (max (r + 1) 2)
  have hrR : r + 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h2R : 2 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max C₁ 0 * (1 + B ^ 2), R, fun ξ hξ hξc hξR ↦ ?_⟩
  have hRΩ : {z : ℝ × ℝ | Real.exp (2 * π * R) < ‖Complex.equivRealProdCLM.symm z‖} ⊆
      {z | Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖} :=
    fun z hz ↦ lt_trans (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])) hz
  obtain ⟨hD, hDs⟩ := ω.continuous_floerLinearization_perturbation hH hHs
    (fun z hz ↦ contDiffAt_of_comp_realChart_cylindricalEndLift_eq p hJe hJeq hz (u z))
    (fun z hz ↦ hu z hz) (hξ.of_le one_le_two) hξc (hξR.trans hRΩ)
  set D := ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u ξ
  -- In end coordinates, `ξ ∘ φ` is supported in a band `[a, b]` on which `ε s ≥ R`.
  obtain ⟨a, b, hab, hband, ha, hb, hout⟩ := p.exists_band_of_tsupport_subset hξc hξR
  obtain ⟨hB, hest⟩ := hfar hab fun s hs ↦ (le_max_left _ _).trans (hband s hs)
  calc _ = ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (ξ ∘ φ) ζ stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ φ) ζ stdComplexLineImag‖ ^ 2 + ‖(ξ ∘ φ) ζ‖ ^ 2) := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (MeasurableSet.univ.prod measurableSet_Icc) (prod_mono (subset_univ _) subset_rfl)
          fun ζ hζ ↦ ?_
        have h0 := hout ζ fun h ↦ hζ.2 ⟨h, hζ.1.2⟩
        rw [h0.fderiv_eq, h0.eq_of_nhds]
        simp
    _ ≤ C₁ * ∫ ζ in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
          (fun w y ↦ (Je w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun w ↦ H w.2) (u ∘ φ) (ξ ∘ φ) ζ‖ ^ 2 :=
        hest (hξ.comp hφ) (fun s t ↦ congrArg ξ (realChart_cylindricalEndLift_add_one p s t))
          ha hb
    _ ≤ max C₁ 0 * ((1 + B ^ 2) * ∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ z‖ ^ 2) :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (setIntegral_nonneg
          (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (ω.setIntegral_norm_floerLinearization_comp_realChart_sq_le
            hH hHs hJe hJeq hu hF hξ hD hDs
            (fun s hs ↦ ⟨by linarith [hband s hs], h2R.trans (hband s hs)⟩) hB)
            (le_max_right _ _))
    _ = _ := by ring

/-- **The slice defect at the end of a decaying plane.** If the loops of `u` along the end come
within `A exp (-κ s)` of an orbit `x` of `H` in `C¹`, for large `s`, with `κ > 0`, and the suspended
Hamiltonian vector field is `L`-Lipschitz, then the slice defect `∂t (u ∘ φ) - X_{H_t}(u ∘ φ)` at
`(ε s, t)` tends uniformly to zero as `s → ∞`. -/
private theorem tendstoUniformlyOn_sliceDefect_of_le_exp (ω : SymplecticForm V) (p : PSSPlane)
    {H : ℝ → V → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H))
    {u : ℝ × ℝ → V} {x : ℝ → V} {κ A : ℝ} (hκ : 0 < κ)
    (hdecay : ∀ᶠ s in atTop, ∀ t,
      ‖u (realChart p.cylindricalEndLift (p.endSign * s, t)) - x t‖ +
        ‖fderiv ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        A * Real.exp (-(κ * s))) (S : Set ℝ) :
    TendstoUniformlyOn (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
      (u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t)) 0 atTop S := by
  refine tendstoUniformlyOn_of_dist_le (u := fun s ↦ (1 + L) * A * Real.exp (-(κ * s)))
    (Real.tendsto_const_mul_exp_neg_mul_atTop _ hκ) ?_
  filter_upwards [hdecay] with s hs t _
  set y := u (realChart p.cylindricalEndLift (p.endSign * s, t))
  set d := fderiv ℝ (u ∘ realChart p.cylindricalEndLift) (p.endSign * s, t)
  have hd : ‖d (0, 1) - ω.hamiltonianVectorField (H t) (x t)‖ ≤
      ‖d - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ := by
    simpa using (d - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (ω.hamiltonianVectorField (H t) (x t))).le_opNorm (0, 1)
  -- The Lipschitz bound of the suspended vector field bounds `X_{H_t}`.
  have hX : ‖ω.hamiltonianVectorField (H t) (x t) - ω.hamiltonianVectorField (H t) y‖ ≤
      L * ‖y - x t‖ := by
    rw [norm_sub_rev y]
    simpa [Prod.dist_eq, dist_eq_norm] using hL.dist_le_mul (t, x t) (t, y)
  have hy : ‖y - x t‖ ≤ A * Real.exp (-(κ * s)) := by
    linarith [hs t, norm_nonneg (d -
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t)))]
  rw [Pi.zero_apply, dist_zero_right, sliceDefect_def]
  calc _ ≤ ‖d (0, 1) - ω.hamiltonianVectorField (H t) (x t)‖ +
        ‖ω.hamiltonianVectorField (H t) (x t) - ω.hamiltonianVectorField (H t) y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ A * Real.exp (-(κ * s)) + L * (A * Real.exp (-(κ * s))) := by
        linarith [hs t, mul_le_mul_of_nonneg_left hy L.coe_nonneg, norm_nonneg (y - x t)]
    _ = _ := by ring

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The end estimate on a finite-energy PSS plane.** Let `u` be `C³` on a part `‖w‖ > r` of the
end of the PSS plane `p`, with image in a compact set `K`, solving there the Floer equation for
the perturbation of a jointly `C³` period-one Hamiltonian `H` whose suspended vector field is
globally Lipschitz, with finite energy there. Suppose that the structures are cylindrical there,
`J(w) = J_t` with `t` the angular coordinate of `w`, for a one-periodic `C²` family `J_t` which is
compatible with `ω` on `K`, and that every one-periodic orbit of `H` in `K` is nondegenerate.
Then there are `C` and `R` such that every `C²` section `ξ` with compact support in the part
`‖w‖ > exp (2π R)` of the end satisfies

`∫_{ℝ × [0, 1]} (‖∂s (ξ ∘ φ)‖² + ‖∂t (ξ ∘ φ)‖² + ‖ξ ∘ φ‖²) ≤ C ∫ ‖D_u ξ‖²`

where `φ` is the end lift and `D_u` the linearized Floer operator of the perturbation of the
plane. The end of `u` converges exponentially fast to a nondegenerate orbit
(`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation`), which gives
the hypotheses of `exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization`. -/
theorem exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization_of_finite_energy
    (ω : SymplecticForm V) (p : PSSPlane) {H : ℝ → V → ℝ} (hH : Periodic H 1)
    (hHs : ContDiff ℝ 3 (uncurry H)) {L : ℝ≥0}
    (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension H)) {K : Set V} (hK : IsCompact K)
    {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 2 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    (hJqper : Periodic Jq 1) (hJqK : ∀ t, ∀ y ∈ K, ω.Compatible (Jq t y))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {r : ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      J z = Jq (p.endCoord (Complex.equivRealProdCLM.symm z)).im)
    (hu : ContDiffOn ℝ 3 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (hF : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL 0 1) (x 0)) :
    ∃ C R : ℝ, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | Real.exp (2 * π * R) < ‖Complex.equivRealProdCLM.symm z‖} →
      ∫ ζ in univ ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ z‖ ^ 2 := by
  have hΩ : IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
    isOpen_lt continuous_const (by fun_prop)
  -- The end converges exponentially fast in `C¹` to the stationary cylinder of an orbit `x`.
  obtain ⟨x, hxper, hx, κ, hκ, A, hdecay⟩ :=
    exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_pssPlanePerturbation
      (J := fun z ↦ J z (u z)) p hH hHs hu hK huK hF hE isOpen_univ hJq.contDiffOn hJqper
      (subset_univ _) (fun t y hy ↦ (hJqK t y hy).tames) (fun z hz ↦ by rw [hJ z hz]) hL hnd
  have hrealChart (s t : ℝ) : Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑s + ↑t * Complex.I)) = realChart p.cylindricalEndLift (s, t) := by
    rw [realChart_apply, Complex.equivRealProdCLM_symm_apply]
  simp only [hrealChart] at hdecay
  have hloop (S : Set ℝ) : TendstoUniformlyOn
      (fun s t ↦ u (realChart p.cylindricalEndLift (p.endSign * s, t))) x atTop S :=
    tendstoUniformlyOn_of_dist_le (Real.tendsto_const_mul_exp_neg_mul_atTop A hκ)
      (hdecay.mono fun s hs t _ ↦ by
        rw [dist_eq_norm]
        exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hs t))
  obtain ⟨a, -, hsub⟩ := exists_le_exp_lt_norm_subset 2 r
  -- The orbit stays in `K`, as a limit of loops in `K`.
  have hxK (t : ℝ) : x t ∈ K := by
    refine hK.isClosed.mem_of_tendsto ((hloop {t}).tendsto_at (mem_singleton t)) ?_
    filter_upwards [eventually_gt_atTop a] with s hs
    exact huK _ (hsub (p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2
      (by simpa [← mul_assoc] using hs)))
  -- Far out on the end, `J` is `J_t` in end coordinates.
  have hJeq (ζ : ℝ × ℝ) (hζ : a < p.endSign * ζ.1) :
      J (realChart p.cylindricalEndLift ζ) = Jq ζ.2 := by
    rw [hJ _ (hsub (p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2 hζ)), realChart_apply,
      ContinuousLinearEquiv.symm_apply_apply, apply_im_endCoord_cylindricalEndLift hJqper,
      Complex.equivRealProdCLM_symm_apply_im]
  exact ω.exists_forall_setIntegral_comp_realChart_le_mul_integral_floerLinearization
    p hH (hHs.of_le (by norm_num)) hL hx (hnd x hxper hx hxK) (Je := Jq) (hJq.of_le one_le_two)
    (fun t ↦ hJqK t _ (hxK t)) hJeq
    (fun z hz ↦ (hu.contDiffAt (hΩ.mem_nhds (hsub hz))).of_le (by norm_num))
    (fun z hz ↦ hF z (hsub hz)) (hloop _)
    (tendstoUniformlyOn_sliceDefect_of_le_exp ω p hL hκ hdecay _)

end InnerProductSpace

end TauCeti.SymplecticForm
