/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Geometry.Symplectic.Cayley.Tangent
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The linearized Floer operator under holomorphic changes of domain coordinates

A Riemann surface with cylindrical ends, such as the pair of pants, carries no global coordinate,
and the Fredholm theory of the linearized Floer operator on it is assembled chart by chart: an
affine chart on the compact part, and the cylinder coordinates `(s, t)` on each end, where the
operator converges to a translation-invariant one. This file shows how the coordinate operators of
`TauCeti.Geometry.Symplectic.Floer.Linearization.Basic` change under a holomorphic change of domain
coordinates `φ : ℝ × ℝ → ℝ × ℝ`, so that the operator read in one chart can be compared with the
operator read in another.

Let `dφ_w` be complex linear, so that it is multiplication by a complex number `a + i b`, with
`(a, b) = dφ_w (1, 0)` and `det dφ_w = a² + b²`. The perturbation datum pulls back to
`φ^*K` (`TauCeti.Floer.perturbationPullback`), the almost complex structures to
`J(φ w, ·)`, the map to `u ∘ φ` and the direction to `ξ ∘ φ`. Then:

* **The nonlinear operator.** The Floer operator `F(u) = ∂ₛu - X_{K_s} + J (∂ₜu - X_{K_t})` of the
  pulled-back data is `(a - b J) F(u)(φ w)`
  (`TauCeti.SymplecticForm.floerOperator_perturbationPullback`). Multiplication by `a - b J` is
  multiplication by the complex conjugate of `a + i b` in the complex structure `J`. In
  particular the Floer equation `F(u) = 0` is preserved, as in
  `TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_perturbationPullback`, and since
  `a - b J` is invertible when `dφ_w ≠ 0`, the two equations have the same solutions
  (`TauCeti.SymplecticForm.floerOperator_perturbationPullback_eq_zero_iff`).
* **The linearized operator.** At a solution of the Floer equation, the linearized operator of the
  pulled-back data in the direction `ξ ∘ φ` is again `(a - b J)` times the linearized operator
  in the direction `ξ` at `φ w`
  (`TauCeti.SymplecticForm.floerLinearization_perturbationPullback`). Here the Floer equation is
  needed: the term `(dJ ξ)(∂ₜu - X_{K_t})` of the linearization involves only the `∂ₜ` part of the
  perturbed derivative, and it transforms correctly because `∂ₛu - X_{K_s} = -J (∂ₜu - X_{K_t})`
  and because the derivative of a family of complex structures anticommutes with them
  (`TauCeti.AlmostComplexStructure.mem_tangentSpace_of_hasFDerivAt`).
* **The `L²` norm of the linearized operator is conformally invariant.** For the form
  `g(v, v) = ω(v, J v)` of `TauCeti.SymplecticForm.associatedBilinForm`,
  `g((a - b J) v, (a - b J) v) = (a² + b²) g(v, v)`, so the value of `g` on the linearized operator
  scales by the Jacobian determinant `det dφ_w`
  (`TauCeti.SymplecticForm.associatedBilinForm_floerLinearization_perturbationPullback`). With the
  change of variables formula, the integral of `g(D ξ, D ξ)` over a region is the same computed in
  either chart (`TauCeti.SymplecticForm.integral_associatedBilinForm_floerLinearization_image`).
* **The `L²` norm in the ambient norm.** Since `|a - b J|` is comparable to `|dφ_w|`, with
  constants depending only on a bound `M` for `J`, the ambient norm of the linearized operator
  scales by `det dφ_w` up to the factor `1 + M²`
  (`TauCeti.SymplecticForm.norm_floerLinearization_perturbationPullback_sq_le`,
  `TauCeti.SymplecticForm.det_mul_norm_floerLinearization_sq_le`). Over a set `s` on which `φ` is
  injective, along a solution,
  `∫_s ‖D'_{u ∘ φ}(ξ ∘ φ)‖² ≤ (1 + M²) ∫_{φ '' s} ‖D_u ξ‖²` and conversely
  (`TauCeti.SymplecticForm.setIntegral_norm_floerLinearization_perturbationPullback_sq_le`,
  `TauCeti.SymplecticForm.setIntegral_image_norm_floerLinearization_sq_le`).

* **The formal adjoint.** A covector field `η` is read in the new coordinates as the
  `(0, 1)`-form `η'(w) = η (φ w) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), with `a`, `b`
  and `J` taken at `w`, `φ w` and `(φ w, u (φ w))`. At a solution of the Floer equation, and for
  `φ` of class `C²` and holomorphic near `w`, the formal adjoint of the pulled-back data on `η'` is
  the Jacobian determinant `det dφ_w = a² + b²` times the formal adjoint on `η` at `φ w`
  (`TauCeti.SymplecticForm.floerLinearizationAdjoint_perturbationPullback`). The proof uses the
  zeroth-order coefficient `a C - b J C` of the pulled-back operator
  (`TauCeti.SymplecticForm.floerLinearizationCoeff_perturbationPullback`) and the Cauchy–Riemann
  equations for `w ↦ (a, b)`, which follow from the symmetry of the second derivative of `φ`
  (`TauCeti.isComplexLinearMap_fderiv_fderiv_apply_stdComplexLineReal`). So the transformation
  law of the adjoint carries the factor `a² + b²` that the `L²` pairing `∫ η (D ξ)` acquires under
  the change of variables, and no derivative of `J`.

Away from solutions, `floerLinearization_perturbationPullback_eq_sub` gives the correction
`-b (dJ ξ) F(u)` for endomorphism-valued families with `J² = -1` near the target point.

These are the identities through which the end estimates of the linearized operator on a cylinder
(`TauCeti.Geometry.Symplectic.Floer.EndLinearization`) apply on the ends of a punctured domain.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.1
  and Section 8.1, on the linearized operator and on Hamiltonian perturbations as one-forms on
  the domain.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the linearized operator on surfaces with
  cylindrical ends.
-/

public section

open Filter Function MeasureTheory Set
open scoped Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The covector field `η` read in the coordinates of a holomorphic map `φ`, as a `(0, 1)`-form:
at `w` it is `η (φ w)` composed with `a + b J(φ w, u (φ w))`, multiplication by the complex
derivative `a + i b` of `φ` at `w` in the complex structure `J`, where `(a, b) = dφ_w (1, 0)`.
This is how the formal adjoint transforms under `φ`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_perturbationPullback`). -/
noncomputable def covectorPullback (φ : ℝ × ℝ → ℝ × ℝ) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (u : ℝ × ℝ → V) (η : ℝ × ℝ → V →L[ℝ] ℝ) (w : ℝ × ℝ) : V →L[ℝ] ℝ :=
  (η (φ w)).comp ((fderiv ℝ φ w stdComplexLineReal).1 • (1 : V →L[ℝ] V) +
    (fderiv ℝ φ w stdComplexLineReal).2 • J (φ w) (u (φ w)))

theorem covectorPullback_apply (φ : ℝ × ℝ → ℝ × ℝ) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (u : ℝ × ℝ → V) (η : ℝ × ℝ → V →L[ℝ] ℝ) (w : ℝ × ℝ) :
    covectorPullback φ J u η w =
      (η (φ w)).comp ((fderiv ℝ φ w stdComplexLineReal).1 • (1 : V →L[ℝ] V) +
        (fderiv ℝ φ w stdComplexLineReal).2 • J (φ w) (u (φ w))) :=
  (rfl)

/-- The pulled-back covector field is `a η + b (η ∘ J)`, with `η` and `J` taken at `φ w`. -/
theorem covectorPullback_eq_add (φ : ℝ × ℝ → ℝ × ℝ) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (u : ℝ × ℝ → V) (η : ℝ × ℝ → V →L[ℝ] ℝ) (w : ℝ × ℝ) :
    covectorPullback φ J u η w = (fderiv ℝ φ w stdComplexLineReal).1 • η (φ w) +
      (fderiv ℝ φ w stdComplexLineReal).2 • (η (φ w)).comp (J (φ w) (u (φ w))) := by
  rw [covectorPullback_apply, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {φ : ℝ × ℝ → ℝ × ℝ} {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V} {w : ℝ × ℝ}
  {J : ℝ × ℝ → V → AlmostComplexStructure V}

/-- **Holomorphic changes of coordinates multiply the Floer operator by `a - b J`.** Let `dφ_w` be
complex linear, with `(a, b) = dφ_w (1, 0)`. The Floer operator of `u ∘ φ` for the pulled-back
datum `φ^*K` and the structures `J(φ w, ·)` is `a F(u) - b J F(u)`, where `F(u)` is the Floer
operator of `u` for `K` and `J` at `φ w`. -/
theorem floerOperator_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ω.floerOperator (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 •
          ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 • J (φ w) (u (φ w))
          (ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
            (φ w)) := by
  set P := ω.perturbedFDeriv Ks Kt u (φ w)
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  have hP (v : ℝ × ℝ) : P v = v.1 • P stdComplexLineReal + v.2 • P stdComplexLineImag :=
    P.apply_stdComplexLine v
  -- The perturbed derivative of `u ∘ φ` is `P ∘ dφ_w`.
  have hP' (v : ℝ × ℝ) : fderiv ℝ (u ∘ φ) w v - v.1 • ω.hamiltonianVectorField
      (perturbationPullback φ Ks Kt stdComplexLineReal w) (u (φ w)) - v.2 •
        ω.hamiltonianVectorField (perturbationPullback φ Ks Kt stdComplexLineImag w) (u (φ w)) =
      P (fderiv ℝ φ w v) := by
    rw [← ContinuousLinearMap.comp_apply, ← ω.perturbedFDeriv_perturbationPullback hφ hu hKs hKt,
      perturbedFDeriv_apply, comp_apply]
  have h1 := hP' stdComplexLineReal
  have h2 := hP' stdComplexLineImag
  simp only [stdComplexLineReal_fst, stdComplexLineReal_snd, stdComplexLineImag_fst,
    stdComplexLineImag_snd, one_smul, zero_smul, sub_zero] at h1 h2
  have hLi : fderiv ℝ φ w stdComplexLineImag = (-b, a) := by
    simpa only [ContinuousLinearMap.coe_coe] using hφJ.apply_stdComplexLineImag_eq
  rw [floerOperator_def, floerOperator_def, comp_apply, h1, h2, hLi,
    hP (fderiv ℝ φ w stdComplexLineReal), hP (-b, a),
    ← perturbedFDeriv_apply_stdComplexLineReal ω Ks Kt u (φ w),
    ← perturbedFDeriv_apply_stdComplexLineImag ω Ks Kt u (φ w)]
  simp only [LinearMap.coe_toContinuousLinearMap', map_add, map_smul, map_neg,
    AlmostComplexStructure.apply_apply, neg_smul]
  module

/-- Under a change of domain coordinates `φ` with complex linear derivative `dφ_w ≠ 0`, `u ∘ φ`
solves the Floer equation for the pulled back data at `w` exactly when `u` solves it at `φ w`. -/
theorem floerOperator_perturbationPullback_eq_zero_iff (ω : SymplecticForm V)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hφ₀ : fderiv ℝ φ w ≠ 0) (hu : DifferentiableAt ℝ u (φ w))
    (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ω.floerOperator (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w = 0 ↔
      ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) = 0 := by
  have hφ : DifferentiableAt ℝ φ w := by
    by_contra h
    exact hφ₀ (fderiv_zero_of_not_differentiableAt h)
  rw [ω.floerOperator_perturbationPullback hφ hφJ hu hKs hKt]
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  set F := ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w)
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  -- A complex-linear map of the plane vanishes when its value at `1` does.
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h₀
    have h0 : ((fderiv ℝ φ w : ℝ × ℝ →L[ℝ] ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) = 0 := by
      rw [hφJ.eq_zero_iff_apply_stdComplexLineReal, ContinuousLinearMap.coe_coe]
      exact Prod.ext (pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith : a ^ 2 = 0))
        (pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith : b ^ 2 = 0))
    exact hφ₀ (ContinuousLinearMap.coe_injective
      (h0.trans ContinuousLinearMap.toLinearMap_zero.symm))
  have hF := (J (φ w) (u (φ w))).smul_add_smul_apply_smul_sub_smul a b F
  rw [h, AlmostComplexStructure.apply_zero, smul_zero, smul_zero, add_zero] at hF
  exact (smul_eq_zero.1 hF.symm).resolve_left hab

/-- **Holomorphic changes of coordinates multiply the linearized Floer operator by `a - b J`.** Let
`dφ_w` be complex linear, with `(a, b) = dφ_w (1, 0)`, and let `u` solve the Floer equation at
`φ w`. The linearized Floer operator along `u ∘ φ` for the pulled-back datum `φ^*K` and the
structures `J(φ w, ·)`, in the direction `ξ ∘ φ`, is `a D ξ - b J D ξ`, where `D ξ` is the
linearized operator along `u` for `K` and `J`, in the direction `ξ`, at `φ w`. -/
theorem floerLinearization_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) =
      0) :
    ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 • ω.floerLinearization
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 • J (φ w) (u (φ w)) (ω.floerLinearization
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ (φ w)) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, fderiv ℝ φ w stdComplexLineReal = (a, b) := ⟨_, _, rfl⟩
  have hLi : fderiv ℝ φ w stdComplexLineImag = (-b, a) := by
    simpa only [ContinuousLinearMap.coe_coe, hab] using hφJ.apply_stdComplexLineImag_eq
  -- Derivatives of the reparametrized maps, expanded on the columns of `dφ_w`.
  have hcol {f : ℝ × ℝ → V} (hf : DifferentiableAt ℝ f (φ w)) (v : ℝ × ℝ) :
      fderiv ℝ (f ∘ φ) w v = (fderiv ℝ φ w v).1 • fderiv ℝ f (φ w) stdComplexLineReal +
        (fderiv ℝ φ w v).2 • fderiv ℝ f (φ w) stdComplexLineImag := by
    rw [fderiv_comp w hf hφ, ContinuousLinearMap.comp_apply]
    exact (fderiv ℝ f (φ w)).apply_stdComplexLine (fderiv ℝ φ w v)
  -- The derivative of the family of complex structures anticommutes with it.
  have hdJ (v : V) : fderiv ℝ (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap) (u (φ w))
      (ξ (φ w)) (J (φ w) (u (φ w)) v) = -J (φ w) (u (φ w))
        (fderiv ℝ (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap) (u (φ w))
          (ξ (φ w)) v) :=
    AlmostComplexStructure.mem_tangentSpace_iff_apply.1
      (AlmostComplexStructure.fderiv_mem_tangentSpace (u (φ w)) (ξ (φ w))) v
  -- The Floer equation at `φ w`: `∂ₛu - X_{K_s} = -J (∂ₜu - X_{K_t})`.
  have hP : fderiv ℝ u (φ w) stdComplexLineReal - ω.hamiltonianVectorField (Ks (φ w)) (u (φ w)) =
      -J (φ w) (u (φ w)) (fderiv ℝ u (φ w) stdComplexLineImag -
        ω.hamiltonianVectorField (Kt (φ w)) (u (φ w))) := by
    rw [floerOperator_def] at hF
    exact eq_neg_of_add_eq_zero_left hF
  -- So the slice defect `∂ₜ(u ∘ φ) - X_{(φ^*K)_t}` is `(b J + a) (∂ₜu - X_{K_t})`.
  have hdefect : fderiv ℝ (u ∘ φ) w stdComplexLineImag -
      ω.hamiltonianVectorField (perturbationPullback φ Ks Kt stdComplexLineImag w) (u (φ w)) =
      b • J (φ w) (u (φ w)) (fderiv ℝ u (φ w) stdComplexLineImag -
          ω.hamiltonianVectorField (Kt (φ w)) (u (φ w))) +
        a • (fderiv ℝ u (φ w) stdComplexLineImag -
          ω.hamiltonianVectorField (Kt (φ w)) (u (φ w))) := by
    calc _ = (-b) • (fderiv ℝ u (φ w) stdComplexLineReal -
          ω.hamiltonianVectorField (Ks (φ w)) (u (φ w))) + a • (fderiv ℝ u (φ w)
            stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ w)) (u (φ w))) := by
          rw [hcol hu, ω.hamiltonianVectorField_perturbationPullback (hKs.self_of_nhds)
            hKt.self_of_nhds, hLi]
          module
      _ = _ := by
          rw [hP]
          module
  rw [floerLinearization_def, floerLinearization_def, comp_apply, comp_apply, hdefect,
    ω.fderiv_hamiltonianVectorField_perturbationPullback hKs hKt hXs hXt,
    ω.fderiv_hamiltonianVectorField_perturbationPullback hKs hKt hXs hXt, hcol hξ, hcol hξ, hab,
    hLi]
  simp only [LinearMap.coe_toContinuousLinearMap', map_add, map_sub, map_smul,
    add_apply, smul_apply, hdJ,
    AlmostComplexStructure.apply_apply]
  module

/-- **The linearized Floer operator is conformally covariant in `L²`.** Under the hypotheses of
`TauCeti.SymplecticForm.floerLinearization_perturbationPullback`, the value of the form
`g(v, v) = ω(v, J v)` on the linearized operator of the pulled-back data at `w` is the Jacobian
determinant of `φ` times its value on the linearized operator of the original data at `φ w`. -/
theorem associatedBilinForm_floerLinearization_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) =
      0) :
    ω.associatedBilinForm (J (φ w) (u (φ w)))
        (ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w)
        (ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w) =
      (fderiv ℝ φ w).det * ω.associatedBilinForm (J (φ w) (u (φ w)))
        (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ
          (φ w))
        (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ
          (φ w)) := by
  rw [ω.floerLinearization_perturbationPullback hφ hφJ hu hξ hKs hKt hXs hXt hF,
    ContinuousLinearMap.det, hφJ.det_eq_sq_add_sq, ContinuousLinearMap.coe_coe]
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  set Jx := J (φ w) (u (φ w))
  set D := ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ
    (φ w)
  -- `J (a D - b J D) = b D + a J D`, and only the mixed term of `ω` survives.
  have hJD : Jx (a • D - b • Jx D) = b • D + a • Jx D := by
    simp only [map_sub, map_smul, AlmostComplexStructure.apply_apply, smul_neg]
    abel
  rw [associatedBilinForm_apply, hJD, sub_eq_add_neg, ← neg_smul, ω.apply_smul_add_smul,
    associatedBilinForm_apply]
  ring

/-- **The linearized operator is conformally bounded under a change of coordinates.** Under the
hypotheses of `TauCeti.SymplecticForm.floerLinearization_perturbationPullback`, the norm of the
linearization in the coordinates `w`, squared, is at most `(1 + M²) det dφ_w` times that in the
coordinates `φ w`, squared, where `M` bounds the norm of `J(φ w, u(φ w))`. -/
theorem norm_floerLinearization_perturbationPullback_sq_le (ω : SymplecticForm V) {M : ℝ}
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) =
      0)
    (hM : ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M) :
    ‖ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 ≤
      (1 + M ^ 2) * (fderiv ℝ φ w).det *
        ‖ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ (φ w)‖ ^ 2 := by
  rw [ω.floerLinearization_perturbationPullback hφ hφJ hu hξ hKs hKt hXs hXt hF,
    ContinuousLinearMap.det, hφJ.det_eq_sq_add_sq, ContinuousLinearMap.coe_coe]
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  have h := ContinuousLinearMap.norm_smul_add_smul_apply_sq_le _ hM a (-b)
    (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ (φ w))
  rwa [neg_sq, neg_smul, ← sub_eq_add_neg] at h

/-- **The linearized operator is conformally bounded below under a change of coordinates.** Under
the hypotheses of `TauCeti.SymplecticForm.floerLinearization_perturbationPullback`, `det dφ_w`
times the norm of the linearization in the coordinates `φ w`, squared, is at most `1 + M²` times
that in the coordinates `w`, squared, where `M` bounds the norm of `J(φ w, u(φ w))`. -/
theorem det_mul_norm_floerLinearization_sq_le (ω : SymplecticForm V) {M : ℝ}
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) =
      0)
    (hM : ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M) :
    (fderiv ℝ φ w).det *
        ‖ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ (φ w)‖ ^ 2 ≤
      (1 + M ^ 2) *
        ‖ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 := by
  rw [ω.floerLinearization_perturbationPullback hφ hφJ hu hξ hKs hKt hXs hXt hF,
    ContinuousLinearMap.det, hφJ.det_eq_sq_add_sq, ContinuousLinearMap.coe_coe]
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  set D := ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    Ks Kt u ξ (φ w)
  set D' := a • D - b • J (φ w) (u (φ w)) D
  have hD : a • D' + b • J (φ w) (u (φ w)) D' = (a ^ 2 + b ^ 2) • D :=
    (J (φ w) (u (φ w))).smul_add_smul_apply_smul_sub_smul a b D
  have h : ‖a • D' + b • J (φ w) (u (φ w)) D'‖ ^ 2 ≤ (1 + M ^ 2) * (a ^ 2 + b ^ 2) * ‖D'‖ ^ 2 :=
    ContinuousLinearMap.norm_smul_add_smul_apply_sq_le _ hM a b D'
  rw [hD, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow] at h
  rcases (by positivity : 0 ≤ a ^ 2 + b ^ 2).eq_or_lt with h₀ | hpos
  · rw [← h₀, zero_mul]
    positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc (a ^ 2 + b ^ 2) * ((a ^ 2 + b ^ 2) * ‖D‖ ^ 2) = (a ^ 2 + b ^ 2) ^ 2 * ‖D‖ ^ 2 := by ring
    _ ≤ (1 + M ^ 2) * (a ^ 2 + b ^ 2) * ‖D'‖ ^ 2 := h
    _ = (a ^ 2 + b ^ 2) * ((1 + M ^ 2) * ‖D'‖ ^ 2) := by ring

variable {s : Set (ℝ × ℝ)}

/-- **Invariance of the `L²` norm of the linearized operator under holomorphic changes of
coordinates.** Let `φ` be injective on a measurable set `s`, with complex-linear derivative at the
points of `s`, and let `u` solve the Floer equation on `φ '' s`. Then the integral of
`g(D ξ, D ξ) = ω(D ξ, J D ξ)` over `φ '' s`, for the linearized operator `D` along `u`, equals
the integral over `s` of the same quantity for the linearized operator along `u ∘ φ` of the
pulled-back data, in the direction `ξ ∘ φ`. -/
theorem integral_associatedBilinForm_floerLinearization_image (ω : SymplecticForm V)
    (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hφJ : ∀ w ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w)) (hξ : ∀ w ∈ s, DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ w ∈ s, ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ w ∈ s, ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : ∀ w ∈ s, DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : ∀ w ∈ s, DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ∀ w ∈ s,
      ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) = 0) :
    ∫ z in φ '' s, ω.associatedBilinForm (J z (u z))
        (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z)
        (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z) =
      ∫ w in s, ω.associatedBilinForm (J (φ w) (u (φ w)))
        (ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w)
        (ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w) :=
  integral_image_eq_integral_of_eq_abs_det_smul hs hinj hφ fun w hw ↦ by
    have hdet : 0 ≤ (fderiv ℝ φ w).det := by
      rw [ContinuousLinearMap.det, (hφJ w hw).det_eq_sq_add_sq]
      positivity
    rw [abs_of_nonneg hdet, smul_eq_mul,
      ω.associatedBilinForm_floerLinearization_perturbationPullback (hφ w hw) (hφJ w hw)
        (hu w hw) (hξ w hw) (hKs w hw) (hKt w hw) (hXs w hw) (hXt w hw) (hF w hw)]

/-- **Comparison of the ambient `L²` norm of the linearized operator under holomorphic changes of
coordinates, upper bound.** Let `φ` be injective on a measurable set `s`, with complex linear
derivative, and let `u` solve the Floer equation on `φ '' s`, with `J` bounded by `M` there. Then
the `L²` norm over `s` of the linearization along `u ∘ φ` for the pulled back data, applied to
`ξ ∘ φ`, squared, is at most `1 + M²` times the `L²` norm of `D_u ξ` over `φ '' s`, squared. -/
theorem setIntegral_norm_floerLinearization_perturbationPullback_sq_le (ω : SymplecticForm V)
    {M : ℝ} (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hφJ : ∀ w ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w)) (hξ : ∀ w ∈ s, DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ w ∈ s, ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ w ∈ s, ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : ∀ w ∈ s, DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : ∀ w ∈ s, DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ∀ w ∈ s,
      ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) = 0)
    (hM : ∀ w ∈ s, ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M)
    (hint : IntegrableOn (fun z ↦ ‖ω.floerLinearization
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) (φ '' s)) :
    ∫ w in s, ‖ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 ≤
      (1 + M ^ 2) * ∫ z in φ '' s, ‖ω.floerLinearization
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hφ' (w : ℝ × ℝ) (hw : w ∈ s) : HasFDerivWithinAt φ (fderiv ℝ φ w) s w :=
    (hφ w hw).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hφ' hinj, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity)
    ((((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hφ' hinj _).1
      hint).const_mul (1 + M ^ 2))) ((ae_restrict_iff' hs).2 (Eventually.of_forall fun w hw ↦ ?_))
  dsimp only
  rw [smul_eq_mul, ContinuousLinearMap.det, abs_of_nonneg (hφJ w hw).det_nonneg, ← mul_assoc]
  exact ω.norm_floerLinearization_perturbationPullback_sq_le (hφ w hw) (hφJ w hw) (hu w hw)
    (hξ w hw) (hKs w hw) (hKt w hw) (hXs w hw) (hXt w hw) (hF w hw) (hM w hw)

/-- **Comparison of the ambient `L²` norm of the linearized operator under holomorphic changes of
coordinates, lower bound.** Let `φ` be injective on a measurable set `s`, with complex linear
derivative, and let `u` solve the Floer equation on `φ '' s`, with `J` bounded by `M` there. Then
the `L²` norm of `D_u ξ` over `φ '' s`, squared, is at most `1 + M²` times the `L²` norm over `s`
of the linearization along `u ∘ φ` for the pulled back data, applied to `ξ ∘ φ`, squared. -/
theorem setIntegral_image_norm_floerLinearization_sq_le (ω : SymplecticForm V) {M : ℝ}
    (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hφJ : ∀ w ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w)) (hξ : ∀ w ∈ s, DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ w ∈ s, ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ w ∈ s, ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : ∀ w ∈ s, DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : ∀ w ∈ s, DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ∀ w ∈ s,
      ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) = 0)
    (hM : ∀ w ∈ s, ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M)
    (hint : IntegrableOn (fun w ↦ ‖ω.floerLinearization
      (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
      (perturbationPullback φ Ks Kt stdComplexLineReal)
      (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2) s) :
    ∫ z in φ '' s, ‖ω.floerLinearization
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 ≤
      (1 + M ^ 2) * ∫ w in s, ‖ω.floerLinearization
        (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hφ' (w : ℝ × ℝ) (hw : w ∈ s) : HasFDerivWithinAt φ (fderiv ℝ φ w) s w :=
    (hφ w hw).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hφ' hinj, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity)
    (hint.const_mul (1 + M ^ 2)) ((ae_restrict_iff' hs).2 (Eventually.of_forall fun w hw ↦ ?_))
  dsimp only
  rw [smul_eq_mul, ContinuousLinearMap.det, abs_of_nonneg (hφJ w hw).det_nonneg]
  exact ω.det_mul_norm_floerLinearization_sq_le (hφ w hw) (hφJ w hw) (hu w hw) (hξ w hw)
    (hKs w hw) (hKt w hw) (hXs w hw) (hXt w hw) (hF w hw) (hM w hw)

section

variable {J : ℝ × ℝ → V → V →L[ℝ] V}

/-- **Naturality of the linearized Floer operator.** Let `dφ_w` be complex linear, with
`dφ_w (1, 0) = (a, b)`, let `J² = -1` near `u (φ w)` and let the Hamiltonians be differentiable near
`u (φ w)` with Hamiltonian vector fields differentiable there. Then the linearization along
`u ∘ φ` in the direction `ξ ∘ φ`, for the structures `J ∘ φ` and the pulled-back datum `φ^*K`, is

`D_{u ∘ φ}(ξ ∘ φ)(w) = (a - b J) D_u ξ(φ w) - b (dJ(u) ξ) F_K(u)(φ w)`,

where `J` and its target derivative `dJ` are taken at `(φ w, u (φ w))` and `ξ` at `φ w`. -/
theorem floerLinearization_perturbationPullback_eq_sub (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hJ : ∀ᶠ y in 𝓝 (u (φ w)), J (φ w) y * J (φ w) y = -1) :
    ω.floerLinearization (fun w' ↦ J (φ w')) (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 • ω.floerLinearization J Ks Kt u ξ (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 •
          J (φ w) (u (φ w)) (ω.floerLinearization J Ks Kt u ξ (φ w)) -
        (fderiv ℝ φ w stdComplexLineReal).2 •
          fderiv ℝ (J (φ w)) (u (φ w)) (ξ (φ w)) (ω.floerOperator J Ks Kt u (φ w)) := by
  have hA (v : V) : J (φ w) (u (φ w)) (J (φ w) (u (φ w)) v) = -v := by
    simpa using congrArg (fun L : V →L[ℝ] V ↦ L v) hJ.self_of_nhds
  -- The target derivative of `J` anticommutes with `J`.
  have hanti (v : V) : J (φ w) (u (φ w)) (fderiv ℝ (J (φ w)) (u (φ w)) (ξ (φ w)) v) +
      fderiv ℝ (J (φ w)) (u (φ w)) (ξ (φ w)) (J (φ w) (u (φ w)) v) = 0 := by
    simpa using congrArg (fun L : V →L[ℝ] V ↦ L v)
      (mul_fderiv_add_fderiv_mul_eq_zero (𝕜 := ℝ) hJ (ξ (φ w)))
  -- The slice defect `∂t (u ∘ φ) - X_{(φ^*K)_t}` is the perturbed derivative of `u` on `(-b, a)`.
  have hP := congrArg (fun L : ℝ × ℝ →L[ℝ] V ↦ L stdComplexLineImag)
    (ω.perturbedFDeriv_perturbationPullback hφ hu hKs.self_of_nhds hKt.self_of_nhds)
  simp only [perturbedFDeriv_apply_stdComplexLineImag, ContinuousLinearMap.comp_apply,
    comp_apply] at hP
  -- The column `(-b, a)` in the standard real basis.
  have hφ' : fderiv ℝ φ w stdComplexLineImag =
      -(fderiv ℝ φ w stdComplexLineReal).2 • stdComplexLineReal +
        (fderiv ℝ φ w stdComplexLineReal).1 • stdComplexLineImag := by
    simpa [stdComplexLineReal, stdComplexLineImag] using hφJ.apply_stdComplexLineImag_eq
  simp only [hφ', map_add, map_smul] at hP
  have hξ' := (fderiv ℝ ξ (φ w) : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine
    (fderiv ℝ φ w stdComplexLineReal)
  simp only [ContinuousLinearMap.coe_coe] at hξ'
  -- Expand both linearizations and the Floer operator in these coordinates.
  rw [floerLinearization_def]
  simp only [comp_apply]
  rw [hP, fderiv_comp w hξ hφ, ω.fderiv_hamiltonianVectorField_perturbationPullback hKs hKt hXs hXt,
    ω.fderiv_hamiltonianVectorField_perturbationPullback hKs hKt hXs hXt, floerLinearization_def,
    floerOperator_eq_perturbedFDeriv]
  simp only [ContinuousLinearMap.comp_apply, hξ', hφ', _root_.add_apply, _root_.smul_apply,
    perturbedFDeriv_apply_stdComplexLineImag, perturbedFDeriv_apply_stdComplexLineReal, map_add,
    map_sub, map_smul, hA, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    stdComplexLineReal_fst, stdComplexLineReal_snd, stdComplexLineImag_fst,
    stdComplexLineImag_snd]
  -- What remains is `b (J dJ + dJ J)` applied to the slice defect `∂t u - X_{K_t}(u)`.
  linear_combination (norm := module)
    (fderiv ℝ φ w stdComplexLineReal).2 • hanti (fderiv ℝ u (φ w) stdComplexLineImag) -
      (fderiv ℝ φ w stdComplexLineReal).2 •
        hanti (ω.hamiltonianVectorField (Kt (φ w)) (u (φ w)))

end

/-! ### The formal adjoint -/

section Adjoint

variable {η : ℝ × ℝ → V →L[ℝ] ℝ}

/-- **The zeroth-order coefficient under a holomorphic change of coordinates.** Under the
hypotheses of `floerLinearization_perturbationPullback`, the zeroth-order part of the linearized
operator of the pulled-back data at `w` is `a C - b J C`, for the zeroth-order part `C` of the
linearized operator at `φ w` and `(a, b) = dφ_w (1, 0)`. -/
theorem floerLinearizationCoeff_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w))
    (hKs : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) =
      0) :
    ω.floerLinearizationCoeff (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 • ω.floerLinearizationCoeff
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 •
          ((J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap.comp (ω.floerLinearizationCoeff
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w))) := by
  ext v
  -- On the constant direction `v` the linearized operator is its zeroth-order part.
  have h := ω.floerLinearization_perturbationPullback (J := J) (ξ := fun _ ↦ v) hφ hφJ hu
    (differentiableAt_const v) hKs hKt hXs hXt hF
  have hc : (fun _ : ℝ × ℝ ↦ v) ∘ φ = fun _ ↦ v := rfl
  simp only [hc, floerLinearization_eq_add] at h
  simpa using h

/-- **Holomorphic changes of coordinates multiply the formal adjoint by the Jacobian.** Let `φ` be
`C²` at `w` with complex-linear derivative near `w`, with `(a, b) = dφ_w (1, 0)`, and let `u` solve
the Floer equation at `φ w`. Read the covector field `η` in the new coordinates as the
`(0, 1)`-form `η' (w') = η (φ w') ∘ (a + b J(φ w', u (φ w')))` (`TauCeti.Floer.covectorPullback`).
Then the formal adjoint of the linearized Floer operator of the pulled-back data along `u ∘ φ`,
applied to `η'` at `w`, is `det dφ_w = a² + b²` times the formal adjoint along `u` applied to `η`
at `φ w`. -/
theorem floerLinearizationAdjoint_perturbationPullback (ω : SymplecticForm V)
    (hφ : ContDiffAt ℝ 2 φ w)
    (hφJ : ∀ᶠ w' in 𝓝 w, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w' : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w))
    (hKs : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Ks (φ w)) y)
    (hKt : ∀ᶠ y in 𝓝 (u (φ w)), DifferentiableAt ℝ (Kt (φ w)) y)
    (hXs : DifferentiableAt ℝ (ω.hamiltonianVectorField (Ks (φ w))) (u (φ w)))
    (hXt : DifferentiableAt ℝ (ω.hamiltonianVectorField (Kt (φ w))) (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) =
      0)
    (hη : DifferentiableAt ℝ η (φ w))
    (hJu : DifferentiableAt ℝ (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap) (φ w)) :
    ω.floerLinearizationAdjoint (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ)
        (covectorPullback φ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) w =
      (fderiv ℝ φ w).det • ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η (φ w) := by
  have hφd : DifferentiableAt ℝ φ w := hφ.differentiableAt (by norm_num)
  have hφJw := hφJ.self_of_nhds
  set Ψ : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ (η z).comp (J z (u z)).toLinearMap.toContinuousLinearMap
  set A : ℝ × ℝ → ℝ × ℝ := fun w' ↦ fderiv ℝ φ w' stdComplexLineReal
  -- The pulled-back field is `a (η ∘ φ) + b (Ψ ∘ φ)` for `Ψ = η ∘ J`, and since `J² = -1` its
  -- composite with `J` is `a (Ψ ∘ φ) - b (η ∘ φ)`.
  have hηe : covectorPullback φ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η =
      fun w' ↦ (A w').1 • η (φ w') + (A w').2 • Ψ (φ w') := funext (covectorPullback_eq_add _ _ u η)
  have hηeJ : (fun w' ↦ (covectorPullback φ (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      u η w').comp ((J (φ w') ((u ∘ φ) w')).toLinearMap.toContinuousLinearMap)) =
      fun w' ↦ (A w').1 • Ψ (φ w') - (A w').2 • η (φ w') := by
    ext w' v
    simp [covectorPullback_apply, Ψ, A, sub_eq_add_neg]
  -- The derivatives of the composites with `φ` and of the coefficients `a`, `b`.
  have hA : DifferentiableAt ℝ A w :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  have hηφ : HasFDerivAt (fun w' ↦ η (φ w')) ((fderiv ℝ η (φ w)).comp (fderiv ℝ φ w)) w :=
    hη.hasFDerivAt.comp w hφd.hasFDerivAt
  have hΨφ : HasFDerivAt (fun w' ↦ Ψ (φ w')) ((fderiv ℝ Ψ (φ w)).comp (fderiv ℝ φ w)) w :=
    (hη.clm_comp hJu).hasFDerivAt.comp w hφd.hasFDerivAt
  have ha := hA.hasFDerivAt.fst
  have hb := hA.hasFDerivAt.snd
  have hLi : fderiv ℝ φ w stdComplexLineImag = (-(A w).2, (A w).1) := by
    simpa only [ContinuousLinearMap.coe_coe] using hφJw.apply_stdComplexLineImag_eq
  have hCR := (isComplexLinearMap_fderiv_fderiv_apply_stdComplexLineReal hφ
    hφJ).apply_stdComplexLineImag_eq
  simp only [ContinuousLinearMap.coe_coe] at hCR
  have hdet : (fderiv ℝ φ w).det = (A w).1 ^ 2 + (A w).2 ^ 2 := by
    rw [ContinuousLinearMap.det, hφJw.det_eq_sq_add_sq, ContinuousLinearMap.coe_coe]
  rw [floerLinearizationAdjoint_def, floerLinearizationAdjoint_def, hηeJ, hηe,
    ((ha.fun_smul hηφ).fun_add (hb.fun_smul hΨφ)).fderiv,
    ((ha.fun_smul hΨφ).fun_sub (hb.fun_smul hηφ)).fderiv,
    ω.floerLinearizationCoeff_perturbationPullback hφd hφJw hu hKs hKt hXs hXt hF, hdet]
  -- Expand everything on a vector; the derivatives of `a` and `b` cancel by the Cauchy–Riemann
  -- equations.
  ext v
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply, hLi, A,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.add_comp]
  rw [(fderiv ℝ η (φ w)).apply_stdComplexLine (fderiv ℝ φ w stdComplexLineReal),
    (fderiv ℝ η (φ w)).apply_stdComplexLine (-_, _),
    (fderiv ℝ Ψ (φ w)).apply_stdComplexLine (fderiv ℝ φ w stdComplexLineReal),
    (fderiv ℝ Ψ (φ w)).apply_stdComplexLine (-_, _)]
  simp only [Ψ, add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    LinearMap.coe_toContinuousLinearMap', AlmostComplexStructure.apply_apply, map_neg,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', hCR]
  ring

end Adjoint

end TauCeti.SymplecticForm
