/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart

/-!
# The linearized Floer operator on the ends of the pair of pants

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with values in a symplectic vector
space `(V, ω)`, and let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` for structures
`J(z, x)`. The linearized operator `D_u` along `u` (`TauCeti.SymplecticForm.floerLinearization`)
is written in the global coordinate `z = s + i t` of `ℂ`. Its Fredholm theory is governed by the
ends, where `u` converges to the asymptotic orbits and `D_u` to the translation-invariant operator
of the orbit (`TauCeti.Geometry.Symplectic.Floer.EndLinearization`); there the natural coordinates
are those of the positive end chart `φ'_q` (`TauCeti.Floer.positiveEndChart`), in which every end
is a positive half-cylinder.

This file identifies the operator `D_u` read on the far part `s ≥ 2` of an end with the
linearized operator of a Floer half-cylinder. In the positive end chart the datum `K` is
`H'_q(t) dt` for the end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`), so the linearized operator along `u ∘ φ'_q` in the
direction `ξ ∘ φ'_q` is that of the cylindrical datum `K_s = 0`, `K_t = H'_q(t)` with the
structures `J(φ'_q(s, t), ·)`. It is `a D_u ξ - b J D_u ξ` at `φ'_q(s, t)`, where `a + i b` is
the complex derivative of `φ'_q`
(`TauCeti.SymplecticForm.floerLinearization_comp_positiveEndChart`). Only the regularity of the
end Hamiltonian `H_q` in the target point is used: when it is `C²`, the Hamiltonian vector fields
of the components of `K` on the end are differentiable
(`TauCeti.SymplecticForm.differentiableAt_hamiltonianVectorField_perturbation_positiveEndChart`).
Since `a - b J` multiplies the form
`g(v, v) = ω(v, J v)` by `a² + b² = det dφ'_q`, the `L²` norms of the two operators, measured by
`g`, correspond under the change of variables `φ'_q`
(`TauCeti.SymplecticForm.integral_associatedBilinForm_floerLinearization_image`). This is the form
in which the estimates of the linearized operator on a cylindrical end apply to the pair of
pants.

The formal adjoint `D_u^*` on covector fields transforms in the same way, with the covector field
`η` read in the chart as the `(0, 1)`-form `η (φ'_q ζ) ∘ (a + b J)`
(`TauCeti.Floer.covectorPullback`): the adjoint of the operator of the half-cylinder on this form
is `det dφ'_q = a² + b²` times `D_u^* η` at `φ'_q(ζ)`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_comp_positiveEndChart`).

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.1
  and Section 8.1.
-/

public section

open Filter Function TauCeti.ThricePuncturedSphere
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- Where `K = H_q(t) dt` on the end `q` and the Hamiltonians `H_q(t)` are `C²`, the Hamiltonian
vector fields of the components of `K` at the point `φ'_q(ζ)` of the end are differentiable. -/
theorem differentiableAt_hamiltonianVectorField_perturbation_positiveEndChart
    (ω : SymplecticForm V) {K : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHs : ∀ t, ContDiff ℝ 2 (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (v : ℂ)
    (y : V) :
    DifferentiableAt ℝ (ω.hamiltonianVectorField
      (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v)) y := by
  simp only [perturbation_positiveEndChart_eq_mul_of_le hKH hζ]
  rw [funext (ω.hamiltonianVectorField_const_mul _ _)]
  exact ((ω.contDiff_hamiltonianVectorField (n := 1) (hHs _)).differentiable
    (by norm_num) _).const_smul _

/-- On the far part `s ≥ 2` of the end `q`, where the Hamiltonians `H_q(t)` are `C²`, the
components of the pair-of-pants perturbation at `φ'_q(ζ)` and their Hamiltonian vector fields are
differentiable near the point `y`, as the transformation laws under `φ'_q` require, and the
pullback of the perturbation along `φ'_q` at `ζ` is the cylindrical datum `H'_q(t) dt` of the end
Hamiltonian. -/
private theorem pairOfPantsPerturbation_positiveEndChart_of_two_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t)) {ζ : ℝ × ℝ}
    (hζ : 2 ≤ ζ.1) (y : V) :
    (∀ v : ℂ, ∀ᶠ x in 𝓝 y, DifferentiableAt ℝ (fun x ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) x) ∧
    (∀ v : ℂ, DifferentiableAt ℝ (ω.hamiltonianVectorField fun x ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v) y) ∧
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal ζ = (fun _ ↦ 0) ∧
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag ζ = positiveEndHamiltonian H q ζ.2 := by
  -- Beyond the height `2` the perturbation is `H_q(t) dt` on the end `q`.
  have hKH (w : ℂ) (x : V) (hw : 2 ≤ q.endSign * (q.endCoord w).re) :
      pairOfPantsPerturbation H w x = H q (q.endCoord w).im x • q.endAngularForm w :=
    pairOfPantsPerturbation_eq_smul_endAngularForm hw x
  exact ⟨fun v ↦ .of_forall (differentiableAt_perturbation_positiveEndChart hKH
      (fun t ↦ (hHs t).differentiable (by norm_num)) hζ v),
    fun v ↦ ω.differentiableAt_hamiltonianVectorField_perturbation_positiveEndChart hKH hHs hζ v y,
    funext (perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ),
    funext (perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH (hH q) hζ)⟩

/-- **The linearized operator of the pair of pants on its ends.** Let `u` solve the Floer
equation for the pair-of-pants perturbation of period-one Hamiltonians `H_q` at the point
`φ'_q(ζ)` of the end `q`, with `ζ = (s, t)` and `s ≥ 2`, where `φ'_q` is the positive end chart,
and let each `H_q(t)` be `C²` on `V`.
Read in this chart, the linearized operator along `u ∘ φ'_q` in the direction `ξ ∘ φ'_q`, for the
cylindrical datum `H'_q(t) dt` of the end Hamiltonian and the structures `J(φ'_q(·), ·)`, is
`a D_u ξ - b J D_u ξ`, where `D_u ξ` is the linearized operator in the global coordinate at
`φ'_q(ζ)` and `(a, b) = dφ'_q (1, 0)`. -/
theorem floerLinearization_comp_positiveEndChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u ξ : ℝ × ℝ → V} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ ζ.1) (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hξ : DifferentiableAt ℝ ξ (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerLinearization
        (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q)
        (ξ ∘ positiveEndChart q) ζ =
      (fderiv ℝ (positiveEndChart q) ζ stdComplexLineReal).1 • ω.floerLinearization
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ξ (positiveEndChart q ζ) -
        (fderiv ℝ (positiveEndChart q) ζ stdComplexLineReal).2 •
          J (positiveEndChart q ζ) (u (positiveEndChart q ζ)) (ω.floerLinearization
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            u ξ (positiveEndChart q ζ)) := by
  obtain ⟨hK, hX, h₀, hH'⟩ :=
    ω.pairOfPantsPerturbation_positiveEndChart_of_two_le hH hHs hζ (u (positiveEndChart q ζ))
  -- The pullback along the positive end chart is the cylindrical datum `H'_q(t) dt` of the end
  -- Hamiltonian, and the linearized operator at `ζ` sees the datum only at `ζ`.
  refine Eq.trans ?_ (ω.floerLinearization_perturbationPullback
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hu hξ (hK 1) (hK Complex.I) (hX 1)
    (hX Complex.I) ((floerOperator_eq_zero_iff ω J _ _ u _).2 hfl))
  rw [floerLinearization_def, floerLinearization_def, h₀, hH']

/-- **The formal adjoint of the pair of pants on its ends.** Let `u` solve the Floer equation for
the pair-of-pants perturbation of period-one Hamiltonians `H_q` at the point `φ'_q(ζ)` of the end
`q`, with `ζ = (s, t)` and `s ≥ 2`, where `φ'_q` is the positive end chart, and let each `H_q(t)`
be `C²` on `V`. Read the covector field `η` in this chart as the `(0, 1)`-form
`η (φ'_q ·) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback`), where `(a, b) = dφ'_q (1, 0)`. The
formal adjoint of the operator along `u ∘ φ'_q` of the cylindrical datum `H'_q(t) dt` of the end
Hamiltonian, with the structures `J(φ'_q(·), ·)`, applied to this form at `ζ`, is
`det dφ'_q = a² + b²` times the formal adjoint `D_u^* η` in the global coordinate at `φ'_q(ζ)`. -/
theorem floerLinearizationAdjoint_comp_positiveEndChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} (hHs : ∀ t, ContDiff ℝ 2 (H q t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ}
    {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) (hu : DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hη : DifferentiableAt ℝ η (positiveEndChart q ζ))
    (hJu : DifferentiableAt ℝ (fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap)
      (positiveEndChart q ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerLinearizationAdjoint
        (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q)
        (covectorPullback (positiveEndChart q)
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ =
      (fderiv ℝ (positiveEndChart q) ζ).det • ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u η (positiveEndChart q ζ) := by
  obtain ⟨hK, hX, h₀, hH'⟩ :=
    ω.pairOfPantsPerturbation_positiveEndChart_of_two_le hH hHs hζ (u (positiveEndChart q ζ))
  refine Eq.trans ?_ (ω.floerLinearizationAdjoint_perturbationPullback
    ((contDiff_positiveEndChart q 2).contDiffAt)
    (.of_forall (isComplexLinearMap_fderiv_positiveEndChart q)) hu (hK 1) (hK Complex.I) (hX 1)
    (hX Complex.I) ((floerOperator_eq_zero_iff ω J _ _ u _).2 hfl) hη hJu)
  -- The pullback of the perturbation at `ζ` is the cylindrical datum `H'_q(t) dt`, and the
  -- adjoint at `ζ` sees the perturbation only at `ζ`.
  rw [floerLinearizationAdjoint_def, floerLinearizationAdjoint_def]
  ext v
  simp only [add_apply, ContinuousLinearMap.comp_apply, floerLinearizationCoeff_apply, h₀, hH']

end TauCeti.SymplecticForm
