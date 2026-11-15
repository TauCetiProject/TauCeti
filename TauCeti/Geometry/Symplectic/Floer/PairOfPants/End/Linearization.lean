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
end Hamiltonian `H_q` in the target point is used. Since `a - b J` multiplies the form
`g(v, v) = ω(v, J v)` by `a² + b² = det dφ'_q`, the `L²` norms of the two operators, measured by
`g`, correspond under the change of variables `φ'_q`
(`TauCeti.SymplecticForm.integral_associatedBilinForm_floerLinearization_image`). This is the form
in which the estimates of the linearized operator on a cylindrical end apply to the pair of
pants.

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
  set z := positiveEndChart q ζ
  -- Beyond the height `2` the perturbation is `H_q(t) dt` on the end `q`.
  have hKH (r : Puncture) (w : ℂ) (x : V) (hw : 2 ≤ r.endSign * (r.endCoord w).re) :
      pairOfPantsPerturbation H w x = H r (r.endCoord w).im x • r.endAngularForm w :=
    pairOfPantsPerturbation_eq_smul_endAngularForm hw x
  -- So at `z` its components are constant multiples of the Hamiltonian `H_q(t₀)` of the end, and
  -- their Hamiltonian vector fields are constant multiples of `X_{H_q(t₀)}`.
  set t₀ := (q.endCoord (Complex.equivRealProdCLM.symm z)).im
  have hcomp (v : ℂ) : (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) =
      fun y ↦ q.endAngularForm (Complex.equivRealProdCLM.symm z) v * H q t₀ y := by
    funext y
    have hre : 2 ≤ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
      rw [show z = endChart q (q.endSign • ζ) from positiveEndChart_apply q ζ, re_endCoord_endChart,
        Prod.smul_fst, smul_eq_mul, ← mul_assoc, Puncture.endSign_mul_self, one_mul]
      exact hζ
    rw [hKH q _ y hre, smul_apply, smul_eq_mul, mul_comm]
  have hK (v : ℂ) : ∀ᶠ y in 𝓝 (u z),
      DifferentiableAt ℝ (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)
        y := by
    rw [hcomp v]
    exact Eventually.of_forall fun y ↦
      (((hHs t₀).differentiable (by norm_num)) y).const_mul _
  have hX (v : ℂ) : DifferentiableAt ℝ (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)) (u z) := by
    have h : ω.hamiltonianVectorField (fun y ↦ q.endAngularForm (Complex.equivRealProdCLM.symm z) v
        * H q t₀ y) = fun y ↦ q.endAngularForm (Complex.equivRealProdCLM.symm z) v •
          ω.hamiltonianVectorField (H q t₀) y :=
      funext fun y ↦ ω.hamiltonianVectorField_const_mul _ _ y
    rw [hcomp v, h]
    exact ((ω.contDiff_hamiltonianVectorField (n := 1) (hHs t₀)).differentiable
      (by norm_num) _).const_smul _
  -- The pullback along the positive end chart is the cylindrical datum `H'_q(t) dt` of the end
  -- Hamiltonian.
  have hs : perturbationPullback (positiveEndChart q)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineReal ζ = fun _ ↦ 0 :=
    funext fun x ↦ perturbationPullback_positiveEndChart_stdComplexLineReal_of_le hKH hζ x
  have ht : perturbationPullback (positiveEndChart q)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineImag ζ = positiveEndHamiltonian H q ζ.2 :=
    funext fun x ↦ perturbationPullback_positiveEndChart_stdComplexLineImag_of_le hKH hH hζ x
  -- The linearized operator at `ζ` sees the datum only at `ζ`.
  have hdatum : ω.floerLinearization
      (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun ζ' ↦ positiveEndHamiltonian H q ζ'.2) (u ∘ positiveEndChart q)
      (ξ ∘ positiveEndChart q) ζ =
    ω.floerLinearization
      (fun ζ' y ↦ (J (positiveEndChart q ζ') y).toLinearMap.toContinuousLinearMap)
      (perturbationPullback (positiveEndChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal)
      (perturbationPullback (positiveEndChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag)
      (u ∘ positiveEndChart q) (ξ ∘ positiveEndChart q) ζ := by
    rw [floerLinearization_def, floerLinearization_def, hs, ht]
  rw [hdatum]
  exact ω.floerLinearization_perturbationPullback
    ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
    (isComplexLinearMap_fderiv_positiveEndChart q ζ) hu hξ (hK 1) (hK Complex.I) (hX 1)
    (hX Complex.I) ((floerOperator_eq_zero_iff ω J _ _ u z).2 hfl)

end TauCeti.SymplecticForm
