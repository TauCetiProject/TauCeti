/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Fredholm
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Index
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Hamiltonian.Hessian

/-!
# Regularity of time-independent Floer cylinders and the Morse–Smale condition

Let `(V, ω)` be a finite-dimensional symplectic vector space whose inner product is the metric
`ω(·, J ·)` of a compatible complex structure `J`, and let `H` be a `C²` autonomous Hamiltonian.
A map `(s, t) ↦ γ(s)` that does not depend on `t` solves the Floer equation
`∂s u + J (∂t u - X_H(u)) = 0` exactly when `γ' = J X_H(γ) = ∇H(γ)`
(`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Basic`), that is, when `γ` is a negative
gradient line of `-H`; a Floer cylinder whose derivative is small relative to the Hamiltonian is of
this form (`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.SmallHamiltonian`). This file
compares the linearized Floer operator `D : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)`
(`TauCeti.SymplecticForm.floerSobolevOperator 2`) along such a cylinder with the transversality of
the gradient line in the Morse theory of `-H`, when `‖dX_H‖ ≤ a < 2π` along `γ`.

On the zero Fourier mode `D` is the Morse operator `ζ ↦ ζ' - J dX_H(γ) ζ`
(`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Sobolev`), and `J dX_H` is the Hessian of `H`
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianVectorField_eq_hessianOperator`), so this is the
operator `ζ ↦ ζ' + Hess (-H)(γ) ζ` of the Morse theory of `-H`
(`TauCeti.SymplecticForm.neg_comp_fderiv_hamiltonianVectorField_eq_hessianOperator_neg`). Let
`γ(s)` be the negative gradient flow line of `-H` through a point `y` of the unstable set of a
nondegenerate critical point `p` and of the stable set of a nondegenerate critical point `q`.

* **The kernel.** The kernel of `D` along `(s, t) ↦ γ(s)` has the dimension of the intersection of
  the tangent spaces at `y` of the unstable set of `p` and the stable set of `q`
  (`TauCeti.SymplecticForm.finrank_ker_floerSobolevOperator_negativeGradientFlow`), for every
  compatible `J`.
* **Regularity along one cylinder.** In a unitary trivialization, where `V = F` is a complex inner
  product space with `ω = Im ⟪·, ·⟫` and `J = i`, the operator `D` is onto exactly when the unstable
  set of `p` and the stable set of `q` are transverse at `y`
  (`TauCeti.SymplecticForm.surjective_floerSobolevOperator_negativeGradientFlow_iff`).
* **The Morse–Smale condition.** In a unitary trivialization, if `‖dX_H‖ ≤ a < 2π` everywhere, the
  negative gradient flow of `-H` is Morse–Smale exactly when every time-independent Floer cylinder
  of `H` between nondegenerate critical points is regular
  (`TauCeti.SymplecticForm.isMorseSmale_neg_iff_forall_surjective_floerSobolevOperator`).

These are the Morse statements
`TauCeti.finrank_ker_trajectoryOperator_hessianOperator_negativeGradientFlow`,
`TauCeti.surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff` and
`TauCeti.isMorseSmale_iff_forall_surjective_trajectoryOperator`, transported through the
comparison of `D` with the Morse operator
(`TauCeti.SymplecticForm.finrank_ker_floerSobolevOperator_eq_finrank_ker_trajectoryOperator` and
`TauCeti.SymplecticForm.surjective_floerSobolevOperator_iff_surjective_trajectoryOperator`). The
gradient lines of `H` are the negative gradient lines of `-H`, so the unstable set of `-H` at `p`
is the stable set of `H` at `p`, and `H` increases along `γ` from `p` to `q`.

## References

* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. 45 (1992), 1303–1360, on the regularity of the Floer
  cylinders of a small Morse Hamiltonian and the Morse–Smale condition.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic Geometry and Topology*, IAS/Park City
  Math. Ser. 7, 1999, Lecture 2.
-/

public section

open Real Filter MeasureTheory Topology
open scoped Gradient NNReal ENNReal RealInnerProductSpace

namespace TauCeti.SymplecticForm

section Compatible

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ω : SymplecticForm E} {J : AlmostComplexStructure E}

/-- **The dimension of the kernel along a time-independent Floer cylinder.** Let the inner
product of `E` be the metric `ω(·, J ·)`, and `H` a `C²` autonomous Hamiltonian such that
`∇(-H)` is globally Lipschitz. Let `y` lie in the unstable set of a nondegenerate critical point
`p` and in the stable set of a nondegenerate critical point `q` for the negative gradient flow `φ`
of `-H`, and suppose that `‖dX_H‖ ≤ a < 2π` along `γ(s) = φ(s, y)`.
Then the kernel of the Sobolev realization of the linearized Floer operator along the Floer
cylinder `(s, t) ↦ γ(s)`, for the data `(J, 0, H)`, has the dimension of the intersection of the
tangent spaces at `y` of the unstable set of `p` and of the stable set of `q`. -/
theorem finrank_ker_floerSobolevOperator_negativeGradientFlow
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {H : E → ℝ} (hH : ContDiff ℝ 2 H) {K : ℝ≥0}
    (hf : LipschitzWith K (∇ (-H))) {p q y : E} (hp : IsNondegenerateCriticalPoint H p)
    (hq : IsNondegenerateCriticalPoint H q)
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow (-H) hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow (-H) hf) q) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (negativeGradientFlow (-H) hf s y)‖ ≤ a) :
    Module.finrank ℝ (ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ negativeGradientFlow (-H) hf z.1 y)).ker =
      Module.finrank ℝ
        (Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow (-H) hf) p) y) ⊓
          Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow (-H) hf) q) y) :
            Submodule ℝ E) := by
  have hH' : ContDiff ℝ 2 (-H) := hH.neg
  have hγ := (isNegativeGradient_negativeGradientFlow (-H) hf).isIntegralCurve y
  have hmem := hH'.memLp_top_hessianOperator_comp hγ.continuous
    (Flow.mem_unstableSet.1 hyu) (Flow.mem_stableSet.1 hys)
    (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))
  rw [finrank_ker_floerSobolevOperator_eq_finrank_ker_trajectoryOperator (H := fun _ ↦ H) hg
    (hH.comp contDiff_snd) hγ.continuous ha haγ (hmem.coeFn_toLp.trans (.of_forall fun s ↦
      (neg_comp_fderiv_hamiltonianVectorField_eq_hessianOperator_neg hg H _).symm))]
  exact finrank_ker_trajectoryOperator_hessianOperator_negativeGradientFlow hp.neg hq.neg hH' hf hyu
    hys hmem.coeFn_toLp

end Compatible

section Unitary

/-! ### Floer cylinders of gradient lines in a unitary trivialization -/

attribute [local instance] InnerProductSpace.complexToReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {ω : SymplecticForm F} {H : F → ℝ}

/-- Along a curve on which `‖dX_H‖ ≤ a < 2π`, the linearized Floer operator of the
time-independent cylinder is onto exactly when the Morse operator `ζ ↦ ζ' + Hess (-H)(γ) ζ` is. -/
private theorem surjective_floerSobolevOperator_iff_surjective_trajectoryOperator_hessianOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) {γ : ℝ → F} (hγ : Continuous γ)
    {a : ℝ} (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    {A : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hA : A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (-H) (γ s)) :
    Function.Surjective (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1)) ↔
      Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) A) :=
  surjective_floerSobolevOperator_iff_surjective_trajectoryOperator (H := fun _ ↦ H) hω
    (hH.comp contDiff_snd) hγ ha haγ
    (hA.trans (.of_forall fun s ↦
      (neg_comp_fderiv_hamiltonianVectorField_eq_hessianOperator_neg
        (ω.apply_ofComplexModule_eq_inner hω) H (γ s)).symm))

/-- **A time-independent Floer cylinder is regular exactly when its gradient line is transverse.**
Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, and `H` a `C²` autonomous Hamiltonian such that `∇(-H)` is globally Lipschitz. Let
`y` lie in the unstable set of a nondegenerate critical point `p` and in the stable set of a
nondegenerate critical point `q` for the negative gradient flow `φ` of `-H`, and suppose that
`‖dX_H‖ ≤ a < 2π` along `γ(s) = φ(s, y)`. Then the Sobolev realization of the linearized Floer
operator along the Floer cylinder `(s, t) ↦ γ(s)` maps `W^{1,2}(ℝ × S¹, F)` onto
`L²(ℝ × S¹, F)` exactly when the unstable set of `p` and the stable set of `q` are transverse at
`y`: their tangent spaces at `y` span `F`. -/
theorem surjective_floerSobolevOperator_negativeGradientFlow_iff
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) {K : ℝ≥0}
    (hf : LipschitzWith K (∇ (-H))) {p q y : F} (hp : IsNondegenerateCriticalPoint H p)
    (hq : IsNondegenerateCriticalPoint H q)
    (hyu : y ∈ Flow.unstableSet (negativeGradientFlow (-H) hf) p)
    (hys : y ∈ Flow.stableSet (negativeGradientFlow (-H) hf) q) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (negativeGradientFlow (-H) hf s y)‖ ≤ a) :
    Function.Surjective (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ negativeGradientFlow (-H) hf z.1 y)) ↔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet (negativeGradientFlow (-H) hf) p) y) ⊔
        Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet (negativeGradientFlow (-H) hf) q) y) =
          ⊤ := by
  have hH' : ContDiff ℝ 2 (-H) := hH.neg
  have hγ := (isNegativeGradient_negativeGradientFlow (-H) hf).isIntegralCurve y
  have hmem := hH'.memLp_top_hessianOperator_comp hγ.continuous
    (Flow.mem_unstableSet.1 hyu) (Flow.mem_stableSet.1 hys)
    (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))
  rw [surjective_floerSobolevOperator_iff_surjective_trajectoryOperator_hessianOperator hω hH
    hγ.continuous ha haγ hmem.coeFn_toLp]
  exact surjective_trajectoryOperator_hessianOperator_negativeGradientFlow_iff hp.neg hq.neg hH'
    hf hyu hys hmem.coeFn_toLp

/-- **Morse–Smale means every time-independent Floer cylinder is regular.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, and `H` a
`C²` autonomous Hamiltonian with `‖dX_H‖ ≤ a < 2π` everywhere and with `∇(-H)` globally Lipschitz.
Then the negative gradient flow of `-H` is Morse–Smale exactly when, for every gradient line
`γ' = ∇H(γ)` from a nondegenerate critical point `p` to a nondegenerate critical point `q`, the
Sobolev realization of the linearized Floer operator along the Floer cylinder `(s, t) ↦ γ(s)` maps
`W^{1,2}(ℝ × S¹, F)` onto `L²(ℝ × S¹, F)`. -/
theorem isMorseSmale_neg_iff_forall_surjective_floerSobolevOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 H) {K : ℝ≥0}
    (hf : LipschitzWith K (∇ (-H))) {a : ℝ} (ha : a < 2 * π)
    (haH : ∀ y, ‖fderiv ℝ (ω.hamiltonianVectorField H) y‖ ≤ a) :
    IsMorseSmale (-H) hf ↔ ∀ ⦃p q : F⦄ ⦃γ : ℝ → F⦄, IsNondegenerateCriticalPoint H p →
      IsNondegenerateCriticalPoint H q → IsIntegralCurve γ (fun _ ↦ ∇ H) →
      Tendsto γ atBot (𝓝 p) → Tendsto γ atTop (𝓝 q) →
      Function.Surjective (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1)) := by
  have hH' : ContDiff ℝ 2 (-H) := hH.neg
  -- The gradient lines of `H` are the negative gradient lines of `-H`.
  have hfield : (fun (_ : ℝ) x ↦ -∇ (-H) x) = fun _ ↦ ∇ H :=
    funext fun _ ↦ funext fun x ↦ by rw [gradient_neg, neg_neg]
  rw [isMorseSmale_iff_forall_surjective_trajectoryOperator hH' hf, hfield]
  constructor
  · intro h p q γ hp hq hγ hbot htop
    have hmem := hH'.memLp_top_hessianOperator_comp hγ.continuous hbot htop
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))
    exact (surjective_floerSobolevOperator_iff_surjective_trajectoryOperator_hessianOperator hω hH
      hγ.continuous ha (fun s ↦ haH (γ s)) hmem.coeFn_toLp).2
      (h hp.neg hq.neg hγ hbot htop _ hmem.coeFn_toLp)
  · intro h p q γ hp hq hγ hbot htop AL hAL
    rw [isNondegenerateCriticalPoint_neg] at hp hq
    exact (surjective_floerSobolevOperator_iff_surjective_trajectoryOperator_hessianOperator hω hH
      hγ.continuous ha (fun s ↦ haH (γ s)) hAL).1 (h hp hq hγ hbot htop)

end Unitary

end TauCeti.SymplecticForm
