/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LyapunovSchmidt

/-!
# Derivatives of the Lyapunov–Schmidt projections of a family of operators

Let `L(σ) : X →L[𝕜] Y` and `P(σ) : Y →L[𝕜] Z` be families of continuous linear maps between
normed spaces, depending on a parameter `σ` in a normed space, with `X` complete. At a parameter
where `A(σ) = P(σ) L(σ)` is invertible, the Lyapunov–Schmidt projections
`Π_σ = id - L(σ) A(σ)⁻¹ P(σ)` (`ContinuousLinearMap.lyapunovSchmidtProj`) inherit the regularity
of the families (`ContDiffAt.lyapunovSchmidtProj`, `DifferentiableAt.lyapunovSchmidtProj`, with
`WithinAt`, `On` and global variants), and their derivative along a direction `v` is

`∂ᵥ Π = -Π (∂ᵥ L) A⁻¹ P - L A⁻¹ (∂ᵥ P) Π`

(`DifferentiableAt.fderiv_lyapunovSchmidtProj`).

In a perturbative construction, `P` and its kernel `W` are often chosen once near a base parameter
and then held fixed. Then `∂ᵥ P = 0`, so the second term of the derivative vanishes, and for a
family of equations `L(σ) f + S(σ) = 0` the reduced section `σ ↦ Π_σ S(σ)` takes values in the
fixed space `W`; its zeros are the parameters at which the equation is solvable
(`ContinuousLinearMap.apply_add_eq_zero_iff`).

## References

* S.-N. Chow and J. K. Hale, *Methods of Bifurcation Theory*, Springer, 1982, §2.4.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open ContinuousLinearMap Set

variable {𝕜 E X Y Z : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace X]
  {L : E → X →L[𝕜] Y} {P : E → Y →L[𝕜] Z} {s : Set E} {σ : E} {n : WithTop ℕ∞}

/-- The Lyapunov–Schmidt projections of families `L` and `P` that are `C^n` within `s` at `σ` are
`C^n` within `s` at `σ`, if `P(σ) L(σ)` is invertible. -/
@[fun_prop]
theorem ContDiffWithinAt.lyapunovSchmidtProj (hL : ContDiffWithinAt 𝕜 n L s σ)
    (hP : ContDiffWithinAt 𝕜 n P s σ) (h : (P σ ∘L L σ).IsInvertible) :
    ContDiffWithinAt 𝕜 n (fun σ => (L σ).lyapunovSchmidtProj (P σ)) s σ := by
  simp only [lyapunovSchmidtProj_def]
  exact contDiffWithinAt_const.sub (hL.clm_comp (((hP.clm_comp hL).clm_inverse h).clm_comp hP))

/-- The Lyapunov–Schmidt projections of families `L` and `P` that are `C^n` at `σ` are `C^n` at
`σ`, if `P(σ) L(σ)` is invertible. -/
@[fun_prop]
theorem ContDiffAt.lyapunovSchmidtProj (hL : ContDiffAt 𝕜 n L σ) (hP : ContDiffAt 𝕜 n P σ)
    (h : (P σ ∘L L σ).IsInvertible) :
    ContDiffAt 𝕜 n (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ :=
  contDiffWithinAt_univ.1 <| hL.contDiffWithinAt.lyapunovSchmidtProj hP.contDiffWithinAt h

/-- The Lyapunov–Schmidt projections of families `L` and `P` that are `C^n` on `s` are `C^n` on
`s`, if `P(σ) L(σ)` is invertible for every `σ ∈ s`. -/
@[fun_prop]
theorem ContDiffOn.lyapunovSchmidtProj (hL : ContDiffOn 𝕜 n L s) (hP : ContDiffOn 𝕜 n P s)
    (h : ∀ σ ∈ s, (P σ ∘L L σ).IsInvertible) :
    ContDiffOn 𝕜 n (fun σ => (L σ).lyapunovSchmidtProj (P σ)) s :=
  fun σ hσ => (hL σ hσ).lyapunovSchmidtProj (hP σ hσ) (h σ hσ)

/-- The Lyapunov–Schmidt projections of `C^n` families `L` and `P` are `C^n`, if `P(σ) L(σ)` is
invertible for every `σ`. -/
@[fun_prop]
theorem ContDiff.lyapunovSchmidtProj (hL : ContDiff 𝕜 n L) (hP : ContDiff 𝕜 n P)
    (h : ∀ σ, (P σ ∘L L σ).IsInvertible) :
    ContDiff 𝕜 n (fun σ => (L σ).lyapunovSchmidtProj (P σ)) :=
  contDiff_iff_contDiffAt.2 fun σ => hL.contDiffAt.lyapunovSchmidtProj hP.contDiffAt (h σ)

/-- The Lyapunov–Schmidt projections of families `L` and `P` differentiable within `s` at `σ` are
differentiable within `s` at `σ`, if `P(σ) L(σ)` is invertible. -/
@[fun_prop]
theorem DifferentiableWithinAt.lyapunovSchmidtProj (hL : DifferentiableWithinAt 𝕜 L s σ)
    (hP : DifferentiableWithinAt 𝕜 P s σ) (h : (P σ ∘L L σ).IsInvertible) :
    DifferentiableWithinAt 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) s σ := by
  have hinv : DifferentiableAt 𝕜 (fun T : X →L[𝕜] Z => T.inverse) (P σ ∘L L σ) :=
    (h.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero
  have hA : DifferentiableWithinAt 𝕜 (fun σ => (P σ ∘L L σ).inverse) s σ :=
    hinv.comp_differentiableWithinAt (f := fun σ => P σ ∘L L σ) σ (hP.clm_comp hL)
  simp only [lyapunovSchmidtProj_def]
  exact (differentiableWithinAt_const _).sub (hL.clm_comp (hA.clm_comp hP))

/-- The Lyapunov–Schmidt projections of families `L` and `P` differentiable at `σ` are
differentiable at `σ`, if `P(σ) L(σ)` is invertible. -/
@[fun_prop]
theorem DifferentiableAt.lyapunovSchmidtProj (hL : DifferentiableAt 𝕜 L σ)
    (hP : DifferentiableAt 𝕜 P σ) (h : (P σ ∘L L σ).IsInvertible) :
    DifferentiableAt 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ :=
  differentiableWithinAt_univ.1 <|
    hL.differentiableWithinAt.lyapunovSchmidtProj hP.differentiableWithinAt h

/-- The Lyapunov–Schmidt projections of families `L` and `P` differentiable on `s` are
differentiable on `s`, if `P(σ) L(σ)` is invertible for every `σ ∈ s`. -/
@[fun_prop]
theorem DifferentiableOn.lyapunovSchmidtProj (hL : DifferentiableOn 𝕜 L s)
    (hP : DifferentiableOn 𝕜 P s) (h : ∀ σ ∈ s, (P σ ∘L L σ).IsInvertible) :
    DifferentiableOn 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) s :=
  fun σ hσ => (hL σ hσ).lyapunovSchmidtProj (hP σ hσ) (h σ hσ)

/-- The Lyapunov–Schmidt projections of differentiable families `L` and `P` are differentiable, if
`P(σ) L(σ)` is invertible for every `σ`. -/
@[fun_prop]
theorem Differentiable.lyapunovSchmidtProj (hL : Differentiable 𝕜 L) (hP : Differentiable 𝕜 P)
    (h : ∀ σ, (P σ ∘L L σ).IsInvertible) :
    Differentiable 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) :=
  fun σ => (hL σ).lyapunovSchmidtProj (hP σ) (h σ)

/-- The derivative of the Lyapunov–Schmidt projections `Π = id - L A⁻¹ P`, `A = P L`, of
differentiable families along a direction `v`, at a parameter where `A` is invertible:
`∂ᵥ Π = -Π (∂ᵥ L) A⁻¹ P - L A⁻¹ (∂ᵥ P) Π`. -/
theorem DifferentiableAt.fderiv_lyapunovSchmidtProj (hL : DifferentiableAt 𝕜 L σ)
    (hP : DifferentiableAt 𝕜 P σ) (h : (P σ ∘L L σ).IsInvertible) (v : E) :
    fderiv 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ v =
      -((L σ).lyapunovSchmidtProj (P σ) ∘L fderiv 𝕜 L σ v ∘L (P σ ∘L L σ).inverse ∘L P σ) -
        L σ ∘L (P σ ∘L L σ).inverse ∘L fderiv 𝕜 P σ v ∘L (L σ).lyapunovSchmidtProj (P σ) := by
  have hA : DifferentiableAt 𝕜 (fun σ => P σ ∘L L σ) σ := hP.clm_comp hL
  have hinv := hA.clm_inverse_of_completeSpace h
  have hderiv : fderiv 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ v =
      -(fderiv 𝕜 L σ v ∘L (P σ ∘L L σ).inverse ∘L P σ +
        L σ ∘L (fderiv 𝕜 (fun σ => (P σ ∘L L σ).inverse) σ v ∘L P σ +
          (P σ ∘L L σ).inverse ∘L fderiv 𝕜 P σ v)) := by
    simp only [lyapunovSchmidtProj_def]
    rw [fderiv_const_sub, fderiv_clm_comp hL (hinv.clm_comp hP), fderiv_clm_comp hinv hP]
    simp [add_comm]
  rw [hderiv, hA.fderiv_clm_inverse h, fderiv_clm_comp hP hL]
  ext y
  simp only [lyapunovSchmidtProj_apply, neg_apply, add_apply, sub_apply, coe_comp,
    Function.comp_apply, map_sub, map_add, map_neg, compL_apply, flip_apply]
  abel
