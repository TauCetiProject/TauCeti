/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
public import TauCeti.Geometry.Diffeomorphism.PushforwardOperator
public import TauCeti.RepresentationTheory.Invariants
import TauCeti.Analysis.Pseudodifferential.Manifold.Diffeomorph

/-!
# Averaging pseudodifferential operators over a finite group of diffeomorphisms

The diffeomorphism group of a manifold `M` acts on the complex-linear operators on `C^n(M, ℂ)` by
pushforward, `Φ_* P : u ↦ P (u ∘ Φ) ∘ Φ⁻¹` (`Diffeomorph.pushforwardOperatorRepresentation`). For a
homomorphism `ρ : G →* (M ≃ₘ M)` from a finite group, Mathlib's `Representation.averageMap` of the
composite representation is the **average**

`avg(P) = |G|⁻¹ ∑_g (ρ g)_* P`

(`Representation.averageMap_apply`), invariant and equivariant under `G`
(`Diffeomorph.pushforwardOperator_averageMap`, `Diffeomorph.averageMap_compRightComplexAlgEquiv`).

On a manifold modelled on `ℝⁿ` the average of a classical pseudodifferential operator of order `m`
(`TauCeti.classicalPseudodifferentialOperators`) is again one, since each `(ρ g)_* P` is
(`TauCeti.pushforwardOperator_mem_classicalPseudodifferentialOperators`). Its principal symbol is
the average of the principal symbol over the cotangent action of `G`,

`σ_m(avg P)(x, ξ) = |G|⁻¹ ∑_g σ_m(P)(g⁻¹ x, ξ ∘ dg_{g⁻¹ x})`,

so averaging keeps an invariant principal symbol, and keeps a principal symbol with positive real
part at nonzero covectors. In the second case the average is elliptic: averaging turns an
operator with positive principal symbol into an equivariant elliptic operator of the same order.

## Main results

* `TauCeti.averageMap_mem_classicalPseudodifferentialOperators`: averaging preserves the classical
  pseudodifferential operators of order `m`.
* `TauCeti.classicalPrincipalSymbol_averageMap`: the principal symbol of the average.
* `TauCeti.classicalPrincipalSymbol_averageMap_of_forall_eq`: averaging fixes an invariant
  principal symbol.
* `TauCeti.re_classicalPrincipalSymbol_averageMap_pos`, `TauCeti.isClassicalElliptic_averageMap`:
  averaging preserves principal symbols with positive real part, and its result is then elliptic.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §5, (5.5)–(5.6), pp. 516–517 (averaging pseudodifferential operators over a compact group).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem
  18.1.17 (invariance of the classical operators and their principal symbols under
  diffeomorphisms).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

open Diffeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {G : Type*} [Group G] [Fintype G]
  (ρ : G →* (M ≃ₘ^∞⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M)) {m : ℝ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **Averaging preserves the order.** The average `|G|⁻¹ ∑_g (ρ g)_* P` of a classical
pseudodifferential operator `P` of order `m` over a finite group `G` of diffeomorphisms of `M` is
a classical pseudodifferential operator of order `m`. -/
theorem averageMap_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    Representation.averageMap
      ((pushforwardOperatorRepresentation 𝓘(ℝ, CoordinateSpace n) M ∞).comp ρ) P ∈
      classicalPseudodifferentialOperators m := by
  rw [Representation.averageMap_apply]
  exact Submodule.smul_mem _ _ <| Submodule.sum_mem _ fun g _ ↦ by
    simpa using pushforwardOperator_mem_classicalPseudodifferentialOperators (ρ g) hP

/-- **The principal symbol of the average.** The principal symbol of the average
`|G|⁻¹ ∑_g (ρ g)_* P` of a classical pseudodifferential operator `P` of order `m` over a finite
group `G` of diffeomorphisms is the average of the principal symbol of `P` over the action of `G`
on the cotangent bundle:

`σ_m(avg P)(x, ξ) = |G|⁻¹ ∑_g σ_m(P)(g⁻¹ x, ξ ∘ dg_{g⁻¹ x})`. -/
theorem classicalPrincipalSymbol_averageMap (hP : P ∈ classicalPseudodifferentialOperators m)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m
        (Representation.averageMap
          ((pushforwardOperatorRepresentation 𝓘(ℝ, CoordinateSpace n) M ∞).comp ρ) P)
        x ξ =
      ⅟(Fintype.card G : ℂ) * ∑ g : G, classicalPrincipalSymbol m P ((ρ g).symm x)
        (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) (ρ g)
          ((ρ g).symm x))) := by
  have hmem (g : G) : (ρ g).pushforwardOperator P ∈ classicalPseudodifferentialOperators m :=
    pushforwardOperator_mem_classicalPseudodifferentialOperators (ρ g) hP
  simp only [Representation.averageMap_apply, MonoidHom.coe_comp, Function.comp_apply,
    pushforwardOperatorRepresentation_apply]
  rw [classicalPrincipalSymbol_smul (Submodule.sum_mem _ fun g _ ↦ hmem g),
    classicalPrincipalSymbol_sum _ fun g _ ↦ hmem g]
  simp only [classicalPrincipalSymbol_pushforwardOperator_apply]

/-- **Averaging fixes invariant principal symbols.** If the principal symbol of a classical
pseudodifferential operator `P` of order `m` is invariant under the cotangent action of a finite
group `G` of diffeomorphisms, `σ_m(P)(g y, ξ) = σ_m(P)(y, ξ ∘ dg_y)`, then the average
`|G|⁻¹ ∑_g (ρ g)_* P` has the same principal symbol as `P`. -/
theorem classicalPrincipalSymbol_averageMap_of_forall_eq
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hσ : ∀ (g : G) (y : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) (ρ g y) →L[ℝ] ℝ),
      classicalPrincipalSymbol m P (ρ g y) ξ =
        classicalPrincipalSymbol m P y
          (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) (ρ g) y)))
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m
        (Representation.averageMap
          ((pushforwardOperatorRepresentation 𝓘(ℝ, CoordinateSpace n) M ∞).comp ρ) P)
        x ξ =
      classicalPrincipalSymbol m P x ξ := by
  have h (g : G) : classicalPrincipalSymbol m P ((ρ g).symm x)
      (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) (ρ g) ((ρ g).symm x))) =
        classicalPrincipalSymbol m P x ξ := by
    have h := hσ g ((ρ g).symm x) ξ
    rw [(ρ g).apply_symm_apply] at h
    exact h.symm
  rw [classicalPrincipalSymbol_averageMap ρ hP, Finset.sum_congr rfl fun g _ ↦ h g]
  simp

/-- **Averaging preserves positive principal symbols.** If the principal symbol of a classical
pseudodifferential operator `P` of order `m` has positive real part at every nonzero covector, so
does the principal symbol of its average `|G|⁻¹ ∑_g (ρ g)_* P` over a finite group `G` of
diffeomorphisms. -/
theorem re_classicalPrincipalSymbol_averageMap_pos
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hpos : ∀ (y : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) y →L[ℝ] ℝ), ξ ≠ 0 →
      0 < (classicalPrincipalSymbol m P y ξ).re)
    {x : M} {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    0 < (classicalPrincipalSymbol m
      (Representation.averageMap
        ((pushforwardOperatorRepresentation 𝓘(ℝ, CoordinateSpace n) M ∞).comp ρ) P)
      x ξ).re := by
  have hsum : 0 < ∑ g : G, (classicalPrincipalSymbol m P ((ρ g).symm x)
      (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) (ρ g)
        ((ρ g).symm x)))).re :=
    Finset.sum_pos (fun g _ ↦ hpos _ _ fun h ↦
      hξ (((ρ g).comp_mfderiv_eq_zero_iff (by simp) _).1 h)) Finset.univ_nonempty
  rw [classicalPrincipalSymbol_averageMap ρ hP, invOf_eq_inv, inv_mul_eq_div,
    Complex.div_natCast_re, Complex.re_sum]
  exact div_pos hsum (by positivity)

/-- **Averaging preserves positive ellipticity.** If the principal symbol of a classical
pseudodifferential operator `P` of order `m` has positive real part at every nonzero covector,
then the average `|G|⁻¹ ∑_g (ρ g)_* P` over a finite group `G` of diffeomorphisms is elliptic. -/
theorem isClassicalElliptic_averageMap (hP : P ∈ classicalPseudodifferentialOperators m)
    (hpos : ∀ (y : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) y →L[ℝ] ℝ), ξ ≠ 0 →
      0 < (classicalPrincipalSymbol m P y ξ).re) :
    IsClassicalElliptic m
      (Representation.averageMap
        ((pushforwardOperatorRepresentation 𝓘(ℝ, CoordinateSpace n) M ∞).comp ρ) P) :=
  isClassicalElliptic_iff.2 fun _ ↦ isClassicalEllipticAt_iff.2 fun _ hξ h ↦
    (re_classicalPrincipalSymbol_averageMap_pos ρ hP hpos hξ).ne' (by rw [h, Complex.zero_re])

end TauCeti
