/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.RepresentationTheory.Invariants
import TauCeti.Analysis.Pseudodifferential.Manifold.Diffeomorph

/-!
# Averaging pseudodifferential operators over a finite group of diffeomorphisms

The diffeomorphism group of a manifold `M` acts on the complex-linear operators on `C^n(M, ℂ)` by
pushforward, `Φ_* P : u ↦ P (u ∘ Φ) ∘ Φ⁻¹` (`Diffeomorph.pushforwardOperator`); this file packages
the action as a group homomorphism (`Diffeomorph.pushforwardOperatorHom`) and as a linear
representation (`Diffeomorph.pushforwardOperatorRepresentation`). For a homomorphism
`ρ : G →* (M ≃ₘ M)` from a finite group, Mathlib's `Representation.averageMap` of the composite
representation is the **average**

`avg(P) = |G|⁻¹ ∑_g (ρ g)_* P`

(`Representation.averageMap_apply`). It is invariant under every `(ρ g)_*`, that is, it commutes
with precomposition by every `ρ g` (`Diffeomorph.averageMap_compRightComplexAlgEquiv`), and it
fixes the invariant operators (`Representation.averageMap_id`). Averaging is how an operator is made
equivariant for a group action, as needed for equivariant elliptic operators and their indices.

On a manifold modelled on `ℝⁿ` the average of a classical pseudodifferential operator of order `m`
(`TauCeti.classicalPseudodifferentialOperators`) is again one, since each `(ρ g)_* P` is
(`TauCeti.pushforwardOperator_mem_classicalPseudodifferentialOperators`). Its principal symbol is
the average of the principal symbol over the cotangent action of `G`,

`σ_m(avg P)(x, ξ) = |G|⁻¹ ∑_g σ_m(P)(g⁻¹ x, ξ ∘ dg_{g⁻¹ x})`,

so averaging keeps an invariant principal symbol, and keeps a principal symbol with positive real
part at nonzero covectors. In the second case the average is elliptic: averaging turns an
operator with positive principal symbol into an equivariant elliptic operator of the same order.

## Main definitions

* `Diffeomorph.pushforwardOperatorHom`, `Diffeomorph.pushforwardOperatorRepresentation`: the
  pushforward action of the diffeomorphism group on operators.

## Main results

* `Diffeomorph.pushforwardOperator_eq_self_iff`: an operator is invariant under `Φ_*` exactly when
  it commutes with precomposition by `Φ`.
* `Diffeomorph.pushforwardOperator_averageMap`, `Diffeomorph.averageMap_compRightComplexAlgEquiv`:
  the average is invariant and equivariant.
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

namespace Diffeomorph

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

variable (I M n) in
/-- The pushforward of operators `P ↦ (u ↦ P (u ∘ Φ) ∘ Φ⁻¹)` along self-diffeomorphisms of `M`
(`Diffeomorph.pushforwardOperator`), as a group homomorphism from the diffeomorphism group of `M`
to the algebra automorphisms of the operators on `C^n(M, ℂ)`. -/
def pushforwardOperatorHom : (M ≃ₘ^n⟮I, I⟯ M) →*
    (Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₐ[ℂ] Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) where
  toFun := pushforwardOperator
  map_one' := pushforwardOperator_refl
  map_mul' Φ Ψ := pushforwardOperator_trans Ψ Φ

@[simp]
theorem pushforwardOperatorHom_apply (Φ : M ≃ₘ^n⟮I, I⟯ M) :
    pushforwardOperatorHom I M n Φ = pushforwardOperator Φ :=
  (rfl)

variable (I M n) in
/-- The diffeomorphism group of `M` acts linearly on the operators on `C^n(M, ℂ)` by pushforward,
`Φ • P = (u ↦ P (u ∘ Φ) ∘ Φ⁻¹)`. Composed with a homomorphism `ρ : G →* (M ≃ₘ M)` from a finite
group, its average `Representation.averageMap` is the average `|G|⁻¹ ∑_g (ρ g)_* P` of an
operator over the action of `G` (`Representation.averageMap_apply`). -/
def pushforwardOperatorRepresentation :
    Representation ℂ (M ≃ₘ^n⟮I, I⟯ M) (Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :=
  (AlgEquiv.toLinearMapHom ℂ _).comp (pushforwardOperatorHom I M n)

@[simp]
theorem pushforwardOperatorRepresentation_apply (Φ : M ≃ₘ^n⟮I, I⟯ M)
    (P : Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    pushforwardOperatorRepresentation I M n Φ P = pushforwardOperator Φ P :=
  (rfl)

/-- An operator is invariant under the pushforward along `Φ` exactly when it commutes with
precomposition by `Φ`: `P (u ∘ Φ) = (P u) ∘ Φ` for every `u`. -/
theorem pushforwardOperator_eq_self_iff (Φ : M ≃ₘ^n⟮I, I⟯ M)
    {P : Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    pushforwardOperator Φ P = P ↔
      ∀ u, P (compRightComplexAlgEquiv Φ u) = compRightComplexAlgEquiv Φ (P u) := by
  refine ⟨fun h u ↦ ContMDiffMap.ext fun x ↦ ?_, fun h ↦ LinearMap.ext fun u ↦
    ContMDiffMap.ext fun y ↦ ?_⟩
  · conv_rhs => rw [compRightComplexAlgEquiv_apply, ← h, pushforwardOperator_apply_apply,
      Φ.symm_apply_apply]
  · rw [pushforwardOperator_apply_apply, h, compRightComplexAlgEquiv_apply, Φ.apply_symm_apply]

variable {G : Type*} [Group G] [Fintype G] (ρ : G →* (M ≃ₘ^n⟮I, I⟯ M))

/-- **The average is invariant.** The average `|G|⁻¹ ∑_g (ρ g)_* P` of an operator over a finite
group `G` of diffeomorphisms is invariant under the pushforward along every `ρ g`. -/
theorem pushforwardOperator_averageMap (g : G) (P : Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    pushforwardOperator (ρ g)
        (Representation.averageMap ((pushforwardOperatorRepresentation I M n).comp ρ) P) =
      Representation.averageMap ((pushforwardOperatorRepresentation I M n).comp ρ) P :=
  by
  have h := Representation.averageMap_invariant ((pushforwardOperatorRepresentation I M n).comp ρ)
    P g
  simpa using h

/-- **The average is equivariant.** The average `|G|⁻¹ ∑_g (ρ g)_* P` of an operator over a finite
group `G` of diffeomorphisms commutes with precomposition by every `ρ g`:
`avg(P) (u ∘ ρ g) = avg(P)(u) ∘ ρ g`. -/
theorem averageMap_compRightComplexAlgEquiv (g : G) (P : Module.End ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯)
    (u : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Representation.averageMap ((pushforwardOperatorRepresentation I M n).comp ρ) P
        (compRightComplexAlgEquiv (ρ g) u) =
      compRightComplexAlgEquiv (ρ g)
        (Representation.averageMap ((pushforwardOperatorRepresentation I M n).comp ρ) P u) :=
  (pushforwardOperator_eq_self_iff (ρ g)).1 (pushforwardOperator_averageMap ρ g P) u

end Diffeomorph

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
  exact Submodule.smul_mem _ _ <| Submodule.sum_mem _ fun g _ ↦
    pushforwardOperator_mem_classicalPseudodifferentialOperators (ρ g) hP

/-- The principal symbol of the pushforward of `P` along `Φ` at a covector `ξ ∈ T*_y M`, read at
the preimage `Φ⁻¹ y`. -/
private theorem classicalPrincipalSymbol_pushforwardOperator_apply
    (Φ : M ≃ₘ^∞⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M) (y : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) y →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (Φ.pushforwardOperator P) y ξ =
      classicalPrincipalSymbol m P (Φ.symm y)
        (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ (Φ.symm y))) := by
  have h := classicalPrincipalSymbol_pushforwardOperator (P := P) (m := m) Φ (Φ.symm y) ξ
  rwa [Φ.apply_symm_apply] at h

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
  rw [classicalPrincipalSymbol_averageMap ρ hP, Finset.sum_congr rfl fun g _ ↦ h g,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, invOf_mul_cancel_left]

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- Pulling a nonzero covector back along a diffeomorphism gives a nonzero covector. -/
private theorem comp_mfderiv_ne_zero
    (Φ : M ≃ₘ^∞⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M) (y : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) (Φ y) →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ y) ≠ 0 := by
  refine fun h ↦ hξ (ContinuousLinearMap.ext fun v ↦ ?_)
  -- Evaluate `ξ ∘ dΦ_y = 0` at `dΦ⁻¹ v`, and use `dΦ_y (dΦ⁻¹ v) = v`. The vector `dΦ⁻¹ v` lies in
  -- the tangent space at `Φ⁻¹ (Φ y)`, equal to the one at `y` only definitionally, so `h'` is
  -- read through `ContinuousLinearMap.comp_apply` by unfolding rather than by rewriting.
  have h' := DFunLike.congr_fun h
    (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ.symm (Φ y) v)
  exact (congrArg ξ (Φ.mfderiv_apply_mfderiv_symm_apply (by simp) y v)).symm.trans h'

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
  rw [classicalPrincipalSymbol_averageMap ρ hP, invOf_eq_inv, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  refine mul_pos (by simp [Fintype.card_pos]) (Finset.sum_pos (fun g _ ↦ hpos _ _ ?_)
    Finset.univ_nonempty)
  exact comp_mfderiv_ne_zero (ρ g) ((ρ g).symm x) hξ

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
