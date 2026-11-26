/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions

/-!
# The diffeomorphism group acting on operators by pushforward

The diffeomorphism group of a manifold `M` acts on the complex-linear operators on `C^n(M, ℂ)` by
pushforward, `Φ_* P : u ↦ P (u ∘ Φ) ∘ Φ⁻¹` (`Diffeomorph.pushforwardOperator`); this file packages
the action as a group homomorphism (`Diffeomorph.pushforwardOperatorHom`) and as a linear
representation (`Diffeomorph.pushforwardOperatorRepresentation`). For a homomorphism
`ρ : G →* (M ≃ₘ M)` from a finite group, Mathlib's `Representation.averageMap` of the composite
representation is the **average** `avg(P) = |G|⁻¹ ∑_g (ρ g)_* P`
(`Representation.averageMap_apply`). It is invariant under every `(ρ g)_*`, that is, it commutes
with precomposition by every `ρ g` (`Diffeomorph.averageMap_compRightComplexAlgEquiv`), and it
fixes the invariant operators (`Representation.averageMap_id`). Averaging is how an operator is made
equivariant for a group action, as needed for equivariant elliptic operators and their indices.

## Main definitions

* `Diffeomorph.pushforwardOperatorHom`, `Diffeomorph.pushforwardOperatorRepresentation`: the
  pushforward action of the diffeomorphism group on operators.

## Main results

* `Diffeomorph.pushforwardOperator_averageMap`, `Diffeomorph.averageMap_compRightComplexAlgEquiv`:
  the average is invariant and equivariant.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §5, (5.5)–(5.6), pp. 516–517 (averaging operators over a compact group).
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
