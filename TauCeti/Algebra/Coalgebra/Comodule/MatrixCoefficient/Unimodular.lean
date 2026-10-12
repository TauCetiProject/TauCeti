/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Unimodular
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation

/-!
# Matrix coefficients of a unimodular vector

In a finite projective comodule over a commutative Hopf algebra, the matrix coefficients
of a unimodular vector generate the unit ideal. Thus these coefficients can serve as
homogeneous coordinates of a morphism to projective space: they have no common zero,
including over nonreduced value algebras.

The result uses the invariant pairing of a comodule with its dual, formalized by
`Comodule.baseChangeEvaluation_dual_endOfPoint_invariant`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective orbits.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

/-- The matrix coefficients of a vector in a finite projective Hopf comodule generate the
unit ideal exactly when the vector is unimodular. -/
@[simp]
theorem span_matrixCoefficient_eq_top_iff_isUnimodular (m : M) :
    Ideal.span (Set.range fun φ : Module.Dual R M ↦
      matrixCoefficient (C := H) φ m) = ⊤ ↔ Module.IsUnimodular R m := by
  constructor
  · intro hm
    let J : Ideal R := LinearMap.range (LinearMap.applyₗ m)
    have hle : Ideal.span (Set.range fun φ : Module.Dual R M ↦
        matrixCoefficient (C := H) φ m) ≤ J.comap (Bialgebra.counitAlgHom R H) := by
      refine Ideal.span_le.mpr (Set.range_subset_iff.mpr fun φ ↦ ?_)
      exact ⟨φ, by simp⟩
    have h := hle (hm ▸ (by simp : (1 : H) ∈ (⊤ : Ideal H)))
    obtain ⟨φ, hφ⟩ := h
    exact Module.isUnimodular_of_apply_eq_one (by simpa using hφ)
  · intro hm
    obtain ⟨φ, hφ⟩ := Module.isUnimodular_iff.mp hm
    let I := Ideal.span (Set.range fun ψ : Module.Dual R M ↦
      matrixCoefficient (C := H) ψ m)
    have hmem (ξ : H ⊗[R] Module.Dual R M) :
        TauCeti.Module.Dual.baseChangeEvaluation ξ
          (endOfPoint M (AlgHom.id R H) (1 ⊗ₜ[R] m)) ∈ I := by
      induction ξ using TensorProduct.inductionOn with
      | add ξ η hξ hη => simpa using I.add_mem hξ hη
      | tmul h ψ =>
        simpa using I.mul_mem_left h (Ideal.subset_span (Set.mem_range_self ψ))
    let := dual (R := R) (H := H) (M := M)
    have h := hmem (endOfPoint (Module.Dual R M) (AlgHom.id R H) (1 ⊗ₜ[R] φ))
    rw [baseChangeEvaluation_dual_endOfPoint_invariant
      (WithConv.toConv (AlgHom.id R H)), TauCeti.Module.Dual.baseChangeEvaluation_tmul,
      hφ] at h
    exact (Ideal.eq_top_iff_one _).mpr (by simpa using h)

end TauCeti.Comodule
