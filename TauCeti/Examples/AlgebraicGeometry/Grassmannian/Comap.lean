/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Comap

import TauCeti.Algebra.DualNumber.Basic

/-!
# Checks for quotient incidence embeddings

In quotient rank zero the incidence embedding is an isomorphism, including zero modules and
the zero ring. For a nilpotent Jordan block on a free module of rank two, the stable line
spanned by `e₁ + ε e₂` over the dual numbers reduces to the line of `e₁`, but is outside every
quotient incidence image whose kernels must contain `e₁`. This is the infinitesimal check for
the first coefficient-window inclusion: `e₁` is the top degree and `e₂` the bottom degree.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Module Module.Grassmannian DualNumber

namespace TauCeti.Grassmannian.Comap

variable {R M P : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

/-- The quotient-rank-zero boundary requires no nontriviality or positive window size. -/
example (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    IsIso (f.grassmannianComap hf 0) :=
  IsIso.of_isIso_fac_right (f.grassmannianComap_toSpec hf 0)

variable (b : Basis (Fin 1 ⊕ Fin 1) R M) {t : Module.End R M}
  (ht₁ : t (b (.inl 0)) = 0) (ht₂ : t (b (.inr 0)) = b (.inl 0))

/-- The infinitesimal stable line is outside the incidence image, over every nonzero base ring. -/
example [Nontrivial R] (f : M →ₗ[R] P) (hf : Function.Surjective f)
    (hf₁ : f (b (.inl 0)) = 0) :
    ¬∃ c : Spec (.of R[ε]) ⟶ scheme R P 1,
      c ≫ f.grassmannianComap hf 1 =
        toSchemeHom ((jordanBlockStableEquiv b ht₁ ht₂ R[ε]).symm
          ⟨ε, by rw [sq, eps_mul_eps]⟩).val := by
  rw [exists_comp_grassmannianComap_eq_iff]
  intro h
  have hb : b (.inl 0) ∈ LinearMap.ker f := by simpa using hf₁
  have hm := h (Submodule.tmul_mem_baseChange_of_mem (1 : R[ε]) hb)
  rw [toSubmodule_jordanBlockStableEquiv_symm_apply] at hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have h₁ := congrArg (fun x ↦ (b.baseChange R[ε]).repr x (.inl 0)) ha
  have h₂ := congrArg (fun x ↦ (b.baseChange R[ε]).repr x (.inr 0)) ha
  have ha' : a = 1 := by simpa [Basis.baseChange_repr_tmul] using h₁
  have hε : a * ε = 0 := by simpa [Basis.baseChange_repr_tmul] using h₂
  exact eps_ne_zero (by simpa [ha'] using hε)

/-- Reduction kills the infinitesimal parameter and recovers the standard stable line. -/
example :
    map (TrivSqZeroExt.fstHom R R R)
        ((jordanBlockStableEquiv b ht₁ ht₂ R[ε]).symm
          ⟨ε, by rw [sq, eps_mul_eps]⟩).val =
      ((jordanBlockStableEquiv b ht₁ ht₂ R).symm ⟨0, by simp⟩).val := by
  simpa using map_jordanBlockStableEquiv_symm_apply b ht₁ ht₂
    (TrivSqZeroExt.fstHom R R R) ⟨ε, by rw [sq, eps_mul_eps]⟩

end TauCeti.Grassmannian.Comap
