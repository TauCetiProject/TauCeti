/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complex conjugation generates the real Galois group

Mathlib classifies real algebra homomorphisms of `ℂ` as the identity or conjugation. Here that
classification is expressed as the generator condition used by cyclic group cohomology. The
quadratic-extension instance makes the Galois structure of `ℂ/ℝ` available to that API.
-/

public section

namespace TauCeti

/-- The complex numbers form a quadratic extension of the reals. -/
instance instIsQuadraticExtensionRealComplex : Algebra.IsQuadraticExtension ℝ ℂ :=
  ⟨Complex.finrank_real_complex⟩

/-- Complex conjugation generates the full group of real algebra automorphisms of `ℂ`. -/
@[simp] theorem zpowers_conjAe_eq_top : Subgroup.zpowers Complex.conjAe = ⊤ :=
  (Subgroup.eq_top_iff' _).2 fun σ ↦
    (Complex.real_algHom_eq_id_or_conj σ).elim
      (fun h ↦ ((AlgEquiv.coe_toAlgHom_injective (h.trans AlgEquiv.refl_toAlgHom.symm)).trans
        AlgEquiv.aut_one.symm) ▸ one_mem _)
      fun h ↦ AlgEquiv.coe_toAlgHom_injective h ▸ Subgroup.mem_zpowers _

end TauCeti
