/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Basic
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Total acyclicity over self-injective rings

Over a left self-injective ring, an acyclic complex of finite projective left modules is totally
acyclic. Injectivity of the regular module makes every cocycle in the dual complex a coboundary.
Applied to the opposite ring, this supplies the same assertion for right modules.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
-/

public section

open CategoryTheory

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

/-- Over a left self-injective ring, acyclicity of a complex of finite projective modules implies
total acyclicity. Modules live in the ring's universe, so the regular module is an object of
the coefficient category. -/
theorem isTotallyAcyclic_of_acyclic_of_moduleInjective_self
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hl : Module.Injective A A)
    (hfinite : ∀ n, Module.Finite A (P.X n)) (hproj : ∀ n, Projective (P.X n))
    (hP : P.Acyclic) : P.IsTotallyAcyclic where
  finite := hfinite
  projective := hproj
  acyclic := hP
  exact_dual i j k hij hjk := by
    let := hl
    have : Injective (ModuleCat.of A A) := Module.injective_object_of_injective_module A A
    have hS : (P.sc' i j k).Exact :=
      (HomologicalComplex.exactAt_iff' P i j k
        (by
          have h : j - 1 = i := by omega
          simpa using h) (by simpa using hjk)).mp
        (hP j)
    intro φ
    constructor
    · intro hφ
      have hz : P.d i j ≫ ModuleCat.ofHom φ = 0 := ModuleCat.hom_ext hφ
      let ψ := hS.descToInjective (ModuleCat.ofHom φ) hz
      exact ⟨ψ.hom, congrArg ModuleCat.Hom.hom (hS.comp_descToInjective _ hz)⟩
    · rintro ⟨ψ, rfl⟩
      ext x
      have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (P.d_comp_d i j k)) x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
        LinearMap.zero_apply] at hz
      simp [hz]

end CochainComplex
