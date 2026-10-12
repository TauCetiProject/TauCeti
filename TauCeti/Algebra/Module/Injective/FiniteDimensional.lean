/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Dual.ProjectiveInjective
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Module.Injective.SelfInjective
public import TauCeti.LinearAlgebra.Dual.Cogenerator

/-!
# Finite-dimensional injective modules over a self-injective algebra

Let `A` be a finite-dimensional algebra over a field `k`, and write `D = Hom_k(-, k)`. The dual
`D(A_A)` of the right regular module is a left `A`-module, by `(a · φ) x = φ (x * a)`. This file
proves that when `A` is **right self-injective** (its regular right module is injective), every
finite-dimensional injective left `A`-module is projective. Together with
`Module.Injective.of_finite_projective`, which gives the converse from left self-injectivity, it
identifies the projective and the injective finite-dimensional modules over an algebra which is
self-injective on both sides: the projective-injective objects of the Frobenius exact category of
finite-dimensional modules.

The argument is duality, in two steps.

* `D(A_A)` is projective. Dualizing a free presentation `Aⁿ → D(A_A)` gives an embedding of `A_A`
  into the right module `D(Aⁿ)`; right self-injectivity splits it, and dualizing the splitting
  back produces a section of the presentation.
* Every finite-dimensional left module embeds into a finite power of `D(A_A)`, through the maps
  `m ↦ (x ↦ χ (x • m))` for `χ` running over a basis of `D M`. An injective module is then a
  retract of a projective one.

The left module `D(A_A)` is not installed as an instance on `Module.Dual k A` (see
`TauCeti/LinearAlgebra/Dual/RightAction.lean`). The duality and cogenerator results take an
arbitrary left `A`-module `Q` together with a `k`-linear identification `e : Q ≃ₗ[k] Dual k A`
carrying the action of `a` to precomposition with right multiplication by `a`.

## Main results

* `LinearEquiv.moduleProjective_of_dual_injective` supplies the projectivity of `D(A_A)`
  from right self-injectivity, as a special case of finite module duality.
* `LinearEquiv.exists_injective_linearMap_pi_of_dual`: `D(A_A)` is a cogenerator for
  finite-dimensional modules; each embeds into a finite power of it.
* `Module.Projective.of_finiteDimensional_injective`: over a finite-dimensional right
  self-injective algebra, every finite-dimensional injective module is projective.
* `Module.Finite.exists_injective_linearMap_pi`: over a finite-dimensional right self-injective
  algebra, every finitely generated module embeds into a finite free module.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Section 3 (injective modules) and Section 15
  (quasi-Frobenius rings, where injective and projective modules coincide).
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras* I, Chapter I (the standard duality `D` and projective and injective modules).
-/

public section

namespace TauCeti

universe u v w

variable {k : Type w} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- **Over a finite-dimensional right self-injective algebra, finite-dimensional injective modules
are projective.** Together with `Module.Injective.of_finite_projective`, this shows that over a
finite-dimensional algebra which is self-injective on both sides the finite-dimensional projective
and injective modules coincide. -/
theorem _root_.Module.Projective.of_finiteDimensional_injective [FiniteDimensional k A]
    (hA : Module.Injective Aᵐᵒᵖ A) (M : Type v) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] [Small.{v} A] [Module.Injective A M] :
    Module.Projective A M := by
  -- The left module `D(A_A)`: `(a · φ) x = φ (x * a)`.
  let : Module A (Module.Dual k A) := Module.compHom _ (dualRightAction k A)
  have hsmul (a : A) (φ : Module.Dual k A) (x : A) : (a • φ) x = φ (x * a) :=
    (dualRightAction_apply_apply k A a φ x).trans (by rw [op_smul_eq_mul])
  let : Module.Injective Aᵐᵒᵖ A := hA
  have := (LinearEquiv.refl k (Module.Dual k A)).moduleProjective_of_dual_injective (A := A)
    (fun a φ x ↦ (hsmul a φ x).trans (by simp))
  obtain ⟨n, f, hf⟩ := (LinearEquiv.refl k _).exists_injective_linearMap_pi_of_dual hsmul M
  have : Module.Projective A (Fin n → Module.Dual k A) :=
    .of_equiv' DFinsupp.linearEquivFunOnFintype
  obtain ⟨g, hg⟩ := Module.Injective.extension_property A M _ _ f hf LinearMap.id
  exact .of_split f g hg

/-- **Over a finite-dimensional right self-injective algebra, every finitely generated module
embeds into a finite free module.** The module embeds into a finite power of `D(A_A)`, which is
finitely generated and projective, hence a direct summand of a finite free module. -/
theorem _root_.Module.Finite.exists_injective_linearMap_pi [FiniteDimensional k A]
    (hA : Module.Injective Aᵐᵒᵖ A) (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] : ∃ (n : ℕ) (f : M →ₗ[A] (Fin n → A)), Function.Injective f := by
  -- `M` is finite-dimensional over `k` through the structure map `k → A`.
  let : Module k M := Module.compHom M (algebraMap k A)
  have : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : FiniteDimensional k M := Module.Finite.trans A M
  -- The left module `D(A_A)`: `(a · φ) x = φ (x * a)`.
  let : Module A (Module.Dual k A) := Module.compHom _ (dualRightAction k A)
  have hsmul (a : A) (φ : Module.Dual k A) (x : A) : (a • φ) x = φ (x * a) :=
    (dualRightAction_apply_apply k A a φ x).trans (by rw [op_smul_eq_mul])
  have : IsScalarTower k A (Module.Dual k A) := IsScalarTower.of_algebraMap_smul fun c φ ↦ by
    ext x
    simp only [hsmul, ← Algebra.commutes, ← Algebra.smul_def, map_smul,
      LinearMap.smul_apply]
  have : Module.Finite A (Module.Dual k A) := .of_restrictScalars_finite k A _
  let : Module.Injective Aᵐᵒᵖ A := hA
  have : Module.Projective A (Module.Dual k A) :=
    (LinearEquiv.refl k (Module.Dual k A)).moduleProjective_of_dual_injective (A := A)
      (fun a φ x ↦ (hsmul a φ x).trans (by simp))
  obtain ⟨n, f, hf⟩ := (LinearEquiv.refl k _).exists_injective_linearMap_pi_of_dual hsmul M
  have : Module.Projective A (Fin n → Module.Dual k A) :=
    .of_equiv' DFinsupp.linearEquivFunOnFintype
  obtain ⟨m, -, g, -, hg, -⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective A (Fin n → Module.Dual k A)
  exact ⟨m, g ∘ₗ f, hg.comp hf⟩

end TauCeti
