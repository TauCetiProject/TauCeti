/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Copresentation.Basic
public import TauCeti.Algebra.Module.Injective.Envelope.FiniteDimensional

/-!
# Finite-dimensional minimal injective copresentations

Every finite-dimensional module over a finite-dimensional algebra admits a minimal injective
copresentation `0 → M → Q₀ → Q₁` with finite-dimensional injective terms. The first term is an
injective envelope of `M`, and the second is an injective envelope of its cokernel. Together with
uniqueness of minimal copresentations, this provides the first two terms of a minimal injective
resolution, as needed for the inverse Auslander–Reiten construction `Tr D`.

Both injective terms can be taken in the universe of the field and algebra, independently of
the universe of `M`. No algebraic closedness or self-injectivity assumption is required.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections I.5 and IV.1.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (M : Type w) [AddCommGroup M] [Module A M]

/-- A finite-dimensional module over a finite-dimensional algebra has a minimal injective
copresentation with both injective terms finite-dimensional, in the universe of the field and
algebra. -/
theorem exists_isMinimalInjectiveCopresentation_finiteDimensional
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] :
    ∃ (Q₀ : Type max u v) (_ : AddCommGroup Q₀) (_ : Module A Q₀) (_ : Module k Q₀)
      (_ : IsScalarTower k A Q₀) (_ : FiniteDimensional k Q₀)
      (Q₁ : Type max u v) (_ : AddCommGroup Q₁) (_ : Module A Q₁) (_ : Module k Q₁)
      (_ : IsScalarTower k A Q₁) (_ : FiniteDimensional k Q₁)
      (i₀ : M →ₗ[A] Q₀) (i₁ : Q₀ →ₗ[A] Q₁), IsMinimalInjectiveCopresentation i₀ i₁ := by
  obtain ⟨Q₀, _, _, _, _, _, i₀, h₀⟩ :=
    exists_isInjectiveEnvelope_finiteDimensional (k := k) (A := A) M
  obtain ⟨Q₁, _, _, _, _, _, j, h₁⟩ :=
    exists_isInjectiveEnvelope_finiteDimensional (k := k) (A := A) (Q₀ ⧸ LinearMap.range i₀)
  let i₁ := j ∘ₗ (LinearMap.range i₀).mkQ
  refine ⟨Q₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Q₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₀, i₁,
    h₀, ?_, h₁.moduleInjective, ?_⟩
  · exact h₁.injective.comp_exact_iff_exact.mpr (LinearMap.exact_map_mkQ_range i₀)
  · simpa only [i₁, LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top] using
      h₁.isEssential_range

/-- A finitely generated module over a finite-dimensional algebra has a finite-dimensional
minimal injective copresentation. The source's field action is induced through the algebra map. -/
theorem exists_isMinimalInjectiveCopresentation_of_finite [Module.Finite A M] :
    ∃ (Q₀ : Type max u v) (_ : AddCommGroup Q₀) (_ : Module A Q₀) (_ : Module k Q₀)
      (_ : IsScalarTower k A Q₀) (_ : FiniteDimensional k Q₀)
      (Q₁ : Type max u v) (_ : AddCommGroup Q₁) (_ : Module A Q₁) (_ : Module k Q₁)
      (_ : IsScalarTower k A Q₁) (_ : FiniteDimensional k Q₁)
      (i₀ : M →ₗ[A] Q₀) (i₁ : Q₀ →ₗ[A] Q₁), IsMinimalInjectiveCopresentation i₀ i₁ := by
  let : Module k M := Module.compHom M (algebraMap k A)
  let : IsScalarTower k A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : FiniteDimensional k M := Module.Finite.trans A M
  exact exists_isMinimalInjectiveCopresentation_finiteDimensional (k := k) (A := A) M

end TauCeti
