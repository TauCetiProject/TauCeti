/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.FiniteEtale.Limits
public import TauCeti.CategoryTheory.Extensive

/-!
# Exactness of base change and of geometric fibre functors

Base change `FiniteEtaleScheme.pullback f` of finite étale schemes along any morphism of
schemes `f : T ⟶ S` preserves finite limits, finite coproducts and epimorphisms. Composing with
the classification of finite étale schemes over a separably closed field, the same holds for
every geometric fibre functor `FiniteEtaleScheme.fiber x : FiniteEtaleScheme S ⥤ FintypeCat`.

These are the axiom (G4) and the finite-coproduct and epimorphism parts of the axiom (G5) for a
fibre functor in the sense of Lenstra, that is, the fields `preservesTerminalObjects`,
`preservesPullbacks`, `preservesFiniteCoproducts` and `preservesEpis` of Mathlib's
`CategoryTheory.PreGaloisCategory.FiberFunctor`. Preservation of quotients by finite groups and
conservativity are not treated here.

Finite limits are preserved because `Over.pullback f` is a right adjoint, and finite coproducts
because finite coproducts of schemes are universal (`CategoryTheory.FinitaryExtensive`). For
epimorphisms we use that an epimorphism of finite étale schemes is the same as a morphism that
is surjective on underlying schemes (`TauCeti.FiniteEtaleScheme.epi_iff_surjective`), and that
surjectivity is stable under base change.

## References

* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}}

/-- Base change of finite étale schemes preserves finite limits. -/
instance (f : T ⟶ S) : PreservesFiniteLimits (pullback f) := by
  have : PreservesFiniteLimits (pullback f ⋙ (finiteEtaleSchemeProperty T).ι) := by
    rw [pullback_comp_ι]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (finiteEtaleSchemeProperty T).ι

/-- Base change of finite étale schemes preserves finite coproducts. -/
instance (f : T ⟶ S) : PreservesFiniteCoproducts (pullback f) := by
  have : PreservesFiniteCoproducts (pullback f ⋙ (finiteEtaleSchemeProperty T).ι) := by
    rw [pullback_comp_ι]
    exact ⟨fun _ ↦ inferInstance⟩
  exact preservesFiniteCoproducts_of_reflects_of_preserves _ (finiteEtaleSchemeProperty T).ι

/-- Base change of finite étale schemes preserves epimorphisms. -/
instance (f : T ⟶ S) : (pullback f).PreservesEpimorphisms where
  preserves {X Y} g _ := by
    have : Surjective ((pullback f).map g).hom.left :=
      MorphismProperty.of_isPullback
        (Over.isPullback_pullback_map_left f ((finiteEtaleSchemeProperty S).ι.map g)).flip
        (inferInstanceAs (Surjective g.hom.left))
    exact epi_of_surjective _

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)

/-- The geometric fibre functor preserves finite limits. -/
instance : PreservesFiniteLimits (fiber x) := by
  rw [fiber_def]
  infer_instance

/-- The geometric fibre functor preserves finite coproducts. -/
instance : PreservesFiniteCoproducts (fiber x) := by
  rw [fiber_def]
  infer_instance

/-- The geometric fibre functor preserves epimorphisms. -/
instance : (fiber x).PreservesEpimorphisms := by
  rw [fiber_def]
  infer_instance

end TauCeti.FiniteEtaleScheme
