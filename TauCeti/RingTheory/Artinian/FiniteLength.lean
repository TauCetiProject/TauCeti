/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.LinearAlgebra.Dual.Defs
import TauCeti.LinearAlgebra.Dual.FiniteProjective

/-!
# Finitely generated modules over an Artinian ring have finite length

A finitely generated module over a left Artinian ring has finite length, which is one implication of
Mathlib's `IsArtinianRing.tfae`. The ring need not be commutative. The same holds over the base of
any finite extension, in particular for a finitely generated module over an Artin algebra. Over an
Artin algebra this applies to the dual `Hom_A(P, A)` of a finitely generated module.
-/

public section

universe u v w

namespace TauCeti

/-- A finitely generated module over an Artinian ring has finite length. -/
theorem isFiniteLength_of_finite (R : Type u) [Ring R] [IsArtinianRing R] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsFiniteLength R M :=
  isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- A module that is finitely generated over a finite extension `B` of an Artinian ring `R`, such as
an Artin `R`-algebra, has finite length over `R`. -/
theorem isFiniteLength_of_finite_trans (R : Type u) [Ring R] [IsArtinianRing R] (B : Type v)
    [Semiring B] [Module R B] [Module.Finite R B] (M : Type w) [AddCommGroup M] [Module R M]
    [Module B M] [IsScalarTower R B M] [Module.Finite B M] : IsFiniteLength R M :=
  have : Module.Finite R M := Module.Finite.trans B M
  isFiniteLength_of_finite R M

/-- Over an Artin `R`-algebra `A`, the dual `Hom_A(P, A)` of a finitely generated `A`-module has
finite length over `R`. -/
theorem isFiniteLength_dual (R : Type u) [CommRing R] [IsArtinianRing R] (A : Type v) [Ring A]
    [Algebra R A] [Module.Finite R A] (P : Type w) [AddCommGroup P] [Module A P]
    [Module.Finite A P] : IsFiniteLength R (Module.Dual A P) := by
  -- Precomposing with a surjection `Aⁿ → P` embeds `Hom_A(P, A)` into `Hom_A(Aⁿ, A)`.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A P
  have : IsNoetherian R (Module.Dual A (Fin n → A)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_of_finite_trans R Aᵐᵒᵖ (Module.Dual A (Fin n → A)))).1
  have : IsNoetherian R (Module.Dual A P) :=
    isNoetherian_of_injective (f.lcomp R A) fun _ _ h ↦ (LinearMap.cancel_right hf).mp h
  exact isFiniteLength_of_finite R _

end TauCeti
