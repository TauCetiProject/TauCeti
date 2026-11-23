/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RingTheory.MatlisDuality.Basic

import TauCeti.RingTheory.Artinian.Module

/-!
# Embedding Artinian modules into finite powers of the dual regular module

Let `R` be a commutative ring, `E` an `R`-module and `A` an `R`-algebra. If evaluation
`N → D_R (D_R N)` is injective for an Artinian left `A`-module `N`, as it is when `E` is an
injective cogenerator of `R`-modules, then `N` embeds into a finite power of `D_R A`, the dual of
the right regular module (`TauCeti.exists_injective_linearMap_pi_matlisDual`). A functional on `N`
that does not kill an element gives, through the Hom-tensor adjunction
`TauCeti.MatlisDual.equivLinearMapDualRegular`, a map `N → D_R A` that does not kill it, and
finitely many such maps suffice as `N` is Artinian (`IsArtinian.exists_injective_linearMap_pi`).

## Main results

* `TauCeti.exists_injective_linearMap_pi_matlisDual`: an Artinian module with injective evaluation
  into its double dual embeds into a finite power of `D_R A`.
-/

public section

namespace TauCeti

open MatlisDual

universe u v w t

section Cogenerator

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E] {A : Type t} [Ring A]
  [Algebra R A] {N : Type w} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- **Embedding into a finite power of `D_R A`.** An Artinian left `A`-module `N` for which
evaluation `N → D_R (D_R N)` is injective, as it is when `E` is an injective cogenerator of
`R`-modules, embeds into a finite power of `D_R A`. -/
theorem exists_injective_linearMap_pi_matlisDual [IsArtinian A N]
    (hEval : Function.Injective (MatlisDual.evalₗ R E N)) :
    ∃ (n : ℕ) (g : N →ₗ[A] (Fin n → MatlisDual R E A)), Function.Injective g := by
  refine IsArtinian.exists_injective_linearMap_pi fun x hx ↦ ?_
  -- Some functional `φ` on `N` does not kill `x`; its adjoint `N → D_R A` does not kill `x`
  -- either, evaluating at `1`.
  obtain ⟨φ, hφ⟩ : ∃ φ : MatlisDual R E N, equivLinearMap R E N φ x ≠ 0 := by
    by_contra! h
    exact hx (hEval (MatlisDual.ext fun φ ↦ by simpa using h φ))
  refine ⟨equivLinearMapDualRegular φ, fun h ↦ hφ ?_⟩
  simpa using congr(equivLinearMap R E A $h 1)

end Cogenerator

end TauCeti
