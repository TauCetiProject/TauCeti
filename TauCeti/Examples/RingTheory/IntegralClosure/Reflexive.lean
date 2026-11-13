/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.IntegralClosure.Reflexive
import TauCeti.LinearAlgebra.Dual.DoubleDual
import Mathlib.Data.ZMod.Basic

/-!
# Reflexive-hull examples

The double dual of a finite module over a Noetherian normal domain is reflexive, and maps to
reflexive modules extend uniquely across evaluation. The mixed module `ℤ × ℤ/2` demonstrates
that the source may have torsion: evaluation kills its torsion summand but not its free summand.
-/

open Module TauCeti

section NormalDomain

variable {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [AddCommGroup M] [Module R M] [Module.Finite R M]

-- A double dual really is reflexive, not merely torsion-free.
example : IsReflexive R (Dual R (Dual R M)) := inferInstance

-- The target need not be finite; reflexivity alone suffices for the universal property.
example {N : Type*} [AddCommMonoid N] [Module R N] [IsReflexive R N] (f : M →ₗ[R] N) :
    ∃! g : Dual R (Dual R M) →ₗ[R] N, g.comp (Dual.eval R M) = f :=
  TauCeti.Module.Dual.existsUnique_comp_eval_eq R M N f

-- The pointwise extension rule simplifies without unfolding the equivalence.
example {N : Type*} [AddCommMonoid N] [Module R N] [IsReflexive R N]
    (f : M →ₗ[R] N) (m : M) :
    (TauCeti.Module.Dual.evalHomEquiv R M N).symm f (Dual.eval R M m) = f m := by
  simp

end NormalDomain

-- A module with both a nonzero free summand and nonzero torsion is admitted.
example : IsReflexive ℤ (Dual ℤ (ℤ × ZMod 2)) :=
  TauCeti.isReflexive_dual_of_isIntegrallyClosed

-- The free summand survives evaluation.
example : Dual.eval ℤ (ℤ × ZMod 2) (1, 0) ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h (LinearMap.fst ℤ ℤ (ZMod 2))
  simp at this

-- The torsion summand is killed, so evaluation need not be injective.
example : Dual.eval ℤ (ℤ × ZMod 2) (0, 1) = 0 := by
  ext φ
  have hx : (2 : ℤ) • ((0, 1) : ℤ × ZMod 2) = 0 := by decide
  have h : (2 : ℤ) * φ (0, 1) = 0 := by
    simpa using (φ.map_smul (2 : ℤ) (0, 1)).symm.trans (congrArg φ hx)
  simpa using (mul_eq_zero.mp h).resolve_left (by decide : (2 : ℤ) ≠ 0)

-- The extension is usable without unfolding the Hom equivalence.
example (f : (ℤ × ZMod 2) →ₗ[ℤ] ℤ) :
    ∃ g : Dual ℤ (Dual ℤ (ℤ × ZMod 2)) →ₗ[ℤ] ℤ,
      g.comp (Dual.eval ℤ (ℤ × ZMod 2)) = f := by
  exact ⟨(TauCeti.Module.Dual.evalHomEquiv ℤ (ℤ × ZMod 2) ℤ).symm f, by simp⟩
