/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.Dual
public import TauCeti.RingTheory.Depth.Bijectivity
public import TauCeti.RingTheory.CohenMacaulay.Normal
public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.RingTheory.Localization.Module
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Reflexive duals over normal domains

Over a Noetherian integrally closed domain, the dual of every finite module is reflexive.
In particular its double dual is a reflexive module, even when the original module has torsion.
The assertion uses the canonical evaluation map of Mathlib's `Module.IsReflexive`.

In codimension at most one the local rings are principal ideal domains and finite torsion-free
modules are free. In higher codimension dual modules have depth at least two; the local depth
criterion for bijectivity then applies to evaluation. This is the algebraic input to reflexive
hulls of coherent sheaves on normal schemes.

## References

* Stacks Project, Lemma 31.13.8 (Tag 0AY4), with target the structure sheaf.
-/

public section

open Module

universe u v

namespace Ideal

/-- Evaluation on a finite torsion-free module over a Noetherian normal domain becomes
bijective at every prime of height at most one. -/
theorem bijective_localizedModule_map_dual_eval_of_height_le_one
    {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsTorsionFree R M] (p : Ideal R) [p.IsPrime] (hp : p.height ≤ 1) :
    Function.Bijective (LocalizedModule.map p.primeCompl (Dual.eval R M)) := by
  have := finitePresentation_of_finite R M
  have := finitePresentation_of_finite R (Dual R M)
  have := IsLocalization.AtPrime.isPrincipalIdealRing_of_height_le_one hp
    (Localization.AtPrime p)
  exact (LocalizedModule.bijective_map_dual_eval_iff p.primeCompl
    (Localization.AtPrime p) (LocalizedModule.mkLinearMap p.primeCompl M)).mpr
      (bijective_dual_eval (Localization.AtPrime p) _)

end Ideal

namespace TauCeti

/-- Over a Noetherian integrally closed domain, the dual of any finite module is reflexive. -/
instance isReflexive_dual_of_isIntegrallyClosed {R : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsReflexive R (Dual R M) := by
  -- The depth API uses a common universe for the ring and its modules. Finite
  -- modules can be shrunk to the universe of the ring without changing their duals.
  have h (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
      IsReflexive R (Dual R M) := by
    have := finitePresentation_of_finite R (Dual R M)
    have := finitePresentation_of_finite R (Dual R (Dual R M))
    constructor
    apply LinearMap.bijective_of_depth_of_addCommGroup
    intro p _
    by_cases hp : p.height ≤ 1
    · left
      -- The localization comparison requires a group structure extending the dual's
      -- existing additive monoid; its conclusion only concerns the evaluation function.
      let : AddCommGroup (Dual R M) := Module.addCommMonoidToAddCommGroup R
      exact p.bijective_localizedModule_map_dual_eval_of_height_le_one hp
    · right
      have : IsIntegrallyClosed (Localization.AtPrime p) :=
        isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
      have hd : 2 ≤ ringKrullDim (Localization.AtPrime p) := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
        exact WithBot.coe_le_coe.mpr (not_lt.mp fun h ↦ hp (ENat.lt_two_iff.mp h))
      have hdepth := IsLocalRing.two_le_depth_of_isIntegrallyClosed hd
      refine ⟨Ideal.le_depth_localizedModule_dual (M := M) p (n := 2) le_rfl hdepth, ?_⟩
      apply (TauCeti.one_le_depth_localizedModule_iff (p := p)).mp
      exact one_le_two.trans (Ideal.le_depth_localizedModule_dual
        (M := Dual R (Dual R M)) p (n := 2) le_rfl hdepth)
  have : Small.{u} M := Module.Finite.small R M
  have := h (Shrink.{u} M)
  exact Module.equiv (Shrink.linearEquiv R M).dualMap.symm

end TauCeti
