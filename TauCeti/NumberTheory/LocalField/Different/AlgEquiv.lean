/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Basic
public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.NumberTheory.LocalField.Monogenic
import TauCeti.RingTheory.DedekindDomain.Different.Monogenic

/-!
# The different under isomorphism

A base-field algebra equivalence between finite extensions of a nonarchimedean local field
restricts to their rings of integers. It preserves the different ideal and its exponent,
so these invariants depend only on the extension's isomorphism class
(Serre, *Local Fields*, Chapter III, §6).
-/

public section
noncomputable section

open ValuativeRel IsLocalRing Polynomial

namespace TauCeti

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]

variable [Algebra.IsSeparable K L]

/-- The different ideal is carried to the different ideal by an equivalence of extensions. -/
@[simp]
theorem differentIdeal_map_integerRingEquiv (e : L ≃ₐ[K] M) :
    (differentIdeal 𝒪[K] 𝒪[L]).map e.integerRingEquiv =
      differentIdeal 𝒪[K] 𝒪[M] := by
  have : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
  obtain ⟨x, hx⟩ := exists_integerRing_adjoin_eq_top K L
  have hy : Algebra.adjoin 𝒪[K] {e.integerRingEquiv x} = ⊤ := by
    have hmap := AlgHom.map_adjoin_singleton (e.integerRingEquiv.toAlgHom) x
    rw [hx] at hmap
    rw [Algebra.map_top] at hmap
    have hrange : (e.integerRingEquiv.toAlgHom).range = ⊤ :=
      (AlgHom.range_eq_top _).2 e.integerRingEquiv.surjective
    rw [hrange] at hmap
    exact hmap.symm
  rw [differentIdeal_eq_span_aeval_derivative_minpoly 𝒪[K] K L 𝒪[L] x hx,
    differentIdeal_eq_span_aeval_derivative_minpoly 𝒪[K] K M 𝒪[M]
      (e.integerRingEquiv x) hy]
  simp only [Ideal.map_span, Set.image_singleton]
  apply congrArg (fun z : 𝒪[M] => Ideal.span {z})
  rw [minpoly.algEquiv_eq e.integerRingEquiv x]
  simpa using
    (congrArg (fun f => f (derivative (minpoly 𝒪[K] x)))
      (Polynomial.aeval_algEquiv e.integerRingEquiv x)).symm

private theorem differentExponent_le_of_algEquiv (e : L ≃ₐ[K] M) :
    differentExponent K L ≤ differentExponent K M := by
  have : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
  apply (pow_dvd_differentIdeal_iff_le_differentExponent (K := K) (L := M)).mp
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.integerRingEquiv.toRingEquiv,
    ← Ideal.map_pow,
    ← differentIdeal_map_integerRingEquiv K L M e]
  exact Ideal.dvd_iff_le.mpr (Ideal.map_mono (Ideal.dvd_iff_le.mp
    ((pow_dvd_differentIdeal_iff_le_differentExponent (K := K) (L := L)).mpr le_rfl)))

/-- The different exponent is invariant under equivalence of finite extensions over `K`. -/
theorem differentExponent_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    differentExponent K L = differentExponent K M := by
  have : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
  exact Nat.le_antisymm (differentExponent_le_of_algEquiv K L M e)
    (differentExponent_le_of_algEquiv K M L e.symm)

end TauCeti
