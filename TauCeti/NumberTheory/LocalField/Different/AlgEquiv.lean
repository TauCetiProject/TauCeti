/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant
import TauCeti.RingTheory.DedekindDomain.Different.Monogenic
import TauCeti.RingTheory.DiscreteValuationRing.Monogenic

/-!
# The different and discriminant under isomorphism

A base-field algebra equivalence between finite extensions of a nonarchimedean local field
restricts to their rings of integers. It preserves the different ideal and hence the different
and discriminant exponents. These invariants therefore depend only on the extension up to
base-field equivalence. The proof uses local monogenicity and the derivative formula for the
different (Serre, *Local Fields*, Chapter III, §6).
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

variable [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

/-- The different ideal is carried to the different ideal by an equivalence of extensions. -/
theorem differentIdeal_map_integerRingEquiv (e : L ≃ₐ[K] M) :
    (differentIdeal 𝒪[K] 𝒪[L]).map e.integerRingEquiv =
      differentIdeal 𝒪[K] 𝒪[M] := by
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top
    (R := 𝒪[K]) (S := 𝒪[L])
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
  apply (pow_dvd_differentIdeal_iff_le_differentExponent (K := K) (L := M)).mp
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.integerRingEquiv.toRingEquiv,
    ← Ideal.map_pow,
    ← differentIdeal_map_integerRingEquiv K L M e]
  exact Ideal.dvd_iff_le.mpr (Ideal.map_mono (Ideal.dvd_iff_le.mp
    ((pow_dvd_differentIdeal_iff_le_differentExponent (K := K) (L := L)).mpr le_rfl)))

/-- The different exponent is invariant under equivalence of finite extensions over `K`. -/
theorem differentExponent_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    differentExponent K L = differentExponent K M :=
  Nat.le_antisymm (differentExponent_le_of_algEquiv K L M e)
    (differentExponent_le_of_algEquiv K M L e.symm)

/-- The discriminant ideal is unchanged by an equivalence of extensions over the base field. -/
theorem discriminantIdeal_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    discriminantIdeal K L = discriminantIdeal K M := by
  rw [discriminantIdeal_def, discriminantIdeal_def,
    ← differentIdeal_map_integerRingEquiv K L M e, Ideal.relNorm_map_algEquiv]

/-- The local discriminant exponent is invariant under equivalence of finite extensions. -/
theorem discriminantExponent_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    discriminantExponent K L = discriminantExponent K M := by
  rw [discriminantExponent_def, discriminantExponent_def,
    discriminantIdeal_eq_of_algEquiv K L M e]

end TauCeti
