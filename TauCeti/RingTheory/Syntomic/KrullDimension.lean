/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RingHom.StandardSyntomic
import Mathlib.RingTheory.Ideal.Height

/-!
# Krull dimension of locally standard syntomic algebras over a field

An algebra over a field `k` which is locally standard syntomic of relative dimension `n` has Krull
dimension at most `n` (`TauCeti.ringKrullDim_le_of_locally_isStandardSyntomicOfRelativeDimension`):
every prime lies in a standard syntomic chart, and a nonzero chart has dimension exactly `n`.
-/

public section

namespace TauCeti

universe u

variable {n : ℕ}

open TensorProduct in
/-- An algebra over a field which is locally standard syntomic of relative dimension `n` has Krull
dimension at most `n`. -/
theorem ringKrullDim_le_of_locally_isStandardSyntomicOfRelativeDimension {k A : Type u} [Field k]
    [CommRing A] [Algebra k A]
    (h : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n) (algebraMap k A)) :
    ringKrullDim A ≤ n := by
  refine (ringKrullDim_le_iff_height_le _).mpr fun P hP ↦ ?_
  -- Some chart `A[1/t]` of the cover contains `P`, and the height of `P` is computed there.
  obtain ⟨t, hdisj, _⟩ :=
    exists_disjoint_powers_isStandardSyntomicOfRelativeDimension_of_locally h P hP.ne_top
  have hPt : (P.map (algebraMap A (Localization.Away t))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P hP hdisj.symm
  -- The chart is nonzero, so over the field `k` its Krull dimension is exactly `n`.
  let e := Algebra.TensorProduct.lid k (Localization.Away t)
  have : Nontrivial (Localization.Away t) := PrimeSpectrum.nontrivial ⟨_, hPt⟩
  have : Nontrivial (k ⊗[k] Localization.Away t) := e.toEquiv.nontrivial
  rw [← IsLocalization.height_map_of_disjoint (S := Localization.Away t) (.powers t) P
    hdisj.symm]
  refine Ideal.height_le_ringKrullDim_of_isPrime.trans_eq ?_
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    Algebra.IsStandardSyntomicOfRelativeDimension.ringKrullDim_tensorProduct_of_field (n := n) k]

end TauCeti
