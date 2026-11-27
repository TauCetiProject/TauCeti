/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GoodPrimes
import Mathlib.Data.Nat.Prime.Infinite
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel

/-!
# Good reduction at all but finitely many rational primes

In the prime indexing of `WeierstrassCurve.goodReductionPrimes`, the bad primes of an elliptic
curve over `ℚ` form a finite set. Any integral equation in the isomorphism class bounds the
exceptional set by the prime divisors of its nonzero discriminant.

See J. H. Silverman, *The Arithmetic of Elliptic Curves*, VII.1.
-/

public section

open Filter

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- Only finitely many rational primes have bad reduction. -/
theorem finite_not_hasGoodReductionAt : {p : Nat.Primes | ¬ E.HasGoodReductionAt p}.Finite := by
  obtain ⟨C, hC⟩ := exists_smul_isIntegral ℤ E
  let W := integralModel ℤ (C • E)
  have hW : W.baseChange ℚ = C • E := baseChange_integralModel_eq ℤ _
  have hΔ : W.Δ ≠ 0 := by
    intro h0
    have h := (C • E).isUnit_Δ.ne_zero
    rw [← hW, baseChange, map_Δ, h0, map_zero] at h
    exact h rfl
  refine ((Set.finite_Iic W.Δ.natAbs).preimage Subtype.val_injective.injOn).subset ?_
  intro p hp
  have hd : (p : ℤ) ∣ W.Δ := by
    by_contra h
    have hgood := W.hasGoodReductionAt_baseChange_of_not_dvd p h
    rw [hW] at hgood
    exact hp ((E.hasGoodReductionAt_smul C).mp hgood)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hΔ) (by simpa using Int.natAbs_dvd_natAbs.mpr hd)

/-- The sample of good primes below a growing cutoff is eventually nonempty. -/
theorem eventually_goodReductionPrimes_nonempty :
    ∀ᶠ x in atTop, (E.goodReductionPrimes x).Nonempty := by
  classical
  let S := E.finite_not_hasGoodReductionAt.toFinset
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (S.sup Subtype.val + 1)
  have hgood : E.HasGoodReductionAt ⟨p, hp⟩ := by
    by_contra hbad
    have hmem : (⟨p, hp⟩ : Nat.Primes) ∈ S :=
      (Set.Finite.mem_toFinset _).mpr hbad
    exact Nat.not_succ_le_self _ (hle.trans (Finset.le_sup (f := Subtype.val) hmem))
  exact (eventually_ge_atTop p).mono fun _ hx ↦
    ⟨⟨p, hp⟩, (E.mem_goodReductionPrimes).2 ⟨hx, hgood⟩⟩

end WeierstrassCurve
