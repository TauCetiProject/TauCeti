/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Cyclic

/-!
# Classification of cyclic dyadic quadratic modules

Every finite quadratic module whose underlying group is cyclic of order `2^k`, with `k ≥ 1`,
is isometric to a dyadic cyclic module `q_θ^{(2)}(2^k)`.  If the module is nondegenerate,
the coefficient `θ` is odd.  This identifies the cyclic constituents in the dyadic part of
Nikulin's generator decomposition; unlike the odd-primary case, general dyadic modules also
require the rank-two generators `u^{(2)}(2^k)` and `v^{(2)}(2^k)`.

The change-of-generator criterion is also explicit.  An additive automorphism of `ℤ/2^k` is
multiplication by a unit `u`, and it identifies the coefficients `θ` and `η` exactly when

```text
θ / 2^{k+1} = η u² / 2^{k+1}  in ℚ/ℤ.
```

The representative `u.val.val` in the theorem below is the canonical natural representative of
the unit modulo `2^k`.  Changing that representative by a multiple of `2^k` does not change its
square modulo `2^{k+1}`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.exists_dyadicCyclic_isometry_of_card_eq_two_pow`: every
  quadratic module on a cyclic group of order `2^k` has a dyadic cyclic presentation.
* `TauCeti.FiniteQuadraticModule.exists_dyadicCyclic_isometry`: in the nondegenerate case the
  coefficient can be taken odd.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_dyadicCyclic_iff`: the unit-square
  coefficient criterion modulo `2^{k+1}`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1 and 1.8.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open AddSubgroup

namespace TauCeti.FiniteQuadraticModule

/-- Every quadratic module on a cyclic group of order `2^k`, for `k ≥ 1`, has a dyadic cyclic
presentation.  No nondegeneracy hypothesis is needed. -/
theorem exists_dyadicCyclic_isometry_of_card_eq_two_pow (A : FiniteQuadraticModule)
    [IsAddCyclic A] {k : ℕ} [NeZero k] (hcard : Nat.card A = 2 ^ k) :
    ∃ θ : ℤ, Nonempty (Isometry (dyadicCyclic k θ) A) := by
  let e : ZMod (2 ^ k) ≃+ A := hcard ▸ zmodAddCyclicAddEquiv (G := A) inferInstance
  have hx : A.quadratic (e 1) ∈ (AddCircle (1 : ℚ))[((2 ^ (k + 1) : ℕ) : ℤ)] := by
    rw [torsionBy.nsmul_iff]
    simpa [hcard, pow_succ', mul_comm] using A.two_mul_natCard_nsmul_quadratic (e 1)
  obtain ⟨θ, hθ⟩ := AddCircle.exists_zsmul_eq_of_mem_torsionBy (1 : ℚ)
    (Nat.cast_ne_zero.mpr (pow_ne_zero _ two_ne_zero)) hx
  have hgen : A.quadratic (e 1) = (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) := by
    rw [← hθ, ← AddCircle.coe_zsmul, zsmul_eq_mul, ← Int.cast_one (R := ZMod (2 ^ k)),
      dyadicCyclic_quadratic_intCast]
    congr 1
    push_cast
    ring
  exact ⟨θ, ⟨cyclicIsometryOfGenerator (2 ^ k) _ _ e hgen⟩⟩

/-- Every nondegenerate quadratic module on a cyclic group of order `2^k`, for `k ≥ 1`, is
isometric to `q_θ^{(2)}(2^k)` for an odd coefficient `θ`. -/
theorem exists_dyadicCyclic_isometry (A : FiniteQuadraticModule) [IsAddCyclic A]
    {k : ℕ} [NeZero k] (hcard : Nat.card A = 2 ^ k) (hA : A.IsNondegenerate) :
    ∃ θ : ℤ, Odd θ ∧ Nonempty (Isometry (dyadicCyclic k θ) A) := by
  obtain ⟨θ, ⟨f⟩⟩ := exists_dyadicCyclic_isometry_of_card_eq_two_pow A hcard
  refine ⟨θ, ?_, ⟨f⟩⟩
  exact (isNondegenerate_dyadicCyclic_iff k θ).mp (f.isNondegenerate_iff.mpr hA)

private theorem nonempty_isometry_dyadicCyclic_iff_addCircle {k : ℕ} [NeZero k] (θ η : ℤ) :
    Nonempty (Isometry (dyadicCyclic k θ) (dyadicCyclic k η)) ↔
      ∃ u : (ZMod (2 ^ k))ˣ,
        (((θ : ℚ) / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) =
          (((η * (u.val.val : ℤ) ^ 2 : ℤ) : ℚ) / 2 ^ (k + 1) : ℚ) := by
  constructor
  · rintro ⟨f⟩
    let e : ZMod (2 ^ k) ≃+ ZMod (2 ^ k) := f.toAddEquiv
    let u : (ZMod (2 ^ k))ˣ := ((ZMod.AddAutEquivUnits (2 ^ k)) e).toMul
    have hu : (u : ZMod (2 ^ k)) = e 1 := by
      simp [u, ZMod.AddAutEquivUnits_apply]
    refine ⟨u, ?_⟩
    have h : (dyadicCyclic k η).quadratic (e 1) =
        (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) := f.map_app' _
    have hθ : (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) =
        (((θ : ℚ) / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) := by
      simpa using dyadicCyclic_quadratic_intCast k θ 1
    have huval : (u : ZMod (2 ^ k)) = ((u.val.val : ℤ) : ZMod (2 ^ k)) := by simp
    rw [← hu, huval, dyadicCyclic_quadratic_intCast, hθ] at h
    simpa [Int.cast_mul, Int.cast_pow] using h.symm
  · rintro ⟨u, hu⟩
    let e : ZMod (2 ^ k) ≃+ ZMod (2 ^ k) := AddAut.mulRight u
    have hgen : (dyadicCyclic k η).quadratic (e (1 : ZMod (2 ^ k))) =
        (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) := by
      rw [AddAut.mulRight_apply, one_mul]
      have huval : (u : ZMod (2 ^ k)) = ((u.val.val : ℤ) : ZMod (2 ^ k)) := by simp
      rw [huval]
      rw [dyadicCyclic_quadratic_intCast]
      have hθ : (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) =
          (((θ : ℚ) / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) := by
        simpa using dyadicCyclic_quadratic_intCast k θ 1
      rw [hθ]
      simpa [Int.cast_mul, Int.cast_pow] using hu.symm
    exact ⟨cyclicIsometryOfGenerator (2 ^ k) _ _ e hgen⟩

/-- The dyadic cyclic isometry criterion: `q_θ^{(2)}(2^k)` and
`q_η^{(2)}(2^k)` are isometric exactly when `θ` and `ηu²` agree modulo `2^{k+1}` for
some unit `u` modulo `2^k`.  The unit is represented by its canonical natural representative
`u.val.val`; changing that representative by a multiple of `2^k` leaves its square unchanged
modulo `2^{k+1}`. -/
@[simp]
theorem nonempty_isometry_dyadicCyclic_iff {k : ℕ} [NeZero k] (θ η : ℤ) :
    Nonempty (Isometry (dyadicCyclic k θ) (dyadicCyclic k η)) ↔
      ∃ u : (ZMod (2 ^ k))ˣ,
        (θ : ZMod (2 ^ (k + 1))) = (η * (u.val.val : ℤ) ^ 2 : ℤ) := by
  rw [nonempty_isometry_dyadicCyclic_iff_addCircle]
  apply exists_congr
  intro u
  rw [← (ZMod.toRatAddCircle_injective (2 ^ (k + 1))).eq_iff]
  simp only [ZMod.toRatAddCircle_intCast]
  norm_cast

end TauCeti.FiniteQuadraticModule
