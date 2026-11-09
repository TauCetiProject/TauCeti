/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Filtration
import TauCeti.Algebra.Group.Equiv.Pow

/-!
# The formal filtration of `E(F_u)` and the valuation of `x`

Let `C` be a Weierstrass curve over the ring of integers `O_u` of the completion `F_u` of the
fraction field of a Dedekind domain at a height-one prime `u`, elliptic over `F_u`. The formal
parametrisation `Ê(𝔪_u) → E(F_u)` (`WeierstrassCurve.formalPointHomAdicCompletion`) carries the
level `Ê(𝔪_u ^ k)` of the formal group, the parameters in `𝔪_u ^ k`, to a subgroup `E_k(F_u)` of
the points over `F_u`; for `k = 1` it is the kernel of reduction. This file describes `E_k(F_u)`
by the valuation of the `x`-coordinate: for `k ≥ 1`,

`P ∈ E_k(F_u) ↔ P = 0 ∨ exp k ^ 2 ≤ v(x(P))`.

Indeed a nonzero parameter `t` has `v(x) · v(t) ^ 2 = 1`
(`WeierstrassCurve.valuation_xCoord_formalPoint_mul_sq`), and `t ∈ 𝔪_u ^ k` exactly when
`v(t) ≤ exp (-k)`. This makes the levels accessible to maps that are only known through their
effect on `x`, such as an isogeny near the point at infinity
(`TauCeti.Isogeny.exists_valuation_xCoord_pointMap_mul_sq`).

The formal-group statements on multiplication by `n` carry over to these levels: if
`n O_u = 𝔪_u ^ e` with `e < k`, then `n E_k(F_u) = E_(k+e)(F_u)` and `E_k(F_u)` has no nonzero
`n`-torsion (`WeierstrassCurve.FormalGroupPoint.map_nsmul_filtration` and
`WeierstrassCurve.FormalGroupPoint.nsmul_filtration_injective`).

## Main results

* `WeierstrassCurve.mem_map_filtration_formalPointHomAdicCompletion_iff`: the description of
  `E_k(F_u)` above.
* `WeierstrassCurve.map_nsmulAddMonoidHom_map_filtration`: `n E_k(F_u) = E_(k+e)(F_u)`.
* `WeierstrassCurve.injective_nsmul_map_filtration`: `E_k(F_u)` has no nonzero `n`-torsion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.3 and VII.2.
-/

public section

open IsDedekindDomain WithZero

namespace WeierstrassCurve

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => IsLocalRing.maximalIdeal O_u

-- Named: anonymous `local instance`s here get the same generated names as the ones in
-- `FormalGroup/Point/Torsion/Basic.lean`, and the names used in
-- `FormalGroup/Point/Torsion/Free.lean` are already taken in this module's imports.
local instance isLinearTopology_adicCompletionIntegers_depth :
    IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

local instance fact_isAdic_maximalIdeal_depth : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **The level `k` of the formal group in `E(F_u)`, by the valuation of `x`**: for `k ≥ 1`, a
point of `C` over `F_u` comes from a parameter in `𝔪_u ^ k` exactly when it is the point at
infinity or its `x`-coordinate has valuation at least `exp k ^ 2`, a pole of order at least
`2 k`. -/
theorem mem_map_filtration_formalPointHomAdicCompletion_iff {k : ℕ} (hk : k ≠ 0)
    {P : (C.baseChange F_u).toAffine.Point} :
    P ∈ (FormalGroupPoint.filtration C m_u k).map (C.formalPointHomAdicCompletion u) ↔
      P = 0 ∨ exp (k : ℤ) ^ 2 ≤ Valued.v (Affine.Point.xCoord P) := by
  have hexp : exp (k : ℤ) ^ 2 * exp (-(k : ℤ)) ^ 2 = 1 := by
    rw [← mul_pow, ← exp_add, add_neg_cancel, exp_zero, one_pow]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rw [formalPointHomAdicCompletion_apply]
    rcases eq_or_ne Q.val 0 with h | h
    · exact Or.inl (C.formalPoint_of_param_eq_zero _ Q.property h)
    · right
      have hx := C.valuation_xCoord_formalPoint_mul_sq u Q.property h
      have ht : Valued.v (Q.val : F_u) ≤ exp (-(k : ℤ)) :=
        (u.mem_maximalIdeal_pow_iff (K := F)).mp (FormalGroupPoint.mem_filtration.mp hQ)
      -- `exp k ^ 2 = exp k ^ 2 · v(x) · v(t) ^ 2 ≤ exp k ^ 2 · v(x) · exp (-k) ^ 2 = v(x)`
      calc exp (k : ℤ) ^ 2 = exp (k : ℤ) ^ 2 * (Valued.v (C.formalPoint (K := F_u)
            (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) Q.property).xCoord *
              Valued.v (Q.val : F_u) ^ 2) := by rw [hx, mul_one]
        _ ≤ exp (k : ℤ) ^ 2 * (Valued.v (C.formalPoint (K := F_u)
            (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) Q.property).xCoord *
              exp (-(k : ℤ)) ^ 2) := by gcongr; exact zero_le
        _ = _ := by rw [mul_left_comm, hexp, mul_one]
  · rintro (rfl | hP)
    · exact zero_mem _
    have hk1 : 1 < exp (k : ℤ) ^ 2 :=
      one_lt_pow₀ (one_lt_exp_iff.mpr (by omega)) two_ne_zero
    obtain ⟨t, ht, rfl⟩ := C.exists_formalPoint_eq_of_one_lt_valuation_xCoord u (hk1.trans_le hP)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [C.formalPoint_of_param_eq_zero _ ht rfl, Affine.Point.xCoord_zero, map_zero] at hP
      exact (hk1.trans_le hP).not_ge zero_le
    have hx := C.valuation_xCoord_formalPoint_mul_sq u ht ht0
    -- `v(t) ^ 2 = v(x)⁻¹ ≤ exp (-k) ^ 2`
    have hsq : Valued.v (t : F_u) ^ 2 ≤ exp (-(k : ℤ)) ^ 2 := by
      calc Valued.v (t : F_u) ^ 2 = exp (k : ℤ) ^ 2 * exp (-(k : ℤ)) ^ 2 *
            Valued.v (t : F_u) ^ 2 := by rw [hexp, one_mul]
        _ ≤ Valued.v (C.formalPoint (K := F_u)
            (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) ht).xCoord *
              exp (-(k : ℤ)) ^ 2 * Valued.v (t : F_u) ^ 2 := by gcongr
        _ = _ := by rw [mul_right_comm, hx, one_mul]
    refine ⟨⟨t, ht⟩, ?_, by rw [formalPointHomAdicCompletion_apply]⟩
    exact FormalGroupPoint.mem_filtration.mpr ((u.mem_maximalIdeal_pow_iff (K := F)).mpr
      ((pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp hsq))

open scoped Classical in
/-- **Multiplication by `n` on the levels of `E(F_u)`**: if `n O_u = 𝔪_u ^ e` with `e < k`, then
`n E_k(F_u) = E_(k+e)(F_u)`, the image of `n Ê(𝔪_u ^ k) = Ê(𝔪_u ^ (k + e))`. -/
theorem map_nsmulAddMonoidHom_map_filtration {n e k : ℕ}
    (hn : Ideal.span {(n : O_u)} = m_u ^ e) (hek : e < k) :
    ((FormalGroupPoint.filtration C m_u k).map (C.formalPointHomAdicCompletion u)).map
        (nsmulAddMonoidHom n) =
      (FormalGroupPoint.filtration C m_u (k + e)).map (C.formalPointHomAdicCompletion u) := by
  have hcomm : (nsmulAddMonoidHom n).comp (C.formalPointHomAdicCompletion u) =
      (C.formalPointHomAdicCompletion u).comp (nsmulAddMonoidHom n) :=
    AddMonoidHom.ext fun P ↦ by
      simp only [AddMonoidHom.comp_apply, nsmulAddMonoidHom_apply, map_nsmul]
  rw [AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map,
    FormalGroupPoint.map_nsmul_filtration hn hek]

open scoped Classical in
/-- **The levels of `E(F_u)` below `n` have no `n`-torsion**: if `n O_u = 𝔪_u ^ e` with `e < k`,
then multiplication by `n` is injective on `E_k(F_u)`. -/
theorem injective_nsmul_map_filtration {n e k : ℕ}
    (hn : Ideal.span {(n : O_u)} = m_u ^ e) (hek : e < k) :
    Function.Injective (fun P : (FormalGroupPoint.filtration C m_u k).map
      (C.formalPointHomAdicCompletion u) ↦ n • P) :=
  ((AddSubgroup.equivMapOfInjective _ _
    (C.formalPointHomAdicCompletion_injective u)).injective_nsmul_iff n).mp
      (FormalGroupPoint.nsmul_filtration_injective hn hek)

end WeierstrassCurve
