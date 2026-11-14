/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Filtration
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.Algebra.Order.GroupWithZero.WithZeroInt

/-!
# The formal filtration of `E(F_u)` and the valuation of `x`

Let `C` be a Weierstrass curve over the ring of integers `O_u` of the completion `F_u` of the
fraction field of a Dedekind domain at a height-one prime `u`, elliptic over `F_u`. The formal
parametrisation `Ê(𝔪_u) → E(F_u)` (`WeierstrassCurve.formalPointHomAdicCompletion`) carries the
level `Ê(𝔪_u ^ k)` of the formal group, the parameters in `𝔪_u ^ k`, to the subgroup
`C.formalPointFiltration u k`, written `E_k(F_u)`, of the points over `F_u`; for `k = 1` it is
the kernel of reduction. This file describes `E_k(F_u)` by the valuation of the `x`-coordinate:
for `k ≥ 1`,

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

* `WeierstrassCurve.mem_formalPointFiltration_iff_valuation_xCoord`: the description of
  `E_k(F_u)` above.
* `WeierstrassCurve.map_nsmul_formalPointFiltration`: `n E_k(F_u) = E_(k+e)(F_u)`.
* `WeierstrassCurve.nsmul_formalPointFiltration_injective`: `E_k(F_u)` has no nonzero `n`-torsion.
* `WeierstrassCurve.eventually_formalPointFiltration_inf_eq_bot`: a finite subgroup of `E(F_u)`
  meets `E_k(F_u)` trivially for all large `k`.

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

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- The image in the local point group of formal parameters in `𝔪_u ^ k`. For `k ≥ 1` this
is the usual `E_k(F_u)`. Levels zero and one both equal the kernel of reduction. -/
noncomputable def formalPointFiltration (k : ℕ) : AddSubgroup (C.baseChange F_u).toAffine.Point :=
  (FormalGroupPoint.filtration C m_u k).map (C.formalPointHomAdicCompletion u)

open scoped Classical in
/-- A formal level is the image of the corresponding parameter subgroup. -/
theorem formalPointFiltration_def (k : ℕ) :
    C.formalPointFiltration u k =
      (FormalGroupPoint.filtration C m_u k).map (C.formalPointHomAdicCompletion u) := (rfl)

open scoped Classical in
/-- Membership in a formal level means having a formal parameter in that ideal power. -/
theorem mem_formalPointFiltration_iff (k : ℕ) (P : (C.baseChange F_u).toAffine.Point) :
    P ∈ C.formalPointFiltration u k ↔
      ∃ t : FormalGroupPoint C m_u, (t : O_u) ∈ m_u ^ k ∧
        C.formalPointHomAdicCompletion u t = P := by
  simp only [formalPointFiltration, AddSubgroup.mem_map, FormalGroupPoint.mem_filtration]

open scoped Classical in
/-- The formal parametrisation preserves and reflects the depth of a parameter. -/
@[simp]
theorem formalPoint_mem_formalPointFiltration_iff (k : ℕ) {t : O_u} (ht : t ∈ m_u) :
    C.formalPoint (K := F_u) (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) ht ∈
        C.formalPointFiltration u k ↔ t ∈ m_u ^ k := by
  rw [← C.formalPointHomAdicCompletion_apply u ⟨t, ht⟩, C.mem_formalPointFiltration_iff u]
  simp only [(C.formalPointHomAdicCompletion_injective u).eq_iff, exists_eq_right]

open scoped Classical in
/-- Formal levels decrease as their depth increases. -/
theorem formalPointFiltration_antitone : Antitone (C.formalPointFiltration u) :=
  fun _ _ hjk ↦ AddSubgroup.map_mono (FormalGroupPoint.filtration_antitone hjk)

open scoped Classical in
@[simp]
theorem formalPointFiltration_zero : C.formalPointFiltration u 0 = C.kerReduction u := by
  rw [formalPointFiltration, FormalGroupPoint.filtration_zero, AddSubgroup.map_top,
    range_formalPointHomAdicCompletion_eq_kerReduction]

open scoped Classical in
@[simp]
theorem formalPointFiltration_one : C.formalPointFiltration u 1 = C.kerReduction u := by
  rw [formalPointFiltration, FormalGroupPoint.filtration_one, AddSubgroup.map_top,
    range_formalPointHomAdicCompletion_eq_kerReduction]

open scoped Classical in
/-- Every formal level is contained in the kernel of reduction. -/
theorem formalPointFiltration_le_kerReduction (k : ℕ) :
    C.formalPointFiltration u k ≤ C.kerReduction u := by
  rw [← C.formalPointFiltration_zero u]
  exact C.formalPointFiltration_antitone u (Nat.zero_le k)

open scoped Classical in
/-- **The level `k` of the formal group in `E(F_u)`, by the valuation of `x`**: for `k ≥ 1`, a
point of `C` over `F_u` comes from a parameter in `𝔪_u ^ k` exactly when it is the point at
infinity or its `x`-coordinate has valuation at least `exp k ^ 2`, a pole of order at least
`2 k`. -/
theorem mem_formalPointFiltration_iff_valuation_xCoord {k : ℕ} (hk : k ≠ 0)
    {P : (C.baseChange F_u).toAffine.Point} :
    P ∈ C.formalPointFiltration u k ↔
      P = 0 ∨ exp (k : ℤ) ^ 2 ≤ Valued.v (Affine.Point.xCoord P) := by
  rw [formalPointFiltration]
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
theorem map_nsmul_formalPointFiltration {n e k : ℕ}
    (hn : Ideal.span {(n : O_u)} = m_u ^ e) (hek : e < k) :
    (C.formalPointFiltration u k).map (nsmulAddMonoidHom n) =
      C.formalPointFiltration u (k + e) := by
  simp only [formalPointFiltration]
  have hcomm : (nsmulAddMonoidHom n).comp (C.formalPointHomAdicCompletion u) =
      (C.formalPointHomAdicCompletion u).comp (nsmulAddMonoidHom n) :=
    AddMonoidHom.ext fun P ↦ by
      simp only [AddMonoidHom.comp_apply, nsmulAddMonoidHom_apply, map_nsmul]
  rw [AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map,
    FormalGroupPoint.map_nsmul_filtration hn hek]

open scoped Classical in
/-- **The levels of `E(F_u)` below `n` have no `n`-torsion**: if `n O_u = 𝔪_u ^ e` with `e < k`,
then multiplication by `n` is injective on `E_k(F_u)`. -/
theorem nsmul_formalPointFiltration_injective {n e k : ℕ}
    (hn : Ideal.span {(n : O_u)} = m_u ^ e) (hek : e < k) :
    Function.Injective (fun P : C.formalPointFiltration u k ↦ n • P) := by
  rw [formalPointFiltration]
  exact ((AddSubgroup.equivMapOfInjective _ _
    (C.formalPointHomAdicCompletion_injective u)).injective_nsmul_iff n).mp
      (FormalGroupPoint.nsmul_filtration_injective hn hek)

open scoped Classical in
/-- **A finite subgroup meets the deep levels trivially**: if `H` is a finite subgroup of
`E(F_u)`, then `E_k(F_u) ∩ H = 0` for all large `k`, since a nonzero point of `H` leaves
`E_k(F_u)` once `exp k ^ 2` exceeds the valuation of its `x`-coordinate. -/
theorem eventually_formalPointFiltration_inf_eq_bot
    (H : AddSubgroup (C.baseChange F_u).toAffine.Point) [Finite H] :
    ∀ᶠ k : ℕ in Filter.atTop, C.formalPointFiltration u k ⊓ H = ⊥ := by
  have h (P : H) : ∀ᶠ k : ℕ in Filter.atTop, P.1 ∈ C.formalPointFiltration u k → P.1 = 0 := by
    filter_upwards [TauCeti.eventually_lt_exp_pow (Valued.v (Affine.Point.xCoord P.1))
      two_ne_zero, Filter.eventually_ne_atTop 0] with k hk hk0 hP
    exact ((C.mem_formalPointFiltration_iff_valuation_xCoord u hk0).mp hP).resolve_right hk.not_ge
  filter_upwards [Filter.eventually_all.mpr h] with k hk
  exact eq_bot_iff.mpr fun P ⟨hPk, hPH⟩ ↦ (AddSubgroup.mem_bot).mpr (hk ⟨P, hPH⟩ hPk)

end WeierstrassCurve
