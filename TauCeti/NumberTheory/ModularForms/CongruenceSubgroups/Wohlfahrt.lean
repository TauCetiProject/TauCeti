/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.StrictLevel
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.Modular.ConjugateTranslation
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Wohlfahrt's theorem in its strict form

A subgroup `Γ ≤ SL(2, ℤ)` is a congruence subgroup when it contains some principal congruence
subgroup `Γ(N)`, `N ≠ 0`. Wohlfahrt's theorem says that the modulus can then be read off the
cusps: a congruence subgroup contains `Γ(N)` for `N` its *strict level*, the least `N > 0` with
every conjugate `σ Tᴺ σ⁻¹` in `Γ` (`Subgroup.strictLevel`), which is the least common multiple of
its strict cusp widths. No sign is allowed, so the statement applies to subgroups that do not
contain `-1`. Together with the definition of a congruence subgroup this gives the criterion
`IsCongruenceSubgroup Γ ↔ Γ(N_s(Γ)) ≤ Γ` for every finite-index `Γ`, and shows that the levels
`N` with `Γ(N) ≤ Γ` are exactly the multiples of the strict level.

The input is a lemma about principal congruence subgroups alone: for `ν ≠ 0`, any subgroup
containing `Γ(ν)` and every conjugate of `Tᴹ` contains `Γ(M)`; for `M ∣ ν` this says
`Γ(M) = Γ(ν) ⊔ ⟨⟨Tᴹ⟩⟩`. Its proof is an elementary matrix reduction, as in Kiming, Schütt
and Verrill. Let `γ = [a, b; c, d] ∈ Γ(M)`.

* A translation `T^(-M i)` on the left replaces `a` by `a - M i c`. As `a` is prime to `M c`,
  some such entry is prime to `ν`, and we may assume `a` is a unit modulo `ν`, with inverse `u`.
* Multiplying by `T^(-u b)` on the right and by `[1, 0; -u c, 1] = S T^(u c) S⁻¹` on the left, both
  conjugates of powers of `Tᴹ` since `M` divides `b` and `c`, gives a matrix congruent to
  `diag(a, u)` modulo `ν`.
* The conjugate of `T^(1 - a)` by `[1, 0; 1, 1]` is `[a, 1 - a; a - 1, 2 - a]`. It is again a
  conjugate of a power of `Tᴹ`, with the same upper-left entry `a`, so the same reduction takes
  it to a matrix congruent to `diag(a, u)` as well. The two reduced matrices differ by an element
  of `Γ(ν)`.

## Main results

* `CongruenceSubgroup.Gamma_le_of_forall_conj_T_pow_mem`: for `ν ≠ 0`, a subgroup containing
  `Γ(ν)` and every conjugate of `Tᴹ` contains `Γ(M)`.
* `CongruenceSubgroup.Gamma_eq_sup_normalClosure`: for `M ∣ ν`, `ν ≠ 0`,
  `Γ(M) = Γ(ν) ⊔ ⟨⟨Tᴹ⟩⟩`.
* `CongruenceSubgroup.IsCongruenceSubgroup.Gamma_strictLevel_le`: a congruence subgroup contains
  `Γ(N)` for `N` its strict level.
* `CongruenceSubgroup.IsCongruenceSubgroup.Gamma_le_iff_strictLevel_dvd`: a congruence subgroup
  contains `Γ(N)` exactly when its strict level divides `N`.
* `CongruenceSubgroup.isCongruenceSubgroup_iff_Gamma_strictLevel_le`: **Wohlfahrt's theorem**,
  strict form: a finite-index `Γ` is a congruence subgroup if and only if it contains `Γ(N)` for
  `N` its strict level.

## References

* K. Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535,
  Theorem 2.
* I. Kiming, M. Schütt and H. A. Verrill, *Lifts of projective congruence groups*,
  J. London Math. Soc. 83 (2011), 96–120, §3, Proposition 3 and Remark 8.
-/

public section

open Matrix Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

namespace CongruenceSubgroup

/-- Multiplying `δ = [a, b; c, d]` on the left by `S T^(u c) S⁻¹ = [1, 0; -u c, 1]` and on the
right by `T^(-u b)`, where `u a ≡ 1` modulo `ν`, gives a matrix congruent to `diag(a, u)`
modulo `ν`. -/
private theorem map_S_mul_T_zpow_mul_S_inv_mul_mul_T_zpow {ν : ℕ} {u : ℤ} (δ : SL(2, ℤ))
    (hu : (u : ZMod ν) * (δ 0 0 : ZMod ν) = 1) :
    ((map (Int.castRingHom (ZMod ν)) (S * T ^ (u * δ 1 0) * S⁻¹ * δ * T ^ (-(u * δ 0 1))) :
      SL(2, ZMod ν)) : Matrix (Fin 2) (Fin 2) (ZMod ν)) =
      !![(δ 0 0 : ZMod ν), 0; 0, (u : ZMod ν)] := by
  have hdet : ((δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 : ℤ) : ZMod ν) = 1 := by
    rw [← det_fin_two, δ.det_coe, Int.cast_one]
  push_cast at hdet
  rw [map_apply_coe, coe_mul, coe_mul, TauCeti.ModularGroup.coe_S_mul_T_zpow_mul_S_inv,
    coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linear_combination -(δ 0 1 : ZMod ν) * hu
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linear_combination -(δ 1 0 : ZMod ν) * hu
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linear_combination ((u : ZMod ν) * δ 0 1 * δ 1 0 - δ 1 1) * hu + (u : ZMod ν) * hdet

/-- A matrix congruent to `1` modulo `M` whose upper-left entry is a unit modulo `ν` lies in every
subgroup containing `Γ(ν)` and every conjugate of every power `Tʲ` with `M ∣ j`. -/
private theorem mem_of_isCoprime {H : Subgroup SL(2, ℤ)} {M ν : ℕ}
    (hT : ∀ (σ : SL(2, ℤ)) (j : ℤ), (M : ℤ) ∣ j → σ * T ^ j * σ⁻¹ ∈ H) (hH : Gamma ν ≤ H)
    {γ : SL(2, ℤ)} (ha : (M : ℤ) ∣ γ 0 0 - 1) (hb : (M : ℤ) ∣ γ 0 1) (hc : (M : ℤ) ∣ γ 1 0)
    (hν : IsCoprime (γ 0 0) ν) : γ ∈ H := by
  obtain ⟨u, v, huv⟩ := hν
  have hu : (u : ZMod ν) * (γ 0 0 : ZMod ν) = 1 := by
    simpa using congrArg (Int.cast : ℤ → ZMod ν) huv
  -- the reduction of a matrix with upper-right and lower-left entries divisible by `M`
  have hred : ∀ δ : SL(2, ℤ), (M : ℤ) ∣ δ 0 1 → (M : ℤ) ∣ δ 1 0 →
      (S * T ^ (u * δ 1 0) * S⁻¹ * δ * T ^ (-(u * δ 0 1)) ∈ H ↔ δ ∈ H) := fun δ hb hc ↦ by
    rw [H.mul_mem_cancel_right (by simpa using hT 1 _ (dvd_neg.2 (hb.mul_left u))),
      H.mul_mem_cancel_left (hT S _ (hc.mul_left u))]
  -- the conjugate `X` of `T ^ (1 - a)` by `[1, 0; 1, 1]` has upper-left entry `a`
  set X := S * T ^ (-1 : ℤ) * S⁻¹ * T ^ (1 - γ 0 0) * (S * T ^ (-1 : ℤ) * S⁻¹)⁻¹ with hXdef
  have hX : (X : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0, 1 - γ 0 0; γ 0 0 - 1, 2 - γ 0 0] := by
    rw [hXdef, coe_conj_T_zpow]
    simp only [TauCeti.ModularGroup.coe_S_mul_T_zpow_mul_S_inv, neg_neg]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp
    · simp
    · simp
      ring
  have hX00 : X 0 0 = γ 0 0 := by simp [hX]
  have hXH : X ∈ H := hT _ _ (by simpa [neg_sub] using ha.neg_right)
  rw [← hred X (by simpa [hX, neg_sub] using ha.neg_right) (by simpa [hX] using ha)] at hXH
  rw [← hred γ hb hc]
  refine (H.mul_mem_cancel_right (H.inv_mem hXH)).1 (hH (Gamma_mem'.2 ?_))
  rw [map_mul, map_inv, mul_inv_eq_one]
  ext1
  rw [map_S_mul_T_zpow_mul_S_inv_mul_mul_T_zpow γ hu,
    map_S_mul_T_zpow_mul_S_inv_mul_mul_T_zpow X (hX00 ▸ hu), hX00]

/-- **Wohlfahrt's lemma.** For `ν ≠ 0`, a subgroup of `SL(2, ℤ)` containing `Γ(ν)` and every
conjugate `σ Tᴹ σ⁻¹` contains `Γ(M)`. The hypothesis `ν ≠ 0` cannot be dropped: `Γ(0)` is
trivial, and the normal closure of `Tᴹ` does not contain `Γ(M)` for `M ≥ 6`. -/
theorem Gamma_le_of_forall_conj_T_pow_mem {H : Subgroup SL(2, ℤ)} {M ν : ℕ} (hν : ν ≠ 0)
    (hT : ∀ σ : SL(2, ℤ), σ * T ^ M * σ⁻¹ ∈ H) (hH : Gamma ν ≤ H) :
    Gamma M ≤ H := by
  have hT' : ∀ (σ : SL(2, ℤ)) (j : ℤ), (M : ℤ) ∣ j → σ * T ^ j * σ⁻¹ ∈ H := by
    rintro σ _ ⟨k, rfl⟩
    rw [_root_.zpow_mul, zpow_natCast, ← conj_zpow]
    exact zpow_mem (hT σ) k
  intro γ hγ
  obtain ⟨h00, h01, h10, -⟩ := Gamma_mem.1 hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h01 h10
  have ha : (M : ℤ) ∣ γ 0 0 - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by push_cast; rw [h00, sub_self])
  -- `a` is prime to `M` and, by the determinant, to `c`
  have hac : IsCoprime (γ 0 0) ((M : ℤ) * γ 1 0) := by
    obtain ⟨k, hk⟩ := ha
    have hdet := γ.det_coe
    rw [det_fin_two] at hdet
    exact IsCoprime.mul_right ⟨1, -k, by linear_combination hk⟩
      ⟨γ 1 1, -γ 0 1, by linear_combination hdet⟩
  -- after a translation by a multiple of `M`, the upper-left entry is a unit modulo `ν`
  obtain ⟨i, hi⟩ := hac.exists_isCoprime_sub_mul (Int.natCast_ne_zero.2 hν)
  have hTi : T ^ (-(M * i)) ∈ H := by simpa using hT' 1 _ (dvd_neg.2 (dvd_mul_right _ i))
  have hγ' : (↑(T ^ (-(M * i)) * γ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0 - i * (M * γ 1 0), γ 0 1 - M * i * γ 1 1; γ 1 0, γ 1 1] := by
    rw [coe_mul, coe_T_zpow]
    ext j k
    fin_cases j <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine (H.mul_mem_cancel_left hTi).1 (mem_of_isCoprime hT' hH ?_ ?_ ?_ ?_)
  · rw [hγ']
    simpa [sub_right_comm] using ha.sub ((dvd_mul_right (M : ℤ) (γ 1 0)).mul_left i)
  · rw [hγ']
    simpa using h01.sub (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  · rw [hγ']
    simpa using h10
  · rw [hγ']
    simpa using hi

/-- **Wohlfahrt's lemma**, as an equality: for `M ∣ ν` with `ν ≠ 0`, `Γ(M)` is generated by
`Γ(ν)` and the conjugates of `Tᴹ`. -/
theorem Gamma_eq_sup_normalClosure {M ν : ℕ} (hν : ν ≠ 0) (hMν : M ∣ ν) :
    Gamma M = Gamma ν ⊔ Subgroup.normalClosure {T ^ M} := by
  have := Gamma_normal M
  refine le_antisymm (Gamma_le_of_forall_conj_T_pow_mem hν (fun σ ↦ ?_) le_sup_left)
    (sup_le (Gamma_le_Gamma_of_dvd hMν) (Subgroup.normalClosure_le_normal ?_))
  · exact Subgroup.mem_sup_right (Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure rfl) σ)
  · simpa [← zpow_natCast] using ModularGroup_T_pow_mem_Gamma M M dvd_rfl

namespace IsCongruenceSubgroup

variable {Γ : Subgroup SL(2, ℤ)}

/-- **Wohlfahrt's theorem**, strict form: a congruence subgroup `Γ` contains `Γ(N)` for `N` its
strict level. -/
theorem Gamma_strictLevel_le (hΓ : IsCongruenceSubgroup Γ) : Gamma Γ.strictLevel ≤ Γ := by
  obtain ⟨ν, hν, hle⟩ := hΓ
  exact Gamma_le_of_forall_conj_T_pow_mem hν Γ.conj_T_pow_strictLevel_mem hle

/-- A congruence subgroup contains `Γ(N)` exactly when its strict level divides `N`: the strict
level is the least level of a principal congruence subgroup it contains. -/
theorem Gamma_le_iff_strictLevel_dvd (hΓ : IsCongruenceSubgroup Γ) {N : ℕ} :
    Gamma N ≤ Γ ↔ Γ.strictLevel ∣ N :=
  ⟨strictLevel_dvd_of_Gamma_le, fun h ↦ (Gamma_le_Gamma_of_dvd h).trans hΓ.Gamma_strictLevel_le⟩

end IsCongruenceSubgroup

/-- **Wohlfahrt's theorem**, strict form: a finite-index subgroup `Γ` of `SL(2, ℤ)` is a
congruence subgroup if and only if it contains `Γ(N)` for `N` its strict level. -/
theorem isCongruenceSubgroup_iff_Gamma_strictLevel_le {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] :
    IsCongruenceSubgroup Γ ↔ Gamma Γ.strictLevel ≤ Γ :=
  ⟨IsCongruenceSubgroup.Gamma_strictLevel_le, fun h ↦ ⟨_, Γ.strictLevel_pos.ne', h⟩⟩

end CongruenceSubgroup
