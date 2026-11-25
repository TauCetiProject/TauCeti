/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.JonesWenzl
public import TauCeti.Algebra.TemperleyLieb.NormalForm

/-!
# The single-clasp recursion

The linear Jones–Wenzl recursion expands `f_(n+2)` as the included `f_(n+1)` multiplied by
the sum of `1` and weighted descending generator words `e_n … e_i`
(`TauCeti.TemperleyLieb.descBlock`). Thus every summand contains only one copy of the smaller
projection, in contrast to Wenzl's quadratic recursion. This is the form used to compute
coefficients by removing one cap at a time.

The coefficients are `(-1)^(n+1-i) [i+1] / [n+2]`, with zero-based generator indices.
Division means `Ring.inverse`. Only `[1], …, [n+1]` need to be units for the identity;
the last denominator is not cancelled in its proof. When it is a unit as well, the
resulting element has the usual Jones–Wenzl projection properties.

## References

* S. Morrison, *A formula for the Jones–Wenzl projections*, arXiv:1503.00384,
  Proposition 3.3. Morrison uses loop value `-[2]`, whereas our generators satisfy
  `e_i² = δ e_i` with `δ = [2]`. Replacing his quantum integer `[k]` by
  `(-1)^(k+1) [k]` gives the alternating signs in the formula here.
-/

public section

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] {δ : R}

private noncomputable def singleClaspSum (δ : R) (n : ℕ) : TemperleyLieb R δ (n + 2) :=
  ∑ i : Fin (n + 1), ((-1 : R) ^ (n + 1 - i.val) * qInt R δ (i.val + 1)) •
    descBlock δ (Fin.last n) i

private theorem singleClaspSum_zero : singleClaspSum δ 0 = -e δ 0 := by
  simp [singleClaspSum]

private theorem singleClaspSum_succ (n : ℕ) :
    singleClaspSum δ (n + 1) =
      -(qInt R δ (n + 2) • e δ (Fin.last (n + 1))) -
        e δ (Fin.last (n + 1)) * strandIncl (singleClaspSum δ n) := by
  rw [singleClaspSum, Fin.sum_univ_castSucc]
  have hblock (i : Fin (n + 1)) :
      descBlock (R := R) (n := n + 3) δ (Fin.last (n + 1)) i.castSucc =
        e δ (Fin.last (n + 1)) * strandIncl (descBlock δ (Fin.last n) i) := by
    rw [strandIncl_descBlock]
    exact (e_mul_descBlock_of_succ_eq δ
      (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i)) (by simp)).symm
  have hsign (i : Fin (n + 1)) :
      ((-1 : R) ^ (n + 1 + 1 - i.val) * qInt R δ (i.val + 1)) =
        -((-1 : R) ^ (n + 1 - i.val) * qInt R δ (i.val + 1)) := by
    have hi : n + 1 + 1 - i.val = (n + 1 - i.val) + 1 := by omega
    rw [hi, pow_succ]
    ring
  simp only [descBlock_self, hblock, Fin.val_castSucc, Fin.val_last, hsign, singleClaspSum,
    map_sum, map_smul, Finset.mul_sum, neg_smul, Finset.sum_neg_distrib, mul_smul_comm,
    Nat.add_sub_cancel_left, pow_one, neg_mul, one_mul]
  abel

private theorem jonesWenzl_add_two_eq_add_smul_aux :
    ∀ n, (∀ k ∈ Finset.Icc 1 (n + 1), IsUnit (qInt R δ k)) →
      jonesWenzl δ (n + 2) = strandIncl (jonesWenzl δ (n + 1)) +
        Ring.inverse (qInt R δ (n + 2)) •
          (strandIncl (jonesWenzl δ (n + 1)) * singleClaspSum δ n)
  | 0, _ => by simp [singleClaspSum_zero, jonesWenzl_two, sub_eq_add_neg]
  | n + 1, h => by
    have hprev : ∀ k ∈ Finset.Icc 1 (n + 1), IsUnit (qInt R δ k) :=
      fun k hk ↦ h k (Finset.Icc_subset_Icc le_rfl (by omega) hk)
    have hunit := h (n + 2) (by simp)
    let F := strandIncl (jonesWenzl δ (n + 2))
    let H := strandIncl (strandIncl (jonesWenzl δ (n + 1)))
    let E : TemperleyLieb R δ (n + 3) := e δ (Fin.last (n + 1))
    let S := strandIncl (singleClaspSum δ n)
    have hF : F = H + Ring.inverse (qInt R δ (n + 2)) • (H * S) := by
      simp only [F, H, S, jonesWenzl_add_two_eq_add_smul_aux n hprev,
        map_add, map_smul, map_mul]
    have hFH : F * H = F := by
      simpa only [F, H, ← map_mul] using
        congrArg strandIncl (jonesWenzl_mul_strandIncl_jonesWenzl hprev)
    have hEH : E * H = H * E :=
      (commute_e_last_strandIncl_strandIncl (jonesWenzl δ (n + 1))).eq
    have hFEH : F * E * H = F * E := by
      rw [mul_assoc, hEH, ← mul_assoc, hFH]
    have hFEF : F * E * F = F * E +
        Ring.inverse (qInt R δ (n + 2)) • (F * E * S) := by
      conv_lhs => rhs; rw [hF]
      rw [mul_add, mul_smul_comm, ← mul_assoc, hFEH]
    rw [jonesWenzl_add_two, singleClaspSum_succ]
    -- Absorption removes the second smaller projection before scalar cancellation.
    have hcancel : qInt R δ (n + 2) * Ring.inverse (qInt R δ (n + 2)) = 1 :=
      Ring.mul_inverse_cancel _ hunit
    have hcoeff : qInt R δ (n + 2) * (Ring.inverse (qInt R δ (n + 3)) *
        Ring.inverse (qInt R δ (n + 2))) = Ring.inverse (qInt R δ (n + 3)) := by
      calc
        _ = Ring.inverse (qInt R δ (n + 3)) *
            (qInt R δ (n + 2) * Ring.inverse (qInt R δ (n + 2))) := by ring
        _ = _ := by rw [hcancel, mul_one]
    dsimp only [F, E, S] at hFEF
    rw [hFEF]
    simp only [mul_sub, mul_neg, mul_smul_comm, mul_assoc, smul_sub, smul_neg, smul_add,
      smul_smul]
    rw [hcoeff]
    module

/-- **The single-clasp recursion:** the next Jones–Wenzl element is the included smaller
element multiplied by the sum of `1` and weighted once-capped descending words. Only the quantum
integers through `[n + 1]` need to be units; division by `[n + 2]` is `Ring.inverse`. -/
theorem jonesWenzl_add_two_eq_strandIncl_mul (n : ℕ)
    (h : ∀ k ∈ Finset.Icc 1 (n + 1), IsUnit (qInt R δ k)) :
    jonesWenzl δ (n + 2) = strandIncl (jonesWenzl δ (n + 1)) *
      (1 + ∑ i : Fin (n + 1),
        ((-1 : R) ^ (n + 1 - i.val) * qInt R δ (i.val + 1) *
          Ring.inverse (qInt R δ (n + 2))) • descBlock δ (Fin.last n) i) := by
  rw [jonesWenzl_add_two_eq_add_smul_aux n h]
  simp only [singleClaspSum, mul_add, mul_one, Finset.mul_sum, Finset.smul_sum,
    mul_smul_comm, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end TauCeti.TemperleyLieb
