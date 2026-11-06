/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Pi
import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Relations
import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.GaussSum
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Classification of sums of dyadic planes at one exponent

An orthogonal sum of `a` copies of `u(2^k)` and `b` copies of `v(2^k)` has a normal form
with at most one `v` summand, obtained from `u ⊥ u ≅ v ⊥ v`. For positive `k`, two such
sums are isometric exactly when their numbers of planes and their parities of `v` summands
agree. This classifies sums of the two even dyadic generators at a fixed exponent; it does
not classify forms containing cyclic generators or summands at different exponents.

The parity is detected by the Gauss sum scaled by `2^(k-1)`. Ordinary Gauss sums alone
would lose this information when `k` is even.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(b), and (k) for passage from lattices to finite quadratic forms.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298, for the quadratic Gauss-sum invariants.
-/

public section

namespace TauCeti.FiniteQuadraticModule

open QuadraticMap.IsometryEquiv

private noncomputable abbrev planeSum (k a b : ℕ) : FiniteQuadraticModule :=
  (pi fun _ : Fin a ↦ dyadicU k).prod (pi fun _ : Fin b ↦ dyadicV k)

private noncomputable def replaceTwoV (k a b : ℕ) :
    Isometry (planeSum k a (b + 2)) (planeSum k (a + 2) b) := by
  let su : Isometry (pi fun _ : Fin (a + 2) ↦ dyadicU k)
      (((dyadicU k).prod (dyadicU k)).prod (pi fun _ : Fin a ↦ dyadicU k)) :=
    (consPi _).symm.trans
      (((QuadraticMap.IsometryEquiv.refl _).prod (consPi _).symm).trans (prodAssoc _ _ _).symm)
  let sv : Isometry (pi fun _ : Fin (b + 2) ↦ dyadicV k)
      (((dyadicV k).prod (dyadicV k)).prod (pi fun _ : Fin b ↦ dyadicV k)) :=
    (consPi _).symm.trans
      (((QuadraticMap.IsometryEquiv.refl _).prod (consPi _).symm).trans (prodAssoc _ _ _).symm)
  exact ((QuadraticMap.IsometryEquiv.refl _).prod sv).trans
    ((prodLeftComm _ _ _).trans
      (((dyadicUProdSelfIsometryDyadicVProdSelf k).symm.prod
        (QuadraticMap.IsometryEquiv.refl _)).trans
          ((prodAssoc _ _ _).symm.trans (su.symm.prod (QuadraticMap.IsometryEquiv.refl _)))))

/-- Every fixed-exponent sum of dyadic planes is isometric to a sum with at most one
`v` summand. Each removed pair of `v` summands becomes a pair of `u` summands. This also
holds at exponent zero, where all the summands are trivial. -/
theorem nonempty_isometry_pi_dyadicU_prod_pi_dyadicV_normal_form (k a b : ℕ) :
    Nonempty (Isometry
      ((pi fun _ : Fin a ↦ dyadicU k).prod (pi fun _ : Fin b ↦ dyadicV k))
      ((pi fun _ : Fin (a + b - b % 2) ↦ dyadicU k).prod
        (pi fun _ : Fin (b % 2) ↦ dyadicV k))) := by
  induction b using Nat.twoStepInduction generalizing a with
  | zero =>
    simpa using (⟨.refl _⟩ : Nonempty (Isometry (planeSum k a 0) (planeSum k a 0)))
  | one =>
    simpa using (⟨.refl _⟩ : Nonempty (Isometry (planeSum k a 1) (planeSum k a 1)))
  | more b ih _ =>
    obtain ⟨e⟩ := ih (a + 2)
    refine ⟨(replaceTwoV k a b).trans (e.trans (Isometry.ofEq ?_))⟩
    have ha : a + 2 + b - b % 2 = a + (b + 2) - (b + 2) % 2 := by omega
    have hb : b % 2 = (b + 2) % 2 := by omega
    rw [ha, hb]

private theorem natCard_planeSum (k a b : ℕ) :
    Nat.card (planeSum k a b) = 2 ^ (2 * k * (a + b)) := by
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, natCard_dyadicU, natCard_dyadicV]
  simp only [Nat.card_fin, ← pow_two, ← pow_mul, ← pow_add]
  congr 1
  ring

private theorem scaledGaussSum_planeSum (j a b : ℕ) :
    (planeSum (j + 1) a b).scaledGaussSum (2 ^ j) =
      (-1 : ℂ) ^ b * ((2 : ℂ) ^ (2 * j + 1)) ^ (a + b) := by
  have hu : (dyadicU (j + 1)).scaledGaussSum (2 ^ j) = (2 : ℂ) ^ (2 * j + 1) := by
    rw [scaledGaussSum_dyadicU_pow_add]
    simp [pow_succ]
  have hv : (dyadicV (j + 1)).scaledGaussSum (2 ^ j) = -((2 : ℂ) ^ (2 * j + 1)) := by
    rw [scaledGaussSum_dyadicV_pow_add]
    simp [pow_succ]
  simp only [planeSum, scaledGaussSum_prod, scaledGaussSum_pi, hu, hv, Fin.prod_const]
  rw [neg_pow, pow_add]
  ring

/-- Two fixed-exponent orthogonal sums of `u` and `v` are isometric exactly when they
have the same number of planes and the same parity of `v` summands. The positive exponent
hypothesis is essential: all generators at exponent zero are trivial. -/
theorem nonempty_isometry_pi_dyadicU_prod_pi_dyadicV_iff (k : ℕ) [NeZero k]
    (a b c d : ℕ) :
    Nonempty (Isometry
      ((pi fun _ : Fin a ↦ dyadicU k).prod (pi fun _ : Fin b ↦ dyadicV k))
      ((pi fun _ : Fin c ↦ dyadicU k).prod (pi fun _ : Fin d ↦ dyadicV k))) ↔
      a + b = c + d ∧ b % 2 = d % 2 := by
  constructor
  · rintro ⟨e⟩
    have hc := Nat.card_congr e.toLinearEquiv.toEquiv
    rw [natCard_planeSum, natCard_planeSum] at hc
    have he := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
    have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    have hn : a + b = c + d := by nlinarith
    refine ⟨hn, ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
    have hG := e.scaledGaussSum_eq (2 ^ j)
    rw [scaledGaussSum_planeSum, scaledGaussSum_planeSum, hn] at hG
    have hp := mul_right_cancel₀
      (pow_ne_zero (c + d) (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))) hG
    have hp' : (-1 : ℂ) ^ (b % 2) = (-1 : ℂ) ^ (d % 2) :=
      (neg_one_pow_eq_pow_mod_two b).symm.trans (hp.trans (neg_one_pow_eq_pow_mod_two d))
    have hb := Nat.mod_lt b (by decide : 0 < 2)
    have hd := Nat.mod_lt d (by decide : 0 < 2)
    interval_cases hbm : b % 2 <;> interval_cases hdm : d % 2 <;> norm_num at hp' <;> rfl
  · rintro ⟨hn, hp⟩
    obtain ⟨e⟩ := nonempty_isometry_pi_dyadicU_prod_pi_dyadicV_normal_form k a b
    obtain ⟨f⟩ := nonempty_isometry_pi_dyadicU_prod_pi_dyadicV_normal_form k c d
    exact ⟨e.trans ((Isometry.ofEq (by rw [hn, hp])).trans f.symm)⟩

end TauCeti.FiniteQuadraticModule
