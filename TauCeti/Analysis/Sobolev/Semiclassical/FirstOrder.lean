/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.CommutatorInduction
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.CoordinateDeriv.LpNorm

/-!
# First-order operators with semiclassically bounded coefficients

On `ℝⁿ`, a first-order operator written in the semiclassical partial derivatives `h ∂ₗ` is

`P u = ∑ₗ aₗ (h ∂ₗ u) + b u`

(`TauCeti.semiclassicalFirstOrderOperator h a b`), with coefficient fields
`aₗ, b : ℝⁿ → L(F, G)`. Its coefficients are *semiclassically bounded* when
`hⁱ ‖Dⁱ aₗ‖ ≤ K` and `hⁱ ‖Dⁱ b‖ ≤ K` for the orders `i` in question: they may vary on the scale
`h`, like the coefficients of a linearized field equation written in the rescaled variables of a
concentrating solution. This file proves the two properties of such operators that the
semiclassical commutator induction (`TauCeti.Analysis.Sobolev.Semiclassical.CommutatorInduction`)
takes as hypotheses, with constants independent of `h`:

* **boundedness**: `P` lowers the order of the semiclassical Sobolev norms by one,
  `‖P u‖_{k,h} ≤ (n + 1) (k + 1) 2ᵏ K ‖u‖_{k+1,h}` when the coefficients are bounded through
  order `k` (`TauCeti.semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_le`);
* **the commutators lose one order**: the commutator of `P` with `h ∂ⱼ` is again a first-order
  operator, with coefficients `h ∂ⱼ aₗ` and `h ∂ⱼ b`,

  `h ∂ⱼ (P u) = P (h ∂ⱼ u) + P' u`, `P' = ∑ₗ (h ∂ⱼ aₗ) h ∂ₗ + h ∂ⱼ b`

  (`TauCeti.const_smul_coordinateDeriv_semiclassicalFirstOrderOperator`), by the Leibniz rule and
  the symmetry of second derivatives. Since `hⁱ ‖Dⁱ (h ∂ⱼ aₗ)‖ ≤ h^(i+1) ‖D^(i+1) aₗ‖`, the
  coefficients of `P'` are bounded through order `k` when those of `P` are bounded through order
  `k + 1`, and boundedness of `P'` gives
  `‖P (h ∂ⱼ u) - h ∂ⱼ (P u)‖_{k,h} ≤ (n + 1) (k + 1) 2ᵏ K ‖u‖_{k+1,h}`
  (`TauCeti.semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_sub_le`).

Together with the commutator induction, an a priori estimate for `P` at the lowest level of the
scale therefore lifts to every level, uniformly in `h`: if
`‖u‖_{1,h} ≤ C₀ (‖P u‖_{0,h} + ‖u‖_{0,h})` on smooth fields with all derivatives in `L²`, then
`‖u‖_{k+1,h} ≤ C_k (‖P u‖_{k,h} + ‖u‖_{0,h})` at every level, with constants `C_k` determined by
`C₀`, the dimension and the coefficient bounds
(`TauCeti.semiclassicalSobolevNorm_succ_le_mul_add_semiclassicalFirstOrderOperator`; without the
lower-order term, `TauCeti.semiclassicalSobolevNorm_succ_le_mul_semiclassicalFirstOrderOperator`).

The linearized operators of Taubes's large-parameter Seiberg–Witten equations, written in a flat
chart in the rescaled variables, are first-order operators of this form. Compressing such an
operator by projections `Π` that vary on the scale `h` keeps the form:
`Π P Π = ∑ₗ (Π aₗ Π) h ∂ₗ + (Π b Π + ∑ₗ Π aₗ (h ∂ₗ Π))`, so the derivatives of the projections
enter only the zeroth-order coefficient.

## Main definitions

* `TauCeti.semiclassicalFirstOrderOperator h a b`: the operator `u ↦ ∑ₗ aₗ (h ∂ₗ u) + b u`.

## Main results

* `TauCeti.const_smul_coordinateDeriv_semiclassicalFirstOrderOperator`: the commutator with
  `h ∂ⱼ` is the first-order operator with coefficients `h ∂ⱼ aₗ`, `h ∂ⱼ b`.
* `TauCeti.semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_le`: boundedness from order
  `k + 1` to order `k`, uniformly in `h`.
* `TauCeti.semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_sub_le`: the commutator bound.
* `TauCeti.semiclassicalSobolevNorm_succ_le_mul_add_semiclassicalFirstOrderOperator`: the
  commutator induction for first-order operators.

## References

* M. Zworski, *Semiclassical Analysis*, Graduate Studies in Mathematics 138, American
  Mathematical Society, 2012 (semiclassical Sobolev spaces).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory
open scoped ContDiff

variable {n : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The **first-order operator** `P u = ∑ₗ aₗ (h ∂ₗ u) + b u` on `ℝⁿ`, written in the
semiclassical partial derivatives `h ∂ₗ`, with coefficient fields `aₗ, b : ℝⁿ → L(F, G)`. -/
def semiclassicalFirstOrderOperator (h : ℝ) (a : Fin n → CoordinateSpace n → F →L[ℝ] G)
    (b : CoordinateSpace n → F →L[ℝ] G) (u : CoordinateSpace n → F) : CoordinateSpace n → G :=
  fun x ↦ ∑ l, a l x (h • coordinateDeriv [l] u x) + b x (u x)

@[simp]
theorem semiclassicalFirstOrderOperator_apply (h : ℝ) (a : Fin n → CoordinateSpace n → F →L[ℝ] G)
    (b : CoordinateSpace n → F →L[ℝ] G) (u : CoordinateSpace n → F) (x : CoordinateSpace n) :
    semiclassicalFirstOrderOperator h a b u x =
      ∑ l, a l x (h • coordinateDeriv [l] u x) + b x (u x) :=
  (rfl)

variable {a : Fin n → CoordinateSpace n → F →L[ℝ] G} {b : CoordinateSpace n → F →L[ℝ] G}
  {u : CoordinateSpace n → F}

/-- The operator as a sum of functions: the terms `aₗ (h ∂ₗ u)` and `b u`. -/
private theorem semiclassicalFirstOrderOperator_eq (h : ℝ) :
    semiclassicalFirstOrderOperator h a b u =
      (∑ l, fun x ↦ a l x ((h • coordinateDeriv [l] u) x)) + fun x ↦ b x (u x) := by
  funext x
  simp

/-- A first-order operator with `Cᵐ` coefficients maps `C^(m+1)` functions to `Cᵐ` functions. -/
theorem contDiff_semiclassicalFirstOrderOperator {m : WithTop ℕ∞}
    (ha : ∀ l, ContDiff ℝ m (a l)) (hb : ContDiff ℝ m b) (hu : ContDiff ℝ (m + 1) u) (h : ℝ) :
    ContDiff ℝ m (semiclassicalFirstOrderOperator h a b u) :=
  (ContDiff.sum fun l _ ↦ (ha l).clm_apply
    ((hu.coordinateDeriv_of_le [l] (by simp)).const_smul h)).add
    (hb.clm_apply (hu.of_le le_self_add))

/-! ### The commutator with a semiclassical partial derivative -/

/-- **The commutator of a first-order operator with `h ∂ⱼ`.** For `C¹` coefficients and a `C²`
function `u`, `h ∂ⱼ (P u) = P (h ∂ⱼ u) + P' u`, where `P'` is the first-order operator with
coefficients `h ∂ⱼ aₗ` and `h ∂ⱼ b`. -/
theorem const_smul_coordinateDeriv_semiclassicalFirstOrderOperator (ha : ∀ l, ContDiff ℝ 1 (a l))
    (hb : ContDiff ℝ 1 b) (hu : ContDiff ℝ 2 u) (h : ℝ) (j : Fin n) :
    h • coordinateDeriv [j] (semiclassicalFirstOrderOperator h a b u) =
      semiclassicalFirstOrderOperator h a b (h • coordinateDeriv [j] u) +
        semiclassicalFirstOrderOperator h (fun l ↦ h • coordinateDeriv [j] (a l))
          (h • coordinateDeriv [j] b) u := by
  have hu₁ : ContDiff ℝ 1 u := hu.of_le one_le_two
  have hdu (l : Fin n) : ContDiff ℝ 1 (h • coordinateDeriv [l] u) :=
    (hu.coordinateDeriv_of_le [l] (by norm_num)).const_smul h
  have hterm (l : Fin n) : ContDiff ℝ 1 fun x ↦ a l x ((h • coordinateDeriv [l] u) x) :=
    (ha l).clm_apply (hdu l)
  -- `∂ⱼ (h ∂ₗ u) = h ∂ₗ (∂ⱼ u)`, by the symmetry of second derivatives.
  have hswap (l : Fin n) (x : CoordinateSpace n) :
      coordinateDeriv [j] (h • coordinateDeriv [l] u) x =
        h • coordinateDeriv [l] (coordinateDeriv [j] u) x := by
    rw [coordinateDeriv_const_smul, Pi.smul_apply, ← coordinateDeriv_append,
      ← coordinateDeriv_append]
    exact congrArg (h • ·) (coordinateDeriv_pair_comm hu j l x)
  have hsum : ContDiff ℝ 1 (∑ l, fun x ↦ a l x ((h • coordinateDeriv [l] u) x)) := by
    rw [Finset.sum_fn]
    exact ContDiff.sum fun l _ ↦ hterm l
  funext x
  rw [semiclassicalFirstOrderOperator_eq, coordinateDeriv_add [j] hsum (hb.clm_apply hu₁),
    coordinateDeriv_sum [j] fun l _ ↦ hterm l]
  have hl (l : Fin n) : coordinateDeriv [j] (fun y ↦ a l y (h • coordinateDeriv [l] u y)) x =
      coordinateDeriv [j] (a l) x (h • coordinateDeriv [l] u x) +
        h • a l x (coordinateDeriv [l] (coordinateDeriv [j] u) x) := by
    rw [← map_smul, ← hswap]
    exact coordinateDeriv_singleton_clm_apply
      ((ha l).differentiable one_ne_zero x) ((hdu l).differentiable one_ne_zero x) j
  rw [Pi.smul_apply, Pi.add_apply, Pi.add_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, hl, coordinateDeriv_singleton_clm_apply
    (hb.differentiable one_ne_zero x) (hu₁.differentiable one_ne_zero x)]
  simp only [semiclassicalFirstOrderOperator_apply, coordinateDeriv_const_smul, Pi.smul_apply,
    smul_apply, map_smul, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  abel

/-! ### Boundedness on the semiclassical scale -/

/-- A semiclassical partial derivative `h ∂ₗ u` of a `C^(k+1)` function whose derivatives of orders
`1, …, k + 1` are square integrable has square-integrable derivatives through order `k`. -/
private theorem memLp_iteratedFDeriv_const_smul_coordinateDeriv {k : ℕ}
    (hu : ContDiff ℝ (k + 1) u) (hum : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ (i + 1) u) 2) (h : ℝ)
    (l : Fin n) : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (h • coordinateDeriv [l] u)) 2 := by
  intro i hi
  have hui : ContDiff ℝ (i + 1) u := hu.of_le (by exact_mod_cast Nat.succ_le_succ hi)
  have hD : iteratedFDeriv ℝ i (h • coordinateDeriv [l] u) =
      h • iteratedFDeriv ℝ i (coordinateDeriv [l] u) :=
    funext fun _ ↦ iteratedFDeriv_const_smul_apply
      (hui.coordinateDeriv_of_le [l] (by simp)).contDiffAt
  rw [hD]
  exact (memLp_iteratedFDeriv_coordinateDeriv hui (hum i hi) l).const_smul h

/-- **First-order operators lower the semiclassical order by one.** Let `h > 0` and let the
coefficients be of class `Cᵏ` with `hⁱ ‖Dⁱ aₗ‖ ≤ K` and `hⁱ ‖Dⁱ b‖ ≤ K` everywhere for `i ≤ k`. For
`u` of class `C^(k+1)` with square-integrable derivatives through order `k + 1`, the derivatives of
`P u` through order `k` are square integrable and

`‖P u‖_{k,h} ≤ (n + 1) (k + 1) 2ᵏ K ‖u‖_{k+1,h}`.

The constant does not depend on `h`. -/
theorem semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_le {k : ℕ} {h K : ℝ} (hh : 0 < h)
    (ha : ∀ l, ContDiff ℝ k (a l)) (hb : ContDiff ℝ k b)
    (haK : ∀ l, ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i (a l) x‖ ≤ K)
    (hbK : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i b x‖ ≤ K)
    (hu : ContDiff ℝ (k + 1) u) (hum : ∀ i ≤ k + 1, MemLp (iteratedFDeriv ℝ i u) 2) :
    (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (semiclassicalFirstOrderOperator h a b u)) 2) ∧
      semiclassicalSobolevNorm k h (semiclassicalFirstOrderOperator h a b u) ≤
        (n + 1) * ((k + 1) * 2 ^ k * K) * semiclassicalSobolevNorm (k + 1) h u := by
  have hum' : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ (i + 1) u) 2 := fun i hi ↦ hum (i + 1) (by omega)
  have huk : ContDiff ℝ k u := hu.of_le (by exact_mod_cast k.le_succ)
  have hdu (l : Fin n) : ContDiff ℝ k (h • coordinateDeriv [l] u) :=
    (hu.coordinateDeriv_of_le [l] (by simp)).const_smul h
  -- The terms `aₗ (h ∂ₗ u)` and `b u`, each through the multiplier estimate.
  have hA (l : Fin n) := semiclassicalSobolevNorm_clm_apply_le_of_le_left (ha l) (hdu l)
    (memLp_iteratedFDeriv_const_smul_coordinateDeriv hu hum' h l) hh (haK l)
  have hB := semiclassicalSobolevNorm_clm_apply_le_of_le_left hb huk
    (fun i hi ↦ hum i (by omega)) hh hbK
  have hAc : ContDiff ℝ k (∑ l, fun x ↦ a l x ((h • coordinateDeriv [l] u) x)) := by
    rw [Finset.sum_fn]
    exact ContDiff.sum fun l _ ↦ (ha l).clm_apply (hdu l)
  have hAm (i : ℕ) (hi : i ≤ k) :
      MemLp (iteratedFDeriv ℝ i (∑ l, fun x ↦ a l x ((h • coordinateDeriv [l] u) x))) 2 := by
    rw [Finset.sum_fn, iteratedFDeriv_sum fun l _ ↦
      ((ha l).clm_apply (hdu l)).of_le (by exact_mod_cast hi)]
    exact memLp_finsetSum' _ fun l _ ↦ (hA l).1 i hi
  rw [semiclassicalFirstOrderOperator_eq]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [iteratedFDeriv_add (hAc.of_le (by exact_mod_cast hi))
      ((hb.clm_apply huk).of_le (by exact_mod_cast hi))]
    exact (hAm i hi).add (hB.1 i hi)
  have hc : 0 ≤ (k + 1 : ℝ) * 2 ^ k * K := by
    have := nonneg_of_forall_pow_mul_norm_iteratedFDeriv_le hbK 0
    positivity
  calc semiclassicalSobolevNorm k h ((∑ l, fun x ↦ a l x ((h • coordinateDeriv [l] u) x)) +
        fun x ↦ b x (u x))
      ≤ semiclassicalSobolevNorm k h (∑ l, fun x ↦ a l x ((h • coordinateDeriv [l] u) x)) +
          semiclassicalSobolevNorm k h (fun x ↦ b x (u x)) :=
        semiclassicalSobolevNorm_add_le hAc (hb.clm_apply huk) hAm hh.le
    _ ≤ ∑ _l : Fin n, (k + 1) * 2 ^ k * K * semiclassicalSobolevNorm (k + 1) h u +
          (k + 1) * 2 ^ k * K * semiclassicalSobolevNorm (k + 1) h u := by
        refine add_le_add ?_ (hB.2.trans (mul_le_mul_of_nonneg_left
          (semiclassicalSobolevNorm_le_semiclassicalSobolevNorm_of_le k.le_succ hh.le u) hc))
        rw [Finset.sum_fn]
        exact (semiclassicalSobolevNorm_sum_le _ (fun l _ ↦ (ha l).clm_apply (hdu l))
          (fun l _ ↦ (hA l).1) hh.le).trans (Finset.sum_le_sum fun l _ ↦ (hA l).2.trans
            (mul_le_mul_of_nonneg_left
              (semiclassicalSobolevNorm_const_smul_coordinateDeriv_le hu hum' hh.le l) hc))
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The coefficient `h ∂ⱼ c` of the commutator has semiclassical bounds through order `k` when `c`
has them through order `k + 1`: `hⁱ ‖Dⁱ (h ∂ⱼ c)‖ ≤ h^(i+1) ‖D^(i+1) c‖`. -/
private theorem pow_mul_norm_iteratedFDeriv_const_smul_coordinateDeriv_le {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {c : CoordinateSpace n → H} {k : ℕ} {h K : ℝ}
    (hh : 0 ≤ h) (hc : ContDiff ℝ (k + 1) c)
    (hK : ∀ i ≤ k + 1, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i c x‖ ≤ K) (j : Fin n) :
    ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i (h • coordinateDeriv [j] c) x‖ ≤ K := by
  intro i hi x
  have hci : ContDiff ℝ (i + 1) c := hc.of_le (by exact_mod_cast Nat.succ_le_succ hi)
  rw [iteratedFDeriv_const_smul_apply (hci.coordinateDeriv_of_le [j] (by simp)).contDiffAt,
    norm_smul, Real.norm_of_nonneg hh, ← mul_assoc, ← pow_succ]
  exact (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_coordinateDeriv_le hci j x)
    (pow_nonneg hh _)).trans (hK (i + 1) (by omega) x)

/-- **The commutators of a first-order operator with `h ∂ⱼ` lose one order.** Let `h > 0` and let
the coefficients be of class `C^(k+1)` with `hⁱ ‖Dⁱ aₗ‖ ≤ K` and `hⁱ ‖Dⁱ b‖ ≤ K` everywhere for
`i ≤ k + 1`. For `u` of class `C^(k+2)` with square-integrable derivatives through order `k + 1`,

`‖P (h ∂ⱼ u) - h ∂ⱼ (P u)‖_{k,h} ≤ (n + 1) (k + 1) 2ᵏ K ‖u‖_{k+1,h}`.

This is the commutator hypothesis of the semiclassical commutator induction
`TauCeti.semiclassicalSobolevNorm_succ_le_mul_add_of_commutator_le`, with a constant independent
of `h`. -/
theorem semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_sub_le {k : ℕ} {h K : ℝ}
    (hh : 0 < h) (ha : ∀ l, ContDiff ℝ (k + 1) (a l)) (hb : ContDiff ℝ (k + 1) b)
    (haK : ∀ l, ∀ i ≤ k + 1, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i (a l) x‖ ≤ K)
    (hbK : ∀ i ≤ k + 1, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i b x‖ ≤ K)
    (hu : ContDiff ℝ (k + 2) u) (hum : ∀ i ≤ k + 1, MemLp (iteratedFDeriv ℝ i u) 2) (j : Fin n) :
    semiclassicalSobolevNorm k h
        (semiclassicalFirstOrderOperator h a b (h • coordinateDeriv [j] u) -
          h • coordinateDeriv [j] (semiclassicalFirstOrderOperator h a b u)) ≤
      (n + 1) * ((k + 1) * 2 ^ k * K) * semiclassicalSobolevNorm (k + 1) h u := by
  rw [const_smul_coordinateDeriv_semiclassicalFirstOrderOperator
      (fun l ↦ (ha l).of_le (by exact_mod_cast Nat.le_add_left 1 k))
      (hb.of_le (by exact_mod_cast Nat.le_add_left 1 k))
      (hu.of_le (by exact_mod_cast Nat.le_add_left 2 k)),
    sub_add_cancel_left, semiclassicalSobolevNorm_neg]
  exact (semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_le hh
    (fun l ↦ ((ha l).coordinateDeriv_of_le [j] (by simp)).const_smul h)
    ((hb.coordinateDeriv_of_le [j] (by simp)).const_smul h)
    (fun l ↦ pow_mul_norm_iteratedFDeriv_const_smul_coordinateDeriv_le hh.le (ha l) (haK l) j)
    (pow_mul_norm_iteratedFDeriv_const_smul_coordinateDeriv_le hh.le hb hbK j)
    (hu.of_le (by exact_mod_cast (k + 1).le_succ)) hum).2

/-! ### The commutator induction for first-order operators -/

section Induction

variable {h : ℝ} {K B C : ℕ → ℝ}

/-- The hypotheses of the commutator induction for a first-order operator with smooth
coefficients obeying `hⁱ ‖Dⁱ aₗ‖, hⁱ ‖Dⁱ b‖ ≤ K i`: the commutator constants `B k` are nonnegative,
the operator preserves smooth fields with all derivatives in `L²`, and its commutators with the
`h ∂ⱼ` lose one order. -/
private theorem semiclassicalFirstOrderOperator_commutator_hypotheses (hh : 0 < h)
    (ha : ∀ l, ContDiff ℝ ∞ (a l)) (hb : ContDiff ℝ ∞ b)
    (haK : ∀ l i x, h ^ i * ‖iteratedFDeriv ℝ i (a l) x‖ ≤ K i)
    (hbK : ∀ i x, h ^ i * ‖iteratedFDeriv ℝ i b x‖ ≤ K i)
    (hB : ∀ k, (n + 1) * ((k + 1) * 2 ^ k * ∑ i ∈ Finset.range (k + 2), K i) ≤ B k) :
    (∀ k, 0 ≤ B k) ∧
      (∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u → (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
        ContDiff ℝ ∞ (semiclassicalFirstOrderOperator h a b u) ∧
          ∀ i, MemLp (iteratedFDeriv ℝ i (semiclassicalFirstOrderOperator h a b u)) 2) ∧
      ∀ k (j : Fin n) (u : CoordinateSpace n → F), ContDiff ℝ ∞ u →
        (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
        semiclassicalSobolevNorm k h
          (semiclassicalFirstOrderOperator h a b (h • coordinateDeriv [j] u) -
            h • coordinateDeriv [j] (semiclassicalFirstOrderOperator h a b u)) ≤
          B k * semiclassicalSobolevNorm (k + 1) h u := by
  have hK (m : ℕ) : 0 ≤ K m :=
    (by positivity : (0 : ℝ) ≤ h ^ m * ‖iteratedFDeriv ℝ m b 0‖).trans (hbK m 0)
  -- A single bound through order `k + 1`: the partial sum of the `K i`.
  have hle (k i : ℕ) (hi : i ≤ k + 1) : K i ≤ ∑ m ∈ Finset.range (k + 2), K m :=
    Finset.single_le_sum (fun m _ ↦ hK m) (Finset.mem_range.2 (by omega))
  refine ⟨fun k ↦ le_trans ?_ (hB k), fun u hu hum ↦ ⟨?_, fun i ↦ ?_⟩, fun k j u hu hum ↦ ?_⟩
  · exact mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ ↦ hK m))
  · exact contDiff_semiclassicalFirstOrderOperator ha hb (hu.of_le (by simp)) h
  · exact (semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_le hh
      (fun l ↦ (ha l).of_le (by exact_mod_cast le_top)) (hb.of_le (by exact_mod_cast le_top))
      (fun l m hm x ↦ (haK l m x).trans (hle i m (by omega)))
      (fun m hm x ↦ (hbK m x).trans (hle i m (by omega)))
      (hu.of_le (by exact_mod_cast le_top)) (fun m _ ↦ hum m)).1 i le_rfl
  · exact (semiclassicalSobolevNorm_semiclassicalFirstOrderOperator_sub_le hh
      (fun l ↦ (ha l).of_le (by exact_mod_cast le_top)) (hb.of_le (by exact_mod_cast le_top))
      (fun l m hm x ↦ (haK l m x).trans (hle k m hm)) (fun m hm x ↦ (hbK m x).trans (hle k m hm))
      (hu.of_le (WithTop.coe_le_coe.2 le_top)) (fun m _ ↦ hum m) j).trans
      (mul_le_mul_of_nonneg_right (hB k) (semiclassicalSobolevNorm_nonneg _ hh.le u))

/-- **The commutator induction for first-order operators.** Let `h > 0` and let `P` be a
first-order operator `P u = ∑ₗ aₗ (h ∂ₗ u) + b u` with smooth coefficients obeying the
semiclassical bounds `hⁱ ‖Dⁱ aₗ‖ ≤ K i` and `hⁱ ‖Dⁱ b‖ ≤ K i` for every `i`. Suppose that on smooth
fields with all derivatives in `L²` it satisfies `‖u‖_{1,h} ≤ C₀ (‖P u‖_{0,h} + ‖u‖_{0,h})`. If
`B k ≥ (n + 1) (k + 1) 2ᵏ ∑_{i ≤ k + 1} K i` and `C_(k+1) ≥ 1 + n C_k (1 + B_k C_k + C₀)`, then at
every level

`‖u‖_{k+1,h} ≤ C_k (‖P u‖_{k,h} + ‖u‖_{0,h})`.

The constants depend on `C₀`, the `K i` and `n` alone, so the estimates are uniform in `h` when the
hypotheses are. -/
theorem semiclassicalSobolevNorm_succ_le_mul_add_semiclassicalFirstOrderOperator (hh : 0 < h)
    (ha : ∀ l, ContDiff ℝ ∞ (a l)) (hb : ContDiff ℝ ∞ b)
    (haK : ∀ l i x, h ^ i * ‖iteratedFDeriv ℝ i (a l) x‖ ≤ K i)
    (hbK : ∀ i x, h ^ i * ‖iteratedFDeriv ℝ i b x‖ ≤ K i)
    (hB : ∀ k, (n + 1) * ((k + 1) * 2 ^ k * ∑ i ∈ Finset.range (k + 2), K i) ≤ B k)
    (hC₀ : 0 ≤ C 0) (hC : ∀ k, 1 + n * C k * (1 + B k * C k + C 0) ≤ C (k + 1))
    (hbase : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u → (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      semiclassicalSobolevNorm 1 h u ≤ C 0 * (semiclassicalSobolevNorm 0 h
        (semiclassicalFirstOrderOperator h a b u) + semiclassicalSobolevNorm 0 h u))
    (k : ℕ) (hu : ContDiff ℝ ∞ u) (hum : ∀ i, MemLp (iteratedFDeriv ℝ i u) 2) :
    semiclassicalSobolevNorm (k + 1) h u ≤
      C k * (semiclassicalSobolevNorm k h (semiclassicalFirstOrderOperator h a b u) +
        semiclassicalSobolevNorm 0 h u) := by
  obtain ⟨hB₀, hL, hcomm⟩ :=
    semiclassicalFirstOrderOperator_commutator_hypotheses hh ha hb haK hbK hB
  exact semiclassicalSobolevNorm_succ_le_mul_add_of_commutator_le hh.le hB₀ hC₀ hC hL hbase hcomm
    k hu hum

/-- **The commutator induction for an injective first-order operator.** If in
`semiclassicalSobolevNorm_succ_le_mul_add_semiclassicalFirstOrderOperator` the estimate at level
zero has no lower-order term, `‖u‖_{1,h} ≤ C₀ ‖P u‖_{0,h}`, then at every level
`‖u‖_{k+1,h} ≤ C_k (1 + C₀) ‖P u‖_{k,h}`. -/
theorem semiclassicalSobolevNorm_succ_le_mul_semiclassicalFirstOrderOperator (hh : 0 < h)
    (ha : ∀ l, ContDiff ℝ ∞ (a l)) (hb : ContDiff ℝ ∞ b)
    (haK : ∀ l i x, h ^ i * ‖iteratedFDeriv ℝ i (a l) x‖ ≤ K i)
    (hbK : ∀ i x, h ^ i * ‖iteratedFDeriv ℝ i b x‖ ≤ K i)
    (hB : ∀ k, (n + 1) * ((k + 1) * 2 ^ k * ∑ i ∈ Finset.range (k + 2), K i) ≤ B k)
    (hC₀ : 0 ≤ C 0) (hC : ∀ k, 1 + n * C k * (1 + B k * C k + C 0) ≤ C (k + 1))
    (hbase : ∀ u : CoordinateSpace n → F, ContDiff ℝ ∞ u → (∀ i, MemLp (iteratedFDeriv ℝ i u) 2) →
      semiclassicalSobolevNorm 1 h u ≤
        C 0 * semiclassicalSobolevNorm 0 h (semiclassicalFirstOrderOperator h a b u))
    (k : ℕ) (hu : ContDiff ℝ ∞ u) (hum : ∀ i, MemLp (iteratedFDeriv ℝ i u) 2) :
    semiclassicalSobolevNorm (k + 1) h u ≤
      C k * (1 + C 0) * semiclassicalSobolevNorm k h (semiclassicalFirstOrderOperator h a b u) := by
  obtain ⟨hB₀, hL, hcomm⟩ :=
    semiclassicalFirstOrderOperator_commutator_hypotheses hh ha hb haK hbK hB
  exact semiclassicalSobolevNorm_succ_le_mul_of_commutator_le hh.le hB₀ hC₀ hC hL hbase hcomm k hu
    hum

end Induction

end TauCeti
