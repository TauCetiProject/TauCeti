/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Basic
public import TauCeti.Data.SignType.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Polynomial

/-! # The Cauchy jump as the jump of a rational function

`Polynomial.cauchyJump p q a` is defined algebraically, from root multiplicities and the
one-sided sign `Polynomial.derivSignRight`. Over an ordered field with its order topology, this
file identifies it with the jump of the function `x ↦ q(x) / p(x)` at `a`.

Away from a pole, that is when `p.rootMultiplicity a ≤ q.rootMultiplicity a`, the function has a
finite limit at `a`. At a pole, and for nonzero `q`, it tends to `+∞` or `-∞` on each side, as
given by the one-sided signs of `p * q`. Hence the jump is `1` exactly when `q / p` tends to `-∞`
from the left of `a` and to `+∞` from the right, and `-1` exactly when it tends to `+∞` from the
left and to `-∞` from the right. This is the sign convention under which the index of `p' / p`
counts distinct roots.

## Main results

* `Polynomial.exists_tendsto_div_nhdsNE_of_rootMultiplicity_le`: away from a pole, `q / p` has a
  finite limit at `a`.
* `Polynomial.tendsto_div_nhdsGT_atTop`, `Polynomial.tendsto_div_nhdsGT_atBot`,
  `Polynomial.tendsto_div_nhdsLT_atTop`, `Polynomial.tendsto_div_nhdsLT_atBot`: at a pole, the
  one-sided limits of `q / p` are infinite with the one-sided signs of `p * q`.
* `Polynomial.cauchyJump_eq_one_iff_tendsto`, `Polynomial.cauchyJump_eq_neg_one_iff_tendsto`: the
  jump is `1` for a jump of `q / p` from `-∞` to `+∞`, and `-1` for a jump from `+∞` to `-∞`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.2.2 (the Cauchy index).
-/

public section

open Filter Set SignType Topology

namespace Polynomial

section Algebra

variable {R : Type*} [Field R] {p q : R[X]} {a : R}

/-- The quotient of the cofactors of `q` and `p` at `a`: writing `p = (X - a) ^ m * p₀` and
`q = (X - a) ^ n * q₀` with `p₀(a) ≠ 0` and `q₀(a) ≠ 0` (for nonzero `p` and `q`), this is
`x ↦ q₀(x) / p₀(x)`. -/
private noncomputable def cofactorDiv (p q : R[X]) (a x : R) : R :=
  (q /ₘ (X - C a) ^ q.rootMultiplicity a).eval x / (p /ₘ (X - C a) ^ p.rootMultiplicity a).eval x

/-- The quotient `q / p` is `(x - a) ^ n / (x - a) ^ m` times the quotient of the cofactors. -/
private theorem eval_div_eval_eq (p q : R[X]) (a x : R) :
    q.eval x / p.eval x =
      (x - a) ^ q.rootMultiplicity a / (x - a) ^ p.rootMultiplicity a * cofactorDiv p q a x := by
  conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq p a,
    ← pow_mul_divByMonic_rootMultiplicity_eq q a]
  simp only [cofactorDiv, eval_mul, eval_pow, eval_sub, eval_X, eval_C, mul_div_mul_comm]

/-- Away from a pole, `q / p` is `(x - a) ^ (n - m)` times the quotient of the cofactors. -/
private theorem eval_div_eval_eq_pow_mul (h : p.rootMultiplicity a ≤ q.rootMultiplicity a)
    {x : R} (hx : x ≠ a) :
    q.eval x / p.eval x =
      (x - a) ^ (q.rootMultiplicity a - p.rootMultiplicity a) * cofactorDiv p q a x := by
  rw [eval_div_eval_eq p q a, pow_sub₀ _ (sub_ne_zero.2 hx) h, div_eq_mul_inv]

/-- To the right of a pole, `q / p` is the reciprocal of `(x - a) ^ (m - n)` times the quotient
of the cofactors. -/
private theorem eval_div_eval_eq_inv_mul (hpole : q.rootMultiplicity a < p.rootMultiplicity a)
    {x : R} (hx : x ≠ a) :
    q.eval x / p.eval x =
      ((x - a) ^ (p.rootMultiplicity a - q.rootMultiplicity a))⁻¹ * cofactorDiv p q a x := by
  rw [eval_div_eval_eq p q a, pow_sub₀ _ (sub_ne_zero.2 hx) hpole.le, ← div_eq_mul_inv, inv_div]

/-- To the left of a pole, `q / p` is the reciprocal of `(a - x) ^ (m - n)` times `(-1) ^ (m - n)`
times the quotient of the cofactors. -/
private theorem eval_div_eval_eq_inv_mul' (hpole : q.rootMultiplicity a < p.rootMultiplicity a)
    {x : R} (hx : x ≠ a) :
    q.eval x / p.eval x = ((a - x) ^ (p.rootMultiplicity a - q.rootMultiplicity a))⁻¹ *
      ((-1) ^ (p.rootMultiplicity a - q.rootMultiplicity a) * cofactorDiv p q a x) := by
  rw [eval_div_eval_eq_inv_mul hpole hx, ← neg_sub a x, neg_pow, mul_inv, ← inv_pow, inv_neg_one]
  ring

end Algebra

section Order

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {p q : R[X]} {a : R}

/-- The sign of the quotient of the cofactors at `a` is the right-hand sign of `p * q`. -/
private theorem sign_cofactorDiv (p q : R[X]) (a : R) :
    sign (cofactorDiv p q a a) = (p * q).derivSignRight a := by
  rw [cofactorDiv, TauCeti.sign_div, derivSignRight_mul, derivSignRight_eq_sign_eval_divByMonic,
    derivSignRight_eq_sign_eval_divByMonic, mul_comm]

/-- At a pole, the left-hand sign of `p * q` is `(-1) ^ (m - n)` times its right-hand sign. -/
private theorem derivSignLeft_mul_eq (hpole : q.rootMultiplicity a < p.rootMultiplicity a)
    (hq : q ≠ 0) :
    (p * q).derivSignLeft a =
      (-1) ^ (p.rootMultiplicity a - q.rootMultiplicity a) * (p * q).derivSignRight a := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hpole
  rw [derivSignLeft_def, rootMultiplicity_mul (mul_ne_zero hp hq)]
  congr 1
  -- The exponents `m + n` and `m - n` differ by `2 n`.
  rw [← Nat.sub_add_cancel hpole.le, add_assoc, ← two_mul, pow_add, pow_mul]
  simp

end Order

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [TopologicalSpace R]
  [OrderTopology R] {p q : R[X]} {a : R}

/-- The quotient of the cofactors tends to its value at `a`. -/
private theorem tendsto_cofactorDiv (hp : p ≠ 0) (q : R[X]) (a : R) :
    Tendsto (cofactorDiv p q a) (𝓝 a) (𝓝 (cofactorDiv p q a a)) :=
  ((q /ₘ _).continuousAt.div (p /ₘ _).continuousAt
    (eval_divByMonic_pow_rootMultiplicity_ne_zero a hp)).tendsto

/-- **No pole, finite limit.** If `p.rootMultiplicity a ≤ q.rootMultiplicity a`, then `q / p`
has a finite limit at `a`, approached from both sides. -/
theorem exists_tendsto_div_nhdsNE_of_rootMultiplicity_le
    (h : p.rootMultiplicity a ≤ q.rootMultiplicity a) :
    ∃ c, Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[≠] a) (𝓝 c) := by
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  have hc : Continuous fun x : R ↦ (x - a) ^ (q.rootMultiplicity a - p.rootMultiplicity a) := by
    fun_prop
  refine ⟨_, Tendsto.congr' ?_ ((hc.tendsto a).mono_left nhdsWithin_le_nhds |>.mul
      ((tendsto_cofactorDiv hp q a).mono_left nhdsWithin_le_nhds))⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (eval_div_eval_eq_pow_mul h hx).symm

/-- The reciprocal of `(x - a) ^ k`, for `k ≠ 0`, tends to `+∞` from the right of `a`. -/
private theorem tendsto_inv_pow_sub_nhdsGT {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun x ↦ ((x - a) ^ k)⁻¹) (𝓝[>] a) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · exact (Continuous.tendsto' (f := fun x : R ↦ (x - a) ^ k) (by fun_prop) a 0
      (by simp [zero_pow hk])).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.2 hx) k

/-- The reciprocal of `(a - x) ^ k`, for `k ≠ 0`, tends to `+∞` from the left of `a`. -/
private theorem tendsto_inv_pow_sub_nhdsLT {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun x ↦ ((a - x) ^ k)⁻¹) (𝓝[<] a) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · exact (Continuous.tendsto' (f := fun x : R ↦ (a - x) ^ k) (by fun_prop) a 0
      (by simp [zero_pow hk])).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_pos (sub_pos.2 hx) k

/-- A product of a function tending to `+∞` and a function tending to a nonzero constant `c`
tends to the infinity of the sign of `c`. -/
private theorem tendsto_of_eventuallyEq_mul {l : Filter R} {f h g : R → R} {c : R}
    (hh : Tendsto h l atTop) (hg : Tendsto g l (𝓝 c)) (hf : (fun x ↦ h x * g x) =ᶠ[l] f) :
    (sign c = 1 → Tendsto f l atTop) ∧ (sign c = -1 → Tendsto f l atBot) :=
  ⟨fun hc ↦ (hh.atTop_mul_pos (sign_eq_one_iff.1 hc) hg).congr' hf,
    fun hc ↦ (hh.atTop_mul_neg (sign_eq_neg_one_iff.1 hc) hg).congr' hf⟩

/-- To the right of a pole, `q / p` tends to the infinity of the right-hand sign of `p * q`. -/
private theorem tendsto_div_nhdsGT (hpole : q.rootMultiplicity a < p.rootMultiplicity a) :
    ((p * q).derivSignRight a = 1 → Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[>] a) atTop) ∧
      ((p * q).derivSignRight a = -1 →
        Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[>] a) atBot) := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hpole
  rw [← sign_cofactorDiv]
  refine tendsto_of_eventuallyEq_mul (tendsto_inv_pow_sub_nhdsGT (Nat.sub_ne_zero_of_lt hpole))
    ((tendsto_cofactorDiv hp q a).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (eval_div_eval_eq_inv_mul hpole (ne_of_gt hx)).symm

/-- To the left of a pole, `q / p` tends to the infinity of the left-hand sign of `p * q`. -/
private theorem tendsto_div_nhdsLT (hpole : q.rootMultiplicity a < p.rootMultiplicity a) :
    ((p * q).derivSignLeft a = 1 → Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[<] a) atTop) ∧
      ((p * q).derivSignLeft a = -1 →
        Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[<] a) atBot) := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hpole
  by_cases hq : q = 0
  · simp [hq]
  have hs : sign ((-1) ^ (p.rootMultiplicity a - q.rootMultiplicity a) * cofactorDiv p q a a) =
      (p * q).derivSignLeft a := by
    rw [sign_mul, sign_pow, sign_neg (neg_one_lt_zero), sign_cofactorDiv,
      derivSignLeft_mul_eq hpole hq]
  rw [← hs]
  refine tendsto_of_eventuallyEq_mul (tendsto_inv_pow_sub_nhdsLT (Nat.sub_ne_zero_of_lt hpole))
    (tendsto_const_nhds.mul ((tendsto_cofactorDiv hp q a).mono_left nhdsWithin_le_nhds)) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (eval_div_eval_eq_inv_mul' hpole (ne_of_lt hx)).symm

/-- At a pole of `q / p` where `p * q` is positive to the right, `q / p` tends to `+∞` from the
right. -/
theorem tendsto_div_nhdsGT_atTop (hpole : q.rootMultiplicity a < p.rootMultiplicity a)
    (hs : (p * q).derivSignRight a = 1) :
    Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[>] a) atTop :=
  (tendsto_div_nhdsGT hpole).1 hs

/-- At a pole of `q / p` where `p * q` is negative to the right, `q / p` tends to `-∞` from the
right. -/
theorem tendsto_div_nhdsGT_atBot (hpole : q.rootMultiplicity a < p.rootMultiplicity a)
    (hs : (p * q).derivSignRight a = -1) :
    Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[>] a) atBot :=
  (tendsto_div_nhdsGT hpole).2 hs

/-- At a pole of `q / p` where `p * q` is positive to the left, `q / p` tends to `+∞` from the
left. -/
theorem tendsto_div_nhdsLT_atTop (hpole : q.rootMultiplicity a < p.rootMultiplicity a)
    (hs : (p * q).derivSignLeft a = 1) :
    Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[<] a) atTop :=
  (tendsto_div_nhdsLT hpole).1 hs

/-- At a pole of `q / p` where `p * q` is negative to the left, `q / p` tends to `-∞` from the
left. -/
theorem tendsto_div_nhdsLT_atBot (hpole : q.rootMultiplicity a < p.rootMultiplicity a)
    (hs : (p * q).derivSignLeft a = -1) :
    Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[<] a) atBot :=
  (tendsto_div_nhdsLT hpole).2 hs

/-- If `q / p` tends to an infinity on one side of `a`, then `a` is a pole of `q / p` and `q` is
nonzero. -/
private theorem rootMultiplicity_lt_of_tendsto {l L : Filter R} [l.NeBot] (hl : l ≤ 𝓝[≠] a)
    (hL : ∀ c : R, Disjoint L (𝓝 c)) (h : Tendsto (fun x ↦ q.eval x / p.eval x) l L) :
    q.rootMultiplicity a < p.rootMultiplicity a ∧ q ≠ 0 := by
  refine ⟨lt_of_not_ge fun hle ↦ ?_, fun hq ↦ ?_⟩
  · obtain ⟨c, hc⟩ := exists_tendsto_div_nhdsNE_of_rootMultiplicity_le hle
    exact h.not_tendsto (hL c) (hc.mono_left hl)
  · exact h.not_tendsto (hL 0) (by simp [hq])

/-- **The Cauchy jump is a jump from `-∞` to `+∞`.** The jump of `q / p` at `a` is `1` exactly
when `q(x) / p(x)` tends to `-∞` as `x` tends to `a` from the left and to `+∞` as `x` tends to `a`
from the right. -/
theorem cauchyJump_eq_one_iff_tendsto :
    cauchyJump p q a = 1 ↔ Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[<] a) atBot ∧
      Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[>] a) atTop := by
  rw [cauchyJump_eq_one_iff]
  refine ⟨fun ⟨hpole, hl, hr⟩ ↦ ⟨tendsto_div_nhdsLT_atBot hpole hl,
    tendsto_div_nhdsGT_atTop hpole hr⟩, fun ⟨hl, hr⟩ ↦ ?_⟩
  obtain ⟨hpole, hq⟩ := rootMultiplicity_lt_of_tendsto
    (nhdsWithin_mono _ fun _ hx ↦ ne_of_gt hx) (fun c ↦ (disjoint_nhds_atTop c).symm) hr
  have hpq : p * q ≠ 0 := mul_ne_zero (by rintro rfl; simp at hpole) hq
  refine ⟨hpole, ?_, ?_⟩
  · -- The left-hand sign is nonzero, and it cannot be `1`, since then `q / p` would tend to `+∞`.
    rcases hs : (p * q).derivSignLeft a with _ | _ | _
    · exact absurd ((derivSignLeft_eq_zero_iff _ _).1 hs) hpq
    · rfl
    · exact absurd hl ((tendsto_div_nhdsLT_atTop hpole hs).not_tendsto disjoint_atBot_atTop.symm)
  · rcases hs : (p * q).derivSignRight a with _ | _ | _
    · exact absurd ((derivSignRight_eq_zero_iff _ _).1 hs) hpq
    · exact absurd hr ((tendsto_div_nhdsGT_atBot hpole hs).not_tendsto disjoint_atBot_atTop)
    · rfl

/-- **The Cauchy jump is `-1` at a jump from `+∞` to `-∞`.** The jump of `q / p` at `a` is `-1`
exactly when `q(x) / p(x)` tends to `+∞` as `x` tends to `a` from the left and to `-∞` as `x`
tends to `a` from the right. -/
theorem cauchyJump_eq_neg_one_iff_tendsto :
    cauchyJump p q a = -1 ↔ Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[<] a) atTop ∧
      Tendsto (fun x ↦ q.eval x / p.eval x) (𝓝[>] a) atBot := by
  rw [← neg_inj, ← cauchyJump_neg_right, neg_neg, cauchyJump_eq_one_iff_tendsto]
  simp only [eval_neg, neg_div, tendsto_neg_atBot_iff, tendsto_neg_atTop_iff]

end Polynomial
