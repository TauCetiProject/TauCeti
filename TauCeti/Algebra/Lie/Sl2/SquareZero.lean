/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# `sl₂` pairs whose raising and lowering elements square to zero

Let `H`, `E`, `F` satisfy the `sl₂` relations for the ring commutator of an associative ring, as in
`TauCeti/Algebra/Lie/Sl2/Associative.lean`, and assume in addition that `E` and `F` square to zero.
For a representation that means the `α`-string through every weight has length at most two, so the
module is a sum of copies of the trivial and the standard two-dimensional representation. This file
records what that hypothesis buys.

First it halves the relation `H E - E H = 2 E` to `E F E = E`: once `E ^ 2 = 0` both `H E` and
`-E H` are already equal to `E F E`. The two products `E F` and `F E` then become orthogonal
idempotents whose difference is `H`, cutting out the two ends of each `α`-string.

Second, a square-zero element makes the exponential `1 + t E` affine in its parameter, and the
Chevalley rank-one identity

```text
x_α(u) x_{-α}(-u⁻¹) x_α(u) = h_α(u) n_α,      n_α = x_α(1) x_{-α}(-1) x_α(1),
```

holds over every commutative coefficient ring, at every unit `u`, because both sides equal
`1 + u E - u⁻¹ F - E F - F E`. The left-hand side is the triple product computed in
`triple_product_of_mul_self_eq_zero`, and the right-hand side is the diagonal element
`1 + (u - 1) E F + (u⁻¹ - 1) F E` rescaling the two root terms of that normal form at parameters
`(1, -1)`, which is `torus_mul_triple_product_of_mul_self_eq_zero`. Neither step divides by
anything: the square-zero hypothesis truncates every divided-power exponential after its first
term, so no denominator is ever introduced.

Together these are the rank-one inputs to the scheme-theoretic root generation of an explicit
Chevalley--Demazure carrier whose representation has short `α`-strings, the standard symplectic
carrier of type `Cₙ` among them.

## Main results

* `e_mul_f_mul_e_of_mul_self_eq_zero` and `f_mul_e_mul_f_of_mul_self_eq_zero`: the halved `sl₂`
  relations `E F E = E` and `F E F = F`.
* `triple_product_of_mul_self_eq_zero`: the normal form of `(1 + α E) (1 + β F) (1 + α E)` when
  `α β = -1`, over an arbitrary commutative coefficient ring.
* `torus_mul_triple_product_of_mul_self_eq_zero`: multiplying that normal form at `(1, -1)` by a
  diagonal element rescales its two root terms.
* `mul_apply_of_eq_intCast_smul`: an integer eigenvector of `H` has eigenvalue `1`, `0` or `-1`,
  and in the outer two cases it is fixed by one of the two idempotents and killed by the other.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3, Lemma 20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti

namespace Sl2

/-! ## Halving the `sl₂` relation -/

section HalfRelation

variable {A : Type*} [Ring A] [Algebra ℚ A] {H E F : A}

/-- **A square-zero raising element satisfies `E F E = E`.** Both `H E` and `-E H` equal `E F E`
once `E * E = 0`, so the `sl₂` relation `H E - E H = 2 E` halves to the displayed identity. -/
theorem e_mul_f_mul_e_of_mul_self_eq_zero (hEE : E * E = 0) (hef : E * F - F * E = H)
    (hhe : H * E - E * H = 2 • E) : E * F * E = E := by
  have h1 : E * F * E = H * E := by
    have h := congrArg (fun T => T * E) hef
    simp only [sub_mul, mul_assoc F E E, hEE, mul_zero, sub_zero] at h
    exact h
  have h2 : E * H = -(E * F * E) := by
    have h := congrArg (fun T => E * T) hef
    simp only [mul_sub, ← mul_assoc, hEE, zero_mul, zero_sub] at h
    exact h.symm
  -- `2 • (E * F * E) = H * E - E * H = 2 • E`, and `2` is invertible in a `ℚ`-algebra.
  have htwo : ∀ x : A, (2 : ℕ) • x = (2 : ℚ) • x := fun x => by rw [two_nsmul, two_smul]
  have key : (2 : ℚ) • (E * F * E) = (2 : ℚ) • E := by
    simp only [← htwo]
    rw [← hhe, ← h1, h2]
    abel
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hhalf := congrArg (fun z : A => ((2 : ℚ)⁻¹) • z) key
  simpa only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] using hhalf

/-- **A square-zero lowering element satisfies `F E F = F`**, the mirror image of
`e_mul_f_mul_e_of_mul_self_eq_zero` across the `sl₂` triple `(-H, F, E)`. -/
theorem f_mul_e_mul_f_of_mul_self_eq_zero (hFF : F * F = 0) (hef : E * F - F * E = H)
    (hhf : H * F - F * H = -(2 • F)) : F * E * F = F := by
  refine e_mul_f_mul_e_of_mul_self_eq_zero (H := -H) hFF ?_ ?_
  · rw [← hef]; abel
  · rw [neg_mul, mul_neg, sub_neg_eq_add, ← neg_neg (2 • F), ← hhf]
    abel

end HalfRelation

/-! ## The rank-one identity over an arbitrary coefficient ring -/

section RankOne

variable {B : Type*} [CommRing B] {N : Type*} [AddCommGroup N] [Module B N]
variable {E F : Module.End B N}

/-- **The rank-one product of three square-zero exponentials.** When the two parameters multiply
to `-1`, the product `(1 + α E) (1 + β F) (1 + α E)` is `1 + α E + β F - E F - F E`. -/
theorem triple_product_of_mul_self_eq_zero (hEE : E * E = 0) (hEFE : E * F * E = E) {α β : B}
    (hαβ : α * β = -1) :
    (1 + α • E) * (1 + β • F) * (1 + α • E) = 1 + α • E + β • F - E * F - F * E := by
  have hβα : β * α = -1 := by rw [mul_comm]; exact hαβ
  -- Expand the product and collect every coefficient in front of a monomial in `E` and `F`, ...
  simp only [add_mul, mul_add, smul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  -- ... then evaluate the monomials and their coefficients.
  simp only [hEE, hEFE, hαβ, hβα, mul_neg_one, smul_zero, add_zero, neg_smul, one_smul]
  abel

/-- **The coroot value times the Weyl representative.** Multiplying the normal form at parameters
`(1, -1)` by the diagonal element `1 + (α - 1) E F + (β - 1) F E` rescales its two root terms. -/
theorem torus_mul_triple_product_of_mul_self_eq_zero (hEE : E * E = 0) (hFF : F * F = 0)
    (hEFE : E * F * E = E) (hFEF : F * E * F = F) (α β : B) :
    (1 + (α - 1) • (E * F) + (β - 1) • (F * E)) *
        (1 + (1 : B) • E + (-1 : B) • F - E * F - F * E) =
      1 + α • E + (-β) • F - E * F - F * E := by
  -- `E F` and `F E` are orthogonal idempotents annihilating `F` respectively `E` on the right.
  have hQE : F * E * E = 0 := by rw [mul_assoc, hEE, mul_zero]
  have hPF : E * F * F = 0 := by rw [mul_assoc, hFF, mul_zero]
  have hPP : E * F * (E * F) = E * F := by rw [← mul_assoc, hEFE]
  have hQQ : F * E * (F * E) = F * E := by rw [← mul_assoc, hFEF]
  have hPQ : E * F * (F * E) = 0 := by rw [← mul_assoc, mul_assoc E F F, hFF, mul_zero, zero_mul]
  have hQP : F * E * (E * F) = 0 := by rw [← mul_assoc, mul_assoc F E E, hEE, mul_zero, zero_mul]
  -- Expand the product and collect every coefficient in front of a monomial in `E` and `F`, ...
  simp only [add_mul, mul_add, mul_sub, smul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  -- ... then evaluate the monomials and their coefficients.
  simp only [hEFE, hFEF, hQE, hPF, hPP, hQQ, hPQ, hQP, neg_one_mul, smul_zero, one_smul,
    sub_smul, neg_smul, add_zero]
  abel

end RankOne

/-! ## The two idempotents on an integer eigenvector -/

section Eigenvector

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {E F H : Module.End ℚ V}

/-- **The two square-zero products split an integer eigenvector of `H`.** The products `E F` and
`F E` are orthogonal idempotents whose difference is `H`, so a nonzero eigenvector with integer
eigenvalue has eigenvalue `1`, `0` or `-1`, and in the outer two cases it is fixed by `E F`
respectively by `F E` while the other product kills it. -/
theorem mul_apply_of_eq_intCast_smul (hEE : E * E = 0) (hFF : F * F = 0) (hEFE : E * F * E = E)
    (hFEF : F * E * F = F) (hef : E * F - F * E = H) {m : ℤ} {v : V}
    (hv : H v = (m : ℚ) • v) (hv0 : v ≠ 0) :
    (m = 1 ∧ (E * F) v = v ∧ (F * E) v = 0) ∨ (m = 0 ∧ (E * F) v = 0 ∧ (F * E) v = 0) ∨
      (m = -1 ∧ (E * F) v = 0 ∧ (F * E) v = v) := by
  have hPP : E * F * (E * F) = E * F := by rw [← mul_assoc, hEFE]
  have hQQ : F * E * (F * E) = F * E := by rw [← mul_assoc, hFEF]
  have hPQ : E * F * (F * E) = 0 := by rw [← mul_assoc, mul_assoc E F F, hFF, mul_zero, zero_mul]
  have hQP : F * E * (E * F) = 0 := by rw [← mul_assoc, mul_assoc F E E, hEE, mul_zero, zero_mul]
  have hRP : (1 - E * F - F * E) * (E * F) = 0 := by
    rw [sub_mul, sub_mul, one_mul, hPP, hQP]
    abel
  have hRQ : (1 - E * F - F * E) * (F * E) = 0 := by
    rw [sub_mul, sub_mul, one_mul, hPQ, hQQ]
    abel
  have hbase : (E * F) v - (F * E) v = (m : ℚ) • v := by
    rw [← LinearMap.sub_apply, hef, hv]
  -- Applying the two idempotents and their complement to `hbase` isolates the three eigenvalues.
  have k1 : ((1 : ℚ) - m) • ((E * F) v) = 0 := by
    have hap := congrArg (fun w => (E * F) w) hbase
    simp only [map_sub, map_smul, ← Module.End.mul_apply, hPP, hPQ, LinearMap.zero_apply,
      sub_zero] at hap
    rw [sub_smul, one_smul, ← hap, sub_self]
  have k2 : ((1 : ℚ) + m) • ((F * E) v) = 0 := by
    have hap := congrArg (fun w => (F * E) w) hbase
    simp only [map_sub, map_smul, ← Module.End.mul_apply, hQQ, hQP, LinearMap.zero_apply,
      zero_sub] at hap
    rw [add_smul, one_smul, ← hap, add_neg_cancel]
  have k3 : (m : ℚ) • (v - (E * F) v - (F * E) v) = 0 := by
    have hRv : (1 - E * F - F * E) ((m : ℚ) • v) = (m : ℚ) • (v - (E * F) v - (F * E) v) := by
      rw [map_smul, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [← hRv, ← hbase, map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, hRP, hRQ,
      LinearMap.zero_apply, sub_zero]
  have hPv : m ≠ 1 → (E * F) v = 0 := fun hm => by
    have hne : ((1 : ℚ) - m) ≠ 0 := fun hz => hm (by exact_mod_cast (sub_eq_zero.1 hz).symm)
    exact (smul_eq_zero.1 k1).resolve_left hne
  have hQv : m ≠ -1 → (F * E) v = 0 := fun hm => by
    have hne : ((1 : ℚ) + m) ≠ 0 := fun hz =>
      hm (by exact_mod_cast (neg_eq_of_add_eq_zero_right hz).symm)
    exact (smul_eq_zero.1 k2).resolve_left hne
  have hsum : m ≠ 0 → v - (E * F) v - (F * E) v = 0 := fun hm =>
    (smul_eq_zero.1 k3).resolve_left (Int.cast_ne_zero.2 hm)
  have hm : m = 1 ∨ m = 0 ∨ m = -1 := by
    by_contra hcon
    push Not at hcon
    refine hv0 ?_
    have hz := hsum hcon.2.1
    rwa [hPv hcon.1, hQv hcon.2.2, sub_zero, sub_zero] at hz
  rcases hm with hm | hm | hm
  · refine Or.inl ⟨hm, ?_, hQv (by omega)⟩
    have hz := hsum (by omega)
    rw [hQv (by omega), sub_zero, sub_eq_zero] at hz
    exact hz.symm
  · exact Or.inr (Or.inl ⟨hm, hPv (by omega), hQv (by omega)⟩)
  · refine Or.inr (Or.inr ⟨hm, hPv (by omega), ?_⟩)
    have hz := hsum (by omega)
    rw [hPv (by omega), sub_zero, sub_eq_zero] at hz
    exact hz.symm

end Eigenvector

end Sl2

end TauCeti
