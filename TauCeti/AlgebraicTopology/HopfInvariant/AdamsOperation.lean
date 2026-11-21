/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.AlgebraicTopology.HopfInvariant.PowerDivisibility

/-!
# The Adams-operation divisibility test for Hopf invariant one

Let `f : S^(4r-1) → S^(2r)` with `r ≥ 1` and let `C_f` be its mapping cone. Adams and Atiyah show
that the reduced complex K-group of `C_f` is free abelian on classes `x` and `y`, where `y` comes
from the top cell and `x` restricts to a generator of the reduced K-group of `S^(2r)`, that
`x² = H(f) y` for the Hopf invariant `H(f)`, and that the Adams operations act by
`ψᵏ x = kʳ x + b_k y` and `ψᵏ y = k²ʳ y` for some integers `b_k`, with `ψ² x ≡ x² (mod 2)`.

This file contains the algebra and arithmetic that turn these facts into the conclusion
`r ∈ {1, 2, 4}` when `H(f)` is odd, stated for an arbitrary abelian group with a basis `x, y`
and additive maps `ψ²`, `ψ³` of this shape:

* comparing `ψˢ ψᵗ x` with `ψᵗ ψˢ x` on the `y`-coordinate gives
  `sʳ (sʳ - 1) b_t = tʳ (tʳ - 1) b_s`;
* the congruence `ψ² x ≡ x² (mod 2)` makes `b₂ ≡ H(f) (mod 2)`, so `b₂` is odd when `H(f)` is;
* taking `s = 2` and `t = 3`, the power `2ʳ` then divides `3ʳ - 1`, which happens only for
  `r ∈ {1, 2, 4}` (`TauCeti.eq_one_or_eq_two_or_eq_four_of_odd_mul_eq`).

## Main results

* `TauCeti.pow_mul_pow_sub_one_mul_eq_pow_mul_pow_sub_one_mul`: the relation
  `sʳ (sʳ - 1) b_t = tʳ (tʳ - 1) b_s` between the off-diagonal coefficients of two commuting
  additive maps of Adams-operation shape.
* `TauCeti.eq_one_or_eq_two_or_eq_four_of_adamsOperation`: if `x, y` is a basis with
  `x * x = h • y` for odd `h`, and commuting `ψ²`, `ψ³` have Adams-operation shape with
  `ψ² x ≡ x * x (mod 2)`, then `r ∈ {1, 2, 4}`.

## References

* J. F. Adams and M. F. Atiyah, *K-theory and the Hopf invariant*, Quart. J. Math. Oxford (2)
  17 (1966), 31–38.
* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017), §2.3.
-/

public section

namespace TauCeti

variable {A : Type*} [AddCommGroup A]

/-- Let `ψˢ` and `ψᵗ` be additive maps acting on `x` and on an element `y` of infinite order as
Adams operations do on the reduced K-theory of a two-cell complex:
`ψˢ x = sʳ x + b_s y`, `ψˢ y = s²ʳ y`, and likewise for `t`. If `ψˢ ψᵗ x = ψᵗ ψˢ x`, then
`sʳ (sʳ - 1) b_t = tʳ (tʳ - 1) b_s`. -/
theorem pow_mul_pow_sub_one_mul_eq_pow_mul_pow_sub_one_mul {x y : A}
    (hy : ¬IsOfFinAddOrder y) {r : ℕ} {s t bs bt : ℤ} {ψs ψt : A →+ A}
    (hsx : ψs x = s ^ r • x + bs • y) (hsy : ψs y = s ^ (2 * r) • y)
    (htx : ψt x = t ^ r • x + bt • y) (hty : ψt y = t ^ (2 * r) • y)
    (hcomm : ψs (ψt x) = ψt (ψs x)) :
    s ^ r * (s ^ r - 1) * bt = t ^ r * (t ^ r - 1) * bs := by
  simp only [htx, hsx, map_add, map_zsmul, hsy, hty] at hcomm
  have h0 : (s ^ r * (s ^ r - 1) * bt - t ^ r * (t ^ r - 1) * bs) • y = 0 := by
    linear_combination (norm := module) hcomm
  by_contra hne
  exact hy (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨_, sub_ne_zero.mpr hne, h0⟩)

/-- **The Adams–Atiyah divisibility test.** Let `x = b 0`, `y = b 1` be a basis of an abelian
group `A` with a multiplication, with `x * x = h • y` for an odd integer `h`. Let `ψ²` and `ψ³` be
additive maps with `ψᵏ x = kʳ x + b_k y` and `ψᵏ y = k²ʳ y` for `k = 2, 3`, such that
`ψ² ψ³ x = ψ³ ψ² x` and `ψ² x ≡ x * x` modulo `2 A`. Then `r ∈ {1, 2, 4}`.

Applied to the reduced K-theory of the mapping cone of `f : S^(4r-1) → S^(2r)`, with `h` the Hopf
invariant of `f`, this shows that odd Hopf invariant occurs only in dimensions `2r ∈ {2, 4, 8}`. -/
theorem eq_one_or_eq_two_or_eq_four_of_adamsOperation [Mul A] (b : Module.Basis (Fin 2) ℤ A)
    {r : ℕ} {h : ℤ} (hh : Odd h) (hsq : b 0 * b 0 = h • b 1) {b₂ b₃ : ℤ} {ψ₂ ψ₃ : A →+ A}
    (h₂x : ψ₂ (b 0) = (2 : ℤ) ^ r • b 0 + b₂ • b 1) (h₂y : ψ₂ (b 1) = (2 : ℤ) ^ (2 * r) • b 1)
    (h₃x : ψ₃ (b 0) = (3 : ℤ) ^ r • b 0 + b₃ • b 1) (h₃y : ψ₃ (b 1) = (3 : ℤ) ^ (2 * r) • b 1)
    (hcomm : ψ₂ (ψ₃ (b 0)) = ψ₃ (ψ₂ (b 0)))
    (hcong : ∃ a, ψ₂ (b 0) - b 0 * b 0 = (2 : ℤ) • a) :
    r = 1 ∨ r = 2 ∨ r = 4 := by
  -- Read the congruence `ψ² x ≡ x * x (mod 2)` in both coordinates: the `x`-coordinate gives
  -- `2 ^ r ≡ 0`, so `r ≠ 0`, and the `y`-coordinate gives `b₂ ≡ h`, so `b₂` is odd.
  obtain ⟨a, ha⟩ := hcong
  have hc (i : Fin 2) : b.repr (ψ₂ (b 0) - b 0 * b 0) i = 2 * b.repr a i := by simp [ha]
  have hc₀ : (2 : ℤ) ^ r = 2 * b.repr a 0 := by simpa [h₂x, hsq] using hc 0
  have hc₁ : b₂ - h = 2 * b.repr a 1 := by simpa [h₂x, hsq] using hc 1
  have hr : r ≠ 0 := by
    rintro rfl
    omega
  have hb₂ : Odd b₂ := by
    obtain ⟨k, hk⟩ := hh
    exact ⟨b.repr a 1 + k, by linarith⟩
  have hy : ¬IsOfFinAddOrder (b 1) := by
    rw [isOfFinAddOrder_iff_zsmul_eq_zero]
    rintro ⟨n, hn, h0⟩
    exact hn (by simpa using congrArg (fun z ↦ b.repr z 1) h0)
  have key := pow_mul_pow_sub_one_mul_eq_pow_mul_pow_sub_one_mul hy h₂x h₂y h₃x h₃y hcomm
  exact eq_one_or_eq_two_or_eq_four_of_odd_mul_eq (Nat.pos_of_ne_zero hr) hb₂ key.symm

end TauCeti
