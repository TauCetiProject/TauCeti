/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.GaussSum
import TauCeti.Data.ZMod.Torsion

/-!
# Exponent reduction for odd cyclic Gauss sums

For an odd `p`, the Gauss-sum invariant of Nikulin's cyclic generator
`q_θ^{(p)}(p^k)` is periodic with period two in the exponent:

```text
sign q_θ^{(p)}(p^{k+2}) = sign q_θ^{(p)}(p^k).
```

Indeed, the `p`-torsion in `ℤ/p^{k+2}` consists of the multiples of `p^{k+1}` and is
quadratic-isotropic. Multiplication by `p`, followed by reduction modulo `p^k`, identifies the
remaining quadratic form with `q_θ^{(p)}(p^k)`. Isotropic reduction therefore preserves the
Gauss-sum invariant. This reduces the odd-prime formula in Nikulin's Proposition 1.11.2 to its
two base exponents.

## Main declaration

* `TauCeti.FiniteQuadraticModule.gaussSign_oddCyclic_pow_add_two`: increasing the exponent
  of an odd-base cyclic form by two does not change its Gauss-sum invariant.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.11.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

/-- **The Gauss-sum invariant of an odd-base cyclic form is periodic with period two in the
exponent.** The `p`-torsion in `ℤ/p^{k+2}` is quadratic-isotropic, and multiplication by `p`
followed by reduction modulo `p^k` carries its quadratic form to that of `ℤ/p^k`. In particular,
this applies to Nikulin's odd-prime cyclic generators. -/
@[simp]
theorem gaussSign_oddCyclic_pow_add_two {p : ℕ} (hp : Odd p) (k : ℕ) {θ : ℤ}
    (hθ : IsCoprime (p : ℤ) θ) :
    (oddCyclic (p ^ (k + 2)) hp.pow θ).gaussSign =
      (oddCyclic (p ^ k) hp.pow θ).gaussSign := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  let _ : NeZero p := ⟨hp0⟩
  have hoddA : Odd (p ^ (k + 2)) := hp.pow
  have hoddB : Odd (p ^ k) := hp.pow
  have hdvd : p ^ k ∣ p ^ (k + 2) := pow_dvd_pow p (by omega)
  let r := (ZMod.castHom hdvd (ZMod (p ^ k))).toAddMonoidHom
  have hnondegA : (oddCyclic (p ^ (k + 2)) hoddA θ).IsNondegenerate := by
    rw [isNondegenerate_oddCyclic_iff]
    simpa only [Nat.cast_pow] using hθ.pow_left
  have hnondegB : (oddCyclic (p ^ k) hoddB θ).IsNondegenerate := by
    rw [isNondegenerate_oddCyclic_iff]
    simpa only [Nat.cast_pow] using hθ.pow_left
  have hiso (x : ZMod (p ^ (k + 2))) (hx : (p : ℤ) • x = 0) :
      (oddCyclic (p ^ (k + 2)) hoddA θ).quadratic x = 0 := by
    obtain ⟨t, rfl⟩ :=
      ZMod.exists_eq_pow_mul_of_zsmul_eq_zero (p := p) (n := k + 1) (by simpa using hx)
    rw [oddCyclic_quadratic_intCast]
    obtain ⟨s, hs⟩ := hoddA
    rw [hs]
    exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2
      ⟨θ * (s + 1) * p ^ k * t ^ 2, by
        have hs' : p ^ k * (p * p) = 2 * s + 1 := by
          simpa only [pow_add, pow_two] using hs
        have hs'Q : (p : ℚ) ^ k * ((p : ℚ) * p) = 2 * s + 1 := by
          exact_mod_cast hs'
        have hsHalf : (s : ℚ) + 1 = ((p : ℚ) ^ k * (p * p) + 1) / 2 := by
          rw [hs'Q]
          ring
        rw [zsmul_eq_mul]
        push_cast
        rw [hsHalf, ← hs'Q]
        field_simp
        rw [pow_add (p : ℚ) k 1, pow_one]
        ring⟩
  have hq (y : ZMod (p ^ (k + 2))) :
      (oddCyclic (p ^ (k + 2)) hoddA θ).quadratic ((p : ℤ) • y) =
        (oddCyclic (p ^ k) hoddB θ).quadratic (r y) := by
    obtain ⟨s, hs⟩ := hp
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective y
    simp only [r, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, map_intCast,
      zsmul_eq_mul, ← Int.cast_mul, oddCyclic_quadratic_intCast]
    push_cast
    rw [← AddCircle.coe_add_intCast
      (θ * (p ^ k + 1) * j ^ 2 / (2 * p ^ k) : ℚ) (2 * θ * (s + 1) * s * j ^ 2)]
    congr 1
    rw [hs]
    push_cast
    field_simp
    ring
  exact gaussSign_eq_of_quadratic_zsmul_eq hnondegA hnondegB p
    ((isIsotropic_def _).2 fun x hx ↦ hiso x ((zsmulAddGroupHom_apply p x).symm.trans hx)) r
    (ZMod.castHom_surjective hdvd) hq

end TauCeti.FiniteQuadraticModule
