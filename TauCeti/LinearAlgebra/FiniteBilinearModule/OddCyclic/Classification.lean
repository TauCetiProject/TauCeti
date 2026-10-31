/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
import TauCeti.NumberTheory.LegendreSymbol.QuadraticCongruence

/-!
# Classification of odd cyclic quadratic modules

Every finite quadratic module whose underlying group is cyclic of odd order is isometric to
an `oddCyclic` module. For a nondegenerate module, the coefficient is prime to its order.
Two such cyclic forms are isometric exactly when their coefficients differ by a unit square
modulo the order. Both the presentation and the coefficient criterion apply to degenerate
forms and to the trivial group.
At an odd prime power `p^e`, coefficients prime to `p` with the same Legendre symbol therefore
give isometric generators, since their product is then a square modulo `p^e`.

These results identify the cyclic constituents of odd-primary discriminant forms and their
change-of-generator relation. They do not assert an orthogonal decomposition of a general
odd-primary module.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1 and 1.8.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open AddSubgroup

namespace TauCeti.FiniteQuadraticModule

/-- Every quadratic module on an odd cyclic group has an odd cyclic presentation.
No nondegeneracy hypothesis is needed, and the presentation includes the trivial group. -/
theorem exists_oddCyclic_isometry_of_odd (A : FiniteQuadraticModule) [IsAddCyclic A]
    (hm : Odd (Nat.card A)) :
    ∃ θ : ℤ, Nonempty (Isometry (oddCyclic (Nat.card A) hm θ) A) := by
  let e := zmodAddCyclicAddEquiv (G := A) inferInstance
  have hx : A.quadratic (e 1) ∈ (AddCircle (1 : ℚ))[(Nat.card A : ℤ)] :=
    torsionBy.nsmul_iff.mpr (A.natCard_nsmul_quadratic_of_odd hm (e 1))
  obtain ⟨t, ht⟩ := AddCircle.exists_zsmul_eq_of_mem_torsionBy (1 : ℚ)
    (Nat.cast_ne_zero.mpr hm.pos.ne') hx
  have hgen : A.quadratic (e 1) =
      (oddCyclic (Nat.card A) hm (2 * t)).quadratic (1 : ZMod (Nat.card A)) := by
    rw [← ht, ← AddCircle.coe_zsmul, zsmul_eq_mul,
      ← Int.cast_one (R := ZMod (Nat.card A)), oddCyclic_quadratic_intCast]
    apply (sub_eq_zero.mp ?_)
    rw [← AddCircle.coe_sub]
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    refine ⟨-t, ?_⟩
    push_cast
    have hm0 : (Nat.card A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.pos.ne'
    field_simp
    ring
  exact ⟨2 * t, ⟨cyclicIsometryOfGenerator (Nat.card A) _ _ e hgen⟩⟩

/-- Every nondegenerate quadratic module on an odd cyclic group has an odd cyclic presentation
with coefficient prime to the group order. -/
theorem exists_oddCyclic_isometry (A : FiniteQuadraticModule) [IsAddCyclic A]
    (hm : Odd (Nat.card A)) (hA : A.IsNondegenerate) :
    ∃ θ : ℤ, IsCoprime (Nat.card A : ℤ) θ ∧
      Nonempty (Isometry (oddCyclic (Nat.card A) hm θ) A) := by
  obtain ⟨θ, ⟨f⟩⟩ := exists_oddCyclic_isometry_of_odd A hm
  refine ⟨θ, ?_, ⟨f⟩⟩
  exact (isNondegenerate_oddCyclic_iff _ _ _).mp
    (f.isNondegenerate_iff.mpr hA)

/-- Two odd cyclic quadratic modules of the same order are isometric exactly when their
coefficients differ by a unit square modulo that order. No nondegeneracy hypothesis is needed;
the criterion includes the trivial group `ZMod 1`. -/
@[simp]
theorem nonempty_isometry_oddCyclic_iff (m : ℕ) (hm : Odd m) (θ η : ℤ) :
    Nonempty (Isometry (oddCyclic m hm θ) (oddCyclic m hm η)) ↔
      ∃ u : (ZMod m)ˣ, (θ : ZMod m) = (η : ZMod m) * (u : ZMod m) ^ 2 := by
  have : NeZero m := ⟨hm.pos.ne'⟩
  constructor
  · rintro ⟨f⟩
    let e : ZMod m ≃+ ZMod m := f.toAddEquiv
    let u : (ZMod m)ˣ := ((ZMod.AddAutEquivUnits m) e).toMul
    have hu : (u : ZMod m) = e 1 := by
      simp [u, ZMod.AddAutEquivUnits_apply]
    refine ⟨u, ?_⟩
    have he : (Isometry.toHom f) (1 : ZMod m) = e (1 : ZMod m) :=
      Isometry.toHom_apply f (1 : ZMod m)
    have h := Hom.map_pairing (Isometry.toHom f) (1 : ZMod m) (1 : ZMod m)
    rw [he] at h
    rw [oddCyclic_pairing, oddCyclic_pairing] at h
    have hcoeff := ZMod.toRatAddCircle_injective m h
    simpa only [hu, mul_one, pow_two, mul_assoc] using hcoeff.symm
  · rintro ⟨u, hu⟩
    let e : ZMod m ≃+ ZMod m := AddAut.mulRight u
    have hgen : (oddCyclic m hm η).quadratic (e (1 : ZMod m)) =
        (oddCyclic m hm θ).quadratic (1 : ZMod m) := by
      rw [AddAut.mulRight_apply, one_mul, oddCyclic_quadratic, oddCyclic_quadratic,
        one_pow, mul_one]
      congr 1
      rw [hu]
      ring
    exact ⟨cyclicIsometryOfGenerator m _ _ e hgen⟩

/-- Two odd cyclic generators of order `p^0 = 1` are isometric: both are trivial. -/
theorem nonempty_isometry_oddCyclic_of_eq_zero {p : ℕ} (hp : Odd p) {e : ℕ} (he : e = 0)
    (a b : ℤ) : Nonempty (Isometry (oddCyclic (p ^ e) hp.pow a) (oddCyclic (p ^ e) hp.pow b)) := by
  subst he
  have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
  exact (nonempty_isometry_oddCyclic_iff _ _ a b).2 ⟨1, Subsingleton.elim _ _⟩

/-- Odd cyclic generators `q_a^{(p)}(p^e)` and `q_b^{(p)}(p^e)` with the same Legendre symbol are
isometric: `ab` is then a square modulo `p^e`. -/
theorem nonempty_isometry_oddCyclic_of_legendreSym_eq {p : ℕ} [Fact p.Prime] (hp : Odd p) (e : ℕ)
    {a b : ℤ} (ha : IsCoprime (p : ℤ) a) (hb : IsCoprime (p : ℤ) b)
    (h : legendreSym p a = legendreSym p b) :
    Nonempty (Isometry (oddCyclic (p ^ e) hp.pow a) (oddCyclic (p ^ e) hp.pow b)) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact nonempty_isometry_oddCyclic_of_eq_zero hp rfl a b
  have hp2 : p ≠ 2 := by rintro rfl; exact Nat.not_even_iff_odd.2 hp even_two
  have hab0 : ((a * b : ℤ) : ZMod p) ≠ 0 :=
    ((ZMod.coe_int_isUnit_iff_isCoprime _ p).2 (ha.mul_right hb)).ne_zero
  -- `ab` has `1 + (ab/p) = 2` square roots modulo `p^e`.
  have hcount := TauCeti.ZMod.natCard_sqrts_prime_pow_eq_legendreSym_add_one hp2 he.ne' hab0
  rw [legendreSym.mul, h, ← sq,
    legendreSym.sq_one p ((ZMod.coe_int_isUnit_iff_isCoprime b p).2 hb).ne_zero] at hcount
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 (by omega : 0 < Nat.card
    {x : ZMod (p ^ e) // x ^ 2 = ((a * b : ℤ) : ZMod (p ^ e))})).1
  have hbu : IsUnit (b : ZMod (p ^ e)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime b (p ^ e)).2 (by simpa using hb.pow_left)
  have hxu : IsUnit x := by
    have hau : IsUnit (a : ZMod (p ^ e)) :=
      (ZMod.coe_int_isUnit_iff_isCoprime a (p ^ e)).2 (by simpa using ha.pow_left)
    have : IsUnit (x ^ 2) := by rw [hx]; push_cast; exact hau.mul hbu
    exact isUnit_pow_iff two_ne_zero |>.1 this
  refine (nonempty_isometry_oddCyclic_iff _ _ a b).2 ⟨hxu.unit * hbu.unit⁻¹, ?_⟩
  have hinv : (b : ZMod (p ^ e)) * ↑hbu.unit⁻¹ = 1 := by
    simpa only [IsUnit.unit_spec] using hbu.unit.mul_inv
  push_cast at hx ⊢
  rw [mul_pow, IsUnit.unit_spec, hx]
  linear_combination (-(a : ZMod (p ^ e)) * (b * ↑hbu.unit⁻¹ + 1)) * hinv

end TauCeti.FiniteQuadraticModule
