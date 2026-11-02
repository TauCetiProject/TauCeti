/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Basis

/-!
# The canonical symmetrizing trace of the type-A Hecke algebra

The coefficient of `T_1` in the PBW basis is a normalized trace. Its multiplication pairing
satisfies `τ(T_v T_w) = δ_(v,w⁻¹)`, so the bases indexed by `w` and `w⁻¹` are dual and the
pairing is nondegenerate over every commutative coefficient ring, including at roots of unity.
For the rescaled basis `g_w = q ^ length w • T_w`, the pairing satisfies
`τ(g_(w⁻¹) g_w) = (q²) ^ length w` and vanishes on pairs whose indices do not multiply to `1`.

Here the Coxeter system can be any realization of type `A_(n-1)`. No semisimplicity,
positivity, or arbitrary-parameter Markov trace existence is assumed or asserted.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 8.1, for the canonical symmetrizing trace.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open CoxeterSystem

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}
variable {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

/-- The canonical trace: the coefficient of the identity in the PBW basis. -/
noncomputable def canonicalTrace : TypeAHeckeAlgebra R q n →ₗ[R] R :=
  (basisTw q cs).coord 1

/-- The canonical trace is the identity coefficient in PBW coordinates. -/
theorem canonicalTrace_apply (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs x = (basisTw q cs).repr x 1 := (rfl)

open Classical in
@[simp]
theorem canonicalTrace_Tw (w : W) :
    canonicalTrace cs (Tw q cs w) = if w = 1 then (1 : R) else 0 := by
  classical
  rw [canonicalTrace_apply, ← coe_basisTw, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

@[simp]
theorem canonicalTrace_one : canonicalTrace cs (1 : TypeAHeckeAlgebra R q n) = 1 := by
  simpa only [Tw_one, ite_true] using canonicalTrace_Tw (q := q) cs 1

/-- The canonical trace vanishes on each simple generator. -/
@[simp]
theorem canonicalTrace_T (i : Fin (n - 1)) : canonicalTrace cs (T q i) = 0 := by
  classical
  rw [← Tw_simple (q := q) cs i, canonicalTrace_Tw, ite_eq_right (cs.simple_ne_one i)]

/-- The canonical trace restricts to the identity on scalars. -/
@[simp]
theorem canonicalTrace_algebraMap (r : R) :
    canonicalTrace cs (algebraMap R (TypeAHeckeAlgebra R q n) r) = r := by
  simp [Algebra.algebraMap_eq_smul_one]

open Classical in
private theorem canonicalTrace_T_mul_Tw (i : Fin (n - 1)) (w : W) :
    canonicalTrace cs (T q i * Tw q cs w) = if cs.simple i * w = 1 then (1 : R) else 0 := by
  classical
  by_cases hd : cs.IsLeftDescent w i
  · have hw : w ≠ 1 := fun h => cs.not_isLeftDescent_one i (h ▸ hd)
    simp only [T_mul_Tw_of_isLeftDescent cs hd, map_add, map_smul, canonicalTrace_Tw,
      ite_eq_right hw, smul_zero, zero_add]
  · rw [T_mul_Tw_of_not_isLeftDescent cs hd, canonicalTrace_Tw]

open Classical in
private theorem canonicalTrace_Tw_mul_T (i : Fin (n - 1)) (w : W) :
    canonicalTrace cs (Tw q cs w * T q i) = if w * cs.simple i = 1 then (1 : R) else 0 := by
  classical
  by_cases hd : cs.IsRightDescent w i
  · have hw : w ≠ 1 := fun h => cs.not_isRightDescent_one i (h ▸ hd)
    simp only [Tw_mul_T_of_isRightDescent cs hd, map_add, map_smul, canonicalTrace_Tw,
      ite_eq_right hw, smul_zero, zero_add]
  · rw [Tw_mul_T_of_not_isRightDescent cs hd, canonicalTrace_Tw]

private theorem canonicalTrace_T_mul (i : Fin (n - 1)) (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs (T q i * x) = canonicalTrace cs (x * T q i) := by
  have h : (canonicalTrace (q := q) cs).comp (LinearMap.mulLeft R (T q i)) =
      (canonicalTrace cs).comp (LinearMap.mulRight R (T q i)) := by
    apply (basisTw q cs).ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      coe_basisTw, canonicalTrace_T_mul_Tw, canonicalTrace_Tw_mul_T]
    rw [mul_eq_one_comm]
  exact LinearMap.congr_fun h x

/-- The identity-coefficient functional is tracial. -/
theorem canonicalTrace_mul_comm (x y : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs (x * y) = canonicalTrace cs (y * x) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]; trivial
  induction hx using Algebra.adjoin_induction generalizing y with
  | mem _ hx =>
    obtain ⟨i, rfl⟩ := hx
    exact canonicalTrace_T_mul cs i y
  | algebraMap r => rw [Algebra.commutes]
  | add a b _ _ ha hb => simp only [add_mul, mul_add, map_add, ha, hb]
  | mul a b _ _ ha hb =>
    calc
      canonicalTrace cs (a * b * y) = canonicalTrace cs (b * y * a) := by
        rw [mul_assoc, ha]
      _ = canonicalTrace cs (y * (a * b)) := by rw [mul_assoc, hb, mul_assoc]

open Classical in
/-- **PBW orthogonality.** The basis vectors `T_v` and `T_(v⁻¹)` are dual for the
multiplication pairing of the canonical trace. -/
@[simp]
theorem canonicalTrace_Tw_mul_Tw (v w : W) :
    canonicalTrace cs (Tw q cs v * Tw q cs w) = if v * w = 1 then (1 : R) else 0 := by
  classical
  induction hlen : cs.length v using Nat.strong_induction_on generalizing v w with
  | h k ih =>
    by_cases hv : v = 1
    · simp [hv, Tw_one]
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hv
    let u := cs.simple i * v
    have hu : cs.length u < k := by
      simpa only [IsLeftDescent, u, hlen] using hi
    have hui : ¬cs.IsLeftDescent u i := cs.isLeftDescent_iff_not_isLeftDescent_mul.mp hi
    have hvu : v = cs.simple i * u := (cs.simple_mul_simple_cancel_left (w := v) i).symm
    have hTv : Tw q cs v = T q i * Tw q cs u := by
      rw [T_mul_Tw_of_not_isLeftDescent cs hui, ← hvu]
    have heq : u * (w * cs.simple i) = 1 ↔ v * w = 1 := by
      rw [hvu]
      constructor <;> intro h
      · have hh := congrArg (fun z => cs.simple i * z * cs.simple i) h
        simpa [mul_assoc] using hh
      · have hh := congrArg (fun z => cs.simple i * z * cs.simple i) h
        simpa [mul_assoc] using hh
    rw [hTv, mul_assoc, canonicalTrace_mul_comm cs (T q i), mul_assoc]
    by_cases hd : cs.IsRightDescent w i
    · have huw : u * w ≠ 1 := by
        intro h
        have hw : w = u⁻¹ := (eq_inv_of_mul_eq_one_right h)
        subst w
        exact hui (cs.isRightDescent_inv_iff.mp hd)
      rw [Tw_mul_T_of_isRightDescent cs hd, mul_add, mul_smul_comm, map_add, map_smul,
        ih _ hu u w rfl, ite_eq_right huw, smul_zero, zero_add, ih _ hu u _ rfl, heq]
    · rw [Tw_mul_T_of_not_isRightDescent cs hd, ih _ hu u _ rfl, heq]

open Classical in
/-- For `g_w = q ^ length w • T_w`, the trace `τ(g_v g_w)` equals
`(q²) ^ length w` if `v * w = 1`, and `0` otherwise. -/
theorem canonicalTrace_rescaled_Tw_mul_rescaled_Tw (v w : W) :
    canonicalTrace cs (((q : R) ^ cs.length v) • Tw q cs v *
      ((q : R) ^ cs.length w) • Tw q cs w) =
        if v * w = 1 then ((q : R) ^ 2) ^ cs.length w else 0 := by
  classical
  rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, canonicalTrace_Tw_mul_Tw]
  split_ifs with h
  · have hv : v = w⁻¹ := eq_inv_of_mul_eq_one_left h
    simp [hv, cs.length_inv, smul_eq_mul, ← pow_add, ← pow_mul, two_mul]
  · simp

/-- Left multiplication by `T_(w⁻¹)` followed by the canonical trace extracts the `w`-coordinate.
This lets consumers use the dual PBW basis without expanding products. -/
theorem canonicalTrace_Tw_inv_mul (w : W) (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs (Tw q cs w⁻¹ * x) = (basisTw q cs).repr x w := by
  classical
  have h : (canonicalTrace (q := q) cs).comp (LinearMap.mulLeft R (Tw q cs w⁻¹)) =
      (basisTw q cs).coord w := by
    apply (basisTw q cs).ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Module.Basis.coord_apply,
      coe_basisTw, canonicalTrace_Tw_mul_Tw]
    conv_rhs => rw [← coe_basisTw, Module.Basis.repr_self]
    simp [Finsupp.single_apply, inv_mul_eq_one, eq_comm]
  exact LinearMap.congr_fun h x

/-- The multiplication pairing of the canonical trace has zero left radical over any
commutative coefficient ring, even when the Hecke algebra is not semisimple. -/
@[simp]
theorem forall_canonicalTrace_mul_eq_zero_iff (x : TypeAHeckeAlgebra R q n) :
    (∀ y, canonicalTrace cs (x * y) = 0) ↔ x = 0 := by
  constructor
  · intro hx
    apply (basisTw q cs).repr.injective
    ext w
    simpa only [map_zero, Finsupp.zero_apply, ← canonicalTrace_Tw_inv_mul,
      canonicalTrace_mul_comm cs (Tw q cs w⁻¹)] using hx (Tw q cs w⁻¹)
  · rintro rfl
    simp

end TauCeti.TypeAHeckeAlgebra
