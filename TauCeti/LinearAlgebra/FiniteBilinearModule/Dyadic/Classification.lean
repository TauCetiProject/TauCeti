/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Cyclic
import TauCeti.Data.ZMod.UnitSquare
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Classification of cyclic dyadic quadratic modules

Every finite quadratic module whose underlying group is cyclic of order `2^k`, with `k ≥ 1`,
is isometric to a dyadic cyclic module `q_θ^{(2)}(2^k)`.  If the module is nondegenerate,
the coefficient `θ` is odd.  This identifies the cyclic constituents in the dyadic part of
Nikulin's generator decomposition; unlike the odd-primary case, general dyadic modules also
require the rank-two generators `u^{(2)}(2^k)` and `v^{(2)}(2^k)`.

The change-of-generator criterion is also explicit.  An additive automorphism of `ℤ/2^k` is
multiplication by a unit `u`, and it identifies the coefficients `θ` and `η` exactly when

```text
θ / 2^{k+1} = η u² / 2^{k+1}  in ℚ/ℤ.
```

The representative `u.val.val` in the theorem below is the canonical natural representative of
the unit modulo `2^k`.  Changing that representative by a multiple of `2^k` does not change its
square modulo `2^{k+1}`.

For odd coefficients, the criterion reduces to congruence modulo four at order two and
modulo eight at every higher order. Thus the nondegenerate cyclic classes have unique
coefficient representatives `1, 3` at order two and `1, 3, 5, 7` at order `2^k` for `k ≥ 2`.
The uniqueness concerns the isometry class, not the isometry itself. The modulus four
exception is essential: coefficients `1` and `5` agree at order two but not at order four.

## Main declarations

* `TauCeti.FiniteQuadraticModule.exists_dyadicCyclic_isometry_of_card_eq_two_pow`: every
  quadratic module on a cyclic group of order `2^k` has a dyadic cyclic presentation.
* `TauCeti.FiniteQuadraticModule.exists_dyadicCyclic_isometry`: in the nondegenerate case the
  coefficient can be taken odd.
* `TauCeti.FiniteQuadraticModule.dyadicCyclicIsometryOfModEqEight`: odd coefficients
  congruent modulo eight yield isometric cyclic modules at every positive exponent.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_dyadicCyclic_iff`: the unit-square
  coefficient criterion modulo `2^{k+1}`.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_dyadicCyclic_one_iff`: the coefficient
  criterion modulo four at order two, including even coefficients.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_dyadicCyclic_iff_modEq_eight`: the
  coefficient criterion modulo eight at higher orders, for an odd source coefficient.
* `TauCeti.FiniteQuadraticModule.existsUnique_dyadicCyclic_one_isometry`: unique coefficient
  representatives `1, 3` for nondegenerate cyclic modules of order two.
* `TauCeti.FiniteQuadraticModule.existsUnique_dyadicCyclic_isometry_of_two_le`: unique
  coefficient representatives `1, 3, 5, 7` for nondegenerate cyclic modules of higher order.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1 and 1.8.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

open AddSubgroup

namespace TauCeti.FiniteQuadraticModule

/-- Every quadratic module on a cyclic group of order `2^k`, for `k ≥ 1`, has a dyadic cyclic
presentation.  No nondegeneracy hypothesis is needed. -/
theorem exists_dyadicCyclic_isometry_of_card_eq_two_pow (A : FiniteQuadraticModule)
    [IsAddCyclic A] {k : ℕ} [NeZero k] (hcard : Nat.card A = 2 ^ k) :
    ∃ θ : ℤ, Nonempty (Isometry (dyadicCyclic k θ) A) := by
  let e : ZMod (2 ^ k) ≃+ A := hcard ▸ zmodAddCyclicAddEquiv (G := A) inferInstance
  have hx : A.quadratic (e 1) ∈ (AddCircle (1 : ℚ))[((2 ^ (k + 1) : ℕ) : ℤ)] := by
    rw [torsionBy.nsmul_iff]
    simpa [hcard, pow_succ', mul_comm] using A.two_mul_natCard_nsmul_quadratic (e 1)
  obtain ⟨θ, hθ⟩ := AddCircle.exists_zsmul_eq_of_mem_torsionBy (1 : ℚ)
    (Nat.cast_ne_zero.mpr (pow_ne_zero _ two_ne_zero)) hx
  have hgen : A.quadratic (e 1) = (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) := by
    rw [← hθ, ← AddCircle.coe_zsmul, zsmul_eq_mul, ← Int.cast_one (R := ZMod (2 ^ k)),
      dyadicCyclic_quadratic_intCast]
    congr 1
    push_cast
    ring
  exact ⟨θ, ⟨cyclicIsometryOfGenerator (2 ^ k) _ _ e hgen⟩⟩

/-- Every nondegenerate quadratic module on a cyclic group of order `2^k`, for `k ≥ 1`, is
isometric to `q_θ^{(2)}(2^k)` for an odd coefficient `θ`. -/
theorem exists_dyadicCyclic_isometry (A : FiniteQuadraticModule) [IsAddCyclic A]
    {k : ℕ} [NeZero k] (hcard : Nat.card A = 2 ^ k) (hA : A.IsNondegenerate) :
    ∃ θ : ℤ, Odd θ ∧ Nonempty (Isometry (dyadicCyclic k θ) A) := by
  obtain ⟨θ, ⟨f⟩⟩ := exists_dyadicCyclic_isometry_of_card_eq_two_pow A hcard
  refine ⟨θ, ?_, ⟨f⟩⟩
  exact (isNondegenerate_dyadicCyclic_iff k θ).mp (f.isNondegenerate_iff.mpr hA)

private theorem nonempty_isometry_dyadicCyclic_iff_addCircle {k : ℕ} [NeZero k] (θ η : ℤ) :
    Nonempty (Isometry (dyadicCyclic k θ) (dyadicCyclic k η)) ↔
      ∃ u : (ZMod (2 ^ k))ˣ,
        (((θ : ℚ) / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) =
          (((η * (u.val.val : ℤ) ^ 2 : ℤ) : ℚ) / 2 ^ (k + 1) : ℚ) := by
  constructor
  · rintro ⟨f⟩
    let e : ZMod (2 ^ k) ≃+ ZMod (2 ^ k) := f.toAddEquiv
    let u : (ZMod (2 ^ k))ˣ := ((ZMod.AddAutEquivUnits (2 ^ k)) e).toMul
    have hu : (u : ZMod (2 ^ k)) = e 1 := by
      simp [u, ZMod.AddAutEquivUnits_apply]
    refine ⟨u, ?_⟩
    have h : (dyadicCyclic k η).quadratic (e 1) =
        (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) := f.map_app' _
    have hθ : (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) =
        (((θ : ℚ) / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) := by
      simpa using dyadicCyclic_quadratic_intCast k θ 1
    have huval : (u : ZMod (2 ^ k)) = ((u.val.val : ℤ) : ZMod (2 ^ k)) := by simp
    rw [← hu, huval, dyadicCyclic_quadratic_intCast, hθ] at h
    simpa [Int.cast_mul, Int.cast_pow] using h.symm
  · rintro ⟨u, hu⟩
    let e : ZMod (2 ^ k) ≃+ ZMod (2 ^ k) := AddAut.mulRight u
    have hgen : (dyadicCyclic k η).quadratic (e (1 : ZMod (2 ^ k))) =
        (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) := by
      rw [AddAut.mulRight_apply, one_mul]
      have huval : (u : ZMod (2 ^ k)) = ((u.val.val : ℤ) : ZMod (2 ^ k)) := by simp
      rw [huval]
      rw [dyadicCyclic_quadratic_intCast]
      have hθ : (dyadicCyclic k θ).quadratic (1 : ZMod (2 ^ k)) =
          (((θ : ℚ) / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) := by
        simpa using dyadicCyclic_quadratic_intCast k θ 1
      rw [hθ]
      simpa [Int.cast_mul, Int.cast_pow] using hu.symm
    exact ⟨cyclicIsometryOfGenerator (2 ^ k) _ _ e hgen⟩

/-- The dyadic cyclic isometry criterion: `q_θ^{(2)}(2^k)` and
`q_η^{(2)}(2^k)` are isometric exactly when `θ` and `ηu²` agree modulo `2^{k+1}` for
some unit `u` modulo `2^k`.  The unit is represented by its canonical natural representative
`u.val.val`; changing that representative by a multiple of `2^k` leaves its square unchanged
modulo `2^{k+1}`. -/
@[simp]
theorem nonempty_isometry_dyadicCyclic_iff {k : ℕ} [NeZero k] (θ η : ℤ) :
    Nonempty (Isometry (dyadicCyclic k θ) (dyadicCyclic k η)) ↔
      ∃ u : (ZMod (2 ^ k))ˣ,
        (θ : ZMod (2 ^ (k + 1))) = (η * (u.val.val : ℤ) ^ 2 : ℤ) := by
  rw [nonempty_isometry_dyadicCyclic_iff_addCircle]
  apply exists_congr
  intro u
  rw [← (ZMod.toRatAddCircle_injective (2 ^ (k + 1))).eq_iff]
  simp only [ZMod.toRatAddCircle_intCast]
  norm_cast

/-- Odd coefficients congruent modulo eight give isometric cyclic dyadic quadratic forms
at every positive exponent. -/
noncomputable def dyadicCyclicIsometryOfModEqEight (k : ℕ) [NeZero k] {θ η : ℤ}
    (hθ : Odd θ) (h : θ ≡ η [ZMOD 8]) : Isometry (dyadicCyclic k θ) (dyadicCyclic k η) :=
  Classical.choice <| by
    have hη : Odd η := by
      obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp h
      obtain ⟨s, hs⟩ := hθ
      refine ⟨s + 4 * d, ?_⟩
      omega
    obtain ⟨u, hu⟩ := ZMod.exists_unit_sq_mul_intCast_eq_of_modEq_eight k hη h
    let v := ZMod.unitsMap (pow_dvd_pow 2 k.le_succ) u
    have hv : ((v.val.val : ℤ) : ZMod (2 ^ k)) =
        ((u.val.val : ℤ) : ZMod (2 ^ k)) := by
      simp [v, ZMod.unitsMap, ZMod.castHom_apply]
    have hq := congrArg (dyadicCyclic k η).quadratic hv
    rw [dyadicCyclic_quadratic_intCast, dyadicCyclic_quadratic_intCast] at hq
    -- Equal residue representatives give equal cyclic values. The public value
    -- formula lifts this equality back to the common dyadic modulus.
    have hlift : ((η * (v.val.val : ℤ) ^ 2 : ℤ) : ZMod (2 ^ (k + 1))) =
        ((η * (u.val.val : ℤ) ^ 2 : ℤ) : ZMod (2 ^ (k + 1))) := by
      apply (ZMod.toRatAddCircle_injective (2 ^ (k + 1))).eq_iff.mp
      rw [ZMod.toRatAddCircle_intCast, ZMod.toRatAddCircle_intCast]
      push_cast
      exact hq
    refine (nonempty_isometry_dyadicCyclic_iff θ η).mpr ⟨v, ?_⟩
    rw [hlift]
    push_cast
    simpa only [ZMod.natCast_zmod_val] using hu.symm

-- These residue criteria are not simp lemmas: the existing general unit-square criterion
-- already simplifies their left-hand sides. Use them explicitly to select the residue form.
/-- At order two, cyclic dyadic quadratic modules are isometric exactly when their
coefficients agree modulo four. This also holds for even coefficients. -/
theorem nonempty_isometry_dyadicCyclic_one_iff (θ η : ℤ) :
    Nonempty (Isometry (dyadicCyclic 1 θ) (dyadicCyclic 1 η)) ↔ θ ≡ η [ZMOD 4] := by
  rw [nonempty_isometry_dyadicCyclic_iff]
  have hval : (1 : (ZMod (2 ^ 1))ˣ).val.val = 1 := by decide
  constructor
  · rintro ⟨u, hu⟩
    have hu1 : ∀ v : (ZMod (2 ^ 1))ˣ, v = 1 := by decide
    obtain rfl := hu1 u
    rw [hval] at hu
    norm_num at hu
    exact (ZMod.intCast_eq_intCast_iff _ _ 4).mp hu
  · intro h
    refine ⟨1, ?_⟩
    rw [hval]
    norm_num only [Nat.reduceAdd, Nat.reducePow]
    simpa using (ZMod.intCast_eq_intCast_iff _ _ 4).mpr h

/-- At order at least four, nondegenerate cyclic dyadic quadratic modules are isometric
exactly when their coefficients agree modulo eight. Only the source coefficient needs to
be assumed odd; the congruence forces the target coefficient to be odd as well. -/
theorem nonempty_isometry_dyadicCyclic_iff_modEq_eight {k : ℕ} [NeZero k]
    (hk : 2 ≤ k) {θ η : ℤ} (hθ : Odd θ) :
    Nonempty (Isometry (dyadicCyclic k θ) (dyadicCyclic k η)) ↔ θ ≡ η [ZMOD 8] := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (nonempty_isometry_dyadicCyclic_iff θ η).mp h
    have hodd : Odd (u.val.val : ℤ) := by
      have hc := ZMod.val_coe_unit_coprime u
      have ho := Nat.coprime_two_right.mp
        ((Nat.coprime_pow_right_iff (by omega : 0 < k) _ _).mp hc)
      exact_mod_cast ho
    have hs : (u.val.val : ℤ) ^ 2 ≡ 1 [ZMOD 8] := by
      apply Int.modEq_iff_dvd.mpr
      simpa only [neg_sub] using dvd_neg.mpr (Int.eight_dvd_sq_sub_one_of_odd hodd)
    have hm := (ZMod.intCast_eq_intCast_iff _ _ (2 ^ (k + 1))).mp hu
    have hd : (8 : ℤ) ∣ (2 ^ (k + 1) : ℕ) := by
      exact_mod_cast (pow_dvd_pow 2 (by omega : 3 ≤ k + 1))
    simpa only [mul_one] using (hm.of_dvd hd).trans (hs.mul_left η)
  · exact fun h ↦ ⟨dyadicCyclicIsometryOfModEqEight k hθ h⟩

private theorem existsUnique_dyadicCyclic_isometry_of_modEq (A : FiniteQuadraticModule)
    {k : ℕ} [NeZero k] {n : ℕ}
    (hcrit : ∀ θ η : ℤ, Odd θ →
      (Nonempty (Isometry (dyadicCyclic k θ) (dyadicCyclic k η)) ↔ θ ≡ η [ZMOD (2 * n)]))
    (i : Fin n) (e : Isometry (dyadicCyclic k (2 * (i : ℤ) + 1)) A) :
    ∃! j : Fin n, Nonempty (Isometry (dyadicCyclic k (2 * (j : ℤ) + 1)) A) := by
  refine ⟨i, ⟨e⟩, ?_⟩
  rintro j ⟨g⟩
  have hij := (hcrit _ _ ⟨j, by ring⟩).mp ⟨g.trans e.symm⟩
  have hi0 : (i : ℤ) < n := by exact_mod_cast i.isLt
  have hj0 : (j : ℤ) < n := by exact_mod_cast j.isLt
  simp only [Int.ModEq] at hij
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hij
  apply Fin.ext
  omega

/-- Every nondegenerate cyclic quadratic module of order two has exactly one of the
coefficient representatives `1, 3`. The unique index selects the coefficient `2i + 1`. -/
theorem existsUnique_dyadicCyclic_one_isometry (A : FiniteQuadraticModule) [IsAddCyclic A]
    (hcard : Nat.card A = 2) (hA : A.IsNondegenerate) :
    ∃! i : Fin 2, Nonempty (Isometry (dyadicCyclic 1 (2 * (i : ℤ) + 1)) A) := by
  obtain ⟨θ, hθ, ⟨e⟩⟩ := exists_dyadicCyclic_isometry A (k := 1) (by simpa using hcard) hA
  obtain ⟨t, ht⟩ := hθ
  have hres : θ % 4 = 1 ∨ θ % 4 = 3 := by omega
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, 2 * (i : ℤ) + 1 ≡ θ [ZMOD 4] := by
    rcases hres with h | h
    · exact ⟨0, by norm_num [Int.ModEq, h]⟩
    · exact ⟨1, by norm_num [Int.ModEq, h]⟩
  obtain ⟨f⟩ := (nonempty_isometry_dyadicCyclic_one_iff _ _).mpr hi
  exact existsUnique_dyadicCyclic_isometry_of_modEq A
    (fun θ η _ ↦ nonempty_isometry_dyadicCyclic_one_iff θ η) i (f.trans e)

/-- At each order `2^k ≥ 4`, every nondegenerate cyclic quadratic module has exactly one
of the coefficient representatives `1, 3, 5, 7`. The unique index selects `2i + 1`. -/
theorem existsUnique_dyadicCyclic_isometry_of_two_le (A : FiniteQuadraticModule)
    [IsAddCyclic A] {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hcard : Nat.card A = 2 ^ k)
    (hA : A.IsNondegenerate) :
    ∃! i : Fin 4, Nonempty (Isometry (dyadicCyclic k (2 * (i : ℤ) + 1)) A) := by
  obtain ⟨θ, hθ, ⟨e⟩⟩ := exists_dyadicCyclic_isometry A hcard hA
  obtain ⟨t, ht⟩ := hθ
  have hres : θ % 8 = 1 ∨ θ % 8 = 3 ∨ θ % 8 = 5 ∨ θ % 8 = 7 := by omega
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, 2 * (i : ℤ) + 1 ≡ θ [ZMOD 8] := by
    rcases hres with h | h | h | h
    · exact ⟨0, by norm_num [Int.ModEq, h]⟩
    · exact ⟨1, by norm_num [Int.ModEq, h]⟩
    · exact ⟨2, by norm_num [Int.ModEq, h]⟩
    · exact ⟨3, by norm_num [Int.ModEq, h]⟩
  have hodd : Odd (2 * (i : ℤ) + 1) := ⟨i, by ring⟩
  let f := dyadicCyclicIsometryOfModEqEight k hodd hi
  exact existsUnique_dyadicCyclic_isometry_of_modEq A
    (fun _ _ hθ ↦ nonempty_isometry_dyadicCyclic_iff_modEq_eight hk hθ) i (f.trans e)

end TauCeti.FiniteQuadraticModule
