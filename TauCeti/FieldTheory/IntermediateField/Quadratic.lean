/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Quadratic normal forms in intermediate fields

This file contains normal-form lemmas for adjoining one element whose square already lies in an
intermediate field, together with the corresponding quadratic finrank and degree-doubling API.
The finrank lemmas live here because they combine the normal form with intermediate-field
scalar restriction for one quadratic tower step.

## Provenance

`exists_add_mul_of_mem_sup_adjoin_sq` is migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where it was a
step in the square-class descent for multiquadratic fields; here it is stated for an arbitrary
field extension.
-/

open IntermediateField

namespace TauCeti.IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `a` and `b` lie in `F`, then `a + b * x` lies in `F ⊔ K⟮x⟯`. -/
theorem mem_sup_adjoin_sq_of_exists {F : IntermediateField K L} {x y : L}
    (hy : ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x) :
    y ∈ F ⊔ IntermediateField.adjoin K {x} := by
  rcases hy with ⟨a, b, ha, hb, rfl⟩
  have hF : F ≤ F ⊔ IntermediateField.adjoin K {x} := le_sup_left
  have hx : IntermediateField.adjoin K {x} ≤ F ⊔ IntermediateField.adjoin K {x} :=
    le_sup_right
  exact add_mem (hF ha)
    (mul_mem (hF hb) (hx (IntermediateField.mem_adjoin_of_mem K (Set.mem_singleton x))))

/-- If `x² ∈ F`, every element of `F ⊔ K⟮x⟯` has the form `a + b * x` with
`a, b ∈ F`. -/
theorem exists_add_mul_of_mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) {y : L}
    (hy : y ∈ F ⊔ IntermediateField.adjoin K {x}) :
    ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x := by
  let S : IntermediateField K L :=
    { carrier := {y | ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x}
      zero_mem' := ⟨0, 0, zero_mem F, zero_mem F, by simp⟩
      add_mem' := by
        rintro y z ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        exact ⟨a + c, b + d, add_mem ha hc, add_mem hb hd, by ring⟩
      one_mem' := ⟨1, 0, one_mem F, zero_mem F, by simp⟩
      mul_mem' := by
        rintro y z ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        refine ⟨a * c + (b * d) * x ^ 2, a * d + b * c, ?_, ?_, by ring⟩
        · exact add_mem (mul_mem ha hc) (mul_mem (mul_mem hb hd) hx2)
        · exact add_mem (mul_mem ha hd) (mul_mem hb hc)
      algebraMap_mem' := fun k => ⟨algebraMap K L k, 0, F.algebraMap_mem k, zero_mem F, by simp⟩
      inv_mem' := by
        classical
        rintro y ⟨a, b, ha, hb, rfl⟩
        by_cases hy0 : a + b * x = 0
        · exact ⟨0, 0, zero_mem F, zero_mem F, by simp [hy0]⟩
        · by_cases hD : a ^ 2 - b ^ 2 * x ^ 2 = 0
          · have hprod : (a - b * x) * (a + b * x) = 0 := by
              calc
                (a - b * x) * (a + b * x) = a ^ 2 - b ^ 2 * x ^ 2 := by ring
                _ = 0 := hD
            have hamul : a - b * x = 0 := (mul_eq_zero.mp hprod).resolve_right hy0
            have haeq : a = b * x := sub_eq_zero.mp hamul
            have hbx : b * x ≠ 0 := by
              intro h
              apply hy0
              rw [haeq, h]
              ring
            have hx0 : x ≠ 0 := by
              intro hx
              apply hbx
              rw [hx, mul_zero]
            have htwo : (2 : L) ≠ 0 := by
              intro htwo
              apply hy0
              rw [haeq, ← two_mul]
              simp [htwo]
            have hden : (2 : L) * b * x ^ 2 ≠ 0 := by
              have hb0 : b ≠ 0 := left_ne_zero_of_mul hbx
              exact mul_ne_zero (mul_ne_zero htwo hb0) (pow_ne_zero 2 hx0)
            have hb0 : b ≠ 0 := left_ne_zero_of_mul hbx
            refine ⟨0, ((2 : L) * b * x ^ 2)⁻¹, zero_mem F, ?_, ?_⟩
            · exact inv_mem (mul_mem (mul_mem (F.natCast_mem 2) hb) hx2)
            · rw [haeq]
              field_simp [hden, hbx, hb0, hx0, htwo]
              rw [mul_zero, zero_mul, zero_add]
              -- `field_simp` leaves the numerator as `1 + 1`; rewrite it to `2` so the
              -- denominator `2 * b * x²` cancels via `div_self`.
              rw [show (1 + 1 : L) = 2 by norm_num]
              exact div_self htwo
          · have hDmem : a ^ 2 - b ^ 2 * x ^ 2 ∈ F :=
              sub_mem (pow_mem ha 2) (mul_mem (pow_mem hb 2) hx2)
            refine ⟨a * (a ^ 2 - b ^ 2 * x ^ 2)⁻¹,
              -b * (a ^ 2 - b ^ 2 * x ^ 2)⁻¹, ?_, ?_, ?_⟩
            · exact mul_mem ha (inv_mem hDmem)
            · exact mul_mem (neg_mem hb) (inv_mem hDmem)
            · field_simp [hD, hy0]
              ring }
  have hle : F ⊔ IntermediateField.adjoin K {x} ≤ S := by
    refine sup_le ?_ ?_
    · intro z hz
      exact ⟨z, 0, hz, zero_mem F, by simp⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨0, 1, zero_mem F, one_mem F, by simp⟩
  exact hle hy

/-- Membership in `F ⊔ K⟮x⟯`, for `x² ∈ F`, is equivalent to having the form `a + b * x`
with `a, b ∈ F`. -/
@[simp]
theorem mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) {y : L} :
    y ∈ F ⊔ IntermediateField.adjoin K {x} ↔
      ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x :=
  ⟨exists_add_mul_of_mem_sup_adjoin_sq hx2, mem_sup_adjoin_sq_of_exists⟩

/-- If `x² ∈ F` but `x ∉ F`, then the simple extension `F⟮x⟯` has finrank two over `F`. -/
theorem finrank_adjoin_simple_eq_two_of_sq_mem_notMem (F : IntermediateField K L) {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) :
    Module.finrank F (IntermediateField.adjoin F {x}) = 2 := by
  have hx2_int : IsIntegral F (x ^ 2) := by
    simpa using isIntegral_algebraMap (R := F) (A := L) (x := (⟨x ^ 2, hx2⟩ : F))
  have hx_int : IsIntegral F x := IsIntegral.of_pow (by norm_num : 0 < 2) hx2_int
  have hfin := IntermediateField.adjoin.finrank hx_int
  have hle : (minpoly F x).natDegree ≤ 2 := by
    have hroot : Polynomial.aeval x
        ((Polynomial.X : Polynomial F) ^ 2 - Polynomial.C ⟨x ^ 2, hx2⟩) = 0 := by simp
    have hdvd : minpoly F x ∣ ((Polynomial.X : Polynomial F) ^ 2 - Polynomial.C ⟨x ^ 2, hx2⟩) :=
      minpoly.dvd F x hroot
    have hpoly_ne :
        ((Polynomial.X : Polynomial F) ^ 2 - Polynomial.C ⟨x ^ 2, hx2⟩) ≠ 0 := by
      intro hzero; have hdeg := congrArg Polynomial.natDegree hzero; norm_num at hdeg
    exact (Polynomial.natDegree_le_of_dvd hdvd hpoly_ne).trans_eq (by simp)
  have hpos : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hx_int
  have hne1 : (minpoly F x).natDegree ≠ 1 := by
    intro hdeg1
    have hfin1 : Module.finrank F (IntermediateField.adjoin F {x}) = 1 := by
      simpa [hfin] using hdeg1
    have hxbot : x ∈ (⊥ : IntermediateField F L) :=
      (IntermediateField.finrank_adjoin_simple_eq_one_iff).mp hfin1
    rw [IntermediateField.mem_bot] at hxbot
    obtain ⟨y, hy⟩ := hxbot
    exact hxF (hy ▸ y.2)
  omega

-- `restrictScalars` keeps the same carrier and inherited `K`-module structure; naming that
-- definitional equality keeps later degree computations from relying on an unexplained `change`.
private theorem finrank_restrictScalars_eq (F : IntermediateField K L)
    (E : IntermediateField F L) :
    Module.finrank K (E.restrictScalars K) = Module.finrank K E := rfl

/-- If `x² ∈ F` but `x ∉ F`, then adjoining `x` doubles the degree:
`[F ⊔ K⟮x⟯ : K] = 2 · [F : K]`. -/
theorem finrank_sup_adjoin_simple_eq_mul_two (F : IntermediateField K L) {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) :
    Module.finrank K ((F ⊔ IntermediateField.adjoin K {x}) : IntermediateField K L)
      = Module.finrank K F * 2 := by
  have hL : (IntermediateField.adjoin F {x}).restrictScalars K
      = F ⊔ IntermediateField.adjoin K {x} :=
    IntermediateField.restrictScalars_adjoin_eq_sup K F ({x} : Set L)
  have hfinL : Module.finrank F (IntermediateField.adjoin F {x}) = 2 :=
    finrank_adjoin_simple_eq_two_of_sq_mem_notMem F hx2 hxF
  calc Module.finrank K ((F ⊔ IntermediateField.adjoin K {x}) : IntermediateField K L)
      = Module.finrank K ((IntermediateField.adjoin F {x}).restrictScalars K) := by rw [hL]
    _ = Module.finrank K (IntermediateField.adjoin F {x}) := by
        rw [finrank_restrictScalars_eq]
    _ = Module.finrank K F * Module.finrank F (IntermediateField.adjoin F {x}) := by
        rw [Module.finrank_mul_finrank]
    _ = Module.finrank K F * 2 := by rw [hfinL]

end TauCeti.IntermediateField
