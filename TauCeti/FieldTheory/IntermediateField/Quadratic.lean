/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

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

public section

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

/-- If `x² ∈ F`, then `x` is integral over `F` (it is a root of `X² - x²`). -/
private theorem isIntegral_of_sq_mem {F : IntermediateField K L} {x : L} (hx2 : x ^ 2 ∈ F) :
    IsIntegral F x := by
  have hx2_int : IsIntegral F (x ^ 2) := by
    simpa using isIntegral_algebraMap (R := F) (A := L) (x := (⟨x ^ 2, hx2⟩ : F))
  exact IsIntegral.of_pow (by norm_num : 0 < 2) hx2_int

/-- If `x² ∈ F`, then the minimal polynomial of `x` over `F` has degree at most `2`, since it
divides the nonzero polynomial `X² - x²`. -/
private theorem minpoly_natDegree_le_two_of_sq_mem {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) : (minpoly F x).natDegree ≤ 2 := by
  have hpoly_ne : ((Polynomial.X : Polynomial F) ^ 2 - Polynomial.C ⟨x ^ 2, hx2⟩) ≠ 0 := by
    intro hzero; have hdeg := congrArg Polynomial.natDegree hzero; norm_num at hdeg
  have hdeg := minpoly.degree_le_of_ne_zero F x hpoly_ne (by simp)
  rw [Polynomial.degree_X_pow_sub_C (n := 2) (by norm_num)] at hdeg
  exact Polynomial.natDegree_le_iff_degree_le.mpr hdeg

/-- If `x² ∈ F`, every element of `F ⊔ K⟮x⟯` has the form `a + b * x` with
`a, b ∈ F`. -/
theorem exists_add_mul_of_mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) {y : L}
    (hy : y ∈ F ⊔ IntermediateField.adjoin K {x}) :
    ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x := by
  -- Since `x² ∈ F`, the element `x` is integral over `F` and the minimal polynomial of `x`
  -- over `F` divides `X² - x²`, so `F⟮x⟯` carries a power basis `1, x` of dimension `≤ 2`.
  have hx_int : IsIntegral F x := isIntegral_of_sq_mem hx2
  -- View `y` as an element of `F⟮x⟯` and write it on the power basis: `y = c₁ * x + c₀`
  -- with `c₀ c₁ ∈ F`, the coefficients of a polynomial of degree `< dim ≤ 2`.
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup K F ({x} : Set L),
    mem_restrictScalars] at hy
  set pb := IntermediateField.adjoin.powerBasis hx_int with hpb
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨y, hy⟩
  have hdim : pb.dim ≤ 2 := by
    rw [hpb, IntermediateField.adjoin.powerBasis_dim]
    exact minpoly_natDegree_le_two_of_sq_mem hx2
  have hfle : f.natDegree ≤ 1 := by
    have := hfdeg.trans_le hdim
    omega
  rw [hpb, Polynomial.eq_X_add_C_of_natDegree_le_one hfle,
    IntermediateField.adjoin.powerBasis_gen] at hf
  refine ⟨algebraMap F L (f.coeff 0), algebraMap F L (f.coeff 1),
    (f.coeff 0).2, (f.coeff 1).2, ?_⟩
  have hfeq := congrArg (Subtype.val (p := (· ∈ adjoin F {x}))) hf
  rw [AdjoinSimple.coe_aeval_gen_apply] at hfeq
  simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X] at hfeq
  linear_combination hfeq

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
  have hx_int : IsIntegral F x := isIntegral_of_sq_mem hx2
  have hfin := IntermediateField.adjoin.finrank hx_int
  have hle : (minpoly F x).natDegree ≤ 2 := minpoly_natDegree_le_two_of_sq_mem hx2
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

-- `restrictScalars` keeps the same carrier and inherited `K`-module structure, so a `K`-finrank is
-- unchanged by it. Mathlib's `Submodule.restrictScalarsEquiv` proves the analogue for submodules,
-- but only as an `F`-linear equivalence, and restricting it to `K` needs `IsScalarTower`/
-- `CompatibleSMul` instances that the tower `K → F → F⟮x⟯` does not provide for
-- `Submodule.restrictScalars K`; so we name the definitional equality here instead.
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
