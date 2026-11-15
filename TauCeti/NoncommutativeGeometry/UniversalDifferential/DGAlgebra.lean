/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.LinearAlgebra.Graded.ExtendByZero
public import TauCeti.NoncommutativeGeometry.UniversalDifferential.Product
public import TauCeti.RingTheory.GradedAlgebra.DirectSum

/-!
# The differential graded algebra of universal forms

The universal forms `Ωⁿ = A⁺ ⊗ A^⊗n` of a possibly nonunital algebra `A` form the `k`-algebra
`⨁ n, Ωⁿ` under Connes' product. This file makes it a differential graded algebra in the sense
of `TauCeti.IsDGAlgebra`: its internal `ℤ`-grading has the summand `Ωⁿ` in degree `n ≥ 0` and
zero in negative degrees, and the universal differential `d : Ωⁿ → Ωⁿ⁺¹` assembles to a
derivation of degree one squaring to zero.

The algebra `A` maps into degree zero by the homomorphism `TauCeti.UniversalForms.ι`, which does
not preserve an existing unit of `A`: the degree-zero part is the forced unitization `A⁺`.
Appending a letter `b` to a form is right multiplication by `dι(b)`, so the word `x da₁ ⋯ daₙ` is
the product `x · dι(a₁) ⋯ dι(aₙ)`. This is the differential graded algebra on which cycles over
`A` are realized by universal forms.

## Main definitions

* `TauCeti.UniversalForms.grading`: the grading of `⨁ n, Ωⁿ` by form degree, extended by zero
  to `ℤ`.
* `TauCeti.UniversalForms.differential`: the universal differential on `⨁ n, Ωⁿ`.
* `TauCeti.UniversalForms.ι`: the inclusion of `A` as zero-forms.

## Main results

* `TauCeti.UniversalForms.isDGAlgebra`: the universal forms are a differential graded algebra.
* `TauCeti.UniversalForms.of_snoc`: appending a letter `b` is right multiplication by `dι(b)`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, Proposition 3, p. 190.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]

namespace UniversalForms

noncomputable section

variable {k A}

/-! ### The grading -/

variable (k A) in
/-- The grading of `⨁ n, Ωⁿ` by form degree: the summand `Ωⁿ` in degree `n ≥ 0`, and zero in
negative degrees. -/
def grading : ℤ → Submodule k (⨁ n, UniversalForms k A n) :=
  Graded.extendByZero (DirectSum.summand k (UniversalForms k A))

/-- An element has degree `n ≥ 0` exactly when it is a form of degree `n`. -/
theorem mem_grading_natCast_iff {n : ℕ} {x : ⨁ n, UniversalForms k A n} :
    x ∈ grading k A n ↔ ∃ ω : UniversalForms k A n, DirectSum.of _ n ω = x := by
  rw [grading, Graded.extendByZero_natCast, DirectSum.mem_summand]

/-- A form of degree `n` has degree `n`. -/
theorem of_mem_grading {n : ℕ} (ω : UniversalForms k A n) :
    DirectSum.of _ n ω ∈ grading k A n :=
  mem_grading_natCast_iff.2 ⟨ω, rfl⟩

/-- The grading vanishes in negative degrees. -/
theorem grading_of_neg {p : ℤ} (hp : p < 0) : grading k A p = ⊥ :=
  Graded.extendByZero_of_neg _ hp

/-! ### The differential -/

variable (k A) in
/-- The universal differential on `⨁ n, Ωⁿ`, acting as `d : Ωⁿ → Ωⁿ⁺¹` on each summand. -/
def differential : (⨁ n, UniversalForms k A n) →ₗ[k] ⨁ n, UniversalForms k A n :=
  DirectSum.toModule k ℕ _ fun n ↦ DirectSum.lof k ℕ (UniversalForms k A) (n + 1) ∘ₗ d k A n

/-- The differential of a form of degree `n` is its universal differential, of degree
`n + 1`. -/
@[simp]
theorem differential_of {n : ℕ} (ω : UniversalForms k A n) :
    differential k A (DirectSum.of _ n ω) = DirectSum.of _ (n + 1) (d k A n ω) := by
  rw [← DirectSum.lof_eq_of k, differential, DirectSum.toModule_lof, LinearMap.comp_apply,
    DirectSum.lof_eq_of]

/-- A word with scalar coefficient is the differential of the word obtained by moving its first
letter into the coefficient: `1 da₀ da₁ ⋯ daₙ = d(a₀ da₁ ⋯ daₙ)`. -/
theorem of_word_one_eq_differential {n : ℕ} (a : Fin (n + 1) → A) :
    DirectSum.of _ (n + 1) (word k A 1 a) =
      differential k A (DirectSum.of _ n (word k A (a 0 : Unitization k A) (Fin.tail a))) := by
  rw [differential_of, d_word, Unitization.snd_inr, Fin.cons_self_tail]

/-! ### The algebra structure -/

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- The universal forms are a `ℤ`-graded algebra for `TauCeti.UniversalForms.grading`. -/
@[instance_reducible]
noncomputable def gradedAlgebra : GradedAlgebra (grading k A) :=
  Graded.gradedAlgebraExtendByZero _

attribute [instance] gradedAlgebra

/-! ### The inclusion of the algebra -/

variable (k A) in
/-- The inclusion of `A` into the zero-forms `A⁺`. It is a homomorphism of nonunital algebras;
even when `A` has a unit it does not send it to the unit `1 ∈ A⁺`. -/
def ι : A →ₙₐ[k] ⨁ n, UniversalForms k A n where
  toFun a := DirectSum.of _ 0 ((zeroEquiv k A).symm a)
  map_smul' c a := by
    rw [Unitization.inr_smul, map_smul, DirectSum.of_smul, MonoidHom.id_apply]
  map_zero' := by rw [Unitization.inr_zero, map_zero, map_zero]
  map_add' a b := by rw [Unitization.inr_add, map_add, map_add]
  map_mul' a b := by
    simp only [zeroEquiv_symm_apply, of_word_mul_of_word, Unitization.inr_mul]

/-- The inclusion sends a letter to the zero-form it defines. -/
theorem ι_apply (a : A) :
    ι k A a = DirectSum.of _ 0 (word k A (a : Unitization k A) Fin.elim0) := by
  rw [← zeroEquiv_symm_apply]
  rfl

/-- The inclusion of `A` lands in degree zero. -/
theorem ι_mem_grading (a : A) : ι k A a ∈ grading k A 0 :=
  of_mem_grading _

/-- Every zero-form is a scalar multiple of the unit plus the image of a letter. -/
theorem of_zero_eq_smul_one_add_ι (ω : UniversalForms k A 0) :
    DirectSum.of _ 0 ω = (zeroEquiv k A ω).fst • 1 + ι k A (zeroEquiv k A ω).snd := by
  obtain ⟨x, rfl⟩ := (zeroEquiv k A).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply, ι_apply, one_def, ← DirectSum.of_smul, ← map_add,
    zeroEquiv_symm_apply, ← word_eq_smul_one_add]

/-- **Appending a letter is right multiplication by its differential**: `ω db = ω · dι(b)`. -/
theorem of_snoc {n : ℕ} (ω : UniversalForms k A n) (b : A) :
    DirectSum.of _ (n + 1) (snoc k A n ω b) =
      DirectSum.of _ n ω * differential k A (ι k A b) := by
  rw [ι_apply, differential_of, of_mul_of, mul_d_word]

/-! ### The differential graded algebra -/

variable (k A) in
/-- **The universal forms are a differential graded algebra**: the universal differential raises
the form degree by one, squares to zero, and satisfies the graded Leibniz rule. -/
theorem isDGAlgebra :
    IsDGAlgebra (R := k) (A := ⨁ n, UniversalForms k A n) (grading k A) (differential k A) where
  map_mem {p x} hx := by
    rcases lt_or_ge p 0 with hp | hp
    · rw [grading_of_neg hp, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact zero_mem _
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨ω, rfl⟩ := mem_grading_natCast_iff.1 hx
    rw [differential_of, ← Nat.cast_one, ← Nat.cast_add]
    exact of_mem_grading _
  sq_zero x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n ω => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  leibniz {p x} hx y := by
    rcases lt_or_ge p 0 with hp | hp
    · rw [grading_of_neg hp, Submodule.mem_bot] at hx
      rw [hx, zero_mul, zero_mul, map_zero, zero_mul, smul_zero, add_zero]
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨ω, rfl⟩ := mem_grading_natCast_iff.1 hx
    induction y using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero, smul_zero, add_zero]
    | of m η =>
      rw [of_mul_of, differential_of, differential_of, d_mul, map_add, of_cast, differential_of,
        of_mul_of, of_mul_of, Units.smul_def, Units.smul_def, map_zsmul]
      -- The degrees `n + m + 1` and `n + (m + 1)` agree definitionally.
      rfl
    | add y z hy hz => simp only [mul_add, map_add, hy, hz, smul_add]; abel

end

end UniversalForms

end TauCeti
