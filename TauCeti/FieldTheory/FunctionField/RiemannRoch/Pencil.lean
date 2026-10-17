/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree

/-!
# Multiplication by the pencil of a function

For a nonzero function `z`, write `Z` and `D` for its zero and pole divisors.
The sections `1, z` of `L(D)` have no common zero; for nonconstant `z` they form
a pencil. If `deg (A - Z) > 2g - 2`, then every element of `L(A + D)` is
`a + z b` with `a, b ∈ L(A)`. The results also allow constant `z`.

In particular, for `D = (z)∞` and sufficiently large `n`,
`L((n + 1)D) = L(nD) + z L(nD)`. Iteration expresses all higher sections using
powers of `z` and a single finite-dimensional space of sections. This is the
multiplication input for finite generation of the section ring of `D` over the
polynomial algebra on its two sections `1, z`.

The argument is the base-point-free pencil calculation: the intersection of
`L(A)` and `z L(A)` is `L(A - Z)`, and Riemann–Roch computes the dimension of their
sum. Multiplication by `z` is the existing equivalence
`TauCeti.riemannRochSpaceEquivSubPrincipal`.

## References

* Hartshorne, *Algebraic Geometry*, Chapter IV, Section 3, for the
  base-point-free pencil argument and section rings.
* Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
  Theorem 1.5.17, for Riemann–Roch in high degree.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The pencil `1, z` generates `L(A + (z)∞)` from `L(A)` in high degree.
The second summand is `z L(A)`, expressed as a Riemann–Roch space via the principal divisor. -/
theorem riemannRochSpace_add_poles_eq_sup (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (z : Fˣ) (A : Divisor k F)
    (hA : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree (A - Divisor.zeros hF z)) :
    riemannRochSpace (A + Divisor.poles hF z) =
      riemannRochSpace A ⊔ riemannRochSpace (A - Divisor.principal hF z) := by
  have hZ : 0 ≤ Divisor.zeros hF z := (Divisor.isEffective_zeros hF z).zero_le
  have hD : 0 ≤ Divisor.poles hF z := (Divisor.isEffective_poles hF z).zero_le
  have hinf : A ⊓ (A - Divisor.principal hF z) = A - Divisor.zeros hF z := by
    ext P
    simp only [WeilDivisor.coeff_inf, WeilDivisor.coeff_sub,
      Divisor.coeff_principal, Divisor.coeff_zeros]
    omega
  have hsup : A ⊔ (A - Divisor.principal hF z) = A + Divisor.poles hF z := by
    ext P
    simp only [WeilDivisor.coeff_sup, WeilDivisor.coeff_add, WeilDivisor.coeff_sub,
      Divisor.coeff_principal, Divisor.coeff_poles]
    omega
  have hle : riemannRochSpace A ⊔ riemannRochSpace (A - Divisor.principal hF z) ≤
      riemannRochSpace (A + Divisor.poles hF z) := by
    rw [← hsup]
    exact sup_le (riemannRochSpace_mono le_sup_left) (riemannRochSpace_mono le_sup_right)
  have hlow : A - Divisor.zeros hF z ≤ A := sub_le_self _ hZ
  have hhigh : A ≤ A + Divisor.poles hF z := le_add_of_nonneg_right hD
  have hdimLow := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
    hF hex hA
  have hdimA := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
    hF hex (hA.trans (Divisor.degree_le_of_le hlow))
  have hdimHigh := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree
    hF hex (hA.trans (Divisor.degree_le_of_le (hlow.trans hhigh)))
  have hdegrees : Divisor.degree (Divisor.zeros hF z) = Divisor.degree (Divisor.poles hF z) := by
    have h := Divisor.degree_principal hF z
    rw [← Divisor.zeros_sub_poles hF z, Divisor.degree_sub] at h
    omega
  have := finiteDimensional_riemannRochSpace hF A
  have := finiteDimensional_riemannRochSpace hF (A - Divisor.principal hF z)
  have := finiteDimensional_riemannRochSpace hF (A + Divisor.poles hF z)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (riemannRochSpace A)
    (riemannRochSpace (A - Divisor.principal hF z))
  rw [← riemannRochSpace_inf, hinf, ← Divisor.dim_def, ← Divisor.dim_def,
    ← Divisor.dim_def, Divisor.dim_sub_principal] at hdim
  simp only [Divisor.degree_sub, Divisor.degree_add, hdegrees] at hdimLow hdimHigh
  rw [← Divisor.dim_def]
  omega

/-- Every section of `A + (z)∞` decomposes as `a + z b` with both terms drawn from `L(A)`,
provided `A - (z)₀` has degree above the canonical degree. -/
theorem mem_riemannRochSpace_add_poles_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (z : Fˣ) (A : Divisor k F)
    (hA : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree (A - Divisor.zeros hF z)) (f : F) :
    f ∈ riemannRochSpace (A + Divisor.poles hF z) ↔
      ∃ a ∈ riemannRochSpace A, ∃ b ∈ riemannRochSpace A, f = a + (z : F) * b := by
  rw [riemannRochSpace_add_poles_eq_sup hF hex z A hA]
  constructor
  · intro hf
    obtain ⟨a, ha, c, hc, hsum⟩ := Submodule.mem_sup.mp hf
    let b := (riemannRochSpaceEquivSubPrincipal hF z A).symm ⟨c, hc⟩
    refine ⟨a, ha, b, b.property, ?_⟩
    have hc' : (z : F) * (b : F) = c := by
      rw [← riemannRochSpaceEquivSubPrincipal_apply]
      exact congrArg Subtype.val
        ((riemannRochSpaceEquivSubPrincipal hF z A).apply_symm_apply ⟨c, hc⟩)
    exact hsum.symm.trans (congrArg (a + ·) hc'.symm)
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Submodule.add_mem_sup ha (mul_mem_riemannRochSpace_sub_principal hF z hb)

/-- Multiplication by `1, z` generates the next multiple of the pole divisor.
The bound is on the preceding multiple, so all three Riemann–Roch dimensions are in high degree. -/
theorem mem_riemannRochSpace_succ_nsmul_poles_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (z : Fˣ) (n : ℕ)
    (hn : 2 * (genus k F : ℤ) - 1 ≤ ((n : ℤ) - 1) * Divisor.degree (Divisor.poles hF z)) (f : F) :
    f ∈ riemannRochSpace ((n + 1) • Divisor.poles hF z) ↔
      ∃ a ∈ riemannRochSpace (n • Divisor.poles hF z),
        ∃ b ∈ riemannRochSpace (n • Divisor.poles hF z), f = a + (z : F) * b := by
  have hdegrees : Divisor.degree (Divisor.zeros hF z) = Divisor.degree (Divisor.poles hF z) := by
    have h := Divisor.degree_principal hF z
    rw [← Divisor.zeros_sub_poles hF z, Divisor.degree_sub] at h
    omega
  have hbound : 2 * (genus k F : ℤ) - 1 ≤
      Divisor.degree (n • Divisor.poles hF z - Divisor.zeros hF z) := by
    rw [Divisor.degree_sub, map_nsmul, nsmul_eq_mul, hdegrees]
    nlinarith [hn]
  simpa only [add_nsmul, one_nsmul] using
    mem_riemannRochSpace_add_poles_iff hF hex z (n • Divisor.poles hF z) hbound f

/-- All higher sections are generated by one space `L(ND)` and bounded powers of `z`,
where `D = (z)∞`. Thus a basis of `L(ND)` supplies finitely many generators for the
high-degree part of the section ring as a module over the pencil `1, z`. -/
theorem riemannRochSpace_add_nsmul_poles_eq_span (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (z : Fˣ) (N : ℕ)
    (hN : 2 * (genus k F : ℤ) - 1 ≤ ((N : ℤ) - 1) * Divisor.degree (Divisor.poles hF z))
    (m : ℕ) :
    riemannRochSpace ((N + m) • Divisor.poles hF z) =
      Submodule.span k {f : F | ∃ i ≤ m, ∃ a ∈ riemannRochSpace (N • Divisor.poles hF z),
        f = (z : F) ^ i * a} := by
  have hD : 0 ≤ Divisor.poles hF z := (Divisor.isEffective_poles hF z).zero_le
  have hdegD : 0 ≤ Divisor.degree (Divisor.poles hF z) := Divisor.degree_nonneg hD
  induction m with
  | zero =>
    apply le_antisymm
    · intro f hf
      exact Submodule.subset_span ⟨0, le_refl 0, f, by simpa using hf, by simp⟩
    · refine Submodule.span_le.mpr ?_
      rintro f ⟨i, hi, a, ha, rfl⟩
      have hi0 : i = 0 := by omega
      simpa [hi0] using ha
  | succ m ih =>
    apply le_antisymm
    · intro f hf
      have hbound : 2 * (genus k F : ℤ) - 1 ≤
          (((N + m : ℕ) : ℤ) - 1) * Divisor.degree (Divisor.poles hF z) := by
        push_cast
        nlinarith
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        (mem_riemannRochSpace_succ_nsmul_poles_iff hF hex z (N + m) hbound f).mp hf
      clear hf
      rw [ih] at ha hb
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.span_mono (by
          rintro f ⟨i, hi, a, ha, rfl⟩
          exact ⟨i, by omega, a, ha, rfl⟩) ha
      · induction hb using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨i, hi, a, ha, rfl⟩ := hf
          apply Submodule.subset_span
          exact ⟨i + 1, by omega, a, ha, by simp [pow_succ, mul_assoc, mul_left_comm]⟩
        | zero => simp
        | add f g _ _ hf hg => simpa [mul_add] using Submodule.add_mem _ hf hg
        | smul c f _ hf => simpa [mul_smul_comm] using Submodule.smul_mem _ c hf
    · refine Submodule.span_le.mpr ?_
      rintro f ⟨i, hi, a, ha, rfl⟩
      have hpow : (z : F) ^ i ∈ riemannRochSpace (i • Divisor.poles hF z) := by
        simpa using pow_mem_riemannRochSpace_zsmul (mem_riemannRochSpace_poles hF z) i
      have hmul := mul_mem_riemannRochSpace_add hpow ha
      rw [← add_nsmul] at hmul
      exact riemannRochSpace_mono (nsmul_le_nsmul_left hD (by omega)) hmul

end TauCeti
