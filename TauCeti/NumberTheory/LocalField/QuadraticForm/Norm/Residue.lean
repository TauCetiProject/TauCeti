/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Residue
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Filtration

/-!
# A finite norm test at the quadratic-defect threshold

For a local unit radicand `a` of finite quadratic defect exponent `d`, put
`n = 2 v_K(2) - d + 1`. Every principal unit of depth `n` is a quadratic norm, so a unit
is a norm from `K(√a)` exactly when its residue is represented by the maximal-order norm
polynomial modulo `𝓂[K]^n`.

The criterion applies to any integral basis `(1, ω)`. In particular it can be used with the
translated and scaled square-root bases for odd or maximal unit defect, whose trace and
norm have already been computed. It reduces the unit-norm problem to two coordinates in
a finite ring, not to an unbounded search for integral witnesses. The precision is supplied
by the quadratic-defect bound on principal-unit norms.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel TauCeti

namespace Module.Basis

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsQuadraticExtension K L]

/-- The unit norms for a unit radicand of finite defect exponent `d` are exactly the unit
values of its integral norm polynomial modulo `𝓂[K]^(2 v_K(2) - d + 1)`. The basis is a
basis of the maximal order, not merely of the square-root suborder. -/
theorem exists_norm_eq_iff_exists_quotient_normForm_of_defectExponent_eq
    (B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L]) (hB : B 0 = 1) (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ}
    (hd : defectExponent a = (d : ℤ)) {s : L} (hs2 : s ^ 2 = algebraMap K L (a : K))
    (b : 𝒪[K]ˣ) :
    (∃ z : L, Algebra.norm K z = (b : K)) ↔
      ∃ x y : 𝒪[K] ⧸ 𝓂[K] ^ (2 * dyadicLevel K h2 - d + 1),
        x ^ 2 + Ideal.Quotient.mk _ (Algebra.trace 𝒪[K] 𝒪[L] (B 1)) * x * y +
          Ideal.Quotient.mk _ (Algebra.norm 𝒪[K] (B 1)) * y ^ 2 =
            Ideal.Quotient.mk _ (b : 𝒪[K]) := by
  have hs : s ∉ Set.range (algebraMap K L) := by
    rintro ⟨t, rfl⟩
    have ht : t ^ 2 = (a : K) := (algebraMap K L).injective (by
      simpa only [map_pow] using hs2)
    exact not_isSquare_of_defectExponent_eq hd
      (Units.isSquare_coe_iff.mp ⟨t, by simpa only [sq] using ht.symm⟩)
  have hnorm : normGroup K L = quadraticNormSubgroup (a : K) := by
    ext u
    rw [mem_normGroup_iff_exists_sq_sub_mul_sq L hs hs2,
      ← hilbertSymbol_eq_one_iff a u, hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup]
  apply B.exists_norm_eq_iff_exists_quotient_normForm hB (Nat.succ_pos _) ?_ b
  rw [hnorm]
  exact unitFiltration_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha hd

end Module.Basis
