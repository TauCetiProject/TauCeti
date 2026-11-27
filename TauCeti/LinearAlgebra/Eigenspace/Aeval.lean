/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic.FieldSimp

/-!
# Generalized eigenspaces of a polynomial in an endomorphism

For an endomorphism `f` of a module over a commutative ring and a polynomial `p`, a vector killed
by `(f - μ) ^ k` is killed by `(p(f) - p(μ)) ^ k`: the generalized eigenspace of `f` at `μ` of
level `k` is contained in that of `p(f)` at `p(μ)`
(`Module.End.genEigenspace_le_genEigenspace_aeval`), and in particular so is the maximal one
(`Module.End.maxGenEigenspace_le_maxGenEigenspace_aeval`). Indeed `p - p(μ)` is divisible by
`X - μ`, and the quotient evaluated at `f` commutes with `f - μ`. This is the eigenspace form of
the spectral mapping theorem for the characteristic roots of `p(f)`.

Along a divisibility `p ∣ q`, a vector killed by a power of `p(f)` is killed by the same power of
`q(f)` (`Module.End.genEigenspace_aeval_zero_le_of_dvd`,
`Module.End.maxGenEigenspace_aeval_zero_le_of_dvd`). An eigenvector of `f²` for `μ` is killed by
`f² - μ` (`Module.End.mem_maxGenEigenspace_aeval_X_sq_sub_C`).

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (1.5.1).
-/

public section

open Polynomial

namespace Module.End

/-- The generalized eigenspace of an endomorphism `f` at `μ` of level `k` is contained in the
generalized eigenspace of `p(f)` at `p(μ)` of the same level. -/
theorem genEigenspace_le_genEigenspace_aeval {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : End R M) (p : R[X]) (μ : R) (k : ℕ∞) :
    f.genEigenspace μ k ≤ (aeval f p).genEigenspace (p.eval μ) k := by
  intro x hx
  obtain ⟨l, hlk, hl⟩ := mem_genEigenspace.1 hx
  -- `p - p(μ)` vanishes at `μ`, so it is `q * (X - μ)` and `p(f) - p(μ) = q(f) * (f - μ)`.
  set q := (p - C (p.eval μ)) /ₘ (X - C μ)
  have hq : p - C (p.eval μ) = q * (X - C μ) := by
    rw [mul_comm, mul_divByMonic_eq_iff_isRoot.2 (by simp)]
  have hpf : aeval f p - p.eval μ • (1 : End R M) = aeval f q * (f - μ • 1) := by
    simpa [Algebra.algebraMap_eq_smul_one] using congrArg (aeval f) hq
  refine mem_genEigenspace.2 ⟨l, hlk, ?_⟩
  have hc : Commute (aeval f q) (f - μ • 1) := by
    have h := (Commute.all q (X - C μ)).map (aeval f)
    rwa [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
  rw [LinearMap.mem_ker] at hl ⊢
  rw [hpf, hc.mul_pow, mul_apply_eq_comp, hl, map_zero]

/-- The maximal generalized eigenspace of an endomorphism `f` at `μ` is contained in the maximal
generalized eigenspace of `p(f)` at `p(μ)`. -/
theorem maxGenEigenspace_le_maxGenEigenspace_aeval {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : End R M) (p : R[X]) (μ : R) :
    f.maxGenEigenspace μ ≤ (aeval f p).maxGenEigenspace (p.eval μ) :=
  genEigenspace_le_genEigenspace_aeval f p μ ⊤

/-- If `p` divides `q`, a vector killed by `p(f) ^ k` is killed by `q(f) ^ k`. -/
theorem genEigenspace_aeval_zero_le_of_dvd {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : End R M) {p q : R[X]} (hpq : p ∣ q) (k : ℕ∞) :
    (aeval f p).genEigenspace 0 k ≤ (aeval f q).genEigenspace 0 k := by
  obtain ⟨r, rfl⟩ := hpq
  intro x hx
  obtain ⟨l, hlk, hl⟩ := mem_genEigenspace.1 hx
  refine mem_genEigenspace.2 ⟨l, hlk, ?_⟩
  rw [LinearMap.mem_ker, zero_smul, sub_zero] at hl ⊢
  rw [mul_comm, map_mul, ((Commute.all r p).map (aeval f)).mul_pow, mul_apply_eq_comp, hl,
    map_zero]

/-- If `p` divides `q`, a vector killed by a power of `p(f)` is killed by a power of `q(f)`. -/
theorem maxGenEigenspace_aeval_zero_le_of_dvd {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : End R M) {p q : R[X]} (hpq : p ∣ q) :
    (aeval f p).maxGenEigenspace 0 ≤ (aeval f q).maxGenEigenspace 0 :=
  genEigenspace_aeval_zero_le_of_dvd f hpq ⊤

/-- An eigenvector of `f²` for `μ` is killed by `f² - μ`. -/
theorem mem_maxGenEigenspace_aeval_X_sq_sub_C {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {f : End R M} {μ : R} {v : M} (hv : f (f v) = μ • v) :
    v ∈ (aeval f (X ^ 2 - C μ)).maxGenEigenspace 0 :=
  (mem_maxGenEigenspace _ _ _).2 ⟨1, by simp [sq, hv]⟩

/-- If `P (U)` kills `y` and `(P / (X - c)) (U)` still kills `y` whenever `c ≠ 0` and `q * c` are
both roots of `P`, then any geometric chain `q ^ i / d` (`i < k`) ending below a root `q ^ k / d`
cancels from `P`. -/
theorem aeval_cofactor_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U : End ℂ V) {y : V} {P : ℂ[X]} {q : ℝ} {d : ℂ}
    (hq : 1 < q) (aeval_P : aeval U P y = 0)
    (two_roots :
      ∀ {c : ℂ} (F : ℂ[X]), (X - C c) * F = P → P.IsRoot ((q : ℂ) * c) → c ≠ 0 →
        aeval U F y = 0)
    (hd : d ≠ 0) (k : ℕ) (R : ℂ[X]) (hroot : P.IsRoot ((q : ℂ) ^ k / d))
    (hP : P = (∏ i ∈ Finset.range k, (C d * X - C ((q : ℂ) ^ i))) * R) :
    aeval U R y = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  induction k generalizing R with
  | zero => simpa [hP] using aeval_P
  | succ k ih =>
    simp only [Finset.prod_range_succ, mul_assoc, pow_succ', mul_div_assoc] at hP hroot
    have h_root_k : P.IsRoot ((q : ℂ) ^ k / d) := by simp [hP, field]
    have eigen_R : U (aeval U R y) = (d⁻¹ * (q : ℂ) ^ k) • aeval U R y := by
      simpa [sub_eq_zero, ← eq_inv_smul_iff₀ hd, smul_smul, -map_pow] using ih _ h_root_k hP
    set Q : ℂ[X] := ∏ i ∈ Finset.range k, (C d * X - C ((q : ℂ) ^ i))
    have cancel : (X - C ((q : ℂ) ^ k / d)) * (d • Q * R) = P := by
      rw [hP, smul_eq_C_mul]
      have h1 : (X - C ((q : ℂ) ^ k / d)) * C d = C d * X - C ((q : ℂ) ^ k) := by
        rw [sub_mul, ← map_mul, div_mul_cancel₀ _ hd, mul_comm X]
      linear_combination (Q * R) * h1
    have killed : aeval U Q (aeval U R y) = 0 := by
      simpa [hd] using two_roots _ cancel hroot (div_ne_zero (pow_ne_zero k hq0) hd)
    have eval_ne : Q.eval (d⁻¹ * (q : ℂ) ^ k) ≠ 0 := by
      intro h0
      rw [eval_prod, Finset.prod_eq_zero_iff] at h0
      obtain ⟨i, hi, h_eq⟩ := h0
      simp only [Finset.mem_range, eval_sub, eval_mul, eval_C, eval_X, sub_eq_zero] at hi h_eq
      have h_pow : (q : ℂ) ^ k = (q : ℂ) ^ i := by
        simpa [← mul_assoc, mul_inv_cancel₀ hd] using h_eq
      have h_powR : q ^ k = q ^ i := by exact_mod_cast h_pow
      exact (pow_lt_pow_right₀ hq hi).ne' h_powR
    rwa [Module.End.aeval_apply_of_mem_apply_eq_smul (p := Q) eigen_R,
      smul_eq_zero_iff_right eval_ne] at killed

end Module.End
