/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
public import TauCeti.RingTheory.Norm.Quadratic
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly

/-!
# Integral bases of Eisenstein quadratic extensions

Let `L/K` be a quadratic extension of nonarchimedean local fields, and let `ω ∈ 𝒪[L]` be a root of
`X² + t X + c` with `t ∈ 𝓂[K]` and `c` a uniformizer of `K`. This polynomial is Eisenstein, so
`ω` generates `L` over `K` and `𝒪[L]` over `𝒪[K]`, and `(1, ω)` is a basis of `𝒪[L]` over `𝒪[K]`
with `Tr ω = -t` and `N ω = c`.

The typical generator is `ω = (x - b)/s` for a square root `x` of `a ∈ K`, when `2b = s t` and
`b² - a = s² c`. With `b = 0` and `s = 1` this is the basis `(1, √a)` for a uniformizer `a`. For a
unit `a` of odd quadratic defect `2k + 1 < 2 v_K(2)`, an optimal approximation `b` of `√a` and
`s = π^k` give the integral basis of the ramified extension `K(√a)`.

## Main results

* `TauCeti.adjoin_eq_top_of_sq_add_mul_add_eq_zero` and
  `TauCeti.algebra_adjoin_eq_top_of_sq_add_mul_add_eq_zero`: a root of an Eisenstein quadratic
  generates `L` over `K` and `𝒪[L]` over `𝒪[K]`.
* `TauCeti.eisensteinQuadraticBasis`: the basis `(1, ω)` of `𝒪[L]` over `𝒪[K]`, with
  `TauCeti.trace_eisensteinQuadraticBasis_one` and `TauCeti.norm_eisensteinQuadraticBasis_one`.
* `TauCeti.exists_basis_integerRing_of_sq_eq`: if `2b = s t` and `b² - a = s² c`, then
  `(1, (x - b)/s)` is a basis of `𝒪[L]` over `𝒪[K]`.
* `TauCeti.exists_basis_integerRing_of_sq_eq_of_irreducible`: for a uniformizer `a`, `(1, √a)` is
  a basis of `𝒪[L]` over `𝒪[K]`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter I, §6, Proposition 17.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField Polynomial
open scoped IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsQuadraticExtension K L]

section Eisenstein

variable {t c : 𝒪[K]} {ω : 𝒪[L]}

/-- A root `ω ∈ 𝒪[L]` of `X² + t X + c`, with `t ∈ 𝓂[K]` and `c` a uniformizer of `K`, generates
the quadratic extension `L` over `K`. -/
theorem adjoin_eq_top_of_sq_add_mul_add_eq_zero (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    K⟮(ω : L)⟯ = ⊤ := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hint : IsIntegral 𝒪[K] ω := IsIntegral.of_finite 𝒪[K] ω
  -- The minimal polynomial of `ω` over `𝒪[K]` is the Eisenstein quadratic, up to a unit.
  have hassoc := associated_minpoly_of_eisenstein_isRoot ω _
    (isEisensteinAt_X_pow_add_C_mul_X_add_C_of_irreducible ht hc le_rfl)
    (by simp [hω])
  have hnat : (minpoly 𝒪[K] ω).natDegree = 2 := by
    rw [natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc),
      natDegree_X_pow_add_C_mul_X_add_C t c le_rfl]
  have hminpoly : minpoly K (ω : L) = (minpoly 𝒪[K] ω).map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.finrank_top', Algebra.IsQuadraticExtension.finrank_eq_two K L,
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := K) (ω : L)),
    hminpoly, (minpoly.monic hint).natDegree_map, hnat]

/-- A root `ω ∈ 𝒪[L]` of `X² + t X + c`, with `t ∈ 𝓂[K]` and `c` a uniformizer of `K`, generates
`𝒪[L]` as an `𝒪[K]`-algebra. -/
theorem algebra_adjoin_eq_top_of_sq_add_mul_add_eq_zero (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    Algebra.adjoin 𝒪[K] {ω} = ⊤ :=
  algebra_adjoin_eq_top_of_eisenstein_adjoin_eq_top
    (isEisensteinAt_X_pow_add_C_mul_X_add_C_of_irreducible ht hc le_rfl)
    (by simp [hω]) (adjoin_eq_top_of_sq_add_mul_add_eq_zero ht hc hω)

private theorem dim_ofAdjoinEqTop'_eq_two (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    (PowerBasis.ofAdjoinEqTop' (IsIntegral.of_finite 𝒪[K] ω)
      (algebra_adjoin_eq_top_of_sq_add_mul_add_eq_zero ht hc hω)).dim = 2 := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  rw [← PowerBasis.finrank, finrank_integerRing, Algebra.IsQuadraticExtension.finrank_eq_two]

/-- **The integral basis of an Eisenstein quadratic extension.** If `ω ∈ 𝒪[L]` is a root of
`X² + t X + c`, with `t ∈ 𝓂[K]` and `c` a uniformizer of `K`, then `(1, ω)` is a basis of `𝒪[L]`
over `𝒪[K]`. -/
noncomputable def eisensteinQuadraticBasis (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    Module.Basis (Fin 2) 𝒪[K] 𝒪[L] :=
  (PowerBasis.ofAdjoinEqTop' (IsIntegral.of_finite 𝒪[K] ω)
    (algebra_adjoin_eq_top_of_sq_add_mul_add_eq_zero ht hc hω)).basis.reindex
      (finCongr (dim_ofAdjoinEqTop'_eq_two ht hc hω))

/-- The first vector of the Eisenstein quadratic basis is `1`. -/
@[simp]
theorem eisensteinQuadraticBasis_zero (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    eisensteinQuadraticBasis ht hc hω 0 = 1 := by
  rw [eisensteinQuadraticBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply_coe]
  simp

/-- The second vector of the Eisenstein quadratic basis is the root `ω`. -/
@[simp]
theorem eisensteinQuadraticBasis_one (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    eisensteinQuadraticBasis ht hc hω 1 = ω := by
  rw [eisensteinQuadraticBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply_coe]
  simp

private theorem coe_notMem_range (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    (ω : L) ∉ Set.range (algebraMap K L) := by
  rintro ⟨y, hy⟩
  have h := adjoin_eq_top_of_sq_add_mul_add_eq_zero ht hc hω
  rw [← hy, IntermediateField.adjoin_simple_eq_bot_iff.mpr (IntermediateField.algebraMap_mem _ y),
    IntermediateField.bot_eq_top_iff_finrank_eq_one,
    Algebra.IsQuadraticExtension.finrank_eq_two K L] at h
  exact absurd h (by norm_num)

/-- The trace of the second vector `ω` of the Eisenstein quadratic basis is `-t`. -/
theorem trace_eisensteinQuadraticBasis_one (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    Algebra.trace K L (eisensteinQuadraticBasis ht hc hω 1 : L) = -(t : K) := by
  rw [eisensteinQuadraticBasis_one]
  exact Algebra.IsQuadraticExtension.trace_eq_neg_of_sq_add_mul_add_eq_zero
    (coe_notMem_range ht hc hω) (by simpa using congrArg ((↑) : 𝒪[L] → L) hω)

/-- The norm of the second vector `ω` of the Eisenstein quadratic basis is `c`. -/
theorem norm_eisensteinQuadraticBasis_one (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0) :
    Algebra.norm K (eisensteinQuadraticBasis ht hc hω 1 : L) = c := by
  rw [eisensteinQuadraticBasis_one]
  exact Algebra.IsQuadraticExtension.norm_eq_of_sq_add_mul_add_eq_zero
    (coe_notMem_range ht hc hω) (by simpa using congrArg ((↑) : 𝒪[L] → L) hω)

end Eisenstein

section SquareRoot

variable {x : L} {a b s : K} {t c : 𝒪[K]}

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- If `x² = a`, `2b = s t` and `b² - a = s² c` with `s ≠ 0`, then `(x - b)/s` is a root of the
monic polynomial `X² + t X + c` over `𝒪[K]`, hence lies in `𝒪[L]`. -/
private theorem exists_sq_add_mul_add_eq_zero_of_sq_eq (hx2 : x ^ 2 = algebraMap K L a)
    (hs : s ≠ 0) (ht : 2 * b = s * t) (hbc : b ^ 2 - a = s ^ 2 * c) :
    ∃ ω : 𝒪[L], (ω : L) = (x - algebraMap K L b) / algebraMap K L s ∧
      ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0 := by
  set y := (x - algebraMap K L b) / algebraMap K L s with hy_def
  have hsL : algebraMap K L s ≠ 0 := (_root_.map_ne_zero _).mpr hs
  have hsy : algebraMap K L s * y = x - algebraMap K L b := mul_div_cancel₀ _ hsL
  have hy : y ^ 2 + algebraMap K L t * y + algebraMap K L c = 0 := by
    have ht' := congrArg (algebraMap K L) ht
    have hbc' := congrArg (algebraMap K L) hbc
    simp only [map_mul, map_sub, map_pow, map_ofNat] at ht' hbc'
    -- Multiply by `s²`: the left side becomes `(x - b)² + 2b (x - b) + b² - a = x² - a`.
    have h : algebraMap K L s ^ 2 * (y ^ 2 + algebraMap K L t * y + algebraMap K L c) = 0 := by
      linear_combination (algebraMap K L s * y + x - algebraMap K L b) * hsy +
        algebraMap K L t * algebraMap K L s * hsy - (x - algebraMap K L b) * ht' - hbc' + hx2
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hsL)
  have hint : IsIntegral 𝒪[K] y := by
    refine ⟨X ^ 2 + C t * X + C c, ?_, ?_⟩
    · rw [add_assoc]
      exact monic_X_pow_add (degree_linear_le.trans_lt (by norm_num))
    · simpa [IsScalarTower.algebraMap_apply 𝒪[K] K L, Algebra.algebraMap_ofSubsemiring_apply]
        using hy
  refine ⟨⟨y, (Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (valuation K)) _).1 hint⟩, rfl, Subtype.ext ?_⟩
  simpa [IsScalarTower.algebraMap_apply 𝒪[K] K L] using hy

/-- **The integral basis `(1, (x - b)/s)`.** Let `x ∈ L` be a square root of `a ∈ K`, and let
`b, s ∈ K` with `s ≠ 0`, `2b = s t` and `b² - a = s² c` for some `t ∈ 𝓂[K]` and some uniformizer
`c` of `K`. Then `ω = (x - b)/s` is a root of the Eisenstein polynomial `X² + t X + c`, and `(1, ω)`
is a basis of `𝒪[L]` over `𝒪[K]` with `Tr ω = -t` and `N ω = c`. -/
theorem exists_basis_integerRing_of_sq_eq (hx2 : x ^ 2 = algebraMap K L a) (hs : s ≠ 0)
    (htm : t ∈ 𝓂[K]) (hc : Irreducible c) (ht : 2 * b = s * t) (hbc : b ^ 2 - a = s ^ 2 * c) :
    ∃ B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L], B 0 = 1 ∧
      (B 1 : L) = (x - algebraMap K L b) / algebraMap K L s ∧
      Algebra.trace K L (B 1 : L) = -(t : K) ∧ Algebra.norm K (B 1 : L) = c := by
  obtain ⟨ω, hω, hroot⟩ := exists_sq_add_mul_add_eq_zero_of_sq_eq hx2 hs ht hbc
  exact ⟨eisensteinQuadraticBasis htm hc hroot, eisensteinQuadraticBasis_zero htm hc hroot,
    by rw [eisensteinQuadraticBasis_one, hω], trace_eisensteinQuadraticBasis_one htm hc hroot,
    norm_eisensteinQuadraticBasis_one htm hc hroot⟩

/-- **The Eisenstein basis `(1, √a)`.** If `x ∈ L` is a square root of a uniformizer `a` of `K`,
then `(1, x)` is a basis of `𝒪[L]` over `𝒪[K]`, with `Tr x = 0` and `N x = -a`. -/
theorem exists_basis_integerRing_of_sq_eq_of_irreducible {a : 𝒪[K]} (ha : Irreducible a)
    (hx2 : x ^ 2 = algebraMap K L a) :
    ∃ B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L], B 0 = 1 ∧ (B 1 : L) = x ∧
      Algebra.trace K L (B 1 : L) = 0 ∧ Algebra.norm K (B 1 : L) = -(a : K) := by
  have hneg : Irreducible (-a) :=
    (Associated.neg_left_iff.mpr (Associated.refl a)).symm.irreducible ha
  obtain ⟨B, h0, h1, htr, hn⟩ := exists_basis_integerRing_of_sq_eq (b := 0) (t := 0) hx2
    one_ne_zero (zero_mem _) hneg (by simp) (by simp)
  exact ⟨B, h0, by simpa using h1, by simpa using htr, by simpa using hn⟩

end SquareRoot

end TauCeti
