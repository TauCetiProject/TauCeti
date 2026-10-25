/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Quadratic
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.RingTheory.LocalRing.QuadraticDoubleRoot

/-!
# Integral bases of unramified quadratic extensions

Let `L/K` be a quadratic extension of nonarchimedean local fields and let `ω ∈ 𝒪[L]`. If the
discriminant `Tr(ω)² - 4 N(ω)` of `ω` is a unit of `𝒪[K]`, then `L/K` is unramified and
`(1, ω)` is a basis of `𝒪[L]` over `𝒪[K]`. Indeed `ω` is a root of `X² - Tr(ω) X + N(ω)`
(`Algebra.IsQuadraticExtension.sq_sub_trace_smul_add_norm_eq_zero`), whose reduction modulo
`𝓂[K]` is separable. A root of that reduction in `𝓀[K]` would be simple, so by Hensel's lemma
it would lift to a root in `𝒪[K]`, and `ω` would lie in `K`, where its discriminant vanishes.
So the residue of `ω` lies outside `𝓀[K]`, the residue degree of `L/K` is two, and
`(1, ω)` lifts the residue basis `(1, residue 𝒪[L] ω)`.

The typical generator is `ω = (x - b)/s` for a square root `x ∉ K` of `a ∈ K`, when `2b = s t`
and `b² - a = s² c` with `t, c ∈ 𝒪[K]`. Its discriminant is `t² - 4c = 4a/s²`. With `b = 0` and
`s = 1` this is the basis `(1, √a)` for a unit `a` in odd residue characteristic. For the
nonsquare unit `a` of maximal quadratic defect `4 𝒪[K]`, an attained approximation `b` of `√a`
and `s = π^{v_K(2)}` give the integral basis of the unramified quadratic extension. These bases,
with their traces and norms, are the input of the description of unit norms
`Module.Basis.exists_norm_eq_iff_of_integerRing`.

## Main results

* `TauCeti.isUnramified_of_isUnit_discrim`: an element of `𝒪[L]` of unit discriminant forces
  `L/K` to be unramified.
* `TauCeti.unramifiedQuadraticBasis`: the basis `(1, ω)` of `𝒪[L]` over `𝒪[K]` for such an
  element `ω`.
* `TauCeti.exists_basis_integerRing_of_sq_eq_of_isUnit_discrim`: if `2b = s t`,
  `b² - a = s² c` and `t² - 4c` is a unit, then `(1, (x - b)/s)` is a basis of `𝒪[L]` over
  `𝒪[K]`, with `Tr = -t` and `N = c`.
* `TauCeti.exists_basis_integerRing_of_sq_eq_of_isUnit`: in odd residue characteristic, `(1, √a)`
  is a basis of `𝒪[L]` over `𝒪[K]` for a nonsquare unit `a`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter III, §5.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsQuadraticExtension K L]

section Discrim

variable {ω : 𝒪[L]}

/-- An element of `𝒪[L]` of unit discriminant does not lie in `K`. -/
private theorem coe_notMem_range_of_isUnit_discrim
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) :
    (ω : L) ∉ Set.range (algebraMap K L) := by
  intro h
  have h0 := Algebra.IsQuadraticExtension.discrim_eq_zero_of_mem_range_algebraMap K L h
  rw [← coe_trace_integerRing, ← coe_norm_integerRing] at h0
  exact hω.ne_zero (Subtype.ext (by push_cast; exact h0))

/-- The residue of an element of `𝒪[L]` of unit discriminant lies outside the residue field of
`K`. A root of the reduction of `X² - Tr(ω) X + N(ω)` in `𝓀[K]` would be simple, because the
discriminant is a unit, and Hensel's lemma would lift it to a root in `𝒪[K]`, putting `ω` in
`K`. -/
private theorem residue_notMem_range_of_isUnit_discrim
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) :
    residue 𝒪[L] ω ∉ Set.range (algebraMap 𝓀[K] 𝓀[L]) := by
  have hroot := Algebra.IsQuadraticExtension.sq_sub_trace_smul_add_norm_eq_zero 𝒪[K] ω
  rw [Algebra.smul_def] at hroot
  set T := Algebra.trace 𝒪[K] 𝒪[L] ω
  set N := Algebra.norm 𝒪[K] ω
  rintro ⟨r₀, hr₀⟩
  obtain ⟨r, rfl⟩ := residue_surjective r₀
  rw [ResidueField.algebraMap_residue] at hr₀
  -- `r` is a root of `X² - T X + N` modulo `𝓂[K]`.
  have hres : residue 𝒪[K] (r ^ 2 - T * r + N) = 0 := by
    apply (algebraMap 𝓀[K] 𝓀[L]).injective
    rw [ResidueField.algebraMap_residue, map_zero, ← map_zero (residue 𝒪[L]), ← hroot]
    simp only [map_add, map_sub, map_mul, map_pow, ← ResidueField.algebraMap_residue, hr₀]
  -- Hensel's lemma lifts `r` to a root `s ∈ 𝒪[K]`: the root is simple, as `T² - 4N` is a unit.
  obtain ⟨s, hs, -, -⟩ := HenselianLocalRing.exists_quadratic_root_of_isUnit_discriminant
    (a := -T) (b := -N) (t := r) (by rwa [neg_sq, mul_neg, ← sub_eq_add_neg])
    ((residue_eq_zero_iff _).mp (by simpa [sub_eq_add_neg] using hres))
  have hs' : s ^ 2 - T * s + N = 0 := by linear_combination hs
  -- Then `(ω - s)(ω + s - T) = 0`, so `ω ∈ 𝒪[K]`.
  have hfac : (ω - algebraMap 𝒪[K] 𝒪[L] s) * (ω + algebraMap 𝒪[K] 𝒪[L] (s - T)) = 0 := by
    have := congrArg (algebraMap 𝒪[K] 𝒪[L]) hs'
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at this ⊢
    linear_combination hroot - this
  refine coe_notMem_range_of_isUnit_discrim hω ?_
  rcases mul_eq_zero.mp hfac with h | h
  · exact ⟨s, by rw [← coe_algebraMap_integerRing, ← sub_eq_zero.mp h]⟩
  · refine ⟨((-(s - T) : 𝒪[K]) : K), ?_⟩
    rw [← coe_algebraMap_integerRing, map_neg, ← eq_neg_of_add_eq_zero_left h]

/-- **An element of unit discriminant forces an unramified extension.** If `ω ∈ 𝒪[L]` has
discriminant `Tr(ω)² - 4 N(ω)` a unit of `𝒪[K]`, then the quadratic extension `L/K` is
unramified. -/
theorem isUnramified_of_isUnit_discrim
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) :
    IsUnramified K L := by
  have hli := linearIndependent_one_of_notMem_range_algebraMap 𝓀[K] 𝓀[L]
    (residue_notMem_range_of_isUnit_discrim hω)
  have hle : 2 ≤ inertiaDegree K L := by
    rw [inertiaDegree_def]
    simpa using hli.fintype_card_le_finrank
  have hef := ramificationIndex_mul_inertiaDegree (K := K) (L := L)
  have hepos := ramificationIndex_pos (K := K) (L := L)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K L] at hef
  rw [isUnramified_iff_inertiaDegree_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two K L]
  nlinarith

private theorem finrank_residueField_eq_two_of_isUnit_discrim
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) :
    Module.finrank 𝓀[K] 𝓀[L] = 2 := by
  have := isUnramified_of_isUnit_discrim hω
  rw [← inertiaDegree_def, IsUnramified.inertiaDegree_eq_finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two K L]

/-- **The integral basis of an unramified quadratic extension.** If `ω ∈ 𝒪[L]` has discriminant
`Tr(ω)² - 4 N(ω)` a unit of `𝒪[K]`, then `(1, ω)` is a basis of `𝒪[L]` over `𝒪[K]`. It lifts the
basis `(1, residue 𝒪[L] ω)` of the residue extension. -/
noncomputable def unramifiedQuadraticBasis
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) :
    Module.Basis (Fin 2) 𝒪[K] 𝒪[L] :=
  haveI := isUnramified_of_isUnit_discrim hω
  IsUnramified.basisOfResidueBasis
    (quadraticExtensionBasis 𝓀[K] 𝓀[L] (residue_notMem_range_of_isUnit_discrim hω)
      (finrank_residueField_eq_two_of_isUnit_discrim hω)) ![1, ω]
    (fun i ↦ by fin_cases i <;> simp)

/-- The first vector of the unramified quadratic basis is `1`. -/
@[simp]
theorem unramifiedQuadraticBasis_zero
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) :
    unramifiedQuadraticBasis hω 0 = 1 := by
  simp [unramifiedQuadraticBasis]

/-- The second vector of the unramified quadratic basis is `ω`. -/
@[simp]
theorem unramifiedQuadraticBasis_one
    (hω : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω)) :
    unramifiedQuadraticBasis hω 1 = ω := by
  simp [unramifiedQuadraticBasis]

end Discrim

section SquareRoot

variable {x : L} {a b s : K} {t c : 𝒪[K]}

/-- **The integral basis `(1, (x - b)/s)` of an unramified quadratic extension.** Let `x ∈ L`,
`x ∉ K`, be a square root of `a ∈ K`, and let `b, s ∈ K` with `s ≠ 0`, `2b = s t` and
`b² - a = s² c` for some `t, c ∈ 𝒪[K]` with `t² - 4c` a unit. Then, for `ω = (x - b)/s`, `(1, ω)`
is a basis of `𝒪[L]` over `𝒪[K]` with `Tr ω = -t` and `N ω = c`. The extension `L/K` is then
unramified, by `TauCeti.isUnramified_of_isUnit_discrim`. -/
theorem exists_basis_integerRing_of_sq_eq_of_isUnit_discrim
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L a) (hs : s ≠ 0)
    (ht : 2 * b = s * t) (hbc : b ^ 2 - a = s ^ 2 * c) (hdisc : IsUnit (t ^ 2 - 4 * c)) :
    ∃ B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L], B 0 = 1 ∧
      (B 1 : L) = (x - algebraMap K L b) / algebraMap K L s ∧
      Algebra.trace K L (B 1 : L) = -(t : K) ∧ Algebra.norm K (B 1 : L) = c := by
  obtain ⟨ω, hω, htr, hn⟩ := exists_integerRing_eq_div_of_sq_eq hx hx2 hs ht hbc
  have htr' : Algebra.trace 𝒪[K] 𝒪[L] ω = -t := Subtype.ext (by simpa using htr)
  have hn' : Algebra.norm 𝒪[K] ω = c := Subtype.ext (by simpa using hn)
  have hunit : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] ω ^ 2 - 4 * Algebra.norm 𝒪[K] ω) := by
    rwa [htr', hn', neg_sq]
  exact ⟨unramifiedQuadraticBasis hunit, unramifiedQuadraticBasis_zero hunit,
    by rw [unramifiedQuadraticBasis_one, hω], by rw [unramifiedQuadraticBasis_one, htr],
    by rw [unramifiedQuadraticBasis_one, hn]⟩

/-- **The basis `(1, √a)` in odd residue characteristic.** If `2` is a unit of `𝒪[K]` and
`x ∈ L`, `x ∉ K`, is a square root of a unit `a` of `𝒪[K]`, then `(1, x)` is a basis of `𝒪[L]`
over `𝒪[K]`, with `Tr x = 0` and `N x = -a`. -/
theorem exists_basis_integerRing_of_sq_eq_of_isUnit (h2 : IsUnit (2 : 𝒪[K])) {a : 𝒪[K]}
    (ha : IsUnit a) (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L a) :
    ∃ B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L], B 0 = 1 ∧ (B 1 : L) = x ∧
      Algebra.trace K L (B 1 : L) = 0 ∧ Algebra.norm K (B 1 : L) = -(a : K) := by
  have hdisc : IsUnit ((0 : 𝒪[K]) ^ 2 - 4 * -a) := by
    rw [show (0 : 𝒪[K]) ^ 2 - 4 * -a = 2 * 2 * a by ring]
    exact (h2.mul h2).mul ha
  obtain ⟨B, h0, h1, htr, hn⟩ := exists_basis_integerRing_of_sq_eq_of_isUnit_discrim (b := 0)
    (s := 1) hx hx2 one_ne_zero (by simp) (by simp) hdisc
  exact ⟨B, h0, by simpa using h1, by simpa using htr, by simpa using hn⟩

end SquareRoot

end TauCeti
