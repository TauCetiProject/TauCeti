/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Examples: local cohomology in degree zero

Mathlib's local cohomology `H⁰_J(M)` is the colimit of `Hom(R ⧸ Jⁿ, M)`, the `J`-power torsion of
`M` (`localCohomology.range_degreeZeroToModule`).

* For a discrete valuation ring `R` with maximal ideal `𝔪`, `H⁰_𝔪(R) = 0`.
* Let `k` be a nonzero commutative ring, `A = k[x₀, x₁, …] ⧸ (x_j ^ (j + 2))` and
  `I = (x₀, x₁, …)`. Every `x_j` is nilpotent, so `V(I) = Spec A`, and `A` is not Noetherian: its
  nilradical is not nilpotent. Yet `H⁰_I(A) = 0`: for a nonzero class `a` and any `n`, a variable
  `x_j` that does not occur in a representative of `a`, with `j + 2 > n`, has `x_jⁿ a ≠ 0`, and
  `x_jⁿ ∈ Iⁿ`. So the native local cohomology of a non-Noetherian ring can vanish in degree zero
  along an ideal whose zero locus is the whole spectrum.
-/

public section

universe u

open CategoryTheory.Limits MvPolynomial

noncomputable section

namespace TauCeti.LocalCohomologyDegreeZeroExample

/-- `H⁰_𝔪(R) = 0` for a discrete valuation ring `R` with maximal ideal `𝔪`. -/
example (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (ModuleCat.of R R)) :=
  localCohomology.isZero_obj_zero_of_ne_bot _ _ (IsDiscreteValuationRing.not_a_field R)

variable (k : Type u) [CommRing k]

/-- The exponents of the relations `x_j ^ (j + 2) = 0`. -/
abbrev relationExponents : Set (ℕ →₀ ℕ) := Set.range fun j ↦ Finsupp.single j (j + 2)

/-- The monomial ideal `(x_j ^ (j + 2))` of `k[x₀, x₁, …]`. -/
abbrev relations : Ideal (MvPolynomial ℕ k) :=
  Ideal.span ((fun s ↦ monomial s (1 : k)) '' relationExponents)

/-- The ring `A = k[x₀, x₁, …] ⧸ (x_j ^ (j + 2))`. -/
abbrev TruncatedRing : Type u := MvPolynomial ℕ k ⧸ relations k

/-- The ideal `I = (x₀, x₁, …)` of `A`. -/
def ideal : Ideal (TruncatedRing k) := Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk _ (X j))

variable {k}

/-- If `x_jⁿ p` lies in the relation ideal for a variable `x_j` not occurring in `p` with
`n < j + 2`, then so does `p`. -/
theorem mem_relations_of_X_pow_mul_mem {p : MvPolynomial ℕ k} {j n : ℕ} (hj : j ∉ p.vars)
    (hn : n < j + 2) (h : X j ^ n * p ∈ relations k) : p ∈ relations k := by
  rw [mem_ideal_span_monomial_image] at h ⊢
  intro m hm
  have hmj : m j = 0 := by
    by_contra hne
    exact hj ((mem_vars_iff_mem_support j).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hne⟩)
  have hsupp : Finsupp.single j n + m ∈ (X j ^ n * p).support := by
    rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul, one_mul]
    exact mem_support_iff.mp hm
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := h _ hsupp
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  rw [Finsupp.single_le_iff] at hle ⊢
  rw [Finsupp.add_apply] at hle
  by_cases hij : i = j
  · subst hij
    rw [Finsupp.single_eq_same, hmj] at hle
    omega
  · rwa [Finsupp.single_eq_of_ne hij, zero_add] at hle

/-- For a nonzero class `a` of `A` and any `n`, some `xⁿ` with `x ∈ I` does not kill `a`: a
variable `x_j` that does not occur in a representative of `a`, with `j + 2 > n`. -/
theorem exists_pow_mul_ne_zero {a : TruncatedRing k} (ha : a ≠ 0) (n : ℕ) :
    ∃ x ∈ ideal k, x ^ n * a ≠ 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  let j := p.vars.sup id + n + 1
  have hj : j ∉ p.vars := fun hj ↦ by
    have := Finset.le_sup (f := id) hj
    simp only [id] at this
    omega
  refine ⟨Ideal.Quotient.mk _ (X j), Ideal.subset_span ⟨j, rfl⟩, fun h ↦ ha ?_⟩
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_relations_of_X_pow_mul_mem hj (by omega) h)

/-- No nonzero element of `A` is killed by a power of `I`. -/
theorem primaryComponent_ideal_eq_bot : Ideal.primaryComponent (TruncatedRing k) (ideal k) = ⊥ :=
  Ideal.primaryComponent_eq_bot_of_forall_exists_pow_smul_ne_zero fun _ ha n ↦ by
    simpa only [smul_eq_mul] using exists_pow_mul_ne_zero ha n

/-- **`H⁰_I(A) = 0`** for the native local cohomology of `A = k[x₀, x₁, …] ⧸ (x_j ^ (j + 2))`
along `I = (x₀, x₁, …)`. -/
theorem isZero_localCohomology_zero :
    IsZero ((localCohomology (ideal k) 0).obj (ModuleCat.of (TruncatedRing k) (TruncatedRing k))) :=
  (localCohomology.isZero_obj_zero_iff _ _).mpr primaryComponent_ideal_eq_bot

/-- Every generator `x_j` of `I` is nilpotent: `x_j ^ (j + 2) = 0`. -/
theorem X_pow_eq_zero (j : ℕ) : (Ideal.Quotient.mk (relations k) (X j)) ^ (j + 2) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, X_pow_eq_monomial]
  exact Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩

/-- `I` lies in the nilradical of `A`, so its zero locus `V(I)` is all of `Spec A`. -/
theorem zeroLocus_ideal : PrimeSpectrum.zeroLocus (ideal k : Set (TruncatedRing k)) = Set.univ := by
  rw [PrimeSpectrum.zeroLocus_eq_univ_iff, SetLike.coe_subset_coe, ideal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact ⟨j + 2, X_pow_eq_zero j⟩

/-- `1` is not in the relation ideal over a nonzero ring: no relation exponent is `0`. -/
theorem one_notMem_relations [Nontrivial k] : (1 : MvPolynomial ℕ k) ∉ relations k := by
  rw [mem_ideal_span_monomial_image]
  intro h
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := h 0 (by simp)
  have := Finsupp.single_le_iff.mp hle
  simp at this

/-- **`A` is not Noetherian.** In a Noetherian ring the nilradical is nilpotent, but `x_m ^ m ≠ 0`
for every `m`, although every `x_j` is nilpotent. -/
theorem not_isNoetherianRing [Nontrivial k] : ¬ IsNoetherianRing (TruncatedRing k) := by
  intro _
  obtain ⟨m, hm⟩ := IsNoetherianRing.isNilpotent_nilradical (TruncatedRing k)
  have hx : Ideal.Quotient.mk (relations k) (X m) ∈ nilradical (TruncatedRing k) :=
    mem_nilradical.mpr ⟨_, X_pow_eq_zero m⟩
  have h := Ideal.pow_mem_pow hx m
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    ← mul_one (X m ^ m)] at h
  exact one_notMem_relations (mem_relations_of_X_pow_mul_mem (by simp) (by omega) h)

end TauCeti.LocalCohomologyDegreeZeroExample

end
