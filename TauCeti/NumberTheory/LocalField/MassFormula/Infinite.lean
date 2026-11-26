/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Ore.Basic

/-!
# Infinitely many totally ramified extensions in equal characteristic

Let `K` be a nonarchimedean local field and `0 < n` with `(n : K) = 0`, that is, `K` has
characteristic `p > 0` and `p ∣ n`. Then `σ_K(n) = totallyRamifiedOfDegree K n` is infinite. This
is the converse half of Serre's finiteness dichotomy: outside this case the discriminant exponents
of the members of `σ_K(n)` are bounded, and the mass formula forces `σ_K(n)` to be finite.

The witnesses are Serre's explicit family. For a uniformizer `π` of `K` and `m ≥ 1`, the polynomial
`X ^ n + π ^ m X + π` is Eisenstein and separable, realizing wild exponent `j = n * (m - 1) + 1`
(which has `j % n = 1`, so `(j % n : K) ≠ 0`). By Ore's realizability theorem
(`TauCeti.exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff` and
`TauCeti.isOreAdmissible_iff_of_natCast_eq_zero`), this yields a member of `σ_K(n)` whose wild
exponent is `n * (m - 1) + 1` and hence whose discriminant exponent is `n * m`, so these members
are pairwise distinct.

## Main results

* `TauCeti.exists_mem_totallyRamifiedOfDegree_discriminantExponent_eq`: if `0 < n` and
  `(n : K) = 0`, then every multiple `n * m` with `0 < m` is the discriminant exponent of a member
  of `σ_K(n)`.
* `TauCeti.infinite_totallyRamifiedOfDegree`: if `0 < n` and `(n : K) = 0`, then `σ_K(n)` is
  infinite.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Remarque 1°.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.
-/

public section
noncomputable section

open ValuativeRel
open scoped IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Serre's family of wild extensions.** If `0 < n` and `(n : K) = 0`, then for every `0 < m`
some member of `σ_K(n)` has discriminant exponent `n * m`. -/
theorem exists_mem_totallyRamifiedOfDegree_discriminantExponent_eq {n : ℕ} (hn : 0 < n)
    (hnK : (n : K) = 0) {m : ℕ} (hm : 0 < m) :
    ∃ L ∈ totallyRamifiedOfDegree K n, L.discriminantExponent = n * m := by
  -- `(1 : K) ≠ 0`, so `n ≠ 1`.
  have hn2 : 2 ≤ n := by
    by_contra h
    obtain rfl : n = 1 := by omega
    exact one_ne_zero (by exact_mod_cast hnK : (1 : K) = 0)
  let j : ℕ := n * (m - 1) + 1
  have hmod : j % n = 1 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hadm : IsOreAdmissible 𝒪[K] n j :=
    (isOreAdmissible_iff_of_natCast_eq_zero (Subtype.ext (by simpa using hnK) : (n : 𝒪[K]) = 0)).mpr
      ⟨hn, by simp [hmod]⟩
  obtain ⟨L, hL, hLw⟩ := exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff.mpr hadm
  have hrel := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL
  have hnm : n * (m - 1) + n = n * m := by
    rw [← Nat.mul_add_one, Nat.sub_add_cancel hm]
  exact ⟨L, hL, by omega⟩

/-- **Infinitely many totally ramified extensions in equal characteristic.** If `0 < n` and
`(n : K) = 0`, that is, `K` has characteristic `p > 0` with `p ∣ n`, then `σ_K(n)` is infinite:
its discriminant exponents are unbounded. -/
theorem infinite_totallyRamifiedOfDegree {n : ℕ} (hn : 0 < n) (hnK : (n : K) = 0) :
    (totallyRamifiedOfDegree K n).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image IntermediateField.discriminantExponent).bddAbove
  obtain ⟨L, hL, hLd⟩ :=
    exists_mem_totallyRamifiedOfDegree_discriminantExponent_eq hn hnK (by omega : 0 < B + 1)
  have := hB ⟨L, hL, hLd⟩
  have := Nat.le_mul_of_pos_left (B + 1) hn
  omega

end TauCeti
