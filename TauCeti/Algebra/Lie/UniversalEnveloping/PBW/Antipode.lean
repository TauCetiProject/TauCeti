/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.LeadingTerm

/-!
# The antipode and PBW order

The antipode preserves the PBW filtration of a universal enveloping algebra over any
commutative ring. On a word it reverses the factors and contributes one minus sign per
factor. Reordering a word changes it only by terms of lower PBW degree, so on degree `n`
the antipode acts by `(-1)^n` modulo the preceding filtration step.

These statements require no freeness or characteristic hypothesis. In particular they apply
to the rational enveloping algebra containing a Kostant integral form and control the order
of its restricted antipode.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§17 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "S" => _root_.UniversalEnvelopingAlgebra.antipode R

/-- The antipode preserves PBW filtration degree. -/
theorem antipode_mem_pbwFiltration {n : ℕ} {a : U} (ha : a ∈ pbwFiltration R L n) :
    S a ∈ pbwFiltration R L n := by
  apply (pbwFiltration_le_iff R L (p := (pbwFiltration R L n).comap S)).2 ?_ ha
  intro l hl
  rw [Submodule.mem_comap, _root_.UniversalEnvelopingAlgebra.antipode_prod_map_ι]
  exact Submodule.smul_mem _ _ (prod_map_ι_mem_pbwFiltration R L (by simpa using hl))

/-- Membership in a PBW filtration step is unchanged by the involutive antipode. -/
@[simp]
theorem antipode_mem_pbwFiltration_iff {n : ℕ} {a : U} :
    S a ∈ pbwFiltration R L n ↔ a ∈ pbwFiltration R L n := by
  refine ⟨fun ha ↦ ?_, antipode_mem_pbwFiltration R L⟩
  simpa only [_root_.UniversalEnvelopingAlgebra.antipode_antipode] using
    antipode_mem_pbwFiltration R L ha

/-- The antipode maps each PBW filtration step onto itself. -/
@[simp]
theorem map_antipode_pbwFiltration (n : ℕ) :
    (pbwFiltration R L n).map S = pbwFiltration R L n := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact antipode_mem_pbwFiltration R L hb
  · intro ha
    exact ⟨S a, antipode_mem_pbwFiltration R L ha,
      _root_.UniversalEnvelopingAlgebra.antipode_antipode R a⟩

/-- The antipode also preserves the preceding PBW filtration step. -/
@[simp]
theorem antipode_mem_pbwFiltrationPrevious_iff {n : ℕ} {a : U} :
    S a ∈ pbwFiltrationPrevious R L n ↔ a ∈ pbwFiltrationPrevious R L n := by
  cases n with
  | zero =>
    simp only [pbwFiltrationPrevious_zero, Submodule.mem_bot]
    exact LinearMap.map_eq_zero_iff S
      (_root_.UniversalEnvelopingAlgebra.antipode_bijective R).injective
  | succ n => simp only [pbwFiltrationPrevious_succ, antipode_mem_pbwFiltration_iff]

/-- **The leading sign of the antipode.** For an element of PBW degree at most `n`, the
antipode agrees with multiplication by `(-1)^n` modulo degree strictly below `n`. -/
theorem antipode_sub_neg_one_pow_smul_mem_pbwFiltrationPrevious {n : ℕ} {a : U}
    (ha : a ∈ pbwFiltration R L n) :
    S a - (-1 : R) ^ n • a ∈ pbwFiltrationPrevious R L n := by
  let f : U →ₗ[R] U := S - (-1 : R) ^ n • LinearMap.id
  suffices hle : pbwFiltration R L n ≤ (pbwFiltrationPrevious R L n).comap f by
    exact hle ha
  apply (pbwFiltration_le_iff R L).2
  intro l hl
  simp only [Submodule.mem_comap, f, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  rcases hl.eq_or_lt with hlen | hlen
  · rw [_root_.UniversalEnvelopingAlgebra.antipode_prod_map_ι, hlen, ← smul_sub]
    apply Submodule.smul_mem
    simpa only [List.length_reverse, hlen] using
      prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm R L
        (List.reverse_perm l)
  · cases n with
    | zero => omega
    | succ n =>
      rw [pbwFiltrationPrevious_succ]
      have hw := prod_map_ι_mem_pbwFiltration R L (l := l) (Nat.le_of_lt_succ hlen)
      exact Submodule.sub_mem _ (antipode_mem_pbwFiltration R L hw)
        (Submodule.smul_mem _ _ hw)

end TauCeti.UniversalEnvelopingAlgebra
