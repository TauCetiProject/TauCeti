/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The class-group presentation by a family of ideals

Let `R` be a Dedekind domain and `I : ι → (Ideal R)⁰` a finite family of nonzero ideals. The
*presentation map* sends an exponent vector `e : ι → ℤ` to the class `∏ i, [I i] ^ e i`, and the
*relation lattice* is its kernel, a `ℤ`-submodule of `ι → ℤ`. When the classes `[I i]` generate
the class group, the presentation map identifies `Cl(R)` with `(ι → ℤ) ⧸ Λ`, and `Λ` has index
the order of the class group. This is the bridge from relations between ideals, which can be
found and checked one at a time, to the class group: a relation matrix whose columns span `Λ`
then determines `Cl(R)` through its Smith normal form, and full-rank found relations bound the
class number.

The presentation map is written additively, as a `ℤ`-linear map into `Additive (ClassGroup R)`,
so that its kernel is a `ℤ`-submodule and quotients and indices are those of `ℤ`-lattices.
The characteristic lemmas are nevertheless stated multiplicatively, in terms of products of
ideal classes.

## Main definitions

* `ClassGroup.presentation I`: the linear map `e ↦ ∏ i, [I i] ^ e i` from `ι → ℤ` to the
  class group, written additively.
* `ClassGroup.relationLattice I`: its kernel, the lattice of relations between the classes
  `[I i]`.

If the presentation map is surjective, the isomorphism
`(ι → ℤ) ⧸ relationLattice I ≃ₗ[ℤ] Additive (ClassGroup R)` is Mathlib's
`(presentation I).quotKerEquivOfSurjective hI`, transported along `relationLattice_def`, which
evaluates on classes by `LinearMap.quotKerEquivOfSurjective_apply_mk`.

## Main results

* `ClassGroup.mem_relationLattice_iff`: `e` is a relation exactly when `∏ i, [I i] ^ e i = 1`.
* `ClassGroup.natCast_mem_relationLattice_iff_isPrincipal`: a nonnegative exponent vector `e` is
  a relation exactly when the ideal `∏ i, I i ^ e i` is principal.
* `ClassGroup.single_mem_relationLattice_iff`: `k` times the `i`-th basis vector is a relation
  exactly when the order of `[I i]` divides `k`.
* `ClassGroup.relationLattice_eq_top_iff`: every vector is a relation exactly when every `I i` is
  principal; in particular for a principal ideal domain, or for an empty family.
* `ClassGroup.presentation_surjective_iff`: the presentation map is surjective exactly when the
  classes `[I i]` generate the class group.
* `ClassGroup.index_relationLattice`: if the presentation map is surjective, the relation lattice
  has index `Nat.card (ClassGroup R)`, the class number for the ring of integers of a number
  field.

## References

* Jean-François Biasse and Claus Fieker, *Subexponential class group and unit group computation
  in large degree number fields*, LMS J. Comput. Math. 17 (2014), Section 2.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {ι : Type*} [Fintype ι]
  (I : ι → (Ideal R)⁰)

/-- The class-group presentation map of a finite family of nonzero ideals `I`: the `ℤ`-linear
map sending an exponent vector `e` to the class `∏ i, [I i] ^ e i`, written additively. -/
noncomputable def presentation : (ι → ℤ) →ₗ[ℤ] Additive (ClassGroup R) :=
  Fintype.linearCombination ℤ fun i ↦ Additive.ofMul (ClassGroup.mk0 (I i))

/-- The relation lattice of a finite family of nonzero ideals `I`: the exponent vectors `e` with
`∏ i, [I i] ^ e i = 1`, the kernel of the presentation map. -/
noncomputable def relationLattice : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (presentation I)

/-- The relation lattice is the kernel of the presentation map. -/
theorem relationLattice_def : relationLattice I = LinearMap.ker (presentation I) :=
  (rfl)

variable {I}

@[simp]
theorem toMul_presentation_apply (e : ι → ℤ) :
    (presentation I e).toMul = ∏ i, ClassGroup.mk0 (I i) ^ e i := by
  simp [presentation, Fintype.linearCombination_apply, ← ofMul_zpow, ← ofMul_prod]

theorem presentation_apply (e : ι → ℤ) :
    presentation I e = Additive.ofMul (∏ i, ClassGroup.mk0 (I i) ^ e i) := by
  rw [← toMul_presentation_apply, ofMul_toMul]

/-- The presentation map sends `k` times the `i`-th basis vector to `[I i] ^ k`. -/
@[simp]
theorem presentation_single [DecidableEq ι] (i : ι) (k : ℤ) :
    presentation I (Pi.single i k) = Additive.ofMul (ClassGroup.mk0 (I i) ^ k) := by
  rw [presentation, Fintype.linearCombination_apply_single, ofMul_zpow]

/-- An exponent vector `e` is a relation exactly when `∏ i, [I i] ^ e i = 1`. -/
theorem mem_relationLattice_iff {e : ι → ℤ} :
    e ∈ relationLattice I ↔ ∏ i, ClassGroup.mk0 (I i) ^ e i = 1 := by
  rw [relationLattice, LinearMap.mem_ker, ← toMul_eq_one, toMul_presentation_apply]

/-- A nonnegative exponent vector `e` is a relation exactly when the ideal `∏ i, I i ^ e i` is
principal. -/
theorem natCast_mem_relationLattice_iff_isPrincipal {e : ι → ℕ} :
    (fun i ↦ (e i : ℤ)) ∈ relationLattice I ↔
      (∏ i, (I i : Ideal R) ^ e i).IsPrincipal := by
  have hprod : ∏ i, ClassGroup.mk0 (I i) ^ (e i : ℤ) = ClassGroup.mk0 (∏ i, I i ^ e i) := by
    simp [map_prod, map_pow]
  have hmem : ∏ i, (I i : Ideal R) ^ e i = ((∏ i, I i ^ e i : (Ideal R)⁰) : Ideal R) := by
    simp
  rw [mem_relationLattice_iff, hprod, hmem, ← ClassGroup.mk0_eq_one_iff]

/-- `k` times the `i`-th basis vector is a relation exactly when the order of the class `[I i]`
divides `k`. -/
theorem single_mem_relationLattice_iff [DecidableEq ι] {i : ι} {k : ℤ} :
    Pi.single i k ∈ relationLattice I ↔ (orderOf (ClassGroup.mk0 (I i)) : ℤ) ∣ k := by
  rw [relationLattice, LinearMap.mem_ker, presentation_single, ofMul_eq_zero,
    orderOf_dvd_iff_zpow_eq_one]

/-- The `i`-th basis vector is a relation exactly when the ideal `I i` is principal. -/
theorem single_one_mem_relationLattice_iff [DecidableEq ι] {i : ι} :
    Pi.single i 1 ∈ relationLattice I ↔ (I i : Ideal R).IsPrincipal := by
  rw [relationLattice, LinearMap.mem_ker, presentation_single, zpow_one, ofMul_eq_zero,
    ← ClassGroup.mk0_eq_one_iff (I i).2]

/-- Every exponent vector is a relation exactly when every ideal `I i` is principal. -/
theorem relationLattice_eq_top_iff :
    relationLattice I = ⊤ ↔ ∀ i, (I i : Ideal R).IsPrincipal := by
  classical
  refine ⟨fun h i ↦ single_one_mem_relationLattice_iff.mp (h ▸ Submodule.mem_top), fun h ↦ ?_⟩
  refine eq_top_iff.mpr fun e _ ↦ mem_relationLattice_iff.mpr (Finset.prod_eq_one fun i _ ↦ ?_)
  rw [(ClassGroup.mk0_eq_one_iff (I i).2).mpr (h i), one_zpow]

/-- Over a ring with trivial class group, for instance a principal ideal domain, every exponent
vector is a relation. -/
theorem relationLattice_eq_top [Subsingleton (ClassGroup R)] : relationLattice I = ⊤ :=
  relationLattice_eq_top_iff.mpr fun i ↦
    (ClassGroup.mk0_eq_one_iff (I i).2).mp (Subsingleton.elim _ _)

/-- For an empty family of ideals, every exponent vector is a relation. -/
theorem relationLattice_of_isEmpty [IsEmpty ι] : relationLattice I = ⊤ :=
  relationLattice_eq_top_iff.mpr isEmptyElim

/-- The presentation map is surjective exactly when the classes `[I i]` generate the class
group. -/
theorem presentation_surjective_iff :
    Function.Surjective (presentation I) ↔
      Subgroup.closure (Set.range fun i ↦ ClassGroup.mk0 (I i)) = ⊤ := by
  simp only [Subgroup.eq_top_iff', Subgroup.mem_closure_range_iff_of_fintype]
  refine ⟨fun h c ↦ ?_, fun h c ↦ ?_⟩
  · obtain ⟨e, he⟩ := h (Additive.ofMul c)
    exact ⟨e, by rw [← toMul_presentation_apply, he, toMul_ofMul]⟩
  · obtain ⟨e, he⟩ := h c.toMul
    exact ⟨e, by rw [presentation_apply, ← he, ofMul_toMul]⟩

/-- If the classes `[I i]` generate the class group, the relation lattice has index the order of
the class group. -/
theorem index_relationLattice (hI : Function.Surjective (presentation I)) :
    (relationLattice I).toAddSubgroup.index = Nat.card (ClassGroup R) := by
  rw [relationLattice, LinearMap.ker_toAddSubgroup, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr hI,
    Nat.card_congr (AddSubgroup.topEquiv.toEquiv.trans Additive.toMul)]

end ClassGroup
