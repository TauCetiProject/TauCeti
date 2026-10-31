/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.PermutationForm
public import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Basic

/-!
# The tabloid form on a Young permutation module

The Young permutation module `M^μ` has a basis indexed by the `μ`-tabloids, and the bilinear form
declaring that basis orthonormal is the **tabloid form**.  It is the specialisation to `M^μ` of the
invariant form on a permutation representation. Over every commutative ring it is symmetric and
  preserved
by the symmetric group. The rational specialization is positive definite, so the orthogonal
complement of a rational subrepresentation of `M^μ` is a complement.

This file names the form, reads it on the tabloid basis and on coset representatives, and records
the two statements that the theory of Specht modules uses: invariance under the symmetric group and
complementation.  The orthogonality relation itself is the tool behind James's submodule theorem,
which compares a submodule of `M^μ` with the orthogonal complement of the Specht module inside it.

## Main definitions

* `TauCeti.tabloidForm`: the tabloid form on `M^μ`.

## Main results

* `TauCeti.tabloidForm_basis_basis`: the tabloid basis is orthonormal.
* `TauCeti.tabloidForm_single_coe_single_coe_of_mem` and
  `TauCeti.tabloidForm_single_coe_single_coe_of_notMem`: two tabloids given by permutations pair to
  `1` or to `0` according to whether the permutations differ by an element of the Young subgroup.
* `TauCeti.tabloidForm_invariant`: the symmetric group acts on `M^μ` by isometries of the tabloid
  form.
* `TauCeti.isCompl_orthogonalSubrepresentation_permutationModule`: a subrepresentation of `M^μ` is
  complemented by its orthogonal complement.

## References

* G. D. James, *The Representation Theory of the Symmetric Groups*, Chapter 1, where the form is
  introduced by declaring the tabloids orthonormal, and Chapter 4 for the submodule theorem.
* [Schur-Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 3, "The submodule theorem (James)", which asks for the tabloid bilinear form as an API in
  its own right.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

open LinearMap (BilinForm)

variable {n : ℕ} (μ : n.Partition)

/-- The **tabloid form** on the Young permutation module `M^μ`: the bilinear form for which the
tabloid basis is orthonormal. -/
noncomputable abbrev tabloidForm :
    BilinForm R (MonoidAlgebra R (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) :=
  permutationForm R (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)

/-- The tabloid basis of `M^μ` is orthonormal for the tabloid form. -/
theorem tabloidForm_basis_basis (i j : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) [Decidable (i = j)] :
    tabloidForm (R := R) μ (permutationModuleBasis (R := R) μ i) (permutationModuleBasis (R :=
      R) μ j) =
      if i = j then 1 else 0 := by
  simpa using permutationForm_single_single i j (1 : R) 1

/-- Two permutations describe the same `μ`-tabloid exactly when they differ by an element of the
Young subgroup, and then the corresponding basis vectors pair to `1`. -/
theorem tabloidForm_single_coe_single_coe_of_mem {g h : Equiv.Perm (Fin n)}
    (hgh : g⁻¹ * h ∈ youngSubgroup μ) :
    tabloidForm (R := R) μ (MonoidAlgebra.single (g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1)
        (MonoidAlgebra.single (h : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1) = 1 := by
  classical
  rw [permutationForm_single_single, ite_eq_left (QuotientGroup.eq.mpr hgh), mul_one]

/-- Permutations lying in different cosets of the Young subgroup describe distinct `μ`-tabloids, so
the corresponding basis vectors pair to `0`. -/
theorem tabloidForm_single_coe_single_coe_of_notMem {g h : Equiv.Perm (Fin n)}
    (hgh : g⁻¹ * h ∉ youngSubgroup μ) :
    tabloidForm (R := R) μ (MonoidAlgebra.single (g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1)
        (MonoidAlgebra.single (h : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) 1) = 0 := by
  classical
  rw [permutationForm_single_single, ite_eq_right fun hq => hgh (QuotientGroup.eq.mp hq)]

/-- The symmetric group acts on `M^μ` by isometries of the tabloid form: it permutes the tabloid
basis. -/
theorem tabloidForm_invariant (σ : Equiv.Perm (Fin n))
    (v w : MonoidAlgebra R (Equiv.Perm (Fin n) ⧸ youngSubgroup μ)) :
    tabloidForm (R := R) μ ((permutationModule (R := R) μ).ρ σ v) ((permutationModule (R := R)
      μ).ρ σ w) =
      tabloidForm (R := R) μ v w :=
  permutationForm_ofMulAction_invariant σ v w

/-- **Invariant orthogonal complements in `M^μ`.**  A subrepresentation of the Young permutation
module is complemented by its orthogonal complement for the tabloid form.  Unlike the complement
produced by Maschke's theorem, this one is canonical: it is cut out by an explicit pairing. -/
theorem isCompl_orthogonalSubrepresentation_permutationModule
    (σ : Subrepresentation (permutationModule (R := ℚ) μ).ρ) :
    IsCompl σ (orthogonalSubrepresentation σ) :=
  isCompl_orthogonalSubrepresentation σ

end TauCeti
