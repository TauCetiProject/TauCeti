/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.CyclicQuotient
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The closed-path trace on a path algebra

Let `Q` be a quiver and `k` a semiring. Summing the coefficients of all closed basis paths defines a
`k`-linear functional `TauCeti.PathAlgebra.closedPathTrace : kQ →ₗ[k] k` sending `ofPath ⟨a, b, p⟩`
to `1` when `a = b` and to `0` when `a ≠ b`.

For two basis paths `x : c ⟶ d` and `y : a ⟶ b`, the product `ofPath x * ofPath y` (concatenating
in later-factor-first order) is a closed path exactly when `b = c` and `a = d`, a condition
symmetric in `x` and `y`. Over a commutative semiring, `closedPathTrace` is therefore invariant
under exchanging the factors of a product, and over a commutative ring it vanishes on the commutator
submodule `[kQ, kQ]` (`TauCeti.commutatorSubmodule`).

Together with the commutator identity `e_b * p - p * e_b = p` for paths `p : a ⟶ b` with `a ≠ b`,
this characterizes the basis paths lying in `[kQ, kQ]` over a nontrivial commutative ring: a basis
path is a sum of commutators if and only if its endpoints are distinct
(`TauCeti.PathAlgebra.ofPath_mem_commutatorSubmodule_iff`). In particular, no closed path in `kQ`
is a sum of commutators.

## Main definitions

* `TauCeti.PathAlgebra.closedPathTrace`: the linear functional summing the coefficients of all
  closed paths.
* `TauCeti.PathAlgebra.closedPathTraceCyclicQuotient`: its descent to `kQ / [kQ, kQ]`.

## Main results

* `TauCeti.PathAlgebra.closedPathTrace_mul_comm`: invariance under cyclic permutation,
  `closedPathTrace (x * y) = closedPathTrace (y * x)`.
* `TauCeti.PathAlgebra.ofPath_notMem_commutatorSubmodule` and
  `TauCeti.PathAlgebra.ofPath_mem_commutatorSubmodule_iff`: **a basis path of `kQ` lies in
  `[kQ, kQ]` over a nontrivial commutative ring if and only if it is not closed.**

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1 and Theorem 3.1.6, for the cyclic quotient
  `HH₀(kQ) = kQ / [kQ, kQ]` of a path algebra as the free module on cyclic equivalence classes of
  closed paths.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver

universe u v w

section Semiring

variable (k : Type w) [Semiring k] (Q : Type u) [Quiver.{v} Q]

open scoped Classical in
/-- The `k`-linear functional on `kQ` summing the coefficients of all closed paths: it sends every
closed basis path to `1` and every path with distinct endpoints to `0`. -/
noncomputable def closedPathTrace : pathAlgebra k Q →ₗ[k] k :=
  liftLinear k fun x => if x.1 = x.2.1 then 1 else 0

variable {k Q}

/-- Every closed basis path has `closedPathTrace` equal to `1`. -/
@[simp]
theorem closedPathTrace_ofPath_self (a : Q) (p : Quiver.Path a a) :
    closedPathTrace k Q (ofPath ⟨a, a, p⟩) = 1 := by
  classical
  simp [closedPathTrace]

/-- Every basis path between distinct vertices has `closedPathTrace` equal to `0`. -/
@[simp]
theorem closedPathTrace_ofPath_of_ne {a b : Q} (p : Quiver.Path a b) (h : a ≠ b) :
    closedPathTrace k Q (ofPath ⟨a, b, p⟩) = 0 := by
  classical
  simp [closedPathTrace, h]

/-- Every vertex idempotent has `closedPathTrace` equal to `1`. -/
@[simp]
theorem closedPathTrace_vertexIdempotent (a : Q) :
    closedPathTrace k Q (vertexIdempotent k a) = 1 := by
  rw [vertexIdempotent_eq_ofPath, closedPathTrace_ofPath_self]

private theorem closedPathTrace_ofPath_mul_ofPath_comm (x y : TauCeti.Quiver.TotalPath Q) :
    closedPathTrace k Q (ofPath x * ofPath y) = closedPathTrace k Q (ofPath y * ofPath x) := by
  obtain ⟨c, d, q⟩ := x
  obtain ⟨a, b, p⟩ := y
  rcases eq_or_ne b c with rfl | hbc
  · rcases eq_or_ne d a with rfl | hda
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp,
        closedPathTrace_ofPath_self, closedPathTrace_ofPath_self]
    · rw [ofPath_mul_ofPath_of_comp, closedPathTrace_ofPath_of_ne _ hda.symm,
        ofPath_mul_ofPath_of_not_composable hda, map_zero]
  · rw [ofPath_mul_ofPath_of_not_composable hbc, map_zero]
    rcases eq_or_ne d a with rfl | hda
    · rw [ofPath_mul_ofPath_of_comp, closedPathTrace_ofPath_of_ne _ hbc.symm]
    · rw [ofPath_mul_ofPath_of_not_composable hda, map_zero]

end Semiring

section CommSemiring

variable {k : Type w} [CommSemiring k] {Q : Type u} [Quiver.{v} Q]

/-- **The closed-path trace is invariant under cyclic permutation**: it takes equal values on
`x * y` and `y * x`. -/
theorem closedPathTrace_mul_comm (x y : pathAlgebra k Q) :
    closedPathTrace k Q (x * y) = closedPathTrace k Q (y * x) := by
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ => rw [add_mul, mul_add, map_add, map_add, hx₁, hx₂]
  | single x r =>
    induction y using induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ => rw [mul_add, add_mul, map_add, map_add, hy₁, hy₂]
    | single y s =>
      rw [single_eq_smul_ofPath, single_eq_smul_ofPath, smul_mul_smul_comm, smul_mul_smul_comm,
        map_smul, map_smul, closedPathTrace_ofPath_mul_ofPath_comm, mul_comm r s]

end CommSemiring

section Ring

variable {k : Type w} [Ring k] {Q : Type u} [Quiver.{v} Q]

/-- A path between distinct vertices is the commutator `e_b * p - p * e_b` with its target vertex
idempotent, so it lies in the commutator submodule `[kQ, kQ]`. -/
theorem ofPath_mem_commutatorSubmodule_of_ne {a b : Q} (p : Quiver.Path a b) (hab : a ≠ b) :
    ofPath (k := k) ⟨a, b, p⟩ ∈ commutatorSubmodule k (pathAlgebra k Q) := by
  have hcomm := mul_sub_mul_mem_commutatorSubmodule k (pathAlgebra k Q)
    (vertexIdempotent k b) (ofPath ⟨a, b, p⟩)
  rwa [vertexIdempotent_mul_ofPath, ofPath_mul_vertexIdempotent_of_ne _ hab.symm,
    sub_zero] at hcomm

end Ring

section CommRing

variable (k : Type w) [CommRing k] (Q : Type u) [Quiver.{v} Q]

/-- The closed-path trace vanishes on the commutator submodule `[kQ, kQ]`. -/
theorem commutatorSubmodule_le_ker_closedPathTrace :
    commutatorSubmodule k (pathAlgebra k Q) ≤ LinearMap.ker (closedPathTrace k Q) :=
  (commutatorSubmodule_le_ker_iff (closedPathTrace k Q)).2 closedPathTrace_mul_comm

/-- The closed-path trace descended to the cyclic quotient `kQ / [kQ, kQ]`. -/
noncomputable def closedPathTraceCyclicQuotient :
    cyclicQuotient k (pathAlgebra k Q) →ₗ[k] k :=
  (commutatorSubmodule k (pathAlgebra k Q)).liftQ (closedPathTrace k Q)
    (commutatorSubmodule_le_ker_closedPathTrace k Q)

variable {k Q}

/-- On the cyclic class of `x`, `closedPathTraceCyclicQuotient` evaluates `closedPathTrace`. -/
@[simp]
theorem closedPathTraceCyclicQuotient_mk (x : pathAlgebra k Q) :
    closedPathTraceCyclicQuotient k Q (Submodule.Quotient.mk x) = closedPathTrace k Q x :=
  (rfl)

/-- **No closed path in `kQ` is a sum of commutators** over a nontrivial commutative ring. -/
theorem ofPath_notMem_commutatorSubmodule [Nontrivial k] (a : Q) (p : Quiver.Path a a) :
    ofPath (k := k) ⟨a, a, p⟩ ∉ commutatorSubmodule k (pathAlgebra k Q) := by
  intro h
  have h0 := LinearMap.mem_ker.mp (commutatorSubmodule_le_ker_closedPathTrace k Q h)
  rw [closedPathTrace_ofPath_self] at h0
  exact one_ne_zero h0

/-- **A basis path of `kQ` lies in the commutator submodule `[kQ, kQ]` over a nontrivial
commutative ring if and only if its endpoints are distinct.** -/
@[simp]
theorem ofPath_mem_commutatorSubmodule_iff [Nontrivial k] {a b : Q} (p : Quiver.Path a b) :
    ofPath (k := k) ⟨a, b, p⟩ ∈ commutatorSubmodule k (pathAlgebra k Q) ↔ a ≠ b := by
  rcases eq_or_ne a b with rfl | hab
  · exact iff_of_false (ofPath_notMem_commutatorSubmodule a p) (not_not.mpr rfl)
  · exact iff_of_true (ofPath_mem_commutatorSubmodule_of_ne p hab) hab

end CommRing

end TauCeti.PathAlgebra
