/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.SepClosedSubfield
public import TauCeti.GroupTheory.FixedSubgroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Finite fixed subgroups from Frobenius coordinates

Suppose a group has an injective system of finitely many coordinates in a field of characteristic
`p`. If an iterate of an endomorphism acts on all those coordinates by a positive power of
Frobenius, its fixed subgroup is finite: every coordinate of a fixed point lies in the finite
Frobenius-fixed subfield.

The coordinate criterion does not require the coordinates to respect multiplication. Its matrix
representation and matrix subgroup specializations apply to Steinberg endomorphisms once their
Frobenius iterate has been identified on the entire ambient group.

## Main results

* `TauCeti.finite_fixedSubgroup_of_frobenius_coordinates`: the finite-coordinate criterion.
* `TauCeti.finite_fixedSubgroup_of_frobenius_representation`: its faithful matrix representation
  form.
* `TauCeti.finite_fixedSubgroup_of_frobenius_matrix_subgroup`: its matrix subgroup form.

The field exponent must be nonzero. The iterate may be zero: in that case the hypothesis already
places every element of the ambient group in finitely many finite-field coordinates.
-/

public section

namespace TauCeti

variable {G K ι : Type*} [Group G] [Field K] [Finite ι]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- A fixed subgroup is finite if an iterate acts by a nontrivial field Frobenius on an injective
system of finitely many coordinates. The coordinate equation is required on the whole group. -/
theorem finite_fixedSubgroup_of_frobenius_coordinates (F : Monoid.End G)
    (c : G → ι → K) (hc : Function.Injective c) (e r : ℕ) (he : e ≠ 0)
    (hF : ∀ g i, c ((F ^ r) g) i = c g i ^ p ^ e) :
    Finite ↥(fixedSubgroup F) := by
  have := finite_frobeniusFixedSubfield K p e he
  let c₀ : fixedSubgroup F → ι → frobeniusFixedSubfield K p e := fun g i =>
    ⟨c g i, by
      rw [mem_frobeniusFixedSubfield]
      have hg := mem_fixedSubgroup.mp (fixedSubgroup_le_fixedSubgroup_pow F r g.property)
      exact (hF g i).symm.trans (congrArg (fun x => c x i) hg)⟩
  refine Finite.of_injective c₀ fun g h hgh => Subtype.ext (hc ?_)
  exact funext fun i => congrArg Subtype.val (congrFun hgh i)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A faithful finite-dimensional matrix representation detects finiteness of the fixed subgroup
when an iterate of the endomorphism acts entrywise by a nontrivial Frobenius. -/
theorem finite_fixedSubgroup_of_frobenius_representation (F : Monoid.End G)
    (ρ : G →* Matrix.GeneralLinearGroup n K) (hρ : Function.Injective ρ)
    (e r : ℕ) (he : e ≠ 0)
    (hF : ∀ g i j, ρ ((F ^ r) g) i j = ρ g i j ^ p ^ e) :
    Finite ↥(fixedSubgroup F) := by
  refine finite_fixedSubgroup_of_frobenius_coordinates p F
    (fun g (ij : n × n) => ρ g ij.1 ij.2) ?_ e r he (fun g ij => hF g ij.1 ij.2)
  intro g h hgh
  apply hρ
  apply Units.ext
  exact Matrix.ext fun i j => congrFun hgh (i, j)

/-- A matrix subgroup has finitely many fixed points when an iterate of its endomorphism is
entrywise Frobenius with nonzero field exponent. -/
theorem finite_fixedSubgroup_of_frobenius_matrix_subgroup
    (S : Subgroup (Matrix.GeneralLinearGroup n K)) (F : Monoid.End S)
    (e r : ℕ) (he : e ≠ 0)
    (hF : ∀ g i j, ((F ^ r) g : Matrix.GeneralLinearGroup n K) i j =
      (g : Matrix.GeneralLinearGroup n K) i j ^ p ^ e) :
    Finite ↥(fixedSubgroup F) :=
  finite_fixedSubgroup_of_frobenius_representation p F S.subtype Subtype.coe_injective e r he hF

end TauCeti
