/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Orbits of a family of transitive actions

For a componentwise action on a sigma type with nonempty transitive fibres, the orbit space
is the indexing type. This identifies the orbit factors in permutation-module calculations.
-/

public noncomputable section

namespace TauCeti

open MulAction

variable {G ι : Type*} {X : ι → Type*} [Group G] [∀ i, MulAction G (X i)]

/-- The stabilizer of a point in a sigma type is its stabilizer in its fibre. -/
@[simp]
theorem MulAction.stabilizer_sigma_mk (i : ι) (x : X i) :
    stabilizer G (Sigma.mk i x) = stabilizer G x := by
  ext g
  simp

variable [∀ i, IsPretransitive G (X i)] [∀ i, Nonempty (X i)]

/-- The orbits of a componentwise action with nonempty transitive fibres are indexed by
the fibres. -/
def MulAction.orbitRelQuotientSigmaEquiv : orbitRel.Quotient G (Σ i, X i) ≃ ι where
  toFun := Quotient.lift Sigma.fst fun a b ⟨g, hg⟩ ↦ by
    cases b
    simpa using congrArg Sigma.fst hg.symm
  invFun i := Quotient.mk'' (Sigma.mk i (Classical.arbitrary (X i)))
  left_inv := by
    rintro ⟨i, x⟩
    obtain ⟨g, hg⟩ := exists_smul_eq G x (Classical.arbitrary (X i))
    exact Quotient.sound ⟨g, by simp [hg]⟩
  right_inv _ := rfl

/-- The orbit of a point is sent to the index of its fibre. -/
@[simp]
theorem MulAction.orbitRelQuotientSigmaEquiv_mk (x : Σ i, X i) :
    orbitRelQuotientSigmaEquiv (Quotient.mk'' x : orbitRel.Quotient G (Σ i, X i)) = x.1 :=
  (rfl)

-- Not a simp lemma: the fibre point on the right is not determined by the left-hand side.
/-- The inverse sends a fibre index to the orbit of any point in that fibre. -/
theorem MulAction.orbitRelQuotientSigmaEquiv_symm_apply (i : ι) (x : X i) :
    (orbitRelQuotientSigmaEquiv (G := G) (X := X)).symm i = Quotient.mk'' (Sigma.mk i x) := by
  apply (orbitRelQuotientSigmaEquiv (G := G) (X := X)).injective
  simp

end TauCeti
