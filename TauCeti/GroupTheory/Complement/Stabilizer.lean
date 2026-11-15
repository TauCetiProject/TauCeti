/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.CrossedProjection

/-!
# Crossed projections and orbit equivalences along point-stabilizer complements

When a subgroup `N` of `G` is complemented by a point stabilizer `MulAction.stabilizer G a` (with
no normality or commutativity assumption on `N`), the normal-factor projection
`Subgroup.IsComplement'.crossedProjection` sends `g` to the unique element `n ∈ N` such that
`n • a = g • a` (`Subgroup.IsComplement'.crossedProjection_stabilizer_smul`,
`Subgroup.IsComplement'.crossedProjection_stabilizer_eq_iff`).

Evaluation at `a` therefore injects `N` into `α`
(`Subgroup.IsComplement'.smul_stabilizer_injective`), and when `G` acts transitively on `α` it
defines an equivalence `Subgroup.IsComplement'.stabilizerOrbitEquiv : N ≃ α` whose inverse
recovers the crossed projection along orbits
(`Subgroup.IsComplement'.stabilizerOrbitEquiv_symm_smul`).
-/

public section

namespace Subgroup.IsComplement'

variable {G α : Type*} [Group G] [MulAction G α] {N : Subgroup G} {a : α}
  (hs : N.IsComplement' (MulAction.stabilizer G a))

/-- Along a point-stabilizer complement, the crossed projection of `g` acts on the base point in
the same way as `g`. -/
@[simp]
theorem crossedProjection_stabilizer_smul (g : G) :
    (hs.crossedProjection g : G) • a = g • a := by
  obtain ⟨⟨n, d⟩, rfl⟩ := hs.surjective g
  rw [hs.crossedProjection_mul, mul_smul, MulAction.mem_stabilizer_iff.mp d.property]

/-- Along a point-stabilizer complement, `c g = n` holds exactly when `n` and `g` send the base
point to the same point. -/
theorem crossedProjection_stabilizer_eq_iff (g : G) (n : N) :
    hs.crossedProjection g = n ↔ (n : G) • a = g • a := by
  rw [hs.crossedProjection_eq_iff, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff,
    eq_comm]

include hs in
/-- If a point stabilizer complements `N`, the orbit map `n ↦ n • a` is injective on `N`. -/
theorem smul_stabilizer_injective : Function.Injective (fun n : N => (n : G) • a) := by
  intro n₁ n₂ heq
  rw [← hs.crossedProjection_coe n₁, hs.crossedProjection_stabilizer_eq_iff]
  exact heq.symm

/-- In a transitive `G`-action, a subgroup `N` complemented by the stabilizer of `a` is in
bijection with `α` via the orbit map `n ↦ n • a`, with inverse determined on `g • a` by the
crossed projection `c g`. -/
noncomputable def stabilizerOrbitEquiv [MulAction.IsPretransitive G α] : N ≃ α where
  toFun n := (n : G) • a
  invFun b := hs.crossedProjection (Classical.choose (MulAction.exists_smul_eq G a b))
  left_inv n :=
    (hs.crossedProjection_stabilizer_eq_iff _ n).mpr
      (Classical.choose_spec (MulAction.exists_smul_eq G a ((n : G) • a))).symm
  right_inv b :=
    (hs.crossedProjection_stabilizer_smul _).trans
      (Classical.choose_spec (MulAction.exists_smul_eq G a b))

/-- The orbit equivalence of a point-stabilizer complement evaluates an element of `N` at the
base point. -/
@[simp]
theorem stabilizerOrbitEquiv_apply [MulAction.IsPretransitive G α] (n : N) :
    hs.stabilizerOrbitEquiv n = (n : G) • a :=
  (rfl)

/-- The inverse of the orbit equivalence sends `g • a` to the crossed projection of `g`. -/
@[simp]
theorem stabilizerOrbitEquiv_symm_smul [MulAction.IsPretransitive G α] (g : G) :
    hs.stabilizerOrbitEquiv.symm (g • a) = hs.crossedProjection g := by
  apply hs.stabilizerOrbitEquiv.injective
  rw [Equiv.apply_symm_apply, stabilizerOrbitEquiv_apply, hs.crossedProjection_stabilizer_smul]

end Subgroup.IsComplement'
