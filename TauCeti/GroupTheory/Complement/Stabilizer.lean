/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.CrossedProjection
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Crossed projections and orbit equivalences along point-stabilizer complements

When a subgroup `N` of `G` is complemented by a point stabilizer `MulAction.stabilizer G a` (with
no normality or commutativity assumption on `N`), the normal-factor projection
`Subgroup.IsComplement'.crossedProjection` sends `g` to the unique element `n ∈ N` such that
`n • a = g • a` (`Subgroup.IsComplement'.coe_crossedProjection_smul_of_stabilizer`,
`Subgroup.IsComplement'.crossedProjection_eq_iff_smul_eq`). When `N` is normal, the crossed
projections along translated point stabilizers transform equivariantly under conjugation
(`Subgroup.IsComplement'.crossedProjection_eq_smul_of_stabilizer`).

Evaluation at `a` injects `N` into `α`
(`Subgroup.IsComplement'.coe_smul_left_injective_of_stabilizer`), and when `G` acts transitively on
`α` it defines an equivalence `Subgroup.IsComplement'.stabilizerOrbitEquiv : N ≃ α` whose inverse
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
theorem coe_crossedProjection_smul_of_stabilizer (g : G) :
    (hs.crossedProjection g : G) • a = g • a := by
  obtain ⟨⟨n, d⟩, rfl⟩ := hs.surjective g
  rw [hs.crossedProjection_mul, mul_smul, MulAction.mem_stabilizer_iff.mp d.property]

/-- Along a point-stabilizer complement, `c g = n` holds exactly when `n` and `g` send the base
point to the same point. -/
theorem crossedProjection_eq_iff_smul_eq (g : G) (n : N) :
    hs.crossedProjection g = n ↔ (n : G) • a = g • a := by
  rw [hs.crossedProjection_eq_iff, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff,
    eq_comm]

include hs in
/-- If a point stabilizer complements `N`, the orbit map `n ↦ n • a` is injective on `N`. -/
theorem coe_smul_left_injective_of_stabilizer : Function.Injective (fun n : N => (n : G) • a) := by
  intro n₁ n₂ heq
  rw [← hs.crossedProjection_coe n₁, hs.crossedProjection_eq_iff_smul_eq]
  exact heq.symm

section Normal

variable [N.Normal]

attribute [local instance] Subgroup.conjugationAction

/-- Conjugation equivariance of crossed projections along point-stabilizer complements: the crossed
projection along `stabilizer G (g • a)` sends `x` to `g • c (g⁻¹ * x * g)`, where `c` is the
crossed projection along `stabilizer G a`. -/
theorem crossedProjection_eq_smul_of_stabilizer (g : G)
    (hs' : N.IsComplement' (MulAction.stabilizer G (g • a))) (x : G) :
    hs'.crossedProjection x = g • hs.crossedProjection (g⁻¹ * x * g) := by
  rw [← hs.crossedProjection_conj_smul, eq_comm, (hs.conj_smul g).crossedProjection_eq_iff,
    MulAction.conj_smul_stabilizer, ← hs'.crossedProjection_eq_iff]

end Normal

/-- In a transitive `G`-action, a subgroup `N` complemented by the stabilizer of `a` is in
bijection with `α` via the orbit map `n ↦ n • a`, with inverse determined on `g • a` by the
crossed projection `c g`. -/
noncomputable def stabilizerOrbitEquiv [MulAction.IsPretransitive G α] : N ≃ α where
  toFun n := (n : G) • a
  invFun b := hs.crossedProjection (Classical.choose (MulAction.exists_smul_eq G a b))
  left_inv n :=
    (hs.crossedProjection_eq_iff_smul_eq _ n).mpr
      (Classical.choose_spec (MulAction.exists_smul_eq G a ((n : G) • a))).symm
  right_inv b :=
    (hs.coe_crossedProjection_smul_of_stabilizer _).trans
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
  rw [Equiv.apply_symm_apply, stabilizerOrbitEquiv_apply,
    hs.coe_crossedProjection_smul_of_stabilizer]

/-- The inverse of the orbit equivalence sends the base point `a` to `1`. -/
@[simp]
theorem stabilizerOrbitEquiv_symm_self [MulAction.IsPretransitive G α] :
    hs.stabilizerOrbitEquiv.symm a = 1 := by
  simpa only [one_smul, crossedProjection_one] using hs.stabilizerOrbitEquiv_symm_smul (1 : G)

/-- Acting on the base point `a` by `hs.stabilizerOrbitEquiv.symm b` yields `b`. -/
@[simp]
theorem coe_stabilizerOrbitEquiv_symm_smul [MulAction.IsPretransitive G α] (b : α) :
    (hs.stabilizerOrbitEquiv.symm b : G) • a = b :=
  hs.stabilizerOrbitEquiv.apply_symm_apply b

end Subgroup.IsComplement'
