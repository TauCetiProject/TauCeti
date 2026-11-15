/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.Complement.CrossedProjection

/-!
# Point-stabilizer conjugation and crossed projections

Pointwise conjugation `MulAut.conj g • MulAction.stabilizer G a` identifies the conjugate of a
point stabilizer with `MulAction.stabilizer G (g • a)` (`MulAction.conj_smul_stabilizer`), so any
point stabilizer is self-normalizing when distinct points have distinct stabilizers
(`MulAction.normalizer_stabilizer_of_injective`).

For any subgroup `N` of `G` and complement `D` of `N` (with no normality or commutativity
assumption), the normal-factor projection `Subgroup.IsComplement'.crossedProjection`
satisfies `c (n * g) = n * c g` for `n ∈ N`, `c (g * d) = c g` for `d ∈ D`, and
`c g = n ↔ n⁻¹ * g ∈ D`.

When `D` is `MulAction.stabilizer G a`, `c g` is the unique element `n ∈ N` such that
`n • a = g • a`. Evaluation at `a` therefore injects `N` into `α`, and when `G` acts
transitively on `α` it defines an equivalence
`Subgroup.IsComplement'.stabilizerOrbitEquiv : N ≃ α` whose inverse recovers the crossed
projection on orbits: `e⁻¹ (g • a) = c g`.
-/

public section

open scoped Pointwise

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

/-- Pointwise conjugation of a point stabilizer moves the stabilized point by the conjugating
element. -/
@[simp]
theorem conj_smul_stabilizer (g : G) (a : α) :
    MulAut.conj g • stabilizer G a = stabilizer G (g • a) :=
  (TauCeti.map_conj_eq_conj_smul g _).symm.trans (stabilizer_smul_eq_stabilizer_map_conj g a).symm

/-- When distinct points have distinct stabilizers, every point stabilizer is self-normalizing. -/
theorem normalizer_stabilizer_of_injective
    (h : Function.Injective (stabilizer G : α → Subgroup G)) (a : α) :
    Subgroup.normalizer (stabilizer G a : Set G) = stabilizer G a := by
  ext g
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
    ← stabilizer_smul_eq_stabilizer_map_conj, h.eq_iff, mem_stabilizer_iff]

end MulAction

namespace Subgroup.IsComplement'

variable {G : Type*} [Group G] {N : Subgroup G}

section General

variable {D : Subgroup G} (h : N.IsComplement' D)

/-- The crossed projection sends `1` to `1`. -/
@[simp]
theorem crossedProjection_one : h.crossedProjection 1 = 1 := by
  simpa only [OneMemClass.coe_one] using h.crossedProjection_coe 1

/-- Left multiplication by an element of `N` multiplies the crossed projection on the left. -/
@[simp]
theorem crossedProjection_mul_left (n : N) (g : G) :
    h.crossedProjection ((n : G) * g) = n * h.crossedProjection g := by
  obtain ⟨⟨m, d⟩, rfl⟩ := h.surjective g
  have hmul : (n : G) * ((m : G) * d) = ((n * m : N) : G) * d := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hmul, h.crossedProjection_mul, h.crossedProjection_mul]

/-- Right multiplication by an element of the complement leaves the crossed projection
unchanged. -/
@[simp]
theorem crossedProjection_mul_right (g : G) (d : D) :
    h.crossedProjection (g * d) = h.crossedProjection g := by
  obtain ⟨⟨n, d'⟩, rfl⟩ := h.surjective g
  have hmul : (n : G) * d' * d = (n : G) * ((d' * d : D) : G) := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hmul, h.crossedProjection_mul, h.crossedProjection_mul]

/-- The crossed projection of `g` equals `n` if and only if `n⁻¹ * g` lies in the complement. -/
theorem crossedProjection_eq_iff (g : G) (n : N) :
    h.crossedProjection g = n ↔ (n : G)⁻¹ * g ∈ D := by
  rw [eq_comm, ← inv_mul_eq_one, ← h.crossedProjection_mul_left n⁻¹ g, Subgroup.coe_inv,
    h.crossedProjection_eq_one_iff]

end General

section Stabilizer

variable {α : Type*} [MulAction G α] {a : α}
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

end Stabilizer

end Subgroup.IsComplement'
