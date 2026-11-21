/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Invariant.Basic
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Sharpness of the invariant-complement theorem on the Klein four-group

`Subgroup.exists_invariant_complement` says: if a finite `q`-group `A` acts on a finite group `W`
by automorphisms, `N` is an abelian normal `p`-subgroup of `W` stable under `A`, `p ≠ q`, and `N`
has a local complement in a Sylow `p`-subgroup of `W`, then `N` has an `A`-stable complement in
`W`. This file shows on the Klein four-group that neither the hypothesis `p ≠ q` nor the
`A`-stability of `N` can be dropped.

The Klein four-group is modelled as `KleinFour = Multiplicative (ZMod 2 × ZMod 2)`, with the
basis vectors `e₁ = ofAdd (1, 0)` and `e₂ = ofAdd (0, 1)`. Take `N = ⟨e₁⟩`; since `KleinFour` is
a `2`-group, its only Sylow `2`-subgroup is `⊤`, and the complements of `N` are exactly `⟨e₂⟩`
and `⟨e₁ * e₂⟩` (`TauCeti.Examples.InvariantSharpness.isComplement'_zpowers_e₁_iff`).

* **`p = q`.** The transvection `e₁ ↦ e₁`, `e₂ ↦ e₁ * e₂` generates a group `A` of order `2`
  stabilizing `N`, and swaps the two complements of `N`. Every hypothesis of the theorem except
  `p ≠ q` holds for `p = q = 2`, yet no complement of `N` is `A`-stable
  (`TauCeti.Examples.InvariantSharpness.not_forall_exists_invariant_complement_of_eq`).
* **`A`-stability of `N`.** The automorphism of order `3` permuting `e₁ ↦ e₂ ↦ e₁ * e₂ ↦ e₁`
  generates a `3`-group `A`. Every hypothesis of the theorem except the `A`-stability of `N` holds
  for `p = 2` and `q = 3`, yet no complement of `N` is `A`-stable: `A` permutes the three
  non-trivial elements, and hence the three subgroups of order `2`, cyclically
  (`TauCeti.Examples.InvariantSharpness.not_forall_exists_invariant_complement_of_not_stable`).

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
-/

public section

open Multiplicative Subgroup

namespace TauCeti.Examples.InvariantSharpness

/-! ### The Klein four-group and the complements of `⟨e₁⟩` -/

/-- The Klein four-group, modelled as the multiplicative group of `(ZMod 2)²`. -/
abbrev KleinFour : Type := Multiplicative (ZMod 2 × ZMod 2)

/-- The first basis vector `ofAdd (1, 0)` of `KleinFour`. -/
def e₁ : KleinFour := ofAdd (1, 0)

/-- The second basis vector `ofAdd (0, 1)` of `KleinFour`. -/
def e₂ : KleinFour := ofAdd (0, 1)

/-- Every element of `KleinFour` squares to `1`. -/
private theorem sq_eq_one_of_kleinFour (d : KleinFour) : d ^ 2 = 1 := by
  revert d
  decide

/-- `KleinFour` is a `2`-group. -/
theorem isPGroup_kleinFour : IsPGroup 2 KleinFour :=
  IsPGroup.of_card (n := 2) (by simp [Nat.card_eq_fintype_card])

/-- If `d ∈ {e₂, e₁ * e₂}`, then `⟨d⟩` is a complement of `⟨e₁⟩`. -/
private theorem isComplement'_zpowers_e₁_zpowers {d : KleinFour} (hd : d = e₂ ∨ d = e₁ * e₂) :
    (zpowers e₁).IsComplement' (zpowers d) := by
  refine isComplement'_of_disjoint_and_mul_eq_univ (disjoint_def.mpr fun {w} h₁ h₂ => ?_)
    (Set.eq_univ_iff_forall.mpr fun w => Set.mem_mul.mpr ?_)
  · rw [mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)] at h₁ h₂
    revert w d
    decide
  · simp only [SetLike.mem_coe, mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)]
    revert w d
    decide

/-- The complements of `⟨e₁⟩` in `KleinFour` are exactly `⟨e₂⟩` and `⟨e₁ * e₂⟩`. -/
theorem isComplement'_zpowers_e₁_iff {D : Subgroup KleinFour} :
    (zpowers e₁).IsComplement' D ↔ D = zpowers e₂ ∨ D = zpowers (e₁ * e₂) := by
  constructor
  · intro h
    have hdisj : ∀ w ∈ D, w = 1 ∨ w = e₁ → w = 1 := fun w hwD hwN =>
      disjoint_def.mp h.disjoint
        ((mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)).mpr hwN) hwD
    obtain ⟨⟨⟨n, hn⟩, ⟨d, hdD⟩⟩, hnd, -⟩ := h.existsUnique e₂
    rw [SetLike.mem_coe, mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)] at hn
    rw [SetLike.mem_coe] at hdD
    have hd : d = e₂ ∨ d = e₁ * e₂ := by
      have key : ∀ n d : KleinFour, n = 1 ∨ n = e₁ → n * d = e₂ → d = e₂ ∨ d = e₁ * e₂ := by
        decide
      exact key n d hn hnd
    have hD : D = zpowers d := by
      refine le_antisymm (fun w hw => ?_) (zpowers_le.mpr hdD)
      rw [mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)]
      -- An element of `D` outside `{1, d}` would give a nontrivial element of `⟨e₁⟩` in `D`.
      have key : ∀ w d : KleinFour, d = e₂ ∨ d = e₁ * e₂ → (w = 1 ∨ w = d) ∨
          (w ≠ 1 ∧ (w = 1 ∨ w = e₁)) ∨ (w * d ≠ 1 ∧ (w * d = 1 ∨ w * d = e₁)) := by
        decide
      rcases key w d hd with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact h
      · exact absurd (hdisj w hw h₂) h₁
      · exact absurd (hdisj _ (D.mul_mem hw hdD) h₂) h₁
    rcases hd with rfl | rfl
    exacts [Or.inl hD, Or.inr hD]
  · rintro (rfl | rfl)
    exacts [isComplement'_zpowers_e₁_zpowers (Or.inl rfl),
      isComplement'_zpowers_e₁_zpowers (Or.inr rfl)]

/-- `⟨e₂⟩` is a local complement of `⟨e₁⟩` in every Sylow `2`-subgroup of `KleinFour`. -/
theorem isLocalComplement_zpowers_e₁_sylow {P : Sylow 2 KleinFour} :
    (zpowers e₁).IsLocalComplement (zpowers e₂) P := by
  -- The `2`-group `KleinFour` is its own unique Sylow `2`-subgroup.
  rw [P.maximal_isPGroup.eq_of_le (isPGroup_kleinFour.to_subgroup ⊤) le_top,
    isLocalComplement_top_iff, isComplement'_zpowers_e₁_iff]
  exact Or.inl rfl

/-- A complement of `⟨e₁⟩` is stable under no automorphism moving both `e₂` and `e₁ * e₂`. -/
private theorem not_exists_isComplement'_and_forall_apply_mem (f : MulAut KleinFour)
    (h₂ : f e₂ ≠ e₂) (h₁₂ : f (e₁ * e₂) ≠ e₁ * e₂) :
    ¬ ∃ D : Subgroup KleinFour, (zpowers e₁).IsComplement' D ∧ ∀ d ∈ D, f d ∈ D := by
  rintro ⟨D, hD, hf⟩
  have hne (d : KleinFour) (hd : d ≠ 1) (hfd : f d ≠ d) (hmem : f d ∈ zpowers d) : False := by
    rcases (mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)).mp hmem with h | h
    · exact hd ((map_eq_one_iff f f.injective).mp h)
    · exact hfd h
  rcases isComplement'_zpowers_e₁_iff.mp hD with rfl | rfl
  · exact hne e₂ (by decide) h₂ (hf _ (mem_zpowers _))
  · exact hne _ (by decide) h₁₂ (hf _ (mem_zpowers _))

/-! ### The hypothesis `p ≠ q` is needed -/

/-- The transvection `e₁ ↦ e₁`, `e₂ ↦ e₁ * e₂` of `KleinFour`, an automorphism of order `2`. -/
def transvection : MulAut KleinFour where
  toFun w := ofAdd ((toAdd w).1 + (toAdd w).2, (toAdd w).2)
  invFun w := ofAdd ((toAdd w).1 + (toAdd w).2, (toAdd w).2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

@[simp]
theorem transvection_apply (w : KleinFour) :
    transvection w = ofAdd ((toAdd w).1 + (toAdd w).2, (toAdd w).2) :=
  (rfl)

-- High priority: these basis normal forms must fire before the coordinate expansion
-- `transvection_apply`, so that `simp` keeps the named basis elements.
@[simp high]
theorem transvection_e₁ : transvection e₁ = e₁ := by decide

@[simp high]
theorem transvection_e₂ : transvection e₂ = e₁ * e₂ := by decide

@[simp high]
theorem transvection_e₁_mul_e₂ : transvection (e₁ * e₂) = e₂ := by decide

theorem orderOf_transvection : orderOf transvection = 2 := by
  refine orderOf_eq_prime (MulEquiv.ext fun w => ?_) fun h => ?_
  · simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    revert w
    decide
  · have h₂ := congrArg (· e₂) h
    simp only [MulAut.one_apply, transvection_e₂] at h₂
    exact absurd h₂ (by decide)

theorem isPGroup_zpowers_transvection : IsPGroup 2 (zpowers transvection) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_transvection, pow_one])

/-- The transvection carries the complement `⟨e₂⟩` of `⟨e₁⟩` to the other complement
`⟨e₁ * e₂⟩`. -/
theorem map_transvection_zpowers_e₂ :
    (zpowers e₂).map transvection.toMonoidHom = zpowers (e₁ * e₂) := by
  rw [MonoidHom.map_zpowers]
  exact congrArg zpowers transvection_e₂

/-- The transvection carries the complement `⟨e₁ * e₂⟩` of `⟨e₁⟩` to the other complement
`⟨e₂⟩`. -/
theorem map_transvection_zpowers_e₁_mul_e₂ :
    (zpowers (e₁ * e₂)).map transvection.toMonoidHom = zpowers e₂ := by
  rw [MonoidHom.map_zpowers]
  exact congrArg zpowers transvection_e₁_mul_e₂

/-- The group generated by the transvection stabilizes `⟨e₁⟩`. -/
theorem smul_mem_zpowers_e₁_of_transvection (a : zpowers transvection) {n : KleinFour}
    (hn : n ∈ zpowers e₁) : a • n ∈ zpowers e₁ := by
  have hle : zpowers transvection ≤ MulAction.stabilizer (MulAut KleinFour) e₁ :=
    zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr transvection_e₁)
  rw [mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)] at hn ⊢
  rcases hn with rfl | rfl
  · exact Or.inl (smul_one a)
  · exact Or.inr ((Subgroup.smul_def a e₁).trans (MulAction.mem_stabilizer_iff.mp (hle a.2)))

/-- No complement of `⟨e₁⟩` in `KleinFour` is stable under the group of order `2` generated by
the transvection. -/
theorem not_exists_invariant_complement_transvection :
    ¬ ∃ D : Subgroup KleinFour, (zpowers e₁).IsComplement' D ∧
      ∀ a : zpowers transvection, ∀ d ∈ D, a • d ∈ D := by
  rintro ⟨D, hD, hstable⟩
  refine not_exists_isComplement'_and_forall_apply_mem transvection
    (by rw [transvection_e₂]; decide) (by rw [transvection_e₁_mul_e₂]; decide)
    ⟨D, hD, fun d hd => ?_⟩
  simpa only [Subgroup.mk_smul, MulAut.smul_def] using hstable ⟨_, mem_zpowers _⟩ d hd

/-- The hypothesis `p ≠ q` of `Subgroup.exists_invariant_complement` cannot be dropped: for
`p = q = 2`, the transvection group acting on `KleinFour` with `N = ⟨e₁⟩` satisfies every other
hypothesis, but `N` has no invariant complement. -/
theorem not_forall_exists_invariant_complement_of_eq :
    ¬ ∀ (W A : Type) [Group W] [Group A] [Finite W] [Finite A] [MulDistribMulAction A W]
      (p : ℕ) [Fact p.Prime] (N : Subgroup W) [N.Normal] [IsMulCommutative N],
      IsPGroup p N → IsPGroup p A → (∀ a : A, ∀ n ∈ N, a • n ∈ N) → ∀ P : Sylow p W,
      (∃ K : Subgroup W, N.IsLocalComplement K P) →
      ∃ D : Subgroup W, N.IsComplement' D ∧ ∀ a : A, ∀ d ∈ D, a • d ∈ D := fun h =>
  not_exists_invariant_complement_transvection <|
    h KleinFour (zpowers transvection) 2 (zpowers e₁) (isPGroup_kleinFour.to_subgroup _)
      isPGroup_zpowers_transvection (fun a _ => smul_mem_zpowers_e₁_of_transvection a) default
      ⟨_, isLocalComplement_zpowers_e₁_sylow⟩

/-! ### The `A`-stability of `N` is needed -/

/-- The automorphism `e₁ ↦ e₂ ↦ e₁ * e₂ ↦ e₁` of `KleinFour`, of order `3`. -/
def rotation : MulAut KleinFour where
  toFun w := ofAdd ((toAdd w).2, (toAdd w).1 + (toAdd w).2)
  invFun w := ofAdd ((toAdd w).1 + (toAdd w).2, (toAdd w).1)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

@[simp]
theorem rotation_apply (w : KleinFour) :
    rotation w = ofAdd ((toAdd w).2, (toAdd w).1 + (toAdd w).2) :=
  (rfl)

-- High priority: these basis normal forms must fire before the coordinate expansion
-- `rotation_apply`, so that `simp` keeps the named basis elements.
@[simp high]
theorem rotation_e₁ : rotation e₁ = e₂ := by decide

@[simp high]
theorem rotation_e₂ : rotation e₂ = e₁ * e₂ := by decide

@[simp high]
theorem rotation_e₁_mul_e₂ : rotation (e₁ * e₂) = e₁ := by decide

theorem orderOf_rotation : orderOf rotation = 3 := by
  refine orderOf_eq_prime (MulEquiv.ext fun w => ?_) fun h => ?_
  · simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    revert w
    decide
  · have h₁ := congrArg (· e₁) h
    simp only [MulAut.one_apply, rotation_e₁] at h₁
    exact absurd h₁ (by decide)

theorem isPGroup_zpowers_rotation : IsPGroup 3 (zpowers rotation) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_rotation, pow_one])

/-- The rotation does not stabilize `⟨e₁⟩`: it sends `e₁` to `e₂`. -/
theorem not_forall_smul_mem_zpowers_e₁_of_rotation :
    ¬ ∀ a : zpowers rotation, ∀ n ∈ zpowers e₁, a • n ∈ zpowers e₁ := fun h => by
  have := h ⟨rotation, mem_zpowers _⟩ e₁ (mem_zpowers _)
  rw [Subgroup.mk_smul, MulAut.smul_def, rotation_e₁,
    mem_zpowers_iff_of_sq_eq_one (sq_eq_one_of_kleinFour _)] at this
  exact absurd this (by decide)

/-- No complement of `⟨e₁⟩` in `KleinFour` is stable under the group of order `3` generated by
the rotation. -/
theorem not_exists_invariant_complement_rotation :
    ¬ ∃ D : Subgroup KleinFour, (zpowers e₁).IsComplement' D ∧
      ∀ a : zpowers rotation, ∀ d ∈ D, a • d ∈ D := by
  rintro ⟨D, hD, hstable⟩
  refine not_exists_isComplement'_and_forall_apply_mem rotation
    (by rw [rotation_e₂]; decide) (by rw [rotation_e₁_mul_e₂]; decide) ⟨D, hD, fun d hd => ?_⟩
  simpa only [Subgroup.mk_smul, MulAut.smul_def] using hstable ⟨_, mem_zpowers _⟩ d hd

/-- The `A`-stability of `N` in `Subgroup.exists_invariant_complement` cannot be dropped: for
`p = 2` and `q = 3`, the rotation group acting on `KleinFour` with `N = ⟨e₁⟩` satisfies every
other hypothesis, but `N` has no invariant complement. -/
theorem not_forall_exists_invariant_complement_of_not_stable :
    ¬ ∀ (W A : Type) [Group W] [Group A] [Finite W] [Finite A] [MulDistribMulAction A W]
      (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (N : Subgroup W) [N.Normal] [IsMulCommutative N],
      IsPGroup p N → IsPGroup q A → p ≠ q → ∀ P : Sylow p W,
      (∃ K : Subgroup W, N.IsLocalComplement K P) →
      ∃ D : Subgroup W, N.IsComplement' D ∧ ∀ a : A, ∀ d ∈ D, a • d ∈ D := fun h =>
  not_exists_invariant_complement_rotation <|
    h KleinFour (zpowers rotation) 2 3 (zpowers e₁) (isPGroup_kleinFour.to_subgroup _)
      isPGroup_zpowers_rotation (by decide) default ⟨_, isLocalComplement_zpowers_e₁_sylow⟩

end TauCeti.Examples.InvariantSharpness
