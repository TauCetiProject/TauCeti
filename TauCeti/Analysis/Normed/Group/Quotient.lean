/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Quotients of seminormed and ultrametric groups

For a subgroup `S` of a seminormed commutative group `M`, an element `s ∈ S` minimises `‖m / s'‖`
over `s' ∈ S` if and only if `‖m / s‖` attains the quotient seminorm `‖(m : M ⧸ S)‖`
(`QuotientGroup.norm_div_eq_norm_mk_iff`), so every coset has a least-norm element precisely when
every class in `M ⧸ S` has a representative of the same norm
(`QuotientGroup.exists_mk_eq_and_norm_eq_iff`). The additive, submodule and ideal counterparts
give the corresponding characterisations of strict closedness for submodules and ideals.

If every nontrivial element of `S` has seminorm at least twice that of `m`, then `m` attains the
quotient seminorm of its class (`QuotientGroup.norm_mk_eq_norm`). So the projection `M → M ⧸ S`
preserves the distance between two points whose distance is at most half the least seminorm of a
nontrivial element of `S` (`QuotientGroup.dist_mk_eq_dist`); for a lattice in a normed space this
says that the projection to the torus is an isometry on small sets.

When `M` is ultrametric, the quotient seminorm on `M ⧸ S` is again ultrametric: each class has
representatives whose norms approximate its quotient norm, and the ultrametric inequality for a
product of such representatives descends to the quotient. The additive form covers quotients of
modules by submodules and of commutative seminormed rings by ideals, so residue norms of
nonarchimedean Banach algebras are again nonarchimedean.
-/

public section

namespace QuotientGroup

section LeastNorm

variable {M : Type*} [SeminormedCommGroup M] {S : Subgroup M}

/-- For `s ∈ S`, the element `m / s` attains the quotient seminorm of `m` modulo `S` if and only
if `s` minimises `‖m / s'‖` over `S`. -/
@[to_additive /-- For `s ∈ S`, the element `m - s` attains the quotient seminorm of `m` modulo `S`
if and only if `s` minimises `‖m - s'‖` over `S`. -/]
theorem norm_div_eq_norm_mk_iff {m s : M} (hs : s ∈ S) :
    ‖m / s‖ = ‖(m : M ⧸ S)‖ ↔ ∀ s' ∈ S, ‖m / s‖ ≤ ‖m / s'‖ := by
  constructor
  · intro h s' hs'
    have hmk : ((m / s' : M) : M ⧸ S) = m :=
      QuotientGroup.eq.mpr (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hs')
    exact h.trans_le (hmk ▸ norm_mk_le_norm)
  · intro h
    apply le_antisymm
    · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      obtain ⟨n, hn, hn'⟩ := exists_norm_mk_lt (m : M ⧸ S) hε
      have hmn : m / n ∈ S := by
        have := QuotientGroup.eq.mp hn.symm
        simpa [div_eq_mul_inv, mul_comm] using S.inv_mem this
      exact (h (m / n) hmn).trans_lt (by simpa [div_div_cancel] using hn')
    · have hmk : ((m / s : M) : M ⧸ S) = m :=
        QuotientGroup.eq.mpr (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hs)
      exact hmk ▸ norm_mk_le_norm

/-- Every class in `M ⧸ S` has a representative attaining its quotient seminorm if and only if
every coset of `S` has an element of least seminorm. -/
@[to_additive /-- Every class in `M ⧸ S` has a representative attaining its quotient seminorm if
and only if every coset of `S` has an element of least seminorm. -/]
theorem exists_mk_eq_and_norm_eq_iff :
    (∀ x : M ⧸ S, ∃ m : M, (m : M ⧸ S) = x ∧ ‖m‖ = ‖x‖) ↔
      ∀ m : M, ∃ s ∈ S, ∀ s' ∈ S, ‖m / s‖ ≤ ‖m / s'‖ := by
  constructor
  · intro h m
    obtain ⟨n, hn, hnorm⟩ := h (m : M ⧸ S)
    have hmn : m / n ∈ S := by
      have := QuotientGroup.eq.mp hn.symm
      simpa [div_eq_mul_inv, mul_comm] using S.inv_mem this
    refine ⟨m / n, hmn, (norm_div_eq_norm_mk_iff hmn).mp ?_⟩
    simpa [div_div_cancel] using hnorm
  · intro h x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨s, hs, hle⟩ := h m
    have hmk : ((m / s : M) : M ⧸ S) = m :=
      QuotientGroup.eq.mpr (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hs)
    exact ⟨m / s, hmk, (norm_div_eq_norm_mk_iff hs).mpr hle⟩

end LeastNorm

section Small

variable {M : Type*} [SeminormedCommGroup M] {S : Subgroup M}

/-- If every nontrivial element of `S` has at least twice the seminorm of `m`, then the quotient
seminorm of `m` modulo `S` is the seminorm of `m`. -/
@[to_additive /-- If every nonzero element of `S` has at least twice the seminorm of `m`, then the
quotient seminorm of `m` modulo `S` is the seminorm of `m`. -/]
theorem norm_mk_eq_norm {m : M} (h : ∀ s ∈ S, s ≠ 1 → 2 * ‖m‖ ≤ ‖s‖) :
    ‖(m : M ⧸ S)‖ = ‖m‖ := by
  refine le_antisymm norm_mk_le_norm (le_norm_iff.2 fun m' hm' ↦ ?_)
  have hs : m⁻¹ * m' ∈ S := QuotientGroup.eq.1 hm'.symm
  by_cases hs1 : m⁻¹ * m' = 1
  · rw [inv_mul_eq_one.1 hs1]
  · have := (h _ hs hs1).trans (norm_mul_le' m⁻¹ m')
    rw [norm_inv'] at this
    linarith

/-- The projection to `M ⧸ S` preserves the distance between `x` and `y` when every nontrivial
element of `S` has at least twice that distance as seminorm. -/
@[to_additive /-- The projection to `M ⧸ S` preserves the distance between `x` and `y` when every
nonzero element of `S` has at least twice that distance as seminorm. -/]
theorem dist_mk_eq_dist {x y : M} (h : ∀ s ∈ S, s ≠ 1 → 2 * dist x y ≤ ‖s‖) :
    dist (x : M ⧸ S) y = dist x y := by
  rw [dist_eq_norm_div, dist_eq_norm_div, ← QuotientGroup.mk_div]
  exact norm_mk_eq_norm fun s hs hs1 ↦ (dist_eq_norm_div x y) ▸ h s hs hs1

end Small

section Ultrametric

variable {M : Type*} [SeminormedCommGroup M] [IsUltrametricDist M]

/-- The quotient of an ultrametric seminormed commutative group by a subgroup is ultrametric. -/
@[to_additive /-- The quotient of an ultrametric seminormed additive commutative group by an
additive subgroup is ultrametric. -/]
instance instIsUltrametricDist (S : Subgroup M) : IsUltrametricDist (M ⧸ S) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_mul_le_max_norm fun x y ↦ by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨a, rfl, ha⟩ := exists_norm_mk_lt x hε
    obtain ⟨b, rfl, hb⟩ := exists_norm_mk_lt y hε
    rw [← QuotientGroup.mk_mul]
    calc ‖((a * b : M) : M ⧸ S)‖ ≤ ‖a * b‖ := norm_mk_le_norm
      _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_mul_le_max a b
      _ ≤ max ‖(a : M ⧸ S)‖ ‖(b : M ⧸ S)‖ + ε :=
        (max_le_max ha.le hb.le).trans (max_add_add_right _ _ _).le

end Ultrametric

end QuotientGroup

section Submodule

variable {R M : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M]

/-- For `s ∈ S`, the vector `m - s` attains the quotient seminorm of `m` modulo the submodule `S`
if and only if `s` minimises `‖m - s'‖` over `S`. -/
theorem Submodule.Quotient.norm_sub_eq_norm_mk_iff {S : Submodule R M} {m s : M} (hs : s ∈ S) :
    ‖m - s‖ = ‖(Submodule.Quotient.mk m : M ⧸ S)‖ ↔ ∀ s' ∈ S, ‖m - s‖ ≤ ‖m - s'‖ :=
  QuotientAddGroup.norm_sub_eq_norm_mk_iff (S := S.toAddSubgroup) hs

/-- Every class in `M ⧸ S` has a representative attaining its quotient seminorm if and only if
every coset of the submodule `S` has a vector of least seminorm. -/
theorem Submodule.Quotient.exists_mk_eq_and_norm_eq_iff {S : Submodule R M} :
    (∀ x : M ⧸ S, ∃ m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ = ‖x‖) ↔
      ∀ m : M, ∃ s ∈ S, ∀ s' ∈ S, ‖m - s‖ ≤ ‖m - s'‖ :=
  QuotientAddGroup.exists_mk_eq_and_norm_eq_iff (S := S.toAddSubgroup)

/-- The quotient of an ultrametric seminormed module by a submodule is ultrametric. -/
instance Submodule.Quotient.instIsUltrametricDist [IsUltrametricDist M] (S : Submodule R M) :
    IsUltrametricDist (M ⧸ S) :=
  inferInstanceAs <| IsUltrametricDist (M ⧸ S.toAddSubgroup)

end Submodule

section Ideal

variable {R : Type*} [SeminormedCommRing R]

/-- For `s ∈ I`, the element `r - s` attains the quotient seminorm of `r` modulo the ideal `I`
if and only if `s` minimises `‖r - s'‖` over `I`. -/
theorem Ideal.Quotient.norm_sub_eq_norm_mk_iff {I : Ideal R} {r s : R} (hs : s ∈ I) :
    ‖r - s‖ = ‖Ideal.Quotient.mk I r‖ ↔ ∀ s' ∈ I, ‖r - s‖ ≤ ‖r - s'‖ :=
  Submodule.Quotient.norm_sub_eq_norm_mk_iff (S := I) hs

/-- Every residue class in `R ⧸ I` has a representative attaining its quotient seminorm if and only
if every coset of `I` has an element of least seminorm. -/
theorem Ideal.Quotient.exists_mk_eq_and_norm_eq_iff {I : Ideal R} :
    (∀ x : R ⧸ I, ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ = ‖x‖) ↔
      ∀ r : R, ∃ s ∈ I, ∀ s' ∈ I, ‖r - s‖ ≤ ‖r - s'‖ :=
  Submodule.Quotient.exists_mk_eq_and_norm_eq_iff (S := I)

end Ideal
