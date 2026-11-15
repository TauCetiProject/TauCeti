/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Character sums over a subgroup

For a finite subgroup `H` of a group `G` and a multiplicative character `χ : G →* k`, this file
studies the element `∑_{h ∈ H} χ(h) h` of the group algebra `k[G]`, here
`TauCeti.subgroupCharSum χ H`.

Two instances of it occur throughout representation theory, and are what this file exists to
share: the **norm element** `∑_{h ∈ H} h` of a subgroup, which is `χ = 1`, and the **signed sum**
`∑_{h ∈ H} sgn(h) h` of a subgroup of a permutation group, which is `χ = sgn`.  The row
symmetrizer and the column antisymmetrizer of a Young tableau are exactly these two.

Everything here follows from `χ` being multiplicative; no assumption that `χ` takes values in
square roots of `1` is needed, even for the square.  The translation laws say that left or right
multiplication by `p ∈ H` rescales the sum by `χ(p⁻¹)`, which is proved by reindexing the sum
along the bijection `h ↦ p * h` or `h ↦ h * p` of `H`; the square is then obtained by summing the
left translation law over `H`, where the scalars `χ(h) χ(h⁻¹) = χ(1) = 1` collapse and leave the
order of `H`.

The coefficients `k` form an arbitrary semiring, except in the right translation law: there the
scalar `χ(p⁻¹)` has to move past the values of `χ`, so `k` is taken to be commutative.

## Main definitions and results

* `TauCeti.subgroupCharSum`: the character sum `∑_{h ∈ H} χ(h) h` in `k[G]`;
* `TauCeti.subgroupCharSum_coeff`: its coefficients are `χ` on `H` and zero off `H`;
* `TauCeti.single_mul_subgroupCharSum` and `TauCeti.subgroupCharSum_mul_single`: the two
  translation laws, scaling by `χ(p⁻¹)` for `p ∈ H`;
* `TauCeti.subgroupCharSum_mul_self`: the character sum squares to `Nat.card H` times itself;
* `TauCeti.subgroupCharSum_eq_one` and `TauCeti.subgroupCharSum_eq_sum_of_eq_top`: its values on
  the two extreme subgroups, `⊥` and `⊤`.
-/

public section

namespace TauCeti

section Semiring

variable {k G : Type*} [Semiring k] [Group G] (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- The **character sum** `∑_{h ∈ H} χ(h) h` of a multiplicative character `χ` over a finite
subgroup `H`, as an element of the group algebra `k[G]`. -/
noncomputable def subgroupCharSum : MonoidAlgebra k G :=
  ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G)

/-- The character sum is the `χ`-weighted sum of the basis elements indexed by `H`. -/
theorem subgroupCharSum_def :
    subgroupCharSum χ H = ∑ h : H, χ (h : G) • MonoidAlgebra.of k G (h : G) :=
  (rfl)

/-- The coefficient of a group element in the character sum is `χ` on `H` and zero off `H`. -/
@[simp]
theorem subgroupCharSum_coeff [DecidablePred (· ∈ H)] (g : G) :
    (subgroupCharSum χ H).coeff g = if g ∈ H then χ g else 0 := by
  classical
  simp [subgroupCharSum_def, MonoidAlgebra.coeff_sum, Finsupp.single_apply]
  split_ifs with hg
  · simpa [← Subtype.coe_inj] using Fintype.sum_ite_eq' (⟨g, hg⟩ : H) fun h : H => χ h
  · simp [fun h : H => ne_of_mem_of_not_mem h.property hg]

/-- Left multiplication by a member of `H` scales the character sum by `χ` of its inverse. -/
@[simp]
theorem single_mul_subgroupCharSum (p : H) :
    MonoidAlgebra.single (p : G) 1 * subgroupCharSum χ H =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft p) _ _ fun h => ?_
  simp [MonoidAlgebra.smul_single, ← mul_assoc, ← map_mul]

/-- The character sum squares to the order of `H` times itself. -/
@[simp]
theorem subgroupCharSum_mul_self :
    subgroupCharSum χ H * subgroupCharSum χ H = Nat.card H • subgroupCharSum χ H := by
  nth_rewrite 1 [subgroupCharSum_def]
  simp only [Finset.sum_mul, smul_mul_assoc, MonoidAlgebra.of_apply, single_mul_subgroupCharSum,
    smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- Over the trivial subgroup the character sum has the single term `χ 1 • 1`, so it is `1`. -/
theorem subgroupCharSum_eq_one (h : H = ⊥) : subgroupCharSum χ H = 1 := by
  subst h
  simp [subgroupCharSum_def, MonoidAlgebra.one_def,
    Subsingleton.elim (default : (⊥ : Subgroup G)) 1]

/-- The character sum over the whole group is the `χ`-weighted sum over the group. -/
theorem subgroupCharSum_eq_sum_of_eq_top [Fintype G] (h : H = ⊤) :
    subgroupCharSum χ H = ∑ g : G, χ g • MonoidAlgebra.of k G g := by
  subst h
  exact Fintype.sum_equiv Subgroup.topEquiv.toEquiv _ _ fun _ => rfl

end Semiring

section CommSemiring

variable {k G : Type*} [CommSemiring k] [Group G] (χ : G →* k) (H : Subgroup G) [Fintype H]

/-- Right multiplication by a member of `H` scales the character sum by `χ` of its inverse. -/
@[simp]
theorem subgroupCharSum_mul_single (p : H) :
    subgroupCharSum χ H * MonoidAlgebra.single (p : G) 1 =
      χ ((p : G)⁻¹) • subgroupCharSum χ H := by
  rw [subgroupCharSum_def, Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight p) _ _ fun h => ?_
  simp [MonoidAlgebra.smul_single, mul_comm (χ (p : G)⁻¹), mul_assoc, ← map_mul]

end CommSemiring

end TauCeti
