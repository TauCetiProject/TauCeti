/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.GroupTheory.Coset.Basic

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
order of `H`.  For the trivial character `χ = 1`, the left multiples of the norm element are
characterized without dividing by `#H`: `x` is of the form `y * ∑_{h ∈ H} h` if and only if right
multiplication by every `h ∈ H` fixes `x`, because its coefficients are then constant on each left
coset `gH`.

The coefficients `k` form an arbitrary semiring, except in the general right translation law —
where the scalar `χ(p⁻¹)` has to move past the values of `χ`, so `k` is taken to be commutative —
and in `TauCeti.mem_span_subgroupCharSum_one_iff`, where both `k` and `G` are taken to be
commutative so that two-sided principal ideals `Ideal.span` apply.

## Main definitions and results

* `TauCeti.subgroupCharSum`: the character sum `∑_{h ∈ H} χ(h) h` in `k[G]`;
* `TauCeti.subgroupCharSum_coeff`: its coefficients are `χ` on `H` and zero off `H`;
* `TauCeti.single_mul_subgroupCharSum` and `TauCeti.subgroupCharSum_mul_single`: the two
  translation laws, scaling by `χ(p⁻¹)` for `p ∈ H`;
* `TauCeti.subgroupCharSum_mul_self`: the character sum squares to `Nat.card H` times itself;
* `TauCeti.subgroupCharSum_eq_one` and `TauCeti.subgroupCharSum_eq_sum_of_eq_top`: its values on
  the two extreme subgroups, `⊥` and `⊤`;
* `TauCeti.exists_mul_subgroupCharSum_one_eq_iff` and `TauCeti.mem_span_subgroupCharSum_one_iff`:
  multiples of the norm element `∑_{h ∈ H} h` are the elements fixed by `H`.
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

/-- Right multiplication by a member of `H` fixes the norm element `∑_{h ∈ H} h`, even when the
coefficient semiring is noncommutative. -/
@[simp]
theorem subgroupCharSum_one_mul_single (p : H) :
    subgroupCharSum (1 : G →* k) H * MonoidAlgebra.single (p : G) 1 =
      subgroupCharSum (1 : G →* k) H := by
  rw [subgroupCharSum_def, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulRight p) _ _ fun h => ?_
  simp [MonoidAlgebra.of_apply]

/-- An element `x` of `k[G]` is a left multiple `y * ∑_{h ∈ H} h` of the subgroup norm element if
and only if right multiplication by every element of `H` fixes `x`. -/
theorem exists_mul_subgroupCharSum_one_eq_iff (x : MonoidAlgebra k G) :
    (∃ y, y * subgroupCharSum (1 : G →* k) H = x) ↔
      ∀ h : H, x * MonoidAlgebra.single (h : G) 1 = x := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ h
    rw [mul_assoc, subgroupCharSum_one_mul_single]
  · intro hx
    have hcoeff (g : G) (h : H) : x.coeff (g * h) = x.coeff g := by
      simpa using (congrArg (fun z ↦ z.coeff (g * h)) (hx h)).symm
    let S : Finset (G ⧸ H) := x.coeff.support.image QuotientGroup.mk
    refine ⟨∑ c ∈ S, MonoidAlgebra.single c.out (x.coeff c.out), ?_⟩
    ext g
    have hterm (c : G ⧸ H) :
        (MonoidAlgebra.single c.out (x.coeff c.out) *
          subgroupCharSum (1 : G →* k) H).coeff g =
            if c = QuotientGroup.mk g then x.coeff g else 0 := by
      rw [MonoidAlgebra.coeff_single_mul_apply, subgroupCharSum_coeff, MonoidHom.one_apply,
        mul_ite, mul_one, mul_zero]
      have hmem : c.out⁻¹ * g ∈ H ↔ c = QuotientGroup.mk g := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      split_ifs with h1 h2 h2
      · obtain ⟨h, hh⟩ : ∃ h : H, c.out * h = g :=
          ⟨⟨c.out⁻¹ * g, h1⟩, mul_inv_cancel_left c.out g⟩
        rw [← hh, hcoeff c.out h]
      · exact absurd (hmem.mp h1) h2
      · exact absurd (hmem.mpr h2) h1
      · rfl
    have hzero (hgS : QuotientGroup.mk g ∉ S) : x.coeff g = 0 :=
      Finsupp.notMem_support_iff.mp fun hg ↦ hgS (Finset.mem_image_of_mem QuotientGroup.mk hg)
    simp +contextual [Finset.sum_mul, MonoidAlgebra.coeff_sum, hterm, hzero]

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

/-- In a commutative group algebra, an element lies in the principal ideal generated by the
subgroup norm `∑_{h ∈ H} h` if and only if multiplication by every element of `H` fixes it. -/
theorem mem_span_subgroupCharSum_one_iff {k G : Type*} [CommSemiring k] [CommGroup G]
    (H : Subgroup G) [Fintype H] (x : MonoidAlgebra k G) :
    x ∈ Ideal.span {subgroupCharSum (1 : G →* k) H} ↔
      ∀ h ∈ H, MonoidAlgebra.single h (1 : k) * x = x := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ h hh
    rw [← mul_assoc, single_mul_subgroupCharSum (1 : G →* k) H ⟨h, hh⟩, MonoidHom.one_apply,
      one_smul]
  · intro hx
    obtain ⟨y, rfl⟩ := (exists_mul_subgroupCharSum_one_eq_iff H x).mpr fun h ↦ by
      rw [mul_comm, hx h h.property]
    exact ⟨y, mul_comm _ _⟩

end CommSemiring

end TauCeti
