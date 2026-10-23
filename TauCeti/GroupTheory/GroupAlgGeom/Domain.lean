/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CSA

/-!
# Zero divisors in groups with coefficients

An element `x ≠ 1` is a zero divisor over a coefficient group `G` if it commutes with every
coefficient conjugate of some `y ≠ 1`. A group is a `G`-domain when it has no such elements.
For a CSA group, malnormality of the centralizer of `x` forces every coefficient to lie in
that abelian centralizer. Thus noncommuting coefficients imply the domain property.

The coefficient map need not be injective for the definitions. The CSA result asks directly
that its image be nonabelian; an injective map from a nonabelian group supplies this condition.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic
  sets and ideal theory*, J. Algebra 219 (1999), §2.1, Definition 1 and Proposition 1.
-/

public section

namespace TauCeti.GroupAlgGeom

variable {G H : Type*} [Group G] [Group H]

/-- A nonidentity element `x` is a zero divisor over `G` if it commutes with every coefficient
conjugate of some nonidentity element `y`. -/
def IsZeroDivisor (ι : G →* H) (x : H) : Prop :=
  x ≠ 1 ∧ ∃ y : H, y ≠ 1 ∧ ∀ g : G, Commute x (ι g * y * (ι g)⁻¹)

/-- A group with coefficients in `G` is a `G`-domain if it has no `G`-zero divisors. -/
def IsGDomain (ι : G →* H) : Prop :=
  ∀ x : H, ¬ IsZeroDivisor ι x

/-- The defining condition for a zero divisor. -/
theorem isZeroDivisor_iff (ι : G →* H) (x : H) :
    IsZeroDivisor ι x ↔
      x ≠ 1 ∧ ∃ y : H, y ≠ 1 ∧ ∀ g : G, Commute x (ι g * y * (ι g)⁻¹) := Iff.rfl

/-- A group is a `G`-domain exactly when every pair of nonidentity elements can be separated by
conjugating the second with a coefficient. -/
theorem isGDomain_iff (ι : G →* H) :
    IsGDomain ι ↔
      ∀ x y : H, x ≠ 1 → y ≠ 1 → ∃ g : G, ¬ Commute x (ι g * y * (ι g)⁻¹) := by
  simp only [IsGDomain, IsZeroDivisor, not_and, not_exists, not_forall]
  tauto

namespace IsGDomain

/-- A `G`-domain is a domain with respect to its entire group of elements. -/
theorem isDomain {ι : G →* H} (h : IsGDomain ι) : IsGDomain (MonoidHom.id H) := by
  apply (isGDomain_iff _).2
  intro x y hx hy
  obtain ⟨g, hg⟩ := (isGDomain_iff ι).1 h x y hx hy
  exact ⟨ι g, by simpa using hg⟩

/-- A CSA group is a `G`-domain if the image of the coefficients is nonabelian. -/
theorem of_isCSA_of_not_commute_range {ι : G →* H} (hCSA : Group.IsCSA H)
    (ha : ∃ a b : G, ¬ Commute (ι a) (ι b)) : IsGDomain ι := by
  intro x hx
  obtain ⟨hx1, y, hy1, hxy⟩ := hx
  let C : Subgroup H := Subgroup.centralizer {x}
  have hC : IsMulCommutative C := hCSA.centralizer_isMulCommutative hx1
  have hTI : TauCeti.IsTISubgroup C := hCSA.centralizer_isTISubgroup hx1
  have hyC : y ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa using (hxy 1).eq.symm
  have hιC (g : G) : ι g ∈ C := by
    by_contra hg
    apply hy1
    apply hTI.eq_one hg hyC
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (hxy g).eq.symm
  obtain ⟨a, b, hab⟩ := ha
  exact hab ((commute_iff_eq _ _).mpr
    ((isMulCommutative_iff_of_setLike.mp hC) (ι a) (hιC a) (ι b) (hιC b)))

/-- A CSA group receiving an embedded nonabelian coefficient group is a `G`-domain. -/
theorem of_isCSA {ι : G →* H} (hCSA : Group.IsCSA H)
    (hι : Function.Injective ι) (hG : ¬ IsMulCommutative G) : IsGDomain ι := by
  apply of_isCSA_of_not_commute_range hCSA
  by_contra h
  push Not at h
  apply hG
  exact ⟨⟨fun a b => hι (by simpa only [map_mul] using (h a b).eq)⟩⟩

end IsGDomain

/-- A nontrivial abelian group has a zero divisor over itself. -/
theorem not_isGDomain_self_of_commutative [IsMulCommutative H] [Nontrivial H] :
    ¬ IsGDomain (MonoidHom.id H) := by
  obtain ⟨x, hx⟩ : ∃ x : H, x ≠ 1 := exists_ne 1
  intro h
  apply h x
  refine ⟨hx, x, hx, ?_⟩
  intro g
  exact (commute_iff_eq _ _).mpr (mul_comm' x (g * x * g⁻¹))

/-- The trivial group is a domain. -/
theorem isGDomain_subsingleton [Subsingleton H] (ι : G →* H) : IsGDomain ι := by
  intro x hx
  exact hx.1 (Subsingleton.elim x 1)

/-- The product of two nontrivial groups is not a domain: elements supported in different
factors commute with every conjugate of one another. -/
theorem not_isGDomain_prod {K : Type*} [Group K] [Nontrivial H] [Nontrivial K] :
    ¬ IsGDomain (MonoidHom.id (H × K)) := by
  obtain ⟨x, hx⟩ : ∃ x : H, x ≠ 1 := exists_ne 1
  obtain ⟨y, hy⟩ : ∃ y : K, y ≠ 1 := exists_ne 1
  intro h
  apply h (x, 1)
  refine ⟨by simpa using hx, (1, y), by simpa using hy, ?_⟩
  intro g
  simpa [Prod.mul_def] using
    (Commute.prod (Commute.one_right x) (Commute.one_left (g.2 * y * g.2⁻¹)))

end TauCeti.GroupAlgGeom

namespace IsFreeGroup

/-- Every nonabelian free group is a domain over itself. -/
theorem isGDomain {H : Type*} [Group H] [IsFreeGroup H]
    (h : ¬ IsMulCommutative H) :
    TauCeti.GroupAlgGeom.IsGDomain (MonoidHom.id H) := by
  apply TauCeti.GroupAlgGeom.IsGDomain.of_isCSA isCSA (fun _ _ h => h)
  exact h

end IsFreeGroup
