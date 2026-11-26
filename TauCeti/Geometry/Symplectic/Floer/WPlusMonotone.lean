/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Spherical
public import TauCeti.Geometry.Symplectic.Floer.PeriodGroup

/-!
# w⁺-monotone symplectic manifolds

Let `(M, ω)` be a closed symplectic manifold of dimension `2n`, with first Chern class `c₁`. It is
**w⁺-monotone** if every spherical class `A ∈ H₂(M; ℤ)` with `0 < c₁(A) ≤ n - 2` has positive
area `ω(A) > 0`. Since a nonconstant pseudoholomorphic sphere has positive area, on a
w⁺-monotone manifold no class of first Chern number in `[2 - n, 0)` is represented by one.

This is the strict form of the condition. Lee counts the pseudoholomorphic tori of a
symplectomorphism and builds the Floer–Novikov torsion under a w⁺-monotonicity assumption in the
style of Hofer–Salamon weak monotonicity, which asks only `ω(A) ≥ 0` on the same range. The strict
form implies the weak one, and for `n ≥ 3` it is strictly stronger: it fails, for instance, when
`ω` vanishes on spherical classes while `c₁` takes a value in `(0, n - 2]`.

As for the period group `TauCeti.Floer.PeriodGroup`, the condition is stated for an arbitrary
additive group `S` with homomorphisms `ω : S →+ ℝ` and `c : S →+ ℤ`
(`TauCeti.Floer.IsWPlusMonotone ω c n`). For a manifold, `S` is the group of spherical classes
(`TauCeti.sphericalClasses`), and `ω` and `c` are integration of the symplectic form and
evaluation of the first Chern class.

* Replacing `A` by `-A`, the condition says that a class of nonnegative area and Chern number at
  least `2 - n` has nonnegative Chern number
  (`TauCeti.Floer.isWPlusMonotone_iff_forall_chern_nonneg`): the form in which it is applied to
  pseudoholomorphic spheres. This is stronger than semipositivity in the sense of McDuff and
  Salamon, which asks it only for classes of positive area and first Chern number at least
  `3 - n`.
* The condition becomes weaker as `n` decreases (`TauCeti.Floer.IsWPlusMonotone.mono`). It holds
  vacuously when no class has Chern number in `(0, n - 2]`, which is the case when the minimal
  Chern number is at least `n - 1` (`TauCeti.Floer.isWPlusMonotone_of_forall_sub_one_le_chern`),
  when `c` vanishes, as on a spherically aspherical manifold
  (`TauCeti.Floer.isWPlusMonotone_of_chern_eq_zero`), and in dimensions `2` and `4`, where the
  range is empty (`TauCeti.Floer.isWPlusMonotone_of_le_two`).
* A positively monotone manifold, `ω = τ c` with `τ > 0`, is w⁺-monotone
  (`TauCeti.Floer.isWPlusMonotone_of_area_eq_mul_chern`).
* The condition pulls back along homomorphisms of class groups and descends along surjective
  ones (`TauCeti.Floer.isWPlusMonotone_comp_iff`). In particular it only depends on the period
  group `S ⧸ (ker ω ⊓ ker c)` with its area and first Chern number
  (`TauCeti.Floer.PeriodGroup.isWPlusMonotone_iff`), and on a path-connected space it is a
  condition on the Hurewicz classes of the elements of `π₂(X, x)` at a single base point
  (`TauCeti.Floer.isWPlusMonotone_sphericalClasses_iff`).

## References

* H. Hofer and D. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial volume*,
  Progr. Math. 133, Birkhäuser, 1995, 483–524 (weak monotonicity).
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311, arXiv:math/0111313, the w⁺-monotonicity
  assumption.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Definition 6.4.1 (semipositivity).
-/

public section

namespace TauCeti.Floer

section ClassGroup

variable {S S' : Type*} [AddGroup S] [AddGroup S'] {ω : S →+ ℝ} {c : S →+ ℤ} {n m : ℕ}

variable (ω c n) in
/-- The class data `(ω, c)` of a symplectic manifold of dimension `2n` is **w⁺-monotone** if every
class whose first Chern number lies in `(0, n - 2]` has positive area. This is the strict form of
the condition; the weak form asks only for nonnegative area. -/
def IsWPlusMonotone : Prop :=
  ∀ s, 0 < c s → c s ≤ (n : ℤ) - 2 → 0 < ω s

/-- The definition of w⁺-monotonicity, whose body is not exposed outside this module. -/
theorem isWPlusMonotone_iff :
    IsWPlusMonotone ω c n ↔ ∀ s, 0 < c s → c s ≤ (n : ℤ) - 2 → 0 < ω s :=
  Iff.rfl

/-- The data are not w⁺-monotone exactly when some class with first Chern number in `(0, n - 2]`
has nonpositive area. -/
theorem not_isWPlusMonotone_iff :
    ¬ IsWPlusMonotone ω c n ↔ ∃ s, 0 < c s ∧ c s ≤ (n : ℤ) - 2 ∧ ω s ≤ 0 := by
  simp only [isWPlusMonotone_iff, not_forall, not_lt, exists_prop]

namespace IsWPlusMonotone

/-- On w⁺-monotone data, a class with first Chern number in `(0, n - 2]` has positive area. -/
theorem area_pos (h : IsWPlusMonotone ω c n) {s : S} (hc : 0 < c s) (hcn : c s ≤ (n : ℤ) - 2) :
    0 < ω s :=
  h s hc hcn

/-- On w⁺-monotone data, a class with first Chern number in `[2 - n, 0)` has negative area. -/
theorem area_neg (h : IsWPlusMonotone ω c n) {s : S} (hcn : 2 - (n : ℤ) ≤ c s) (hc : c s < 0) :
    ω s < 0 := by
  have := h (-s) (by rw [map_neg]; omega) (by rw [map_neg]; omega)
  rwa [map_neg, neg_pos] at this

/-- **The form in which w⁺-monotonicity is applied to pseudoholomorphic spheres.** On w⁺-monotone
data, a class of nonnegative area and first Chern number at least `2 - n` has nonnegative first
Chern number. -/
theorem chern_nonneg (h : IsWPlusMonotone ω c n) {s : S} (hω : 0 ≤ ω s)
    (hcn : 2 - (n : ℤ) ≤ c s) : 0 ≤ c s := by
  by_contra hc
  exact (h.area_neg hcn (not_le.1 hc)).not_ge hω

/-- w⁺-monotonicity becomes weaker as the dimension decreases. -/
theorem mono (h : IsWPlusMonotone ω c n) (hmn : m ≤ n) : IsWPlusMonotone ω c m :=
  fun s hc hcm ↦ h s hc (hcm.trans (by omega))

/-- w⁺-monotone data pull back to w⁺-monotone data along any homomorphism of class groups. -/
theorem comp (h : IsWPlusMonotone ω c n) (f : S' →+ S) :
    IsWPlusMonotone (ω.comp f) (c.comp f) n :=
  fun s ↦ h (f s)

end IsWPlusMonotone

/-- **w⁺-monotonicity in its semipositivity form**: the data are w⁺-monotone exactly when every
class of nonnegative area and first Chern number at least `2 - n` has nonnegative first Chern
number. -/
theorem isWPlusMonotone_iff_forall_chern_nonneg :
    IsWPlusMonotone ω c n ↔ ∀ s, 0 ≤ ω s → 2 - (n : ℤ) ≤ c s → 0 ≤ c s := by
  refine ⟨fun h s hω hcn ↦ h.chern_nonneg hω hcn, fun h s hc hcn ↦ ?_⟩
  by_contra hω
  have := h (-s) (by rw [map_neg]; linarith [not_lt.1 hω]) (by rw [map_neg]; omega)
  rw [map_neg] at this
  omega

/-- w⁺-monotonicity holds when the minimal Chern number is at least `n - 1`: no class then has
first Chern number in `(0, n - 2]`. -/
theorem isWPlusMonotone_of_forall_sub_one_le_chern (h : ∀ s, 0 < c s → (n : ℤ) - 1 ≤ c s) :
    IsWPlusMonotone ω c n :=
  fun s hc hcn ↦ absurd (h s hc) (by omega)

/-- Data whose first Chern number vanishes, such as those of a spherically aspherical manifold,
are w⁺-monotone. -/
theorem isWPlusMonotone_of_chern_eq_zero (h : ∀ s, c s = 0) : IsWPlusMonotone ω c n :=
  isWPlusMonotone_of_forall_sub_one_le_chern fun s hc ↦ absurd (h s) hc.ne'

/-- **In dimensions `2` and `4` every symplectic manifold is w⁺-monotone**: no integer lies in
`(0, n - 2]` when `n ≤ 2`. -/
theorem isWPlusMonotone_of_le_two (hn : n ≤ 2) : IsWPlusMonotone ω c n :=
  isWPlusMonotone_of_forall_sub_one_le_chern fun _ hc ↦ by omega

/-- **Positively monotone data are w⁺-monotone**: if `ω = τ c` with `τ > 0`, every class of
positive first Chern number has positive area. -/
theorem isWPlusMonotone_of_area_eq_mul_chern {τ : ℝ} (h : ∀ s, ω s = τ * c s) (hτ : 0 < τ) :
    IsWPlusMonotone ω c n :=
  fun s hc _ ↦ by
    rw [h s]
    exact mul_pos hτ (Int.cast_pos.2 hc)

/-- Along a surjective homomorphism of class groups, the pulled-back data are w⁺-monotone exactly
when the original ones are. -/
theorem isWPlusMonotone_comp_iff {f : S' →+ S} (hf : Function.Surjective f) :
    IsWPlusMonotone (ω.comp f) (c.comp f) n ↔ IsWPlusMonotone ω c n := by
  refine ⟨fun h s hc hcn ↦ ?_, fun h ↦ h.comp f⟩
  obtain ⟨s', rfl⟩ := hf s
  exact h s' hc hcn

/-- **w⁺-monotonicity only depends on the period group**: the area and first Chern number of the
period group are w⁺-monotone exactly when the data on the class group are. -/
theorem PeriodGroup.isWPlusMonotone_iff :
    IsWPlusMonotone (area ω c) (chern ω c) n ↔ IsWPlusMonotone ω c n := by
  have hω : (area ω c).comp (QuotientAddGroup.mk' _) = ω := by ext s; simp
  have hc : (chern ω c).comp (QuotientAddGroup.mk' _) = c := by ext s; simp
  rw [← isWPlusMonotone_comp_iff (QuotientAddGroup.mk'_surjective _), hω, hc]

end ClassGroup

section Spherical

open CategoryTheory AlgebraicTopology HomotopyGroup

variable {X : Type} [TopologicalSpace X]
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ} {n : ℕ}

/-- On w⁺-monotone spherical classes, the Hurewicz class of a sphere with first Chern number in
`(0, n - 2]` has positive area. -/
theorem IsWPlusMonotone.area_hurewiczIntHom_pos
    (h : IsWPlusMonotone (ω.comp (sphericalClasses X 1).subtype)
      (c.comp (sphericalClasses X 1).subtype) n)
    (x : X) {a : Additive (HomotopyGroup (Fin 2) X x)} (hc : 0 < c (hurewiczIntHom X x 1 a))
    (hcn : c (hurewiczIntHom X x 1 a) ≤ (n : ℤ) - 2) : 0 < ω (hurewiczIntHom X x 1 a) :=
  h ⟨_, hurewiczIntHom_mem_sphericalClasses x a⟩ hc hcn

/-- **w⁺-monotonicity of a path-connected space in terms of spheres**: on a path-connected space
the spherical classes are w⁺-monotone exactly when every element of `π₂(X, x)`, at any single
base point `x`, whose Hurewicz class has first Chern number in `(0, n - 2]` has a Hurewicz class
of positive area. -/
theorem isWPlusMonotone_sphericalClasses_iff [PathConnectedSpace X] (x : X) :
    IsWPlusMonotone (ω.comp (sphericalClasses X 1).subtype)
        (c.comp (sphericalClasses X 1).subtype) n ↔
      ∀ a : Additive (HomotopyGroup (Fin 2) X x), 0 < c (hurewiczIntHom X x 1 a) →
        c (hurewiczIntHom X x 1 a) ≤ (n : ℤ) - 2 → 0 < ω (hurewiczIntHom X x 1 a) := by
  refine ⟨fun h a hc hcn ↦ h.area_hurewiczIntHom_pos x hc hcn, fun h s hc hcn ↦ ?_⟩
  obtain ⟨a, ha⟩ := (mem_sphericalClasses_iff x).1 s.property
  simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← ha] at hc hcn ⊢
  exact h a hc hcn

end Spherical

end TauCeti.Floer
