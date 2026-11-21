/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The `{±I}` subgroup and signed quotient `SL(n, R) ⧸ {±I}`

For an even-rank special linear group `SL(n, R)` over a commutative ring `R`, the scalar matrix `-I`
generates the central subgroup `{±I} = ⟨-1⟩` (`TauCeti.Matrix.SpecialLinearGroup.negOneSubgroup`).
Over rings with zero divisors (such as `ZMod 8` or `ZMod 12`), the full center `Z(SL(n, R))` can
strictly contain `{±I}`; the **signed quotient** `TauCeti.Matrix.SignedQuotient n R = SL(n, R) ⧸
{±I}` retains the extra central roots of unity and maps surjectively onto `PSL(n, R)` (`toPSL`),
agreeing canonically with `PSL(2, R)` when `R` has no zero divisors (`equivPSL`). Extension of
scalars along `R →+* S` is functorial (`map`, `map_id`, `map_comp`).
-/

public section

open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

variable (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] [Fact (Even (Fintype.card n))]

/-- The central subgroup `{±I} = ⟨-1⟩` of `SL(n, R)`. Over rings with zero divisors (such as
`ZMod 8` or `ZMod 12`), this can be a proper subgroup of `Subgroup.center (SpecialLinearGroup n R)`.
-/
def negOneSubgroup : Subgroup (_root_.Matrix.SpecialLinearGroup n R) :=
  Subgroup.zpowers (-1)

/-- Unfolding characterization of `negOneSubgroup`. -/
theorem negOneSubgroup_def : negOneSubgroup n R = Subgroup.zpowers (-1) := by rw [negOneSubgroup]

variable {n R}

/-- An element of `SL(n, R)` lies in `negOneSubgroup n R` if and only if it is `1` or `-1`. -/
@[simp]
theorem mem_negOneSubgroup_iff {g : _root_.Matrix.SpecialLinearGroup n R} :
    g ∈ negOneSubgroup n R ↔ g = 1 ∨ g = -1 := by
  have hsq : (-1 : _root_.Matrix.SpecialLinearGroup n R) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, neg_one_mul, neg_neg]
  rw [negOneSubgroup_def, Subgroup.mem_zpowers_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ?_,
    fun h ↦ h.elim (fun h1 ↦ ⟨0, by simp [h1]⟩) (fun h1 ↦ ⟨1, by simp [h1]⟩)⟩
  subst hk
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact Or.inl (by rw [← two_mul, _root_.zpow_mul, hsq]; simp)
  · exact Or.inr (by rw [_root_.zpow_add, zpow_one, _root_.zpow_mul, hsq]; simp)

/-- `negOneSubgroup n R` lies inside the center of `SL(n, R)`. -/
theorem negOneSubgroup_le_center :
    negOneSubgroup n R ≤ Subgroup.center (_root_.Matrix.SpecialLinearGroup n R) := by
  rw [negOneSubgroup_def, Subgroup.zpowers_le]
  exact Subgroup.mem_center_iff.mpr fun _ ↦ by rw [neg_one_mul, mul_neg_one]

/-- The central subgroup `negOneSubgroup n R` is normal in `SL(n, R)`. -/
instance instNormalNegOneSubgroup : (negOneSubgroup n R).Normal :=
  ⟨fun _ hx _ ↦ by rcases mem_negOneSubgroup_iff.mp hx with rfl | rfl <;> simp⟩

/-- Over a commutative ring without zero divisors, `negOneSubgroup (Fin 2) R` is the full center of
`SL₂(R)`. -/
theorem negOneSubgroup_eq_center [NoZeroDivisors R] :
    negOneSubgroup (Fin 2) R = Subgroup.center SL(2, R) := by
  ext g
  rw [mem_negOneSubgroup_iff, _root_.Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]

end TauCeti.Matrix.SpecialLinearGroup

namespace TauCeti.Matrix

/-- **The signed special linear quotient `SL(n, R) ⧸ {±I}`** (`Q_N` when `n = Fin 2` and
`R = ZMod N`), the quotient by `{±I}` through which `PSL₂(ℤ) = SL₂(ℤ) ⧸ {±I}` acts at level `N`. -/
abbrev SignedQuotient (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]
    [Fact (Even (Fintype.card n))] : Type _ :=
  _root_.Matrix.SpecialLinearGroup n R ⧸ SpecialLinearGroup.negOneSubgroup n R

namespace SignedQuotient

open SpecialLinearGroup

/-- The canonical quotient homomorphism `SignedQuotient n R →* PSL(n, R)`, dividing out any
remaining central roots of unity beyond `±I`. -/
noncomputable def toPSL (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] :
    SignedQuotient n R →* _root_.Matrix.ProjectiveSpecialLinearGroup n R :=
  QuotientGroup.map _ _ (MonoidHom.id _) negOneSubgroup_le_center

/-- `toPSL` sends the class of `g` modulo `{±I}` to the class of `g` modulo the full center. -/
@[simp]
theorem toPSL_mk (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] (g : _root_.Matrix.SpecialLinearGroup n R) :
    toPSL n R (QuotientGroup.mk g) = QuotientGroup.mk g := by rw [toPSL]; rfl

/-- The canonical projection `SignedQuotient n R →* PSL(n, R)` is surjective. -/
theorem toPSL_surjective (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] : Function.Surjective (toPSL n R) := fun x ↦ by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk g, toPSL_mk n R g⟩

/-- Over a commutative ring without zero divisors, `SignedQuotient (Fin 2) R` is canonically
isomorphic to `PSL₂(R)`. -/
noncomputable def equivPSL (R : Type*) [CommRing R] [NoZeroDivisors R] :
    SignedQuotient (Fin 2) R ≃* PSL(2, R) :=
  QuotientGroup.quotientMulEquivOfEq negOneSubgroup_eq_center

/-- `equivPSL` maps the class of `g` modulo `{±I}` to the class of `g` in `PSL₂(R)`. -/
@[simp]
theorem equivPSL_mk (R : Type*) [CommRing R] [NoZeroDivisors R] (g : SL(2, R)) :
    equivPSL R (QuotientGroup.mk g) = QuotientGroup.mk g := by rw [equivPSL]; rfl

/-- Extension of scalars on signed quotients `SL(n, R) ⧸ {±I} →* SL(n, S) ⧸ {±I}`. -/
noncomputable def map {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Fact (Even (Fintype.card n))] (f : R →+* S) :
    SignedQuotient n R →* SignedQuotient n S :=
  QuotientGroup.map (negOneSubgroup n R) (negOneSubgroup n S)
    (_root_.Matrix.SpecialLinearGroup.map f) fun _ hg ↦ by
      rw [Subgroup.mem_comap, mem_negOneSubgroup_iff]
      rcases mem_negOneSubgroup_iff.mp hg with rfl | rfl
      · exact Or.inl (map_one _)
      · exact Or.inr (by ext i j; by_cases hij : i = j <;> simp [hij])

/-- `SignedQuotient.map f` acts on coset representatives by entrywise application of `f`. -/
@[simp]
theorem map_mk {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Fact (Even (Fintype.card n))] (f : R →+* S) (g : _root_.Matrix.SpecialLinearGroup n R) :
    map f (QuotientGroup.mk g) = QuotientGroup.mk (_root_.Matrix.SpecialLinearGroup.map f g) := by
  rw [map]; rfl

/-- Extension of scalars by the identity ring homomorphism is the identity on signed quotients. -/
@[simp]
theorem map_id (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] :
    map (n := n) (RingHom.id R) = MonoidHom.id (SignedQuotient n R) := by ext g; simp

/-- Extension of scalars on signed quotients respects composition of ring homomorphisms. -/
@[simp]
theorem map_comp {n R S T : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [CommRing T] [Fact (Even (Fintype.card n))] (f : R →+* S) (g : S →+* T) :
    (map (n := n) g).comp (map (n := n) f) = map (n := n) (g.comp f) := by ext x; rfl

end SignedQuotient

end TauCeti.Matrix
