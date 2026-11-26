/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The `{±I}` subgroup and signed quotient `SL(n, R) ⧸ {±I}`

For an even-rank special linear group `SL(n, R)` over a commutative ring `R`, the scalar matrix `-I`
generates the central subgroup `{±I} = Subgroup.zpowers (-1)`. Over rings with zero divisors (such
as `ZMod 8` or `ZMod 12`), the full center `Z(SL(n, R))` can strictly contain `{±I}`; the **signed
quotient** `TauCeti.Matrix.SignedQuotient n R = SL(n, R) ⧸ Subgroup.zpowers (-1)` retains the
extra central roots of unity and maps surjectively onto `PSL(n, R)` (`toPSL`), agreeing canonically
with `PSL(2, R)` when `R` has no zero divisors (`equivPSL`). Extension of scalars along `R →+* S`
is functorial (`map`, `map_id`, `map_comp`).
-/

public section

open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [Fact (Even (Fintype.card n))]

/-- The subgroup `{±I} = Subgroup.zpowers (-1)` lies inside the center of `SL(n, R)`. -/
theorem zpowers_neg_one_le_center :
    Subgroup.zpowers (-1 : _root_.Matrix.SpecialLinearGroup n R) ≤
      Subgroup.center (_root_.Matrix.SpecialLinearGroup n R) :=
  Subgroup.zpowers_le.mpr <| Subgroup.mem_center_iff.mpr fun _ ↦ by rw [neg_one_mul, mul_neg_one]

end TauCeti.Matrix.SpecialLinearGroup

namespace TauCeti.Matrix

/-- **The signed special linear quotient `SL(n, R) ⧸ {±I}`** (`Q_N` when `n = Fin 2` and
`R = ZMod N`), the quotient by `{±I}` through which `PSL₂(ℤ) = SL₂(ℤ) ⧸ {±I}` acts at level `N`. -/
abbrev SignedQuotient (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]
    [Fact (Even (Fintype.card n))] : Type _ :=
  _root_.Matrix.SpecialLinearGroup n R ⧸
    (Subgroup.zpowers (-1) : Subgroup (_root_.Matrix.SpecialLinearGroup n R))

namespace SignedQuotient

open SpecialLinearGroup

/-- The canonical quotient homomorphism `SignedQuotient n R →* PSL(n, R)`, dividing out any
remaining central roots of unity beyond `±I`. -/
noncomputable def toPSL (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] :
    SignedQuotient n R →* _root_.Matrix.ProjectiveSpecialLinearGroup n R :=
  QuotientGroup.map _ _ (MonoidHom.id _) zpowers_neg_one_le_center

/-- `toPSL` sends the class of `g` modulo `{±I}` to the class of `g` modulo the full center. -/
@[simp]
theorem toPSL_mk (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] (g : _root_.Matrix.SpecialLinearGroup n R) :
    toPSL n R (QuotientGroup.mk g) = QuotientGroup.mk g := by rw [toPSL]; rfl

/-- The canonical projection `SignedQuotient n R →* PSL(n, R)` is surjective. -/
theorem toPSL_surjective (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] : Function.Surjective (toPSL n R) :=
  QuotientGroup.map_surjective_of_surjective _ _ (MonoidHom.id _)
    (QuotientGroup.mk'_surjective _) _

/-- Over a commutative ring without zero divisors, `SignedQuotient (Fin 2) R` is canonically
isomorphic to `PSL₂(R)`. -/
noncomputable def equivPSL (R : Type*) [CommRing R] [NoZeroDivisors R] :
    SignedQuotient (Fin 2) R ≃* PSL(2, R) :=
  QuotientGroup.quotientMulEquivOfEq
    _root_.Matrix.SpecialLinearGroup.center_eq_zpowers_neg_one.symm

/-- `equivPSL` maps the class of `g` modulo `{±I}` to the class of `g` in `PSL₂(R)`. -/
@[simp]
theorem equivPSL_mk (R : Type*) [CommRing R] [NoZeroDivisors R] (g : SL(2, R)) :
    equivPSL R (QuotientGroup.mk g) = QuotientGroup.mk g := by rw [equivPSL]; rfl

private theorem map_zpowers_neg_one_le {n R S : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [CommRing S] [Fact (Even (Fintype.card n))] (f : R →+* S) :
    (Subgroup.zpowers (-1 : _root_.Matrix.SpecialLinearGroup n R)) ≤
      (Subgroup.zpowers (-1 : _root_.Matrix.SpecialLinearGroup n S)).comap
        (_root_.Matrix.SpecialLinearGroup.map f) :=
  Subgroup.map_le_iff_le_comap.mp <| by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    rw [show _root_.Matrix.SpecialLinearGroup.map f (-1) = -1 by
      ext i j; by_cases hij : i = j <;> simp [hij]]
    exact Subgroup.mem_zpowers (-1)

/-- Extension of scalars on signed quotients `SL(n, R) ⧸ {±I} →* SL(n, S) ⧸ {±I}`. -/
noncomputable def map {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Fact (Even (Fintype.card n))] (f : R →+* S) :
    SignedQuotient n R →* SignedQuotient n S :=
  QuotientGroup.map (Subgroup.zpowers (-1)) (Subgroup.zpowers (-1))
    (_root_.Matrix.SpecialLinearGroup.map f) (map_zpowers_neg_one_le f)

/-- `SignedQuotient.map f` acts on coset representatives by entrywise application of `f`. -/
@[simp]
theorem map_mk {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Fact (Even (Fintype.card n))] (f : R →+* S) (g : _root_.Matrix.SpecialLinearGroup n R) :
    map f (QuotientGroup.mk g) = QuotientGroup.mk (_root_.Matrix.SpecialLinearGroup.map f g) := by
  rw [map]; rfl

/-- If `SL(n, R) →* SL(n, S)` along `f` is surjective, then `SignedQuotient.map f` is surjective. -/
theorem map_surjective {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Fact (Even (Fintype.card n))] {f : R →+* S}
    (hf : Function.Surjective (_root_.Matrix.SpecialLinearGroup.map f :
      _root_.Matrix.SpecialLinearGroup n R →* _root_.Matrix.SpecialLinearGroup n S)) :
    Function.Surjective (map (n := n) f) :=
  QuotientGroup.map_surjective_of_surjective _ _ _ ((QuotientGroup.mk'_surjective _).comp hf) _

/-- Extension of scalars by the identity ring homomorphism is the identity on signed quotients. -/
@[simp]
theorem map_id (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]
    [Fact (Even (Fintype.card n))] :
    map (n := n) (RingHom.id R) = MonoidHom.id (SignedQuotient n R) := by
  rw [map]
  simpa only [_root_.Matrix.SpecialLinearGroup.map_id] using
    QuotientGroup.map_id (Subgroup.zpowers (-1 : _root_.Matrix.SpecialLinearGroup n R))

/-- Extension of scalars on signed quotients respects composition of ring homomorphisms. -/
@[simp]
theorem map_comp {n R S T : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [CommRing T] [Fact (Even (Fintype.card n))] (f : R →+* S) (g : S →+* T) :
    (map (n := n) g).comp (map (n := n) f) = map (n := n) (g.comp f) := by
  rw [map, map, map]
  simpa only [_root_.Matrix.SpecialLinearGroup.map_comp_map] using
    QuotientGroup.map_comp_map
      (Subgroup.zpowers (-1 : _root_.Matrix.SpecialLinearGroup n R))
      (Subgroup.zpowers (-1 : _root_.Matrix.SpecialLinearGroup n S))
      (Subgroup.zpowers (-1 : _root_.Matrix.SpecialLinearGroup n T))
      (_root_.Matrix.SpecialLinearGroup.map f) (_root_.Matrix.SpecialLinearGroup.map g)
      (map_zpowers_neg_one_le f) (map_zpowers_neg_one_le g)
      (by simpa only [← _root_.Matrix.SpecialLinearGroup.map_comp_map] using
        map_zpowers_neg_one_le (g.comp f))

end SignedQuotient

end TauCeti.Matrix
