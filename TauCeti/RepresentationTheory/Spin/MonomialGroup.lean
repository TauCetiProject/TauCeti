/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import TauCeti.LinearAlgebra.CliffordAlgebra.MonomialGroup
public import TauCeti.RepresentationTheory.Induction.Restriction
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
-- Non-public: `IsPrimitiveRoot.neg_one_of_two_ne_zero` and `rootsOfUnity.isCyclic` supply the
-- square roots of unity of a field in which `2` is invertible.
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The characters of the group of signed monomials on which `ε` acts trivially

Let `b` be an orthogonal basis of a quadratic module `(M, Q)` whose generators square to `±1`,
indexed by a type with `n` elements. The group `CliffordAlgebra.monomialGroup Q b` of signed
monomials `±e_s`, its central element `ε = -1`, the sign subgroup `⟨ε⟩` it generates and the
quotient by that subgroup are built in `TauCeti.LinearAlgebra.CliffordAlgebra.MonomialGroup`:
over a nontrivial coefficient ring in which `2` is invertible the group has `2 ^ (n + 1)` elements,
the sign subgroup has two, and the quotient is commutative with every element of order dividing
two and has `2 ^ n` elements. Every count below inherits those two hypotheses on the coefficient
ring `R`; in characteristic two `ε = 1`, the sign subgroup is trivial and the counts fail.

This file turns those group-theoretic facts into representation theory. A representation of the
group of signed monomials on which `ε` acts by the identity is the same as a representation of the
quotient. Two halves of the `ε = +1` classification are proved here: over an algebraically closed
field such a representation is one-dimensional whenever it is irreducible, because the quotient is
commutative; and over any field `F` in which `2` is invertible the quotient has exactly `2 ^ n`
characters, each of which carries such a representation on a line. The two halves are not assembled
into a bijection here, so nothing below asserts that the characters exhaust the `ε`-trivial
irreducibles up to isomorphism. The field of the representations and the coefficient ring of the
Clifford algebra are independent. The complementary sector, where `ε` acts by `-1`, is the one
`CliffordAlgebra.monomialGroupLift` identifies with the Clifford modules.

## Main results

* `CliffordAlgebra.finrank_eq_one_of_monomialGroupEpsilon_eq_one`: over an algebraically closed
  field, an irreducible representation on which `ε` acts trivially is a line, and
  `CliffordAlgebra.ofLinearCharacter_comp_mk_apply_monomialGroupEpsilon` goes the other way, from a
  character of the quotient to a representation on which `ε` acts trivially.
* `CliffordAlgebra.natCard_monoidHom_quotient_monomialGroupSign` and
  `CliffordAlgebra.natCard_monomialGroupChar_monomialGroupEpsilon_eq_one`: for a finite orthogonal
  basis of `n` generators squaring to `±1` over a nontrivial ring in which `2` is invertible, and
  with values in a field in which `2` is invertible, there are exactly `2 ^ n` characters of the
  quotient, equivalently `2 ^ n` characters of the group of signed monomials sending `ε` to `1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §3.1 for the
  characters of a finite abelian group.
-/

public section

namespace CliffordAlgebra

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}
  (v : I → M)

/-! ### Irreducible representations on which `ε` acts trivially -/

/-- **An irreducible representation of the group of signed monomials on which `ε` acts trivially
is a line**, over an algebraically closed field. Such a representation factors through the quotient
by the sign subgroup, which is commutative, so Schur's lemma leaves no room for more than one
dimension. -/
theorem finrank_eq_one_of_monomialGroupEpsilon_eq_one
    (hv : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) {F W : Type*} [Field F] [IsAlgClosed F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F (monomialGroup Q v) W) [ρ.IsIrreducible]
    (hρ : ρ (monomialGroupEpsilon Q v) = 1) :
    Module.finrank F W = 1 := by
  have htriv : Representation.IsTrivial (ρ.comp (monomialGroupSign Q v).subtype) := by
    refine ⟨fun g ↦ ?_⟩
    rw [← Module.End.one_eq_id]
    rcases (mem_monomialGroupSign_iff v).mp g.2 with hg | hg
    · simp [hg]
    · simp [hg, hρ]
  have : IsMulCommutative (monomialGroup Q v ⧸ monomialGroupSign Q v) :=
    isMulCommutative_quotient_monomialGroupSign v hv
  have : (ρ.ofQuotient (monomialGroupSign Q v)).IsIrreducible :=
    (Representation.isIrreducible_ofQuotient_iff ρ (monomialGroupSign Q v)).mpr ‹ρ.IsIrreducible›
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    (ρ.ofQuotient (monomialGroupSign Q v))

/-- **Each character of the quotient by the sign subgroup gives a representation of the group of
signed monomials on which `ε` acts trivially.** The representation is the line carrying the
character of the class, `Representation.ofLinearCharacter`; over a field it is irreducible by
`Representation.isIrreducible_ofLinearCharacter`, and distinct characters give distinct
representations by `Representation.ofLinearCharacter_injective`. The identity itself needs no more
of the coefficients than a commutative semiring. -/
theorem ofLinearCharacter_comp_mk_apply_monomialGroupEpsilon {F : Type*} [CommSemiring F]
    (χ : (monomialGroup Q v ⧸ monomialGroupSign Q v) →* Fˣ) :
    Representation.ofLinearCharacter (χ.comp (QuotientGroup.mk' (monomialGroupSign Q v)))
      (monomialGroupEpsilon Q v) = 1 := by
  have hε := (QuotientGroup.eq_one_iff (N := monomialGroupSign Q v)
    (monomialGroupEpsilon Q v)).mpr (monomialGroupEpsilon_mem_monomialGroupSign v)
  refine LinearMap.ext fun x ↦ ?_
  simp [hε]

/-! ### The characters of the quotient -/

variable [Invertible (2 : R)] [LinearOrder I] {b : Module.Basis I R M}

/-- **The quotient by the sign subgroup has exactly `2 ^ n` characters** with values in a field in
which `2` is invertible: it is a finite commutative group of exponent dividing two with `2 ^ n`
elements, and such a group is isomorphic to its character group. -/
theorem natCard_monoidHom_quotient_monomialGroupSign [Fintype I] [Nontrivial R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    {F : Type*} [Field F] (hF : (2 : F) ≠ 0) :
    Nat.card ((monomialGroup Q b ⧸ monomialGroupSign Q b) →* Fˣ) = 2 ^ Fintype.card I := by
  have hortho : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j) := fun _ _ hij ↦
    QuadraticMap.associated_isOrtho.mp (hb hij)
  have : Finite (monomialGroup Q b) := finite_monomialGroup hb hQ
  have : HasEnoughRootsOfUnity F 2 :=
    { prim := ⟨-1, IsPrimitiveRoot.neg_one_of_two_ne_zero hF⟩, cyc := inferInstance }
  have : HasEnoughRootsOfUnity F
      (Monoid.exponent (monomialGroup Q b ⧸ monomialGroupSign Q b)) :=
    HasEnoughRootsOfUnity.of_dvd F (exponent_quotient_monomialGroupSign_dvd_two hb hQ)
  let hG : Group (monomialGroup Q b ⧸ monomialGroupSign Q b) := inferInstance
  let : CommGroup (monomialGroup Q b ⧸ monomialGroupSign Q b) :=
    { hG with
      mul_comm := isMulCommutative_iff.mp (isMulCommutative_quotient_monomialGroupSign b hortho) }
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ F,
    natCard_quotient_monomialGroupSign hb hQ]

/-- **The group of signed monomials has exactly `2 ^ n` characters sending `ε` to `1`**, with
values in a field in which `2` is invertible: they are the characters of the quotient by the sign
subgroup. -/
theorem natCard_monomialGroupChar_monomialGroupEpsilon_eq_one [Fintype I] [Nontrivial R]
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    {F : Type*} [Field F] (hF : (2 : F) ≠ 0) :
    Nat.card {χ : monomialGroup Q b →* Fˣ // χ (monomialGroupEpsilon Q b) = 1} =
      2 ^ Fintype.card I := by
  rw [Nat.card_congr (monomialGroupSignCharEquiv (Q := Q) b),
    natCard_monoidHom_quotient_monomialGroupSign hb hQ hF]

end CliffordAlgebra
