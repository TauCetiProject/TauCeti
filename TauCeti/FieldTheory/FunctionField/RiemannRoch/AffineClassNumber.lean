/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.AffineModel
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.ClassNumber

/-!
# The ideal class group of an affine model of a function field

`TauCeti.FieldTheory.FunctionField.RiemannRoch.ClassNumber` proves that the degree-zero divisor
class group `Cl⁰(F)` of an algebraic function field with a *finite* constant field is finite, and
`TauCeti.FieldTheory.FunctionField.Divisor.AffineModel` exhibits the ideal class group of an
affine model `R` of `F / k` as a quotient of the full divisor class group,

`⟨[P] : P ∤ R⟩ → Cl(F) → ClassGroup R → 0`.

This file joins the two: **the ideal class group of every affine model of an algebraic function
field with a finite constant field is finite.**

The transfer is not immediate, because `Cl(F)` itself is infinite — the degree map
`deg : Cl(F) → ℤ` has finite kernel `Cl⁰(F)` but nonzero image.  What kills the degree is that a
model always has a place `P` at infinity (`TauCeti.Place.exists_algebraMap_notMem_integers`),
whose class dies in `ClassGroup R`.  Correcting a preimage by a multiple of `[P]` therefore moves
its degree into `[0, deg P)` without changing its image, so `ClassGroup R` is the image of the
finitely many degree classes of degree `0, …, deg P − 1`, each a coset of the finite group
`Cl⁰(F)`.

There is no separability hypothesis and no chosen rational subfield: `R` is any Dedekind
`k`-subalgebra of `F` with fraction field `F`.  Mathlib's
`FunctionField.RingOfIntegers.instFintypeClassGroup` is the special case `R = ` the integral
closure of `𝔽_q[X]` in `F`, and it is proved by a different route (Minkowski-style counting
through `ClassGroup.fintypeOfAdmissibleOfFinite`) under the extra hypothesis that `F` is separable
over `𝔽_q(X)`.

The rational function field closes the file as a worked instance: the only place of `k(x)`
infinite on the model `k[X]` is the place at infinity, which is rational, so
`TauCeti.Divisor.degreeZeroClassGroupEquiv` applies and identifies `Cl⁰(k(x))` with
`ClassGroup k[X]`.  The latter vanishes because `k[X]` is a principal ideal domain, so **the
rational function field has class number one**: this is Stichtenoth's Example 5.1 read through
the affine bridge rather than through the explicit description of the divisor classes of `k(x)`
(which `TauCeti.Divisor.linearlyEquivalent_zsmul_ofPoint_infty` also gives directly), and it is
the acceptance test that the bridge is set up correctly.

## Main results

* `TauCeti.Divisor.finite_preimage_degreeClass`: over a finite constant field the preimage under
  `deg : Cl(F) → ℤ` of a finite set of integers is finite — each fibre is a coset of `Cl⁰(F)`.
* `TauCeti.Divisor.finite_classGroup`: **the ideal class group of an affine model of an algebraic
  function field with a finite constant field is finite.**
* `TauCeti.Divisor.card_classGroup_dvd_classNumber`: when some place infinite on the model is
  rational, the class number of the model divides the class number of `F / k`.
* `TauCeti.Divisor.ker_degreeClass_ratFunc_eq_bot` and `TauCeti.Divisor.classNumber_ratFunc`:
  `Cl⁰(k(x)) = 0` and `h_{k(x)} = 1`, through the affine bridge at the model `k[X]`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.4 and V.1.
-/

public section

open IsDedekindDomain Polynomial

namespace TauCeti

open AlgebraicGeometry AlgebraicGeometry.WeilDivisor

universe u v w

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {R : Type w} [CommRing R] [IsDedekindDomain R] [Algebra k R] [Algebra R F]
  [IsScalarTower k R F] [IsFractionRing R F]

namespace Divisor

/-! ### Divisor classes of bounded degree -/

/-- Over a finite constant field a fibre of the degree map on divisor classes is finite: it is
empty or a coset of `Cl⁰(F)`, which is finite by
`TauCeti.Divisor.finite_ker_degreeClass`. -/
theorem finite_preimage_degreeClass_singleton (hF : IsFunctionField k F) [Finite k] (n : ℤ) :
    (⇑(degreeClass hF) ⁻¹' {n}).Finite := by
  have hker : Finite (degreeClass hF).ker := finite_ker_degreeClass hF
  rcases Set.eq_empty_or_nonempty (⇑(degreeClass hF) ⁻¹' {n}) with hempty | ⟨c₀, hc₀⟩
  · rw [hempty]
    exact Set.finite_empty
  · refine Set.Finite.subset
      (Set.Finite.image (· + c₀) (Set.toFinite ((degreeClass hF).ker : Set _))) fun c hc ↦ ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc hc₀
    exact ⟨c - c₀, by simp [AddMonoidHom.mem_ker, hc, hc₀], by simp⟩

/-- Over a finite constant field only finitely many divisor classes have degree in a given finite
set of integers. -/
theorem finite_preimage_degreeClass (hF : IsFunctionField k F) [Finite k] {s : Set ℤ}
    (hs : s.Finite) : (⇑(degreeClass hF) ⁻¹' s).Finite := by
  have hsplit : ⇑(degreeClass hF) ⁻¹' s = ⋃ n ∈ s, ⇑(degreeClass hF) ⁻¹' {n} := by
    ext c
    simp
  rw [hsplit]
  exact hs.biUnion fun n _ ↦ finite_preimage_degreeClass_singleton hF n

/-! ### Finiteness of the ideal class group of a model -/

variable (R) in
/-- **The ideal class group of an affine model of an algebraic function field with a finite
constant field is finite** — the affine half of Stichtenoth's Proposition 5.1.3.  Every ideal
class of the model comes from a divisor class whose degree lies in `[0, deg P)` for a place `P` at
infinity (`TauCeti.Divisor.exists_degreeClass_mem_Ico_and_classGroupHom_eq`), and only finitely
many divisor classes have degree in that range.

No separability hypothesis and no chosen rational subfield are needed: `R` is an arbitrary
Dedekind `k`-subalgebra of `F` with fraction field `F`. -/
theorem finite_classGroup (hF : IsFunctionField k F) [Finite k] : Finite (ClassGroup R) := by
  obtain ⟨P, hP⟩ := Place.exists_algebraMap_notMem_integers k F R hF
  have hfin : Finite (Additive (ClassGroup R)) := by
    refine Set.finite_univ_iff.mp (Set.Finite.subset
      (Set.Finite.image (classGroupHom R hF)
        (finite_preimage_degreeClass hF (Set.finite_Ico (0 : ℤ) (P.degree : ℤ)))) fun x _ ↦ ?_)
    obtain ⟨c, hc, hcx⟩ := exists_degreeClass_mem_Ico_and_classGroupHom_eq R hF hP x
    exact ⟨c, hc, hcx⟩
  exact Finite.of_equiv _ (Additive.ofMul (α := ClassGroup R)).symm

variable (R) in
/-- **With a rational place at infinity, the class number of the model divides the class number of
`F / k`**: over a finite constant field the ideal class group of the model is then a quotient of
the finite group `Cl⁰(F)` (`TauCeti.Divisor.classGroupHom_comp_subtype_surjective`). -/
theorem card_classGroup_dvd_classNumber (hF : IsFunctionField k F) [Finite k] {P : Place k F}
    (hP : ∃ r : R, algebraMap R F r ∉ P.integers) (hdeg : P.degree = 1) :
    Nat.card (ClassGroup R) ∣ classNumber hF := by
  have hker : Finite (degreeClass hF).ker := finite_ker_degreeClass hF
  rw [Nat.card_congr (Additive.ofMul (α := ClassGroup R)), classNumber_def]
  exact AddSubgroup.card_dvd_of_surjective _
    (classGroupHom_comp_subtype_surjective R hF hP hdeg)

/-! ### The rational function field -/

section RatFunc

variable (k)

/-- **The degree-zero divisor class group of `k(x)` is the ideal class group of `k[X]`**: the
model `k[X]` has a single place at infinity
(`TauCeti.Place.exists_algebraMap_notMem_integers_iff_eq_infty`), and that place is rational. -/
noncomputable def degreeZeroClassGroupEquivPolynomial :
    (degreeClass (IsFunctionField.ratFunc k)).ker ≃+ Additive (ClassGroup (k[X])) :=
  degreeZeroClassGroupEquiv (k[X]) (IsFunctionField.ratFunc k)
    (Set.ext fun _ ↦ Place.exists_algebraMap_notMem_integers_iff_eq_infty)
    (Place.degree_infty k)

/-- **Every degree-zero divisor class of the rational function field is trivial**: through the
affine bridge it is an ideal class of `k[X]`, and `k[X]` is a principal ideal domain. -/
theorem ker_degreeClass_ratFunc_eq_bot :
    (degreeClass (IsFunctionField.ratFunc k)).ker = ⊥ := by
  have hsub : Subsingleton (ClassGroup (k[X])) :=
    Fintype.card_le_one_iff_subsingleton.mp (card_classGroup_eq_one (R := k[X])).le
  have hadd : Subsingleton (Additive (ClassGroup (k[X]))) :=
    inferInstanceAs (Subsingleton (ClassGroup (k[X])))
  have : Subsingleton (degreeClass (IsFunctionField.ratFunc k)).ker :=
    (degreeZeroClassGroupEquivPolynomial k).toEquiv.subsingleton
  exact AddSubgroup.eq_bot_of_subsingleton _

/-- **The rational function field has class number one** (Stichtenoth, Example 5.1). -/
theorem classNumber_ratFunc : classNumber (IsFunctionField.ratFunc k) = 1 := by
  rw [classNumber_def, ker_degreeClass_ratFunc_eq_bot, AddSubgroup.card_bot]

end RatFunc

end Divisor

end TauCeti
