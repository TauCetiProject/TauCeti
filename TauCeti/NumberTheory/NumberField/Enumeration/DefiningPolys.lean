/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.NumberField.Index.PowerBasis
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.NumberTheory.NumberField.Minpoly

/-!
# The defining polynomials of a number field

A *defining polynomial* of a number field `K` is the minimal polynomial over `ℤ` of an algebraic
integer that generates `K` over `ℚ`. Equivalently, it is a monic integer polynomial of degree
`[K : ℚ]` with a root in `K` generating `K`. A number field has infinitely many defining
polynomials (`X ^ 2 - 5` and `X ^ 2 - X - 1` both define `ℚ(√5)`), and tables of number fields
name each field by choosing one of them canonically, such as the polynomial returned by PARI's
`polredabs`. This file sets up the set of defining polynomials that such a choice minimizes over.

The set of defining polynomials is an isomorphism invariant that classifies number fields: two
number fields have the same defining polynomials exactly when they are isomorphic, and a single
common defining polynomial already forces an isomorphism, because each field is then the stem
field `ℚ[X] / (P)`.

## Main definitions

* `TauCeti.NumberField.definingPolys K`: the minimal polynomials over `ℤ` of the integral
  primitive elements of `K`.

## Main results

* `TauCeti.NumberField.mem_definingPolys_iff`: `P` is a defining polynomial of `K` if and only if
  it is monic of degree `[K : ℚ]` with a root in `K` generating `K` over `ℚ`.
* `TauCeti.NumberField.irreducible_of_mem_definingPolys`,
  `TauCeti.NumberField.irreducible_map_of_mem_definingPolys`: defining polynomials are
  irreducible over `ℤ` and over `ℚ`.
* `TauCeti.NumberField.definingPolys_nonempty`: every number field has a defining polynomial.
* `TauCeti.NumberField.mem_definingPolys_adjoinRoot`: a monic integer polynomial that is
  irreducible over `ℚ` defines its stem field `ℚ[X] / (P)`.
* `TauCeti.NumberField.nonempty_algEquiv_adjoinRoot_of_mem_definingPolys`: a number field is
  isomorphic to the stem field of each of its defining polynomials.
* `TauCeti.NumberField.definingPolys_eq_iff_nonempty_algEquiv`: two number fields have the same
  defining polynomials if and only if they are isomorphic.
* `TauCeti.NumberField.definingPolys_rat`: the defining polynomials of `ℚ` are the `X - n` for
  `n : ℤ`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, Springer 1993,
  §4.4 (defining polynomials and `polredabs`).
* The LMFDB Collaboration, knowl `nf.polredabs`.
-/

public section

open Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] {P : ℤ[X]}

variable (K) in
/-- The defining polynomials of a number field `K`: the minimal polynomials over `ℤ` of the
algebraic integers generating `K` over `ℚ`. -/
noncomputable def definingPolys : Set ℤ[X] :=
  Set.range fun θ : IntegralPrimitiveElement K ↦ minpoly ℤ θ.val

/-- A polynomial is a defining polynomial of `K` if and only if it is the minimal polynomial of an
integral primitive element of `K`. -/
theorem mem_definingPolys : P ∈ definingPolys K ↔
    ∃ θ : IntegralPrimitiveElement K, minpoly ℤ θ.val = P :=
  Set.mem_range

/-- The minimal polynomial of an integral primitive element is a defining polynomial. -/
@[simp]
theorem minpoly_mem_definingPolys (θ : IntegralPrimitiveElement K) :
    minpoly ℤ θ.val ∈ definingPolys K :=
  Set.mem_range_self θ

/-- **Defining polynomials, intrinsically.** A polynomial `P` defines `K` if and only if it is
monic of degree `[K : ℚ]` and has a root in `K` generating `K` over `ℚ`. -/
theorem mem_definingPolys_iff : P ∈ definingPolys K ↔
    P.Monic ∧ P.natDegree = Module.finrank ℚ K ∧
      ∃ x : K, aeval x P = 0 ∧ Algebra.adjoin ℚ {x} = ⊤ := by
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨minpoly.monic θ.val.isIntegral, θ.natDegree_minpoly, θ.val, ?_, θ.property⟩
    rw [← aeval_minpoly_rat_eq_aeval_minpoly_int]
    exact minpoly.aeval ℚ _
  · rintro ⟨hP, hdeg, x, hx, hgen⟩
    let θ : IntegralPrimitiveElement K := ⟨⟨x, P, hP, hx⟩, hgen⟩
    refine mem_definingPolys.mpr
      ⟨θ, (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic θ.val.isIntegral) hP ?_ ?_).symm⟩
    · rw [← _root_.NumberField.RingOfIntegers.minpoly_coe]
      exact minpoly.isIntegrallyClosed_dvd ⟨P, hP, hx⟩ hx
    · rw [hdeg, θ.natDegree_minpoly]

/-- A defining polynomial is monic. -/
theorem monic_of_mem_definingPolys (hP : P ∈ definingPolys K) : P.Monic :=
  (mem_definingPolys_iff.mp hP).1

/-- A defining polynomial of `K` has degree `[K : ℚ]`. -/
theorem natDegree_of_mem_definingPolys (hP : P ∈ definingPolys K) :
    P.natDegree = Module.finrank ℚ K :=
  (mem_definingPolys_iff.mp hP).2.1

/-- A defining polynomial is irreducible over `ℤ`. -/
theorem irreducible_of_mem_definingPolys (hP : P ∈ definingPolys K) : Irreducible P := by
  obtain ⟨θ, rfl⟩ := mem_definingPolys.mp hP
  exact minpoly.irreducible θ.val.isIntegral

/-- A defining polynomial stays irreducible over `ℚ`: it becomes the minimal polynomial over `ℚ`
of a generator of `K`. -/
theorem irreducible_map_of_mem_definingPolys (hP : P ∈ definingPolys K) :
    Irreducible (P.map (Int.castRingHom ℚ)) := by
  obtain ⟨θ, rfl⟩ := mem_definingPolys.mp hP
  rw [← algebraMap_int_eq, ← _root_.NumberField.RingOfIntegers.minpoly_rat_coe]
  exact minpoly.irreducible (IsIntegral.of_finite ℚ _)

/-- Every number field has a defining polynomial. -/
theorem definingPolys_nonempty : (definingPolys K).Nonempty :=
  Set.range_nonempty _

/-- A monic integer polynomial that is irreducible over `ℚ` defines its stem field
`ℚ[X] / (P)`, with root the class of `X`. -/
theorem mem_definingPolys_adjoinRoot (hP : P.Monic)
    [Fact (Irreducible (P.map (Int.castRingHom ℚ)))] :
    P ∈ definingPolys (AdjoinRoot (P.map (Int.castRingHom ℚ))) := by
  have hmon : (P.map (Int.castRingHom ℚ)).Monic := hP.map _
  refine mem_definingPolys_iff.mpr ⟨hP, ?_, AdjoinRoot.root _, ?_, AdjoinRoot.adjoinRoot_eq_top⟩
  · rw [(AdjoinRoot.powerBasis hmon.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
      hP.natDegree_map]
  · have hmap : P.map (algebraMap ℤ ℚ) = P.map (Int.castRingHom ℚ) := by
      rw [algebraMap_int_eq]
    rw [← aeval_map_algebraMap ℚ, hmap]
    exact (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self

/-- Two number fields sharing a defining polynomial are isomorphic: both power bases have the
same minimal polynomial over `ℚ`. -/
theorem nonempty_algEquiv_of_mem_definingPolys (hK : P ∈ definingPolys K)
    (hL : P ∈ definingPolys L) : Nonempty (K ≃ₐ[ℚ] L) := by
  obtain ⟨θ, rfl⟩ := mem_definingPolys.mp hK
  obtain ⟨η, hη⟩ := mem_definingPolys.mp hL
  refine ⟨θ.powerBasis.equivOfMinpoly η.powerBasis ?_⟩
  rw [IntegralPrimitiveElement.powerBasis_gen, IntegralPrimitiveElement.powerBasis_gen,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe, hη]

/-- **The stem field of a defining polynomial.** A number field is isomorphic over `ℚ` to
`ℚ[X] / (P)` for each of its defining polynomials `P`. The irreducibility instance making the
quotient a field always holds, by `irreducible_map_of_mem_definingPolys`. -/
theorem nonempty_algEquiv_adjoinRoot_of_mem_definingPolys
    [Fact (Irreducible (P.map (Int.castRingHom ℚ)))] (hP : P ∈ definingPolys K) :
    Nonempty (AdjoinRoot (P.map (Int.castRingHom ℚ)) ≃ₐ[ℚ] K) :=
  nonempty_algEquiv_of_mem_definingPolys
    (mem_definingPolys_adjoinRoot (monic_of_mem_definingPolys hP)) hP

/-- An isomorphism of number fields carries each defining polynomial of its source to one of its
target; `definingPolys_eq_of_algEquiv` applies it in both directions. -/
private theorem definingPolys_subset_of_algEquiv (e : K ≃ₐ[ℚ] L) :
    definingPolys K ⊆ definingPolys L := by
  intro P hP
  obtain ⟨hmon, hdeg, x, hx, hgen⟩ := mem_definingPolys_iff.mp hP
  refine mem_definingPolys_iff.mpr ⟨hmon, hdeg.trans e.toLinearEquiv.finrank_eq, e x, ?_, ?_⟩
  · rw [← AlgEquiv.restrictScalars_apply ℤ, ← AlgEquiv.coe_toAlgHom, aeval_algHom_apply, hx,
      map_zero]
  · rw [← Set.image_singleton, ← AlgEquiv.coe_toAlgHom, Algebra.adjoin_image, hgen,
      Algebra.map_top, AlgHom.range_eq_top]
    exact e.surjective

/-- An isomorphism of number fields carries the defining polynomials of one onto those of the
other. -/
theorem definingPolys_eq_of_algEquiv (e : K ≃ₐ[ℚ] L) : definingPolys K = definingPolys L :=
  (definingPolys_subset_of_algEquiv e).antisymm (definingPolys_subset_of_algEquiv e.symm)

/-- **Defining polynomials classify number fields.** Two number fields have the same defining
polynomials if and only if they are isomorphic over `ℚ`. -/
theorem definingPolys_eq_iff_nonempty_algEquiv :
    definingPolys K = definingPolys L ↔ Nonempty (K ≃ₐ[ℚ] L) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ definingPolys_eq_of_algEquiv e⟩
  obtain ⟨P, hP⟩ := definingPolys_nonempty (K := K)
  exact nonempty_algEquiv_of_mem_definingPolys hP (h ▸ hP)

/-- The defining polynomials of `ℚ` are the monic linear polynomials `X - n` with `n : ℤ`. In
particular `X` defines `ℚ` even though its root is `0`. -/
theorem definingPolys_rat : definingPolys ℚ = Set.range fun n : ℤ ↦ X - C n := by
  ext P
  rw [mem_definingPolys_iff, Module.finrank_self, Set.mem_range]
  constructor
  · rintro ⟨hP, hdeg, -⟩
    refine ⟨-P.coeff 0, ?_⟩
    rw [hP.eq_X_add_C hdeg, coeff_add, coeff_X_zero, coeff_C_zero, zero_add, map_neg,
      sub_neg_eq_add]
  · rintro ⟨n, rfl⟩
    refine ⟨monic_X_sub_C _, natDegree_X_sub_C _, n, by simp, ?_⟩
    exact eq_top_iff.mpr fun y _ ↦ Subalgebra.algebraMap_mem _ y

end TauCeti.NumberField
