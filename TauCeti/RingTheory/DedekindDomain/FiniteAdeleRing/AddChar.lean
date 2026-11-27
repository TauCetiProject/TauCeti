/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Additive characters of the finite adeles trivial on the integral finite adeles

Let `R` be a Dedekind domain with fraction field `K`, `𝔸_f` its finite adele ring and
`Ô = ∏_v 𝒪_v` the integral finite adeles. By strong approximation every finite adele is the
diagonal image of an element of `K` plus an element of `Ô`, and `K ∩ Ô = R`
(`IsDedekindDomain.FiniteAdeleRing.quotientEquivQuotientIntegralAdeles`). Hence an additive
character `χ` of `K` that is trivial on `R` extends in exactly one way to an additive character
of `𝔸_f` that is trivial on `Ô`: the value at `a = x + o`, with `x ∈ K` and `o ∈ Ô`, is `χ x`
(`IsDedekindDomain.FiniteAdeleRing.extendAddChar`).

The extension is constant on the cosets of the open subgroup `Ô`, so it is locally constant and
continuous for every topology on the values. For a number field and the character
`x ↦ exp (2πi Tr x)` this is the finite part of the standard additive character of the adeles.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.extendAddChar χ hχ`: the extension of a character `χ` of `K`
  trivial on `R` to a character of `𝔸_f` trivial on `Ô`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.extendAddChar_apply_of_sub_mem_integralAdeles`: its value at
  `a` is `χ x` for every `x ∈ K` with `x - a ∈ Ô`.
* `IsDedekindDomain.FiniteAdeleRing.extendAddChar_algebraMap`: it extends `χ`.
* `IsDedekindDomain.FiniteAdeleRing.extendAddChar_eq_one_of_mem_integralAdeles`: it is trivial on
  `Ô`.
* `IsDedekindDomain.FiniteAdeleRing.eq_extendAddChar`: it is the only character of `𝔸_f` with
  these two properties.
* `IsDedekindDomain.FiniteAdeleRing.isLocallyConstant_extendAddChar`,
  `IsDedekindDomain.FiniteAdeleRing.continuous_extendAddChar`: it is locally constant, hence
  continuous.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), in
  J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter XV, §3.

The construction of the extension by a representative chosen by strong approximation, and its
triviality on the integral finite adeles, are adapted from grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC),
`src/Lib/Adelic/Adeles/AdditiveCharacter.lean` (`New.ψf`), stated there for the trace character
of a number field; here they are generalized to any additive character of the fraction field of a
Dedekind domain that is trivial on the ring.
-/

public section

namespace IsDedekindDomain.FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {M : Type*} [Monoid M]

/-- A character of `K` trivial on `R` takes the same value at two elements of `K` whose diagonal
images differ by an integral finite adele: their difference lies in `R`. -/
private theorem addChar_eq_of_algebraMap_sub_mem {χ : AddChar K M}
    (hχ : ∀ r : R, χ (algebraMap R K r) = 1) {x y : K}
    (h : algebraMap K (FiniteAdeleRing R K) x - algebraMap K (FiniteAdeleRing R K) y ∈
      integralAdeles R K) :
    χ x = χ y := by
  rw [← map_sub, algebraMap_mem_integralAdeles_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [← sub_add_cancel x y, ← hr, AddChar.map_add_eq_mul, hχ, one_mul]

/-- An element of `K` whose diagonal image differs from the finite adele `a` by an integral finite
adele, chosen by strong approximation. -/
private noncomputable def rep (a : FiniteAdeleRing R K) : K :=
  (exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem).choose

private theorem algebraMap_rep_sub_mem (a : FiniteAdeleRing R K) :
    algebraMap K (FiniteAdeleRing R K) (rep a) - a ∈ integralAdeles R K :=
  (exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem).choose_spec.2

/-- A character of `K` trivial on `R` takes the value `χ x` at `rep a` whenever the diagonal image
of `x` differs from `a` by an integral finite adele. -/
private theorem addChar_rep_eq {χ : AddChar K M} (hχ : ∀ r : R, χ (algebraMap R K r) = 1)
    {a : FiniteAdeleRing R K} {x : K}
    (h : algebraMap K (FiniteAdeleRing R K) x - a ∈ integralAdeles R K) : χ (rep a) = χ x := by
  refine addChar_eq_of_algebraMap_sub_mem hχ ?_
  convert sub_mem (algebraMap_rep_sub_mem a) h using 1
  abel

/-- The extension of an additive character `χ` of `K` trivial on `R` to the additive character of
the finite adeles that is trivial on the integral finite adeles: its value at `a` is `χ x` for any
`x ∈ K` with `x - a` integral (`extendAddChar_apply_of_sub_mem_integralAdeles`). -/
noncomputable def extendAddChar (χ : AddChar K M) (hχ : ∀ r : R, χ (algebraMap R K r) = 1) :
    AddChar (FiniteAdeleRing R K) M where
  toFun a := χ (rep a)
  map_zero_eq_one' := by
    rw [addChar_rep_eq hχ (x := 0) (by simp), AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    rw [addChar_rep_eq hχ (x := rep a + rep b), AddChar.map_add_eq_mul]
    convert add_mem (algebraMap_rep_sub_mem a) (algebraMap_rep_sub_mem b) using 1
    rw [map_add]
    abel

variable {χ : AddChar K M} {hχ : ∀ r : R, χ (algebraMap R K r) = 1}

/-- Unfolding lemma: the extended character at `a` is `χ` at the chosen representative of `a`. -/
private theorem extendAddChar_apply_eq_rep (a : FiniteAdeleRing R K) :
    extendAddChar χ hχ a = χ (rep a) :=
  (rfl)

/-- **The value of the extended character.** At a finite adele `a` it is `χ x` for every `x ∈ K`
whose diagonal image differs from `a` by an integral finite adele. -/
theorem extendAddChar_apply_of_sub_mem_integralAdeles {a : FiniteAdeleRing R K} {x : K}
    (h : algebraMap K (FiniteAdeleRing R K) x - a ∈ integralAdeles R K) :
    extendAddChar χ hχ a = χ x := by
  rw [extendAddChar_apply_eq_rep, addChar_rep_eq hχ h]

/-- The extended character extends `χ`. -/
@[simp]
theorem extendAddChar_algebraMap (x : K) :
    extendAddChar χ hχ (algebraMap K (FiniteAdeleRing R K) x) = χ x :=
  extendAddChar_apply_of_sub_mem_integralAdeles (by simp)

/-- The extended character is trivial on the integral finite adeles. -/
theorem extendAddChar_eq_one_of_mem_integralAdeles {a : FiniteAdeleRing R K}
    (ha : a ∈ integralAdeles R K) : extendAddChar χ hχ a = 1 := by
  rw [extendAddChar_apply_of_sub_mem_integralAdeles (x := 0) (by simpa using ha),
    AddChar.map_zero_eq_one]

/-- **Uniqueness of the extension.** A character of the finite adeles that extends `χ` and is
trivial on the integral finite adeles is `extendAddChar χ hχ`. -/
theorem eq_extendAddChar {ψ : AddChar (FiniteAdeleRing R K) M}
    (halg : ∀ x : K, ψ (algebraMap K (FiniteAdeleRing R K) x) = χ x)
    (hint : ∀ a ∈ integralAdeles R K, ψ a = 1) : ψ = extendAddChar χ hχ := by
  ext a
  obtain ⟨x, -, hx⟩ := exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem
  rw [extendAddChar_apply_of_sub_mem_integralAdeles hx, ← halg,
    ← add_sub_cancel a (algebraMap K (FiniteAdeleRing R K) x), AddChar.map_add_eq_mul, hint _ hx,
    mul_one]

/-- The extended character is constant on the cosets of the open subgroup of integral finite
adeles, so it is locally constant. -/
theorem isLocallyConstant_extendAddChar : IsLocallyConstant (extendAddChar χ hχ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun a ↦ ?_
  have hU : {b : FiniteAdeleRing R K | b - a ∈ integralAdeles R K} ∈ nhds a :=
    ((isOpen_integralAdeles R K).preimage (continuous_sub_right a)).mem_nhds (by simp)
  filter_upwards [hU] with b hb
  rw [← sub_add_cancel b a, AddChar.map_add_eq_mul,
    extendAddChar_eq_one_of_mem_integralAdeles hb, one_mul]

/-- The extended character is continuous, for every topology on its values. -/
theorem continuous_extendAddChar [TopologicalSpace M] : Continuous (extendAddChar χ hχ) :=
  isLocallyConstant_extendAddChar.continuous

end IsDedekindDomain.FiniteAdeleRing
