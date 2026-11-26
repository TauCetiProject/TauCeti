/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

import TauCeti.Topology.Algebra.AddChar

/-!
# Additive characters of the finite adeles trivial on the integral adeles

Let `R` be a Dedekind domain with fraction field `K`, let `𝔸ᶠ` be its finite adele ring and
`Ô = ∏_v 𝒪_v` the integral finite adeles. By strong approximation `𝔸ᶠ = K + Ô`, and `K ∩ Ô = R`
(`IsDedekindDomain.FiniteAdeleRing.quotientEquivQuotientIntegralAdeles`). Hence an additive
character `χ` of `K` that is trivial on `R` extends uniquely to an additive character of `𝔸ᶠ`
that is trivial on `Ô`: its value at `a` is `χ x` for any `x ∈ K` with `a - x ∈ Ô`. This
extension, `IsDedekindDomain.FiniteAdeleRing.extendAddChar χ hχ`, is locally constant because `Ô`
is open.

For a number field `K` and `χ = exp (2πi Tr_{K/ℚ} ·)` this is the finite part of the standard
additive character of the adeles of `K`, which is trivial on `Ô` and equals
`exp (2πi Tr_{K/ℚ} a)` at `a ∈ K`.

The extension pairs `𝔸ᶠ` with `Ô` through `(z, u) ↦ ψ (z u)`: the `z` with `ψ (z u) = 1` for every
`u ∈ Ô` are those of the form `x + o` with `o ∈ Ô` and `x ∈ K` such that `χ (x r) = 1` for every
`r ∈ R` (`forall_extendAddChar_mul_eq_one_iff`). For the trace character of a number field this
set of `x` is the inverse different.

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.extendAddChar`: the extension of a character of `K` trivial on
  `R` to a character of the finite adeles trivial on the integral finite adeles.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.extendAddChar_apply_of_sub_mem`: the value at `a` is `χ x` for
  every `x ∈ K` with `a - x ∈ Ô`; in particular `extendAddChar_algebraMap` and
  `extendAddChar_apply_of_mem_integralAdeles`.
* `IsDedekindDomain.FiniteAdeleRing.addChar_ext`: a character of the finite adeles trivial on `Ô`
  is determined by its values on `K`.
* `IsDedekindDomain.FiniteAdeleRing.eq_extendAddChar_iff`: the extension is the unique character
  trivial on `Ô` that restricts to `χ` on `K`.
* `IsDedekindDomain.FiniteAdeleRing.isLocallyConstant_extendAddChar`: the extension is locally
  constant, hence continuous for every topology on the values.
* `IsDedekindDomain.FiniteAdeleRing.forall_extendAddChar_mul_eq_one_iff`: the annihilator of `Ô`
  under `(z, u) ↦ ψ (z u)`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in
  J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory* (1967).
-/

public section

noncomputable section

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {M : Type*} [Monoid M]

variable (χ : AddChar K M) (hχ : ∀ r : R, χ (algebraMap R K r) = 1)

include hχ in
/-- Two elements of `K` that differ from the same finite adele by integral finite adeles have the
same value under a character trivial on `R`: their difference lies in `K ∩ Ô = R`. -/
private theorem apply_eq_of_sub_mem {a : FiniteAdeleRing R K} {x y : K}
    (hx : algebraMap K (FiniteAdeleRing R K) x - a ∈ integralAdeles R K)
    (hy : algebraMap K (FiniteAdeleRing R K) y - a ∈ integralAdeles R K) : χ x = χ y := by
  have hxy : algebraMap K (FiniteAdeleRing R K) (x - y) ∈ integralAdeles R K := by
    simpa only [map_sub, sub_sub_sub_cancel_right] using sub_mem hx hy
  obtain ⟨r, hr⟩ := (algebraMap_mem_integralAdeles_iff (x - y)).mp hxy
  rw [← sub_add_cancel x y, ← hr, AddChar.map_add_eq_mul, hχ, one_mul]

/-- The extension of an additive character `χ` of `K` that is trivial on `R` to the finite adele
ring: the value at a finite adele `a` is `χ x` for any `x ∈ K` with `a - x` integral at every finite
place (`extendAddChar_apply_of_sub_mem`). It is the unique character of the finite adeles that is
trivial on the integral finite adeles and restricts to `χ` on `K` (`eq_extendAddChar_iff`). -/
def extendAddChar : AddChar (FiniteAdeleRing R K) M where
  -- a representative `x ∈ K` of `a` modulo the integral finite adeles, by strong approximation
  toFun a := χ (exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem).choose
  map_zero_eq_one' := by
    rw [apply_eq_of_sub_mem χ hχ
      (exists_algebraMap_mem_and_sub_mem_integralAdeles _ Filter.univ_mem).choose_spec.2 (y := 0)
      (by simp), AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    have ha := (exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem).choose_spec.2
    have hb := (exists_algebraMap_mem_and_sub_mem_integralAdeles b Filter.univ_mem).choose_spec.2
    rw [apply_eq_of_sub_mem χ hχ
      (exists_algebraMap_mem_and_sub_mem_integralAdeles (a + b) Filter.univ_mem).choose_spec.2
      (y := _ + _)
      (by rw [map_add, add_sub_add_comm]; exact add_mem ha hb), AddChar.map_add_eq_mul]

/-- **The value of the extended character.** At a finite adele `a`, the extension of `χ` takes the
value `χ x` for every `x ∈ K` such that `a - x` is an integral finite adele. -/
theorem extendAddChar_apply_of_sub_mem {a : FiniteAdeleRing R K} {x : K}
    (hx : a - algebraMap K (FiniteAdeleRing R K) x ∈ integralAdeles R K) :
    extendAddChar χ hχ a = χ x :=
  apply_eq_of_sub_mem χ hχ
    (exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem).choose_spec.2
    (sub_mem_comm_iff.mp hx)

/-- The extended character restricts to `χ` on the diagonal copy of `K`. -/
@[simp]
theorem extendAddChar_algebraMap (x : K) :
    extendAddChar χ hχ (algebraMap K (FiniteAdeleRing R K) x) = χ x :=
  extendAddChar_apply_of_sub_mem χ hχ (by simp)

/-- The extended character is trivial on the integral finite adeles. -/
theorem extendAddChar_apply_of_mem_integralAdeles {a : FiniteAdeleRing R K}
    (ha : a ∈ integralAdeles R K) : extendAddChar χ hχ a = 1 := by
  rw [extendAddChar_apply_of_sub_mem χ hχ (x := 0) (by simpa using ha), AddChar.map_zero_eq_one]

/-- **Uniqueness.** Two additive characters of the finite adele ring that are trivial on the
integral finite adeles and agree on the diagonal copy of `K` are equal, since every finite adele is
the sum of an element of `K` and an integral finite adele. -/
theorem addChar_ext {ψ ψ' : AddChar (FiniteAdeleRing R K) M}
    (h : ∀ a ∈ integralAdeles R K, ψ a = 1) (h' : ∀ a ∈ integralAdeles R K, ψ' a = 1)
    (hK : ∀ x : K, ψ (algebraMap K (FiniteAdeleRing R K) x) =
      ψ' (algebraMap K (FiniteAdeleRing R K) x)) : ψ = ψ' := by
  ext a
  obtain ⟨x, -, hx⟩ := exists_algebraMap_mem_and_sub_mem_integralAdeles a Filter.univ_mem
  rw [sub_mem_comm_iff] at hx
  rw [← sub_add_cancel a (algebraMap K (FiniteAdeleRing R K) x), AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, h _ hx, h' _ hx, hK]

/-- **Characterization of the extended character**: it is the unique additive character of the
finite adele ring that is trivial on the integral finite adeles and restricts to `χ` on `K`. -/
theorem eq_extendAddChar_iff {ψ : AddChar (FiniteAdeleRing R K) M} :
    ψ = extendAddChar χ hχ ↔ (∀ a ∈ integralAdeles R K, ψ a = 1) ∧
      ∀ x : K, ψ (algebraMap K (FiniteAdeleRing R K) x) = χ x := by
  have h1 (a) (ha : a ∈ integralAdeles R K) := extendAddChar_apply_of_mem_integralAdeles χ hχ ha
  refine ⟨?_, fun h ↦ addChar_ext h.1 h1 fun x ↦ by rw [h.2, extendAddChar_algebraMap]⟩
  rintro rfl
  exact ⟨h1, extendAddChar_algebraMap χ hχ⟩

/-- The extended character is locally constant: it is constant on the cosets of the open subgroup
of integral finite adeles. In particular it is continuous for every topology on `M`. -/
theorem isLocallyConstant_extendAddChar : IsLocallyConstant (extendAddChar χ hχ) :=
  AddChar.isLocallyConstant_of_setOf_eq_one_mem_nhds_zero <|
    Filter.mem_of_superset ((isOpen_integralAdeles R K).mem_nhds (zero_mem _))
      fun _ ha ↦ extendAddChar_apply_of_mem_integralAdeles χ hχ ha

/-- **The annihilator of the integral finite adeles.** A finite adele `z` satisfies
`ψ (z u) = 1` for every integral finite adele `u`, where `ψ` extends `χ`, exactly when
`z = x + o` with `o` integral and `x ∈ K` such that `χ (x r) = 1` for every `r ∈ R`. -/
theorem forall_extendAddChar_mul_eq_one_iff (z : FiniteAdeleRing R K) :
    (∀ u ∈ integralAdeles R K, extendAddChar χ hχ (z * u) = 1) ↔
      ∃ x : K, (∀ r : R, χ (x * algebraMap R K r) = 1) ∧
        z - algebraMap K (FiniteAdeleRing R K) x ∈ integralAdeles R K := by
  -- in `z u = x u + (z - x) u` only `x u` matters, as `(z - x) u` is integral
  have hsplit {x : K} (hx : z - algebraMap K (FiniteAdeleRing R K) x ∈ integralAdeles R K)
      {u : FiniteAdeleRing R K} (hu : u ∈ integralAdeles R K) :
      extendAddChar χ hχ (z * u) = extendAddChar χ hχ (algebraMap K _ x * u) := by
    rw [← sub_add_cancel z (algebraMap K (FiniteAdeleRing R K) x), add_mul,
      AddChar.map_add_eq_mul, extendAddChar_apply_of_mem_integralAdeles χ hχ (mul_mem hx hu),
      one_mul]
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := exists_algebraMap_mem_and_sub_mem_integralAdeles z Filter.univ_mem
    rw [sub_mem_comm_iff] at hx
    refine ⟨x, fun r ↦ ?_, hx⟩
    have hr : algebraMap R (FiniteAdeleRing R K) r ∈ integralAdeles R K :=
      (integralAdeles R K).algebraMap_mem r
    rw [← h _ hr, hsplit hx hr, IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K), ← map_mul,
      extendAddChar_algebraMap]
  · rintro ⟨x, hxR, hx⟩ u hu
    rw [hsplit hx hu]
    -- approximate `u` by `r ∈ R` so closely that `x (u - r)` is integral
    have hU : IsOpen {v : FiniteAdeleRing R K |
        algebraMap K (FiniteAdeleRing R K) x * (u - v) ∈ integralAdeles R K} :=
      (isOpen_integralAdeles R K).preimage (by fun_prop)
    have hu' : u ∈ closure (Set.range (algebraMap R (FiniteAdeleRing R K))) := by
      rwa [closure_range_algebraMap]
    obtain ⟨_, hrU, r, rfl⟩ := mem_closure_iff.mp hu' _ hU (by simp)
    rw [← sub_add_cancel u (algebraMap R (FiniteAdeleRing R K) r), mul_add,
      AddChar.map_add_eq_mul, extendAddChar_apply_of_mem_integralAdeles χ hχ hrU, one_mul,
      IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K), ← map_mul,
      extendAddChar_algebraMap, hxR]

end IsDedekindDomain.FiniteAdeleRing
