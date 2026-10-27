/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.PurelyInseparable.Exponent

/-!
# A quadratic extension away from characteristic two is separable

An extension of fields of degree `2` is separable unless `2 = 0` in the base field. Indeed the
separable degree divides the degree, so it is `1` or `2`; the value `2` is separability itself,
while the value `1` makes the extension purely inseparable, hence of degree a power of the
exponential characteristic — and `2` is a power of the exponential characteristic only in
characteristic two.

The characteristic-two exception is genuine: over `K = 𝔽₂(t)` the extension `K(√t) / K` has
degree `2` and is purely inseparable.

Conversely, an inseparable extension of degree two contains the square of each of its elements in
the base field.  Consequently, if `L` is separable over some simple subextension `K⟮t⟯`, then `L`
is inseparable of degree two over at most one intermediate field.

## Main results

* `TauCeti.Algebra.isSeparable_of_finrank_eq_two`
* `TauCeti.Algebra.sq_mem_range_algebraMap_of_finrank_eq_two`
* `TauCeti.Algebra.finrank_eq_two_of_not_isSeparable`
* `TauCeti.IntermediateField.eq_of_finrank_eq_two_of_not_isSeparable`
-/

public section

open scoped IntermediateField

namespace TauCeti

namespace Algebra

open Module

/-- A finite extension of degree at most two that is not separable has degree two and separable
degree one: its separable degree is a proper divisor of its degree. -/
private theorem finSepDegree_eq_one_and_finrank_eq_two {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (h : finrank K L ≤ 2) (hs : ¬Algebra.IsSeparable K L) :
    Field.finSepDegree K L = 1 ∧ finrank K L = 2 := by
  have hne : Field.finSepDegree K L ≠ finrank K L :=
    mt (Field.finSepDegree_eq_finrank_iff K L).mp hs
  have hpos : 0 < Field.finSepDegree K L := Nat.pos_of_ne_zero (NeZero.ne _)
  have hle := Nat.le_of_dvd finrank_pos (Field.finSepDegree_dvd_finrank K L)
  omega

/-- **A field extension of degree two with `2 ≠ 0` in the base field is separable.**

The hypothesis is the nonvanishing of `2` in the base field rather than a `CharP` assumption, so
that it transfers along any field extension by injectivity of the structure map. -/
theorem isSeparable_of_finrank_eq_two {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h2 : (2 : K) ≠ 0) (h : finrank K L = 2) : Algebra.IsSeparable K L := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  -- Otherwise the separable degree is one: the extension is purely inseparable, so `2` is a power
  -- of the exponential characteristic, which forces characteristic two.
  by_contra hs
  have : IsPurelyInseparable K L :=
    isPurelyInseparable_of_finSepDegree_eq_one (finSepDegree_eq_one_and_finrank_eq_two h.le hs).1
  obtain ⟨q, hq⟩ := ExpChar.exists K
  have _ : ExpChar K q := hq
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K L q
  rw [h] at hn
  cases hq with
  | zero => simp at hn
  | prime hp =>
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by rw [hn]; exact dvd_pow_self q hn0)
    subst hq2
    exact h2 (by exact_mod_cast CharP.cast_eq_zero K 2)

/-- **A field extension of degree two that is not separable contains the square of each of its
elements in the base field**: it is purely inseparable of exponent one. -/
theorem sq_mem_range_algebraMap_of_finrank_eq_two {K L : Type*} [Field K] [Field L]
    [Algebra K L] (h : finrank K L = 2) (hs : ¬Algebra.IsSeparable K L) (a : L) :
    a ^ 2 ∈ (algebraMap K L).range := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have : IsPurelyInseparable K L :=
    isPurelyInseparable_of_finSepDegree_eq_one (finSepDegree_eq_one_and_finrank_eq_two h.le hs).1
  obtain ⟨q, hq⟩ := ExpChar.exists K
  have _ : ExpChar K q := hq
  -- The degree `2` is a power `q ^ m` of the exponential characteristic.
  obtain ⟨m, hm⟩ := IsPurelyInseparable.finrank_eq_pow K L q
  have := TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow K L q hm.le a
  rwa [← hm, h] at this

/-- **A finite extension of degree at most two that is not separable has degree exactly two.** -/
theorem finrank_eq_two_of_not_isSeparable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (h : finrank K L ≤ 2) (hs : ¬Algebra.IsSeparable K L) :
    finrank K L = 2 :=
  (finSepDegree_eq_one_and_finrank_eq_two h hs).2

end Algebra

namespace IntermediateField

open Module Polynomial

/-- **Two intermediate fields of index two over which `L` is inseparable coincide**, as soon as `L`
is separable over `K⟮t⟯` for some `t`. -/
theorem eq_of_finrank_eq_two_of_not_isSeparable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (t : L) [Algebra.IsSeparable K⟮t⟯ L] {E₁ E₂ : IntermediateField K L}
    (h₁ : finrank E₁ L = 2) (hs₁ : ¬Algebra.IsSeparable E₁ L) (h₂ : finrank E₂ L = 2)
    (hs₂ : ¬Algebra.IsSeparable E₂ L) : E₁ = E₂ := by
  -- Every square of `L` lies in `M = E₁ ⊓ E₂`, so `L` is purely inseparable over `M(t)`; it is
  -- also separable over `M(t) ⊇ K(t)`, so `L = M(t)`, which has degree at most two over `M`.
  set M := E₁ ⊓ E₂
  have hsq (a : L) : a ^ 2 ∈ M := by
    obtain ⟨c₁, hc₁⟩ := Algebra.sq_mem_range_algebraMap_of_finrank_eq_two h₁ hs₁ a
    obtain ⟨c₂, hc₂⟩ := Algebra.sq_mem_range_algebraMap_of_finrank_eq_two h₂ hs₂ a
    exact ⟨hc₁ ▸ c₁.2, hc₂ ▸ c₂.2⟩
  -- `L` has characteristic two, as an inseparable extension of degree two of `E₁`.
  have h2 : (2 : L) = 0 := by
    by_contra h
    refine hs₁ (Algebra.isSeparable_of_finrank_eq_two (fun h' ↦ h ?_) h₁)
    have := congrArg (algebraMap E₁ L) h'
    rwa [map_ofNat, map_zero] at this
  -- `L = M(t)`: it is separable over `M(t) ⊇ K(t)`, and purely inseparable over it.
  set E : IntermediateField M L := IntermediateField.adjoin M {t}
  set E' : IntermediateField K L := E.restrictScalars K
  have hle : K⟮t⟯ ≤ E' := IntermediateField.adjoin_simple_le_iff.mpr
    (IntermediateField.mem_adjoin_simple_self M t)
  let : Algebra K⟮t⟯ E' := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K⟮t⟯ E' L := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsSeparable E' L := Algebra.isSeparable_tower_top_of_isSeparable K⟮t⟯ E' L
  have : CharP E' 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr
    ((algebraMap E' L).injective (by rw [map_natCast, map_zero]; exact_mod_cast h2))
  have : IsPurelyInseparable E' L := (isPurelyInseparable_iff_pow_mem E' 2).mpr fun a ↦
    ⟨1, ⟨⟨a ^ 2, E.algebraMap_mem ⟨a ^ 2, hsq a⟩⟩, by simp⟩⟩
  have hE : E = ⊤ := by
    refine IntermediateField.restrictScalars_injective K (eq_top_iff.mpr fun a _ ↦ ?_)
    obtain ⟨b, rfl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable E' L a
    exact b.2
  -- So `[L : M] ≤ 2`, which forces `M = E₁` and `M = E₂`.
  have hpoly : (X ^ 2 - C (⟨t ^ 2, hsq t⟩ : M)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hroot : aeval t (X ^ 2 - C (⟨t ^ 2, hsq t⟩ : M)) = 0 := by simp
  have hint : IsIntegral M t := ⟨_, hpoly, hroot⟩
  have hMt : finrank M L = (minpoly M t).natDegree := by
    rw [← IntermediateField.finrank_top', ← hE, IntermediateField.adjoin.finrank hint]
  have : FiniteDimensional M L :=
    Module.finite_of_finrank_pos (hMt ▸ minpoly.natDegree_pos hint)
  have hM : finrank M L ≤ 2 := by
    rw [hMt, ← natDegree_X_pow_sub_C (n := 2) (a := (⟨t ^ 2, hsq t⟩ : M))]
    exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (pnz := hpoly.ne_zero) (hp := hroot))
  have hM₁ : M = E₁ := IntermediateField.eq_of_le_of_finrank_eq' inf_le_left
    (le_antisymm (h₁ ▸ hM) (IntermediateField.finrank_le_of_le_left inf_le_left))
  have hM₂ : M = E₂ := IntermediateField.eq_of_le_of_finrank_eq' inf_le_right
    (le_antisymm (h₂ ▸ hM) (IntermediateField.finrank_le_of_le_left inf_le_right))
  exact hM₁.symm.trans hM₂

end IntermediateField

end TauCeti
