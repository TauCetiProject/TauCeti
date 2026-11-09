/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.PurelyInseparable.Exponent

/-!
# Separability of extensions of prime degree

An extension of fields of prime degree `p` is separable unless `p = 0` in the base field. Indeed
the separable degree divides the degree, so it is `1` or `p`; the value `p` is separability
itself, while the value `1` makes the extension purely inseparable, hence of degree a power of the
exponential characteristic — and the prime `p` is such a power only in characteristic `p`. In
particular a quadratic extension away from characteristic two is separable.

The characteristic-`p` exception is genuine: over `K = 𝔽_p(t)` the extension `K(t ^ (1 / p)) / K`
has degree `p` and is purely inseparable.

Conversely, an inseparable extension of prime degree `p` contains the `p`-th power of each of its
elements in the base field. Consequently, if `L` is separable over some simple subextension
`K⟮t⟯`, then `L` is inseparable of degree `p` over at most one intermediate field.

## Main results

* `TauCeti.Algebra.isSeparable_of_finrank_prime`
* `TauCeti.Algebra.isSeparable_of_finrank_eq_two`
* `TauCeti.Algebra.isPurelyInseparable_iff_not_isSeparable`
* `TauCeti.Algebra.pow_finrank_mem_range_algebraMap_of_not_isSeparable`
* `TauCeti.Algebra.finrank_eq_two_of_not_isSeparable`
* `TauCeti.IntermediateField.eq_of_finrank_eq_of_not_isSeparable`
-/

public section

open scoped IntermediateField

namespace TauCeti

namespace Algebra

open Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **An extension of prime degree is purely inseparable exactly when it is not separable**: its
separable degree divides its degree, so it is either one or the whole degree. -/
theorem isPurelyInseparable_iff_not_isSeparable (hp : (finrank K L).Prime) :
    IsPurelyInseparable K L ↔ ¬Algebra.IsSeparable K L := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hp.pos
  rw [isPurelyInseparable_iff_finSepDegree_eq_one, ← Field.finSepDegree_eq_finrank_iff]
  rcases (Nat.dvd_prime hp).mp (Field.finSepDegree_dvd_finrank K L) with h | h <;>
    simp [h, hp.ne_one, hp.ne_one.symm]

/-- **A finite extension of degree at most two that is not separable has degree exactly two.** -/
theorem finrank_eq_two_of_not_isSeparable [FiniteDimensional K L] (h : finrank K L ≤ 2)
    (hs : ¬Algebra.IsSeparable K L) : finrank K L = 2 := by
  have hne := mt (Field.finSepDegree_eq_finrank_iff K L).mp hs
  have hle := Field.finSepDegree_le_finrank K L
  have hpos : 0 < Field.finSepDegree K L := Nat.pos_of_ne_zero (NeZero.ne _)
  omega

/-- **A field extension of prime degree `p` with `p ≠ 0` in the base field is separable.**

The hypothesis is the nonvanishing of `p` in the base field rather than a `CharP` assumption, so
that it transfers along any field extension by injectivity of the structure map. -/
theorem isSeparable_of_finrank_prime (hp : (finrank K L).Prime) (hpK : (finrank K L : K) ≠ 0) :
    Algebra.IsSeparable K L := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hp.pos
  -- Otherwise the separable degree is one: the extension is purely inseparable, so `p` is a power
  -- of the exponential characteristic, which forces characteristic `p`.
  by_contra hs
  have : IsPurelyInseparable K L := (isPurelyInseparable_iff_not_isSeparable hp).2 hs
  obtain ⟨q, hq⟩ := ExpChar.exists K
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K L q
  obtain ⟨hqp, -⟩ := hp.pow_eq_iff.mp hn.symm
  cases hq with
  | zero => exact Nat.not_prime_one (hqp ▸ hp)
  | prime => exact hpK (hqp ▸ CharP.cast_eq_zero K q)

/-- **A field extension of degree two with `2 ≠ 0` in the base field is separable.** -/
theorem isSeparable_of_finrank_eq_two (h2 : (2 : K) ≠ 0) (h : finrank K L = 2) :
    Algebra.IsSeparable K L :=
  isSeparable_of_finrank_prime (h ▸ Nat.prime_two) (by rwa [h, Nat.cast_ofNat])

/-- **A field extension of prime degree `p` that is not separable contains the `p`-th power of each
of its elements in the base field**: it is purely inseparable of exponent one. -/
theorem pow_finrank_mem_range_algebraMap_of_not_isSeparable (hp : (finrank K L).Prime)
    (hs : ¬Algebra.IsSeparable K L) (a : L) : a ^ finrank K L ∈ (algebraMap K L).range := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hp.pos
  have : IsPurelyInseparable K L := (isPurelyInseparable_iff_not_isSeparable hp).2 hs
  obtain ⟨q, hq⟩ := ExpChar.exists K
  -- The degree is a power `q ^ m` of the exponential characteristic.
  obtain ⟨m, hm⟩ := IsPurelyInseparable.finrank_eq_pow K L q
  rw [hm]
  exact TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow K L q hm.le a

end Algebra

namespace IntermediateField

open Module Polynomial

/-- **Two intermediate fields of prime index `p` over which `L` is inseparable coincide**, as soon
as `L` is separable over `K⟮t⟯` for some `t`. -/
theorem eq_of_finrank_eq_of_not_isSeparable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (t : L) [Algebra.IsSeparable K⟮t⟯ L] {p : ℕ} (hp : p.Prime) {E₁ E₂ : IntermediateField K L}
    (h₁ : finrank E₁ L = p) (hs₁ : ¬Algebra.IsSeparable E₁ L) (h₂ : finrank E₂ L = p)
    (hs₂ : ¬Algebra.IsSeparable E₂ L) : E₁ = E₂ := by
  -- Every `p`-th power of `L` lies in `M = E₁ ⊓ E₂`, so `L` is purely inseparable over `M(t)`; it
  -- is also separable over `M(t) ⊇ K(t)`, so `L = M(t)`, which has degree at most `p` over `M`.
  set M := E₁ ⊓ E₂
  have hpow (a : L) : a ^ p ∈ M := by
    obtain ⟨c₁, hc₁⟩ :=
      Algebra.pow_finrank_mem_range_algebraMap_of_not_isSeparable (h₁ ▸ hp) hs₁ a
    obtain ⟨c₂, hc₂⟩ :=
      Algebra.pow_finrank_mem_range_algebraMap_of_not_isSeparable (h₂ ▸ hp) hs₂ a
    exact ⟨h₁ ▸ hc₁ ▸ c₁.2, h₂ ▸ hc₂ ▸ c₂.2⟩
  -- `L` has characteristic `p`, as an inseparable extension of degree `p` of `E₁`.
  have hpL : (p : L) = 0 := by
    have := not_not.mp (mt (Algebra.isSeparable_of_finrank_prime (h₁ ▸ hp)) hs₁)
    simpa [h₁] using congrArg (algebraMap E₁ L) this
  -- `L = M(t)`: it is separable over `M(t) ⊇ K(t)`, and purely inseparable over it.
  set E : IntermediateField M L := IntermediateField.adjoin M {t}
  set E' : IntermediateField K L := E.restrictScalars K
  have hle : K⟮t⟯ ≤ E' := IntermediateField.adjoin_simple_le_iff.mpr
    (IntermediateField.mem_adjoin_simple_self M t)
  let : Algebra K⟮t⟯ E' := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K⟮t⟯ E' L := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsSeparable E' L := Algebra.isSeparable_tower_top_of_isSeparable K⟮t⟯ E' L
  have : CharP E' p := (CharP.charP_iff_prime_eq_zero hp).mpr
    ((algebraMap E' L).injective (by simpa using hpL))
  have : ExpChar E' p := .prime hp
  have : IsPurelyInseparable E' L := (isPurelyInseparable_iff_pow_mem E' p).mpr fun a ↦
    ⟨1, ⟨⟨a ^ p, E.algebraMap_mem ⟨a ^ p, hpow a⟩⟩, by simp⟩⟩
  have hE : E = ⊤ := by
    refine IntermediateField.restrictScalars_injective K (eq_top_iff.mpr fun a _ ↦ ?_)
    obtain ⟨b, rfl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable E' L a
    exact b.2
  -- So `[L : M] ≤ p`, which forces `M = E₁` and `M = E₂`.
  have hpoly : (X ^ p - C (⟨t ^ p, hpow t⟩ : M)).Monic := monic_X_pow_sub_C _ hp.ne_zero
  have hroot : aeval t (X ^ p - C (⟨t ^ p, hpow t⟩ : M)) = 0 := by simp
  have hint : IsIntegral M t := ⟨_, hpoly, hroot⟩
  have hMt : finrank M L = (minpoly M t).natDegree := by
    rw [← IntermediateField.finrank_top', ← hE, IntermediateField.adjoin.finrank hint]
  have : FiniteDimensional M L :=
    Module.finite_of_finrank_pos (hMt ▸ minpoly.natDegree_pos hint)
  have hM : finrank M L ≤ p := by
    rw [hMt, ← natDegree_X_pow_sub_C (n := p) (a := (⟨t ^ p, hpow t⟩ : M))]
    exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (pnz := hpoly.ne_zero) (hp := hroot))
  have hM₁ : M = E₁ := IntermediateField.eq_of_le_of_finrank_eq' inf_le_left
    (le_antisymm (h₁ ▸ hM) (IntermediateField.finrank_le_of_le_left inf_le_left))
  have hM₂ : M = E₂ := IntermediateField.eq_of_le_of_finrank_eq' inf_le_right
    (le_antisymm (h₂ ▸ hM) (IntermediateField.finrank_le_of_le_left inf_le_right))
  exact hM₁.symm.trans hM₂

end IntermediateField

end TauCeti
