/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Kummer.Degree
public import TauCeti.FieldTheory.IntermediateField.RootsOfUnity

import Mathlib.FieldTheory.Relrank
import TauCeti.Algebra.Group.PowMonoidHom

/-!
# Kummer extensions over an intermediate field

Let `K` be a field, `Δ` a subgroup of `Kˣ`, and `L` an intermediate field of an extension `E/K`.
Read in `Lˣ`, the subgroup `Δ` generates the Kummer field `L(Δ^{1/n})` over `L`, which is the
compositum of `L` with `K(Δ^{1/n})` (`IntermediateField.restrictScalars_kummerField_map_eq_sup`).
Write `Δ ∩ (Lˣ)ⁿ` for the elements of `Δ` that are `n`-th powers in `L`. Suppose that `n ≠ 0`,
that every element of `Δ` has an `n`-th root in `E`, and that `L` contains the `n`-th roots of
unity, as it does when `K` does (`IntermediateField.hasEnoughRootsOfUnity`). If `Δ ∩ (Lˣ)ⁿ` has
finite index in `Δ`, then the degree of `L(Δ^{1/n})` over `L` is

`[L(Δ^{1/n}) : L] = [Δ : Δ ∩ (Lˣ)ⁿ]`

(`IntermediateField.finrank_kummerField_map`). When `L` lies inside `K(Δ^{1/n})`, this computes
the degree of `K(Δ^{1/n})` over `L` (`TauCeti.finrank_extendScalars_kummerField`). If moreover `K`
contains the `n`-th roots of unity and `Δ ∩ (Kˣ)ⁿ` has finite index in `Δ`, then `L` is itself the
Kummer field of `Δ ∩ (Lˣ)ⁿ` (`TauCeti.kummerField_inf_comap_eq`), and
`[L : K] = [Δ ∩ (Lˣ)ⁿ : Δ ∩ (Kˣ)ⁿ]` (`TauCeti.finrank_eq_relIndex_inf_comap`): the intermediate
fields of `K(Δ^{1/n})/K` are the Kummer fields of the subgroups between `Δ ∩ (Kˣ)ⁿ` and `Δ`.

Over a number field containing the `p`-th roots of unity, the degree formula is the count of the
`S`-units that become `p`-th powers in a subfield `L` of `M = K(U(S)^{1/p})`, the index
`[U(S) : U(S) ∩ (Lˣ)ᵖ] = [M : L]` of Milne's proof of the second inequality of global class field
theory.

## Main results

* `IntermediateField.restrictScalars_kummerField_map_eq_sup`: `L(Δ^{1/n}) = L ⊔ K(Δ^{1/n})`.
* `IntermediateField.finrank_kummerField_map`: `[L(Δ^{1/n}) : L] = [Δ : Δ ∩ (Lˣ)ⁿ]`.
* `TauCeti.kummerField_map_eq_extendScalars`, `TauCeti.finrank_extendScalars_kummerField`: for
  `L ≤ K(Δ^{1/n})`, the field `L(Δ^{1/n})` is `K(Δ^{1/n})`, and
  `[K(Δ^{1/n}) : L] = [Δ : Δ ∩ (Lˣ)ⁿ]`.
* `TauCeti.kummerField_inf_comap_eq`, `TauCeti.finrank_eq_relIndex_inf_comap`: for
  `L ≤ K(Δ^{1/n})`, `L = K((Δ ∩ (Lˣ)ⁿ)^{1/n})` and `[L : K] = [Δ ∩ (Lˣ)ⁿ : Δ ∩ (Kˣ)ⁿ]`.

## References

* S. Lang, *Algebra*, Graduate Texts in Mathematics 211, Springer (2002), Chapter VI, §8,
  Theorem 8.1.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Theorem A.3 and the proof of
  Lemma 6.9.
-/

public section

open IntermediateField Module TauCeti

namespace IntermediateField

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] {n : ℕ} {Δ : Subgroup Kˣ}
  (L : IntermediateField K E)

/-- **The Kummer field over an intermediate field is a compositum.** Read in `Lˣ`, the subgroup
`Δ` of `Kˣ` generates over `L` the compositum `L(Δ^{1/n}) = L ⊔ K(Δ^{1/n})`. -/
theorem restrictScalars_kummerField_map_eq_sup :
    (kummerField E n (Δ.map (Units.map (algebraMap K L : K →* L)))).restrictScalars K =
      L ⊔ kummerField E n Δ := by
  rw [kummerField_def, kummerField_def, restrictScalars_adjoin_eq_sup]
  congr 2
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hx⟩
    exact ⟨a, ha, by simpa using hx⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨_, ⟨a, ha, rfl⟩, by simpa using hx⟩

variable [NeZero n]

/-- **The degree of a Kummer extension over an intermediate field.** If `L` contains the `n`-th
roots of unity and every element of `Δ` has an `n`-th root in `E`, then `[L(Δ^{1/n}) : L]` is the
index in `Δ` of the elements that are `n`-th powers in `L`, as soon as this index is finite. -/
theorem finrank_kummerField_map [HasEnoughRootsOfUnity L n]
    [((powMonoidHom n : Lˣ →* Lˣ).range.comap
      (Units.map (algebraMap K L : K →* L))).IsFiniteRelIndex Δ]
    (hroots : ∀ a ∈ Δ, ∃ x : E, x ^ n = algebraMap K E a) :
    finrank L (kummerField E n (Δ.map (Units.map (algebraMap K L : K →* L)))) =
      ((powMonoidHom n : Lˣ →* Lˣ).range.comap (Units.map (algebraMap K L : K →* L))).relIndex
        Δ := by
  have : (powMonoidHom n : Lˣ →* Lˣ).range.IsFiniteRelIndex
      (Δ.map (Units.map (algebraMap K L : K →* L))) :=
    Subgroup.isFiniteRelIndex_comap_iff.1 inferInstance
  rw [Subgroup.relIndex_comap]
  refine finrank_kummerField fun _ ⟨a, ha, h⟩ ↦ ?_
  obtain ⟨x, hx⟩ := hroots a ha
  exact ⟨x, by simpa [← h] using hx⟩

end IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] {n : ℕ} {Δ : Subgroup Kˣ}
  {L : IntermediateField K E}

/-- For `L ≤ K(Δ^{1/n})`, the Kummer field of `Δ` over `L` is `K(Δ^{1/n})` itself. -/
theorem kummerField_map_eq_extendScalars (hL : L ≤ kummerField E n Δ) :
    kummerField E n (Δ.map (Units.map (algebraMap K L : K →* L))) =
      extendScalars hL :=
  restrictScalars_injective K <| by
    rw [restrictScalars_kummerField_map_eq_sup, extendScalars_restrictScalars, sup_eq_right.2 hL]

variable [NeZero n]

/-- **The degree of a Kummer extension over an intermediate field.** If `L` contains the `n`-th
roots of unity, every element of `Δ` has an `n`-th root in `E`, and `L ≤ K(Δ^{1/n})`, then the
degree `[K(Δ^{1/n}) : L]` is the index in `Δ` of the elements that are `n`-th powers in `L`, as
soon as this index is finite. -/
theorem finrank_extendScalars_kummerField [HasEnoughRootsOfUnity L n]
    [((powMonoidHom n : Lˣ →* Lˣ).range.comap
      (Units.map (algebraMap K L : K →* L))).IsFiniteRelIndex Δ]
    (hroots : ∀ a ∈ Δ, ∃ x : E, x ^ n = algebraMap K E a) (hL : L ≤ kummerField E n Δ) :
    finrank L (extendScalars hL) =
      ((powMonoidHom n : Lˣ →* Lˣ).range.comap (Units.map (algebraMap K L : K →* L))).relIndex
        Δ := by
  rw [← kummerField_map_eq_extendScalars, L.finrank_kummerField_map hroots]

variable [HasEnoughRootsOfUnity K n]

/-- **The degree of an intermediate field of a Kummer extension.** If `K` contains the `n`-th
roots of unity, every element of `Δ` has an `n`-th root in `E`, and `Δ ∩ (Kˣ)ⁿ` has finite index
in `Δ`, then every intermediate field `L` of `K(Δ^{1/n})/K` has degree `[L : K]` equal to the
index of `Δ ∩ (Kˣ)ⁿ` in the elements of `Δ` that are `n`-th powers in `L`. -/
theorem finrank_eq_relIndex_inf_comap [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ a ∈ Δ, ∃ x : E, x ^ n = algebraMap K E a) (hL : L ≤ kummerField E n Δ) :
    finrank K L = (powMonoidHom n : Kˣ →* Kˣ).range.relIndex
      (Δ ⊓ (powMonoidHom n : Lˣ →* Lˣ).range.comap (Units.map (algebraMap K L : K →* L))) := by
  set C := (powMonoidHom n : Lˣ →* Lˣ).range.comap (Units.map (algebraMap K L : K →* L))
  have hPC := (Units.map (algebraMap K L : K →* L)).range_powMonoidHom_le_comap n
  -- The tower `K ≤ L ≤ K(Δ^{1/n})` against `Δ ∩ (Kˣ)ⁿ ≤ Δ ∩ (Lˣ)ⁿ ≤ Δ`.
  have htower := finrank_bot_mul_relfinrank hL
  rw [relfinrank_eq_finrank_of_le hL, finrank_extendScalars_kummerField hroots hL,
    finrank_kummerField hroots] at htower
  have hindex := Subgroup.relIndex_inf_mul_relIndex (powMonoidHom n : Kˣ →* Kˣ).range C Δ
  rw [inf_eq_left.2 hPC, ← htower, inf_comm] at hindex
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero) hindex).symm

/-- **Intermediate fields of a Kummer extension are Kummer fields.** If `K` contains the `n`-th
roots of unity, every element of `Δ` has an `n`-th root in `E`, and `Δ ∩ (Kˣ)ⁿ` has finite index
in `Δ`, then every intermediate field `L` of `K(Δ^{1/n})/K` is the Kummer field of the elements of
`Δ` that are `n`-th powers in `L`. -/
theorem kummerField_inf_comap_eq [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ a ∈ Δ, ∃ x : E, x ^ n = algebraMap K E a) (hL : L ≤ kummerField E n Δ) :
    kummerField E n
        (Δ ⊓ (powMonoidHom n : Lˣ →* Lˣ).range.comap (Units.map (algebraMap K L : K →* L))) =
      L := by
  set Δ' := Δ ⊓ (powMonoidHom n : Lˣ →* Lˣ).range.comap (Units.map (algebraMap K L : K →* L))
  have hle : kummerField E n Δ' ≤ L := by
    refine kummerField_le_iff.2 fun a ha x hx ↦ ?_
    -- An `n`-th root of `a = bⁿ`, `b ∈ L`, differs from `b` by an `n`-th root of unity of `K`.
    obtain ⟨b, hb⟩ := (Subgroup.mem_inf.1 ha).2
    have hpow : x ^ n = ((b : L) : E) ^ n := by
      have := congrArg (fun u : Lˣ ↦ ((u : L) : E)) hb
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, IntermediateField.coe_pow] at this
      simpa [this] using hx
    obtain ⟨z, rfl⟩ := exists_eq_algebraMap_mul_of_pow_eq (K := K) hpow
    exact L.mul_mem (L.algebraMap_mem z) (b : L).2
  have : FiniteDimensional K L := .of_injective (IntermediateField.inclusion hL).toLinearMap
    (IntermediateField.inclusion hL).injective
  have := Subgroup.isFiniteRelIndex_of_le_right (powMonoidHom n : Kˣ →* Kˣ).range
    (inf_le_left : Δ' ≤ Δ)
  refine eq_of_le_of_finrank_eq hle ?_
  rw [finrank_kummerField fun a ha ↦ hroots a (Subgroup.mem_inf.1 ha).1,
    finrank_eq_relIndex_inf_comap hroots hL]

end TauCeti
