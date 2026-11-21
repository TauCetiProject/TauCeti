/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Fiber
public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.NumberTheory.MulChar.Basic
public import TauCeti.NumberTheory.MulChar.Duality
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Orthogonality relations for multiplicative characters

Let `M` be a commutative monoid with finitely many units and `R` a domain with enough roots of
unity, such as `ℂ`. Mathlib's `MulChar.sum_eq_zero_of_ne_one` and `MulChar.sum_one_eq_card_units`
sum one character over a finite `M` (Tau Ceti's `MulChar.sum_eq_ite` joins them), and
Mathlib's `DirichletCharacter.sum_characters_eq` sums all Dirichlet characters at one point. Tau
Ceti's `CommGroup.sum_monoidHom_apply_eq_ite`, `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` and
`CommGroup.sum_inv_smul_sum_smul` sum the characters `G →* Rˣ` of a finite commutative group. This
file states these sums for the characters `MulChar M R`, through `MulChar.equivToUnitHom`, in the
forms that character sums over a finite field use.

The characters trivial on a subgroup `H` of `Mˣ` are the characters of `Mˣ ⧸ H`. If `H` has finite
index, there are finitely many of them, and their values at a unit `u` sum to the index of `H` if
`u ∈ H` and to zero otherwise. This needs enough roots of unity in `R` only for the exponent of
`Mˣ ⧸ H`, and it holds also when `Mˣ` is infinite. When the type `MulChar M R` is finite, the same
sum is a sum over a filter of all characters. For the subgroup of `d`-th powers, the characters
trivial on `H` are the characters `χ` with `χ ^ d = 1`, and the sum is the number of `d`-th roots of
`u` in `Mˣ`; for a finite field and `d ≠ 0` this gives the classical count of solutions of
`y ^ d = c`.

Throughout, a cardinality or an index on the right of an identity is a natural number cast into the
coefficient ring `R`. In positive characteristic the identities determine these numbers only modulo
the characteristic; with values in `ℂ` they are exact counts.

## Main results

* `Subgroup.sum_subtype_mulChar_apply_eq_ite`: for `H` of finite index, the values at a unit `u`
  of the characters trivial on `H` sum to the cast of `H.index` if `u ∈ H` and to zero otherwise.
  The sum is over the subtype of these characters, which is finite
  (`Subgroup.finite_subtype_mulChar`).
* `Subgroup.sum_filter_mulChar_apply_eq_ite`: the same sum as a filter of a finite type
  `MulChar M R`.
The next four results need enough roots of unity in `R` for the exponent of `Mˣ`.

* `TauCeti.sum_mulChar_apply_eq_ite`: `∑ χ, χ a` is the cast of `#Mˣ` if `a = 1` and zero
  otherwise.
* `Units.sum_inv_mul_mulChar_apply_eq_ite`: for a unit `v`, `∑ χ, χ⁻¹ v * χ a` is the cast of
  `#Mˣ` if `a = v` and zero otherwise.
* `TauCeti.card_units_mul_apply_eq_sum_mulChar_units`: the Fourier expansion of a function `φ` on
  `Mˣ`, `#Mˣ · φ u = ∑ χ, χ u ∑_{y ∈ Mˣ} φ y χ⁻¹ y`.
* `TauCeti.card_units_mul_apply_eq_sum_mulChar`: the same expansion for a function `φ` on a finite
  `M`, with the inner sum over all `y ∈ M`.

Over a field `K` with enough roots of unity for the exponent of `Mˣ`, the cast of `#Mˣ` is nonzero
(`TauCeti.natCast_card_ne_zero_of_hasEnoughRootsOfUnity`).

* `TauCeti.apply_eq_inv_card_units_mul_sum_mulChar_units` and
  `TauCeti.apply_eq_inv_card_units_mul_sum_mulChar`: the normalized expansions
  `φ u = #Mˣ⁻¹ ∑ χ, χ u ∑ y, φ y (χ y)⁻¹`, for `φ` on `Mˣ` with `y ∈ Mˣ`, and for `φ` on a finite
  `M` with `y ∈ M`.
* `TauCeti.sum_filter_mulChar_pow_eq_one_apply_eq_card_pow_eq`: the values at a unit `u` of the
  characters `χ` with `χ ^ d = 1` sum to the cast of the number of `y ∈ Mˣ` with `y ^ d = u`.
* `TauCeti.card_pow_eq_eq_one_add_sum_filter_mulChar`: for a finite field `F`, `d ≠ 0`, and a
  coefficient domain with enough roots of unity for the exponent of `Fˣ ⧸ (Fˣ) ^ d`, the cast of
  the number of solutions of `y ^ d = c` in `F` is `1 + ∑_{χ ^ d = 1, χ ≠ 1} χ c`, also at
  `c = 0`. It holds for every finite commutative group with zero.
-/

public section

open Finset

variable {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R] [IsDomain R]
  [Fintype (MulChar M R)]

namespace Subgroup

omit [Finite Mˣ] [IsDomain R] [Fintype (MulChar M R)] in
/-- The characters trivial on a subgroup `H` of `Mˣ` are the characters of `Mˣ ⧸ H`. -/
private noncomputable def mulCharEquivQuotient (H : Subgroup Mˣ) :
    {χ : MulChar M R // ∀ h ∈ H, χ h = 1} ≃ (Mˣ ⧸ H →* Rˣ) :=
  (MulChar.equivToUnitHom.subtypeEquiv fun χ ↦ by
    simp [MonoidHom.mem_ker, MonoidHom.domRestrict_eq_one_iff, Units.ext_iff]).trans
    (MonoidHom.domRestrictHomKerEquiv Rˣ H).toEquiv

omit [Finite Mˣ] [IsDomain R] [Fintype (MulChar M R)] in
private theorem mulCharEquivQuotient_apply (H : Subgroup Mˣ)
    (χ : {χ : MulChar M R // ∀ h ∈ H, χ h = 1}) (u : Mˣ) :
    (mulCharEquivQuotient H χ (u : Mˣ ⧸ H) : R) = (χ : MulChar M R) u := by
  simp [mulCharEquivQuotient]

omit [Finite Mˣ] [Fintype (MulChar M R)] in
/-- A subgroup of finite index has finitely many characters trivial on it, since they are the
characters of the finite group `Mˣ ⧸ H`. -/
instance finite_subtype_mulChar (H : Subgroup Mˣ) [Finite (Mˣ ⧸ H)] :
    Finite {χ : MulChar M R // ∀ h ∈ H, χ h = 1} :=
  Finite.of_equiv _ (mulCharEquivQuotient H).symm

omit [Finite Mˣ] [Fintype (MulChar M R)] in
/-- **Orthogonality for the characters trivial on a subgroup.** For a subgroup `H` of `Mˣ` of
finite index, the values at a unit `u` of the characters trivial on `H` sum to the cast of the
index of `H` if `u ∈ H` and to zero otherwise. The sum is over the subtype of these characters, so
`Mˣ` and `MulChar M R` can be infinite. These characters are the characters of `Mˣ ⧸ H`, so this is
`CommGroup.sum_monoidHom_apply_eq_ite` on `Mˣ ⧸ H`, and `R` needs enough roots of unity only for
the exponent of `Mˣ ⧸ H`. -/
@[simp]
theorem sum_subtype_mulChar_apply_eq_ite (H : Subgroup Mˣ) [Finite (Mˣ ⧸ H)]
    [HasEnoughRootsOfUnity R (Monoid.exponent (Mˣ ⧸ H))] (u : Mˣ) [Decidable (u ∈ H)]
    [Fintype {χ : MulChar M R // ∀ h ∈ H, χ h = 1}] :
    ∑ χ : {χ : MulChar M R // ∀ h ∈ H, χ h = 1}, (χ : MulChar M R) u =
      if u ∈ H then (H.index : R) else 0 := by
  classical
  rw [Fintype.sum_equiv (mulCharEquivQuotient H) _ (fun ψ ↦ (ψ (u : Mˣ ⧸ H) : R))
      fun χ ↦ (mulCharEquivQuotient_apply H χ u).symm, CommGroup.sum_monoidHom_apply_eq_ite]
  simp only [QuotientGroup.eq_one_iff, index_eq_card]

omit [Finite Mˣ] in
/-- **Orthogonality for the characters trivial on a subgroup, as a filtered sum.** For a finite
type `MulChar M R` and a subgroup `H` of `Mˣ` of finite index, the values at a unit `u` of the
characters trivial on `H` sum to the cast of the index of `H` if `u ∈ H` and to zero otherwise.
This is `Subgroup.sum_subtype_mulChar_apply_eq_ite` with the sum over a filter of all
characters. -/
@[simp]
theorem sum_filter_mulChar_apply_eq_ite (H : Subgroup Mˣ) [Finite (Mˣ ⧸ H)]
    [HasEnoughRootsOfUnity R (Monoid.exponent (Mˣ ⧸ H))] (u : Mˣ) [Decidable (u ∈ H)]
    [DecidablePred fun χ : MulChar M R ↦ ∀ h ∈ H, χ h = 1] :
    ∑ χ : MulChar M R with ∀ h ∈ H, χ h = 1, χ u = if u ∈ H then (H.index : R) else 0 := by
  rw [sum_subtype (univ.filter fun χ : MulChar M R ↦ ∀ h ∈ H, χ h = 1)
    (p := fun χ : MulChar M R ↦ ∀ h ∈ H, χ h = 1) (fun χ ↦ by simp) fun χ ↦ χ u]
  exact sum_subtype_mulChar_apply_eq_ite H u

end Subgroup

namespace TauCeti

open MulChar

section Ambient

variable [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

/-- **Orthogonality for the characters at a point.** With enough roots of unity in `R` for the
exponent of `Mˣ`, the values at `a` of all characters of `M` sum to the cast of `#Mˣ` if `a = 1`
and to zero otherwise. At a unit this is
`CommGroup.sum_monoidHom_apply_eq_ite` for the characters of `Mˣ`; at a nonunit every term is
zero. -/
@[simp]
theorem sum_mulChar_apply_eq_ite (a : M) [Decidable (a = 1)] :
    ∑ χ : MulChar M R, χ a = if a = 1 then (Nat.card Mˣ : R) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    -- Transport the column orthogonality of the characters `Mˣ →* Rˣ` along `equivToUnitHom`.
    rw [Fintype.sum_equiv equivToUnitHom _ (fun φ : Mˣ →* Rˣ ↦ (φ u : R)) fun χ ↦ by simp,
      CommGroup.sum_monoidHom_apply_eq_ite]
    simp [Units.val_eq_one]
  · rw [ite_eq_right (by rintro rfl; exact ha isUnit_one)]
    exact sum_eq_zero fun χ _ ↦ χ.map_nonunit ha

/-- **Tagged orthogonality for the characters.** With enough roots of unity in `R` for the
exponent of `Mˣ`, for a unit `v` and `a ∈ M` the sum `∑ χ, χ⁻¹ v * χ a` over all characters is the
cast of `#Mˣ` if `a = v` and zero otherwise. Each term is `χ (v⁻¹ * a)`, so this is
`TauCeti.sum_mulChar_apply_eq_ite` at `v⁻¹ * a`. -/
@[simp]
theorem _root_.Units.sum_inv_mul_mulChar_apply_eq_ite (v : Mˣ) (a : M) [Decidable (a = v)] :
    ∑ χ : MulChar M R, χ⁻¹ v * χ a = if a = v then (Nat.card Mˣ : R) else 0 := by
  classical
  have hterm (χ : MulChar M R) : χ⁻¹ v * χ a = χ (↑v⁻¹ * a) := by
    rw [map_mul, inv_apply_units]
  simp_rw [hterm, sum_mulChar_apply_eq_ite, Units.inv_mul_eq_one, eq_comm (a := (v : M))]

omit [Finite Mˣ] in
/-- **The Fourier expansion on `Mˣ`.** With enough roots of unity in `R` for the exponent of
`Mˣ`, for a function `φ` on `Mˣ` and a unit `u`, `#Mˣ · φ u = ∑ χ, χ u ∑ y, φ y χ⁻¹ y`, with the
inner sum over `y ∈ Mˣ`. This is
`CommGroup.sum_inv_smul_sum_smul` for the characters of `Mˣ`, reindexed by `χ ↦ χ⁻¹`. -/
theorem card_units_mul_apply_eq_sum_mulChar_units [Fintype Mˣ] (φ : Mˣ → R) (u : Mˣ) :
    (Nat.card Mˣ : R) * φ u = ∑ χ : MulChar M R, χ u * ∑ y : Mˣ, φ y * χ⁻¹ y := by
  rw [← smul_eq_mul, ← CommGroup.sum_inv_smul_sum_smul φ u]
  refine Fintype.sum_equiv (equivToUnitHom.symm.trans (Equiv.inv _)) _ _ fun ψ ↦ ?_
  simp [inv_apply_units, mul_comm]

omit [Finite Mˣ] in
/-- **The Fourier expansion on `Mˣ` of a function on `M`.** With enough roots of unity in `R` for
the exponent of `Mˣ`, for a function `φ` on a finite commutative monoid `M` and a unit `u`,
`#Mˣ · φ u = ∑ χ, χ u ∑ y, φ y χ⁻¹ y`, with the inner sum over all `y ∈ M`. The terms at nonunits
`y` vanish, since `χ⁻¹ y = 0` there, so this is `card_units_mul_apply_eq_sum_mulChar_units` for
the restriction of `φ` to `Mˣ`. -/
theorem card_units_mul_apply_eq_sum_mulChar [Fintype M] (φ : M → R) (u : Mˣ) :
    (Nat.card Mˣ : R) * φ u = ∑ χ : MulChar M R, χ u * ∑ y, φ y * χ⁻¹ y := by
  classical
  rw [card_units_mul_apply_eq_sum_mulChar_units (fun y : Mˣ ↦ φ y) u]
  refine sum_congr rfl fun χ _ ↦ congrArg (χ u * ·) ?_
  refine Fintype.sum_of_injective _ Units.val_injective _ _ (fun y hy ↦ ?_) fun _ ↦ rfl
  rw [χ⁻¹.map_nonunit fun h ↦ hy ⟨h.unit, h.unit_spec⟩, mul_zero]

end Ambient

section Normalized

variable {K : Type*} [Field K] [HasEnoughRootsOfUnity K (Monoid.exponent Mˣ)]

omit [Finite Mˣ] in
/-- **The normalized Fourier expansion on `Mˣ`.** Over a field `K` with enough roots of unity for
the exponent of `Mˣ`, such as `ℂ`, a function `φ` on `Mˣ` satisfies
`φ u = #Mˣ⁻¹ ∑ χ, χ u ∑ y, φ y (χ y)⁻¹` for every unit `u`, with the inner sum over `y ∈ Mˣ`. Such
a field has `#Mˣ ≠ 0`. -/
theorem apply_eq_inv_card_units_mul_sum_mulChar_units [Fintype (MulChar M K)] [Fintype Mˣ]
    (φ : Mˣ → K) (u : Mˣ) :
    φ u = (Nat.card Mˣ : K)⁻¹ * ∑ χ : MulChar M K, χ u * ∑ y : Mˣ, φ y * (χ y)⁻¹ := by
  simp_rw [← inv_apply_eq_inv']
  rw [← card_units_mul_apply_eq_sum_mulChar_units,
    inv_mul_cancel_left₀ (natCast_card_ne_zero_of_hasEnoughRootsOfUnity K)]

omit [Finite Mˣ] in
/-- **The normalized Fourier expansion on `Mˣ` of a function on `M`.** Over a field `K` with enough
roots of unity for the exponent of `Mˣ`, such as `ℂ`, a function `φ` on a finite commutative monoid
`M` satisfies `φ u = #Mˣ⁻¹ ∑ χ, χ u ∑ y, φ y (χ y)⁻¹` for every unit `u`, with the inner sum over
all `y ∈ M`. Such a field has `#Mˣ ≠ 0`. -/
theorem apply_eq_inv_card_units_mul_sum_mulChar [Fintype (MulChar M K)] [Fintype M]
    (φ : M → K) (u : Mˣ) :
    φ u = (Nat.card Mˣ : K)⁻¹ * ∑ χ : MulChar M K, χ u * ∑ y, φ y * (χ y)⁻¹ := by
  simp_rw [← inv_apply_eq_inv']
  rw [← card_units_mul_apply_eq_sum_mulChar,
    inv_mul_cancel_left₀ (natCast_card_ne_zero_of_hasEnoughRootsOfUnity K)]

end Normalized

/-- **Counting `d`-th roots.** The values at a unit `u` of the characters `χ` with `χ ^ d = 1`
sum to the cast of the number of `y ∈ Mˣ` with `y ^ d = u`. The coefficient domain needs enough
roots of unity for the exponent of the quotient of `Mˣ` by its `d`-th powers. -/
theorem sum_filter_mulChar_pow_eq_one_apply_eq_card_pow_eq (d : ℕ)
    [HasEnoughRootsOfUnity R (Monoid.exponent (Mˣ ⧸ (powMonoidHom d : Mˣ →* Mˣ).range))]
    (u : Mˣ) [DecidablePred fun χ : MulChar M R ↦ χ ^ d = 1] :
    ∑ χ : MulChar M R with χ ^ d = 1, χ u = (Nat.card {y : Mˣ // y ^ d = u} : R) := by
  classical
  set f : Mˣ →* Mˣ := powMonoidHom d
  have hfilter : (univ.filter fun χ : MulChar M R ↦ χ ^ d = 1) =
      univ.filter fun χ : MulChar M R ↦ ∀ h ∈ f.range, χ h = 1 := by
    ext χ
    simp [f, pow_eq_one_iff_forall_mem_range_apply_eq_one]
  rw [hfilter, Subgroup.sum_filter_mulChar_apply_eq_ite]
  split_ifs with hu
  · -- The `d`-th roots of `f x` form a fiber of `f`, which has as many elements as its kernel.
    obtain ⟨x, rfl⟩ := hu
    rw [Subgroup.index_range, ← f.card_fiber_eq_card_ker (a := x) rfl]
    simp only [f, powMonoidHom_apply]
  · -- No `y` has `f y = u`, since `u` is not in the range of `f`.
    have : IsEmpty {y : Mˣ // y ^ d = u} :=
      ⟨fun y ↦ hu <| MonoidHom.mem_range.2
        ⟨y, by simpa only [f, powMonoidHom_apply] using y.property⟩⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]

section GroupWithZero

variable {F : Type*} [CommGroupWithZero F] [Finite F] [Fintype (MulChar F R)]

/-- **The number of solutions of `y ^ d = c` in a finite field.** Let `F` be a finite field, or
more generally a finite commutative group with zero, and let the coefficient domain have enough
roots of unity for the exponent of the quotient of `Fˣ` by its `d`-th powers. For `d ≠ 0` and
every `c ∈ F`, the cast of the number of solutions is `1 + ∑ χ`, the sum over the nontrivial
characters `χ` with `χ ^ d = 1` at `c`. At `c = 0` both sides are `1`: every character, the
trivial one included, vanishes at `0`. -/
theorem card_pow_eq_eq_one_add_sum_filter_mulChar {d : ℕ} (hd : d ≠ 0)
    [HasEnoughRootsOfUnity R (Monoid.exponent (Fˣ ⧸ (powMonoidHom d : Fˣ →* Fˣ).range))] (c : F)
    [DecidablePred fun χ : MulChar F R ↦ χ ^ d = 1 ∧ χ ≠ 1] :
    (Nat.card {y : F // y ^ d = c} : R) = 1 + ∑ χ : MulChar F R with χ ^ d = 1 ∧ χ ≠ 1, χ c := by
  classical
  by_cases hc : c = 0
  · subst hc
    have : Nat.card {y : F // y ^ d = 0} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨⟨0, zero_pow hd⟩, fun y ↦ Subtype.ext ((pow_eq_zero_iff hd).mp y.property)⟩
    rw [this, Nat.cast_one, left_eq_add]
    exact sum_eq_zero fun χ _ ↦ χ.map_zero
  · lift c to Fˣ using IsUnit.mk0 c hc
    have hsplit := add_sum_erase (univ.filter fun χ : MulChar F R ↦ χ ^ d = 1)
      (fun χ ↦ χ (c : F)) (by simp : (1 : MulChar F R) ∈ _)
    rw [← filter_ne', filter_filter, one_apply_coe,
      sum_filter_mulChar_pow_eq_one_apply_eq_card_pow_eq] at hsplit
    -- The solutions in `F` are nonzero, so they are the solutions in `Fˣ`.
    have hne {y : F} (hy : y ^ d = c) : y ≠ 0 := fun h ↦ hc (by rw [← hy, h, zero_pow hd])
    have hcard : Nat.card {y : F // y ^ d = c} = Nat.card {y : Fˣ // y ^ d = c} :=
      Nat.card_congr <| (Equiv.subtypeSubtypeEquivSubtype hne).symm.trans
        (unitsEquivNeZero.subtypeEquiv fun y ↦ by simp [Units.ext_iff]).symm
    rw [hcard, ← hsplit]
    -- The two sides differ only in the decidability instance of the filter.
    congr

end GroupWithZero

end TauCeti
