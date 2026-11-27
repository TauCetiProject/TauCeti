/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Range

/-!
# Value groups of monoid-with-zero homomorphisms

This file records two facts about the value group `valueGroup f ≤ Bˣ` of a monoid-with-zero
homomorphism `f : A →*₀ B`: how its embedding with zero adjoined evaluates, and how it relates to
surjectivity of `f`.

For a monoid-with-zero homomorphism `f : A →*₀ B` into a group with zero, the embedding
`MonoidWithZeroHom.ValueGroup₀.embedding : ValueGroup₀ f →*₀ B` sends an element `x` of the
value group `valueGroup f`, viewed in `ValueGroup₀ f`, to its underlying element of `B`.
Together with `MonoidWithZeroHom.valueGroup.mk_eq_div`, `simp` evaluates the embedding on
`valueGroup.mk f r s hr hs` as `f s / f r`.

A surjective monoid-with-zero homomorphism has full value group, with no condition on the
codomain. Between groups with zero, for instance for a valuation from a division ring into an
ordered group with zero, full value group conversely means surjectivity, so such a map is
surjective as soon as it attains a generator of the units of its codomain.

## Main results

* `MonoidWithZeroHom.ValueGroup₀.embedding_coe`: the embedding sends `x : valueGroup f`, viewed
  in `ValueGroup₀ f`, to `((x : Bˣ) : B)`.
* `MonoidWithZeroHom.mem_valueGroup_iff`: for a homomorphism between groups with zero,
  membership in `f.valueGroup` is equivalent to being attained by `f`.
* `MonoidWithZeroHom.valueGroup_eq_range_unitsMap`: for a homomorphism between groups with zero,
  `f.valueGroup` is the range of `Units.map f.toMonoidHom`.
* `MonoidWithZeroHom.valueGroup_eq_top_of_surjective`: a surjective monoid-with-zero homomorphism
  has full value group.
* `MonoidWithZeroHom.valueGroup_eq_top_iff_surjective`: between groups with zero, the converse
  holds as well.
* `MonoidWithZeroHom.surjective_of_mem_range_of_zpowers_eq_top`: between groups with zero, a map
  that attains a generator of the units of its codomain is surjective.
-/

public section

namespace MonoidWithZeroHom

section GroupWithZero

variable {A B : Type*} [GroupWithZero A] [GroupWithZero B]

/-- For a homomorphism `f : A →*₀ B` between groups with zero, an element `γ : Bˣ` lies in
`f.valueGroup` if and only if `(γ : B)` is attained by `f`. -/
theorem mem_valueGroup_iff {f : A →*₀ B} {γ : Bˣ} :
    γ ∈ f.valueGroup ↔ ∃ a : A, f a = γ := by
  have h := Set.ext_iff.mp (valueGroup_eq_range f) (γ : B)
  simpa [Units.val_inj, Units.ne_zero] using h

/-- For a homomorphism `f : A →*₀ B` between groups with zero, `f.valueGroup` is the range of
`Units.map f.toMonoidHom`. -/
theorem valueGroup_eq_range_unitsMap (f : A →*₀ B) :
    f.valueGroup = (Units.map f.toMonoidHom).range := by
  ext γ
  rw [mem_valueGroup_iff, MonoidHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨a, congrArg Units.val ha⟩⟩
  have ha0 : a ≠ 0 := fun h0 ↦ Units.ne_zero γ (by simpa [h0] using ha.symm)
  exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩

end GroupWithZero

namespace ValueGroup₀

variable {A B : Type*} [MonoidWithZero A] [GroupWithZero B] {f : A →*₀ B}

/-- The embedding of the value group with zero into the codomain sends an element `x` of the
value group, viewed in `ValueGroup₀ f`, to its underlying element `((x : Bˣ) : B)`. -/
@[simp]
theorem embedding_coe (x : valueGroup f) : embedding (x : ValueGroup₀ f) = ((x : Bˣ) : B) := by
  simp [embedding_apply]

end ValueGroup₀

section MonoidWithZero

variable {A B : Type*} [MonoidWithZero A] [MonoidWithZero B]

/-- Surjectivity of `f` makes its value group the whole of `Bˣ`. -/
theorem valueGroup_eq_top_of_surjective (f : A →*₀ B) (hf : Function.Surjective f) :
    f.valueGroup = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun γ ↦ mem_valueGroup _ (hf γ)

/-- A surjective monoid-with-zero homomorphism has nontrivial value group once `Bˣ` is
nontrivial. -/
theorem nontrivial_valueGroup_of_surjective [Nontrivial Bˣ] (f : A →*₀ B)
    (hf : Function.Surjective f) : Nontrivial f.valueGroup :=
  (Subgroup.nontrivial_iff_ne_bot _).mpr <| valueGroup_eq_top_of_surjective f hf ▸ top_ne_bot

end MonoidWithZero

section GroupWithZero

variable {A B : Type*} [GroupWithZero A] [GroupWithZero B]

/-- **Between groups with zero, full value group means surjectivity.** The nonzero values of `f`
are closed under inverses, so they already form the value group. On a ring this fails: the
`t`-adic valuation on `k[t², t³]` has full value group in `ℤᵐ⁰` without attaining `exp (-1)`. -/
theorem valueGroup_eq_top_iff_surjective (f : A →*₀ B) :
    f.valueGroup = ⊤ ↔ Function.Surjective f := by
  refine ⟨fun h b ↦ ?_, valueGroup_eq_top_of_surjective f⟩
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨0, map_zero f⟩
  -- Between groups with zero, the nonzero values of `f` are exactly its value group.
  have hb' : b ∈ Units.val '' (f.valueGroup : Set Bˣ) :=
    ⟨Units.mk0 b hb, h ▸ Subgroup.mem_top _, rfl⟩
  rw [valueGroup_eq_range] at hb'
  exact hb'.1

/-- **Between groups with zero, a map that attains a generator of the units of its codomain is
surjective**: the value group contains that generator, so it is full. -/
theorem surjective_of_mem_range_of_zpowers_eq_top (f : A →*₀ B) {u : Bˣ}
    (hu : (u : B) ∈ Set.range f) (hzu : Subgroup.zpowers u = ⊤) : Function.Surjective f :=
  (valueGroup_eq_top_iff_surjective f).mp <| top_unique <|
    hzu ▸ Subgroup.zpowers_le.mpr (mem_valueGroup _ hu)

end GroupWithZero

end MonoidWithZeroHom
