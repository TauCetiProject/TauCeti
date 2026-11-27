/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Action
public import TauCeti.Analysis.AbsoluteValue.Equivalence

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Places of a field of characteristic zero as `ℚ`-normalised absolute values

For a field `L` of characteristic zero, a *place* of `L` is an absolute value
`w : AbsoluteValue L ℝ` whose restriction `w.under ℚ` to `ℚ` is the real absolute value or a
`p`-adic one (`Rat.AbsoluteValue.IsStandard`). The type of places is the subtype
`AbsoluteValue.Place L := {w : AbsoluteValue L ℝ // Rat.AbsoluteValue.IsStandard (w.under ℚ)}`;
no other normalisation predicate is introduced. Finite and infinite places are one type: a place
`w` is finite when `IsNonarchimedean w`, equivalently when `w.under ℚ` is `p`-adic
(`AbsoluteValue.Place.isNonarchimedean_iff`), and infinite otherwise, equivalently when `w.under ℚ`
is the real absolute value (`AbsoluteValue.Place.not_isNonarchimedean_iff`).

The normalisation on `ℚ` is the one that is stable under restriction: a place of `L` restricts to a
place of every subfield (`AbsoluteValue.Place.under`), and a group acting on `L` by ring
automorphisms acts on the places (`AbsoluteValue.Place.instMulAction`), without changing the
restriction to a subring that it fixes pointwise. It is not the normalisation of Mathlib's
`NumberField.FinitePlace`: on `ℚ(√5)` the place above `5` takes the value `5 ^ (-1/2)` at `√5`,
where `NumberField.FinitePlace` takes the value `1/5`.

Two equivalent places are equal (`AbsoluteValue.Place.eq_of_isEquiv`), so each absolute value of
`L` is equivalent to at most one place (`AbsoluteValue.Place.subsingleton_setOf_isEquiv`). That
every nontrivial absolute value of an algebraic extension of `ℚ` is equivalent to a place is not
proved here. For a field that is not algebraic over `ℚ` the places are only the `ℚ`-normalised
absolute values: on `ℚ(t)` the `t`-adic absolute value is nontrivial and trivial on `ℚ`, so it is
equivalent to no place.

The comparisons with Mathlib's `NumberField.InfinitePlace` and `NumberField.FinitePlace` are in
`TauCeti.NumberTheory.NumberField.PlacesOver.Place`.

## Main definitions

* `AbsoluteValue.Place L`: the `ℚ`-normalised absolute values of a field `L` of characteristic zero.
* `AbsoluteValue.Place.under K`: the restriction of a place to a subfield `K`.
* `AbsoluteValue.Place.comap`: the restriction of a place along a field embedding.
* `AbsoluteValue.Place.instMulAction`: the action `(g • w) x = w (g⁻¹ • x)` of a group acting on `L`
  by ring automorphisms.

## Main results

* `AbsoluteValue.Place.eq_of_isEquiv`, `AbsoluteValue.Place.isEquiv_iff_eq`: equivalent places are
  equal.
* `AbsoluteValue.Place.isNonarchimedean_iff`, `AbsoluteValue.Place.not_isNonarchimedean_iff`: a
  place is finite if and only if its restriction to `ℚ` is `p`-adic, and infinite if and only if it
  is real.
* `AbsoluteValue.Place.apply_natCast_lt_one_of_under_eq_padic`: a place above `p` is less than one
  at `p`.
* `AbsoluteValue.Place.under_smul`: the action does not change the restriction to a subfield that
  the group fixes pointwise.

## Acknowledgments

Using absolute values for the places of algebraic extensions of `ℚ`, so that finite and infinite
places are one type, follows the advice of Thomas Browning and Jz Pan on the Lean Zulip, in the
Riemann-Hypothesis channel, topic Library design discrepancies between RH/Mathlib/TauCeti:
<https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780662>
and
<https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643806146>.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Ch. II, §§3 and 8.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press, 1967,
  Ch. II, §§9 and 10.
-/

public section

namespace AbsoluteValue

variable (L : Type*) [Field L] [CharZero L]

/-- A *place* of a field `L` of characteristic zero: an absolute value `w : AbsoluteValue L ℝ`
whose restriction to `ℚ` is the real absolute value or a `p`-adic one. Finite places
(`IsNonarchimedean w`) and infinite places are one type. -/
@[expose] def Place : Type _ := {w : AbsoluteValue L ℝ // Rat.AbsoluteValue.IsStandard (w.under ℚ)}

namespace Place

variable {L}

instance : FunLike (Place L) L ℝ where
  coe w x := w.val x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext fun x ↦ congr($h x))

theorem coe_apply (w : Place L) (x : L) : w x = w.val x := rfl

@[ext]
theorem ext {v w : Place L} (h : ∀ x, v x = w x) : v = w :=
  Subtype.ext <| AbsoluteValue.ext h

theorem val_injective : Function.Injective (Subtype.val : Place L → AbsoluteValue L ℝ) :=
  Subtype.val_injective

@[simp]
theorem val_inj {v w : Place L} : v.val = w.val ↔ v = w :=
  Subtype.val_inj

instance : MonoidWithZeroHomClass (Place L) L ℝ where
  map_mul w _ _ := w.val.map_mul _ _
  map_one w := w.val.map_one
  map_zero w := w.val.map_zero

instance : NonnegHomClass (Place L) L ℝ where
  apply_nonneg w _ := w.val.nonneg _

/-- The restriction of a place to `ℚ` is the real absolute value or a `p`-adic one. -/
theorem isStandard_under (w : Place L) : Rat.AbsoluteValue.IsStandard (w.val.under ℚ) :=
  w.property

/-- A place agrees on `ℚ` with its restriction to `ℚ`. -/
theorem apply_ratCast (w : Place L) (q : ℚ) : w q = w.val.under ℚ q := by
  rw [under_apply, eq_ratCast (algebraMap ℚ L), coe_apply]

private theorem val_natCast (w : Place L) (n : ℕ) : w.val n = w.val.under ℚ n := by
  rw [AbsoluteValue.under_apply, map_natCast (algebraMap ℚ L)]

/-- A place is a nontrivial absolute value. -/
theorem isNontrivial (w : Place L) : w.val.IsNontrivial :=
  isNontrivial_of_forall_natCast_eq w.isStandard_under.isNontrivial w.val_natCast

/-- **Equivalent places are equal.** -/
theorem eq_of_isEquiv {v w : Place L} (h : v.val.IsEquiv w.val) : v = w :=
  Subtype.ext <| h.eq_of_isStandard v.isStandard_under w.isStandard_under
    v.val_natCast w.val_natCast

theorem isEquiv_iff_eq {v w : Place L} : v.val.IsEquiv w.val ↔ v = w :=
  ⟨eq_of_isEquiv, fun h ↦ h ▸ .rfl⟩

/-- An absolute value is equivalent to at most one place. -/
theorem subsingleton_setOf_isEquiv (u : AbsoluteValue L ℝ) :
    {w : Place L | w.val.IsEquiv u}.Subsingleton :=
  fun _ hv _ hw ↦ eq_of_isEquiv (hv.trans hw.symm)

/-! ### Finite and infinite places -/

/-- A place is finite if and only if its restriction to `ℚ` is a `p`-adic absolute value. -/
theorem isNonarchimedean_iff (w : Place L) :
    IsNonarchimedean w.val ↔
      ∃ (p : ℕ) (_ : Fact p.Prime), w.val.under ℚ = Rat.AbsoluteValue.padic p := by
  rw [isNonarchimedean_iff_of_liesOver w.val (w.val.under ℚ)]
  rcases Rat.AbsoluteValue.isStandard_iff.mp w.isStandard_under with h | h
  · rw [h]
    refine iff_of_false Rat.AbsoluteValue.not_isNonarchimedean_real ?_
    rintro ⟨p, _, hp⟩
    exact Rat.AbsoluteValue.not_real_isEquiv_padic p (hp ▸ .rfl)
  · refine iff_of_true ?_ h
    obtain ⟨p, _, hp⟩ := h
    rw [hp, isNonarchimedean_iff_forall_natCast_le_one]
    exact fun n ↦ by exact_mod_cast Rat.AbsoluteValue.padic_le_one p n

/-- A place above the prime number `p` takes a value less than one at `p`. -/
theorem apply_natCast_lt_one_of_under_eq_padic {w : Place L} {p : ℕ} [Fact p.Prime]
    (hp : w.val.under ℚ = Rat.AbsoluteValue.padic p) : w.val (p : L) < 1 := by
  have h1 : w.val (p : L) = Rat.AbsoluteValue.padic p (p : ℚ) := by
    rw [← hp, AbsoluteValue.under_apply]
    simp
  rw [h1, Rat.AbsoluteValue.padic_eq_padicNorm]
  exact_mod_cast padicNorm.padicNorm_p_lt_one_of_prime

/-- A place is infinite if and only if its restriction to `ℚ` is the real absolute value. -/
theorem not_isNonarchimedean_iff (w : Place L) :
    ¬ IsNonarchimedean w.val ↔ w.val.under ℚ = Rat.AbsoluteValue.real := by
  rw [isNonarchimedean_iff]
  rcases Rat.AbsoluteValue.isStandard_iff.mp w.isStandard_under with h | h
  · refine iff_of_true ?_ h
    rintro ⟨p, _, hp⟩
    exact Rat.AbsoluteValue.not_real_isEquiv_padic p (h ▸ hp ▸ .rfl)
  · refine iff_of_false (not_not_intro h) fun hr ↦ ?_
    obtain ⟨p, _, hp⟩ := h
    exact Rat.AbsoluteValue.not_real_isEquiv_padic p (hr ▸ hp ▸ .rfl)

/-! ### Restriction to a subfield -/

section under

variable (K : Type*) [Field K] [CharZero K] [Algebra K L]

/-- The restriction of a place of `L` to a subfield `K` is a place of `K`. -/
def under (w : Place L) : Place K :=
  ⟨w.val.under K, by rw [AbsoluteValue.under_under]; exact w.isStandard_under⟩

@[simp]
theorem val_under (w : Place L) : (w.under K).val = w.val.under K := (rfl)

@[simp]
theorem under_apply (w : Place L) (x : K) : w.under K x = w (algebraMap K L x) := (rfl)

/-- A place of `L` lies over a place `v` of `K` exactly when its restriction to `K` is `v`. -/
theorem liesOver_iff_under_eq {w : Place L} {v : Place K} :
    w.val.LiesOver v.val ↔ w.under K = v := by
  rw [AbsoluteValue.liesOver_iff, ← val_inj, val_under]

/-- A place lies over its restriction. -/
instance (w : Place L) : w.val.LiesOver (w.under K).val :=
  (liesOver_iff_under_eq K).mpr rfl

@[simp]
theorem under_self (w : Place L) : w.under L = w := (rfl)

/-- Restriction is transitive in a tower `K ⊆ M ⊆ L`. -/
@[simp]
theorem under_under (M : Type*) [Field M] [CharZero M] [Algebra K M] [Algebra M L]
    [IsScalarTower K M L] (w : Place L) : (w.under M).under K = w.under K :=
  Subtype.ext <| AbsoluteValue.under_under K M w.val

end under

/-! ### Restriction along a field embedding -/

section comap

variable {M : Type*} [Field M] [CharZero M]

/-- The restriction of a place of `M` along a field embedding `f : L →+* M` is a place of `L`. -/
def comap (w : Place M) (f : L →+* M) : Place L :=
  ⟨w.val.comp f.injective, by
    have : (w.val.comp f.injective).under ℚ = w.val.under ℚ :=
      AbsoluteValue.ext fun q ↦ by
        rw [AbsoluteValue.under_apply, AbsoluteValue.under_apply, comp_apply,
          eq_ratCast (algebraMap ℚ L), map_ratCast f, eq_ratCast (algebraMap ℚ M)]
    rw [this]
    exact w.isStandard_under⟩

@[simp]
theorem val_comap (w : Place M) (f : L →+* M) : (w.comap f).val = w.val.comp f.injective := (rfl)

@[simp]
theorem comap_apply (w : Place M) (f : L →+* M) (x : L) : w.comap f x = w (f x) := (rfl)

/-- Restricting along a field embedding does not change the restriction to `ℚ`. -/
@[simp]
theorem under_comap (w : Place M) (f : L →+* M) : (w.comap f).under ℚ = w.under ℚ :=
  ext fun q ↦ by rw [under_apply, under_apply, comap_apply, eq_ratCast (algebraMap ℚ L),
    map_ratCast f, eq_ratCast (algebraMap ℚ M)]

end comap

/-! ### The action of a group of ring automorphisms -/

section MulAction

variable {G : Type*} [Group G] [MulSemiringAction G L]

/-- A group acting on `L` by ring automorphisms acts on the places of `L` by
`(g • w) x = w (g⁻¹ • x)`. -/
instance instMulAction : MulAction G (Place L) where
  smul g w := ⟨g • w.val, by rw [AbsoluteValue.under_smul]; exact w.isStandard_under⟩
  one_smul w := Subtype.ext (one_smul G w.val)
  mul_smul g h w := Subtype.ext (mul_smul g h w.val)

@[simp]
theorem val_smul (g : G) (w : Place L) : (g • w).val = g • w.val := rfl

@[simp]
theorem smul_apply (g : G) (w : Place L) (x : L) : (g • w) x = w (g⁻¹ • x) := rfl

/-- The stabiliser of a place is the stabiliser of its underlying absolute value. -/
theorem stabilizer_eq (w : Place L) :
    MulAction.stabilizer G w = MulAction.stabilizer G w.val := by
  ext g
  simp [MulAction.mem_stabilizer_iff, ← val_inj]

/-- A group fixing a subfield `K` pointwise does not change the restriction of a place to `K`. -/
@[simp]
theorem under_smul (K : Type*) [Field K] [CharZero K] [Algebra K L] [SMulCommClass G K L]
    (g : G) (w : Place L) : (g • w).under K = w.under K :=
  Subtype.ext <| AbsoluteValue.under_smul g w.val

end MulAction

end Place

end AbsoluteValue
