/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import TauCeti.Analysis.AbsoluteValue.Action
public import TauCeti.Analysis.AbsoluteValue.Equivalence

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.AbsoluteValue.Rpow

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
`L` is equivalent to at most one place (`AbsoluteValue.Place.subsingleton_setOf_isEquiv`). An
absolute value `w` whose restriction to `ℚ` is nontrivial is equivalent to exactly one place
(`AbsoluteValue.Place.existsUnique_isEquiv_of_isNontrivial_under`), its `ℚ`-normalised
representative `AbsoluteValue.toPlace`. By Ostrowski's theorem `w.under ℚ` is the `c`-th root of the
real or of a `p`-adic absolute value for some `c > 0`, and `x ↦ w x ^ c` is the place: in both
cases it is at most the real absolute value on the natural numbers, which is enough for the
triangle inequality (`AbsoluteValue.rpowOfNatCast`). When `L` is algebraic over `ℚ`, the
restriction to `ℚ` of a nontrivial absolute value is nontrivial
(`AbsoluteValue.isNontrivial_iff_of_liesOver`), so every nontrivial absolute value of `L` is
equivalent to exactly one place (`AbsoluteValue.Place.existsUnique_isEquiv`), and the places are
the places of `L` in the classical sense. For a field that is not algebraic over `ℚ` the places are
only the `ℚ`-normalised absolute values: on `ℚ(t)` the `t`-adic absolute value is nontrivial and
trivial on `ℚ`, so it is equivalent to no place.

The comparisons with Mathlib's `NumberField.InfinitePlace` and `NumberField.FinitePlace` are in
`TauCeti.NumberTheory.NumberField.PlacesOver.Place`.

## Main definitions

* `AbsoluteValue.Place L`: the `ℚ`-normalised absolute values of a field `L` of characteristic zero.
* `AbsoluteValue.Place.under K`: the restriction of a place to a subfield `K`.
* `AbsoluteValue.Place.instMulAction`: the action `(g • w) x = w (g⁻¹ • x)` of a group acting on `L`
  by ring automorphisms.
* `AbsoluteValue.toPlace`: the place equivalent to an absolute value whose restriction to `ℚ` is
  nontrivial.

## Main results

* `AbsoluteValue.Place.eq_of_isEquiv`, `AbsoluteValue.Place.isEquiv_iff_eq`: equivalent places are
  equal.
* `AbsoluteValue.Place.isNonarchimedean_iff`, `AbsoluteValue.Place.not_isNonarchimedean_iff`: a
  place is finite if and only if its restriction to `ℚ` is `p`-adic, and infinite if and only if it
  is real.
* `AbsoluteValue.Place.under_smul`: the action does not change the restriction to a subfield that
  the group fixes pointwise.
* `AbsoluteValue.Place.existsUnique_isEquiv_of_isNontrivial_under`,
  `AbsoluteValue.Place.existsUnique_isEquiv`: an absolute value whose restriction to `ℚ` is
  nontrivial, and so, when `L` is algebraic over `ℚ`, every nontrivial absolute value, is
  equivalent to exactly one place.
* `AbsoluteValue.toPlace_eq_iff`, `AbsoluteValue.Place.toPlace_val`, `AbsoluteValue.toPlace_smul`,
  `AbsoluteValue.under_toPlace`: the normalised representative is characterised by equivalence,
  is the identity on places, and commutes with the action and with restriction.

## Acknowledgments

Using absolute values for the places of algebraic extensions of `ℚ`, so that finite and infinite
places are one type, follows the advice of Thomas Browning and Jz Pan on the Lean Zulip, in the
Riemann-Hypothesis channel, topic Library design discrepancies between RH/Mathlib/TauCeti:
<https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780662>
and
<https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643806146>.

The construction of the normalised representative `AbsoluteValue.toPlace` follows
`AbsoluteValue.normalization` in Jz Pan's lean-iwasawa
(<https://github.com/acmepjz/lean-iwasawa>, branch `autoformalize.v1` at `7666c16`,
`Iwasawalib/NumberTheory/AbsoluteValue/Normalization.lean`, Apache 2.0).

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

/-! ### The place equivalent to an absolute value -/

section Normalisation

variable {w : AbsoluteValue L ℝ}

/-- **Existence of the normalised representative.** An absolute value of `L` whose restriction to
`ℚ` is nontrivial is equivalent to a place. -/
theorem exists_isEquiv_of_isNontrivial_under (hw : (w.under ℚ).IsNontrivial) :
    ∃ v : Place L, w.IsEquiv v.val := by
  -- By Ostrowski's theorem `w.under ℚ` is equivalent to a standard absolute value `u`, which is
  -- at most the real absolute value on the natural numbers.
  obtain ⟨u, hu, hun, h⟩ : ∃ u : AbsoluteValue ℚ ℝ, Rat.AbsoluteValue.IsStandard u ∧
      (∀ n : ℕ, u n ≤ n) ∧ (w.under ℚ).IsEquiv u := by
    rcases Rat.AbsoluteValue.equiv_real_or_padic _ hw with h | ⟨p, ⟨_, h⟩, -⟩
    · exact ⟨_, .real, fun n ↦ by simp, h⟩
    · refine ⟨_, .padic p, fun n ↦ ?_, h⟩
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · exact (Rat.AbsoluteValue.padic_le_one p n).trans
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  obtain ⟨c, hc, hcw⟩ := isEquiv_iff_exists_rpow_eq.mp h
  have hn (n : ℕ) : w n ^ c ≤ n := by
    simpa [under_apply] using (congrFun hcw n).trans_le (hun n)
  refine ⟨⟨w.rpowOfNatCast hc hn, ?_⟩, isEquiv_iff_exists_rpow_eq.mpr
    ⟨c, hc, funext fun x ↦ (rpowOfNatCast_apply w hc hn x).symm⟩⟩
  convert hu using 1
  ext q
  simpa [under_apply] using congrFun hcw q

/-- An absolute value of `L` whose restriction to `ℚ` is nontrivial is equivalent to exactly one
place. -/
theorem existsUnique_isEquiv_of_isNontrivial_under (hw : (w.under ℚ).IsNontrivial) :
    ∃! v : Place L, w.IsEquiv v.val :=
  let ⟨v, hv⟩ := exists_isEquiv_of_isNontrivial_under hw
  ⟨v, hv, fun _ hu ↦ eq_of_isEquiv (hu.symm.trans hv)⟩

/-- **Places of an algebraic extension of `ℚ`.** Every nontrivial absolute value of a field
algebraic over `ℚ` is equivalent to exactly one place. -/
theorem existsUnique_isEquiv [Algebra.IsAlgebraic ℚ L] (hw : w.IsNontrivial) :
    ∃! v : Place L, w.IsEquiv v.val :=
  existsUnique_isEquiv_of_isNontrivial_under ((isNontrivial_iff_of_liesOver w (w.under ℚ)).mp hw)

/-- Every nontrivial absolute value of a field algebraic over `ℚ` is equivalent to a place. -/
theorem exists_isEquiv [Algebra.IsAlgebraic ℚ L] (hw : w.IsNontrivial) :
    ∃ v : Place L, w.IsEquiv v.val :=
  (existsUnique_isEquiv hw).exists

end Normalisation

end Place

variable {L}

/-- The place equivalent to an absolute value `w` of `L` whose restriction to `ℚ` is nontrivial:
the `ℚ`-normalised representative of `w`. -/
noncomputable def toPlace (w : AbsoluteValue L ℝ) (hw : (w.under ℚ).IsNontrivial) : Place L :=
  (Place.exists_isEquiv_of_isNontrivial_under hw).choose

variable {w : AbsoluteValue L ℝ} (hw : (w.under ℚ).IsNontrivial)

/-- An absolute value is equivalent to its normalised representative. -/
theorem isEquiv_toPlace : w.IsEquiv (w.toPlace hw).val :=
  (Place.exists_isEquiv_of_isNontrivial_under hw).choose_spec

/-- The normalised representative of `w` is the unique place equivalent to `w`. -/
theorem toPlace_eq_iff {v : Place L} : w.toPlace hw = v ↔ w.IsEquiv v.val :=
  ⟨fun h ↦ h ▸ isEquiv_toPlace hw,
    fun h ↦ Place.eq_of_isEquiv ((isEquiv_toPlace hw).symm.trans h)⟩

/-- Equivalent absolute values have the same normalised representative. -/
theorem IsEquiv.toPlace_eq {w' : AbsoluteValue L ℝ} (h : w.IsEquiv w')
    (hw' : (w'.under ℚ).IsNontrivial) : w.toPlace hw = w'.toPlace hw' :=
  (toPlace_eq_iff hw).mpr (h.trans (isEquiv_toPlace hw'))

/-- A place is its own normalised representative. -/
@[simp]
theorem Place.toPlace_val (v : Place L) : v.val.toPlace v.isStandard_under.isNontrivial = v :=
  (toPlace_eq_iff _).mpr .rfl

/-- Taking the normalised representative commutes with the action of a group of ring
automorphisms. -/
theorem toPlace_smul {G : Type*} [Group G] [MulSemiringAction G L] (g : G) :
    (g • w).toPlace (by rwa [under_smul]) = g • w.toPlace hw :=
  (toPlace_eq_iff _).mpr fun x y ↦ by
    simpa only [smul_apply, Place.val_smul] using isEquiv_toPlace hw (g⁻¹ • x) (g⁻¹ • y)

/-- Taking the normalised representative commutes with restriction to a subfield. -/
theorem under_toPlace (K : Type*) [Field K] [CharZero K] [Algebra K L] :
    (w.toPlace hw).under K = (w.under K).toPlace (by rwa [under_under]) :=
  ((toPlace_eq_iff _).mpr fun x y ↦ by
    simpa only [under_apply, Place.val_under] using
      isEquiv_toPlace hw (algebraMap K L x) (algebraMap K L y)).symm

end AbsoluteValue
