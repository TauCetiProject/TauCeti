/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import TauCeti.NumberTheory.BinaryQuadraticForm.Content

/-!
# Lagrange reduction of binary quadratic forms of nonsquare discriminant

An integral binary quadratic form `a x² + b x y + c y²` is **Lagrange reduced** when
`|b| ≤ |a| ≤ |c|`. Every form of nonsquare discriminant `D`, of either sign, is properly
equivalent to a Lagrange reduced form. Choose a form in the `SL(2, ℤ)`-class whose leading
coefficient has least absolute value; this least value is not zero, because a form of nonsquare
discriminant does not represent zero on a primitive vector. A power of `T` then moves `b` into
`[-|a|, |a|]` without changing `a`, and `|a| ≤ |c|` holds because `c` is the leading
coefficient of a properly equivalent form.

A Lagrange reduced form satisfies `3 |a| |c| ≤ |D|` whatever the sign of `D`. If `a c ≥ 0`, then
`-D = 4 a c - b² ≥ 3 a c` because `b² ≤ a² ≤ a c`. If `a c < 0`, then `D = b² + 4 |a c|`. For
`D ≠ 0` the coefficients `a` and `c` are nonzero, so `|b| ≤ |a| ≤ √(|D| / 3)` and
`|c| ≤ |D| / 3`. Hence `lagrangeReducedForms D`, the set of Lagrange reduced forms of
discriminant `D`, is an explicit finite and decidable set.

Together these give finiteness of classes for every nonsquare discriminant: forms of discriminant
`D` fall into finitely many `SL(2, ℤ)`-classes. In particular there are finitely many proper
classes of primitive forms of discriminant `D`. For `D > 0` these are the indefinite forms, which
the positive definite reduction theory of `TauCeti.reducedForms` does not cover; for `D < 0` that
theory moreover counts the positive definite classes exactly. Unlike the reduced forms of a
positive definite class, a class of indefinite forms can contain several Lagrange reduced forms:
`x² + x y - y²` and `-x² - x y + y²` are both Lagrange reduced of discriminant `5`, and the
rotation `S` carries the first to the second. So `lagrangeReducedForms D` meets every class
without counting the classes.

## Main definitions

* `TauCeti.BinaryQuadraticForm.IsLagrangeReduced`: the form satisfies `|b| ≤ |a| ≤ |c|`.
* `TauCeti.BinaryQuadraticForm.lagrangeReducedForms D`: for `D ≠ 0`, the finite set of Lagrange
  reduced forms of discriminant `D`.

## Main results

* `TauCeti.BinaryQuadraticForm.IsLagrangeReduced.three_mul_abs_a_mul_abs_c_le_abs_discrim`: a
  Lagrange reduced form has `3 |a| |c| ≤ |D|`.
* `TauCeti.BinaryQuadraticForm.mem_lagrangeReducedForms`: for `D ≠ 0`, the set
  `lagrangeReducedForms D` contains every Lagrange reduced form of discriminant `D`.
* `TauCeti.BinaryQuadraticForm.exists_smul_isLagrangeReduced`: every form of nonsquare
  discriminant is properly equivalent to a Lagrange reduced form.
* `TauCeti.BinaryQuadraticForm.finite_orbitRel_quotient_of_forall_discrim_eq`: a set of forms of
  one nonsquare discriminant, stable under `SL(2, ℤ)`, has finitely many classes.
* `TauCeti.BinaryQuadraticForm.finite_orbitRel_quotient_primitiveForms`: there are finitely many
  proper classes of primitive forms of nonsquare discriminant `D`, an instance under
  `[Fact (¬ IsSquare D)]`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2, Theorem 2.8, for Lagrange's argument in the
  positive definite case.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 13, for binary forms of arbitrary
  discriminant.
-/

public section

open Finset MulAction
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- The integral binary quadratic form `f = a x² + b x y + c y²` is **Lagrange reduced**:
`|b| ≤ |a| ≤ |c|`.

Every form of nonsquare discriminant is properly equivalent to a Lagrange reduced form
(`exists_smul_isLagrangeReduced`), and for a nonzero discriminant there are only finitely many
Lagrange reduced forms (`mem_lagrangeReducedForms`). A class can contain several of them. -/
def IsLagrangeReduced (f : BinaryQuadraticForm ℤ) : Prop :=
  |f.b| ≤ |f.a| ∧ |f.a| ≤ |f.c|
deriving Decidable

/-- The form `f = a x² + b x y + c y²` is Lagrange reduced exactly when `|b| ≤ |a| ≤ |c|`. -/
theorem isLagrangeReduced_iff {f : BinaryQuadraticForm ℤ} :
    f.IsLagrangeReduced ↔ |f.b| ≤ |f.a| ∧ |f.a| ≤ |f.c| :=
  Iff.rfl

namespace IsLagrangeReduced

variable {f : BinaryQuadraticForm ℤ}

/-- A Lagrange reduced form `a x² + b x y + c y²` has `3 |a| |c| ≤ |b² - 4 a c|`. -/
theorem three_mul_abs_a_mul_abs_c_le_abs_discrim (hf : f.IsLagrangeReduced) :
    3 * (|f.a| * |f.c|) ≤ |f.discrim| := by
  obtain ⟨hb, hac⟩ := hf
  -- `b² ≤ a² ≤ |a| |c|`
  have hbb : f.b ^ 2 ≤ |f.a| * |f.c| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg f.b, abs_nonneg f.a]
  rw [← abs_mul] at hbb
  rw [discrim_def, discrim, ← abs_mul]
  rcases le_or_gt 0 (f.a * f.c) with h | h
  · -- `D = b² - 4 a c ≤ -3 a c ≤ 0`
    rw [abs_of_nonneg h] at hbb ⊢
    rw [le_abs]
    right
    linarith
  · -- `D = b² + 4 |a c| ≥ 3 |a c|`
    rw [abs_of_neg h] at hbb ⊢
    rw [le_abs]
    left
    nlinarith [sq_nonneg f.b]

/-- A Lagrange reduced form of nonzero discriminant has nonzero leading coefficient. -/
theorem a_ne_zero (hf : f.IsLagrangeReduced) (hD : f.discrim ≠ 0) : f.a ≠ 0 := by
  intro ha
  have hb : f.b = 0 := abs_nonpos_iff.mp (by simpa [ha] using hf.1)
  exact hD (by simp [discrim_def, discrim, ha, hb])

/-- A Lagrange reduced form of nonzero discriminant has nonzero last coefficient. -/
theorem c_ne_zero (hf : f.IsLagrangeReduced) (hD : f.discrim ≠ 0) : f.c ≠ 0 := by
  intro hc
  exact hf.a_ne_zero hD (abs_nonpos_iff.mp (by simpa [hc] using hf.2))

end IsLagrangeReduced

/-- The Lagrange reduced forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = D`.

The definition searches the box `|a| ≤ √(|D| / 3)`, `|b| ≤ √(|D| / 3)`, `|c| ≤ |D| / 3` (with
`Nat.sqrt` and natural division), which makes it a finite, decidable set;
`mem_lagrangeReducedForms` shows that for `D ≠ 0` this box loses nothing. For `D = 0` the box only
contains the zero form (`lagrangeReducedForms_zero`). -/
def lagrangeReducedForms (D : ℤ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ (Icc (-(D.natAbs / 3).sqrt : ℤ) (D.natAbs / 3).sqrt ×ˢ
      Icc (-(D.natAbs / 3).sqrt : ℤ) (D.natAbs / 3).sqrt ×ˢ
      Icc (-(D.natAbs / 3 : ℕ) : ℤ) (D.natAbs / 3 : ℕ)).map equivProd.symm.toEmbedding |
    f.discrim = D ∧ f.IsLagrangeReduced}

/-- The search box of `lagrangeReducedForms 0` contains only the zero form, which is Lagrange
reduced of discriminant `0`. -/
@[simp] theorem lagrangeReducedForms_zero : lagrangeReducedForms 0 = {0} := by
  ext f
  simp +contextual [lagrangeReducedForms, IsLagrangeReduced, discrim_def, discrim,
    BinaryQuadraticForm.ext_iff, and_assoc]

/-- **The Lagrange reduced forms of discriminant `D`**: for `D ≠ 0`, `f ∈ lagrangeReducedForms D`
exactly when `f.discrim = D` and `f` is Lagrange reduced, so the box that `lagrangeReducedForms`
searches loses nothing. -/
@[simp] theorem mem_lagrangeReducedForms {D : ℤ} (hD : D ≠ 0) {f : BinaryQuadraticForm ℤ} :
    f ∈ lagrangeReducedForms D ↔ f.discrim = D ∧ f.IsLagrangeReduced := by
  refine mem_filter.trans <| and_iff_right_of_imp fun ⟨hd, hf⟩ ↦ mem_map_equiv.2 ?_
  have ha := hf.a_ne_zero (hd ▸ hD)
  -- `3 |a|² ≤ 3 |a| |c| ≤ |D|` and `3 |c| ≤ 3 |a| |c| ≤ |D|`, in natural numbers
  have h3 : 3 * (f.a.natAbs * f.c.natAbs) ≤ D.natAbs := by
    have := hf.three_mul_abs_a_mul_abs_c_le_abs_discrim
    simp only [hd, Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hb : f.b.natAbs ≤ f.a.natAbs := by
    have := hf.1
    simp only [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hac : f.a.natAbs * f.a.natAbs ≤ f.a.natAbs * f.c.natAbs := by
    have := hf.2
    simp only [Int.abs_eq_natAbs] at this
    exact Nat.mul_le_mul_left _ (by exact_mod_cast this)
  have hc : f.c.natAbs ≤ f.a.natAbs * f.c.natAbs :=
    Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr ha)
  have hsq : f.a.natAbs ≤ (D.natAbs / 3).sqrt := Nat.le_sqrt.2 <| by lia
  simp only [Equiv.symm_symm, equivProd_apply, mem_product, mem_Icc, ← abs_le,
    Int.abs_eq_natAbs]
  lia

/-- **Lagrange reduction**: every integral binary quadratic form of nonsquare discriminant is
properly equivalent to a Lagrange reduced form. -/
theorem exists_smul_isLagrangeReduced (f : BinaryQuadraticForm ℤ) (hf : ¬ IsSquare f.discrim) :
    ∃ γ : SL(2, ℤ), (γ • f).IsLagrangeReduced := by
  classical
  -- a form `g = γ₀ • f` in the class of `f` whose leading coefficient has least absolute value
  have hex : ∃ n : ℕ, ∃ γ : SL(2, ℤ), (γ • f).a.natAbs = n := ⟨_, 1, rfl⟩
  obtain ⟨γ₀, hγ₀⟩ := Nat.find_spec hex
  set g := γ₀ • f
  have hmin (γ : SL(2, ℤ)) : |g.a| ≤ |(γ • g).a| := by
    have h := hγ₀ ▸ Nat.find_min' hex ⟨γ * γ₀, rfl⟩
    rw [mul_smul] at h
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact Int.ofNat_le.mpr h
  have ha : g.a ≠ 0 := a_ne_zero_of_not_isSquare_discrim (by rwa [discrim_smul])
  -- a translation `T ^ k` moves `b` into `[-|a|, |a|]`, as `b - 2 a k = b.bmod (2 |a|)`
  have hm : 0 < (2 * g.a).natAbs := Int.natAbs_pos.mpr (mul_ne_zero two_ne_zero ha)
  have hm' : ((2 * g.a).natAbs : ℤ) = 2 * |g.a| := by
    rw [Int.natCast_natAbs, abs_mul, abs_two]
  obtain ⟨k, hk⟩ := Int.natAbs_dvd.mp (Int.dvd_self_sub_bmod (x := g.b) (m := (2 * g.a).natAbs))
  have hb : |g.b - 2 * g.a * k| ≤ |g.a| := by
    have h₁ := Int.le_bmod (x := g.b) hm
    have h₂ := Int.bmod_lt (x := g.b) hm
    rw [hm'] at h₁ h₂
    rw [abs_le]
    constructor <;> lia
  -- the last coefficient is the leading coefficient of `S • T ^ k • g`, a form in the class
  have hc := hmin (ModularGroup.S * ModularGroup.T ^ k)
  rw [mul_smul, S_smul, T_zpow_smul] at hc
  refine ⟨ModularGroup.T ^ k * γ₀, ?_⟩
  rw [mul_smul, T_zpow_smul]
  exact ⟨hb, hc⟩

/-- A form of nonsquare discriminant is properly equivalent to a member of the finite set
`lagrangeReducedForms` of its discriminant. -/
theorem exists_smul_mem_lagrangeReducedForms (f : BinaryQuadraticForm ℤ)
    (hf : ¬ IsSquare f.discrim) : ∃ γ : SL(2, ℤ), γ • f ∈ lagrangeReducedForms f.discrim := by
  have hD : f.discrim ≠ 0 := fun h ↦ hf (h ▸ IsSquare.zero)
  obtain ⟨γ, hγ⟩ := exists_smul_isLagrangeReduced f hf
  exact ⟨γ, (mem_lagrangeReducedForms hD).2 ⟨discrim_smul γ f, hγ⟩⟩

/-- **Finiteness of classes of nonsquare discriminant**: a set of integral binary quadratic forms
of one nonsquare discriminant `D`, stable under `SL(2, ℤ)`, falls into finitely many
`SL(2, ℤ)`-classes. The finitely many Lagrange reduced forms of discriminant `D` meet every
class. -/
theorem finite_orbitRel_quotient_of_forall_discrim_eq {D : ℤ} (hD : ¬ IsSquare D)
    (s : SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ)) (hs : ∀ f ∈ s, f.discrim = D) :
    Finite (orbitRel.Quotient SL(2, ℤ) s) := by
  -- the members of `s` in `lagrangeReducedForms D` form a finite set meeting every class
  let R := {f : s // f.1 ∈ lagrangeReducedForms D}
  have : Finite R :=
    .of_injective (fun f : R ↦ (⟨f.1.1, f.2⟩ : lagrangeReducedForms D)) fun f g h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  refine .of_surjective (fun f : R ↦ (Quotient.mk'' f.1 : orbitRel.Quotient SL(2, ℤ) s))
    (Quotient.ind' fun f ↦ ?_)
  obtain ⟨γ, hγ⟩ := exists_smul_mem_lagrangeReducedForms f.1 (hs f.1 f.2 ▸ hD)
  exact ⟨⟨γ • f, hs f.1 f.2 ▸ hγ⟩, Quotient.sound' ⟨γ, rfl⟩⟩

/-- There are finitely many proper equivalence classes of primitive integral binary quadratic
forms of a nonsquare discriminant `D`, positive or negative. -/
instance finite_orbitRel_quotient_primitiveForms {D : ℤ} [Fact (¬ IsSquare D)] :
    Finite (orbitRel.Quotient SL(2, ℤ) (primitiveForms D)) :=
  finite_orbitRel_quotient_of_forall_discrim_eq Fact.out _ fun f hf ↦
    ((mem_primitiveForms D f).1 hf).1

/-! The two Lagrange reduced forms `x² + x y - y²` and `-x² - x y + y²` of discriminant `5` are
properly equivalent, by the rotation `S`; so a class can contain several Lagrange reduced forms. -/

example : (⟨1, 1, -1⟩ : BinaryQuadraticForm ℤ).IsLagrangeReduced ∧
    (⟨-1, -1, 1⟩ : BinaryQuadraticForm ℤ).IsLagrangeReduced := by
  decide

example : ModularGroup.S • (⟨1, 1, -1⟩ : BinaryQuadraticForm ℤ) = ⟨-1, -1, 1⟩ := by
  simp

end TauCeti.BinaryQuadraticForm
