/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import TauCeti.Data.Nat.Choose.Dvd
public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# δ-structures on square-zero extensions by `ZMod p`

Let `B` be a `δ`-ring with a ring homomorphism `B →+* ZMod p` (the `algebraMap` of an
`Algebra B (ZMod p)` instance), so that `ZMod p` is a `B`-module with central action. For each
`c : ZMod p`, the square-zero extension `B ⊕ ZMod p ε` carries the `δ`-structure

`δ (a, b) = (δ a, (c - ā ^ (p - 1)) * b)`,

where `ā` is the image of `a` under `B →+* ZMod p`. Its Frobenius `(a, b) ↦ (φ a, 0)` does not
depend on `c`, while distinct parameters give distinct `δ`-structures. This explicit family
illustrates the phenomenon noted in Bhatt and Scholze, *Prisms and prismatic cohomology*,
Remark 2.2: on a ring with `p`-torsion the Frobenius lift does not determine the `δ`-structure,
and a ring homomorphism commuting with the Frobenius lifts need not commute with `δ`. For
`B = ℤ` this ring has characteristic zero.

The computation rests on the second coordinate of the addition correction on any commutative
square-zero extension `R ⊕ M`:
`(addCorrection p x y).snd` is
`(a ^ (p - 1) - (a + c) ^ (p - 1)) • b + (c ^ (p - 1) - (a + c) ^ (p - 1)) • d`
for `x = (a, b)` and `y = (c, d)` (`TrivSqZeroExt.snd_addCorrection`).

## Main definitions

* `TauCeti.DeltaRing.trivSqZeroExt`: the `δ`-structure on `TrivSqZeroExt B (ZMod p)` with
  parameter `c : ZMod p`.

## Main results

* `TrivSqZeroExt.snd_addCorrection`: the second coordinate of the addition correction on a
  square-zero extension.
* `TauCeti.DeltaRing.frobenius_trivSqZeroExt`: the Frobenius of `trivSqZeroExt c` is
  `(a, b) ↦ (φ a, 0)`, independently of `c`.
* `TauCeti.DeltaRing.isDeltaMap_inlHom_trivSqZeroExt`, `isDeltaMap_fstHom_trivSqZeroExt`: the
  inclusion of `B` and the projection to `B` are `δ`-maps.
* `TauCeti.DeltaRing.trivSqZeroExt_injective`: distinct parameters give distinct
  `δ`-structures.
* `TauCeti.DeltaRing.not_isDeltaMap_id_trivSqZeroExt`: for distinct parameters, the identity
  ring homomorphism is not a `δ`-map, although it commutes with the Frobenius lifts
  (`frobenius_trivSqZeroExt_eq`).

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  Definition 2.1, Remarks 2.2 and 2.3, Example 2.6.
-/

public section

namespace TrivSqZeroExt

open TauCeti DeltaRing

variable {p : ℕ} {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]

/-- The first coordinate of the addition correction is the addition correction of the first
coordinates. -/
@[simp]
theorem fst_addCorrection (x y : TrivSqZeroExt R M) :
    (addCorrection p x y).fst = addCorrection p x.fst y.fst :=
  map_addCorrection (p := p) (fstHom R R M) x y

/-- On a commutative square-zero extension, the second coordinate of the addition correction of
`x = (a, b)` and `y = (c, d)` is
`(a ^ (p - 1) - (a + c) ^ (p - 1)) • b + (c ^ (p - 1) - (a + c) ^ (p - 1)) • d`
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Definition 2.1). -/
@[simp]
theorem snd_addCorrection [hp : Fact p.Prime] (x y : TrivSqZeroExt R M) :
    (addCorrection p x y).snd =
      (x.fst ^ (p - 1) - (x.fst + y.fst) ^ (p - 1)) • x.snd +
        (y.fst ^ (p - 1) - (x.fst + y.fst) ^ (p - 1)) • y.snd := by
  have h (i : ℕ) : (x ^ i * y ^ (p - i) * ((p.choose i / p : ℕ) : TrivSqZeroExt R M)).snd =
      (((p.choose i / p * i : ℕ) : R) * (x.fst ^ (i - 1) * y.fst ^ (p - i))) • x.snd +
        (((p.choose i / p * (p - i) : ℕ) : R) * (x.fst ^ i * y.fst ^ (p - i - 1))) • y.snd := by
    simp only [snd_mul, snd_natCast, fst_natCast, fst_mul, fst_pow, snd_pow, smul_zero,
      zero_add, op_smul_eq_smul, Nat.pred_eq_sub_one]
    simp only [smul_add, smul_smul, ← Nat.cast_smul_eq_nsmul R, Nat.cast_mul]
    rw [add_comm]
    congr 2 <;> ring
  rw [addCorrection_def, snd_neg, snd_sum, Finset.sum_congr rfl fun i _ => h i,
    Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
    hp.out.sum_choose_div_mul_left, hp.out.sum_choose_div_mul_right]
  module

end TrivSqZeroExt

namespace TauCeti

namespace DeltaRing

open TrivSqZeroExt

variable {p : ℕ}

section SquareZero

variable [hp : Fact p.Prime] {B : Type*} [CommRing B] [DeltaRing p B] [Algebra B (ZMod p)]
  [Module Bᵐᵒᵖ (ZMod p)] [IsCentralScalar B (ZMod p)]

variable (B) in
/-- The `δ`-structure `δ (a, b) = (δ a, (c - ā ^ (p - 1)) * b)` on the square-zero extension
`B ⊕ ZMod p ε`, where `ā` is the image of `a` under `algebraMap B (ZMod p)`. Its Frobenius
`(a, b) ↦ (φ a, 0)` does not depend on `c` (`frobenius_trivSqZeroExt`), but distinct `c` give
distinct structures (`trivSqZeroExt_injective`). This family is an explicit example of the
phenomenon noted in Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.2: with
`p`-torsion, the Frobenius lift does not determine the `δ`-structure. -/
@[instance_reducible]
def trivSqZeroExt (c : ZMod p) : DeltaRing p (TrivSqZeroExt B (ZMod p)) where
  delta x := inl (delta p x.fst) + inr ((c - algebraMap B (ZMod p) x.fst ^ (p - 1)) * x.snd)
  delta_zero := by ext <;> simp
  delta_one := by ext <;> simp
  delta_add x y := by
    ext
    · simp [fst_addCorrection, delta_add]
    · simp only [snd_add, snd_inl, snd_inr, zero_add, fst_add, snd_addCorrection,
        Algebra.smul_def, map_sub, map_pow, map_add]
      ring
  delta_mul x y := by
    ext
    · simp [delta_mul]
    · simp only [snd_add, snd_inl, snd_inr, zero_add, fst_add, fst_mul, snd_mul, snd_pow,
        fst_pow, fst_inl, add_zero, fst_natCast, snd_natCast, op_smul_eq_smul, Algebra.smul_def,
        map_pow, map_mul, map_natCast, eq_natCast, ZMod.natCast_self, zero_mul, smul_zero,
        mul_pow]
      set a := algebraMap B (ZMod p) x.fst
      set b := algebraMap B (ZMod p) y.fst
      have ha := ZMod.pow_card a
      have hb := ZMod.pow_card b
      have ha' : a ^ (p - 1) * a = a := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.Prime.one_le hp.out), ha]
      have hb' : b ^ (p - 1) * b = b := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.Prime.one_le hp.out), hb]
      linear_combination (-(c - b ^ (p - 1)) * y.snd) * ha +
        (-(c - a ^ (p - 1)) * x.snd) * hb + (-(b ^ (p - 1)) * y.snd) * ha' +
        (-(a ^ (p - 1)) * x.snd) * hb'

/-- The `δ`-operation of `trivSqZeroExt B c`. -/
theorem delta_trivSqZeroExt (c : ZMod p) (x : TrivSqZeroExt B (ZMod p)) :
    @delta p _ _ (trivSqZeroExt B c) x =
      inl (delta p x.fst) + inr ((c - algebraMap B (ZMod p) x.fst ^ (p - 1)) * x.snd) :=
  (rfl)

/-- The first coordinate of `δ x` for `trivSqZeroExt B c` is `δ x.fst`. -/
@[simp]
theorem fst_delta_trivSqZeroExt (c : ZMod p) (x : TrivSqZeroExt B (ZMod p)) :
    (@delta p _ _ (trivSqZeroExt B c) x).fst = delta p x.fst := by
  simp [delta_trivSqZeroExt]

/-- The second coordinate of `δ x` for `trivSqZeroExt B c` is `(c - ā ^ (p - 1)) * x.snd`, where
`ā` is the image of `x.fst` in `ZMod p`. -/
@[simp]
theorem snd_delta_trivSqZeroExt (c : ZMod p) (x : TrivSqZeroExt B (ZMod p)) :
    (@delta p _ _ (trivSqZeroExt B c) x).snd =
      (c - algebraMap B (ZMod p) x.fst ^ (p - 1)) * x.snd := by
  simp [delta_trivSqZeroExt]

/-- `δ ε = c ε` for `trivSqZeroExt B c`, where `ε = inr 1`. -/
@[simp]
theorem delta_trivSqZeroExt_inr_one (c : ZMod p) :
    @delta p _ _ (trivSqZeroExt B c) (inr 1) = inr c := by
  ext
  · simp
  · simp [zero_pow (Nat.sub_ne_zero_of_lt (Nat.Prime.one_lt hp.out))]

/-- The Frobenius of `trivSqZeroExt B c` is `(a, b) ↦ (φ a, 0)`, independently of `c`. -/
@[simp]
theorem frobenius_trivSqZeroExt (c : ZMod p) (x : TrivSqZeroExt B (ZMod p)) :
    @frobenius p _ _ _ (trivSqZeroExt B c) x = inl (frobenius p B x.fst) := by
  ext
  · simp [frobenius_apply]
  · simp [frobenius_apply, snd_pow, Algebra.smul_def]

/-- The inclusion `B →+* B ⊕ ZMod p ε` is a `δ`-map for `trivSqZeroExt B c`. -/
theorem isDeltaMap_inlHom_trivSqZeroExt (c : ZMod p) :
    @IsDeltaMap p B _ (TrivSqZeroExt B (ZMod p)) _ _ (trivSqZeroExt B c)
      (inlHom B (ZMod p)) := by
  let := trivSqZeroExt B c
  exact ⟨fun a => by ext <;> simp⟩

/-- The projection `B ⊕ ZMod p ε →+* B` is a `δ`-map for `trivSqZeroExt B c`. -/
theorem isDeltaMap_fstHom_trivSqZeroExt (c : ZMod p) :
    @IsDeltaMap p (TrivSqZeroExt B (ZMod p)) _ B _ (trivSqZeroExt B c) _
      (fstHom B B (ZMod p)).toRingHom := by
  let := trivSqZeroExt B c
  exact ⟨fun x => by simp⟩

variable (B) in
/-- Distinct parameters give distinct `δ`-structures on `B ⊕ ZMod p ε`: they differ on `ε`. -/
theorem trivSqZeroExt_injective : Function.Injective (trivSqZeroExt (p := p) B) := by
  intro c c' h
  have h' := delta_trivSqZeroExt_inr_one (B := B) c
  rw [h, delta_trivSqZeroExt_inr_one] at h'
  exact inr_injective h'.symm

/-- The Frobenius lifts of `trivSqZeroExt B c` and `trivSqZeroExt B c'` agree, so the identity of
`B ⊕ ZMod p ε` intertwines them. -/
theorem frobenius_trivSqZeroExt_eq (c c' : ZMod p) :
    @frobenius p _ _ _ (trivSqZeroExt B c) = @frobenius p _ _ _ (trivSqZeroExt B c') :=
  RingHom.ext fun x => by simp

/-- For distinct parameters `c` and `c'`, the identity of `B ⊕ ZMod p ε` is not a `δ`-map from
`trivSqZeroExt B c` to `trivSqZeroExt B c'`, although it intertwines their Frobenius lifts
(`frobenius_trivSqZeroExt_eq`). This illustrates Bhatt and Scholze, *Prisms and prismatic
cohomology*, Remark 2.2. -/
theorem not_isDeltaMap_id_trivSqZeroExt {c c' : ZMod p} (h : c ≠ c') :
    ¬ @IsDeltaMap p _ _ (TrivSqZeroExt B (ZMod p)) _ (trivSqZeroExt B c) (trivSqZeroExt B c')
      (RingHom.id _) := fun hd => by
  let := trivSqZeroExt B c
  exact h <| trivSqZeroExt_injective B <|
    eq_of_isDeltaMap_of_surjective Function.surjective_id (isDeltaMap_id p _) hd

end SquareZero

end DeltaRing

end TauCeti
