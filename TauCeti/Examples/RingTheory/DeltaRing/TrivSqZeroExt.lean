/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TrivSqZeroExt.SymmetricBimodule
public import TauCeti.RingTheory.DeltaRing.TrivSqZeroExt

/-!
# Checks for the `δ`-structures on `ℤ ⊕ ZMod 2 ε`

These examples exercise the `2`-`δ`-structures `δ_c (a, b) = ((a - a ^ 2) / 2, (c - ā) b)` on
the square-zero extension `ℤ ⊕ ZMod 2 ε`, a ring of characteristic zero with `2`-torsion, for
`c : ZMod 2`. The opposite action of `ℤ` on `ZMod 2` is the integer action.

* `δ_c ε = c ε`, and `δ_c (1 + ε) = (c - 1) ε`, which differs from `δ_c 1 + δ_c ε = c ε`: the
  addition correction `-(1 * ε) = -ε` is needed.
* The inclusion of `ℤ` is a `δ`-map, and so is the projection to `ℤ`; for the projection this
  follows from its compatibility with the Frobenius lifts since `2` is a nonzerodivisor on `ℤ`,
  although the source has `2`-torsion.
* The parameters `0` and `1` give `δ₀ ε = 0` and `δ₁ ε = ε ≠ 0`, but both Frobenius lifts are
  `(a, b) ↦ (a, 0)`. So the identity intertwines the Frobenius lifts without being a `δ`-map,
  and for `δ₁` the element `ε` has `φ ε = ε ^ 2 = 0` but `δ₁ ε ≠ 0`.
-/

public section

namespace TauCeti.Examples

open DeltaRing _root_.TrivSqZeroExt
open scoped TauCeti.TrivSqZeroExt

-- On `ℤ ⊕ ZMod 2 ε`, `δ_c (a, b) = ((a - a ^ 2) / 2, (c - ā) b)`.
example (c : ZMod 2) (a : ℤ) (b : ZMod 2) :
    @delta 2 _ _ (trivSqZeroExt ℤ c) (inl a + inr b) =
      inl ((a - a ^ 2) / 2) + inr ((c - a) * b) := by
  ext <;> simp [delta_int]

-- `δ_c ε = c ε`.
example (c : ZMod 2) : @delta 2 _ _ (trivSqZeroExt ℤ c) (inr 1) = inr c :=
  delta_trivSqZeroExt_inr_one c

-- `δ_c (1 + ε) = (c - 1) ε`, which is not `δ_c 1 + δ_c ε`.
example (c : ZMod 2) :
    @delta 2 _ _ (trivSqZeroExt ℤ c) (1 + inr 1) = inr (c - 1) := by
  ext <;> simp

example (c : ZMod 2) :
    @delta 2 _ _ (trivSqZeroExt ℤ c) (1 + inr 1) ≠
      @delta 2 _ _ (trivSqZeroExt ℤ c) 1 + @delta 2 _ _ (trivSqZeroExt ℤ c) (inr 1) := by
  intro h
  have h' := congrArg snd h
  simp at h'

-- The inclusion of `ℤ` is a `δ`-map: restricting `δ_c` along it gives the `δ`-structure on `ℤ`.
example (c : ZMod 2) :
    @IsDeltaMap 2 ℤ _ _ _ _ (trivSqZeroExt ℤ c) (inlHom ℤ (ZMod 2)) :=
  isDeltaMap_inlHom_trivSqZeroExt c

-- The projection to `ℤ` is a `δ`-map, by compatibility with the Frobenius lifts: `2` is a
-- nonzerodivisor on the target `ℤ`, though not on the source.
example (c : ZMod 2) :
    @IsDeltaMap 2 _ _ ℤ _ (trivSqZeroExt ℤ c) _ (fstHom ℤ ℤ (ZMod 2)).toRingHom := by
  let := trivSqZeroExt ℤ c
  refine (isDeltaMap_iff_comp_frobenius
    (isRegular_iff_ne_zero.mpr (by norm_num)) _).mpr (RingHom.ext fun x => ?_)
  simp [frobenius_trivSqZeroExt]

-- The source has `2`-torsion: `2 ε = 0` with `ε ≠ 0`.
example : ((2 : ℕ) : TrivSqZeroExt ℤ (ZMod 2)) * inr 1 = 0 := by
  ext
  · simp
  · simp only [snd_mul, fst_natCast, snd_natCast, snd_inr, fst_inr, smul_zero, add_zero,
      Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, snd_zero]

-- The parameters `0` and `1` give `δ₀ ε = 0` and `δ₁ ε = ε ≠ 0`.
example : @delta 2 _ _ (trivSqZeroExt ℤ 0) (inr 1) = 0 := by
  rw [delta_trivSqZeroExt_inr_one, inr_zero]

example : @delta 2 _ _ (trivSqZeroExt ℤ 1) (inr 1) = inr 1 :=
  delta_trivSqZeroExt_inr_one 1

example : (inr 1 : TrivSqZeroExt ℤ (ZMod 2)) ≠ 0 :=
  fun h => one_ne_zero (by simpa using congrArg snd h : (1 : ZMod 2) = 0)

example : trivSqZeroExt (p := 2) ℤ 0 ≠ trivSqZeroExt ℤ 1 :=
  (trivSqZeroExt_injective ℤ).ne (by decide)

-- Both Frobenius lifts send `(a, b)` to `(a, 0)`.
example (c : ZMod 2) (x : TrivSqZeroExt ℤ (ZMod 2)) :
    @frobenius 2 _ _ _ (trivSqZeroExt ℤ c) x = inl x.fst := by
  rw [frobenius_trivSqZeroExt, frobenius_int, RingHom.id_apply]

-- The identity intertwines the Frobenius lifts of `δ₀` and `δ₁` but is not a `δ`-map.
example :
    (RingHom.id _).comp (@frobenius 2 _ _ _ (trivSqZeroExt ℤ 0)) =
        (@frobenius 2 _ _ _ (trivSqZeroExt ℤ 1)).comp (RingHom.id _) ∧
      ¬ @IsDeltaMap 2 _ _ (TrivSqZeroExt ℤ (ZMod 2)) _ (trivSqZeroExt ℤ 0) (trivSqZeroExt ℤ 1)
        (RingHom.id _) :=
  ⟨by rw [RingHom.id_comp, RingHom.comp_id, frobenius_trivSqZeroExt_eq],
    not_isDeltaMap_id_trivSqZeroExt (by decide)⟩

-- For `δ₁`, `φ ε = ε ^ 2 = 0` although `δ₁ ε ≠ 0`.
example : @frobenius 2 _ _ _ (trivSqZeroExt ℤ 1) (inr 1) = 0 ∧
    (inr 1 : TrivSqZeroExt ℤ (ZMod 2)) ^ 2 = 0 := by
  constructor
  · rw [frobenius_trivSqZeroExt, fst_inr, map_zero, inl_zero]
  · rw [sq, inr_mul_inr]

end TauCeti.Examples
