/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.RingTheory.Extension.SquareZero.BaerSum

/-!
# A nonsplit square-zero extension

The extension `ℤ/4 → ℤ/2` of `ℤ/2` by `ℤ/2` over `ℤ`, with kernel `2ℤ/4ℤ`, does not split, since
there is no ring map `ℤ/2 → ℤ/4`. Its class in `Exal_ℤ(ℤ/2, ℤ/2)` is therefore nonzero. Its Baer
sum with itself does split: in the quotient of the fibre product by the antidiagonal, `2` is the
class of `(ι 1, ι 1)`, which is the kernel element `1 + 1 = 0`. So the class has order two in the
group `Exal_ℤ(ℤ/2, ℤ/2)`, and the Baer sum of two nonsplit extensions can split.

## Main results

* `TauCeti.SquareZeroExtension.zmodFour_extensionClass_ne_zero`: the extension `ℤ/4 → ℤ/2` has
  a nonzero class.
* `TauCeti.SquareZeroExtension.zmodFour_extensionClass_add_self`: twice its class is zero.
-/

public section

namespace TauCeti

namespace SquareZeroExtension

/-- The square-zero extension `ℤ/4 → ℤ/2` of `ℤ/2` by `ℤ/2` over `ℤ`, whose kernel `2ℤ/4ℤ` is
identified with `ℤ/2` by `m ↦ 2m`. -/
@[expose] def zmodFour : SquareZeroExtension.{0} ℤ (ZMod 2) (ZMod 2) where
  Ring := ZMod 4
  π := (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toIntAlgHom
  π_surjective := by decide
  ι := AddMonoidHom.mk' (fun m ↦ 2 * (m.val : ZMod 4)) (by decide)
  ι_injective := by decide
  exact y := by
    rw [Set.mem_range]
    revert y
    decide
  mul_ι := by decide

/-- The extension `ℤ/4 → ℤ/2` does not split: there is no ring map `ℤ/2 → ℤ/4`. -/
theorem isEmpty_splitting_zmodFour : IsEmpty zmodFour.Splitting := by
  refine ⟨fun s ↦ ?_⟩
  have h := map_add s.toAlgHom 1 1
  rw [(by decide : (1 + 1 : ZMod 2) = 0), map_zero, map_one] at h
  exact absurd h (by decide : (0 : ZMod 4) ≠ 1 + 1)

/-- The extension `ℤ/4 → ℤ/2` has a nonzero class in `Exal_ℤ(ℤ/2, ℤ/2)`. -/
theorem zmodFour_extensionClass_ne_zero : zmodFour.extensionClass ≠ 0 := by
  rw [Ne, extensionClass_eq_zero_iff, not_nonempty_iff]
  exact isEmpty_splitting_zmodFour

/-- The ring of the Baer sum of `ℤ/4 → ℤ/2` with itself has characteristic `2`: `2` is the class
of `(ι 1, ι 1)`, which is the kernel element `1 + 1 = 0`. -/
theorem two_eq_zero_baerSum_zmodFour : (2 : (zmodFour.baerSum zmodFour).Ring) = 0 := by
  -- The ring of `zmodFour` is `ZMod 4` by its exposed definition, where `ι 1 = 2`.
  have hι : (2 : zmodFour.Ring) = zmodFour.ι 1 :=
    (by decide : (2 : ZMod 4) = 2 * ((1 : ZMod 2).val : ZMod 4))
  have h : (2 : zmodFour.fiberProduct zmodFour) = ⟨(zmodFour.ι 1, zmodFour.ι 1), by simp⟩ :=
    Subtype.ext (Prod.ext hι hι)
  rw [← map_ofNat (zmodFour.toBaerSum zmodFour) 2, h, toBaerSum_ι_ι,
    (by decide : (1 + 1 : ZMod 2) = 0), map_zero]

/-- The Baer sum of `ℤ/4 → ℤ/2` with itself splits, by the unique ring map from `ℤ/2`. -/
noncomputable def baerSumZModFourSplitting : (zmodFour.baerSum zmodFour).Splitting where
  toAlgHom := (Algebra.ofId ℤ (ZMod 2)).liftOfSurjective ZMod.intCast_surjective
    (Algebra.ofId ℤ _) fun n hn ↦ by
      obtain ⟨k, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).1 (RingHom.mem_ker.1 hn)
      exact RingHom.mem_ker.2 (by simp [two_eq_zero_baerSum_zmodFour])
  π_toAlgHom b := congr($(Subsingleton.elim
    ((zmodFour.baerSum zmodFour).π.toRingHom.comp _ : ZMod 2 →+* ZMod 2) (RingHom.id _)) b)

/-- Twice the class of `ℤ/4 → ℤ/2` vanishes in `Exal_ℤ(ℤ/2, ℤ/2)`, although the class itself is
nonzero (`TauCeti.SquareZeroExtension.zmodFour_extensionClass_ne_zero`). -/
theorem zmodFour_extensionClass_add_self :
    zmodFour.extensionClass + zmodFour.extensionClass = 0 := by
  rw [← extensionClass_baerSum, extensionClass_eq_zero_iff]
  exact ⟨baerSumZModFourSplitting⟩

end SquareZeroExtension

end TauCeti
