/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.Nilpotent
import Mathlib.Algebra.Lie.AdjointAction.Derivation

/-!
# The filtration of a centralizer by powers of `ad e`

Let `L` be a Lie algebra and `e ∈ L`. The centralizer `ker (ad e)` of `e` carries the decreasing
filtration `𝔲ₖ = ker (ad e) ⊓ range ((ad e) ^ k)`. Over a field of characteristic zero it is
compatible with brackets, `⁅𝔲ᵢ, 𝔲ⱼ⁆ ⊆ 𝔲ᵢ₊ⱼ`, by the Leibniz rule for powers of the derivation
`ad e`: in the expansion of `(ad e) ^ (i + j) ⁅a, b⁆` only the term
`⁅(ad e) ^ i a, (ad e) ^ j b⁆` survives when `(ad e) ^ (i + 1)` kills `a` and `(ad e) ^ (j + 1)`
kills `b`.

The first step `𝔲₁ = ker (ad e) ⊓ [e, L]` consists of `ad`-nilpotent elements in finite dimension:
this is Jacobson's lemma `LinearMap.isNilpotent_lie_of_lie_lie_eq_zero` for the adjoint
representation.

## Main results

* `TauCeti.antitone_ker_inf_range_pow`: the filtration is decreasing.
* `TauCeti.lie_mem_ker_inf_range_pow_add`: the filtration is compatible with brackets.
* `TauCeti.isNilpotent_ad_lie_of_lie_lie_eq_zero`: Jacobson's lemma for the adjoint
  representation.
* `TauCeti.isNilpotent_ad_of_mem_ker_inf_range`: every element of `ker (ad e) ⊓ [e, L]` is
  `ad`-nilpotent.

## References

* N. Jacobson, *Lie Algebras*, Interscience, 1962, Chapter III, §11.
-/

public section

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- The filtration `ker (ad e) ⊓ range ((ad e) ^ k)` of the centralizer of `e` is decreasing. -/
theorem antitone_ker_inf_range_pow {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (e : L) : Antitone fun k : ℕ => LinearMap.ker (ad R L e) ⊓ LinearMap.range (ad R L e ^ k) :=
  fun _ _ hkl => inf_le_inf_left _ ((ad R L e).iterateRange.monotone hkl)

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- The filtration `ker (ad e) ⊓ range ((ad e) ^ k)` of the centralizer of `e` is compatible with
brackets: a bracket of an element of the `i`-th step with an element of the `j`-th step lies in the
`(i + j)`-th step. -/
theorem lie_mem_ker_inf_range_pow_add {e x y : L} {i j : ℕ}
    (hx : x ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e ^ i))
    (hy : y ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e ^ j)) :
    ⁅x, y⁆ ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e ^ (i + j)) := by
  obtain ⟨hxe, a, rfl⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hye, b, rfl⟩ := Submodule.mem_inf.mp hy
  rw [LinearMap.mem_ker, ad_apply] at hxe hye
  refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, ((i + j).choose i : K)⁻¹ • ⁅a, b⁆, ?_⟩
  · rw [ad_apply, leibniz_lie, hxe, hye, zero_lie, lie_zero, add_zero]
  -- By the Leibniz rule, `(ad e) ^ (i + j)` sends `⁅a, b⁆` to a sum of brackets in which only
  -- `⁅(ad e) ^ i a, (ad e) ^ j b⁆` survives, since `(ad e) ^ (i + 1)` kills `a` and
  -- `(ad e) ^ (j + 1)` kills `b`.
  have hpow {c : L} {n : ℕ} (hc : ⁅e, (ad K L e ^ n) c⁆ = 0) {m : ℕ} (hm : n < m) :
      (ad K L e ^ m) c = 0 :=
    Module.End.pow_map_zero_of_le (Nat.succ_le_of_lt hm)
      (by simpa only [pow_succ', Module.End.mul_apply, ad_apply] using hc)
  have hleib : (ad K L e ^ (i + j)) ⁅a, b⁆ =
      ((i + j).choose i : K) • ⁅(ad K L e ^ i) a, (ad K L e ^ j) b⁆ := by
    have hD : ⇑(LieDerivation.ad K L e) = ⇑(ad K L e) := funext fun c => by simp
    have := (LieDerivation.ad K L e).iterate_apply_lie (i + j) a b
    simp only [hD, ← Module.End.pow_apply] at this
    rw [this, Finset.sum_eq_single_of_mem (i, j) (Finset.mem_antidiagonal.2 rfl),
      Nat.cast_smul_eq_nsmul]
    rintro ⟨p, q⟩ hpq hne
    rw [Finset.mem_antidiagonal] at hpq
    rcases lt_or_ge i p with hip | hpi
    · rw [hpow hxe hip, zero_lie, smul_zero]
    · have hjq : j < q := by
        by_contra! hqj
        exact hne (Prod.ext (by omega) (by omega))
      rw [hpow hye hjq, lie_zero, smul_zero]
  rw [map_smul, hleib, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (Nat.choose_pos
    (Nat.le_add_right i j)).ne'), one_smul]

variable [FiniteDimensional K L]

/-- **Jacobson's lemma** for the adjoint representation. In a finite-dimensional Lie algebra over
a field of characteristic zero, if `⁅e, ⁅e, a⁆⁆ = 0` then `ad ⁅e, a⁆` is nilpotent. In particular
every element of `ker (ad e) ⊓ [e, L]` is `ad`-nilpotent. -/
theorem isNilpotent_ad_lie_of_lie_lie_eq_zero {e a : L} (h : ⁅e, ⁅e, a⁆⁆ = 0) :
    IsNilpotent (ad K L ⁅e, a⁆) := by
  rw [LieHom.map_lie]
  refine LinearMap.isNilpotent_lie_of_lie_lie_eq_zero ?_
  rw [← LieHom.map_lie, ← LieHom.map_lie, h, map_zero]

/-- Every element of `ker (ad e) ⊓ [e, L]` is `ad`-nilpotent. -/
theorem isNilpotent_ad_of_mem_ker_inf_range {e y : L}
    (hy : y ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e)) :
    IsNilpotent (ad K L y) := by
  obtain ⟨hye, a, rfl⟩ := Submodule.mem_inf.mp hy
  rw [LinearMap.mem_ker, ad_apply, ad_apply] at hye
  rw [ad_apply]
  exact isNilpotent_ad_lie_of_lie_lie_eq_zero hye

end TauCeti
