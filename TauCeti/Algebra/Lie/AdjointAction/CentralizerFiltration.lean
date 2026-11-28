/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.Nilpotent
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import TauCeti.Algebra.Lie.Basic

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
* `TauCeti.mem_ker_inf_range_pow_iff`: membership in a step of the filtration does not depend on
  the base ring.
* `TauCeti.lie_mem_ker_inf_range_pow_add`: the filtration is compatible with brackets.
* `LieHom.isNilpotent_apply_lie_of_lie_lie_eq_zero` and
  `LieHom.isNilpotent_apply_of_mem_ker_inf_range`: Jacobson's lemma for finite-dimensional
  representations, showing that `ker (ad e) ⊓ [e, L]` acts nilpotently.
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

/-- Membership in a step of the filtration of the centralizer of `e` does not depend on the base
ring of the Lie algebra: `ad` over `R` and over `S` is the same bracket. -/
theorem mem_ker_inf_range_pow_iff {L : Type*} [LieRing L] (R S : Type*) [CommRing R]
    [CommRing S] [LieAlgebra R L] [LieAlgebra S L] {e x : L} {n : ℕ} :
    x ∈ LinearMap.ker (ad R L e) ⊓ LinearMap.range (ad R L e ^ n) ↔
      x ∈ LinearMap.ker (ad S L e) ⊓ LinearMap.range (ad S L e ^ n) := by
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range, ad_apply,
    ad_pow_apply_eq_ad_pow_apply R S e]

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
      (by simpa only [pow_succ', mul_apply_eq_comp, ad_apply] using hc)
  have hleib : (ad K L e ^ (i + j)) ⁅a, b⁆ =
      ((i + j).choose i : K) • ⁅(ad K L e ^ i) a, (ad K L e ^ j) b⁆ := by
    have hD : ⇑(LieDerivation.ad K L e) = ⇑(ad K L e) := funext fun c => by simp
    have := (LieDerivation.ad K L e).iterate_apply_lie (i + j) a b
    simp only [hD, ← pow_apply_eq_iterate] at this
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

end TauCeti

namespace LieHom

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **Jacobson's lemma** for a finite-dimensional representation. Over a field of characteristic
zero, if `⁅e, ⁅e, a⁆⁆ = 0` then `ρ ⁅e, a⁆` is nilpotent in every finite-dimensional representation
`ρ` of `L`. The Lie algebra `L` itself need not be finite-dimensional. -/
theorem isNilpotent_apply_lie_of_lie_lie_eq_zero (ρ : L →ₗ⁅K⁆ Module.End K M) {e a : L}
    (h : ⁅e, ⁅e, a⁆⁆ = 0) : IsNilpotent (ρ ⁅e, a⁆) := by
  rw [LieHom.map_lie]
  refine LinearMap.isNilpotent_lie_of_lie_lie_eq_zero ?_
  rw [← LieHom.map_lie, ← LieHom.map_lie, h, map_zero]

/-- Every element of `ker (ad e) ⊓ [e, L]` acts nilpotently in every finite-dimensional
representation of `L` over a field of characteristic zero. -/
theorem isNilpotent_apply_of_mem_ker_inf_range (ρ : L →ₗ⁅K⁆ Module.End K M) {e y : L}
    (hy : y ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e)) :
    IsNilpotent (ρ y) := by
  obtain ⟨hye, a, rfl⟩ := Submodule.mem_inf.mp hy
  rw [LinearMap.mem_ker, ad_apply, ad_apply] at hye
  rw [ad_apply]
  exact ρ.isNilpotent_apply_lie_of_lie_lie_eq_zero hye

end LieHom

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

/-- **Jacobson's lemma** for the adjoint representation. In a finite-dimensional Lie algebra over
a field of characteristic zero, if `⁅e, ⁅e, a⁆⁆ = 0` then `ad ⁅e, a⁆` is nilpotent. In particular
every element of `ker (ad e) ⊓ [e, L]` is `ad`-nilpotent. -/
theorem isNilpotent_ad_lie_of_lie_lie_eq_zero {e a : L} (h : ⁅e, ⁅e, a⁆⁆ = 0) :
    IsNilpotent (ad K L ⁅e, a⁆) :=
  (ad K L).isNilpotent_apply_lie_of_lie_lie_eq_zero h

/-- Every element of `ker (ad e) ⊓ [e, L]` is `ad`-nilpotent. -/
theorem isNilpotent_ad_of_mem_ker_inf_range {e y : L}
    (hy : y ∈ LinearMap.ker (ad K L e) ⊓ LinearMap.range (ad K L e)) :
    IsNilpotent (ad K L y) :=
  (ad K L).isNilpotent_apply_of_mem_ker_inf_range hy

end TauCeti
