/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Nonunits and domination for valuation subrings

A valuation subring `A` of a field is determined by its nonunits, and a valuation subring
dominating `A` (containing it, with every nonunit of `A` a nonunit) is `A` itself. Pulling a
valuation subring back along a field homomorphism `f` detects nonunits through `f`, so a
valuation subring dominates its pullback, and conversely a valuation subring pulls back to any
valuation subring that it dominates through `f`. Units of a valuation subring stay units in any
valuation subring whose pullback contains it, and among finitely many elements of the field, not
all zero, one of largest valuation divides all the others in the valuation subring.

When a valuation `w` on a field has archimedean value group, every nonzero prime ideal of
`w.valuationSubring` contains the maximal ideal, so `w.valuationSubring` has Krull dimension at
most one. For any valuation `w` with `Ring.KrullDimLE 1 w.valuationSubring`, a nontrivial valuation
`v` on the same field taking the value `1` whenever `w x = 1` is automatically equivalent to `w`.

## Main results

* `ValuationSubring.mem_nonunits_comap`: nonunits of a pulled-back valuation subring.
* `ValuationSubring.valuation_map_eq_one`: units of `O` map to units of every valuation subring
  whose pullback contains `O`.
* `ValuationSubring.exists_ne_zero_and_div_mem`: among finitely many elements, not all zero, one
  is nonzero and divides all the others in `O`.
* `ValuationSubring.eq_of_le_of_nonunits_le`: a valuation subring equals any valuation subring
  dominating it.
* `ValuationSubring.isLocalHom_restrict`: a valuation subring dominates its pullback.
* `ValuationSubring.comap_eq_of_map_maximalIdeal_le`: a valuation subring `W` of `L` pulls back to
  a valuation subring `V` of `K` when `V` maps through a ring `S` into `W`, with its maximal ideal
  landing in an ideal of `S` that is sent into the nonunits of `W`.
* `Valuation.krullDimLE_one_valuationSubring`: a valuation on a field with archimedean value group
  has valuation subring of Krull dimension at most one.
* `Valuation.isEquiv_of_val_eq_one_imp`: a nontrivial valuation taking the value `1` wherever a
  valuation of Krull dimension at most one takes the value `1` is equivalent to it.

## References

* [Stacks Project, Tag 00IA](https://stacks.math.columbia.edu/tag/00IA) (valuation rings
  dominating a local ring).
-/

public section

open IsLocalRing

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L]

/-- An element lies in the nonunits of a pulled-back valuation subring exactly when its image
lies in the nonunits of the original one. -/
@[simp]
theorem mem_nonunits_comap {A : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  simp [mem_nonunits_iff_or, map_inv₀]

/-- Units of `O` are sent to units of every valuation subring `W` of `L` whose pullback along
`f : K →+* L` contains `O`. -/
theorem valuation_map_eq_one {O : ValuationSubring K} {W : ValuationSubring L} {f : K →+* L}
    (hW : O ≤ W.comap f) {a : K} (ha : O.valuation a = 1) : W.valuation (f a) = 1 := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have h₁ : W.valuation (f a) ≤ 1 :=
    (W.valuation_le_one_iff _).mpr (hW ((O.valuation_le_one_iff a).mp ha.le))
  have h₂ : W.valuation (f a⁻¹) ≤ 1 :=
    (W.valuation_le_one_iff _).mpr
      (hW ((O.valuation_le_one_iff _).mp (by rw [map_inv₀, ha, inv_one])))
  have hmul : W.valuation (f a) * W.valuation (f a⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
  by_contra hne
  exact (mul_lt_one_of_lt_of_le (lt_of_le_of_ne h₁ hne) h₂).ne hmul

/-- **Clearing denominators in a valuation subring.** Among finitely many elements `g i` of `K`,
`i ∈ s`, not all zero, there is a nonzero `g k` dividing all the others in `O`, namely one of
largest valuation. -/
theorem exists_ne_zero_and_div_mem (O : ValuationSubring K) {ι : Type*} {s : Finset ι}
    {g : ι → K} (h : ∃ i ∈ s, g i ≠ 0) : ∃ k ∈ s, g k ≠ 0 ∧ ∀ i ∈ s, g i / g k ∈ O := by
  obtain ⟨i₀, hi₀s, hi₀⟩ := h
  obtain ⟨k, hks, hkmax⟩ := s.exists_max_image (fun i ↦ O.valuation (g i)) ⟨i₀, hi₀s⟩
  have hgk : g k ≠ 0 := by
    intro hk
    have := hkmax i₀ hi₀s
    rw [hk, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₀ this
  refine ⟨k, hks, hgk, fun i hi ↦ ?_⟩
  rw [← O.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hkmax i hi) zero_le

/-- A valuation subring is determined by any valuation subring dominating it: if `A ≤ B` and
every nonunit of `A` is a nonunit of `B`, then `A = B`. -/
theorem eq_of_le_of_nonunits_le {A B : ValuationSubring K} (h : A ≤ B)
    (h' : A.nonunits ≤ B.nonunits) : A = B :=
  nonunits_injective (le_antisymm h' (nonunits_le_nonunits.mpr h))

/-- The inclusion of a pulled-back valuation subring `A.comap f` into `A` is a local
homomorphism: a valuation subring dominates its pullback. -/
theorem isLocalHom_restrict (A : ValuationSubring L) (f : K →+* L) {B : ValuationSubring K}
    (hB : B = A.comap f) : IsLocalHom (f.restrict B A fun _ hx ↦ mem_comap.mp (hB ▸ hx)) := by
  refine ⟨fun ⟨x, hx⟩ ha ↦ ?_⟩
  subst hB
  rw [← notMem_maximalIdeal, ← coe_mem_nonunits_iff] at ha ⊢
  exact mem_nonunits_comap.not.mpr ha

/-- Let `ψ : S →+* L` map into a valuation subring `W` of the field `L`, sending an ideal `Q` into
the nonunits of `W`. If a valuation subring `V` of `K` maps to `S` with its maximal ideal in `Q`,
compatibly with `g : K →+* L`, then `W` dominates the image of `V`, so `W` pulls back to `V`. -/
theorem comap_eq_of_map_maximalIdeal_le {S : Type*} [CommRing S]
    {V : ValuationSubring K} {W : ValuationSubring L} (ι : V →+* S) (ψ : S →+* L) {Q : Ideal S}
    (hQ : (maximalIdeal V).map ι ≤ Q) (hmem : ∀ s, ψ s ∈ W) (hnon : ∀ s ∈ Q, ψ s ∈ W.nonunits)
    (g : K →+* L) (hg : ∀ v : V, g v = ψ (ι v)) : W.comap g = V := by
  refine (eq_of_le_of_nonunits_le (fun x hx ↦ ?_) fun x hx ↦ ?_).symm
  · simpa only [mem_comap, hg ⟨x, hx⟩] using hmem (ι ⟨x, hx⟩)
  · simpa only [mem_nonunits_comap, hg ⟨x, nonunits_subset hx⟩] using
      hnon _ (hQ (Ideal.mem_map_of_mem _ (coe_mem_nonunits_iff.mp hx)))

end ValuationSubring

namespace RingHom

/-- If `ψ : R →+* L` is a ring map to a field whose kernel lies in a proper ideal `Q`, then some
valuation subring of `L` contains the range of `ψ` and has the image of `Q` among its nonunits. -/
theorem exists_valuationSubring_mem_and_image_subset_nonunits {R L : Type*} [CommRing R]
    [Field L] (ψ : R →+* L) {Q : Ideal R} (hQ : Q ≠ ⊤) (hker : RingHom.ker ψ ≤ Q) :
    ∃ W : ValuationSubring L, (∀ x, ψ x ∈ W) ∧ ∀ x ∈ Q, ψ x ∈ W.nonunits := by
  have hQ' : Q.map ψ.rangeRestrict ≠ ⊤ := fun htop ↦ hQ <| by
    have := Ideal.comap_map_of_surjective _ ψ.rangeRestrict_surjective Q
    rw [htop, Ideal.comap_top, sup_eq_left.mpr] at this
    · exact this.symm
    · intro x hx
      exact hker (congrArg Subtype.val (Ideal.mem_bot.mp hx))
  obtain ⟨W, hrange, hnon⟩ := Ideal.image_subset_nonunits_valuationSubring _ hQ'
  exact ⟨W, fun x ↦ hrange ⟨x, rfl⟩, fun x hx ↦
    hnon ⟨ψ.rangeRestrict x, Ideal.mem_map_of_mem _ hx, rfl⟩⟩

end RingHom

namespace Valuation

variable {K Γ₀ Γ₁ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₁]

/-- A valuation on a field whose value group is archimedean has valuation subring of Krull
dimension at most one: every nonzero prime ideal contains the maximal ideal, since archimedeanity
forces a power of any maximal-ideal element to divide any nonzero element of the prime ideal. -/
theorem krullDimLE_one_valuationSubring (v : Valuation K Γ₀) [MulArchimedean v.valueGroup] :
    Ring.KrullDimLE 1 v.valuationSubring := by
  refine Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr fun P hP0 hP ↦ ?_
  suffices h : P = maximalIdeal v.valuationSubring from h ▸ maximalIdeal.isMaximal _
  refine le_antisymm (le_maximalIdeal hP.ne_top) fun b hb ↦ ?_
  rcases eq_or_ne b 0 with rfl | hb0
  · exact P.zero_mem
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have haK : (a : K) ≠ 0 := ZeroMemClass.coe_eq_zero.not.mpr ha0
  have hbK : (b : K) ≠ 0 := ZeroMemClass.coe_eq_zero.not.mpr hb0
  have hva : v (a : K) ≠ 0 := v.ne_zero_iff.mpr haK
  have hvb : v (b : K) ≠ 0 := v.ne_zero_iff.mpr hbK
  let γa : v.valueGroup := ⟨Units.mk0 (v (a : K)) hva, v.mem_valueGroup ⟨a, rfl⟩⟩
  let γb : v.valueGroup := ⟨Units.mk0 (v (b : K)) hvb, v.mem_valueGroup ⟨b, rfl⟩⟩
  have hγb : 1 < γb⁻¹ := by
    rw [one_lt_inv', ← Subtype.coe_lt_coe, ← Units.val_lt_val]
    simpa [γb] using v.mem_maximalIdeal_iff.mp hb
  obtain ⟨n, hn⟩ := MulArchimedean.arch γa⁻¹ hγb
  have hpow : v ((b : K) ^ n) ≤ v (a : K) := by
    rw [inv_pow, inv_le_inv_iff] at hn
    rw [map_pow]
    simpa [γa, γb] using Units.val_le_val.mpr (Subtype.coe_le_coe.mpr hn)
  let q : v.valuationSubring := ⟨(b : K) ^ n / (a : K),
    (v.mem_valuationSubring_iff _).mpr (by rw [map_div₀]; exact div_le_one_of_le₀ hpow zero_le)⟩
  have hbn : b ^ n = a * q := Subtype.ext (by simp [q, mul_div_cancel₀ _ haK])
  exact hP.mem_of_pow_mem n (hbn ▸ P.mul_mem_right q haP)

/-- **Unit-triviality criterion for equivalence with a rank-at-most-one valuation.** Let `v` and
`w` be valuations on a field `K` such that `v` is nontrivial and `w.valuationSubring` has Krull
dimension at most one (in particular, whenever `w.valuationSubring` is a discrete valuation ring
or `w.valueGroup` is archimedean). If `v` takes the value `1` on every element of `K` with
`w x = 1`, then `v` is equivalent to `w`. -/
theorem isEquiv_of_val_eq_one_imp (v : Valuation K Γ₀) [v.IsNontrivial]
    (w : Valuation K Γ₁) [Ring.KrullDimLE 1 w.valuationSubring]
    (hu : ∀ x : K, w x = 1 → v x = 1) :
    v.IsEquiv w := by
  have hle : w.valuationSubring ≤ v.valuationSubring :=
    ValuationSubring.unitGroup_le_unitGroup.mp fun x hx ↦ by
      rw [ValuationSubring.mem_unitGroup_iff] at hx ⊢
      exact v.isEquiv_valuation_valuationSubring.eq_one_iff_eq_one.mp
        (hu x (w.isEquiv_valuation_valuationSubring.eq_one_iff_eq_one.mpr hx))
  exact (Valuation.isEquiv_iff_valuationSubring v w).mpr
    (w.valuationSubring.eq_of_le_of_ne_top hle (by simpa using ‹v.IsNontrivial›)).symm

end Valuation

