/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.RingTheory.Valuation.Pair
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Idempotent
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Hermite form of one column over a valuation pair

Let `R ⊆ A` be a valuation pair (`Subring.IsValuationPair R`), for instance a valuation subring of
a field, or a product `∏ w, O w ⊆ ∏ w, F w` of valuation pairs (`Subring.IsValuationPair.pi`).
For every vector `p : ι → A` over a finite index type and every index `i`, some `W : GL ι R`
(acting on `A^ι` through `GeneralLinearGroup.map R.subtype`) clears every entry of `p` except the
`i`-th one. Equivalently, `p = (V⁻¹ p)_i • V e_i` for some `V : GL ι R`, where `V e_i` is the
`i`-th column of `V`.

Since `W` and `W⁻¹` have entries in `R`, the surviving entry `(W p)_i` generates the same
`R`-submodule of `A` as the entries of `p` together: a vector over a valuation pair reduces to a
single generator times a column of an invertible matrix over `R`.

Each clearing step uses the valuation-pair condition for two entries `p i` and `p j`. It gives an
idempotent `e : R`, and the step patches two row operations over `R` along `e`
(`IsIdempotentElem.cutGL`, `IsIdempotentElem.val_map_mul_cutGL_inv_mul`): one that works where
`p i` divides `p j`, and one that works where `p j` divides `p i`.

## Main results

* `Subring.IsValuationPair.exists_mulVec_eq_single`: some `W : GL ι R` maps `p` to a multiple of
  the `i`-th basis vector.
* `Subring.IsValuationPair.exists_eq_smul_col`: some `V : GL ι R` satisfies
  `p = (V⁻¹ p)_i • V e_i`.

## References

* The folder `grh` of <https://github.com/lsernau/grh-lean> at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, `Lib/General/LinearAlgebra/HermiteForm.lean`
  (`New.IsValuationPair.hermite`).
* N. Bourbaki, *Commutative Algebra*, Chapter VI (valuation rings and finitely generated ideals).
-/

public section

open Matrix Submodule

namespace Subring

variable {A : Type*} [CommRing A] {R : Subring A} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The clearing step: for a pivot `i ≠ j`, some `W : GL ι R` sends the `j`-th entry of `q` to
zero and leaves every entry other than the `i`-th and `j`-th unchanged. -/
private lemma IsValuationPair.exists_mulVec_apply_eq_zero (hR : R.IsValuationPair)
    {i j : ι} (hij : i ≠ j) (q : ι → A) :
    ∃ W : GL ι R, (GeneralLinearGroup.map R.subtype W *ᵥ q) j = 0 ∧
      ∀ k, k ≠ i → k ≠ j → (GeneralLinearGroup.map R.subtype W *ᵥ q) k = q k := by
  obtain ⟨e, he, hle⟩ := isValuationPair_iff.1 hR (q i) (q j)
  obtain ⟨r, hr⟩ := mem_span_singleton.1 (le_sup_left.trans hle (mem_span_singleton_self _))
  obtain ⟨s, hs⟩ := mem_span_singleton.1 (le_sup_right.trans hle (mem_span_singleton_self _))
  rw [Subring.smul_def, smul_eq_mul] at hr hs
  have he' : (e : A) * e = e := congrArg Subtype.val he.eq
  -- `c` subtracts `s` times row `i` from row `j`; `d` swaps rows `i, j`, then subtracts `r` times
  -- row `i` from row `j`.
  let c : GL ι R := TauCeti.transvectionUnit hij.symm (-s)
  let d : GL ι R := TauCeti.transvectionUnit hij.symm (-r) * GeneralLinearGroup.swap R i j
  have hd : (GeneralLinearGroup.map R.subtype d).val *ᵥ q =
      Function.update (q ∘ Equiv.swap i j) j (q i - r * q j) := by
    simp only [d, map_mul, Units.val_mul, ← mulVec_mulVec, GeneralLinearGroup.map_swap,
      GeneralLinearGroup.val_swap, swap_mulVec, TauCeti.map_transvectionUnit,
      TauCeti.transvectionUnit_mulVec]
    simp [sub_eq_add_neg]
  have hc : (GeneralLinearGroup.map R.subtype c).val *ᵥ q =
      Function.update q j (q j - s * q i) := by
    simp only [c, TauCeti.map_transvectionUnit, TauCeti.transvectionUnit_mulVec]
    simp [sub_eq_add_neg]
  refine ⟨c * he.cutGL (c⁻¹ * d), ?_, fun k hki hkj ↦ ?_⟩ <;>
    simp only [he.val_map_mul_cutGL_inv_mul, add_mulVec, smul_mulVec, hd, hc]
  · simp only [Pi.add_apply, Pi.smul_apply, Function.update_self, smul_eq_mul,
      Subring.coe_subtype]
    linear_combination (-(e : A)) * hr + (r : A) * (q j - q i) * he' -
      (1 - (e : A)) * hs + (s : A) * (q i - q j) * he'
  · simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      Function.update_of_ne hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    ring

/-- For a finite set `t` of indices avoiding the pivot `i`, a single `W : GL ι R` sends `p` to a
vector vanishing at every index of `t`. The induction on `t` is the one of
`Matrix.exists_gl_mul_eq_zero_on_of_preValuationRing`, with the valuation-pair clearing step. -/
private lemma IsValuationPair.exists_mulVec_eq_zero_on (hR : R.IsValuationPair) (p : ι → A)
    {i : ι} {t : Finset ι} (hi : i ∉ t) :
    ∃ W : GL ι R, ∀ j ∈ t, (GeneralLinearGroup.map R.subtype W *ᵥ p) j = 0 := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert j t hj ih =>
    obtain ⟨hij, hi⟩ : i ≠ j ∧ i ∉ t := by simpa [eq_comm] using hi
    obtain ⟨W, hW⟩ := ih hi
    obtain ⟨V, hVj, hV⟩ :=
      hR.exists_mulVec_apply_eq_zero hij (GeneralLinearGroup.map R.subtype W *ᵥ p)
    refine ⟨V * W, fun k hk ↦ ?_⟩
    obtain rfl | hk := Finset.mem_insert.1 hk
    · simpa using hVj
    · simpa using (hV k (fun h ↦ hi (h ▸ hk)) (fun h ↦ hj (h ▸ hk))).trans (hW k hk)

/-- **Hermite form of one column over a valuation pair.** For a valuation pair `R ⊆ A`, every
vector `p : ι → A` and every index `i`, some `W : GL ι R` sends `p` to a multiple of the `i`-th
basis vector: `W p = (W p)_i • e_i`. -/
theorem IsValuationPair.exists_mulVec_eq_single (hR : R.IsValuationPair) (p : ι → A) (i : ι) :
    ∃ W : GL ι R, GeneralLinearGroup.map R.subtype W *ᵥ p =
      Pi.single i ((GeneralLinearGroup.map R.subtype W *ᵥ p) i) := by
  obtain ⟨W, hW⟩ := hR.exists_mulVec_eq_zero_on p (i := i) (t := Finset.univ.erase i) (by simp)
  refine ⟨W, funext fun k ↦ ?_⟩
  rcases eq_or_ne k i with rfl | hk
  · simp
  · rw [Pi.single_eq_of_ne hk, hW k (by simp [hk])]

/-- **Hermite form of one column over a valuation pair**, in the form `p = (V⁻¹ p)_i • V e_i`:
for a valuation pair `R ⊆ A`, every `p : ι → A` and every `i`, some `V : GL ι R` has
`p = (V⁻¹ p)_i • V.col i`, where `V.col i = V e_i` is the `i`-th column of `V` read in `A`. -/
theorem IsValuationPair.exists_eq_smul_col (hR : R.IsValuationPair) (p : ι → A) (i : ι) :
    ∃ V : GL ι R, p = ((GeneralLinearGroup.map R.subtype V⁻¹).val *ᵥ p) i •
      (GeneralLinearGroup.map R.subtype V).val.col i := by
  obtain ⟨W, hW⟩ := hR.exists_mulVec_eq_single p i
  refine ⟨W⁻¹, ?_⟩
  rw [inv_inv, map_inv]
  calc p = (GeneralLinearGroup.map R.subtype W)⁻¹.val *ᵥ
        (GeneralLinearGroup.map R.subtype W *ᵥ p) := by
        simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    _ = _ := by
        rw [hW, mulVec_single]
        ext k
        simp [mul_comm]

end Subring
