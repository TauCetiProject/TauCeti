/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.RingTheory.Valuation.Pair
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Idempotent
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Row reduction over a valuation pair

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
`p i` divides `p j`, and one that works where `p j` divides `p i`. The resulting matrix acts only
through the two entries involved: it leaves every other entry of every vector unchanged and fixes
every vector vanishing at both. This lets the clearing of one column leave the columns already
reduced untouched, so iterating it over the columns in order of a weight `b : ι → α` makes every
square matrix `M` over `A` block triangular for `b` after multiplication on the left by some
`W : GL ι R`. Transposing, `M * k` is block triangular for some `k : GL ι R`: this is the Iwasawa
decomposition of `GL_ι(A)` into block triangular matrices times `GL_ι(R)`.

## Main results

* `Subring.IsValuationPair.exists_mulVec_apply_eq_zero`,
  `Subring.IsValuationPair.exists_mulVec_eq_zero_on`: clearing one entry, or the entries on a set
  of indices, against a pivot, by a matrix acting only through the indices involved.
* `Subring.IsValuationPair.exists_mulVec_eq_single`: some `W : GL ι R` maps `p` to a multiple of
  the `i`-th basis vector.
* `Subring.IsValuationPair.exists_eq_smul_col`: some `V : GL ι R` satisfies
  `p = (V⁻¹ p)_i • V e_i`.
* `Subring.IsValuationPair.exists_blockTriangular_mul`,
  `Subring.IsValuationPair.exists_mul_blockTriangular`: some `W : GL ι R` makes `W * M`, and
  some `k : GL ι R` makes `M * k`, block triangular for a given weight.

## References

* The folder `grh` of <https://github.com/lsernau/grh-lean> at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, `Lib/General/LinearAlgebra/HermiteForm.lean`
  (`New.IsValuationPair.hermite`).
* J. Tits, *Reductive groups over local fields*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33 (1979), §3.3.2, for the Iwasawa decomposition.
* N. Bourbaki, *Commutative Algebra*, Chapter VI (valuation rings and finitely generated ideals).
-/

public section

open Matrix Submodule

namespace Subring

variable {A : Type*} [CommRing A] {R : Subring A} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The clearing step: for a pivot `i ≠ j`, some `W : GL ι R` sends the `j`-th entry of `q` to
zero. It acts only through the `i`-th and `j`-th entries: it leaves every other entry of every
vector unchanged, and it fixes every vector vanishing at `i` and at `j`. -/
theorem IsValuationPair.exists_mulVec_apply_eq_zero (hR : R.IsValuationPair)
    {i j : ι} (hij : i ≠ j) (q : ι → A) :
    ∃ W : GL ι R, (GeneralLinearGroup.map R.subtype W *ᵥ q) j = 0 ∧
      (∀ (p : ι → A) (k : ι), k ≠ i → k ≠ j → (GeneralLinearGroup.map R.subtype W *ᵥ p) k = p k) ∧
      ∀ p : ι → A, p i = 0 → p j = 0 → GeneralLinearGroup.map R.subtype W *ᵥ p = p := by
  obtain ⟨e, he, hle⟩ := isValuationPair_iff.1 hR (q i) (q j)
  obtain ⟨r, hr⟩ := mem_span_singleton.1 (le_sup_left.trans hle (mem_span_singleton_self _))
  obtain ⟨s, hs⟩ := mem_span_singleton.1 (le_sup_right.trans hle (mem_span_singleton_self _))
  rw [Subring.smul_def, smul_eq_mul] at hr hs
  have he' : (e : A) * e = e := congrArg Subtype.val he.eq
  -- `c` subtracts `s` times row `i` from row `j`; `d` swaps rows `i, j`, then subtracts `r` times
  -- row `i` from row `j`.
  let c : GL ι R := TauCeti.transvectionUnit hij.symm (-s)
  let d : GL ι R := TauCeti.transvectionUnit hij.symm (-r) * GeneralLinearGroup.swap R i j
  have hd (p : ι → A) : (GeneralLinearGroup.map R.subtype d).val *ᵥ p =
      Function.update (p ∘ Equiv.swap i j) j (p i - r * p j) := by
    simp only [d, map_mul, Units.val_mul, ← mulVec_mulVec, GeneralLinearGroup.map_swap,
      GeneralLinearGroup.val_swap, swap_mulVec, TauCeti.map_transvectionUnit,
      TauCeti.transvectionUnit_mulVec]
    simp [sub_eq_add_neg]
  have hc (p : ι → A) : (GeneralLinearGroup.map R.subtype c).val *ᵥ p =
      Function.update p j (p j - s * p i) := by
    simp only [c, TauCeti.map_transvectionUnit, TauCeti.transvectionUnit_mulVec]
    simp [sub_eq_add_neg]
  -- the patched matrix is `e • d + (1 - e) • c`
  have hW (p : ι → A) (k : ι) :
      ((GeneralLinearGroup.map R.subtype (c * he.cutGL (c⁻¹ * d))).val *ᵥ p) k =
        e * Function.update (p ∘ Equiv.swap i j) j (p i - r * p j) k +
          (1 - e) * Function.update p j (p j - s * p i) k := by
    rw [he.val_map_mul_cutGL_inv_mul, add_mulVec, smul_mulVec, smul_mulVec, hd, hc]
    simp
  refine ⟨c * he.cutGL (c⁻¹ * d), ?_, fun p k hki hkj ↦ ?_, fun p hpi hpj ↦ funext fun k ↦ ?_⟩
  · rw [hW]
    simp only [Function.update_self]
    linear_combination (-(e : A)) * hr + (r : A) * (q j - q i) * he' -
      (1 - (e : A)) * hs + (s : A) * (q i - q j) * he'
  · rw [hW, Function.update_of_ne hkj, Function.update_of_ne hkj, Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne hki hkj]
    ring
  · rw [hW]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hpi, hpj]
    · rw [Function.update_of_ne hkj, Function.update_of_ne hkj, Function.comp_apply]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left, hpj, hpi]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        ring

/-- For a finite set `t` of indices avoiding the pivot `i`, a single `W : GL ι R` sends `p` to a
vector vanishing at every index of `t`, and fixes every vector vanishing at `i` and on `t`. The
induction on `t` is the one of `Matrix.exists_gl_mul_eq_zero_on_of_preValuationRing`, with the
valuation-pair clearing step. -/
theorem IsValuationPair.exists_mulVec_eq_zero_on (hR : R.IsValuationPair) (p : ι → A)
    {i : ι} {t : Finset ι} (hi : i ∉ t) :
    ∃ W : GL ι R, (∀ j ∈ t, (GeneralLinearGroup.map R.subtype W *ᵥ p) j = 0) ∧
      ∀ q : ι → A, q i = 0 → (∀ j ∈ t, q j = 0) → GeneralLinearGroup.map R.subtype W *ᵥ q = q := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert j t hj ih =>
    obtain ⟨hij, hi⟩ : i ≠ j ∧ i ∉ t := by simpa [eq_comm] using hi
    obtain ⟨W, hW, hWfix⟩ := ih hi
    obtain ⟨V, hVj, hV, hVfix⟩ :=
      hR.exists_mulVec_apply_eq_zero hij (GeneralLinearGroup.map R.subtype W *ᵥ p)
    refine ⟨V * W, fun k hk ↦ ?_, fun q hqi hqt ↦ ?_⟩ <;>
      simp only [map_mul, Units.val_mul, ← mulVec_mulVec]
    · obtain rfl | hk := Finset.mem_insert.1 hk
      · exact hVj
      · rw [hV _ k (fun h ↦ hi (h ▸ hk)) (fun h ↦ hj (h ▸ hk)), hW k hk]
    · rw [hWfix q hqi fun k hk ↦ hqt k (Finset.mem_insert_of_mem hk),
        hVfix q hqi (hqt j (Finset.mem_insert_self j t))]

/-- **Hermite form of one column over a valuation pair.** For a valuation pair `R ⊆ A`, every
vector `p : ι → A` and every index `i`, some `W : GL ι R` sends `p` to a multiple of the `i`-th
basis vector: `W p = (W p)_i • e_i`. -/
theorem IsValuationPair.exists_mulVec_eq_single (hR : R.IsValuationPair) (p : ι → A) (i : ι) :
    ∃ W : GL ι R, GeneralLinearGroup.map R.subtype W *ᵥ p =
      Pi.single i ((GeneralLinearGroup.map R.subtype W *ᵥ p) i) := by
  obtain ⟨W, hW, -⟩ := hR.exists_mulVec_eq_zero_on p (i := i) (t := Finset.univ.erase i) (by simp)
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

/-- **Triangular row reduction over a valuation pair.** For a valuation pair `R ⊆ A`, every square
matrix `M` over `A` and every `b : ι → α` into a linear order, some `W : GL ι R` makes `W * M`
block triangular for `b`: `(W * M) i j = 0` whenever `b j < b i`. -/
theorem IsValuationPair.exists_blockTriangular_mul (hR : R.IsValuationPair) {α : Type*}
    [LinearOrder α] (b : ι → α) (M : Matrix ι ι A) :
    ∃ W : GL ι R, ((GeneralLinearGroup.map R.subtype W).val * M).BlockTriangular b := by
  -- Refine `b` to an injective weight `f`, breaking ties by an enumeration of `ι`.
  let f : ι → α ×ₗ Fin (Fintype.card ι) := fun i ↦ toLex (b i, Fintype.equivFin ι i)
  have hf : Function.Injective f := fun i j h ↦
    (Fintype.equivFin ι).injective (congrArg (fun x ↦ (ofLex x).2) h)
  have hfb {i j : ι} (h : b i < b j) : f i < f j := Prod.Lex.toLex_lt_toLex.2 (Or.inl h)
  -- Reduce the columns in order of increasing `f`: a reduced column `j` vanishes in every row `i`
  -- with `f j < f i`. To add the column `a`, clear its rows `i` with `f a < f i` against the pivot
  -- row `a`; the earlier columns vanish in all these rows, so the clearing leaves them unchanged.
  have reduce (s : Finset ι) : ∃ W : GL ι R, ∀ j ∈ s, ∀ i, f j < f i →
      ((GeneralLinearGroup.map R.subtype W).val * M) i j = 0 := by
    induction s using Finset.induction_on_max_value f with
    | empty => exact ⟨1, by simp⟩
    | insert a s ha hmax ih =>
      obtain ⟨W, hW⟩ := ih
      obtain ⟨V, hV, hVfix⟩ :=
        hR.exists_mulVec_eq_zero_on (((GeneralLinearGroup.map R.subtype W).val * M).col a)
          (i := a) (t := {i | f a < f i}) (by simp)
      have hcol (i j : ι) : ((GeneralLinearGroup.map R.subtype (V * W)).val * M) i j =
          ((GeneralLinearGroup.map R.subtype V).val *ᵥ
            ((GeneralLinearGroup.map R.subtype W).val * M).col j) i := by
        rw [map_mul, Units.val_mul, Matrix.mul_assoc, ← col_mul_eq_mulVec_col, col_apply]
      refine ⟨V * W, fun j hj i hji ↦ ?_⟩
      rw [hcol]
      obtain rfl | hjs := Finset.mem_insert.1 hj
      · exact hV i (by simpa using hji)
      · have hja : f j < f a := (hmax j hjs).lt_of_ne fun h ↦ ha (hf h ▸ hjs)
        rw [hVfix (((GeneralLinearGroup.map R.subtype W).val * M).col j) (hW j hjs a hja)
          fun k hk ↦ hW j hjs k (hja.trans (by simpa using hk))]
        exact hW j hjs i hji
  obtain ⟨W, hW⟩ := reduce Finset.univ
  exact ⟨W, fun i j hji ↦ hW j (Finset.mem_univ j) i (hfb hji)⟩

/-- **Iwasawa decomposition over a valuation pair.** For a valuation pair `R ⊆ A`, every square
matrix `M` over `A` and every `b : ι → α` into a linear order, some `k : GL ι R` makes `M * k`
block triangular for `b`. Thus `M = (M * k) * k⁻¹` is a block triangular matrix times a matrix of
`GL ι R`, and the block triangular factor is invertible when `M` is. -/
theorem IsValuationPair.exists_mul_blockTriangular (hR : R.IsValuationPair) {α : Type*}
    [LinearOrder α] (b : ι → α) (M : Matrix ι ι A) :
    ∃ k : GL ι R, (M * (GeneralLinearGroup.map R.subtype k).val).BlockTriangular b := by
  obtain ⟨W, hW⟩ := hR.exists_blockTriangular_mul (OrderDual.toDual ∘ b) Mᵀ
  refine ⟨(GeneralLinearGroup.transposeMulEquiv ι W).unop, fun i j hij ↦ ?_⟩
  have hk : (GeneralLinearGroup.map R.subtype (GeneralLinearGroup.transposeMulEquiv ι W).unop).val =
      (GeneralLinearGroup.map R.subtype W).valᵀ := by
    ext r c
    simp [GeneralLinearGroup.map_apply]
  rw [hk]
  calc (M * (GeneralLinearGroup.map R.subtype W).valᵀ) i j
      = ((GeneralLinearGroup.map R.subtype W).val * Mᵀ)ᵀ i j := by
        rw [transpose_mul, transpose_transpose]
    _ = 0 := hW (OrderDual.toDual_lt_toDual.2 hij)

end Subring
