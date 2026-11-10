/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
public import TauCeti.NumberTheory.Padics.BilinearForm.GaussSum
import TauCeti.Algebra.Group.AddChar
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.GaussSum
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Submodule.Compl
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.LinearAlgebra.Matrix.GaussSum
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# Gauss sums of the lower constituents of a dyadic Jordan splitting

Let `B` be a symmetric form on a finite free `ℤ_[2]`-module with a Jordan splitting `N` with
respect to `2`, so that `B` restricted to `N i` is `2 ^ i • C i` for a unimodular form `C i` of
rank `n i`. Write `ε i = χ₈(det C i)` for the sign and `t i = C i (w i) (w i)` for the oddity of
`C i`, where `w i` is a characteristic vector, and `e(t) = exp (2πi t)`. For `k ≥ j + 2`, this file
evaluates the Gauss sum modulo `2 ^ k` of the sum `L₍ⱼ₎` of the constituents of index at most `j`:

```text
∑_{x ∈ (ℤ/2^k)^{rank L₍ⱼ₎}} e(xᵀ G x / 2^k)
  = ∏_{i ≤ j} √2^{n i (k + i + 1)} · ε i^{k - i + 1} · e(t i / 8)
```

for a Gram matrix `G` of `L₍ⱼ₎`
(`LinearMap.BilinForm.IsJordanSplitting.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_prod`).
The Gauss sum of `L₍ⱼ₎` is the product of those of the constituents, the Gauss sum of `2 ^ i • C i`
modulo `2 ^ k` is `2 ^ (i n i)` times that of `C i` modulo `2 ^ (k - i)`, and the latter is given
in terms of the rank, sign and oddity of `C i`
(`LinearMap.BilinForm.IsSymm.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_χ₈`).

The partial sums `L₍ⱼ₎` are not isometry invariants, but when the constituent `N (j + 1)` is of
type II their Gauss sums modulo `2 ^ (j + 2)` are
(`LinearMap.BilinForm.IsJordanSplitting.sum_addChar_dotProduct_toMatrix_mulVec_eq_of_equivalent`).
Since the ranks `n i` are invariants as well, the evaluation turns this into a condition on the
Conway–Sloane `2`-adic symbol: the quantity

```text
∏_{i ≤ j} ε i^{j + 1 - i} · e((∑_{i ≤ j} t i) / 8)
```

is an isometry invariant
(`LinearMap.BilinForm.IsJordanSplitting.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent`).
So the oddities of the constituents up to `j` are invariant in total modulo `8`, up to `4` times
the number of signs `ε i = -1` with `j - i` even, while the individual signs and oddities are not:
sign walking `⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]`
(`TauCeti.equivalent_toBilin'_unary_two_hyperbolic`) changes the sign and the oddity of the
constituent of index `0` together, from `(1, 1)` to `(-1, 5)`, and leaves `ε 0 · e(t 0 / 8)`
unchanged.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_prod`:
  the Gauss sum of the constituents of index at most `j` modulo `2 ^ k`, for `k ≥ j + 2`, in terms
  of the ranks, signs and oddities of the constituents.
* `LinearMap.BilinForm.IsJordanSplitting.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent`: if
  `N (j + 1)` is of type II, then `∏_{i ≤ j} ε i^{j + 1 - i} · e((∑_{i ≤ j} t i) / 8)` is an
  isometry invariant.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module ZMod
open LinearMap (BilinForm)
open scoped Matrix

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M} {α : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- The Gauss sum modulo `2 ^ k` of a single constituent `N i`, with `i + 2 ≤ k`, in terms of the
rank, sign and oddity of its unimodular rescaling `C`. -/
private theorem IsJordanSplitting.sum_stdAddChar_dotProduct_two_pow_smul_toMatrix_map_mulVec_eq
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {i k : ℕ} (hik : i + 2 ≤ k)
    {C : BilinForm ℤ_[2] (N i)} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    (d : Basis (α i) ℤ_[2] (N i)) {w : N i} (hw : C.IsCharacteristic w) :
    ∑ x : α i → ZMod (2 ^ k),
        stdAddChar (x ⬝ᵥ ((2 : ℤ_[2]) ^ i • C.toMatrix d).map (PadicInt.toZModPow k) *ᵥ x) =
      (√2 : ℂ) ^ (Fintype.card (α i) * (k + i + 1)) *
        ((χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) : ℤ) : ℂ) ^ (k - i + 1) *
          stdAddChar (PadicInt.toZModPow 3 (C w w)) := by
  have h2 : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  have hCs : C.IsSymm := IsSymm.of_smul h2 (hC ▸ hB.restrict (N i))
  have hdet : IsUnit (C.toMatrix d).det :=
    d.isUnit_det_of_isPerfPair C ((h.isModular i).isPerfPair_of_smul_eq h2 hC)
  obtain ⟨m, rfl⟩ : ∃ m, k = i + m := ⟨k - i, by omega⟩
  have hscale := PadicInt.sum_stdAddChar_dotProduct_map_pow_smul_mulVec (p := 2) (C.toMatrix d)
    (rfl : i + m = i + m)
  rw [Nat.cast_ofNat, Nat.cast_ofNat] at hscale
  rw [hscale, hCs.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_χ₈ d hdet hw (by omega)]
  -- `2 ^ (i n) = √2 ^ (2 i n)`, and the exponents of `√2` add up.
  have hsq : (2 : ℂ) = (√2 : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt zero_le_two, Complex.ofReal_ofNat]
  rw [hsq, ← pow_mul, ← mul_assoc, ← mul_assoc, ← pow_add,
    show i + m - i + 1 = m + 1 by omega]
  congr 3
  ring

/-- **The Gauss sum of the lower constituents of a dyadic Jordan splitting.** Let `B` be a
symmetric form over `ℤ_[2]` with a Jordan splitting `N` with respect to `2`. For `i ≤ j`, let `C i`
be the unimodular rescaling of the constituent `N i`, so that `2 ^ i • C i` is the restriction of
`B` to `N i`, let `d i` be a basis of `N i` and `w i` a characteristic vector of `C i`. Then for
`k ≥ j + 2`, with `e(t) = exp (2πi t)`, the Gauss sum modulo `2 ^ k` of a Gram matrix `G` of the
sum `L₍ⱼ₎` of the constituents of index at most `j` is

```text
∑_x e(xᵀ G x / 2^k)
  = ∏_{i ≤ j} √2^{n i (k + i + 1)} · χ₈(det C i)^{k - i + 1} · e(C i (w i) (w i) / 8),
```

where `n i` is the rank of `N i`. In the language of Conway–Sloane `2`-adic symbols, the factors
are given by the ranks, signs and oddities of the constituents. -/
theorem IsJordanSplitting.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_prod
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {j k : ℕ} (hk : j + 2 ≤ k)
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i ≤ j, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i ≤ j, (C i).IsCharacteristic (w i)) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℤ_[2] ↥(⨆ i ∈ Set.Iic j, N i)) :
    ∑ x : κ → ZMod (2 ^ k), stdAddChar
        (x ⬝ᵥ ((B.restrict (⨆ i ∈ Set.Iic j, N i)).toMatrix b).map (PadicInt.toZModPow k) *ᵥ x) =
      ∏ i ∈ Finset.Iic j, (√2 : ℂ) ^ (Fintype.card (α i) * (k + i + 1)) *
        ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^ (k - i + 1) *
          stdAddChar (PadicInt.toZModPow 3 (C i (w i) (w i))) := by
  classical
  -- `L₍ⱼ₎` is the orthogonal internal sum of the constituents of index at most `j`.
  have hP := DirectSum.isInternal_biSup_submodule_of_iSupIndep (Set.Iic j)
    (h.isInternal.submodule_iSupIndep.comp Subtype.val_injective)
  let d' (i : Set.Iic j) : Basis (α i) ℤ_[2] ((N i).comap (⨆ i ∈ Set.Iic j, N i).subtype) :=
    (d i).map (Submodule.comapSubtypeEquivOfLe (le_biSup N i.2)).symm
  -- In the basis collected from the `d i`, the Gram matrix is block diagonal.
  have hgram : (B.restrict (⨆ i ∈ Set.Iic j, N i)).toMatrix (hP.collectedBasis d') =
      Matrix.blockDiagonal' fun i : Set.Iic j ↦ (2 : ℤ_[2]) ^ (i : ℕ) • (C i).toMatrix (d i) := by
    rw [toMatrix_collectedBasis hP
      (fun i i' hii x hx y hy ↦ h.apply_eq_zero i i' (fun h ↦ hii (Subtype.ext h)) _ hx _ hy) d']
    congr 1
    funext i
    refine Matrix.ext fun a a' ↦ ?_
    simpa [toMatrix_apply, d'] using (LinearMap.congr_fun₂ (hC i i.2) (d i a) (d i a')).symm
  rw [sum_addChar_dotProduct_toMatrix_map_mulVec_eq _ (hP.collectedBasis d') b, hgram,
    Matrix.blockDiagonal'_map _ _ (map_zero _), Matrix.sum_addChar_dotProduct_blockDiagonal'_mulVec,
    Finset.prod_subtype (Finset.Iic j) (p := (· ∈ Set.Iic j)) (by simp)]
  exact Fintype.prod_congr _ _ fun i ↦
    h.sum_stdAddChar_dotProduct_two_pow_smul_toMatrix_map_mulVec_eq hB
      (by have := Set.mem_Iic.mp i.2; omega)
      (hC i i.2) (d i) (hw i i.2)

/-- **The signs and oddities of the lower constituents of a dyadic Jordan splitting.** Let `B` and
`B'` be isometric symmetric forms on finite free `ℤ_[2]`-modules, with Jordan splittings `N` and
`N'` with respect to `2`. For `i ≤ j`, let `C i` and `C' i` be the unimodular rescalings of the
constituents `N i` and `N' i`, with bases `d i`, `d' i` and characteristic vectors `w i`, `w' i`.
Suppose that `N (j + 1)` is of type II, that is, even at its own scale (possibly zero). Then, with
the signs `ε i = χ₈(det C i)`, `ε' i = χ₈(det C' i)`, the oddities `t i = C i (w i) (w i)`,
`t' i = C' i (w' i) (w' i)` and `e(t) = exp (2πi t)`,

```text
∏_{i ≤ j} ε i^{j + 1 - i} · e((∑_{i ≤ j} t i) / 8)
  = ∏_{i ≤ j} ε' i^{j + 1 - i} · e((∑_{i ≤ j} t' i) / 8).
```

This is the Gauss-sum invariant of the sum of the constituents of index at most `j` modulo
`2 ^ (j + 2)`, divided by its absolute value, which only depends on the ranks. The parity hypothesis
cannot be dropped: `⟨1⟩ ⊥ ⟨2⟩ ≅ ⟨3⟩ ⊥ ⟨6⟩`, while for `j = 0` the two sides are `e(1 / 8)` and
`-e(3 / 8)`. -/
theorem IsJordanSplitting.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M']
    {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'} {α' : ℕ → Type*}
    [∀ i, Fintype (α' i)] [∀ i, DecidableEq (α' i)] (h : B.IsJordanSplitting 2 N)
    (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm) (hBB' : B.Equivalent B') {j : ℕ}
    (hnext : ∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v)
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i ≤ j, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i ≤ j, (C i).IsCharacteristic (w i))
    (C' : ∀ i, BilinForm ℤ_[2] (N' i)) (hC' : ∀ i ≤ j, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i ≤ j, (C' i).IsCharacteristic (w' i)) :
    (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^
        (j + 1 - i)) * stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
      (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^
        (j + 1 - i)) *
        stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i))) := by
  classical
  obtain ⟨ε⟩ := _root_.id hBB'
  have : Module.Free ℤ_[2] M' := .of_equiv ε.toLinearEquiv
  have : Module.Finite ℤ_[2] M' := .equiv ε.toLinearEquiv
  have hB' : B'.IsSymm := ⟨fun x y ↦ by rw [← ε.symm.map_app, ← ε.symm.map_app, hB.eq]⟩
  -- The constituents of the two splittings have the same ranks.
  have hn (i : ℕ) : Fintype.card (α i) = Fintype.card (α' i) := by
    rw [← finrank_eq_card_basis (d i), ← finrank_eq_card_basis (d' i)]
    exact h.finrank_eq_of_equivalent h' hBB' two_ne_zero PadicInt.not_isUnit_two i
  -- Bases of the two sums of the constituents of index at most `j`, with the same index type.
  obtain ⟨_, _⟩ := (⨆ i ∈ Set.Iic j, N i).finite_free_of_isCompl
    (h.isCompl_biSup_Iic_biSup_Ici j)
  obtain ⟨_, _⟩ := (⨆ i ∈ Set.Iic j, N' i).finite_free_of_isCompl
    (h'.isCompl_biSup_Iic_biSup_Ici j)
  have hrank : finrank ℤ_[2] ↥(⨆ i ∈ Set.Iic j, N' i) = finrank ℤ_[2] ↥(⨆ i ∈ Set.Iic j, N i) := by
    simp only [h.finrank_biSup_Iic, h'.finrank_biSup_Iic, finrank_eq_card_basis (d _),
      finrank_eq_card_basis (d' _), hn]
  -- The Gauss sums modulo `2 ^ (j + 2)` of these sums agree, and they are evaluated as products.
  have hf : PadicInt.toZModPow (p := 2) (j + 2) (2 * 2 ^ (j + 1)) = 0 := by
    rw [← pow_succ', map_pow, map_ofNat]
    exact_mod_cast ZMod.natCast_self (2 ^ (j + 2))
  have key := h.sum_addChar_dotProduct_toMatrix_mulVec_eq_of_equivalent h' hB hBB'
    (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl hnext (PadicInt.toZModPow (j + 2)) hf
    stdAddChar (finBasis ℤ_[2] _) ((finBasis ℤ_[2] _).reindex (finCongr hrank))
  rw [h.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_prod hB le_rfl C hC d w hw,
    h'.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_prod hB' le_rfl C' hC' d' w' hw',
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib] at key
  simp only [hn] at key
  rw [mul_assoc, mul_assoc] at key
  replace key := mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (by simp))
    key
  -- `ε ^ (j + 3 - i) = ε ^ (j + 1 - i)`, since `j + 1 - i ≥ 1` and `ε ^ 3 = ε`.
  have hχ (x : ZMod (2 ^ 3)) {i : ℕ} (hi : i ∈ Finset.Iic j) :
      ((χ₈ x : ℤ) : ℂ) ^ (j + 2 - i + 1) = ((χ₈ x : ℤ) : ℂ) ^ (j + 1 - i) := by
    have h3 : χ₈ x ^ 3 = χ₈ x := by revert x; decide
    have h3' : ((χ₈ x : ℤ) : ℂ) ^ 3 = (χ₈ x : ℤ) := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h3
    have hij := Finset.mem_Iic.mp hi
    obtain ⟨m, hm⟩ : ∃ m, j + 1 - i = m + 1 := ⟨j - i, by omega⟩
    rw [hm, show j + 2 - i + 1 = m + 3 by omega, pow_add, pow_add, h3', pow_one]
  rw [Finset.prod_congr rfl fun i hi ↦ hχ _ hi, Finset.prod_congr rfl fun i hi ↦ hχ _ hi] at key
  simpa only [map_sum, AddChar.map_sum_eq_prod] using key

end LinearMap.BilinForm
