/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Iwahori

/-!
# The Iwasawa–Bruhat decomposition of `GL_m` over a valued field

Let `K` be a field with a valuation subring `𝒪` (for instance the ring of integers of a
nonarchimedean local field), and let `I₁ ⊆ GL_m(K)` be the image of the pro-`p` Iwahori subgroup
`TauCeti.iwahoriOne m 𝒪` of `GL_m(𝒪)`: the integral invertible matrices that are upper
unitriangular modulo the maximal ideal. In terms of the valuation `v` of `𝒪`, a matrix `k ∈ GL_m(K)`
lies in `I₁` exactly when all its entries have `v ≤ 1`, its entries below the diagonal have
`v < 1`, and `v (k i i - 1) < 1` for every `i` (`TauCeti.mem_map_iwahoriOne_iff`).

The **Iwasawa–Bruhat decomposition** says that every `g ∈ GL_m(K)` factors as

`g = u * t * σ * k`,

with `u` upper unitriangular over `K`, `t` diagonal, `σ` a permutation matrix and `k ∈ I₁`; and
that for `g ∈ I₁` the factor `u` can be chosen in `I₁` with `u⁻¹ * g` lower triangular (the
Iwahori factorization of `I₁`). It is a decomposition `GL_m(K) = U(K) · N · I₁` along the
pro-`p` Iwahori subgroup, `N` the monomial matrices, without any Bruhat–Tits theory.

## The construction

Call `p` the *pivot* of a nonzero vector `x : m → K` if `p` is the first index at which `v ∘ x`
takes its largest value. A row of `k ∈ I₁` has its pivot at the
diagonal, and a row of `t * σ * k` is a nonzero multiple of a row of `k`. So `g = u * t * σ * k`
says exactly that the rows of `u⁻¹ * g` have pairwise distinct pivots, and then `t`, `σ` and `k`
are read off these rows. The rows are produced by elimination from the bottom up:

* for a subspace `W` of `K^m`, vectors of `W` with pairwise distinct pivots are linearly
  independent (an ultrametric argument at the first pivot of largest weight), while a nonzero
  vector of `W` vanishing at all pivots of `W` is impossible; so the set `P(W)` of pivots of the
  nonzero vectors of `W` has `dim W` elements and restriction to `P(W)` is an isomorphism
  `W ≃ K^{P(W)}`;
* for each row `g_i`, subtract the vector of `W_{i+1} = span (g_j)_{j > i}` that agrees with
  `g_i` on `P(W_{i+1})`. The difference is nonzero and vanishes on `P(W_{i+1})`, so its pivot
  lies in `P(W_i) \ P(W_{i+1})`; these sets are disjoint for distinct `i`.

For `g ∈ I₁` the Iwahori factorization
`TauCeti.exists_mem_upperUnitriangularGroup_isLowerTriangular_inv_mul` over `𝒪` gives the
factor `u`, with `t = σ = 1`.

## Main results

* `TauCeti.mem_map_iwahoriOne_iff`: membership in the image of the pro-`p` Iwahori subgroup,
  through valuations of the entries.
* `TauCeti.exists_eq_mul_diagGL_mul_permutationGL_mul`: the Iwasawa–Bruhat decomposition
  `g = u * t * σ * k`.
* `TauCeti.exists_eq_mul_diagGL_mul_permutationGL_mul_and_isLowerTriangular`: the same
  decomposition, with `u ∈ I₁` and `u⁻¹ * g` lower triangular when `g ∈ I₁`.

## References

* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965), §2.
* W. Casselman, *Introduction to admissible representations of p-adic groups: `GL_n`*, notes,
  §13.
-/

public section

namespace TauCeti

open Matrix

variable {K : Type*} [Field K] (A : ValuationSubring K) {m : Type*} [Fintype m] [LinearOrder m]

/-! ### The pro-`p` Iwahori subgroup in `GL_m(K)` -/

/-- **Membership in the pro-`p` Iwahori subgroup of `GL_m(K)`.** An invertible matrix over `K`
comes from the pro-`p` Iwahori subgroup of `GL_m(𝒪)` exactly when all its entries are integral,
its entries below the diagonal lie in the maximal ideal, and its diagonal entries are congruent
to `1` modulo the maximal ideal, all measured by the valuation of `𝒪`. -/
theorem mem_map_iwahoriOne_iff {g : GL m K} :
    g ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) ↔
      (∀ i j, A.valuation (g i j) ≤ 1) ∧ (∀ ⦃i j⦄, j < i → A.valuation (g i j) < 1) ∧
        ∀ i, A.valuation (g i i - 1) < 1 := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hklow, hkdiag⟩ := mem_upperUnitriangularCongruenceSubgroup_iff.mp hk
    refine ⟨fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_⟩
    · rw [GeneralLinearGroup.map_apply]
      exact A.valuation_le_one _
    · rw [GeneralLinearGroup.map_apply]
      exact (A.valuation_lt_one_iff _).mp (hklow hji)
    · rw [GeneralLinearGroup.map_apply, ← map_one (algebraMap A K), ← map_sub]
      exact (A.valuation_lt_one_iff _).mp (hkdiag i)
  · rintro ⟨h1, hlow, hdiag⟩
    let M : Matrix m m A := of fun i j ↦ ⟨g i j, (A.valuation_le_one_iff _).mp (h1 i j)⟩
    have hlowM : ∀ ⦃i j⦄, j < i → M i j ∈ IsLocalRing.maximalIdeal A := fun _ _ hji ↦
      (A.valuation_lt_one_iff _).mpr (hlow hji)
    have hdiagM : ∀ i, M i i - 1 ∈ IsLocalRing.maximalIdeal A := fun i ↦
      (A.valuation_lt_one_iff _).mpr (hdiag i)
    -- Modulo the maximal ideal, `M` is upper unitriangular, so its determinant is a unit.
    have hdet : IsUnit M.det := by
      refine isUnit_det_of_isUpperTriangular_map (f := IsLocalRing.residue A)
        (fun _ _ hji ↦ (IsLocalRing.residue_eq_zero_iff _).mpr (hlowM hji)) fun i ↦ ?_
      rw [← sub_add_cancel (M i i) 1, map_add,
        (IsLocalRing.residue_eq_zero_iff _).mpr (hdiagM i), zero_add, map_one]
      exact isUnit_one
    refine ⟨GeneralLinearGroup.mk'' M hdet, ?_, ?_⟩
    · exact mem_upperUnitriangularCongruenceSubgroup_iff.mpr ⟨hlowM, hdiagM⟩
    · ext i j
      rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.val_mk'']
      rfl

/-! ### Pivots -/

/-- `p` is the *pivot* of `x`: the entry `x p` is nonzero, and `p` is the first index at which
the valuation of the entries of `x` is largest. -/
private def IsPivot (x : m → K) (p : m) : Prop :=
  x p ≠ 0 ∧ (∀ j, A.valuation (x j) ≤ A.valuation (x p)) ∧
    ∀ j < p, A.valuation (x j) < A.valuation (x p)

omit [Fintype m] in
/-- Every nonzero vector has a pivot. -/
private theorem exists_isPivot [Finite m] {x : m → K} (hx : x ≠ 0) : ∃ p, IsPivot A x p := by
  classical
  have := Fintype.ofFinite m
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  rw [Pi.zero_apply] at hj₀
  obtain ⟨q, -, hq⟩ :=
    Finset.exists_max_image Finset.univ (fun j ↦ A.valuation (x j)) ⟨j₀, Finset.mem_univ _⟩
  -- The pivot is the first index at which the largest valuation is attained.
  obtain ⟨p, hpT, hp⟩ := (Finset.univ.filter fun j ↦ A.valuation (x j) = A.valuation (x q))
    |>.exists_min_image id ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hpq : A.valuation (x p) = A.valuation (x q) := (Finset.mem_filter.mp hpT).2
  refine ⟨p, fun h0 ↦ hj₀ ?_, fun j ↦ hpq ▸ hq j (Finset.mem_univ _), fun j hj ↦ ?_⟩
  · rw [← map_eq_zero A.valuation]
    exact le_antisymm (by simpa [hpq.symm, h0] using hq j₀ (Finset.mem_univ _)) zero_le
  · rw [hpq]
    refine lt_of_le_of_ne (hq j (Finset.mem_univ _)) fun h ↦ ?_
    exact (hp j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).not_gt hj

omit [Fintype m] in
/-- Vectors with pairwise distinct pivots are linearly independent. Look at the first pivot among
the terms of largest valuation in a nontrivial vanishing combination: there that term dominates
all the others, which is impossible in an ultrametric field. -/
private theorem linearIndependent_of_isPivot {ι : Type*} [Finite ι] {f : ι → m → K}
    {piv : ι → m} (hpiv : Function.Injective piv) (hf : ∀ i, IsPivot A (f i) (piv i)) :
    LinearIndependent K f := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  let a : ι → A.ValueGroup := fun i ↦ A.valuation (c i * f i (piv i))
  obtain ⟨i₂, -, hi₂⟩ := Finset.exists_max_image Finset.univ a ⟨i₁, Finset.mem_univ _⟩
  obtain ⟨i₀, hi₀T, hi₀⟩ := (Finset.univ.filter fun i ↦ a i = a i₂).exists_min_image piv
    ⟨i₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have ha₀ : a i₀ = a i₂ := (Finset.mem_filter.mp hi₀T).2
  have hpos : 0 < a i₀ := by
    rw [ha₀]
    refine lt_of_lt_of_le ?_ (hi₂ i₁ (Finset.mem_univ _))
    simp only [a, map_mul]
    exact mul_pos (pos_iff_ne_zero.mpr ((A.valuation).ne_zero_iff.mpr hi₁))
      (pos_iff_ne_zero.mpr ((A.valuation).ne_zero_iff.mpr (hf i₁).1))
  -- The entry of the combination at the column `piv i₀`.
  have hcol := congrFun hc (piv i₀)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hcol
  have hlt : A.valuation (∑ i ∈ Finset.univ.erase i₀, c i * f i (piv i₀)) < a i₀ := by
    refine Valuation.map_sum_lt _ hpos.ne' fun i hi ↦ ?_
    rw [map_mul]
    rcases eq_or_ne (c i) 0 with hci | hci
    · rwa [hci, map_zero, zero_mul]
    have hcv : 0 < A.valuation (c i) := pos_iff_ne_zero.mpr ((A.valuation).ne_zero_iff.mpr hci)
    rcases (hi₂ i (Finset.mem_univ _)).lt_or_eq with h | h
    · calc A.valuation (c i) * A.valuation (f i (piv i₀))
          ≤ A.valuation (c i) * A.valuation (f i (piv i)) :=
            mul_le_mul_right ((hf i).2.1 _) _
        _ = a i := (map_mul _ _ _).symm
        _ < a i₀ := ha₀ ▸ h
    · -- A term of largest valuation: its pivot comes after `piv i₀`.
      have hlt' : piv i₀ < piv i := lt_of_le_of_ne
        (hi₀ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
        (hpiv.ne (Finset.ne_of_mem_erase hi).symm)
      calc A.valuation (c i) * A.valuation (f i (piv i₀))
          < A.valuation (c i) * A.valuation (f i (piv i)) :=
            mul_lt_mul_of_pos_left ((hf i).2.2 _ hlt') hcv
        _ = a i := (map_mul _ _ _).symm
        _ = a i₀ := h.trans ha₀.symm
  have := Valuation.map_add_eq_of_lt_left _ hlt
  rw [hcol, map_zero] at this
  exact hpos.ne this

open Classical in
/-- The set of pivots of the nonzero vectors of a subspace `W` of `K^m`. -/
private noncomputable def pivotSet (W : Submodule K (m → K)) : Finset m :=
  Finset.univ.filter fun p ↦ ∃ w ∈ W, IsPivot A w p

private theorem mem_pivotSet {W : Submodule K (m → K)} {p : m} :
    p ∈ pivotSet A W ↔ ∃ w ∈ W, IsPivot A w p := by
  classical
  simp [pivotSet]

/-- Every vector agrees with some vector of `W` at the pivots of `W`: restriction to the pivots of
`W` is injective on `W`, and the pivots of `W` are at most `dim W` in number. -/
private theorem exists_mem_eqOn_pivotSet (W : Submodule K (m → K)) (x : m → K) :
    ∃ w ∈ W, ∀ p ∈ pivotSet A W, w p = x p := by
  let r : W →ₗ[K] (pivotSet A W → K) :=
    (LinearMap.funLeft K K (Subtype.val : pivotSet A W → m)).comp W.subtype
  have hinj : Function.Injective r := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    obtain ⟨p, hp⟩ := exists_isPivot A (x := (w : m → K)) fun h ↦ hne (Subtype.ext h)
    exact hp.1 (congrFun hw ⟨p, (mem_pivotSet A).mpr ⟨w, w.property, hp⟩⟩)
  have hcard : Fintype.card (pivotSet A W) ≤ Module.finrank K W := by
    choose f hfW hf using fun p : pivotSet A W ↦ (mem_pivotSet A).mp p.property
    exact (LinearIndependent.of_comp W.subtype (v := fun p ↦ (⟨f p, hfW p⟩ : W))
      (linearIndependent_of_isPivot A Subtype.val_injective hf)).fintype_card_le_finrank
  have hsurj : Function.Surjective r := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    refine le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) ?_
    rwa [Module.finrank_pi]
  obtain ⟨w, hw⟩ := hsurj fun p ↦ x p
  exact ⟨w, w.property, fun p hp ↦ congrFun hw ⟨p, hp⟩⟩

private theorem pivotSet_mono {W W' : Submodule K (m → K)} (h : W ≤ W') :
    pivotSet A W ⊆ pivotSet A W' := fun p hp ↦ by
  obtain ⟨w, hw, hwp⟩ := (mem_pivotSet A).mp hp
  exact (mem_pivotSet A).mpr ⟨w, h hw, hwp⟩

/-- Subtracting from each row of `G` a combination of the rows below it is multiplication on the
left by an upper-unitriangular matrix. -/
private theorem exists_isUpperUnitriangular_mul_apply (G : Matrix m m K) {w : m → m → K}
    (hw : ∀ i, w i ∈ Submodule.span K (G.row '' ↑(Finset.univ.filter fun j ↦ i < j))) :
    ∃ U : Matrix m m K, U.IsUpperUnitriangular ∧ ∀ i l, (U * G) i l = G i l - w i l := by
  classical
  choose c hc using fun i ↦ (Submodule.mem_span_image_finset_iff_exists_fun' K).mp (hw i)
  let U : Matrix m m K := of fun i j ↦ if i = j then 1 else if i < j then -c i j else 0
  refine ⟨U, (isUpperUnitriangular_iff U).mpr
    ⟨fun i j hji ↦ by simp [U, hji.ne', hji.not_gt], fun i ↦ by simp [U]⟩, fun i l ↦ ?_⟩
  have hterm (j : m) : U i j * G j l =
      (if i = j then G j l else 0) - (if i < j then c i j * G j l else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [U, h, h.ne]
    · simp [U]
    · simp [U, h.ne', h.not_gt]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), ← Finset.sum_filter, ← hc i]
  simp [Finset.sum_apply]

/-- Elimination from the bottom up: some upper-unitriangular `U` makes the rows of `U * g` have
pairwise distinct pivots. -/
private theorem exists_isUpperUnitriangular_isPivot_mul (g : GL m K) :
    ∃ U : Matrix m m K, U.IsUpperUnitriangular ∧ ∃ q : m → m, Function.Injective q ∧
      ∀ i, IsPivot A ((U * (g : Matrix m m K)) i) (q i) := by
  classical
  set G : Matrix m m K := (g : Matrix m m K)
  -- `W i` is spanned by the rows below the row `i`, and `W' i` also by the row `i`.
  let W : m → Submodule K (m → K) := fun i ↦
    Submodule.span K (G.row '' ↑(Finset.univ.filter fun j ↦ i < j))
  let W' : m → Submodule K (m → K) := fun i ↦
    Submodule.span K (G.row '' ↑(Finset.univ.filter fun j ↦ i ≤ j))
  have hWW' (i : m) : W i ≤ W' i := by
    refine Submodule.span_mono (Set.image_mono fun l hl ↦ ?_)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl ⊢
    exact hl.le
  have hW'W {i j : m} (hij : i < j) : W' j ≤ W i := by
    refine Submodule.span_mono (Set.image_mono fun l hl ↦ ?_)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl ⊢
    exact hij.trans_le hl
  -- Subtract from the row `i` the vector of `W i` that agrees with it at the pivots of `W i`.
  choose w hwW hw using fun i ↦ exists_mem_eqOn_pivotSet A (W i) (G i)
  obtain ⟨U, hU, hrow⟩ := exists_isUpperUnitriangular_mul_apply G hwW
  have hrow' (i : m) : (U * G) i = G.row i - w i := funext (hrow i)
  refine ⟨U, hU, ?_⟩
  -- The new rows are nonzero, since the rows of `g` are linearly independent.
  have hne (i : m) : (U * G) i ≠ 0 := by
    rw [hrow', sub_ne_zero]
    intro h
    refine (linearIndependent_rows_of_det_ne_zero g.det_ne_zero).notMem_span_image
      (s := ↑(Finset.univ.filter fun j ↦ i < j)) (x := i) (by simp) ?_
    rw [h]
    exact hwW i
  choose q hq using fun i ↦ exists_isPivot A (hne i)
  -- The pivot of the new row `i` is a pivot of `W' i` but not of `W i`.
  have hqW (i : m) : q i ∉ pivotSet A (W i) := fun h ↦
    (hq i).1 (by rw [hrow, hw i _ h, sub_self])
  have hqW' (i : m) : q i ∈ pivotSet A (W' i) := by
    refine (mem_pivotSet A).mpr ⟨_, ?_, hq i⟩
    rw [hrow']
    exact sub_mem (Submodule.subset_span ⟨i, by simp, rfl⟩) (hWW' i (hwW i))
  refine ⟨q, fun i j hij ↦ ?_, hq⟩
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with h | h
  · exact hqW i (hij ▸ pivotSet_mono A (hW'W h) (hqW' j))
  · exact hqW j (hij ▸ pivotSet_mono A (hW'W h) (hqW' i))

/-! ### The decomposition -/

/-- **The Iwasawa–Bruhat decomposition of `GL_m(K)`.** For a valuation subring `𝒪` of `K`, every
`g ∈ GL_m(K)` is `u * t * σ * k` with `u` upper unitriangular over `K`, `t` diagonal, `σ` a
permutation matrix and `k` in the image of the pro-`p` Iwahori subgroup of `GL_m(𝒪)`. -/
theorem exists_eq_mul_diagGL_mul_permutationGL_mul (g : GL m K) :
    ∃ u ∈ upperUnitriangularGroup m K, ∃ (t : m → Kˣ) (σ : Equiv.Perm m),
      ∃ k ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)),
        g = u * diagGL t * permutationGL σ * k := by
  obtain ⟨U, hU, q, hq, hpiv⟩ := exists_isUpperUnitriangular_isPivot_mul A g
  set Y : Matrix m m K := U * (g : Matrix m m K)
  -- The pivots of the rows of `Y` give the permutation, the pivot entries the diagonal factor.
  let π : Equiv.Perm m := Equiv.ofBijective q hq.bijective_of_finite
  let t : m → Kˣ := fun i ↦ Units.mk0 (Y i (q i)) (hpiv i).1
  let k : GL m K := (permutationGL π⁻¹)⁻¹ * (diagGL t)⁻¹ * hU.toGL * g
  refine ⟨hU.toGL⁻¹, inv_mem (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup hU), t,
    π⁻¹, k, ?_, by simp only [k]; group⟩
  -- The row `π i = q i` of `k` is the row `i` of `Y` divided by its pivot entry.
  have hk (i j : m) : (k : Matrix m m K) (π i) j = (Y i (q i))⁻¹ * Y i j := by
    simp only [k]
    rw [← map_inv, inv_inv, ← map_inv, mul_assoc, mul_assoc, Units.val_mul, permutationGL_coe,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply, Units.val_mul, diagGL_coe, diagonal_mul,
      Units.val_mul, hU.coe_toGL, Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_mk0, id]
  have hpos (i : m) : 0 < A.valuation (Y i (q i)) :=
    pos_iff_ne_zero.mpr ((A.valuation).ne_zero_iff.mpr (hpiv i).1)
  rw [mem_map_iwahoriOne_iff]
  refine ⟨fun r j ↦ ?_, fun r j hjr ↦ ?_, fun r ↦ ?_⟩ <;> obtain ⟨i, rfl⟩ := π.surjective r
  · rw [hk, map_mul, map_inv₀, ← div_eq_inv_mul, div_le_one₀ (hpos i)]
    exact (hpiv i).2.1 j
  · rw [hk, map_mul, map_inv₀, ← div_eq_inv_mul, div_lt_one₀ (hpos i)]
    exact (hpiv i).2.2 j hjr
  · rw [hk, Equiv.ofBijective_apply, inv_mul_cancel₀ (hpiv i).1, sub_self, map_zero]
    exact zero_lt_one

/-- **The Iwasawa–Bruhat decomposition with the Iwahori factorization.** Every `g ∈ GL_m(K)` is
`u * t * σ * k` as in `TauCeti.exists_eq_mul_diagGL_mul_permutationGL_mul`, where moreover, if
`g` lies in the image `I₁` of the pro-`p` Iwahori subgroup of `GL_m(𝒪)`, then so does `u`, and
`u⁻¹ * g` is lower triangular. -/
theorem exists_eq_mul_diagGL_mul_permutationGL_mul_and_isLowerTriangular (g : GL m K) :
    ∃ u ∈ upperUnitriangularGroup m K, ∃ (t : m → Kˣ) (σ : Equiv.Perm m),
      ∃ k ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)),
        g = u * diagGL t * permutationGL σ * k ∧
          (g ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) →
            u ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K)) ∧
              ((u⁻¹ * g : GL m K) : Matrix m m K).IsLowerTriangular) := by
  by_cases hg : g ∈ (iwahoriOne m A).map (GeneralLinearGroup.map (algebraMap A K))
  · obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨u', hu', hl⟩ := exists_mem_upperUnitriangularGroup_isLowerTriangular_inv_mul
      (IsLocalRing.ringJacobson_eq_maximalIdeal A).ge (iwahoriOne_le_iwahori hg')
    have hu'1 : u' ∈ iwahoriOne m A := upperUnitriangularCongruenceSubgroup_mono bot_le
      (upperUnitriangularCongruenceSubgroup_bot (m := m) (R := A) ▸ hu')
    refine ⟨GeneralLinearGroup.map (algebraMap A K) u',
      UpperUnitriangularGroup.coe_map (algebraMap A K) ⟨u', hu'⟩ ▸
        (UpperUnitriangularGroup.map (algebraMap A K) ⟨u', hu'⟩).property, 1, 1,
      GeneralLinearGroup.map (algebraMap A K) (u'⁻¹ * g'),
      Subgroup.mem_map_of_mem _ (mul_mem (inv_mem hu'1) hg'), by simp,
      fun _ ↦ ⟨Subgroup.mem_map_of_mem _ hu'1, fun i j hij ↦ ?_⟩⟩
    rw [← map_inv, ← map_mul, GeneralLinearGroup.map_apply, hl hij, map_zero]
  · obtain ⟨u, hu, t, σ, k, hk, h⟩ := exists_eq_mul_diagGL_mul_permutationGL_mul A g
    exact ⟨u, hu, t, σ, k, hk, h, fun h' ↦ absurd h' hg⟩

end TauCeti
