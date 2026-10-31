/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import Mathlib.Algebra.Lie.TensorProduct
public import TauCeti.Algebra.Lie.GeneralLinear.Carrier
import TauCeti.Algebra.Lie.GeneralLinear.CompleteReducibility
import TauCeti.Algebra.Lie.GeneralLinear.DualTensorProduct
import TauCeti.Algebra.Lie.GeneralLinear.Isotypic
import TauCeti.Algebra.Lie.Matrix.Single

/-!
# The dual-standard Pieri rule for `gl n`

Let `K` be an algebraically closed field of characteristic zero, `V = K^n` the standard module of
`gl n K` and `V*` its dual. For a dominant weight `μ`, this file decomposes the tensor product of
`V*` with the irreducible module `L(μ) = TauCeti.glIrreducible n μ`:

`V* ⊗ L(μ) ≅ ⨁ L(μ - εₜ)`,

the sum running over the indices `t` for which `μ - εₜ` is still dominant, each summand occurring
once (`TauCeti.gl_dual_standard_pieri`). Here `εₜ = Pi.single t 1`, and `-εₜ` are the weights of
`V*`, so the summands are exactly the weights `μ + (weight of V*)` that remain dominant.

## The argument

Write an element of `V* ⊗ M` as `∑ₛ e*ₛ ⊗ mₛ`, with `e*ₛ` the dual basis. The matrix unit `Eᵢⱼ`
sends `e*ᵢ` to `-e*ⱼ` and kills the other `e*ₛ`, so the coefficients of `⁅Eᵢⱼ, x⁆` are those of
`x` acted on by `Eᵢⱼ`, minus the coefficient at `i` moved to `j`
(`TauCeti.dualStandardCoeff_lie_single`).

* **Upper bound.** If `x` is a highest weight vector of weight `ν` and `s` is the least index with
  `mₛ ≠ 0`, the moved terms cannot reach `mₛ`, so `mₛ` is a highest weight vector of weight
  `ν + εₛ` in `M`. In an irreducible `M` all highest weight vectors have the same weight `μ`
  (`TauCeti.IsGlHighestWeightVector.weight_eq_of_isIrreducible`), so `ν = μ - εₛ`
  (`TauCeti.exists_eq_sub_single_of_isGlHighestWeightVector_dual_tensorProduct`). For a fixed
  weight `μ - εₜ` the least index is then `t` and `mₜ` lies on the highest weight line of `M`, so
  two such vectors are proportional: each weight occurs at most once.
* **Existence.** If `v` is a highest weight vector of weight `μ` and `μ - εₜ` is dominant, set
  `mₛ = 0` for `s < t`, `mₜ = v` and recursively
  `mₛ = (μₜ - μₛ + s - t - 1)⁻¹ • ∑_{k < s} Eₛₖ mₖ` for `s > t`; dominance of `μ - εₜ` makes the
  denominators nonzero. Then `∑ₛ e*ₛ ⊗ mₛ` is a highest weight vector of weight `μ - εₜ`
  (`TauCeti.exists_isGlHighestWeightVector_dual_tensorProduct`). These are the classical
  lowering-operator formulas for the Gelfand–Tsetlin patterns of `gl n`.

The identity matrix acts on `V* ⊗ L(μ)` by the scalar `∑ μ - 1`
(`TauCeti.one_lie_dual_tensorProduct`), so the module is completely
reducible, and the multiplicity-free criterion
`TauCeti.nonempty_lieModuleEquiv_directSum_glIrreducible_of_forall_exists_eq_smul` assembles the
two halves into the decomposition.

## Main results

* `TauCeti.exists_isGlHighestWeightVector_dual_tensorProduct`: for a highest weight vector of
  weight `μ` and a dominant `μ - εₜ`, the tensor product with the dual standard module has a
  highest weight vector of weight `μ - εₜ`.
* `TauCeti.exists_eq_sub_single_of_isGlHighestWeightVector_dual_tensorProduct`: for an
  irreducible module with a highest weight vector of weight `μ`, every highest weight vector of
  its tensor product with the dual standard module has weight `μ - εₜ` for some `t`.
* `TauCeti.gl_dual_standard_pieri`: **the dual-standard Pieri rule**
  `V* ⊗ L(μ) ≅ ⨁_{μ - εₜ dominant} L(μ - εₜ)`.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, GTM 255, §9.2.3
  (Pieri's rule for `gl n`).
* D. P. Zhelobenko, *Compact Lie Groups and Their Representations*, Translations of Mathematical
  Monographs 40, AMS, §§48–49 (lowering operators for `gl n`).
-/

public section

namespace TauCeti

open Matrix TensorProduct
open scoped DirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M]

variable [LieRingModule (Matrix (Fin n) (Fin n) K) M] [LieModule K (Matrix (Fin n) (Fin n) K) M]

/-! ### Highest weight vectors of `V* ⊗ M` -/

section UpperBound

/-- **The least nonzero coefficient of a highest weight vector is a highest weight vector**, of the
weight shifted by `εₛ`: the raising matrix units can move a coefficient only to a larger index. -/
private theorem isGlHighestWeightVector_dualStandardCoeff {nu : Fin n → K}
    {x : Module.Dual K (Fin n → K) ⊗[K] M} (hx : IsGlHighestWeightVector nu x) {s : Fin n}
    (hs : dualStandardCoeff M s x ≠ 0) (hmin : ∀ r < s, dualStandardCoeff M r x = 0) :
    IsGlHighestWeightVector (nu + Pi.single s (1 : K)) (dualStandardCoeff M s x) := by
  refine isGlHighestWeightVector_iff.mpr ⟨hs, fun k => lie_single_self_dualStandardCoeff
    hx.lie_single_self_eq_smul k s, fun i j hij => ?_⟩
  have h := dualStandardCoeff_lie_single i j s x
  rw [hx.lie_single_eq_zero hij, map_zero, eq_comm, sub_eq_zero] at h
  rw [h]
  split_ifs with hjs
  · exact hmin i (hjs ▸ hij)
  · rfl

variable [CharZero K] [LieModule.IsIrreducible K (Matrix (Fin n) (Fin n) K) M] {mu : Fin n → K}
  {v : M}

/-- **The weights of highest weight vectors of `V* ⊗ M`.** If `M` is irreducible with a highest
weight vector of weight `μ`, then every highest weight vector of `V* ⊗ M` has weight `μ - εₜ` for
some index `t`. -/
theorem exists_eq_sub_single_of_isGlHighestWeightVector_dual_tensorProduct
    (hv : IsGlHighestWeightVector mu v) {nu : Fin n → K}
    {x : Module.Dual K (Fin n → K) ⊗[K] M} (hx : IsGlHighestWeightVector nu x) :
    ∃ t : Fin n, nu = mu - Pi.single t 1 := by
  obtain ⟨s, hs, hmin⟩ := exists_dualStandardCoeff_ne_zero_of_ne_zero hx.ne_zero
  exact ⟨s, eq_sub_of_add_eq (hv.weight_eq_of_isIrreducible
    (isGlHighestWeightVector_dualStandardCoeff hx hs hmin))⟩

/-- A highest weight vector of weight `μ - εₜ` has vanishing coefficients below `t`, and its
coefficient at `t` is a nonzero multiple of the highest weight vector of `M`. -/
private theorem dualStandardCoeff_of_isGlHighestWeightVector_sub_single
    (hv : IsGlHighestWeightVector mu v) {t : Fin n} {x : Module.Dual K (Fin n → K) ⊗[K] M}
    (hx : IsGlHighestWeightVector (mu - Pi.single t 1) x) :
    (∀ r < t, dualStandardCoeff M r x = 0) ∧ ∃ c : K, c ≠ 0 ∧ dualStandardCoeff M t x = c • v := by
  obtain ⟨s, hs, hmin⟩ := exists_dualStandardCoeff_ne_zero_of_ne_zero hx.ne_zero
  have hxs := isGlHighestWeightVector_dualStandardCoeff hx hs hmin
  have hst : s = t := by
    by_contra hne
    have h := congr_fun (hv.weight_eq_of_isIrreducible hxs) s
    simp [hne] at h
  subst hst
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isGlHighestWeightVector_of_mem_lieSpan hv
    (by simp [lieSpan_singleton_eq_top_of_ne_zero hv.ne_zero])
    (by simpa using hxs.lie_single_self_eq_smul)
  exact ⟨hmin, c, fun h => hs (by rw [hc, h, zero_smul]), hc⟩

/-- **Each weight `μ - εₜ` occurs at most once**: two highest weight vectors of `V* ⊗ M` of that
weight are proportional. -/
private theorem exists_eq_smul_of_isGlHighestWeightVector_sub_single
    (hv : IsGlHighestWeightVector mu v) {t : Fin n} {x y : Module.Dual K (Fin n → K) ⊗[K] M}
    (hx : IsGlHighestWeightVector (mu - Pi.single t 1) x)
    (hy : IsGlHighestWeightVector (mu - Pi.single t 1) y) : ∃ c : K, y = c • x := by
  obtain ⟨hx0, a, ha, hxa⟩ := dualStandardCoeff_of_isGlHighestWeightVector_sub_single hv hx
  obtain ⟨hy0, b, hb, hyb⟩ := dualStandardCoeff_of_isGlHighestWeightVector_sub_single hv hy
  refine ⟨b / a, ?_⟩
  by_contra hne
  have hx' := hx.smul (div_ne_zero hb ha)
  have hz : IsGlHighestWeightVector (mu - Pi.single t 1) (y - (b / a) • x) :=
    isGlHighestWeightVector_iff.mpr ⟨sub_ne_zero.mpr hne, fun k => by
      rw [lie_sub, hy.lie_single_self_eq_smul, hx'.lie_single_self_eq_smul, smul_sub],
      fun i j hij => by
      rw [lie_sub, hy.lie_single_eq_zero hij, hx'.lie_single_eq_zero hij, sub_zero]⟩
  obtain ⟨-, c, hc, hzc⟩ := dualStandardCoeff_of_isGlHighestWeightVector_sub_single hv hz
  apply hc
  have hv0 := hv.ne_zero
  rw [map_sub, map_smul, hxa, hyb, smul_smul, div_mul_cancel₀ b ha, sub_self, eq_comm,
    smul_eq_zero] at hzc
  exact hzc.resolve_right hv0

end UpperBound

/-! ### The lowering vectors -/

section Lowering

variable (mu : Fin n → K) (v : M) (t : Fin n)

/-- The denominator `μₜ - μₛ + s - t - 1` of the lowering recursion. -/
private noncomputable def pieriDenom (s : Fin n) : K :=
  mu t - mu s + (((s : ℕ) - t - 1 : ℕ) : K)

/-- The lowering vectors: `0` below `t`, `v` at `t`, and above `t` the recursion
`mₛ = (μₜ - μₛ + s - t - 1)⁻¹ • ∑_{k < s} Eₛₖ mₖ`. -/
private noncomputable def pieriVec (s : Fin n) : M :=
  if s ≤ t then (if s = t then v else 0) else
    (pieriDenom mu t s)⁻¹ • ∑ k ∈ (Finset.Iio s).attach,
      ⁅(single s k.1 1 : Matrix (Fin n) (Fin n) K), pieriVec k.1⁆
termination_by (s : ℕ)
decreasing_by exact Fin.lt_def.mp (Finset.mem_Iio.mp k.2)

variable {mu v t}

omit [LieModule K (Matrix (Fin n) (Fin n) K) M] in
private theorem pieriVec_of_lt {s : Fin n} (h : s < t) : pieriVec mu v t s = 0 := by
  rw [pieriVec]
  simp [h.le, h.ne]

omit [LieModule K (Matrix (Fin n) (Fin n) K) M] in
private theorem pieriVec_self : pieriVec mu v t t = v := by
  rw [pieriVec]
  simp

omit [LieModule K (Matrix (Fin n) (Fin n) K) M] in
private theorem pieriVec_of_gt {s : Fin n} (h : t < s) :
    pieriVec mu v t s = (pieriDenom mu t s)⁻¹ •
      ∑ k ∈ Finset.Iio s, ⁅(single s k 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t k⁆ := by
  rw [pieriVec]
  simp only [h.not_ge, ite_false]
  rw [Finset.sum_attach (Finset.Iio s) fun k => ⁅(single s k 1 : Matrix (Fin n) (Fin n) K),
      pieriVec mu v t k⁆]

/-- The lowering vector at `s` has weight `μ - εₜ + εₛ`. -/
private theorem lie_single_self_pieriVec (hv : IsGlHighestWeightVector mu v) (s k : Fin n) :
    ⁅(single k k 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t s⁆ =
      (mu - Pi.single t (1 : K) + Pi.single s (1 : K) : Fin n → K) k • pieriVec mu v t s := by
  induction s using WellFoundedLT.induction generalizing k with
  | ind s ih =>
    rcases lt_trichotomy s t with hst | rfl | hts
    · simp [pieriVec_of_lt hst]
    · simp [pieriVec_self, hv.lie_single_self_eq_smul]
    · rw [pieriVec_of_gt hts, lie_smul, lie_sum, Finset.smul_sum, Finset.smul_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [lie_single_self_lie_single_eq_smul (fun k => ih r (Finset.mem_Iio.mp hr) k),
        smul_comm (α := M)]
      congr 1
      simp only [Pi.add_apply, Pi.sub_apply]
      ring

variable [CharZero K]

/-- The denominators above `t` are nonzero when `μ - εₜ` is dominant. -/
private theorem pieriDenom_ne_zero (hmut : IsGlDominantIntegral (mu - Pi.single t 1)) {s : Fin n}
    (h : t < s) : pieriDenom mu t s ≠ 0 := by
  obtain ⟨a, ha⟩ := hmut.exists_natCast_sub_of_le h.le
  have hts : ((s : ℕ) - t - 1 : ℕ) + 1 = (s : ℕ) - t := by
    rw [Fin.lt_def] at h; omega
  simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h.ne', sub_zero] at ha
  rw [pieriDenom, show mu t - mu s = (a : K) + 1 by linear_combination ha]
  exact_mod_cast (by omega : a + 1 + ((s : ℕ) - t - 1) ≠ 0)

omit [LieModule K (Matrix (Fin n) (Fin n) K) M] in
/-- The lowering recursion, read backwards: above `t`, the sum `∑_{k < s} Eₛₖ mₖ` is the
denominator times `mₛ`. -/
private theorem sum_lie_single_pieriVec_of_gt (hmut : IsGlDominantIntegral (mu - Pi.single t 1))
    {s : Fin n} (h : t < s) :
    ∑ k ∈ Finset.Iio s, ⁅(single s k 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t k⁆ =
      pieriDenom mu t s • pieriVec mu v t s := by
  rw [pieriVec_of_gt h, smul_inv_smul₀ (pieriDenom_ne_zero hmut h)]

/-- The sum `∑_{k ≤ i} Eᵢₖ mₖ` is `(μₜ + i - t) • mᵢ`. Below `t` both sides vanish; at `t` it is
the weight of `v`; above `t` it combines the recursion with the weight of `mᵢ`. -/
private theorem sum_Iic_lie_single_pieriVec (hv : IsGlHighestWeightVector mu v)
    (hmut : IsGlDominantIntegral (mu - Pi.single t 1)) (i : Fin n) :
    ∑ k ∈ Finset.Iic i, ⁅(single i k 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t k⁆ =
      (mu t + (((i : ℕ) - t : ℕ) : K)) • pieriVec mu v t i := by
  rcases lt_trichotomy i t with hit | rfl | hti
  · rw [pieriVec_of_lt hit, smul_zero]
    exact Finset.sum_eq_zero fun k hk => by
      rw [pieriVec_of_lt ((Finset.mem_Iic.mp hk).trans_lt hit), lie_zero]
  · rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self,
      Finset.sum_eq_zero fun k hk => by rw [pieriVec_of_lt (Finset.mem_Iio.mp hk), lie_zero],
      pieriVec_self, hv.lie_single_self_eq_smul]
    simp
  · rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self,
      sum_lie_single_pieriVec_of_gt hmut hti, lie_single_self_pieriVec hv, ← add_smul]
    congr 1
    have hti' : (((i : ℕ) - t : ℕ) : K) = (((i : ℕ) - t - 1 : ℕ) : K) + 1 := by
      rw [← Nat.cast_add_one]
      congr 1
      rw [Fin.lt_def] at hti
      omega
    simp only [pieriDenom, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hti.ne']
    rw [hti']
    ring

/-- The sum `∑_{k < j} Eᵢₖ mₖ` for `i < j` is `(μₜ + j - t - 1) • mᵢ`, provided each `Eᵢₖ` with
`i < k < j` sends `mₖ` to `mᵢ`: the terms with `k ≤ i` are `sum_Iic_lie_single_pieriVec`, and the
`j - i - 1` remaining terms are each `mᵢ`. -/
private theorem sum_Iio_lie_single_pieriVec (hv : IsGlHighestWeightVector mu v)
    (hmut : IsGlDominantIntegral (mu - Pi.single t 1)) {i j : Fin n} (hij : i < j)
    (h : ∀ k ∈ Finset.Ioo i j,
      ⁅(single i k 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t k⁆ = pieriVec mu v t i) :
    ∑ k ∈ Finset.Iio j, ⁅(single i k 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t k⁆ =
      (mu t + (((j : ℕ) - t - 1 : ℕ) : K)) • pieriVec mu v t i := by
  have hlow : (Finset.Iio j).filter (· ≤ i) = Finset.Iic i := by
    ext k; simpa using fun hki : k ≤ i => hki.trans_lt hij
  have hhigh : (Finset.Iio j).filter (fun k => ¬k ≤ i) = Finset.Ioo i j := by
    ext k; simp [and_comm, not_le]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Iio j) (· ≤ i), hlow, hhigh,
    sum_Iic_lie_single_pieriVec hv hmut, Finset.sum_congr rfl h, Finset.sum_const, Fin.card_Ioo,
    ← Nat.cast_smul_eq_nsmul K, ← add_smul]
  by_cases hit : i < t
  · rw [pieriVec_of_lt hit, smul_zero, smul_zero]
  · congr 1
    rw [not_lt, Fin.le_def] at hit
    rw [Fin.lt_def] at hij
    rw [add_assoc, ← Nat.cast_add]
    congr 3
    omega

/-- The raising matrix units on the lowering vectors: `Eᵢⱼ mₛ` is `mᵢ` when `j = s` and `0`
otherwise. The proof is by strong induction on `s`; above `t` the bracket `[Eᵢⱼ, Eₛₖ]` is expanded
inside the recursion, and when `j = s` the coefficient of `mᵢ` is exactly the denominator. -/
private theorem lie_single_pieriVec (hv : IsGlHighestWeightVector mu v)
    (hmut : IsGlDominantIntegral (mu - Pi.single t 1)) (s : Fin n) {i j : Fin n} (hij : i < j) :
    ⁅(single i j 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t s⁆ =
      if j = s then pieriVec mu v t i else 0 := by
  induction s using WellFoundedLT.induction generalizing i j with
  | ind s ih =>
    rcases lt_trichotomy s t with hst | rfl | hts
    · rw [pieriVec_of_lt hst, lie_zero]
      split_ifs with hjs
      · rw [pieriVec_of_lt (hij.trans (hjs ▸ hst))]
      · rfl
    · rw [pieriVec_self, hv.lie_single_eq_zero hij]
      split_ifs with hjs
      · rw [pieriVec_of_lt (hjs ▸ hij)]
      · rfl
    -- Above `t`, expand `Eᵢⱼ Eₛᵣ mᵣ = [Eᵢⱼ, Eₛᵣ] mᵣ + Eₛᵣ Eᵢⱼ mᵣ` inside the recursion.
    have hterm : ∀ r ∈ Finset.Iio s,
        ⁅(single i j 1 : Matrix (Fin n) (Fin n) K),
            ⁅(single s r 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t r⁆⁆ =
          ((if j = s then ⁅(single i r 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t r⁆
              else 0) -
            if r = i then ⁅(single s j 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t r⁆
              else 0) +
          if j = r then ⁅(single s r 1 : Matrix (Fin n) (Fin n) K), pieriVec mu v t i⁆
            else 0 := by
      intro r hr
      have hrs := Finset.mem_Iio.mp hr
      rw [leibniz_lie, Matrix.lie_single_single, ih r hrs hij, sub_lie]
      split_ifs <;> simp
    rw [pieriVec_of_gt hts, lie_smul, lie_sum, Finset.sum_congr rfl hterm,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases hjs : j = s
    · -- The coefficient at `i` collects `(μₜ + s - t - 1 - μₛ) • mᵢ`.
      subst hjs
      have hsum := sum_Iio_lie_single_pieriVec hv hmut hij fun r hr =>
        (ih r (Finset.mem_Ioo.mp hr).2 (Finset.mem_Ioo.mp hr).1).trans (ite_eq_left rfl)
      simp only [↓reduceIte]
      rw [ite_eq_left (Finset.mem_Iio.mpr hij), ite_eq_right Finset.notMem_Iio_self, add_zero,
        hsum, lie_single_self_pieriVec hv, ← sub_smul, smul_smul]
      convert one_smul K (pieriVec mu v t i) using 2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hts.ne',
        Pi.single_eq_of_ne hij.ne', sub_zero, add_zero]
      rw [inv_mul_eq_one₀ (pieriDenom_ne_zero hmut hts), pieriDenom]
      ring
    · -- Otherwise the two moved terms cancel or vanish.
      simp only [hjs, ↓reduceIte, Finset.sum_const_zero, zero_sub]
      by_cases hjs' : j < s
      · rw [ite_eq_left (Finset.mem_Iio.mpr (hij.trans hjs')),
          ite_eq_left (Finset.mem_Iio.mpr hjs'), neg_add_cancel, smul_zero]
      · have hsj : s < j := lt_of_le_of_ne (not_lt.mp hjs') (Ne.symm hjs)
        rw [ite_eq_right fun h => hjs' (Finset.mem_Iio.mp h), add_zero]
        by_cases his : i < s
        · rw [ite_eq_left (Finset.mem_Iio.mpr his), ih i his hsj, ite_eq_right hij.ne', neg_zero,
            smul_zero]
        · rw [ite_eq_right fun h => his (Finset.mem_Iio.mp h), neg_zero, smul_zero]

end Lowering

/-! ### The dual-standard Pieri rule -/

variable [CharZero K]

/-- **A highest weight vector of `V* ⊗ M` of weight `μ - εₜ`.** If `v` is a highest weight vector
of weight `μ` in a `gl n K`-module `M` and `μ - εₜ` is dominant, then `V* ⊗ M` has a highest weight
vector of weight `μ - εₜ`, namely `∑ₛ e*ₛ ⊗ mₛ` for the lowering vectors `mₛ` of `v`. -/
theorem exists_isGlHighestWeightVector_dual_tensorProduct {mu : Fin n → K} {v : M}
    (hv : IsGlHighestWeightVector mu v) {t : Fin n}
    (hmut : IsGlDominantIntegral (mu - Pi.single t 1)) :
    ∃ x : Module.Dual K (Fin n → K) ⊗[K] M, IsGlHighestWeightVector (mu - Pi.single t 1) x := by
  set x : Module.Dual K (Fin n → K) ⊗[K] M :=
    ∑ r, (Pi.basisFun K (Fin n)).dualBasis r ⊗ₜ pieriVec mu v t r with hx
  refine ⟨x, isGlHighestWeightVector_iff.mpr ⟨fun h0 => hv.ne_zero ?_, fun k => ?_,
    fun i j hij => ?_⟩⟩
  · rw [← pieriVec_self (mu := mu) (v := v) (t := t),
      ← dualStandardCoeff_sum_dualBasis_tmul (K := K) (pieriVec mu v t) t, ← hx, h0, map_zero]
  · refine ext_dualStandardCoeff fun r => ?_
    rw [dualStandardCoeff_lie_single, map_smul, hx, dualStandardCoeff_sum_dualBasis_tmul,
      dualStandardCoeff_sum_dualBasis_tmul, lie_single_self_pieriVec hv]
    split_ifs with hkr
    · subst hkr; simp [add_smul]
    · simp [Pi.single_eq_of_ne hkr]
  · refine ext_dualStandardCoeff fun r => ?_
    rw [dualStandardCoeff_lie_single, map_zero, hx, dualStandardCoeff_sum_dualBasis_tmul,
      dualStandardCoeff_sum_dualBasis_tmul, lie_single_pieriVec hv hmut r hij, sub_self]

/-- **The dual-standard Pieri rule for `gl n`.** Over an algebraically closed field of
characteristic zero, the tensor product of the dual standard module `V*` with the irreducible
module `L(μ)` of a dominant weight `μ` is the direct sum of the irreducible modules `L(μ - εₜ)`,
one for each index `t` such that `μ - εₜ` is still dominant. -/
theorem gl_dual_standard_pieri [IsAlgClosed K] (mu : Fin n → K) (hmu : IsGlDominantIntegral mu) :
    Nonempty (Module.Dual K (Fin n → K) ⊗[K] glIrreducible n mu
        ≃ₗ⁅K, Matrix (Fin n) (Fin n) K⁆
      ⨁ t : {t : Fin n // IsGlDominantIntegral (mu - Pi.single t 1)},
        glIrreducible n (mu - Pi.single (t : Fin n) 1)) := by
  let _ := isIrreducible_glIrreducible (K := K) hmu
  have hg := isGlHighestWeightVector_glIrreducibleGenerator (K := K) hmu
  let _ := complementedLattice_lieSubmodule_gl_of_forall_one_lie_eq_smul K (Fin n)
    (Module.Dual K (Fin n → K) ⊗[K] glIrreducible n mu)
    (one_lie_dual_tensorProduct (one_lie_glIrreducible_eq_smul hmu))
  refine nonempty_lieModuleEquiv_directSum_glIrreducible_of_forall_exists_eq_smul
    (lam := fun t : {t : Fin n // IsGlDominantIntegral (mu - Pi.single t 1)} =>
      mu - Pi.single (t : Fin n) 1) (fun s t hst => Subtype.ext ?_) (fun nu x hx hnu => ?_)
    (fun t => exists_isGlHighestWeightVector_dual_tensorProduct hg t.2)
    (fun t x y hx hy => exists_eq_smul_of_isGlHighestWeightVector_sub_single hg hx hy)
  · by_contra hne
    have h := congr_fun hst (s : Fin n)
    simp [Pi.single_eq_of_ne hne] at h
  · obtain ⟨t, rfl⟩ := exists_eq_sub_single_of_isGlHighestWeightVector_dual_tensorProduct hg hx
    exact ⟨⟨t, hnu⟩, rfl⟩

end TauCeti
