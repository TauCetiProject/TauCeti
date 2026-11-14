/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.Data.Set.PowersetCard
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume
public import TauCeti.NumberTheory.Height.Subspace.Basic

import TauCeti.Analysis.AbsoluteValue.LinearForms
import TauCeti.Analysis.ExteriorPower.Plucker
import TauCeti.LinearAlgebra.ExteriorPower.Hyperplane
import TauCeti.NumberTheory.Height.FundamentalInequality
import TauCeti.NumberTheory.Height.Primitive
import TauCeti.NumberTheory.Height.WedgeForms
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic

/-!
# Heights of hyperplane approximation spans and the exceptional subspace

Let `K` be a number field, `S₀` a finite set of finite places of `K`, `L` a family of linear forms
on `ι → K` linearly independent at every infinite place and every place of `S₀`, and `c` a family
of real exponents. At each level `Q`, `TauCeti.NumberField.approxSpan S₀ L c Q` is the subspace of
`ι → K` spanned by `TauCeti.NumberField.approxDomain S₀ L c Q`.

At every level `Q ≥ 1`, expressing each coordinate at a place in terms of the forms `L v` bounds
the Plücker coordinates of a domain basis of `approxSpan S₀ L c Q` at the infinite places and `S₀`,
while integrality outside `S₀` bounds all remaining finite places by `1`. Consequently, the
relative logarithmic height of `approxSpan S₀ L c Q` is bounded above linearly in `log Q`
(`TauCeti.NumberField.exists_forall_logHeight_approxSpan_le`).

When `approxWeight S₀ c ≤ -ε / 2` (`0 < ε`) and `approxSpan S₀ L c Q` is a hyperplane
(`finrank K (approxSpan S₀ L c Q) + 1 = Fintype.card ι`), a complementary lower bound holds outside
at most one fixed proper subspace `W₀` independent of `Q`
(`TauCeti.NumberField.exists_forall_logHeight_approxSpan`). Specifically, at each relevant place
`v`, choosing `k v` of maximal exponent `c v (k v)` among the indices `i` whose
`(Fintype.card ι - 1)`-wedge form omitting `i` does not vanish on the Plücker point of
`approxSpan S₀ L c Q` places any normal vector of `approxSpan S₀ L c Q` in the threshold subspace
`TauCeti.NumberField.thresholdSubspace S₀ L c k` (Evertse 1996, Lemma 27). Two cases arise:

* If some index choice `k` with `TauCeti.NumberField.weightAt S₀ c k < -ε / 4` has a nonzero vector
  `z₀ ∈ thresholdSubspace S₀ L c k`, the product formula forces `z₀ ⬝ᵥ x = 0` for all points `x`
  of `approxDomain S₀ L c Q` above a threshold level
  (`TauCeti.NumberField.exists_forall_mem_of_weightAt_lt`), so every hyperplane
  `approxSpan S₀ L c Q` above that threshold equals the single fixed hyperplane `W₀` orthogonal to
  `z₀`.
* Otherwise, every `k` arising from a hyperplane `approxSpan S₀ L c Q` satisfies
  `-ε / 4 ≤ weightAt S₀ c k`, and combining the local Liouville inequality for the nonvanishing
  wedge forms with the domain bounds over all `t = Fintype.card (InfinitePlace K) + S₀.card` places
  yields `ε * log Q / (4 * t) - C₅ ≤ (approxSpan S₀ L c Q).relativeSubspaceLogHeight`
  (`TauCeti.NumberField.exists_forall_le_logHeight_approxSpan`). Notice that `t` counts places
  without archimedean multiplicity because the projective height in the local Liouville inequality
  carries exponent `1` even at complex places.

In Diophantine approximation, the upper bound combines with Northcott's finiteness property at
bounded levels, while the lower bound outside `W₀` feeds Roth's lemma along a chain of growing
levels when proving the finiteness of hyperplane spans.

## Main definitions

* `TauCeti.NumberField.weightAt S₀ c k`: the weight of an exponent family `c` along a place-indexed
  choice `k : AbsoluteValue K ℝ → ι`, namely
  `∑ v : InfinitePlace K, v.mult * c v.1 (k v.1) + ∑ v ∈ S₀, c v.1 (k v.1)`.
* `TauCeti.NumberField.thresholdSubspace S₀ L c k`: the subspace of `ι → K` of vectors that, at
  every infinite place and every place of `S₀`, lie in the span of the coefficient vectors of the
  forms `L v i` with `c v i ≤ c v (k v)`.

## Main results

* `TauCeti.NumberField.exists_forall_one_le_mul_rpow_weightAt`: for any
  `z ∈ thresholdSubspace S₀ L c k`, some `M ≥ 1` satisfies `1 ≤ M * Q ^ weightAt S₀ c k` whenever
  `Q ≥ 1`, `x ∈ approxDomain S₀ L c Q`, and `z ⬝ᵥ x ≠ 0`.
* `TauCeti.NumberField.exists_forall_mem_of_weightAt_lt`: if `weightAt S₀ c k < -ε / 4` and
  `thresholdSubspace S₀ L c k ≠ ⊥`, a single proper subspace `W₀ ≠ ⊤` contains
  `approxDomain S₀ L c Q` for all `Q ≥ 1` with `C₄ / ε ≤ log Q`.
* `TauCeti.NumberField.exists_forall_logHeight_approxSpan_le` and
  `TauCeti.NumberField.exists_forall_logHeight_approxSpan_le_of_finrank_add_one`: upper bound on
  `(approxSpan S₀ L c Q).relativeSubspaceLogHeight` valid at every level `Q ≥ 1`.
* `TauCeti.NumberField.exists_forall_le_logHeight_approxSpan`: lower bound on
  `(approxSpan S₀ L c Q).relativeSubspaceLogHeight` for hyperplanes when no `k` with nontrivial
  `thresholdSubspace` has `weightAt S₀ c k < -ε / 4`.
* `TauCeti.NumberField.exists_forall_logHeight_approxSpan`: Bombieri–Gubler Lemma 7.5.21, giving a
  single proper subspace `W₀ ≠ ⊤` outside which every hyperplane `approxSpan S₀ L c Q` at large
  level satisfies both logarithmic height bounds.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 7.5.21.
* J.-H. Evertse, *An improvement of the quantitative Subspace Theorem*, Compos. Math. **101**
  (1996), Lemma 27.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute Subspace Theorem*,
  J. Reine Angew. Math. **548** (2002), Lemmas 12.3–12.4.
-/

public section

noncomputable section

open Height Matrix Module NumberField Set Set.powersetCard

namespace TauCeti.NumberField

/-! ### Weight along a placewise index choice -/

section WeightAt

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- **The weight of an exponent family along an index choice `k`**: the sum
`∑ v : InfinitePlace K, v.mult * c v.1 (k v.1) + ∑ v ∈ S₀, c v.1 (k v.1)` over the infinite places
and `S₀`. -/
def weightAt (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) : ℝ :=
  ∑ v : InfinitePlace K, (v.mult : ℝ) * c v.1 (k v.1) + ∑ v ∈ S₀, c v.1 (k v.1)

/-- Explicit sum formula for `weightAt`. -/
theorem weightAt_def (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) :
    weightAt S₀ c k =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * c v.1 (k v.1) + ∑ v ∈ S₀, c v.1 (k v.1) := by
  rfl

/-- The weight of the zero exponent family along any `k` is `0`. -/
@[simp]
theorem weightAt_zero (S₀ : Finset (FinitePlace K)) (k : AbsoluteValue K ℝ → ι) :
    weightAt S₀ (0 : AbsoluteValue K ℝ → ι → ℝ) k = 0 := by
  simp [weightAt]

/-- `weightAt S₀ c k` depends on `c` and `k` only at the infinite places and `S₀`. -/
theorem weightAt_congr {S₀ : Finset (FinitePlace K)} {c₁ c₂ : AbsoluteValue K ℝ → ι → ℝ}
    {k₁ k₂ : AbsoluteValue K ℝ → ι}
    (hInf : ∀ v : InfinitePlace K, c₁ v.1 (k₁ v.1) = c₂ v.1 (k₂ v.1))
    (hFin : ∀ v ∈ S₀, c₁ v.1 (k₁ v.1) = c₂ v.1 (k₂ v.1)) :
    weightAt S₀ c₁ k₁ = weightAt S₀ c₂ k₂ := by
  rw [weightAt, weightAt]
  congr 1
  · exact Finset.sum_congr rfl fun v _ ↦ by rw [hInf v]
  · exact Finset.sum_congr rfl fun v hv ↦ hFin v hv

/-- Over a finite index type, `weightAt S₀ c k` is at most the weighted sum of the local suprema
`⨆ i, c v i`. -/
theorem weightAt_le [Finite ι] (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) :
    weightAt S₀ c k ≤
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.1 i) + ∑ v ∈ S₀, ⨆ i, c v.1 i := by
  rw [weightAt]
  refine add_le_add ?_ ?_
  · gcongr with v
    exact Finite.le_ciSup_of_le (k v.1) le_rfl
  · gcongr with v
    exact Finite.le_ciSup_of_le (k v.1) le_rfl

/-- A positive level raised to `weightAt S₀ c k` splits as the product of the selected local
powers. -/
theorem rpow_weightAt (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) {Q : ℝ} (hQ : 0 < Q) :
    Q ^ weightAt S₀ c k =
      (∏ v : InfinitePlace K, (Q ^ c v.1 (k v.1)) ^ v.mult) *
        ∏ v ∈ S₀, Q ^ c v.1 (k v.1) := by
  rw [weightAt, Real.rpow_add hQ, Real.rpow_sum_of_pos hQ, Real.rpow_sum_of_pos hQ]
  congr 1
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [mul_comm, Real.rpow_mul hQ.le, Real.rpow_natCast]

/-- For `p + 1 = Fintype.card ι` and `0 < Q`, `Q ^ (approxWeight S₀ c - weightAt S₀ c k)` equals
the product of the local bounds over the `p`-subsets `omitOne hm (k v)` omitting `k v`. -/
theorem rpow_approxWeight_sub_weightAt [DecidableEq ι] [Fintype ι] {p : ℕ}
    (hm : p + 1 = Fintype.card ι) (S₀ : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) {Q : ℝ} (hQ : 0 < Q) :
    Q ^ (approxWeight S₀ c - weightAt S₀ c k) =
      (∏ v : InfinitePlace K,
          (∏ j ∈ (omitOne hm (k v.1) : Finset ι), Q ^ c v.1 j) ^ v.mult) *
        ∏ v ∈ S₀, ∏ j ∈ (omitOne hm (k v.1) : Finset ι), Q ^ c v.1 j := by
  have herase (v : AbsoluteValue K ℝ) :
      ∑ i, c v i - c v (k v) = ∑ j ∈ Finset.univ.erase (k v), c v j :=
    (Finset.sum_erase_eq_sub (Finset.mem_univ (k v))).symm
  have hsub : approxWeight S₀ c - weightAt S₀ c k =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (∑ j ∈ Finset.univ.erase (k v.1), c v.1 j) +
        ∑ v ∈ S₀, ∑ j ∈ Finset.univ.erase (k v.1), c v.1 j := by
    rw [approxWeight_def, weightAt_def]
    simp_rw [← herase, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsub, Real.rpow_add hQ, Real.rpow_sum_of_pos hQ, Real.rpow_sum_of_pos hQ]
  congr 1
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [mul_comm, Real.rpow_mul hQ.le, Real.rpow_natCast, Real.rpow_sum_of_pos hQ, coe_omitOne]
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [Real.rpow_sum_of_pos hQ, coe_omitOne]

end WeightAt

/-! ### The threshold subspace and the exceptional hyperplane -/

section ThresholdSubspace

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [DecidableEq ι]

/-- **The threshold subspace** associated to a placewise index choice `k` (Evertse 1996, Lemma 27):
the vectors in `ι → K` that, at every infinite place `v` and every `v ∈ S₀`, belong to the span of
the coefficient vectors of the forms `L v i` with `c v i ≤ c v (k v)`. -/
def thresholdSubspace (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) : Submodule K (ι → K) :=
  (⨅ v : InfinitePlace K,
      Submodule.span K ((fun i j ↦ L v.1 i (Pi.single j 1)) '' {i | c v.1 i ≤ c v.1 (k v.1)})) ⊓
    ⨅ v ∈ S₀,
      Submodule.span K ((fun i j ↦ L v.1 i (Pi.single j 1)) '' {i | c v.1 i ≤ c v.1 (k v.1)})

/-- Explicit intersection formula for `thresholdSubspace`. -/
theorem thresholdSubspace_def (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    (k : AbsoluteValue K ℝ → ι) :
    thresholdSubspace S₀ L c k =
      (⨅ v : InfinitePlace K,
          Submodule.span K
            ((fun i j ↦ L v.1 i (Pi.single j 1)) '' {i | c v.1 i ≤ c v.1 (k v.1)})) ⊓
        ⨅ v ∈ S₀,
          Submodule.span K
            ((fun i j ↦ L v.1 i (Pi.single j 1)) '' {i | c v.1 i ≤ c v.1 (k v.1)}) := by
  rfl

/-- Membership in `thresholdSubspace` unfolded place by place. -/
theorem mem_thresholdSubspace_iff {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {k : AbsoluteValue K ℝ → ι} {z : ι → K} :
    z ∈ thresholdSubspace S₀ L c k ↔
      (∀ v : InfinitePlace K, z ∈ Submodule.span K
        ((fun i j ↦ L v.1 i (Pi.single j 1)) '' {i | c v.1 i ≤ c v.1 (k v.1)})) ∧
      ∀ v ∈ S₀, z ∈ Submodule.span K
        ((fun i j ↦ L v.1 i (Pi.single j 1)) '' {i | c v.1 i ≤ c v.1 (k v.1)}) := by
  simp [thresholdSubspace]

/-- **Product-formula bound on threshold pairings.** For any `z ∈ thresholdSubspace S₀ L c k`, some
constant `M ≥ 1` independent of `Q` satisfies `1 ≤ M * Q ^ weightAt S₀ c k` whenever `Q ≥ 1`,
`x ∈ approxDomain S₀ L c Q`, and `z ⬝ᵥ x ≠ 0`. -/
theorem exists_forall_one_le_mul_rpow_weightAt [Fintype ι] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {k : AbsoluteValue K ℝ → ι} {z : ι → K} (hz : z ∈ thresholdSubspace S₀ L c k) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ⦃Q : ℝ⦄, 1 ≤ Q → ∀ x ∈ approxDomain S₀ L c Q,
      z ⬝ᵥ x ≠ 0 → 1 ≤ M * Q ^ weightAt S₀ c k := by
  obtain ⟨d, hd0, hd_int⟩ := NumberField.exists_smul_apply_le_one z
  have hdz : d • z ∈ thresholdSubspace S₀ L c k := Submodule.smul_mem _ d hz
  obtain ⟨hdz_inf, hdz_fin⟩ := mem_thresholdSubspace_iff.mp hdz
  choose Binf hBinf1 hBinf using fun v : InfinitePlace K ↦
    v.1.exists_one_le_forall_dotProduct_le_mul_rpow (L v.1) (c v.1) (c v.1 (k v.1)) (hdz_inf v)
  have hfin_ex (v : FinitePlace K) : ∃ B : ℝ, 1 ≤ B ∧ (v ∈ S₀ → ∀ ⦃Q : ℝ⦄, 1 ≤ Q →
      ∀ ⦃x : ι → K⦄, (∀ i, v (L v.1 i x) ≤ Q ^ c v.1 i) →
        v ((d • z) ⬝ᵥ x) ≤ B * Q ^ c v.1 (k v.1)) := by
    by_cases hv : v ∈ S₀
    · obtain ⟨B, hB1, hB⟩ := v.1.exists_one_le_forall_dotProduct_le_mul_rpow (L v.1) (c v.1)
        (c v.1 (k v.1)) (hdz_fin v hv)
      exact ⟨B, hB1, fun _ ↦ hB⟩
    · exact ⟨1, le_rfl, fun h ↦ (hv h).elim⟩
  choose Bfin hBfin1 hBfin using hfin_ex
  refine ⟨(∏ v : InfinitePlace K, Binf v ^ v.mult) * ∏ v ∈ S₀, Bfin v,
    one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun v _ ↦ one_le_pow₀ (hBinf1 v))
      (Finset.one_le_prod₀ fun v _ ↦ hBfin1 v),
    fun Q hQ x hx hzx ↦ ?_⟩
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  obtain ⟨hx_inf, hx_fin, hx_out⟩ := mem_approxDomain.mp hx
  have hdzx : (d • z) ⬝ᵥ x ≠ 0 := by simpa [smul_dotProduct] using mul_ne_zero hd0 hzx
  have hprod := NumberField.one_le_prod_apply_of_forall_le_one S₀ hdzx fun v hv ↦
    v.1.apply_dotProduct_le_one_of_isNonarchimedean v.add_le (hd_int v) (hx_out v hv)
  refine hprod.trans ?_
  calc (∏ v : InfinitePlace K, v ((d • z) ⬝ᵥ x) ^ v.mult) * ∏ v ∈ S₀, v ((d • z) ⬝ᵥ x)
      ≤ (∏ v : InfinitePlace K, (Binf v * Q ^ c v.1 (k v.1)) ^ v.mult) *
          ∏ v ∈ S₀, Bfin v * Q ^ c v.1 (k v.1) := by
        refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _)
          (Finset.prod_nonneg fun v _ ↦ pow_nonneg
            (mul_nonneg (zero_le_one.trans (hBinf1 v)) (by positivity)) _)
        · gcongr with v
          exact hBinf v hQ (hx_inf v)
        · gcongr with v hv
          exact hBfin v hv hQ (hx_fin v hv)
    _ = ((∏ v : InfinitePlace K, Binf v ^ v.mult) * ∏ v ∈ S₀, Bfin v) * Q ^ weightAt S₀ c k := by
        simp only [mul_pow, Finset.prod_mul_distrib, rpow_weightAt S₀ c k hQ0]
        ring

/-- **Uniqueness of the exceptional subspace** (Evertse 1996, Lemma 27): if some index choice `k`
with `weightAt S₀ c k < -ε / 4` (`0 < ε`) has a nontrivial `thresholdSubspace S₀ L c k`, then a
single proper subspace `W₀ ≠ ⊤` of `ι → K` and a threshold constant `C₄ > 0` satisfy
`x ∈ W₀` for every `Q ≥ 1` with `C₄ / ε ≤ Real.log Q` and every `x ∈ approxDomain S₀ L c Q`. -/
theorem exists_forall_mem_of_weightAt_lt [Finite ι] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {c : AbsoluteValue K ℝ → ι → ℝ}
    {k : AbsoluteValue K ℝ → ι} {ε : ℝ} (hε : 0 < ε) (hk : weightAt S₀ c k < -ε / 4)
    (ht : thresholdSubspace S₀ L c k ≠ ⊥) :
    ∃ (W₀ : Submodule K (ι → K)) (C₄ : ℝ), W₀ ≠ ⊤ ∧ 0 < C₄ ∧
      ∀ ⦃Q : ℝ⦄, 1 ≤ Q → C₄ / ε ≤ Real.log Q →
        ∀ ⦃x : ι → K⦄, x ∈ approxDomain S₀ L c Q → x ∈ W₀ := by
  cases nonempty_fintype ι
  obtain ⟨z₀, hz₀_mem, hz₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
  obtain ⟨M, hM1, hM⟩ := exists_forall_one_le_mul_rpow_weightAt hz₀_mem
  let W₀ : Submodule K (ι → K) := LinearMap.ker (dotProductBilin K K z₀)
  have hW₀ : W₀ ≠ ⊤ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hz₀
    intro htop
    have hmem : (Pi.single j 1 : ι → K) ∈ W₀ := htop ▸ Submodule.mem_top
    exact hj (by simpa [W₀] using hmem)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  refine ⟨W₀, 4 * (Real.log M + 1), hW₀, by positivity, fun Q hQ hlogQ x hx ↦ ?_⟩
  by_contra hxW₀
  have hzx : z₀ ⬝ᵥ x ≠ 0 := by simpa [W₀] using hxW₀
  have h1 : 1 ≤ M * Q ^ weightAt S₀ c k := hM hQ x hx hzx
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hM0 : 0 < M := zero_lt_one.trans_le hM1
  have hlt : M * Q ^ weightAt S₀ c k < 1 := by
    calc M * Q ^ weightAt S₀ c k
        ≤ M * Q ^ (-ε / 4) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ hk.le) hM0.le
      _ = Real.exp (Real.log M + Real.log Q * (-ε / 4)) := by
          rw [Real.rpow_def_of_pos hQ0, Real.exp_add, Real.exp_log hM0]
      _ < 1 := by
          rw [Real.exp_lt_one_iff]
          have := (div_le_iff₀ hε).mp hlogQ
          linarith
  linarith

end ThresholdSubspace

/-! ### Upper bound on the height of `approxSpan` -/

section UpperBound

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [LinearOrder ι]

/-- Uniform multiplicative height upper bound on the Plücker coordinates of any linearly
independent family drawn from `approxDomain S₀ L c Q` (`Q ≥ 1`). -/
private theorem exists_one_le_forall_mulHeight_plucker_le [Finite ι] [Nonempty ι]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) ⦃Q : ℝ⦄, 1 ≤ Q →
      ∀ {p : ℕ} {x : Fin p → ι → K},
        LinearIndependent K x → (∀ r, x r ∈ approxDomain S₀ L c Q) →
        mulHeight (plucker x) ≤
          C * Q ^ ((p : ℝ) *
            (∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.1 i) +
              ∑ v ∈ S₀, ⨆ i, c v.1 i)) := by
  choose A hA1 hA using fun v : InfinitePlace K ↦
    v.1.exists_one_le_forall_iSup_plucker_le (hLinf v)
  have hfin_ex (v : FinitePlace K) : ∃ B : ℝ, 1 ≤ B ∧ (v ∈ S₀ →
      ∀ (e : ι → ℝ) ⦃Q : ℝ⦄, 1 ≤ Q → ∀ {p : ℕ} {x : Fin p → ι → K},
        (∀ r i, v (L v.1 i (x r)) ≤ Q ^ e i) →
          ⨆ s, v (plucker x s) ≤ B * Q ^ ((p : ℝ) * ⨆ i, e i)) := by
    by_cases hv : v ∈ S₀
    · obtain ⟨B, hB1, hB⟩ := v.1.exists_one_le_forall_iSup_plucker_le (hLfin v hv)
      exact ⟨B, hB1, fun _ ↦ hB⟩
    · exact ⟨1, le_rfl, fun h ↦ (hv h).elim⟩
  choose B hB1 hB using hfin_ex
  refine ⟨(∏ v : InfinitePlace K, A v ^ v.mult) * ∏ v ∈ S₀, B v,
    one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun v _ ↦ one_le_pow₀ (hA1 v))
      (Finset.one_le_prod₀ fun v _ ↦ hB1 v),
    fun c Q hQ p x hx hxr ↦ ?_⟩
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hw : plucker x ≠ 0 := (plucker_ne_zero_iff x).mpr hx
  -- Outside `S₀`, nonarchimedean integrality bounds every Plücker coordinate by `1`.
  have hout (v : FinitePlace K) (hv : v ∉ S₀) (s : powersetCard ι p) : v (plucker x s) ≤ 1 :=
    (v.1.plucker_le_prod_iSup v.add_le x s).trans <|
      Finset.prod_le_one₀ (fun _ _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) fun r _ ↦
        ciSup_le fun j ↦ (mem_approxDomain.mp (hxr r)).2.2 v hv j
  -- Multiply the local bounds over the infinite places and `S₀`.
  refine (NumberField.mulHeight_le_prod_of_forall_le_one S₀ hw hout).trans ?_
  calc (∏ v : InfinitePlace K, (⨆ s, v (plucker x s)) ^ v.mult) *
        ∏ v ∈ S₀, ⨆ s, v (plucker x s)
      ≤ (∏ v : InfinitePlace K, (A v * Q ^ ((p : ℝ) * ⨆ i, c v.1 i)) ^ v.mult) *
          ∏ v ∈ S₀, B v * Q ^ ((p : ℝ) * ⨆ i, c v.1 i) := by
        refine mul_le_mul ?_ ?_
          (Finset.prod_nonneg fun _ _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
          (Finset.prod_nonneg fun v _ ↦ pow_nonneg
            (mul_nonneg (zero_le_one.trans (hA1 v)) (by positivity)) _)
        · exact Finset.prod_le_prod₀
            (fun _ _ ↦ pow_nonneg (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) _) fun v _ ↦
            pow_le_pow_left₀ (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
              (hA v (c v.1) hQ fun r i ↦ (mem_approxDomain.mp (hxr r)).1 v i) v.mult
        · exact Finset.prod_le_prod₀
            (fun _ _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) fun v hv ↦
            hB v hv (c v.1) hQ fun r i ↦ (mem_approxDomain.mp (hxr r)).2.1 v hv i
    _ = ((∏ v : InfinitePlace K, A v ^ v.mult) * ∏ v ∈ S₀, B v) *
          Q ^ ((p : ℝ) *
            (∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.1 i) +
              ∑ v ∈ S₀, ⨆ i, c v.1 i)) := by
        simp only [mul_pow, Finset.prod_mul_distrib, mul_add, Finset.mul_sum, Real.rpow_add hQ0,
          Real.rpow_sum_of_pos hQ0]
        have hpow (v : InfinitePlace K) :
            (Q ^ ((p : ℝ) * ⨆ i, c v.1 i)) ^ v.mult =
              Q ^ ((p : ℝ) * ((v.mult : ℝ) * ⨆ i, c v.1 i)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
          ring_nf
        simp only [hpow]
        ring

/-- **Upper bound on the height of `approxSpan`** at every level `Q ≥ 1`: there exists `C₆ ≥ 0`
(independent of `Q`) such that `(approxSpan S₀ L c Q).relativeSubspaceLogHeight` is bounded by
`finrank K (approxSpan S₀ L c Q)` times the weighted sum of local maximum exponents times `log Q`,
plus `C₆`. -/
theorem exists_forall_logHeight_approxSpan_le [Finite ι] [Nonempty ι]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧ ∀ ⦃Q : ℝ⦄, 1 ≤ Q →
      (approxSpan S₀ L c Q).relativeSubspaceLogHeight ≤
        (finrank K (approxSpan S₀ L c Q) : ℝ) *
          (∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.1 i) +
            ∑ v ∈ S₀, ⨆ i, c v.1 i) * Real.log Q + C₆ := by
  cases nonempty_fintype ι
  obtain ⟨C, hC1, hC⟩ := exists_one_le_forall_mulHeight_plucker_le hLinf hLfin
  refine ⟨Real.log C, Real.log_nonneg hC1, fun Q hQ ↦ ?_⟩
  obtain ⟨x, hxr, hx_span, hx_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (approxDomain S₀ L c Q)
  have hV_eq : Submodule.span K (Set.range x) = approxSpan S₀ L c Q :=
    hx_span.trans (approxSpan_eq_span S₀ L c Q).symm
  have hmul := hC c hQ hx_li hxr
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  rw [← hV_eq, Submodule.relativeSubspaceLogHeight_span_range hx_li, logHeight_eq_log_mulHeight,
    hx_span]
  refine (Real.log_le_log (mulHeight_pos _) hmul).trans_eq ?_
  rw [Real.log_mul hC0.ne' (Real.rpow_pos_of_pos hQ0 _).ne', Real.log_rpow hQ0]
  ring

/-- Hyperplane specialization of `exists_forall_logHeight_approxSpan_le`: at every level `Q ≥ 1`
where `approxSpan S₀ L c Q` has codimension one, its relative logarithmic height is bounded by
`Fintype.card ι - 1` times the weighted sum of local maximum exponents times `log Q`, plus `C₆`. -/
theorem exists_forall_logHeight_approxSpan_le_of_finrank_add_one [Fintype ι] [Nonempty ι]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧ ∀ ⦃Q : ℝ⦄, 1 ≤ Q →
      finrank K (approxSpan S₀ L c Q) + 1 = Fintype.card ι →
      (approxSpan S₀ L c Q).relativeSubspaceLogHeight ≤
        ((Fintype.card ι - 1 : ℕ) : ℝ) *
          (∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.1 i) +
            ∑ v ∈ S₀, ⨆ i, c v.1 i) * Real.log Q + C₆ := by
  obtain ⟨C₆, hC₆, h⟩ := exists_forall_logHeight_approxSpan_le hLinf hLfin c
  refine ⟨C₆, hC₆, fun Q hQ hdim ↦ ?_⟩
  have hcard : finrank K (approxSpan S₀ L c Q) = Fintype.card ι - 1 := by omega
  simpa only [hcard] using h hQ

end UpperBound

/-! ### Lower bound outside the exceptional subspace -/

section LowerBound

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- Choosing at each place `v` the index `k v` of largest exponent `c v i` among those `i` where
`wedgeForms (L v) p (omitOne hm i) (plucker x) ≠ 0` places any orthogonal vector `a` in
`thresholdSubspace S₀ L c k`. -/
private theorem exists_pattern_max [Nonempty ι] {p : ℕ} (hm : p + 1 = Fintype.card ι)
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {x : Fin p → ι → K} (hx : LinearIndependent K x)
    {a : ι → K} (hxa : ∀ r, x r ⬝ᵥ a = 0) :
    ∃ k : AbsoluteValue K ℝ → ι, a ∈ thresholdSubspace S₀ L c k ∧
      (∀ v : InfinitePlace K, wedgeForms (L v.1) p (omitOne hm (k v.1)) (plucker x) ≠ 0) ∧
      ∀ v ∈ S₀, wedgeForms (L v.1) p (omitOne hm (k v.1)) (plucker x) ≠ 0 := by
  classical
  have hw : plucker x ≠ 0 := (plucker_ne_zero_iff x).mpr hx
  have hex (v : AbsoluteValue K ℝ) :
      ∃ i : ι, LinearIndependent K (L v) →
        wedgeForms (L v) p (omitOne hm i) (plucker x) ≠ 0 ∧
        (∀ j, wedgeForms (L v) p (omitOne hm j) (plucker x) ≠ 0 → c v j ≤ c v i) := by
    by_cases hLv : LinearIndependent K (L v)
    · let P : Finset ι :=
        Finset.univ.filter fun j ↦ wedgeForms (L v) p (omitOne hm j) (plucker x) ≠ 0
      obtain ⟨j₀, hj₀⟩ := exists_wedgeForms_omitOne_ne_zero hm hLv hw
      have hPne : P.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
      obtain ⟨i, hiP, himax⟩ := P.exists_max_image (c v) hPne
      exact ⟨i, fun _ ↦ ⟨(Finset.mem_filter.mp hiP).2,
        fun j hj ↦ himax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩⟩
    · exact ⟨Classical.arbitrary ι, fun h ↦ (hLv h).elim⟩
  choose k hk using hex
  refine ⟨k, mem_thresholdSubspace_iff.mpr ⟨fun v ↦ ?_, fun v hv ↦ ?_⟩,
    fun v ↦ (hk v.1 (hLinf v)).1, fun v hv ↦ (hk v.1 (hLfin v hv)).1⟩
  · exact Submodule.span_mono (Set.image_mono fun j hj ↦ (hk v.1 (hLinf v)).2 j hj)
      (mem_span_of_forall_dotProduct_eq_zero hm (hLinf v) hx hxa)
  · exact Submodule.span_mono (Set.image_mono fun j hj ↦ (hk v.1 (hLfin v hv)).2 j hj)
      (mem_span_of_forall_dotProduct_eq_zero hm (hLfin v hv) hx hxa)

/-- Uniform multiplicative height comparison over all infinite places and `S₀` for the Plücker
point of `p` linearly independent points in `approxDomain S₀ L c Q` (`p + 1 = Fintype.card ι`). -/
private theorem exists_one_le_forall_one_le_mul_mulHeight_plucker_pow [Nonempty ι] {p : ℕ}
    (hm : p + 1 = Fintype.card ι) {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (k : AbsoluteValue K ℝ → ι)
      ⦃Q : ℝ⦄, 1 ≤ Q → ∀ {x : Fin p → ι → K},
        LinearIndependent K x → (∀ r, x r ∈ approxDomain S₀ L c Q) →
        (∀ v : InfinitePlace K, wedgeForms (L v.1) p (omitOne hm (k v.1)) (plucker x) ≠ 0) →
        (∀ v ∈ S₀, wedgeForms (L v.1) p (omitOne hm (k v.1)) (plucker x) ≠ 0) →
        1 ≤ C * mulHeight (plucker x) ^ (Fintype.card (InfinitePlace K) + S₀.card) *
          Q ^ (approxWeight S₀ c - weightAt S₀ c k) := by
  choose Ainf hAinf1 hAinf using fun v : InfinitePlace K ↦
    v.exists_one_le_forall_iSup_plucker_pow_mult_le (hLinf v) p
  have hfin_ex (v : FinitePlace K) : ∃ B : ℝ, 1 ≤ B ∧ (v ∈ S₀ →
      ∀ {x : Fin p → ι → K} (T : powersetCard ι p) {b : ι → ℝ},
        wedgeForms (L v.1) p T (plucker x) ≠ 0 →
        (∀ r, ∀ j ∈ T, v (L v.1 j (x r)) ≤ b j) →
        ⨆ s, v (plucker x s) ≤
          B * mulHeight (plucker x) * ∏ j ∈ (T : Finset ι), b j) := by
    by_cases hv : v ∈ S₀
    · obtain ⟨B, hB1, hB⟩ := v.exists_one_le_forall_iSup_plucker_le (hLfin v hv) p
      exact ⟨B, hB1, fun _ ↦ hB⟩
    · exact ⟨1, le_rfl, fun h ↦ (hv h).elim⟩
  choose Bfin hBfin1 hBfin using hfin_ex
  let C : ℝ := (∏ v : InfinitePlace K, Ainf v) * ∏ v ∈ S₀, Bfin v
  have hC1 : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (Finset.one_le_prod₀ fun v _ ↦ hAinf1 v) (Finset.one_le_prod₀ fun v _ ↦ hBfin1 v)
  refine ⟨C, hC1, fun c k Q hQ x hx_li hxr hkinf hkfin ↦ ?_⟩
  let w := plucker x
  have hw : w ≠ 0 := (plucker_ne_zero_iff x).mpr hx_li
  -- Outside `S₀`, every Plücker coordinate has `v`-adic norm at most `1`.
  have hout (v : FinitePlace K) (hv : v ∉ S₀) (s : powersetCard ι p) : v (w s) ≤ 1 :=
    (v.1.plucker_le_prod_iSup v.add_le x s).trans <|
      Finset.prod_le_one₀ (fun _ _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) fun r _ ↦
        ciSup_le fun j ↦ (mem_approxDomain.mp (hxr r)).2.2 v hv j
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  -- Combine `1 ≤ mulHeight w` with the local Liouville-and-domain bounds across all places.
  calc (1 : ℝ)
      ≤ mulHeight w := one_le_mulHeight w
    _ ≤ (∏ v : InfinitePlace K, (⨆ s, v (w s)) ^ v.mult) * ∏ v ∈ S₀, ⨆ s, v (w s) :=
        NumberField.mulHeight_le_prod_of_forall_le_one S₀ hw hout
    _ ≤ (∏ v : InfinitePlace K, Ainf v * mulHeight w *
            (∏ j ∈ (omitOne hm (k v.1) : Finset ι), Q ^ c v.1 j) ^ v.mult) *
        ∏ v ∈ S₀, Bfin v * mulHeight w *
          ∏ j ∈ (omitOne hm (k v.1) : Finset ι), Q ^ c v.1 j := by
        refine mul_le_mul ?_ ?_
          (Finset.prod_nonneg fun _ _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
          (Finset.prod_nonneg fun v _ ↦ mul_nonneg
            (mul_nonneg (zero_le_one.trans (hAinf1 v)) (mulHeight_pos w).le)
            (pow_nonneg (Finset.prod_nonneg fun _ _ ↦ by positivity) _))
        · exact Finset.prod_le_prod₀
            (fun _ _ ↦ pow_nonneg (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) _) fun v _ ↦
            hAinf v (omitOne hm (k v.1)) (hkinf v) fun r j _ ↦ (mem_approxDomain.mp (hxr r)).1 v j
        · exact Finset.prod_le_prod₀
            (fun _ _ ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _) fun v hv ↦
            hBfin v hv (omitOne hm (k v.1)) (hkfin v hv)
              fun r j _ ↦ (mem_approxDomain.mp (hxr r)).2.1 v hv j
    _ = C * mulHeight w ^ (Fintype.card (InfinitePlace K) + S₀.card) *
          Q ^ (approxWeight S₀ c - weightAt S₀ c k) := by
        simp only [C, pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          rpow_approxWeight_sub_weightAt hm S₀ c k hQ0]
        ring

/-- **Lower bound on the height of a hyperplane `approxSpan`** when no index choice `k` with
nontrivial `thresholdSubspace S₀ L c k` has `weightAt S₀ c k < -ε / 4`: there exists `C₅ ≥ 0`
(independent of `Q`) such that at every level `Q ≥ 1` where `approxSpan S₀ L c Q` is a hyperplane,
its relative logarithmic height is at least
`ε * Real.log Q / (4 * (Fintype.card (InfinitePlace K) + S₀.card : ℝ)) - C₅`. -/
theorem exists_forall_le_logHeight_approxSpan [Nonempty ι]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    {c : AbsoluteValue K ℝ → ι → ℝ} {ε : ℝ} (hc : approxWeight S₀ c ≤ -ε / 2)
    (hno : ∀ k : AbsoluteValue K ℝ → ι, thresholdSubspace S₀ L c k ≠ ⊥ →
      -ε / 4 ≤ weightAt S₀ c k) :
    ∃ C₅ : ℝ, 0 ≤ C₅ ∧ ∀ ⦃Q : ℝ⦄, 1 ≤ Q →
      finrank K (approxSpan S₀ L c Q) + 1 = Fintype.card ι →
      ε * Real.log Q / (4 * (Fintype.card (InfinitePlace K) + S₀.card : ℝ)) - C₅ ≤
        (approxSpan S₀ L c Q).relativeSubspaceLogHeight := by
  let p := Fintype.card ι - 1
  have hm : p + 1 = Fintype.card ι := Nat.sub_add_cancel Fintype.card_pos
  obtain ⟨C, hC1, hC⟩ := exists_one_le_forall_one_le_mul_mulHeight_plucker_pow hm hLinf hLfin
  let tNat : ℕ := Fintype.card (InfinitePlace K) + S₀.card
  let t : ℝ := (Fintype.card (InfinitePlace K) : ℝ) + S₀.card
  have ht_eq : (tNat : ℝ) = t := Nat.cast_add _ _
  have ht_pos : 0 < t := ht_eq ▸ by exact_mod_cast Nat.add_pos_left Fintype.card_pos S₀.card
  refine ⟨Real.log C / t, div_nonneg (Real.log_nonneg hC1) ht_pos.le, fun Q hQ hdim ↦ ?_⟩
  obtain ⟨y, hyr, hy_span, hy_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (approxDomain S₀ L c Q)
  have hdim_span : finrank K ↥(Submodule.span K (approxDomain S₀ L c Q)) + 1 = Fintype.card ι := by
    rwa [← approxSpan_eq_span]
  have hfp : finrank K ↥(Submodule.span K (approxDomain S₀ L c Q)) = p := by omega
  let x : Fin p → ι → K := y ∘ Fin.cast hfp.symm
  have hxr (r : Fin p) : x r ∈ approxDomain S₀ L c Q := hyr (Fin.cast hfp.symm r)
  have hx_li : LinearIndependent K x := hy_li.comp _ (Fin.cast_injective _)
  have hx_span : Submodule.span K (Set.range x) = approxSpan S₀ L c Q := by
    have hrange : Set.range x = Set.range y := (Fin.castOrderIso hfp.symm).surjective.range_comp y
    rw [hrange, hy_span, approxSpan_eq_span]
  obtain ⟨a, ha, hVa, -⟩ := Submodule.exists_normal hdim
  have hxa (r : Fin p) : x r ⬝ᵥ a = 0 :=
    (hVa (x r)).mp (hx_span ▸ Submodule.subset_span ⟨r, rfl⟩)
  obtain ⟨k, ha_mem, hkinf, hkfin⟩ := exists_pattern_max hm hLinf hLfin c hx_li hxa
  have hwk : -ε / 4 ≤ weightAt S₀ c k :=
    hno k fun hbot ↦ ha ((Submodule.mem_bot K).mp (hbot ▸ ha_mem))
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have h1 : 1 ≤ C * mulHeight (plucker x) ^ tNat * Q ^ (-ε / 4) :=
    (hC c k hQ hx_li hxr hkinf hkfin).trans <| mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))
      (mul_nonneg (zero_le_one.trans hC1) (pow_nonneg (mulHeight_pos _).le _))
  have hlog : 0 ≤ Real.log C + t * logHeight (plucker x) + -ε / 4 * Real.log Q := by
    have hC0 : 0 < C := zero_lt_one.trans_le hC1
    have hHt : 0 < mulHeight (plucker x) ^ tNat := pow_pos (mulHeight_pos _) _
    have hlog1 := Real.log_nonneg h1
    rwa [Real.log_mul (mul_ne_zero hC0.ne' hHt.ne') (Real.rpow_pos_of_pos hQ0 _).ne',
      Real.log_mul hC0.ne' hHt.ne', Real.log_pow, ht_eq, ← logHeight_eq_log_mulHeight,
      Real.log_rpow hQ0] at hlog1
  have hdiv_eq : ε * Real.log Q / (4 * t) - Real.log C / t =
      (ε * Real.log Q / 4 - Real.log C) / t := by
    rw [sub_div, div_div]
  rw [← hx_span, Submodule.relativeSubspaceLogHeight_span_range hx_li, hdiv_eq, div_le_iff₀ ht_pos]
  linarith

/-- **Heights of hyperplane approximation spans and the exceptional subspace**
(Bombieri–Gubler, Lemma 7.5.21; Evertse–Schlickewei 2002, Lemmas 12.3–12.4): for forms `L`
linearly independent at every infinite place and every `v ∈ S₀` and exponents `c` with
`approxWeight S₀ c ≤ -ε / 2` (`0 < ε`), there exist a proper subspace `W₀ ≠ ⊤` of `ι → K` and
constants `C₄ > 0`, `C₅ ≥ 0`, `C₆ ≥ 0` independent of `Q` such that at every level `Q ≥ 1` with
`C₄ / ε ≤ Real.log Q` where `approxSpan S₀ L c Q` is a hyperplane, either
`approxSpan S₀ L c Q = W₀` or `(approxSpan S₀ L c Q).relativeSubspaceLogHeight` lies between
`ε * Real.log Q / (4 * (Fintype.card (InfinitePlace K) + S₀.card : ℝ)) - C₅` and
`(Fintype.card ι - 1) * (∑ v, v.mult * ⨆ i, c v.1 i + ∑ v ∈ S₀, ⨆ i, c v.1 i) * Real.log Q + C₆`. -/
theorem exists_forall_logHeight_approxSpan [Nonempty ι]
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hc : approxWeight S₀ c ≤ -ε / 2) :
    ∃ (W₀ : Submodule K (ι → K)) (C₄ C₅ C₆ : ℝ),
      W₀ ≠ ⊤ ∧ 0 < C₄ ∧ 0 ≤ C₅ ∧ 0 ≤ C₆ ∧
      ∀ ⦃Q : ℝ⦄, 1 ≤ Q → C₄ / ε ≤ Real.log Q →
        finrank K (approxSpan S₀ L c Q) + 1 = Fintype.card ι →
        approxSpan S₀ L c Q = W₀ ∨
          (ε * Real.log Q / (4 * (Fintype.card (InfinitePlace K) + S₀.card : ℝ)) - C₅ ≤
              (approxSpan S₀ L c Q).relativeSubspaceLogHeight ∧
            (approxSpan S₀ L c Q).relativeSubspaceLogHeight ≤
              ((Fintype.card ι - 1 : ℕ) : ℝ) *
                (∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.1 i) +
                  ∑ v ∈ S₀, ⨆ i, c v.1 i) * Real.log Q + C₆) := by
  obtain ⟨C₆, hC₆, hup⟩ := exists_forall_logHeight_approxSpan_le_of_finrank_add_one hLinf hLfin c
  by_cases hexc : ∃ k : AbsoluteValue K ℝ → ι,
      weightAt S₀ c k < -ε / 4 ∧ thresholdSubspace S₀ L c k ≠ ⊥
  · obtain ⟨k₀, hk₀, ht₀⟩ := hexc
    obtain ⟨W₀, C₄, hW₀, hC₄, hmem⟩ := exists_forall_mem_of_weightAt_lt hε hk₀ ht₀
    refine ⟨W₀, C₄, 0, C₆, hW₀, hC₄, le_rfl, hC₆, fun Q hQ hlogQ hdim ↦ Or.inl ?_⟩
    have hle : approxSpan S₀ L c Q ≤ W₀ := approxSpan_le_iff.mpr (hmem hQ hlogQ)
    have hlt : finrank K W₀ < Fintype.card ι := by
      simpa [Module.finrank_fintype_fun_eq_card K] using Submodule.finrank_lt hW₀
    have hge : finrank K (approxSpan S₀ L c Q) ≤ finrank K W₀ := Submodule.finrank_mono hle
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  · have hno : ∀ k : AbsoluteValue K ℝ → ι, thresholdSubspace S₀ L c k ≠ ⊥ →
        -ε / 4 ≤ weightAt S₀ c k :=
      fun k ht ↦ le_of_not_gt fun hlt ↦ hexc ⟨k, hlt, ht⟩
    obtain ⟨C₅, hC₅, hlow⟩ := exists_forall_le_logHeight_approxSpan hLinf hLfin hc hno
    have hbot : (⊥ : Submodule K (ι → K)) ≠ ⊤ := by
      let i₀ : ι := Classical.arbitrary ι
      intro h
      have hmem : (Pi.single i₀ (1 : K) : ι → K) ∈ (⊥ : Submodule K (ι → K)) :=
        h ▸ Submodule.mem_top
      simp at hmem
    exact ⟨⊥, 1, C₅, C₆, hbot, zero_lt_one, hC₅, hC₆,
      fun Q hQ _ hdim ↦ Or.inr ⟨hlow hQ hdim, hup hQ hdim⟩⟩

end LowerBound

/-! ### Counterexamples -/

/-- **A single form value on a Plücker representative is not bounded by the subspace height.**
Over `ℚ`, for every positive natural number `N`, the vector `w = ![(N : ℚ), 0]` spans a line of
relative height `1`, while its first coordinate `LinearMap.proj 0 w = N` has scalar height `N`.
Thus no constant `C` can bound `mulHeight₁ (l w)` by `C * (ℚ ∙ w).relativeSubspaceHeight` across
all spanning representatives `w`; the proof of `exists_forall_le_logHeight_approxSpan` uses the
scale-invariant local Liouville inequality instead. -/
example (N : ℕ) (hN : 1 ≤ N) :
    let w : Fin 2 → ℚ := ![(N : ℚ), 0]
    (ℚ ∙ w).relativeSubspaceHeight = 1 ∧
      mulHeight₁ (LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0 w) = N := by
  intro w
  have : NeZero N := ⟨by omega⟩
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine ⟨?_, ?_⟩
  · rw [Submodule.relativeSubspaceHeight_span_singleton]
    have hw : w = (N : ℚ) • ![(1 : ℚ), 0] := by
      ext i
      fin_cases i <;> simp [w]
    rw [hw, mulHeight_smul_eq_mulHeight _ hN0]
    have hswap : mulHeight ![(1 : ℚ), 0] = mulHeight (![(1 : ℚ), 0] ∘ Equiv.swap 0 1) :=
      (mulHeight_comp_equiv (Equiv.swap 0 1) _).symm
    have h01 : (![(1 : ℚ), 0] ∘ Equiv.swap 0 1) = ![(0 : ℚ), 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hswap, h01, ← mulHeight₁_eq_mulHeight, mulHeight₁_zero]
  · simpa [w] using Rat.mulHeight₁_natCast N

/-- **Without the exceptional subspace `W₀`, the lower bound of `exists_forall_logHeight_approxSpan`
is false.** Over `ℚ` in two variables with `S₀ = ∅`, coordinate forms `L _ = LinearMap.proj`, and
exponents `c _ = ![-1, 0]`, the total weight is `approxWeight ∅ c = -1 ≤ -1 / 2`, yet at every
level `Q > 1` the span `approxSpan ∅ L c Q` is the fixed hyperplane `ℚ ∙ ![0, 1]` of relative
logarithmic height `0`, which violates any positive-slope lower bound `ε * log Q / 4 - C₅` for
large `Q`. -/
example :
    let L : AbsoluteValue ℚ ℝ → Fin 2 → Dual ℚ (Fin 2 → ℚ) := fun _ ↦ LinearMap.proj
    let c : AbsoluteValue ℚ ℝ → Fin 2 → ℝ := fun _ ↦ ![-1, 0]
    approxWeight ∅ c ≤ -(1 : ℝ) / 2 ∧
      ∀ ⦃Q : ℝ⦄, 1 < Q →
        finrank ℚ (approxSpan ∅ L c Q) + 1 = Fintype.card (Fin 2) ∧
        (approxSpan ∅ L c Q).relativeSubspaceLogHeight = 0 := by
  intro L c
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    have := NumberField.totalWeight_eq_sum_mult (K := ℚ)
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Fintype.sum_unique] at this
    exact this.symm
  refine ⟨?_, fun Q hQ ↦ ?_⟩
  · rw [approxWeight_def, Fintype.sum_unique, Finset.sum_empty, hmult]
    norm_num [c, Fin.sum_univ_two]
  · have hQ0 : 0 < Q := zero_lt_one.trans hQ
    have heq : approxSpan ∅ L c Q = ℚ ∙ ![(0 : ℚ), 1] := by
      refine le_antisymm (approxSpan_le_iff.mpr fun x hx ↦ ?_) ?_
      · obtain ⟨hinf, -, hout⟩ := mem_approxDomain.mp hx
        have hx0 : x 0 = 0 := by
          by_contra hx0
          have h1 := NumberField.one_le_prod_apply_of_forall_le_one (Sfin := ∅) hx0
            fun v _ ↦ hout v (by simp) 0
          rw [Finset.prod_empty, mul_one, Fintype.prod_unique, hmult, pow_one] at h1
          have h2 : (default : InfinitePlace ℚ) (x 0) ≤ Q ^ (-1 : ℝ) := by
            simpa [L, c] using hinf default 0
          have h3 : Q ^ (-1 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hQ (by norm_num)
          linarith
        rw [SetLike.mem_coe, Submodule.mem_span_singleton]
        refine ⟨x 1, ?_⟩
        ext i
        fin_cases i <;> simp [hx0]
      · rw [Submodule.span_singleton_le_iff_mem]
        apply mem_approxSpan_of_mem
        refine mem_approxDomain.mpr ⟨fun v i ↦ ?_, by simp, fun v _ j ↦ ?_⟩
        · fin_cases i
          · simpa [L, c] using (Real.rpow_pos_of_pos hQ0 (-1)).le
          · simp [L, c, Rat.infinitePlace_apply]
        · fin_cases j <;> simp
    have hne : (![(0 : ℚ), 1] : Fin 2 → ℚ) ≠ 0 := fun h ↦ by simpa using congrFun h 1
    refine ⟨?_, ?_⟩
    · rw [heq, finrank_span_singleton hne, Fintype.card_fin]
    · rw [heq, Submodule.relativeSubspaceLogHeight_span_singleton, logHeight_eq_log_mulHeight,
        ← mulHeight₁_eq_mulHeight, mulHeight₁_zero, Real.log_one]

end TauCeti.NumberField
