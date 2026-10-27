/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage

/-!
# Polynomial coefficients in an analytic stage

At level `h`, the coefficient vectors vanishing above degree `k` form the submodule
`polynomialSubmodule S k`. When `p^h ≠ 0`, restricting to the indices
`ZMod (p^h) × Fin (k+1)` identifies it isometrically with the finite product of coefficient
modules, and degree truncations converge in norm. Degree truncation is always a contractive
projection onto this submodule, and the union over all degrees is dense.

For coefficients in a complete ultrametric `ℤ_p`-module, these vectors evaluate on each
disc to a polynomial in the normalized coordinate `w = (x-a)/p^h`. The polynomial on a
disc uses Mathlib's `PolynomialModule`; its monomials are `w^j`, without extra powers of
`p^h`. The evaluated functions form `locallyPolynomialSubmodule S k`, the image under
analytic-stage evaluation. The coefficient model is kept distinct from this image:
no injectivity of evaluation is assumed.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti.AnalyticStage

variable {p h k : ℕ} {E : Type*} [NormedAddCommGroup E]

section Coefficients

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]

/-- The additive subgroup of coefficient vectors vanishing above degree `k`. -/
def polynomialAddSubgroup (k : ℕ) : AddSubgroup (AnalyticStage p h E) where
  carrier := {c | ∀ a n, k < n → c (a, n) = 0}
  zero_mem' := by simp
  add_mem' hc hd a n hn := by simp [hc a n hn, hd a n hn]
  neg_mem' hc a n hn := by simp [hc a n hn]

/-- Membership in the additive polynomial coefficient subgroup is vanishing in higher degrees. -/
@[simp]
theorem mem_polynomialAddSubgroup (c : AnalyticStage p h E) :
    c ∈ polynomialAddSubgroup k ↔ ∀ a n, k < n → c (a, n) = 0 := Iff.rfl

/-- Coefficient vectors of discwise polynomials of degree at most `k` in the normalized
disc coordinate. -/
def polynomialSubmodule (k : ℕ) : Submodule S (AnalyticStage p h E) where
  __ := (polynomialAddSubgroup (p := p) (h := h) (E := E) k).toAddSubmonoid
  smul_mem' s c hc a n hn := by simp [hc a n hn]

/-- Polynomial coefficients inherit the native normed group structure from their additive
subgroup, including when the commuting scalars form only a semiring. -/
noncomputable instance instSeminormedAddCommGroupPolynomialSubmodule :
    SeminormedAddCommGroup (polynomialSubmodule (p := p) (h := h) (E := E) S k) :=
  inferInstanceAs <| SeminormedAddCommGroup (polynomialAddSubgroup (p := p) (h := h) (E := E) k)

/-- The inherited polynomial coefficient seminorm separates coefficient vectors. -/
noncomputable instance instNormedAddCommGroupPolynomialSubmodule :
    NormedAddCommGroup (polynomialSubmodule (p := p) (h := h) (E := E) S k) :=
  { instSeminormedAddCommGroupPolynomialSubmodule S with
    eq_of_dist_eq_zero := fun hxy ↦ Subtype.ext (eq_of_dist_eq_zero hxy) }

/-- The polynomial submodule carries the restriction of the analytic-stage Gauss norm. -/
@[simp, norm_cast]
theorem norm_coe_polynomialSubmodule
    (c : polynomialSubmodule (p := p) (h := h) (E := E) S k) :
    ‖(c : AnalyticStage p h E)‖ = ‖c‖ := (rfl)

/-- A coefficient vector has degree at most `k` precisely when its higher coefficients vanish. -/
@[simp]
theorem mem_polynomialSubmodule (c : AnalyticStage p h E) :
    c ∈ polynomialSubmodule S k ↔ ∀ a n, k < n → c (a, n) = 0 := Iff.rfl

/-- Increasing the degree bound enlarges the polynomial coefficient submodule. -/
theorem polynomialSubmodule_mono {l : ℕ} (hkl : k ≤ l) :
    polynomialSubmodule (p := p) (h := h) (E := E) S k ≤ polynomialSubmodule S l :=
  fun _ hc a n hn ↦ hc a n (hkl.trans_lt hn)

/-- A normalized disc monomial of degree at most `k` is a polynomial coefficient vector. -/
theorem single_mem_polynomialSubmodule (a : ZMod (p ^ h)) {n : ℕ} (hn : n ≤ k) (e : E) :
    ZeroAtInftyContinuousMap.single (a, n) e ∈ polynomialSubmodule S k := by
  intro b m hm
  apply ZeroAtInftyContinuousMap.single_eq_of_ne
  intro heq
  have hmn : m = n := congrArg Prod.snd heq
  exact hm.not_ge (hmn.symm ▸ hn)

/-- Truncation of every disc expansion after degree `k`. -/
noncomputable def polynomialTruncation (k : ℕ) : AnalyticStage p h E →L[S] AnalyticStage p h E :=
  ZeroAtInftyContinuousMap.indicatorCLM S {i | i.2 ≤ k}

/-- Truncation keeps exactly the coefficients of degree at most `k`. -/
@[simp]
theorem polynomialTruncation_apply (c : AnalyticStage p h E) (i : ZMod (p ^ h) × ℕ) :
    polynomialTruncation S k c i = if i.2 ≤ k then c i else 0 := by
  simp only [polynomialTruncation, ZeroAtInftyContinuousMap.coe_indicatorCLM,
    Set.indicator_apply, Set.mem_ofPred_eq]

/-- Truncation takes values in the polynomial coefficient submodule. -/
theorem polynomialTruncation_mem (c : AnalyticStage p h E) :
    polynomialTruncation S k c ∈ polynomialSubmodule S k := by
  intro a n hn
  simp only [polynomialTruncation_apply, not_le_of_gt hn, ite_false]

/-- A vector is fixed by degree truncation exactly when its degree is at most `k`. -/
@[simp]
theorem polynomialTruncation_eq_self_iff (c : AnalyticStage p h E) :
    polynomialTruncation S k c = c ↔ c ∈ polynomialSubmodule S k := by
  constructor
  · intro hc
    exact hc ▸ polynomialTruncation_mem S c
  · intro hc
    ext ⟨a, n⟩
    rw [polynomialTruncation_apply]
    split_ifs with hn
    · rfl
    · exact (hc a n (lt_of_not_ge hn)).symm

/-- Applying the same degree truncation twice has the same effect as applying it once. -/
@[simp]
theorem polynomialTruncation_idem (c : AnalyticStage p h E) :
    polynomialTruncation S k (polynomialTruncation S k c) = polynomialTruncation S k c :=
  (polynomialTruncation_eq_self_iff S _).mpr (polynomialTruncation_mem S c)

/-- Degree truncation does not increase the Gauss norm. -/
theorem norm_polynomialTruncation_le (c : AnalyticStage p h E) :
    ‖polynomialTruncation S k c‖ ≤ ‖c‖ :=
  ZeroAtInftyContinuousMap.norm_indicatorCLM_apply_le _ _

end Coefficients

section FiniteProduct

variable [NeZero (p ^ h)]

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]

private noncomputable def ofPolynomialCoeffs (v : ZMod (p ^ h) × Fin (k + 1) → E) :
    AnalyticStage p h E :=
  ZeroAtInftyContinuousMap.mkOfDiscrete
    (fun i ↦ if hi : i.2 ≤ k then v (i.1, ⟨i.2, Nat.lt_succ_of_le hi⟩) else 0) <| by
      have hfin : {i : ZMod (p ^ h) × ℕ | i.2 ≤ k}.Finite :=
        (Set.finite_univ.prod (Set.finite_Iic k)).subset fun i hi ↦ by simpa using hi
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hfin.compl_mem_cofinite] with i hi
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hi
      simp [hi]

private theorem ofPolynomialCoeffs_apply (v : ZMod (p ^ h) × Fin (k + 1) → E)
    (i : ZMod (p ^ h) × ℕ) :
    ofPolynomialCoeffs v i =
      if hi : i.2 ≤ k then v (i.1, ⟨i.2, Nat.lt_succ_of_le hi⟩) else 0 :=
  congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _) i

/-- Polynomial coefficient vectors are the finite product with one coordinate for each disc
and each degree `0, …, k`. The product has its native maximum norm. -/
noncomputable def polynomialEquiv (k : ℕ) :
    polynomialSubmodule (p := p) (h := h) (E := E) S k ≃ₗᵢ[S]
      (ZMod (p ^ h) × Fin (k + 1) → E) where
  toFun c i := c.val (i.1, i.2)
  invFun v := ⟨ofPolynomialCoeffs v, by
    intro a n hn
    simp only [ofPolynomialCoeffs_apply, not_le_of_gt hn, dite_false]⟩
  left_inv c := by
    apply Subtype.ext
    ext ⟨a, n⟩
    rw [ofPolynomialCoeffs_apply]
    split_ifs with hn
    · rfl
    · exact (c.property a n (lt_of_not_ge hn)).symm
  right_inv v := by
    funext ⟨a, n⟩
    simp only [ofPolynomialCoeffs_apply, Nat.le_of_lt_succ n.isLt, dite_true]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' c := by
    rw [← norm_coe_polynomialSubmodule]
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg c.val)).mpr fun i ↦
        c.val.norm_coe_le_norm (i.1, i.2)
    · refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg _)).mpr ?_
      rintro ⟨a, n⟩
      by_cases hi : n ≤ k
      · exact norm_le_pi_norm (fun j : ZMod (p ^ h) × Fin (k + 1) ↦ c.val (j.1, j.2))
          (a, ⟨n, Nat.lt_succ_of_le hi⟩)
      · rw [c.property a n (lt_of_not_ge hi), norm_zero]
        exact norm_nonneg _

/-- The finite-product comparison reads the corresponding coefficient. -/
@[simp]
theorem polynomialEquiv_apply (c : polynomialSubmodule (p := p) (h := h) (E := E) S k)
    (i : ZMod (p ^ h) × Fin (k + 1)) :
    polynomialEquiv (p := p) (h := h) (E := E) S k c i = c.val (i.1, i.2) := (rfl)

/-- The inverse finite-product comparison extends the coefficients by zero. -/
@[simp]
theorem polynomialEquiv_symm_apply (v : ZMod (p ^ h) × Fin (k + 1) → E)
    (i : ZMod (p ^ h) × ℕ) :
    ((polynomialEquiv (p := p) (h := h) (E := E) S k).symm v).val i =
      if hi : i.2 ≤ k then v (i.1, ⟨i.2, Nat.lt_succ_of_le hi⟩) else 0 :=
  ofPolynomialCoeffs_apply v i

end FiniteProduct

section Approximation

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]

/-- Degree truncations converge in the Gauss norm to the original analytic coefficient vector. -/
theorem tendsto_polynomialTruncation [NeZero (p ^ h)] (c : AnalyticStage p h E) :
    Tendsto (fun k ↦ polynomialTruncation S k c) atTop (𝓝 c) := by
  let u (k : ℕ) : Finset (ZMod (p ^ h) × ℕ) := Finset.univ ×ˢ Finset.range (k + 1)
  have hu : Tendsto u atTop atTop := by
    refine tendsto_atTop.2 fun s ↦ ?_
    refine eventually_atTop.2 ⟨s.sup Prod.snd, fun k hk ↦ ?_⟩
    intro i hi
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr <|
      Nat.lt_succ_of_le ((Finset.le_sup (f := Prod.snd) hi).trans hk)⟩
  have hset (k : ℕ) : {i : ZMod (p ^ h) × ℕ | i.2 ≤ k} = (u k : Set _) := by
    ext i
    simp [u]
  simpa only [polynomialTruncation, hset, ZeroAtInftyContinuousMap.indicatorCLM_finset_apply,
    Function.comp_def]
    using (ZeroAtInftyContinuousMap.hasSum_single c).comp hu

/-- Discwise polynomial coefficient vectors are dense in every analytic stage. -/
theorem dense_iUnion_polynomialSubmodule :
    Dense (⋃ k, (polynomialSubmodule (p := p) (h := h) (E := E) S k :
      Set (AnalyticStage p h E))) := by
  refine ZeroAtInftyContinuousMap.dense_setOf_finite_support.mono fun c hc ↦ ?_
  obtain ⟨k, hk⟩ := (hc.image Prod.snd).bddAbove
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  intro a n hn
  by_contra hne
  have hm : (a, n) ∈ Function.support c := hne
  exact hn.not_ge (hk (Set.mem_image_of_mem Prod.snd hm))

end Approximation

section Evaluation

variable [hp : Fact p.Prime]

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [Module ℤ_[p] E]

/-- The polynomial module element giving the expansion of a polynomial vector on one disc. -/
noncomputable def discPolynomial (c : polynomialSubmodule (p := p) (h := h) (E := E) S k)
    (a : ZMod (p ^ h)) : PolynomialModule ℤ_[p] E :=
  PolynomialModule.ofCoeff ℤ_[p] <| Finsupp.ofSupportFinite (fun n ↦ c.val (a, n)) <|
    (Set.finite_Iic k).subset fun n hn ↦ by
      by_contra hnk
      exact hn (c.property a n (lt_of_not_ge hnk))

/-- The polynomial on a disc has exactly the coefficients of the stage vector. -/
@[simp]
theorem discPolynomial_coeff (c : polynomialSubmodule (p := p) (h := h) (E := E) S k)
    (a : ZMod (p ^ h)) (n : ℕ) : (discPolynomial S c a).coeff n = c.val (a, n) := (rfl)

variable [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
  [SMulCommClass ℤ_[p] S E]

/-- A polynomial coefficient vector evaluates on each disc as a finite sum in the normalized
disc coordinate. -/
theorem eval_polynomial_natCast_val_add_mul
    (c : polynomialSubmodule (p := p) (h := h) (E := E) S k) (a : ZMod (p ^ h)) (w : ℤ_[p]) :
    eval S c.val ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) =
      ∑ n ∈ Finset.range (k + 1), w ^ n • c.val (a, n) := by
  rw [eval_natCast_val_add_mul]
  exact tsum_eq_sum fun n hn ↦ by
    rw [c.property a n (by simpa using hn), smul_zero]

/-- The finite disc expansion is evaluation of Mathlib's native polynomial module element. -/
theorem eval_eq_discPolynomial
    (c : polynomialSubmodule (p := p) (h := h) (E := E) S k) (a : ZMod (p ^ h)) (w : ℤ_[p]) :
    eval S c.val ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) =
      PolynomialModule.eval w (discPolynomial S c a) := by
  rw [eval_polynomial_natCast_val_add_mul, PolynomialModule.eval_apply]
  symm
  apply Finsupp.sum_of_support_subset
  · intro n hn
    by_contra hnk
    exact Finsupp.mem_support_iff.mp hn <| by
      rw [discPolynomial_coeff, c.property a n (by simpa using hnk)]
  · intro n hn
    exact smul_zero _

/-- Continuous functions represented by degree-at-most-`k` polynomials in the normalized
coordinate on every level-`h` disc. This is the image of the coefficient submodule. -/
noncomputable def locallyPolynomialSubmodule (k : ℕ) : Submodule S C(ℤ_[p], E) :=
  (polynomialSubmodule (p := p) (h := h) (E := E) S k).map (eval S).toLinearMap

/-- Membership in the locally polynomial function submodule means having polynomial
coefficient data, without a uniqueness assertion. -/
@[simp]
theorem mem_locallyPolynomialSubmodule (f : C(ℤ_[p], E)) :
    f ∈ locallyPolynomialSubmodule (p := p) (h := h) S k ↔
      ∃ c ∈ polynomialSubmodule (p := p) (h := h) (E := E) S k, eval S c = f :=
  Submodule.mem_map

end Evaluation

end TauCeti.AnalyticStage
