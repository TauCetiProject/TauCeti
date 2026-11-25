/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import TauCeti.Topology.Algebra.InfiniteSum.ConvolutionRing
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Algebra.Order.GroupWithZero.Pow

/-!
# Laurent convergence and Gauss norms

For a two-sided coefficient family `a : ℤ → R`, convergence at a radius `ρ` means that
`‖a n‖ * ρ ^ n` tends to zero along the cofinite filter. The Gauss norm is the supremum of these
weighted norms. At positive radii, convergence at the two endpoints implies convergence on the
whole interval, and the two endpoint Gauss norms bound every intermediate Gauss norm.

Over a complete ultrametric ring, convolution preserves convergence at each positive radius.
The convolution estimate also applies to bounded weighted coefficients without decay, as used
at radius one for the Amice ring.

## References

* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), §2.3.
* M. Lazard, *Les zéros des fonctions analytiques d'une variable sur un corps valué complet*,
  Publ. Math. IHÉS 14 (1962), §2.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti

variable {R : Type*}

/-! ### Convergence and the Gauss norm at one radius -/

section Norm

variable [Norm R]

/-- The Laurent series `∑_{n ∈ ℤ} aₙ tⁿ` with coefficients `a` satisfies the convergence condition
on the circle `|t| = ρ`: the weighted coefficient norms `‖aₙ‖ ρⁿ` tend to zero as `|n| → ∞`. -/
def LaurentConvergesAt (ρ : ℝ) (a : ℤ → R) : Prop :=
  Tendsto (fun n ↦ ‖a n‖ * ρ ^ n) cofinite (𝓝 0)

theorem laurentConvergesAt_iff {ρ : ℝ} {a : ℤ → R} :
    LaurentConvergesAt ρ a ↔ Tendsto (fun n ↦ ‖a n‖ * ρ ^ n) cofinite (𝓝 0) :=
  (Iff.rfl)

/-- The Gauss norm `|a|_ρ = sup_n ‖aₙ‖ ρⁿ` of a coefficient family at the radius `ρ`. It is the
Gauss norm of the Laurent series `∑ aₙ tⁿ` on the circle `|t| = ρ` when the series converges
there (`TauCeti.LaurentConvergesAt`). Without convergence the value need not be the Gauss norm of
a convergent series; it is the junk value `0` when the weighted norms are unbounded. -/
noncomputable def laurentGaussNorm (ρ : ℝ) (a : ℤ → R) : ℝ :=
  ⨆ n, ‖a n‖ * ρ ^ n

theorem laurentGaussNorm_def (ρ : ℝ) (a : ℤ → R) : laurentGaussNorm ρ a = ⨆ n, ‖a n‖ * ρ ^ n :=
  (rfl)

/-- The weighted coefficient norms of a family converging at `ρ` are bounded above. -/
theorem LaurentConvergesAt.bddAbove {ρ : ℝ} {a : ℤ → R} (ha : LaurentConvergesAt ρ a) :
    BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n) :=
  ha.isBoundedUnder_le.bddAbove_range_of_cofinite

/-- Every weighted coefficient norm of a family whose weighted norms are bounded above is at most
its Gauss norm. A family converging at `ρ` has such a bound by
`TauCeti.LaurentConvergesAt.bddAbove`. -/
theorem le_laurentGaussNorm {ρ : ℝ} {a : ℤ → R}
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n)) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ laurentGaussNorm ρ a :=
  le_ciSup ha n

/-- The Gauss norm is at most every common bound of the weighted coefficient norms. -/
theorem laurentGaussNorm_le {ρ C : ℝ} {a : ℤ → R} (h : ∀ n, ‖a n‖ * ρ ^ n ≤ C) :
    laurentGaussNorm ρ a ≤ C :=
  ciSup_le h

/-- For a family whose weighted norms are bounded above, the Gauss norm is the least common bound
of the weighted coefficient norms. -/
theorem laurentGaussNorm_le_iff {ρ C : ℝ} {a : ℤ → R}
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n)) :
    laurentGaussNorm ρ a ≤ C ↔ ∀ n, ‖a n‖ * ρ ^ n ≤ C :=
  ⟨fun h n ↦ (le_laurentGaussNorm ha n).trans h, laurentGaussNorm_le⟩

end Norm

section SeminormedAddGroup

variable [SeminormedAddGroup R]

/-- Convergence at two positive radii is equivalent to decay with their maximum weight. -/
theorem laurentConvergesAt_endpoints_iff {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {a : ℤ → R} :
    LaurentConvergesAt α a ∧ LaurentConvergesAt β a ↔
      Tendsto (fun n ↦ ‖a n‖ * max (α ^ n) (β ^ n)) cofinite (𝓝 0) := by
  constructor
  · rintro ⟨ha, hb⟩
    simp_rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
    simpa only [max_self] using (laurentConvergesAt_iff.mp ha).max (laurentConvergesAt_iff.mp hb)
  · intro hab
    exact ⟨squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos hα n).le)
      (fun _ ↦ mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)) hab,
      squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos hβ n).le)
        (fun _ ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)) hab⟩

/-- Endpoint convergence implies convergence at every intermediate radius. -/
theorem LaurentConvergesAt.of_endpoints {α ρ β : ℝ}
    (hα : 0 < α) (hαρ : α ≤ ρ) (hρβ : ρ ≤ β) {a : ℤ → R}
    (ha : LaurentConvergesAt α a) (hb : LaurentConvergesAt β a) : LaurentConvergesAt ρ a := by
  have hmax := (laurentConvergesAt_endpoints_iff hα (hα.trans_le (hαρ.trans hρβ))).mp ⟨ha, hb⟩
  exact squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (zpow_pos (hα.trans_le hαρ) n).le)
    (fun n ↦ mul_le_mul_of_nonneg_left (zpow_le_max_endpoints hα hαρ hρβ n) (norm_nonneg _)) hmax

/-- Every intermediate Gauss norm is bounded by the maximum of the endpoint Gauss norms. -/
theorem laurentGaussNorm_le_max_endpoints {α ρ β : ℝ}
    (hα : 0 < α) (hαρ : α ≤ ρ) (hρβ : ρ ≤ β) {a : ℤ → R}
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * α ^ n))
    (hb : BddAbove (Set.range fun n ↦ ‖a n‖ * β ^ n)) :
    laurentGaussNorm ρ a ≤ max (laurentGaussNorm α a) (laurentGaussNorm β a) := by
  refine laurentGaussNorm_le fun n ↦ ?_
  calc ‖a n‖ * ρ ^ n ≤ ‖a n‖ * max (α ^ n) (β ^ n) :=
        mul_le_mul_of_nonneg_left (zpow_le_max_endpoints hα hαρ hρβ n) (norm_nonneg _)
    _ = max (‖a n‖ * α ^ n) (‖a n‖ * β ^ n) := mul_max_of_nonneg _ _ (norm_nonneg _)
    _ ≤ _ := max_le_max (le_laurentGaussNorm ha n) (le_laurentGaussNorm hb n)

/-- The Gauss norm is nonnegative at every radius, including where the weighted norms are unbounded
and the supremum takes the junk value `0`. -/
theorem laurentGaussNorm_nonneg (ρ : ℝ) (a : ℤ → R) : 0 ≤ laurentGaussNorm ρ a := by
  by_cases h : BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n)
  · exact le_ciSup_of_le h 0 (by simp)
  · rw [laurentGaussNorm, Real.iSup_of_not_bddAbove h]

@[simp]
theorem laurentGaussNorm_neg (ρ : ℝ) (a : ℤ → R) :
    laurentGaussNorm ρ (-a) = laurentGaussNorm ρ a := by
  simp [laurentGaussNorm]

@[simp]
theorem laurentConvergesAt_zero (ρ : ℝ) : LaurentConvergesAt ρ (0 : ℤ → R) := by
  simp [LaurentConvergesAt]

@[simp]
theorem laurentGaussNorm_zero (ρ : ℝ) : laurentGaussNorm ρ (0 : ℤ → R) = 0 := by
  simp [laurentGaussNorm]

/-- A family supported in one degree converges at every radius. -/
theorem laurentConvergesAt_single (ρ : ℝ) (n : ℤ) (c : R) :
    LaurentConvergesAt ρ (Pi.single n c) :=
  tendsto_const_nhds.congr' <| (eventually_cofinite_ne n).mono fun m hm ↦ by
    simp [Pi.single_eq_of_ne hm]

/-- The Gauss norm of the monomial `c tⁿ` at a radius `ρ ≥ 0` is `‖c‖ ρⁿ`. -/
@[simp]
theorem laurentGaussNorm_single {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℤ) (c : R) :
    laurentGaussNorm ρ (Pi.single n c) = ‖c‖ * ρ ^ n := by
  refine le_antisymm (laurentGaussNorm_le fun m ↦ ?_) ?_
  · rcases eq_or_ne m n with rfl | hm
    · simp
    · simpa [Pi.single_eq_of_ne hm] using mul_nonneg (norm_nonneg c) (zpow_nonneg hρ n)
  · simpa using le_laurentGaussNorm (laurentConvergesAt_single ρ n c).bddAbove n

theorem LaurentConvergesAt.add {ρ : ℝ} {a b : ℤ → R} (ha : LaurentConvergesAt ρ a)
    (hb : LaurentConvergesAt ρ b) : LaurentConvergesAt ρ (a + b) := by
  have h : Tendsto (fun n ↦ ‖‖a n‖ * ρ ^ n‖ + ‖‖b n‖ * ρ ^ n‖) cofinite (𝓝 0) := by
    simpa using (Tendsto.norm ha).add (Tendsto.norm hb)
  refine squeeze_zero_norm (f := fun n ↦ ‖(a + b) n‖ * ρ ^ n) (fun n ↦ ?_) h
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_norm, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le (a n) (b n)) (abs_nonneg (ρ ^ n))

theorem LaurentConvergesAt.neg {ρ : ℝ} {a : ℤ → R} (ha : LaurentConvergesAt ρ a) :
    LaurentConvergesAt ρ (-a) := by
  simpa [LaurentConvergesAt] using ha

theorem LaurentConvergesAt.sub {ρ : ℝ} {a b : ℤ → R} (ha : LaurentConvergesAt ρ a)
    (hb : LaurentConvergesAt ρ b) : LaurentConvergesAt ρ (a - b) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

/-- In an ultrametric group the Gauss norm of a sum is at most the larger Gauss norm. -/
theorem laurentGaussNorm_add_le [IsUltrametricDist R] {ρ : ℝ} (hρ : 0 ≤ ρ) {a b : ℤ → R}
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n))
    (hb : BddAbove (Set.range fun n ↦ ‖b n‖ * ρ ^ n)) :
    laurentGaussNorm ρ (a + b) ≤ max (laurentGaussNorm ρ a) (laurentGaussNorm ρ b) :=
  laurentGaussNorm_le fun n ↦
    (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (zpow_nonneg hρ n)).trans <|
      by rw [max_mul_of_nonneg _ _ (zpow_nonneg hρ n)]
         exact max_le_max (le_laurentGaussNorm ha n) (le_laurentGaussNorm hb n)

/-- The coefficients of a Laurent series converging on a circle of radius `0 < ρ ≤ 1` tend to zero
at `-∞`: for `n ≤ 0` they satisfy `‖aₙ‖ ≤ ‖aₙ‖ ρⁿ`. -/
theorem LaurentConvergesAt.tendsto_atBot {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) {a : ℤ → R}
    (ha : LaurentConvergesAt ρ a) : Tendsto a atBot (𝓝 0) := by
  refine squeeze_zero_norm' ?_ ((laurentConvergesAt_iff.1 ha).mono_left
    (le_sup_left.trans_eq Int.cofinite_eq.symm))
  filter_upwards [eventually_le_atBot 0] with n hn
  simpa using mul_le_mul_of_nonneg_left (one_le_zpow_of_nonpos₀ hρ₀ hρ₁ hn) (norm_nonneg (a n))

end SeminormedAddGroup

theorem LaurentConvergesAt.smul [SeminormedRing R] {ρ : ℝ} {a : ℤ → R}
    (ha : LaurentConvergesAt ρ a) (c : R) : LaurentConvergesAt ρ (c • a) := by
  have h : Tendsto (fun n ↦ ‖c‖ * ‖‖a n‖ * ρ ^ n‖) cofinite (𝓝 0) := by
    simpa using (Tendsto.norm ha).const_mul ‖c‖
  refine squeeze_zero_norm (f := fun n ↦ ‖(c • a) n‖ * ρ ^ n) (fun n ↦ ?_) h
  simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_norm, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_mul_le c (a n)) (abs_nonneg (ρ ^ n))

/-- The Gauss norm of `c • a` at a radius `ρ ≥ 0` is at most `‖c‖ |a|_ρ`. -/
theorem laurentGaussNorm_smul_le [SeminormedRing R] {ρ : ℝ} (hρ : 0 ≤ ρ) {a : ℤ → R}
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n)) (c : R) :
    laurentGaussNorm ρ (c • a) ≤ ‖c‖ * laurentGaussNorm ρ a :=
  laurentGaussNorm_le fun n ↦ by
    calc ‖(c • a) n‖ * ρ ^ n ≤ ‖c‖ * (‖a n‖ * ρ ^ n) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (norm_mul_le c (a n)) (zpow_nonneg hρ n)
      _ ≤ ‖c‖ * laurentGaussNorm ρ a :=
          mul_le_mul_of_nonneg_left (le_laurentGaussNorm ha n) (norm_nonneg c)

/-! ### Convolution at one radius -/

section Convolution

variable [SeminormedRing R] {ρ : ℝ} {a b c : ℤ → R}

/-- A term of a product coefficient is bounded by the product of the weighted norms of its
factors: `‖aᵢ bⱼ‖ ρⁱ⁺ʲ ≤ (‖aᵢ‖ ρⁱ)(‖bⱼ‖ ρʲ)`. -/
private theorem norm_mul_mul_zpow_le (hρ : 0 < ρ) (a b : ℤ → R) (i j : ℤ) :
    ‖a i * b j‖ * ρ ^ (i + j) ≤ (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) := by
  calc ‖a i * b j‖ * ρ ^ (i + j) ≤ (‖a i‖ * ‖b j‖) * (ρ ^ i * ρ ^ j) := by
        rw [zpow_add₀ hρ.ne']
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _)
          (mul_pos (zpow_pos hρ i) (zpow_pos hρ j)).le
    _ = (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) := by ring

/-- The terms `a (n - y) * b y` of the `n`-th convolution coefficient of two families converging at
a radius `ρ > 0` tend to zero along the cofinite filter. -/
private theorem LaurentConvergesAt.tendsto_mul_sub (hρ : 0 < ρ) (ha : LaurentConvergesAt ρ a)
    (hb : LaurentConvergesAt ρ b) (n : ℤ) :
    Tendsto (fun y ↦ a (n - y) * b y) cofinite (𝓝 0) := by
  have hinj : Function.Injective fun y : ℤ ↦ (n - y, y) := fun _ _ h ↦ (Prod.ext_iff.1 h).2
  -- the weighted products `(‖aᵢ‖ ρⁱ)(‖bⱼ‖ ρʲ)` tend to zero along the cofinite filter of `ℤ × ℤ`
  have hP : Tendsto (fun y ↦ (‖a (n - y)‖ * ρ ^ (n - y)) * (‖b y‖ * ρ ^ y) / ρ ^ n) cofinite
      (𝓝 0) := by
    simpa only [Function.comp_def, zero_div] using
      ((tendsto_mul_cofinite_nhds_zero ha hb).comp hinj.tendsto_cofinite).div_const (ρ ^ n)
  refine squeeze_zero_norm (fun y ↦ (le_div_iff₀ (zpow_pos hρ n)).2 ?_) hP
  simpa using norm_mul_mul_zpow_le hρ a b (n - y) y

variable [IsUltrametricDist R]

/-- Over a complete ultrametric ring, every convolution coefficient of two families converging at a
radius `ρ > 0` is a convergent series. -/
theorem LaurentConvergesAt.addConvolutionExists [CompleteSpace R] (hρ : 0 < ρ)
    (ha : LaurentConvergesAt ρ a) (hb : LaurentConvergesAt ρ b) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ R) a b := fun n ↦
  (DiscreteConvolution.addFiberEquivSub n).summable_iff.1 <|
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (ha.tendsto_mul_sub hρ hb n)).congr
      fun y ↦ by simp

/-- **Convolution preserves convergence at a radius**: if `∑ aₙ tⁿ` and `∑ bₙ tⁿ` converge on the
circle `|t| = ρ`, so does the series with coefficients `a ⋆ᵣ₊ b`. -/
theorem LaurentConvergesAt.addRingConvolution (hρ : 0 < ρ) (ha : LaurentConvergesAt ρ a)
    (hb : LaurentConvergesAt ρ b) : LaurentConvergesAt ρ (a ⋆ᵣ₊ b) := by
  refine laurentConvergesAt_iff.2 <| Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  -- the finitely many pairs `(i, j)` whose weighted product is at least `ε / 2`
  have hbad := eventually_cofinite.1 <|
    (tendsto_mul_cofinite_nhds_zero ha hb).eventually (gt_mem_nhds (half_pos hε))
  refine eventually_cofinite.2 <| (hbad.image fun p ↦ p.1 + p.2).subset fun n hn ↦ ?_
  by_contra hnot
  refine hn ?_
  have hterm (y : ℤ) : ‖a (n - y) * b y‖ ≤ ε / 2 / ρ ^ n := by
    refine (le_div_iff₀ (zpow_pos hρ n)).2 ?_
    have h := norm_mul_mul_zpow_le hρ a b (n - y) y
    rw [sub_add_cancel] at h
    refine h.trans (not_lt.1 fun hlt ↦ hnot ⟨(n - y, y), not_lt.2 hlt.le, by simp⟩)
  have hcoeff : ‖(a ⋆ᵣ₊ b) n‖ ≤ ε / 2 / ρ ^ n := by
    rw [DiscreteConvolution.addRingConvolution_eq_tsum_sub]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (div_pos (half_pos hε) (zpow_pos hρ n)).le hterm
  have hle : ‖(a ⋆ᵣ₊ b) n‖ * ρ ^ n ≤ ε / 2 := (le_div_iff₀ (zpow_pos hρ n)).1 hcoeff
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (zpow_pos hρ n).le)]
  linarith

/-- **The Gauss norm is submultiplicative**: `|a ⋆ b|_ρ ≤ |a|_ρ |b|_ρ` at a radius `ρ > 0` for
families whose weighted norms are bounded above, in particular for families converging at `ρ`. -/
theorem laurentGaussNorm_addRingConvolution_le (hρ : 0 < ρ)
    (ha : BddAbove (Set.range fun n ↦ ‖a n‖ * ρ ^ n))
    (hb : BddAbove (Set.range fun n ↦ ‖b n‖ * ρ ^ n)) :
    laurentGaussNorm ρ (a ⋆ᵣ₊ b) ≤ laurentGaussNorm ρ a * laurentGaussNorm ρ b := by
  refine laurentGaussNorm_le fun n ↦ (le_div_iff₀ (zpow_pos hρ n)).1 ?_
  rw [DiscreteConvolution.addRingConvolution_eq_tsum_sub]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (div_nonneg (mul_nonneg (laurentGaussNorm_nonneg ρ a) (laurentGaussNorm_nonneg ρ b))
      (zpow_pos hρ n).le) fun y ↦ (le_div_iff₀ (zpow_pos hρ n)).2 ?_
  have h := norm_mul_mul_zpow_le hρ a b (n - y) y
  rw [sub_add_cancel] at h
  exact h.trans (mul_le_mul (le_laurentGaussNorm ha _) (le_laurentGaussNorm hb _)
    (mul_nonneg (norm_nonneg _) (zpow_pos hρ _).le) (laurentGaussNorm_nonneg ρ a))

open DiscreteConvolution in
/-- Over a complete ultrametric ring, the triple products `a i * b j * c k` over the triples with
`i + j + k = n` of three families converging at a radius `ρ > 0` form a summable family, indexed as
in `DiscreteConvolution.addRingConvolution_assoc`. -/
theorem LaurentConvergesAt.summable_sigma_addFiber_mul_mul [CompleteSpace R] (hρ : 0 < ρ)
    (ha : LaurentConvergesAt ρ a) (hb : LaurentConvergesAt ρ b) (hc : LaurentConvergesAt ρ c)
    (n : ℤ) :
    Summable fun σ : Σ p : addFiber n, addFiber p.val.1 ↦
      a σ.2.val.1 * b σ.2.val.2 * c σ.1.val.2 := by
  -- `σ ↦ ((i, j), k)` is injective, and the weighted triple products tend to zero
  have hj : Function.Injective fun σ : Σ p : addFiber n, addFiber p.val.1 ↦ (σ.2.val, σ.1.val.2) :=
    fun _ _ _ ↦ by grind
  have hP := ((tendsto_mul_cofinite_nhds_zero (tendsto_mul_cofinite_nhds_zero ha hb) hc).comp
    hj.tendsto_cofinite).div_const (ρ ^ n)
  rw [zero_div] at hP
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    squeeze_zero_norm (fun σ ↦ (le_div_iff₀ (zpow_pos hρ n)).2 ?_) hP
  obtain ⟨⟨⟨m, k⟩, hmk⟩, ⟨⟨i, j⟩, hij⟩⟩ := σ
  obtain rfl := mem_addFiber.1 hmk
  obtain rfl := mem_addFiber.1 hij
  calc ‖a i * b j * c k‖ * ρ ^ (i + j + k)
      ≤ (‖a i * b j‖ * ρ ^ (i + j)) * (‖c k‖ * ρ ^ k) := by
        simpa using norm_mul_mul_zpow_le hρ (fun _ ↦ a i * b j) c (i + j) k
    _ ≤ (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) * (‖c k‖ * ρ ^ k) :=
        mul_le_mul_of_nonneg_right (norm_mul_mul_zpow_le hρ a b i j)
          (mul_nonneg (norm_nonneg _) (zpow_pos hρ k).le)

end Convolution

end TauCeti
