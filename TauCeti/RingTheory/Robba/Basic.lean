/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import TauCeti.Topology.Algebra.InfiniteSum.ConvolutionRing
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Instances.Int
import TauCeti.Analysis.Normed.Group.Pi

/-!
# The Robba ring and its annular coefficient algebras

Let `R` be a normed ring with an ultrametric norm. A two-sided coefficient family `a : ℤ → R`
gives a formal Laurent series `∑_{n ∈ ℤ} aₙ tⁿ`. This file constructs the rings of such series
converging on half-open annuli `r < |t| < 1` and their union, the Robba ring.

* At a radius `ρ`, `TauCeti.LaurentConvergesAt ρ a` says `‖aₙ‖ ρⁿ → 0` as `|n| → ∞`, the condition
  for `∑ aₙ tⁿ` to converge on the circle `|t| = ρ`, and `TauCeti.laurentGaussNorm ρ a` is the
  Gauss norm `|a|_ρ = sup_n ‖aₙ‖ ρⁿ`.
* `TauCeti.annularCoeff R r` is the `R`-module of families converging at every radius `ρ` with
  `0 < ρ`, `r < ρ < 1`: the series on the annulus `r < |t| < 1` (the punctured open unit disc when
  `r ≤ 0`).
* `TauCeti.robbaCoeff R` is the directed union of these modules over `r < 1`: the series converging
  on some annulus `r < |t| < 1`.
* `TauCeti.RobbaRing R` is `robbaCoeff R` with the convolution product
  `(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ`, a ring when `R` is a complete ultrametric normed ring, and a
  commutative `R`-algebra when `R` is moreover commutative: over a complete ultrametric
  seminormed ring `robbaCoeff R` satisfies
  `TauCeti.IsConvolutionRing`, which supplies these structures, the monomials and the integral
  subring `TauCeti.IsConvolutionRing.integral (robbaCoeff R)` (`R^int`). It contains the annular
  algebras `TauCeti.RobbaRing.annulus R r` and the subalgebra `TauCeti.RobbaRing.bounded R` of
  series with bounded coefficients (the bounded Robba ring, written `R^bd` or `E†`).

Each coefficient of a product is an infinite series: for `ρ` in the convergence domain of both
factors, its terms satisfy `‖aᵢ bₙ₋ᵢ‖ ρⁿ ≤ (‖aᵢ‖ ρⁱ)(‖bₙ₋ᵢ‖ ρⁿ⁻ⁱ)`, and the right side tends to
zero along the cofinite filter of `ℤ × ℤ`. Hence, over a complete ultrametric ring, the product
coefficients converge, the product converges at `ρ` again, and the Gauss norm is submultiplicative
(`TauCeti.laurentGaussNorm_addRingConvolution_le`). The Gauss-norm lemmas only ask the weighted
norms to be bounded above, so they also apply at radius `1` to families with bounded coefficients
that need not decay at `+∞`, such as those of the Amice ring
(`TauCeti.bddAbove_of_mem_amiceCoeff`). The radius-wise Fréchet and inductive-limit topologies are
not constructed here.

## Main definitions

* `TauCeti.LaurentConvergesAt`, `TauCeti.laurentGaussNorm`: convergence and the Gauss norm at a
  radius.
* `TauCeti.annularCoeff`, `TauCeti.robbaCoeff`: the coefficient modules of an annulus and of the
  Robba ring.
* `TauCeti.RobbaRing`: the Robba ring, with its `Ring`, `CommRing` and `Algebra` instances from
  `TauCeti.instIsConvolutionRingRobbaCoeff`.
* `TauCeti.RobbaRing.annulus`, `TauCeti.RobbaRing.bounded`: the annular and bounded subrings.

## Main results

* `TauCeti.LaurentConvergesAt.addRingConvolution`: convergence at a radius is preserved by
  convolution.
* `TauCeti.RobbaRing.isUnit_monomial_bounded`: `t` is a unit of the bounded Robba ring.
* `TauCeti.RobbaRing.iSup_annulus`: the Robba ring is the union of its annular algebras.

## References

* K. S. Kedlaya, *Local monodromy of p-adic differential equations: an overview*, Int. J. Number
  Theory 1 (2005), Definition 3.5.1.
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

/-! ### The annular coefficient modules and the Robba coefficient module -/

section Coeff

variable (R) [SeminormedRing R]

/-- The `R`-module of coefficient families `a : ℤ → R` whose Laurent series converge on the annulus
`r < |t| < 1`: `‖aₙ‖ ρⁿ → 0` as `|n| → ∞` for every radius `0 < ρ` with `r < ρ < 1`. For `r ≤ 0`
the annulus is the punctured open unit disc. -/
def annularCoeff (r : ℝ) : Submodule R (ℤ → R) where
  carrier := {a | ∀ ρ, 0 < ρ → r < ρ → ρ < 1 → LaurentConvergesAt ρ a}
  zero_mem' _ _ _ _ := laurentConvergesAt_zero _
  add_mem' ha hb ρ h₀ hr h₁ := (ha ρ h₀ hr h₁).add (hb ρ h₀ hr h₁)
  smul_mem' c _ ha ρ h₀ hr h₁ := (ha ρ h₀ hr h₁).smul c

variable {R}

theorem mem_annularCoeff {r : ℝ} {a : ℤ → R} :
    a ∈ annularCoeff R r ↔ ∀ ρ, 0 < ρ → r < ρ → ρ < 1 → LaurentConvergesAt ρ a :=
  (Iff.rfl)

/-- A smaller inner radius is a larger annulus, so it has fewer convergent series. -/
theorem annularCoeff_mono {r s : ℝ} (h : r ≤ s) : annularCoeff R r ≤ annularCoeff R s :=
  fun _ ha ρ h₀ hs h₁ ↦ ha ρ h₀ (h.trans_lt hs) h₁

theorem single_mem_annularCoeff (r : ℝ) (n : ℤ) (c : R) :
    Pi.single n c ∈ annularCoeff R r :=
  fun ρ _ _ _ ↦ laurentConvergesAt_single ρ n c

variable (R) in
/-- The `R`-module of coefficient families of the Robba ring: the families whose Laurent series
converge on some annulus `r < |t| < 1`. It is the directed union of the modules
`TauCeti.annularCoeff R r` over `r < 1` (`TauCeti.iSup_annularCoeff`). -/
def robbaCoeff : Submodule R (ℤ → R) where
  carrier := {a | ∃ r < 1, a ∈ annularCoeff R r}
  zero_mem' := ⟨0, zero_lt_one, zero_mem _⟩
  add_mem' := fun ⟨r, hr, ha⟩ ⟨s, hs, hb⟩ ↦ ⟨max r s, max_lt hr hs,
    add_mem (annularCoeff_mono (le_max_left r s) ha) (annularCoeff_mono (le_max_right r s) hb)⟩
  smul_mem' c _ := fun ⟨r, hr, ha⟩ ↦ ⟨r, hr, Submodule.smul_mem _ c ha⟩

theorem mem_robbaCoeff {a : ℤ → R} : a ∈ robbaCoeff R ↔ ∃ r < 1, a ∈ annularCoeff R r :=
  (Iff.rfl)

theorem annularCoeff_le_robbaCoeff {r : ℝ} (hr : r < 1) : annularCoeff R r ≤ robbaCoeff R :=
  fun _ ha ↦ ⟨r, hr, ha⟩

/-- The Robba coefficient module is the union of the annular coefficient modules over the inner
radii `r < 1`. -/
theorem iSup_annularCoeff : ⨆ r : Set.Iio (1 : ℝ), annularCoeff R r = robbaCoeff R :=
  le_antisymm (iSup_le fun r ↦ annularCoeff_le_robbaCoeff r.property) fun _ ⟨r, hr, ha⟩ ↦
    Submodule.mem_iSup_of_mem (⟨r, hr⟩ : Set.Iio (1 : ℝ)) ha

/-- **A Robba coefficient family is one converging at every radius `ρ < 1` close enough to `1`.** -/
theorem mem_robbaCoeff_iff_eventually {a : ℤ → R} :
    a ∈ robbaCoeff R ↔ ∀ᶠ ρ in 𝓝[<] (1 : ℝ), LaurentConvergesAt ρ a := by
  refine ⟨fun ⟨r, hr, ha⟩ ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [Ioo_mem_nhdsLT (max_lt hr zero_lt_one)] with ρ hρ
    exact ha ρ ((le_max_right r 0).trans_lt hρ.1) ((le_max_left r 0).trans_lt hρ.1) hρ.2
  · obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h
    exact ⟨l, hl, fun ρ _ hlρ hρ ↦ hsub ⟨hlρ, hρ⟩⟩

/-- A property holding at every radius close enough to `1` holds at some positive radius. -/
private theorem exists_pos_of_eventually {p : ℝ → Prop} (h : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), p ρ) :
    ∃ ρ, 0 < ρ ∧ p ρ :=
  have h₀ : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one
  (h₀.and h).exists.imp fun _ h ↦ ⟨h.1.1, h.2⟩

/-- The coefficients of a Robba coefficient family tend to zero at `-∞`. -/
theorem tendsto_atBot_of_mem_robbaCoeff {a : ℤ → R} (ha : a ∈ robbaCoeff R) :
    Tendsto a atBot (𝓝 0) := by
  obtain ⟨ρ, h₀, ha, h₁⟩ := exists_pos_of_eventually <|
    (mem_robbaCoeff_iff_eventually.1 ha).and self_mem_nhdsWithin
  exact ha.tendsto_atBot h₀ (le_of_lt h₁)

/-- The family equal to `1` in every negative degree and to `0` elsewhere does not tend to zero at
`-∞`. -/
theorem not_tendsto_indicator_Iio_one_atBot [NormOneClass R] :
    ¬ Tendsto ((Set.Iio (0 : ℤ)).indicator (1 : ℤ → R)) atBot (𝓝 0) := fun h ↦ by
  have h₁ : Tendsto (fun n ↦ ‖(Set.Iio (0 : ℤ)).indicator (1 : ℤ → R) n‖) atBot (𝓝 1) :=
    tendsto_const_nhds.congr' <| (eventually_lt_atBot 0).mono fun n hn ↦ by
      beta_reduce
      rw [Set.indicator_of_mem (Set.mem_Iio.2 hn), Pi.one_apply, norm_one]
  exact one_ne_zero <| tendsto_nhds_unique h₁ (by simpa using Tendsto.norm h)

/-- The family equal to `1` in every negative degree and to `0` elsewhere converges on no annulus:
its coefficients do not tend to zero at `-∞`. -/
theorem indicator_Iio_one_notMem_robbaCoeff [NormOneClass R] :
    (Set.Iio 0).indicator 1 ∉ robbaCoeff R := fun h ↦
  not_tendsto_indicator_Iio_one_atBot (tendsto_atBot_of_mem_robbaCoeff h)

end Coeff

section Mul

variable [SeminormedRing R] [IsUltrametricDist R]

/-- The convolution of two families converging on the annulus `r < |t| < 1` converges there. -/
theorem addRingConvolution_mem_annularCoeff {r : ℝ} {a b : ℤ → R} (ha : a ∈ annularCoeff R r)
    (hb : b ∈ annularCoeff R r) : a ⋆ᵣ₊ b ∈ annularCoeff R r :=
  fun ρ h₀ hr h₁ ↦ (ha ρ h₀ hr h₁).addRingConvolution h₀ (hb ρ h₀ hr h₁)

theorem addRingConvolution_mem_robbaCoeff {a b : ℤ → R} (ha : a ∈ robbaCoeff R)
    (hb : b ∈ robbaCoeff R) : a ⋆ᵣ₊ b ∈ robbaCoeff R := by
  obtain ⟨r, hr, ha⟩ := ha
  obtain ⟨s, hs, hb⟩ := hb
  exact annularCoeff_le_robbaCoeff (max_lt hr hs) <| addRingConvolution_mem_annularCoeff
    (annularCoeff_mono (le_max_left r s) ha) (annularCoeff_mono (le_max_right r s) hb)

theorem addConvolutionExists_of_mem_robbaCoeff [CompleteSpace R] {a b : ℤ → R}
    (ha : a ∈ robbaCoeff R) (hb : b ∈ robbaCoeff R) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ R) a b := by
  obtain ⟨ρ, h₀, ha, hb⟩ := exists_pos_of_eventually <|
    (mem_robbaCoeff_iff_eventually.1 ha).and (mem_robbaCoeff_iff_eventually.1 hb)
  exact ha.addConvolutionExists h₀ hb

/-- Over a complete ultrametric seminormed ring the Robba coefficient families satisfy the
`IsConvolutionRing` hypotheses; they form a ring under convolution when `R` is moreover normed
(hence `T3`). -/
instance instIsConvolutionRingRobbaCoeff [CompleteSpace R] : IsConvolutionRing (robbaCoeff R) where
  single_mem n c := annularCoeff_le_robbaCoeff zero_lt_one (single_mem_annularCoeff 0 n c)
  addRingConvolution_mem := addRingConvolution_mem_robbaCoeff
  addConvolutionExists := addConvolutionExists_of_mem_robbaCoeff
  summable_sigma_addFiber_mul_mul ha hb hc := by
    obtain ⟨ρ, h₀, ha, hb, hc⟩ := exists_pos_of_eventually <|
      (mem_robbaCoeff_iff_eventually.1 ha).and <|
        (mem_robbaCoeff_iff_eventually.1 hb).and (mem_robbaCoeff_iff_eventually.1 hc)
    exact ha.summable_sigma_addFiber_mul_mul h₀ hb hc

end Mul

/-! ### The Robba ring -/

variable (R) in
/-- **The Robba ring** `R_R`: the Laurent series `∑_{n ∈ ℤ} aₙ tⁿ` with coefficients in `R`
converging on some annulus `r < |t| < 1`, with the convolution product
`(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ`. Its ring structure needs `R` normed (not just seminormed), complete
and ultrametric (`TauCeti.instIsConvolutionRingRobbaCoeff` and
`TauCeti.IsConvolutionRing.instRing`). -/
abbrev RobbaRing [SeminormedRing R] : Type _ :=
  robbaCoeff R

namespace RobbaRing

open IsConvolutionRing

section CommRing

variable [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-! ### Annular, bounded and integral subrings -/

variable (R) in
/-- The subalgebra `A(r, 1)` of the Robba ring of series converging on the annulus
`r < |t| < 1`. -/
def annulus (r : ℝ) : Subalgebra R (RobbaRing R) where
  carrier := {f | (f : ℤ → R) ∈ annularCoeff R r}
  mul_mem' hf hg := addRingConvolution_mem_annularCoeff hf hg
  add_mem' {f g} hf hg := (Submodule.add_mem _ hf hg : (f : ℤ → R) + g ∈ annularCoeff R r)
  algebraMap_mem' c := by simpa using single_mem_annularCoeff r 0 c

@[simp]
theorem mem_annulus {r : ℝ} {f : RobbaRing R} : f ∈ annulus R r ↔ (f : ℤ → R) ∈ annularCoeff R r :=
  (Iff.rfl)

theorem annulus_mono {r s : ℝ} (h : r ≤ s) : annulus R r ≤ annulus R s :=
  fun _ hf ↦ annularCoeff_mono h hf

/-- Every monomial `c tⁿ` converges on every annulus. -/
theorem monomial_mem_annulus (r : ℝ) (n : ℤ) (c : R) : monomial n c ∈ annulus R r := by
  simpa using single_mem_annularCoeff r n c

/-- **The Robba ring is the directed union of its annular subalgebras** over the inner radii
`r < 1`. -/
theorem iSup_annulus : ⨆ r : Set.Iio (1 : ℝ), annulus R r = ⊤ :=
  eq_top_iff.2 fun f _ ↦ by
    obtain ⟨r, hr, hf⟩ := f.property
    exact Algebra.mem_iSup_of_mem (⟨r, hr⟩ : Set.Iio (1 : ℝ)) hf

variable (R) in
/-- **The bounded Robba ring** `R^bd`, also written `E†`: the subalgebra of series with bounded
coefficients. -/
def bounded : Subalgebra R (RobbaRing R) where
  carrier := {f | BddAbove (Set.range fun n ↦ ‖(f : ℤ → R) n‖)}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    exact ⟨A * B, Set.forall_mem_range.2 <|
      DiscreteConvolution.norm_addRingConvolution_apply_le (fun n ↦ hA ⟨n, rfl⟩)
        (fun n ↦ hB ⟨n, rfl⟩)⟩
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨max A B, Set.forall_mem_range.2 fun n ↦ ?_⟩
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (hA ⟨n, rfl⟩) (hB ⟨n, rfl⟩))
  algebraMap_mem' c := ⟨‖c‖, Set.forall_mem_range.2 fun n ↦ by
    simpa using Pi.norm_single_apply_le (E := fun _ ↦ R) 0 n c⟩

@[simp]
theorem mem_bounded {f : RobbaRing R} :
    f ∈ bounded R ↔ BddAbove (Set.range fun n ↦ ‖(f : ℤ → R) n‖) :=
  (Iff.rfl)

/-- Every monomial `c tⁿ` has bounded coefficients. -/
theorem monomial_mem_bounded (n : ℤ) (c : R) : monomial n c ∈ bounded R :=
  ⟨‖c‖, Set.forall_mem_range.2 fun m ↦ by
    simpa using Pi.norm_single_apply_le (E := fun _ ↦ R) n m c⟩

/-- A monomial `a tⁿ` with a unit coefficient is a unit of the bounded Robba ring: its inverse
`a⁻¹ t⁻ⁿ` is bounded too. In particular `t` is a unit of `R^bd`. -/
theorem isUnit_monomial_bounded (n : ℤ) {a : R} (ha : IsUnit a) :
    IsUnit (⟨monomial n a, monomial_mem_bounded n a⟩ : bounded R) := by
  obtain ⟨u, rfl⟩ := ha
  exact isUnit_iff_exists.2 ⟨⟨monomial (-n) ↑u⁻¹, monomial_mem_bounded _ _⟩,
    Subtype.ext (by simp), Subtype.ext (by simp)⟩

variable [NormOneClass R]

/-- Integral series have bounded coefficients. -/
theorem integral_le_bounded : integral (robbaCoeff R) ≤ (bounded R).toSubring :=
  fun _ hf ↦ ⟨1, Set.forall_mem_range.2 (mem_integral.1 hf)⟩

end CommRing

end RobbaRing

end TauCeti
