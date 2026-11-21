/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Robba.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Instances.Int
import TauCeti.Analysis.Normed.Group.Pi

/-!
# The Amice ring

Let `R` be a complete normed ring with an ultrametric norm. The Amice ring `E` over `R` consists of
the two-sided Laurent series `∑_{n ∈ ℤ} aₙ tⁿ` whose coefficients are bounded and tend to zero as
`n → -∞`, with the convolution product `(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ`. These are the bounded functions
on the "boundary circle" `|t| = 1⁻` with no convergence condition inside: unlike the Robba ring,
the negative tail only tends to zero, with no exponential decay, so the series need not converge on
any annulus `r < |t| < 1` and `E` is not a ring of functions on an annulus. Its subring
`O_E` consists of the series with coefficients in the closed unit ball. For a complete discretely
valued field, `E` is a field with valuation ring `O_E` and residue field the Laurent series over
the residue field; that structure is not constructed here.

The bounded Robba ring embeds in `E` (`TauCeti.RobbaRing.boundedToAmice`): the coefficients of a
series converging on an annulus `r < |t| < 1` tend to zero at `-∞`. Its image consists exactly of
the elements of `E` whose coefficients converge on some annulus
(`TauCeti.RobbaRing.mem_range_boundedToAmice`), the identity `R^bd = R ∩ E`.

Each coefficient of a product converges because its terms `a_{n - y} b_y` tend to zero along the
cofinite filter: as `y → -∞` because `b_y → 0` and `a` is bounded, and as `y → ∞` because
`a_{n - y} → 0` and `b` is bounded.

## Main definitions

* `TauCeti.amiceCoeff`: the `R`-module of bounded families tending to zero at `-∞`.
* `TauCeti.AmiceRing`: the Amice ring, with its `Ring`, `CommRing` and `Algebra` instances, its
  Laurent monomials and its integral subring
  `O_E = TauCeti.IsConvolutionRing.integral (amiceCoeff R)`, all from
  `TauCeti.instIsConvolutionRingAmiceCoeff`.
* `TauCeti.RobbaRing.boundedToAmice`: the embedding of the bounded Robba ring into `E`.

## Main results

* `TauCeti.addRingConvolution_mem_amiceCoeff`: the convolution of two Amice families is an Amice
  family.
* `TauCeti.instIsConvolutionRingAmiceCoeff`: over a complete ultrametric ring, the coefficients
  of a product of Amice families are convergent convolution sums, and the triple products are
  summable.
* `TauCeti.RobbaRing.boundedToAmice_injective`, `TauCeti.RobbaRing.mem_range_boundedToAmice`: the
  bounded Robba ring is the subring of the Amice ring of series converging on some annulus.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* K. S. Kedlaya, *Local monodromy of p-adic differential equations: an overview*, Int. J. Number
  Theory 1 (2005), Definition 3.5.1.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), §2.3.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti

variable {R : Type*}

/-! ### The Amice coefficient module -/

section Coeff

variable (R) [SeminormedRing R]

/-- The `R`-module of coefficient families of the Amice ring: the families `a : ℤ → R` with bounded
norms that tend to zero as `n → -∞`. -/
def amiceCoeff : Submodule R (ℤ → R) where
  carrier := {a | BddAbove (Set.range fun n ↦ ‖a n‖) ∧ Tendsto a atBot (𝓝 0)}
  zero_mem' := ⟨⟨0, Set.forall_mem_range.2 fun _ ↦ by simp⟩, tendsto_const_nhds⟩
  add_mem' := by
    rintro a b ⟨⟨A, hA⟩, ha⟩ ⟨⟨B, hB⟩, hb⟩
    refine ⟨⟨A + B, Set.forall_mem_range.2 fun n ↦ ?_⟩, by rw [← add_zero (0 : R)]; exact ha.add hb⟩
    exact (norm_add_le _ _).trans (add_le_add (hA ⟨n, rfl⟩) (hB ⟨n, rfl⟩))
  smul_mem' c := by
    rintro a ⟨⟨A, hA⟩, ha⟩
    refine ⟨⟨‖c‖ * A, Set.forall_mem_range.2 fun n ↦ ?_⟩,
      by rw [← smul_zero c]; exact ha.const_smul c⟩
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hA ⟨n, rfl⟩) (norm_nonneg c))

variable {R}

theorem mem_amiceCoeff {a : ℤ → R} :
    a ∈ amiceCoeff R ↔ BddAbove (Set.range fun n ↦ ‖a n‖) ∧ Tendsto a atBot (𝓝 0) :=
  (Iff.rfl)

/-- The weighted coefficient norms at radius `1` of an Amice family are bounded above, so the
Gauss-norm lemmas such as `TauCeti.le_laurentGaussNorm` and
`TauCeti.laurentGaussNorm_addRingConvolution_le` apply to it at `ρ = 1`. -/
theorem bddAbove_of_mem_amiceCoeff {a : ℤ → R} (ha : a ∈ amiceCoeff R) :
    BddAbove (Set.range fun n ↦ ‖a n‖ * (1 : ℝ) ^ n) := by
  simpa using ha.1

theorem single_mem_amiceCoeff (n : ℤ) (c : R) : Pi.single n c ∈ amiceCoeff R := by
  refine ⟨⟨‖c‖, Set.forall_mem_range.2 (Pi.norm_single_apply_le (E := fun _ ↦ R) n · c)⟩,
    tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_lt_atBot n] with m hm
  simp [Pi.single_eq_of_ne hm.ne]

/-- The family equal to `1` in every negative degree and to `0` elsewhere is bounded but does not
tend to zero at `-∞`, so it is not an Amice family. -/
theorem indicator_Iio_one_notMem_amiceCoeff [NormOneClass R] :
    (Set.Iio 0).indicator 1 ∉ amiceCoeff R := fun h ↦
  not_tendsto_indicator_Iio_one_atBot h.2

/-- A family in `amiceCoeff R` has a nonnegative bound on its coefficient norms. -/
private theorem exists_norm_le_of_mem_amiceCoeff {a : ℤ → R} (ha : a ∈ amiceCoeff R) :
    ∃ A, 0 ≤ A ∧ ∀ n, ‖a n‖ ≤ A := by
  obtain ⟨A, hA⟩ := ha.1
  exact ⟨max A 0, le_max_right A 0, fun n ↦ (hA ⟨n, rfl⟩).trans (le_max_left A 0)⟩

end Coeff

/-! ### Convolution of Amice families -/

section Convolution

variable [SeminormedRing R] {a b c : ℤ → R}

/-- The terms `a (n - y) * b y` of the `n`-th convolution coefficient of two Amice families tend
to zero along the cofinite filter. -/
private theorem tendsto_mul_sub_of_mem_amiceCoeff (ha : a ∈ amiceCoeff R)
    (hb : b ∈ amiceCoeff R) (n : ℤ) : Tendsto (fun y ↦ a (n - y) * b y) cofinite (𝓝 0) := by
  obtain ⟨A, -, hA⟩ := exists_norm_le_of_mem_amiceCoeff ha
  obtain ⟨B, -, hB⟩ := exists_norm_le_of_mem_amiceCoeff hb
  rw [Int.cofinite_eq, tendsto_sup]
  refine ⟨isBoundedUnder_le_mul_tendsto_zero (isBoundedUnder_of ⟨A, fun y ↦ hA _⟩) hb.2, ?_⟩
  have hsub : Tendsto (fun y : ℤ ↦ n - y) atTop atBot :=
    tendsto_atTop_atBot.2 fun m ↦ ⟨n - m, fun y hy ↦ by omega⟩
  exact (ha.2.comp hsub).zero_mul_isBoundedUnder_le (isBoundedUnder_of ⟨B, fun y ↦ hB _⟩)

/-- The products `a i * b j * c (n - i - j)` of three Amice families tend to zero along the
cofinite filter of `ℤ × ℤ`. -/
private theorem tendsto_mul_mul_sub_of_mem_amiceCoeff (ha : a ∈ amiceCoeff R)
    (hb : b ∈ amiceCoeff R) (hc : c ∈ amiceCoeff R) (n : ℤ) :
    Tendsto (fun p : ℤ × ℤ ↦ a p.1 * b p.2 * c (n - p.1 - p.2)) cofinite (𝓝 0) := by
  obtain ⟨A, hA₀, hA⟩ := exists_norm_le_of_mem_amiceCoeff ha
  obtain ⟨B, hB₀, hB⟩ := exists_norm_le_of_mem_amiceCoeff hb
  obtain ⟨C, -, hC⟩ := exists_norm_le_of_mem_amiceCoeff hc
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  -- below `N` each family is small against the product of the other two bounds
  obtain ⟨N, hN⟩ := eventually_atBot.1 <|
    (((Tendsto.norm ha.2).mul_const (B * C) |>.eventually (gt_mem_nhds (by simpa using hε))).and
      ((Tendsto.norm hb.2).mul_const (A * C) |>.eventually (gt_mem_nhds (by simpa using hε)))).and
      ((Tendsto.norm hc.2).mul_const (A * B) |>.eventually (gt_mem_nhds (by simpa using hε)))
  -- a large product has all three degrees above `N`, which leaves finitely many pairs
  refine eventually_cofinite.2 <|
    ((Set.finite_Ioo N (n - N - N)).prod (Set.finite_Ioo N (n - N - N))).subset fun p hp ↦ ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hp
  have hle : ‖a p.1 * b p.2 * c (n - p.1 - p.2)‖ ≤ ‖a p.1‖ * ‖b p.2‖ * ‖c (n - p.1 - p.2)‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  -- bound the product by one factor times the bounds of the other two, with that factor first
  have h₁ : N < p.1 := not_le.1 fun h ↦ (hN p.1 h).1.1.not_ge <| hp.trans <| hle.trans <| by
    rw [mul_assoc]; gcongr; exacts [hB _, hC _]
  have h₂ : N < p.2 := not_le.1 fun h ↦ (hN p.2 h).1.2.not_ge <| hp.trans <| hle.trans <| by
    rw [mul_comm ‖a p.1‖, mul_assoc]; gcongr; exacts [hA _, hC _]
  have h₃ : N < n - p.1 - p.2 := not_le.1 fun h ↦ (hN _ h).2.not_ge <| hp.trans <| hle.trans <| by
    rw [mul_comm]; gcongr; exacts [hA _, hB _]
  exact ⟨⟨h₁, by omega⟩, ⟨h₂, by omega⟩⟩

variable [IsUltrametricDist R]

/-- **The convolution of two Amice families is an Amice family**: its coefficient norms are bounded
by the product of the bounds, and it tends to zero at `-∞`. -/
theorem addRingConvolution_mem_amiceCoeff (ha : a ∈ amiceCoeff R) (hb : b ∈ amiceCoeff R) :
    a ⋆ᵣ₊ b ∈ amiceCoeff R := by
  obtain ⟨A, -, hA⟩ := exists_norm_le_of_mem_amiceCoeff ha
  obtain ⟨B, -, hB⟩ := exists_norm_le_of_mem_amiceCoeff hb
  -- every coefficient has norm at most `A B`
  refine ⟨⟨A * B,
    Set.forall_mem_range.2 (DiscreteConvolution.norm_addRingConvolution_apply_le hA hB)⟩,
    Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  -- below `N` both families are small against the other's bound, and a coefficient of degree
  -- `n ≤ N + N` has in each term `a (n - y) * b y` a factor of degree at most `N`
  have hsmall (x : ℤ → R) (hx : Tendsto x atBot (𝓝 0)) (C : ℝ) :
      ∀ᶠ m in atBot, ‖x m‖ * C < ε / 2 := by
    have h := (Tendsto.norm hx).mul_const C
    rw [norm_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atBot.1 <| (hsmall a ha.2 B).and (hsmall b hb.2 A)
  filter_upwards [eventually_le_atBot (N + N)] with n hn
  rw [dist_zero_right, DiscreteConvolution.addRingConvolution_eq_tsum_sub]
  refine (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le
    fun y ↦ ?_).trans_lt (half_lt_self hε)
  refine (norm_mul_le _ _).trans ?_
  rcases le_or_gt y N with hy | hy
  · exact (mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)).trans
      ((mul_comm _ _).trans_le (hN y hy).2.le)
  · exact (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)).trans (hN (n - y) (by omega)).1.le

variable [CompleteSpace R]

/-- Over a complete ultrametric ring, every convolution coefficient of two Amice families is a
convergent series. -/
theorem addConvolutionExists_of_mem_amiceCoeff (ha : a ∈ amiceCoeff R) (hb : b ∈ amiceCoeff R) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ R) a b := fun n ↦
  (DiscreteConvolution.addFiberEquivSub n).summable_iff.1 <|
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_mul_sub_of_mem_amiceCoeff ha hb n)).congr fun y ↦ by simp

open DiscreteConvolution in
/-- Over a complete ultrametric ring, the triple products `a i * b j * c k` over the triples with
`i + j + k = n` of three Amice families form a summable family, indexed as in
`DiscreteConvolution.addRingConvolution_assoc`. -/
theorem summable_sigma_addFiber_mul_mul_of_mem_amiceCoeff (ha : a ∈ amiceCoeff R)
    (hb : b ∈ amiceCoeff R) (hc : c ∈ amiceCoeff R) (n : ℤ) :
    Summable fun σ : Σ p : addFiber n, addFiber p.val.1 ↦
      a σ.2.val.1 * b σ.2.val.2 * c σ.1.val.2 := by
  -- such a pair `((m, k), (i, j))` is determined by `(i, j)`, since `k = n - i - j`
  have hj : Function.Injective fun σ : Σ p : addFiber n, addFiber p.val.1 ↦ σ.2.val :=
    fun _ _ _ ↦ by grind
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    (tendsto_mul_mul_sub_of_mem_amiceCoeff ha hb hc n).comp hj.tendsto_cofinite).congr fun σ ↦ ?_
  obtain ⟨⟨⟨m, k⟩, hmk⟩, ⟨⟨i, j⟩, hij⟩⟩ := σ
  simp only [mem_addFiber] at hmk hij
  simp only [Function.comp_apply]
  congr 2
  omega

/-- Over a complete ultrametric seminormed ring the Amice coefficient families satisfy the
`IsConvolutionRing` hypotheses; they form a ring under convolution when `R` is moreover normed
(hence `T3`). -/
instance instIsConvolutionRingAmiceCoeff : IsConvolutionRing (amiceCoeff R) where
  single_mem := single_mem_amiceCoeff
  addRingConvolution_mem := addRingConvolution_mem_amiceCoeff
  addConvolutionExists := addConvolutionExists_of_mem_amiceCoeff
  summable_sigma_addFiber_mul_mul := summable_sigma_addFiber_mul_mul_of_mem_amiceCoeff

end Convolution

/-! ### The Amice ring -/

variable (R) in
/-- **The Amice ring** `E` over `R`: the Laurent series `∑_{n ∈ ℤ} aₙ tⁿ` with bounded
coefficients tending to zero as `n → -∞`, with the convolution product. Its ring structure needs
`R` normed (not just seminormed), complete and ultrametric
(`TauCeti.instIsConvolutionRingAmiceCoeff` and `TauCeti.IsConvolutionRing.instRing`). -/
abbrev AmiceRing [SeminormedRing R] : Type _ :=
  amiceCoeff R

/-! ### The bounded Robba ring inside the Amice ring -/

namespace RobbaRing

open IsConvolutionRing

variable [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- A Robba series with bounded coefficients is an element of the Amice ring. -/
theorem coe_mem_amiceCoeff {f : RobbaRing R} (hf : f ∈ bounded R) :
    (f : ℤ → R) ∈ amiceCoeff R :=
  ⟨mem_bounded.1 hf, tendsto_atBot_of_mem_robbaCoeff f.property⟩

variable (R) in
/-- **The embedding of the bounded Robba ring `R^bd` into the Amice ring `E`**, the identity on
coefficients. -/
noncomputable def boundedToAmice : bounded R →ₐ[R] AmiceRing R where
  toFun f := ⟨f.val, coe_mem_amiceCoeff f.property⟩
  map_one' := Subtype.ext <| by simp
  map_mul' _ _ := Subtype.ext <| by simp
  map_zero' := Subtype.ext <| by simp
  map_add' _ _ := Subtype.ext <| by simp
  commutes' _ := Subtype.ext <| by simp

@[simp]
theorem coe_boundedToAmice (f : bounded R) :
    (boundedToAmice R f : ℤ → R) = ((f : RobbaRing R) : ℤ → R) :=
  (rfl)

/-- The embedding of the bounded Robba ring into the Amice ring is injective. -/
theorem boundedToAmice_injective : Function.Injective (boundedToAmice R) :=
  fun _ _ h ↦ Subtype.ext <| Subtype.ext <| by
    simpa using congr_arg (fun g : AmiceRing R ↦ (g : ℤ → R)) h

/-- The embedding of the bounded Robba ring into the Amice ring sends each monomial `c tⁿ` to the
monomial `c tⁿ`. -/
@[simp]
theorem boundedToAmice_monomial (n : ℤ) (c : R) :
    boundedToAmice R ⟨monomial n c, monomial_mem_bounded n c⟩ = (monomial n c : AmiceRing R) :=
  Subtype.ext <| by simp

/-- **`R^bd = R ∩ E`**: an element of the Amice ring comes from the bounded Robba ring exactly when
its coefficients converge on some annulus `r < |t| < 1`. -/
theorem mem_range_boundedToAmice {g : AmiceRing R} :
    g ∈ (boundedToAmice R).range ↔ (g : ℤ → R) ∈ robbaCoeff R := by
  refine ⟨?_, fun hg ↦
    ⟨⟨⟨g, hg⟩, mem_bounded.2 (mem_amiceCoeff.1 g.property).1⟩, Subtype.ext (by simp)⟩⟩
  rintro ⟨f, rfl⟩
  simp

end RobbaRing

end TauCeti
