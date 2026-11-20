/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Robba.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Instances.Int
import TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# The Amice ring

Let `R` be a complete normed ring with an ultrametric norm. The Amice ring `E` over `R` consists of
the two-sided Laurent series `∑_{n ∈ ℤ} aₙ tⁿ` whose coefficients are bounded and tend to zero as
`n → -∞`, with the convolution product `(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ`. These are the bounded functions
on the "boundary circle" `|t| = 1⁻` with no convergence condition inside: unlike the Robba ring,
the positive tail is only bounded, so `E` is not a ring of functions on any annulus. Its subring
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
* `TauCeti.AmiceRing`: the Amice ring, with its `Ring`, `CommRing` and `Algebra` instances.
* `TauCeti.AmiceRing.monomial`: the Laurent monomial `c tⁿ`.
* `TauCeti.AmiceRing.integral`: the integral subring `O_E`.
* `TauCeti.RobbaRing.boundedToAmice`: the embedding of the bounded Robba ring into `E`.

## Main results

* `TauCeti.addRingConvolution_mem_amiceCoeff`: the convolution of two Amice families is an Amice
  family.
* `TauCeti.AmiceRing.hasSum_coeff_mul`: the coefficients of a product are the convergent
  convolution sums.
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

theorem single_mem_amiceCoeff (n : ℤ) (c : R) : Pi.single n c ∈ amiceCoeff R := by
  refine ⟨⟨‖c‖, Set.forall_mem_range.2 (norm_single_apply_le n · c)⟩,
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

variable [NormedRing R] {a b c : ℤ → R}

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
  refine ⟨⟨A * B, Set.forall_mem_range.2 (norm_addRingConvolution_apply_le hA hB)⟩,
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
    Summable fun σ : Σ p : addFiber n, addFiber p.1.1 ↦ a σ.2.1.1 * b σ.2.1.2 * c σ.1.1.2 := by
  -- such a pair `((m, k), (i, j))` is determined by `(i, j)`, since `k = n - i - j`
  have hj : Function.Injective fun σ : Σ p : addFiber n, addFiber p.1.1 ↦ σ.2.1 :=
    fun _ _ _ ↦ by grind
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    (tendsto_mul_mul_sub_of_mem_amiceCoeff ha hb hc n).comp hj.tendsto_cofinite).congr fun σ ↦ ?_
  obtain ⟨⟨⟨m, k⟩, hmk⟩, ⟨⟨i, j⟩, hij⟩⟩ := σ
  simp only [mem_addFiber] at hmk hij
  simp only [Function.comp_apply]
  congr 2
  omega

end Convolution

/-! ### The Amice ring -/

variable (R) in
/-- **The Amice ring** `E` over `R`: the Laurent series `∑_{n ∈ ℤ} aₙ tⁿ` with bounded
coefficients tending to zero as `n → -∞`, with the convolution product. Its ring structure needs
`R` complete and ultrametric (`TauCeti.AmiceRing.instRing`). -/
abbrev AmiceRing [SeminormedRing R] : Type _ :=
  amiceCoeff R

namespace AmiceRing

section One

variable [SeminormedRing R]

@[ext]
theorem ext {f g : AmiceRing R} (h : ∀ n, (f : ℤ → R) n = (g : ℤ → R) n) : f = g :=
  Subtype.ext <| funext h

instance instOne : One (AmiceRing R) where
  one := ⟨Pi.single 0 1, single_mem_amiceCoeff 0 1⟩

@[simp, norm_cast]
theorem coe_one : ((1 : AmiceRing R) : ℤ → R) = Pi.single 0 1 :=
  (rfl)

/-- **The Laurent monomial `c tⁿ`** of the Amice ring. -/
def monomial (n : ℤ) (c : R) : AmiceRing R :=
  ⟨Pi.single n c, single_mem_amiceCoeff n c⟩

@[simp, norm_cast]
theorem coe_monomial (n : ℤ) (c : R) : (monomial n c : ℤ → R) = Pi.single n c :=
  (rfl)

@[simp]
theorem monomial_zero_one : monomial 0 (1 : R) = 1 :=
  (rfl)

end One

section Ring

variable [NormedRing R] [IsUltrametricDist R]

noncomputable instance instMul : Mul (AmiceRing R) where
  mul f g := ⟨f ⋆ᵣ₊ g, addRingConvolution_mem_amiceCoeff f.2 g.2⟩

/-- The coefficient family of a product is the convolution of the coefficient families. -/
@[simp, norm_cast]
theorem coe_mul (f g : AmiceRing R) : ((f * g : AmiceRing R) : ℤ → R) = ↑f ⋆ᵣ₊ ↑g :=
  (rfl)

/-- **Laurent monomials multiply by adding degrees**: `(a tᵐ)(b tⁿ) = ab tᵐ⁺ⁿ`. -/
@[simp]
theorem monomial_mul_monomial (m n : ℤ) (a b : R) :
    monomial m a * monomial n b = monomial (m + n) (a * b) :=
  Subtype.ext <| DiscreteConvolution.single_addRingConvolution_single m n a b

variable [CompleteSpace R]

/-- **The coefficients of a product are convergent convolution sums**: the `n`-th coefficient of
`f g` is the sum of the convergent series `∑_{y ∈ ℤ} fₙ₋ᵧ gᵧ`. -/
theorem hasSum_coeff_mul (f g : AmiceRing R) (n : ℤ) :
    HasSum (fun y ↦ (f : ℤ → R) (n - y) * (g : ℤ → R) y) (((f * g : AmiceRing R) : ℤ → R) n) := by
  rw [coe_mul]
  exact (addConvolutionExists_of_mem_amiceCoeff f.2 g.2 n).hasSum_sub

/-- **The Amice ring is a ring** over a complete ultrametric normed ring. -/
noncomputable instance instRing : Ring (AmiceRing R) where
  mul_assoc f g h := Subtype.ext <| by
    simp only [coe_mul]
    exact DiscreteConvolution.addRingConvolution_assoc
      (addConvolutionExists_of_mem_amiceCoeff f.2 g.2)
      (addConvolutionExists_of_mem_amiceCoeff g.2 h.2)
      (summable_sigma_addFiber_mul_mul_of_mem_amiceCoeff f.2 g.2 h.2)
  one_mul f := Subtype.ext <| by
    rw [coe_mul, coe_one, DiscreteConvolution.single_addRingConvolution]
  mul_one f := Subtype.ext <| by
    rw [coe_mul, coe_one, DiscreteConvolution.addRingConvolution_single]
  zero_mul f := Subtype.ext <| by
    rw [coe_mul, Submodule.coe_zero, DiscreteConvolution.zero_addRingConvolution]
  mul_zero f := Subtype.ext <| by
    rw [coe_mul, Submodule.coe_zero, DiscreteConvolution.addRingConvolution_zero]
  left_distrib f g h := Subtype.ext <| by
    rw [coe_mul, Submodule.coe_add, Submodule.coe_add, coe_mul, coe_mul]
    exact DiscreteConvolution.addRingConvolution_add _ _ _
      (addConvolutionExists_of_mem_amiceCoeff f.2 g.2)
      (addConvolutionExists_of_mem_amiceCoeff f.2 h.2)
  right_distrib f g h := Subtype.ext <| by
    rw [coe_mul, Submodule.coe_add, Submodule.coe_add, coe_mul, coe_mul]
    exact DiscreteConvolution.add_addRingConvolution _ _ _
      (addConvolutionExists_of_mem_amiceCoeff f.2 h.2)
      (addConvolutionExists_of_mem_amiceCoeff g.2 h.2)

/-- **A monomial with a unit coefficient is a unit**: the inverse of `a tⁿ` is `a⁻¹ t⁻ⁿ`. In
particular the variable `t = monomial 1 1` is a unit of the Amice ring. -/
theorem isUnit_monomial (n : ℤ) {a : R} (ha : IsUnit a) : IsUnit (monomial n a) := by
  obtain ⟨u, rfl⟩ := ha
  exact isUnit_iff_exists.2 ⟨monomial (-n) ↑u⁻¹, by simp, by simp⟩

section Integral

variable [NormOneClass R]

variable (R) in
/-- **The integral Amice ring** `O_E`: the subring of series whose coefficients lie in the closed
unit ball. -/
def integral : Subring (AmiceRing R) where
  carrier := {f | ∀ n, ‖(f : ℤ → R) n‖ ≤ 1}
  mul_mem' hf hg n := (norm_addRingConvolution_apply_le hf hg n).trans_eq (one_mul 1)
  one_mem' n := (norm_single_apply_le 0 n (1 : R)).trans_eq norm_one
  add_mem' hf hg n := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))
  zero_mem' n := by simp
  neg_mem' hf n := by simpa using hf n

@[simp]
theorem mem_integral {f : AmiceRing R} : f ∈ integral R ↔ ∀ n, ‖(f : ℤ → R) n‖ ≤ 1 :=
  (Iff.rfl)

/-- A monomial `c tⁿ` with `‖c‖ ≤ 1` is integral. -/
theorem monomial_mem_integral (n : ℤ) {c : R} (hc : ‖c‖ ≤ 1) : monomial n c ∈ integral R :=
  fun m ↦ (norm_single_apply_le n m c).trans hc

end Integral

end Ring

section CommRing

variable [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **The Amice ring over a commutative ring is commutative.** -/
noncomputable instance instCommRing : CommRing (AmiceRing R) where
  mul_comm f g := Subtype.ext <| by
    rw [coe_mul, coe_mul, DiscreteConvolution.addRingConvolution_comm]

/-- **The Amice ring is an `R`-algebra**, with the coefficientwise scalar action. -/
noncomputable instance instAlgebra : Algebra R (AmiceRing R) :=
  .ofModule
    (fun c f g ↦ Subtype.ext <| by
      rw [Submodule.coe_smul, coe_mul, coe_mul, Submodule.coe_smul]
      exact DiscreteConvolution.smul_addRingConvolution c _ _
        (addConvolutionExists_of_mem_amiceCoeff f.2 g.2))
    (fun c f g ↦ Subtype.ext <| by
      rw [Submodule.coe_smul, coe_mul, coe_mul, Submodule.coe_smul]
      exact DiscreteConvolution.addRingConvolution_smul c _ _
        (addConvolutionExists_of_mem_amiceCoeff f.2 g.2))

/-- The structure map sends `c` to the constant series `c = c t⁰`. -/
@[simp, norm_cast]
theorem coe_algebraMap (c : R) : (algebraMap R (AmiceRing R) c : ℤ → R) = Pi.single 0 c := by
  simp [Algebra.algebraMap_eq_smul_one, ← Pi.single_smul]

end CommRing

end AmiceRing

/-! ### The bounded Robba ring inside the Amice ring -/

namespace RobbaRing

variable [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- A Robba series with bounded coefficients is an element of the Amice ring. -/
theorem coe_mem_amiceCoeff {f : RobbaRing R} (hf : f ∈ bounded R) :
    (f : ℤ → R) ∈ amiceCoeff R :=
  ⟨mem_bounded.1 hf, tendsto_atBot_of_mem_robbaCoeff f.2⟩

variable (R) in
/-- **The embedding of the bounded Robba ring `R^bd` into the Amice ring `E`**, the identity on
coefficients. -/
noncomputable def boundedToAmice : bounded R →ₐ[R] AmiceRing R where
  toFun f := ⟨f.1, coe_mem_amiceCoeff f.2⟩
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
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
    boundedToAmice R ⟨monomial n c, monomial_mem_bounded n c⟩ = AmiceRing.monomial n c :=
  Subtype.ext <| by simp

/-- **`R^bd = R ∩ E`**: an element of the Amice ring comes from the bounded Robba ring exactly when
its coefficients converge on some annulus `r < |t| < 1`. -/
theorem mem_range_boundedToAmice {g : AmiceRing R} :
    g ∈ (boundedToAmice R).range ↔ (g : ℤ → R) ∈ robbaCoeff R := by
  refine ⟨?_, fun hg ↦ ⟨⟨⟨g, hg⟩, mem_bounded.2 (mem_amiceCoeff.1 g.2).1⟩, Subtype.ext (by simp)⟩⟩
  rintro ⟨f, rfl⟩
  simp

end RobbaRing

end TauCeti
