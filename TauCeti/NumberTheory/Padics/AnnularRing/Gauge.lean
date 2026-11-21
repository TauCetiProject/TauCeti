/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.AnnularRing.Localization
public import TauCeti.RingTheory.Huber.TateGauge.Normed

/-!
# The `T`-adic Tate gauge on `H[1/T]`

Let `H = TauCeti.AnnularRing p` be the integral annular coefficient ring `ℤ_p⟦T, p/T⟧` and let `A`
be any localization of `H` away from `T`. Endow `A` with the `T`-adic topology whose neighbourhoods
of zero have basis `T ^ n H = TauCeti.Huber.awayNhd T A n`. Since `H` is `(T)`-adically complete
and `T` is a non-zero-divisor in `H`, `A` is a complete Hausdorff Tate ring with ring of definition
`H` and pseudo-uniformiser `T`.

For each radius `α ∈ (0, 1)`, the Tate gauge `TauCeti.Huber.tateNorm` attached to `(H, T, α)` gives
a complete ultrametric Banach–Tate ring norm on `A` inducing the `T`-adic topology
(`TauCeti.AnnularRing.awayNormedCommRing`):

* Its closed unit ball is `H` (`TauCeti.AnnularRing.tateNorm_le_one_iff`), and more generally its
  closed ball of radius `α ^ n` is characterized by the coefficient bound
  `‖localizedCoeff p x m‖ ≤ p ^ min 0 (m - n)`.
* Multiplication by `T` scales the norm exactly by `α`, so `T` is a multiplicative
  pseudo-uniformiser of norm `α`, and `‖p‖ = ‖T U‖ = α`.
* Every power `U ^ j = p ^ j T ^ (-j)` lies in `H \ T H` and therefore has norm `1`.
* Consequently, the terms `U ^ j` do not tend to `0` in the `T`-adic topology, and the partial sums
  `∑_{j < N} U ^ j` are neither convergent nor Cauchy in `A`, even though the formal geometric
  series `ofPowerSeriesU (PowerSeries.mk 1)` is a bona fide element of `H` inverting `1 - U`.

Following `TauCeti.Huber.awayTopology` and `TauCeti.Huber.tateNormedCommRing`, neither the uniform
structure nor the normed ring structure is registered as a global instance; the results in the first
section apply to any topology on `A` whose neighbourhoods of zero have basis `T ^ n H`.

## Main definitions

* `TauCeti.AnnularRing.tateNormDatum`: the `Huber.TateNormDatum A` given by `(H, T, α)` for any
  `T`-adic topology on `A`.
* `TauCeti.AnnularRing.awayUniformSpace`: the additive group uniformity of `Huber.awayTopology T A`.
* `TauCeti.AnnularRing.awayNormedCommRing`: the complete ultrametric `NormedCommRing A` induced by
  the `T`-adic Tate gauge of radius `α ∈ (0, 1)`.

## Main results

* `TauCeti.AnnularRing.tateNorm_le_zpow_iff_norm_localizedCoeff_le`,
  `TauCeti.AnnularRing.tateNorm_le_one_iff`: closed balls and unit ball of the `T`-gauge.
* `TauCeti.AnnularRing.tateNorm_T_mul`, `TauCeti.AnnularRing.tateNorm_T`,
  `TauCeti.AnnularRing.tateNorm_U_pow`, `TauCeti.AnnularRing.tateNorm_p`: exact norms of `T`,
  `U ^ j`, and `p`.
* `TauCeti.AnnularRing.not_tendsto_sum_U_pow`, `TauCeti.AnnularRing.not_cauchySeq_sum_U_pow`:
  divergence of the partial sums `∑_{j < N} U ^ j` in the `T`-adic topology.
* `TauCeti.AnnularRing.completeSpace_awayNormedCommRing`,
  `TauCeti.AnnularRing.isUltrametricDist_awayNormedCommRing`,
  `TauCeti.AnnularRing.isTate_awayNormedCommRing`: Banach–Tate properties of `awayNormedCommRing`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.AnnularRing

/-! ### The `T`-adic Tate gauge for any topology with basis `T ^ n H` -/

section HasBasis

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

section Topological

variable [TopologicalSpace A]
  (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
    (Huber.awayNhd (T : AnnularRing p) A n : Set A))
include hb

/-- The terms `U ^ j` do not tend to zero in the `T`-adic topology on `H[1/T]`, since no power
`U ^ j` is divisible by `T` in `H`. -/
theorem not_tendsto_U_pow_zero :
    ¬ Tendsto (fun j : ℕ ↦ algebraMap (AnnularRing p) A (U ^ j)) atTop (𝓝 0) := by
  intro h
  obtain ⟨j, hj⟩ := (h.eventually (hb.mem_of_mem (i := 1) trivial)).exists
  exact T_not_dvd_U_pow j <| by
    simpa only [pow_one] using (Huber.algebraMap_mem_awayNhd_iff T_mem_nonZeroDivisors).mp hj

/-- The partial sums `∑_{j < N} U ^ j` do not converge in the `T`-adic topology on `H[1/T]`, even
though the formal geometric series `ofPowerSeriesU (PowerSeries.mk 1)` lies in `H` and inverts
`1 - U`. -/
theorem not_tendsto_sum_U_pow [ContinuousSub A] :
    ¬ ∃ L : A, Tendsto (fun N : ℕ ↦ ∑ j ∈ Finset.range N, algebraMap (AnnularRing p) A (U ^ j))
      atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hdiff := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
  refine not_tendsto_U_pow_zero hb ?_
  simpa only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hdiff

/-- The series `∑ U ^ j` is not summable in the `T`-adic topology on `H[1/T]`. -/
theorem not_summable_U_pow [ContinuousSub A] :
    ¬ Summable fun j : ℕ ↦ algebraMap (AnnularRing p) A (U ^ j) := fun ⟨L, hL⟩ ↦
  not_tendsto_sum_U_pow hb ⟨L, hL.tendsto_sum_nat⟩

section Datum

variable [SeparatelyContinuousAdd A]

/-- The Tate norm datum on `H[1/T]` given by the ring of definition `H`, the pseudo-uniformiser
`T`, and a chosen radius `α ∈ (0, 1)`. -/
def tateNormDatum {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) : Huber.TateNormDatum A where
  ringOfDefinition := (algebraMap (AnnularRing p) A).range
  isOpen_ringOfDefinition := Huber.isOpen_range_algebraMap_of_hasBasis hb
  isBounded_ringOfDefinition := Huber.isBounded_range_algebraMap_of_hasBasis hb
  pseudoUniformizer := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
  isTopologicallyNilpotent_pseudoUniformizer :=
    (Huber.isPseudoUniformizer_algebraMap_of_hasBasis hb).isTopologicallyNilpotent
  pseudoUniformizer_mem := ⟨T, rfl⟩
  radius := α
  radius_pos := hα₀
  radius_lt_one := hα₁

@[simp] theorem tateNormDatum_ringOfDefinition {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (tateNormDatum hb hα₀ hα₁).ringOfDefinition = (algebraMap (AnnularRing p) A).range := (rfl)

@[simp] theorem tateNormDatum_pseudoUniformizer {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (tateNormDatum hb hα₀ hα₁).pseudoUniformizer =
      (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit := (rfl)

theorem coe_tateNormDatum_pseudoUniformizer {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ((tateNormDatum hb hα₀ hα₁).pseudoUniformizer : A) = algebraMap (AnnularRing p) A T := (rfl)

@[simp] theorem tateNormDatum_radius {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (tateNormDatum hb hα₀ hα₁).radius = α := (rfl)

end Datum

variable [IsTopologicalRing A]

/-- The closed ball of radius `α ^ n` for the `T`-gauge on `H[1/T]` is cut out by the shifted
coefficient bound `‖localizedCoeff p x m‖ ≤ p ^ min 0 (m - n)`. -/
theorem tateNorm_le_zpow_iff_norm_localizedCoeff_le {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {x : A} {n : ℤ} :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁) x ≤ α ^ n ↔
      ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 (m - n) :=
  (Huber.tateNorm_le_zpow_iff (tateNormDatum hb hα₀ hα₁)).trans T_zpow_neg_mul_mem_range_iff

/-- The closed unit ball of the `T`-gauge on `H[1/T]` is `H`. -/
theorem tateNorm_le_one_iff {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) {x : A} :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁) x ≤ 1 ↔ x ∈ (algebraMap (AnnularRing p) A).range := by
  simpa using Huber.tateNorm_le_zpow_iff (tateNormDatum hb hα₀ hα₁) (x := x) (n := 0)

/-- Multiplication by an integer power `T ^ k` scales the `T`-gauge exactly by `α ^ k`. -/
theorem tateNorm_T_zpow_mul {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (k : ℤ) (x : A) :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁)
        (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) * x) =
      α ^ k * Huber.tateNorm (tateNormDatum hb hα₀ hα₁) x :=
  Huber.tateNorm_zpow_mul (tateNormDatum hb hα₀ hα₁) k x

/-- Multiplication by `T` scales the `T`-gauge exactly by `α`. -/
theorem tateNorm_T_mul {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (x : A) :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁) (algebraMap (AnnularRing p) A T * x) =
      α * Huber.tateNorm (tateNormDatum hb hα₀ hα₁) x :=
  Huber.tateNorm_pseudoUniformizer_mul (tateNormDatum hb hα₀ hα₁) x

/-- In the `T`-gauge of radius `α`, the element `T` has norm `α`. -/
theorem tateNorm_T {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁) (algebraMap (AnnularRing p) A T) = α := by
  have : T2Space A := Huber.t2Space_of_hasBasis hb T_mem_nonZeroDivisors
  have : Nontrivial A := (algebraMap_injective (p := p) (A := A)).nontrivial
  simpa using tateNorm_T_mul hb hα₀ hα₁ 1

/-- Every power `U ^ j` has norm `1` for the `T`-gauge of any radius `α ∈ (0, 1)`. -/
theorem tateNorm_U_pow {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (j : ℕ) :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁) (algebraMap (AnnularRing p) A (U ^ j)) = 1 := by
  have hmem : (((tateNormDatum hb hα₀ hα₁).pseudoUniformizer ^ (-(0 : ℤ)) : Aˣ) : A) *
      algebraMap (AnnularRing p) A (U ^ j) ∈ (tateNormDatum hb hα₀ hα₁).ringOfDefinition := by
    simpa using (algebraMap (AnnularRing p) A).mem_range_self (U ^ j)
  have hnot : (((tateNormDatum hb hα₀ hα₁).pseudoUniformizer ^ (-((0 : ℤ) + 1)) : Aˣ) : A) *
      algebraMap (AnnularRing p) A (U ^ j) ∉ (tateNormDatum hb hα₀ hα₁).ringOfDefinition := by
    intro h
    rw [tateNormDatum_pseudoUniformizer, tateNormDatum_ringOfDefinition, zero_add,
      T_zpow_neg_mul_mem_range_iff] at h
    exact T_not_dvd_U_pow j <| T_dvd_iff.mpr fun m ↦ by
      simpa only [localizedCoeff_algebraMap] using h m
  simpa using Huber.tateNorm_eq_zpow_of_mem_of_not_mem (tateNormDatum hb hα₀ hα₁) hmem hnot

/-- The element `U = p / T` has norm `1` for the `T`-gauge of any radius `α ∈ (0, 1)`. -/
theorem tateNorm_U {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁) (algebraMap (AnnularRing p) A U) = 1 := by
  simpa using tateNorm_U_pow hb hα₀ hα₁ 1

/-- Since `p = T U`, the element `p` has norm `α` for the `T`-gauge of radius `α`. -/
theorem tateNorm_p {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    Huber.tateNorm (tateNormDatum hb hα₀ hα₁) (p : A) = α := by
  rw [← map_natCast (algebraMap (AnnularRing p) A), ← T_mul_U, map_mul, tateNorm_T_mul,
    tateNorm_U, mul_one]

end Topological

/-- The partial sums `∑_{j < N} U ^ j` do not form a Cauchy sequence in the `T`-adic uniformity on
`H[1/T]`. -/
theorem not_cauchySeq_sum_U_pow [UniformSpace A] [IsUniformAddGroup A]
    (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A)) :
    ¬ CauchySeq fun N : ℕ ↦ ∑ j ∈ Finset.range N, algebraMap (AnnularRing p) A (U ^ j) := by
  have : CompleteSpace A := Huber.completeSpace_of_hasBasis hb T_mem_nonZeroDivisors
  exact fun hc ↦ not_tendsto_sum_U_pow hb (cauchySeq_tendsto_of_complete hc)

end HasBasis

/-! ### The complete Banach–Tate `NormedCommRing` structure on `H[1/T]` -/

section AwayNormedCommRing

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- The additive group uniformity on `H[1/T]` induced by the `T`-adic topology
`Huber.awayTopology T A`. It is not a global instance. -/
abbrev awayUniformSpace : UniformSpace A :=
  letI : TopologicalSpace A := Huber.awayTopology (T : AnnularRing p) A
  haveI : IsTopologicalRing A := Huber.isTopologicalRing_awayTopology (π := (T : AnnularRing p))
  IsTopologicalAddGroup.rightUniformSpace A

/-- The complete ultrametric Banach–Tate `NormedCommRing` structure on `H[1/T]` induced by the
`T`-adic Tate gauge of radius `α ∈ (0, 1)`.

Its underlying `CommRing`, `UniformSpace`, and `TopologicalSpace` structures are definitionally
`‹CommRing A›`, `awayUniformSpace p A`, and `Huber.awayTopology T A`, independent of `α`. It is
not registered as a global instance. -/
abbrev awayNormedCommRing {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) : NormedCommRing A :=
  letI : UniformSpace A := awayUniformSpace p A
  haveI : IsTopologicalRing A := Huber.isTopologicalRing_awayTopology (π := (T : AnnularRing p))
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  haveI : T2Space A :=
    Huber.t2Space_of_hasBasis
      (Huber.hasBasis_nhds_zero_awayTopology (π := (T : AnnularRing p)) (A := A))
      T_mem_nonZeroDivisors
  Huber.tateNormedCommRing
    (tateNormDatum (Huber.hasBasis_nhds_zero_awayTopology (π := (T : AnnularRing p)) (A := A))
      hα₀ hα₁)

variable {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)

theorem commRing_awayNormedCommRing :
    (awayNormedCommRing p A hα₀ hα₁).toCommRing = (inferInstance : CommRing A) := (rfl)

theorem uniformSpace_awayNormedCommRing :
    (awayNormedCommRing p A hα₀ hα₁).toUniformSpace = awayUniformSpace p A := (rfl)

theorem topologicalSpace_awayNormedCommRing :
    (awayNormedCommRing p A hα₀ hα₁).toUniformSpace.toTopologicalSpace =
      Huber.awayTopology (T : AnnularRing p) A := (rfl)

theorem hasBasis_nhds_zero_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (Huber.awayNhd (T : AnnularRing p) A n : Set A) :=
  Huber.hasBasis_nhds_zero_awayTopology (π := (T : AnnularRing p)) (A := A)

theorem norm_awayNormedCommRing (x : A) :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖x‖ = Huber.tateNorm
      (tateNormDatum (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁) x := by
  let := awayNormedCommRing p A hα₀ hα₁
  exact Huber.norm_tateNormedCommRing
    (tateNormDatum (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁) x

/-- `H[1/T]` is complete for the `T`-adic Tate gauge of any radius `α ∈ (0, 1)`. -/
theorem completeSpace_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    CompleteSpace A := by
  let := awayNormedCommRing p A hα₀ hα₁
  exact Huber.completeSpace_of_hasBasis (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁)
    T_mem_nonZeroDivisors

/-- The `T`-adic Tate gauge on `H[1/T]` is ultrametric. -/
theorem isUltrametricDist_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    IsUltrametricDist A := by
  let := awayNormedCommRing p A hα₀ hα₁
  exact Huber.isUltrametricDist_tateNormedCommRing
    (tateNormDatum (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁)

/-- `‖1‖ = 1` for the `T`-adic Tate gauge on `H[1/T]`. -/
theorem normOneClass_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    NormOneClass A := by
  let := awayNormedCommRing p A hα₀ hα₁
  have : Nontrivial A := (algebraMap_injective (p := p) (A := A)).nontrivial
  exact Huber.normOneClass_tateNormedCommRing
    (tateNormDatum (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁)

/-- `H[1/T]` with the `T`-adic Tate gauge is a normed Tate ring. -/
theorem isTate_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    NormedRing.IsTate A := by
  let := awayNormedCommRing p A hα₀ hα₁
  have : Nontrivial A := (algebraMap_injective (p := p) (A := A)).nontrivial
  exact Huber.isTate_tateNormedCommRing
    (tateNormDatum (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁)

theorem norm_le_zpow_iff_awayNormedCommRing {x : A} {n : ℤ} :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖x‖ ≤ α ^ n ↔ ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_le_zpow_iff_norm_localizedCoeff_le
    (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁

theorem norm_le_one_iff_awayNormedCommRing {x : A} :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖x‖ ≤ 1 ↔ x ∈ (algebraMap (AnnularRing p) A).range := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_le_one_iff (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁

theorem norm_T_zpow_mul_awayNormedCommRing (k : ℤ) (x : A) :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖(((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) : A) * x‖ =
      α ^ k * ‖x‖ := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing, norm_awayNormedCommRing]
  exact tateNorm_T_zpow_mul (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁ k x

theorem norm_T_mul_awayNormedCommRing (x : A) :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖algebraMap (AnnularRing p) A T * x‖ = α * ‖x‖ := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing, norm_awayNormedCommRing]
  exact tateNorm_T_mul (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁ x

theorem norm_T_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖algebraMap (AnnularRing p) A T‖ = α := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_T (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁

theorem norm_U_pow_awayNormedCommRing (j : ℕ) :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖algebraMap (AnnularRing p) A (U ^ j)‖ = 1 := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_U_pow (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁ j

theorem norm_U_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖algebraMap (AnnularRing p) A U‖ = 1 := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_U (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁

theorem norm_p_awayNormedCommRing :
    letI := awayNormedCommRing p A hα₀ hα₁
    ‖(p : A)‖ = α := by
  let := awayNormedCommRing p A hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_p (hasBasis_nhds_zero_awayNormedCommRing p A hα₀ hα₁) hα₀ hα₁

end AwayNormedCommRing

end TauCeti.AnnularRing
